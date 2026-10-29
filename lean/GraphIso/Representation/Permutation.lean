module

public import GraphIso.Semantics.Action
public import Mathlib.Data.Fintype.Basic

/-!
# Represented permutations

A permutation of `Fin n` is represented by a pair of arrays of naturals: the forward images
and the inverse images. `PermData.Valid n d` says that both arrays have length `n`, all entries
are below `n`, and the arrays are mutually inverse. `PermData.denote n d` interprets valid data
as a permutation of `Fin n` (and is the identity on invalid data, so that it is total).

Array reads use `get a i = a.getD i 0`, the semantics of an array read in the cost model.

The functional models of the elementary operations are proved to agree with the interpreted
permutations:

| operation | data | semantics |
|---|---|---|
| `PermData.one n` | `(range n, range n)` | `1` |
| `PermData.inv d` | swap the two arrays | `(denote d)⁻¹` |
| `PermData.mul g h` | `(amap (get g.1) h.1, amap (get h.2) g.2)` | `denote g * denote h` |
| `PermData.beq g h` | compare forward arrays | `denote g = denote h` |

Their costs are established when they are implemented in the cost language.
-/

@[expose] public section

namespace GraphIso

open Equiv

/-- Total array read with default `0`; the semantics of an array read in the cost model. -/
def get (a : Array ℕ) (i : ℕ) : ℕ := a.getD i 0

theorem get_eq_getElem {a : Array ℕ} {i : ℕ} (h : i < a.size) : get a i = a[i] := by
  simp [get, h]

theorem get_toArray (l : List ℕ) (i : ℕ) : get l.toArray i = l.getD i 0 := by
  simp [get, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

theorem get_of_size_le {a : Array ℕ} {i : ℕ} (h : a.size ≤ i) : get a i = 0 := by
  simp [get, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none h]

/-- Map over an array through its list of elements. It equals `Array.map` (`amap_eq_map`) and,
unlike `Array.map`, reduces in the kernel, so concrete checks can use `decide`. -/
def amap {α β : Type} (f : α → β) (a : Array α) : Array β := (a.toList.map f).toArray

@[simp] theorem amap_eq_map {α β : Type} (f : α → β) (a : Array α) : amap f a = a.map f := by
  cases a
  simp [amap]

@[simp] theorem size_amap {α β : Type} (f : α → β) (a : Array α) : (amap f a).size = a.size := by
  simp

theorem get_map {a : Array ℕ} {f : ℕ → ℕ} {i : ℕ} (h : i < a.size) :
    get (a.map f) i = f (get a i) := by
  rw [get_eq_getElem (by simpa using h), get_eq_getElem h, Array.getElem_map]

theorem get_amap {a : Array ℕ} {f : ℕ → ℕ} {i : ℕ} (h : i < a.size) :
    get (amap f a) i = f (get a i) := by
  rw [amap_eq_map, get_map h]

@[simp] theorem get_range {n i : ℕ} (h : i < n) : get (Array.range n) i = i := by
  rw [get_eq_getElem (by simpa using h), Array.getElem_range]

theorem get_ofFn {n : ℕ} (f : Fin n → ℕ) (i : Fin n) : get (Array.ofFn f) i = f i := by
  rw [get_eq_getElem (by simp), Array.getElem_ofFn]

theorem sum_map_const {α : Type} (xs : List α) (c : ℕ) :
    (xs.map fun _ => c).sum = xs.length * c := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih, Nat.succ_mul]
    omega

theorem sum_map_le {α : Type} (xs : List α) (f : α → ℕ) (c : ℕ) (h : ∀ x ∈ xs, f x ≤ c) :
    (xs.map f).sum ≤ xs.length * c := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    have := ih fun y hy => h y (List.mem_cons_of_mem _ hy)
    have := h x List.mem_cons_self
    omega

/-- Raw permutation data: forward images and inverse images. -/
abbrev PermData := Array ℕ × Array ℕ

namespace PermData

/-- Valid data for a permutation of `Fin n`. -/
structure Valid (n : ℕ) (d : PermData) : Prop where
  size_fwd : d.1.size = n
  size_inv : d.2.size = n
  fwd_lt : ∀ i < n, get d.1 i < n
  inv_lt : ∀ i < n, get d.2 i < n
  inv_fwd : ∀ i < n, get d.2 (get d.1 i) = i
  fwd_inv : ∀ i < n, get d.1 (get d.2 i) = i

/-- Executable validity check. -/
def validB (n : ℕ) (d : PermData) : Bool :=
  d.1.size == n && d.2.size == n &&
    (List.range n).all fun i =>
      decide (get d.1 i < n) && decide (get d.2 i < n) &&
        get d.2 (get d.1 i) == i && get d.1 (get d.2 i) == i

theorem validB_iff {n : ℕ} {d : PermData} : validB n d = true ↔ Valid n d := by
  simp only [validB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq]
  constructor
  · rintro ⟨⟨h1, h2⟩, h⟩
    exact ⟨h1, h2, fun i hi => (h i hi).1.1.1, fun i hi => (h i hi).1.1.2,
      fun i hi => (h i hi).1.2, fun i hi => (h i hi).2⟩
  · intro h
    exact ⟨⟨h.size_fwd, h.size_inv⟩, fun i hi =>
      ⟨⟨⟨h.fwd_lt i hi, h.inv_lt i hi⟩, h.inv_fwd i hi⟩, h.fwd_inv i hi⟩⟩

instance (n : ℕ) (d : PermData) : Decidable (Valid n d) :=
  decidable_of_iff _ validB_iff

/-- The permutation of `Fin n` described by valid data. -/
def toPerm {n : ℕ} (d : PermData) (h : Valid n d) : Perm (Fin n) where
  toFun i := ⟨get d.1 i, h.fwd_lt i i.2⟩
  invFun i := ⟨get d.2 i, h.inv_lt i i.2⟩
  left_inv i := Fin.ext (h.inv_fwd i i.2)
  right_inv i := Fin.ext (h.fwd_inv i i.2)

/-- Total interpretation of permutation data: `toPerm` on valid data, the identity otherwise. -/
def denote (n : ℕ) (d : PermData) : Perm (Fin n) :=
  if h : Valid n d then toPerm d h else 1

theorem denote_of_valid {n : ℕ} {d : PermData} (h : Valid n d) : denote n d = toPerm d h := by
  simp [denote, h]

theorem val_denote_apply {n : ℕ} {d : PermData} (h : Valid n d) (i : Fin n) :
    (denote n d i).val = get d.1 i := by
  rw [denote_of_valid h]
  rfl

theorem val_denote_inv_apply {n : ℕ} {d : PermData} (h : Valid n d) (i : Fin n) :
    ((denote n d)⁻¹ i).val = get d.2 i := by
  rw [denote_of_valid h]
  rfl

theorem denote_apply {n : ℕ} {d : PermData} (h : Valid n d) (i : Fin n) :
    denote n d i = ⟨get d.1 i, h.fwd_lt i i.2⟩ :=
  Fin.ext (val_denote_apply h i)

/-- Forward arrays of valid data agree with the interpreted permutation. -/
theorem fwd_eq_ofFn {n : ℕ} {d : PermData} (h : Valid n d) :
    d.1 = Array.ofFn fun i : Fin n => (denote n d i).val := by
  apply Array.ext (by simp [h.size_fwd])
  intro i hi _
  rw [Array.getElem_ofFn, val_denote_apply h, get_eq_getElem hi]

theorem inv_eq_ofFn {n : ℕ} {d : PermData} (h : Valid n d) :
    d.2 = Array.ofFn fun i : Fin n => ((denote n d)⁻¹ i).val := by
  apply Array.ext (by simp [h.size_inv])
  intro i hi _
  rw [Array.getElem_ofFn, val_denote_inv_apply h, get_eq_getElem hi]

/-! ### Representing a given permutation -/

/-- The data representing a permutation of `Fin n`. -/
def ofPerm {n : ℕ} (π : Perm (Fin n)) : PermData :=
  (Array.ofFn fun i => (π i).val, Array.ofFn fun i => (π⁻¹ i).val)

theorem valid_ofPerm {n : ℕ} (π : Perm (Fin n)) : Valid n (ofPerm π) := by
  refine ⟨by simp [ofPerm], by simp [ofPerm], fun i hi => ?_, fun i hi => ?_, fun i hi => ?_,
    fun i hi => ?_⟩
  · rw [ofPerm, get_ofFn _ ⟨i, hi⟩]
    exact (π _).2
  · rw [ofPerm, get_ofFn _ ⟨i, hi⟩]
    exact (π⁻¹ _).2
  · simp only [ofPerm]
    rw [get_ofFn _ ⟨i, hi⟩, get_ofFn _ (π ⟨i, hi⟩)]
    simp
  · simp only [ofPerm]
    rw [get_ofFn _ ⟨i, hi⟩, get_ofFn _ (π⁻¹ ⟨i, hi⟩)]
    simp

@[simp] theorem denote_ofPerm {n : ℕ} (π : Perm (Fin n)) : denote n (ofPerm π) = π := by
  ext i
  rw [val_denote_apply (valid_ofPerm π), ofPerm, get_ofFn]

/-- Valid data is determined by its interpretation. -/
theorem eq_ofPerm_denote {n : ℕ} {d : PermData} (h : Valid n d) : d = ofPerm (denote n d) := by
  rw [ofPerm, ← fwd_eq_ofFn h, ← inv_eq_ofFn h]

theorem denote_injOn {n : ℕ} {d e : PermData} (hd : Valid n d) (he : Valid n e)
    (h : denote n d = denote n e) : d = e := by
  rw [eq_ofPerm_denote hd, eq_ofPerm_denote he, h]

/-! ### Identity -/

/-- The identity permutation of `Fin n`. -/
def one (n : ℕ) : PermData := (Array.range n, Array.range n)

theorem valid_one (n : ℕ) : Valid n (one n) := by
  refine ⟨by simp [one], by simp [one], fun i hi => ?_, fun i hi => ?_, fun i hi => ?_,
    fun i hi => ?_⟩ <;> simp [one, hi]

@[simp] theorem denote_one (n : ℕ) : denote n (one n) = 1 := by
  ext i
  rw [val_denote_apply (valid_one n), one, get_range i.2]
  rfl

/-! ### Inverse -/

/-- Inversion swaps the forward and inverse arrays. -/
def inv (d : PermData) : PermData := (d.2, d.1)

theorem Valid.inv {n : ℕ} {d : PermData} (h : Valid n d) : Valid n d.inv :=
  ⟨h.size_inv, h.size_fwd, h.inv_lt, h.fwd_lt, h.fwd_inv, h.inv_fwd⟩

theorem denote_inv {n : ℕ} {d : PermData} (h : Valid n d) : denote n d.inv = (denote n d)⁻¹ := by
  ext i
  rw [val_denote_apply h.inv, val_denote_inv_apply h]
  rfl

/-! ### Composition -/

/-- Composition `g * h` (apply `h` first): forward `i ↦ g (h i)`, inverse `i ↦ h⁻¹ (g⁻¹ i)`. -/
def mul (g h : PermData) : PermData := (amap (get g.1) h.1, amap (get h.2) g.2)

theorem Valid.mul {n : ℕ} {g h : PermData} (hg : Valid n g) (hh : Valid n h) :
    Valid n (g.mul h) := by
  have hf : ∀ i < n, get (amap (get g.1) h.1) i = get g.1 (get h.1 i) := fun i hi =>
    get_amap (by rw [hh.size_fwd]; exact hi)
  have hi' : ∀ i < n, get (amap (get h.2) g.2) i = get h.2 (get g.2 i) := fun i hi =>
    get_amap (by rw [hg.size_inv]; exact hi)
  refine ⟨by simp [PermData.mul, hh.size_fwd], by simp [PermData.mul, hg.size_inv],
    fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · rw [PermData.mul, hf i hi]
    exact hg.fwd_lt _ (hh.fwd_lt i hi)
  · rw [PermData.mul, hi' i hi]
    exact hh.inv_lt _ (hg.inv_lt i hi)
  · simp only [PermData.mul]
    rw [hf i hi, hi' _ (hg.fwd_lt _ (hh.fwd_lt i hi)), hg.inv_fwd _ (hh.fwd_lt i hi),
      hh.inv_fwd i hi]
  · simp only [PermData.mul]
    rw [hi' i hi, hf _ (hh.inv_lt _ (hg.inv_lt i hi)), hh.fwd_inv _ (hg.inv_lt i hi),
      hg.fwd_inv i hi]

theorem denote_mul {n : ℕ} {g h : PermData} (hg : Valid n g) (hh : Valid n h) :
    denote n (g.mul h) = denote n g * denote n h := by
  ext i
  rw [val_denote_apply (hg.mul hh), Perm.mul_apply, val_denote_apply hg, val_denote_apply hh,
    PermData.mul, get_amap (by rw [hh.size_fwd]; exact i.2)]

/-! ### Equality test -/

/-- Equality test on forward arrays. -/
def beq (g h : PermData) : Bool := g.1 == h.1

theorem beq_iff {n : ℕ} {g h : PermData} (hg : Valid n g) (hh : Valid n h) :
    g.beq h = true ↔ denote n g = denote n h := by
  rw [beq, beq_iff_eq]
  constructor
  · intro e
    ext i
    rw [val_denote_apply hg, val_denote_apply hh, e]
  · intro e
    rw [fwd_eq_ofFn hg, fwd_eq_ofFn hh, e]

end PermData

end GraphIso
