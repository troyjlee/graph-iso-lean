module

public import GraphIso.Coherent.WL
public import GraphIso.Representation.Permutation
public import Mathlib.Tactic.Ring

/-!
# Tuples as codes and digit lists

The programs store a colouring of the `k`-tuples of `Fin m` as an array indexed by the codes
`enc x = ∑ⱼ xⱼ mʲ` (mathlib's `finFunctionFinEquiv`). This file gives the functional models of
the tables they precompute, and their meaning:

* `tupList k m`: the digit lists of all codes `t < m^k`, in increasing order (`tupList_eq`),
  built by prepending each digit to the shorter lists (`ext`);
* `pwTab k m`: the products `z · mʲ` (`get2_pwTab`), so that the code of `update x j z` is
  `enc x − xⱼ mʲ + z mʲ` (`nbrRowM_eq`) and the code of `x ∘ τ` is `∑ᵢ x_{τ i} mⁱ`
  (`monoRowM_eq`), with no multiplication at run time;
* `infoL k m`: for every code `t`, the equality pattern of its tuple (`patRowM_eq`), the codes
  of the tuples with one position replaced and the codes of the tuples `x ∘ τ`.

`toFun col` reads an array as a colouring; `arrOf c` writes a colouring as an array, and
`toFun (arrOf c) = c`.
-/

@[expose] public section

namespace GraphIso.Coherent

open Finset Function

variable {k m : ℕ}

/-! ### Codes -/

/-- The code of a tuple. -/
def enc (x : Tup k m) : ℕ := (finFunctionFinEquiv x : ℕ)

/-- The digits of a tuple, position `0` first. -/
def digits (x : Tup k m) : List ℕ := List.ofFn fun j => (x j : ℕ)

/-- The digits of a code: `t / mʲ % m` for `j < k`. -/
def digitsOf (k m t : ℕ) : List ℕ := List.ofFn fun j : Fin k => t / m ^ (j : ℕ) % m

/-- An array read as a colouring of the tuples. -/
def toFun (col : Array ℕ) (x : Tup k m) : ℕ := get col (enc x)

variable (k m) in
/-- A colouring written as an array indexed by codes. -/
def arrOf (c : Tup k m → ℕ) : Array ℕ :=
  ((List.finRange (m ^ k)).map fun t => c (finFunctionFinEquiv.symm t)).toArray

theorem enc_lt (x : Tup k m) : enc x < m ^ k := (finFunctionFinEquiv x).2

theorem enc_eq_sum (x : Tup k m) : enc x = ∑ j, (x j : ℕ) * m ^ (j : ℕ) :=
  finFunctionFinEquiv_apply x

theorem enc_injective : Function.Injective (enc (k := k) (m := m)) := fun _ _ h =>
  finFunctionFinEquiv.injective (Fin.ext h)

theorem symm_enc (x : Tup k m) : finFunctionFinEquiv.symm ⟨enc x, enc_lt x⟩ = x := by
  rw [show (⟨enc x, enc_lt x⟩ : Fin (m ^ k)) = finFunctionFinEquiv x from Fin.ext rfl,
    Equiv.symm_apply_apply]

theorem enc_symm (t : Fin (m ^ k)) : enc (finFunctionFinEquiv.symm t) = t := by
  simp [enc]

theorem digits_symm (t : Fin (m ^ k)) : digits (finFunctionFinEquiv.symm t) = digitsOf k m t := by
  simp [digits, digitsOf, finFunctionFinEquiv_symm_apply_val]

theorem size_arrOf (c : Tup k m → ℕ) : (arrOf k m c).size = m ^ k := by
  simp [arrOf]

theorem get_arrOf (c : Tup k m → ℕ) (x : Tup k m) : get (arrOf k m c) (enc x) = c x := by
  have h := enc_lt x
  simp only [get, arrOf, Array.getD_eq_getD_getElem?]
  simp only [List.getElem?_toArray, List.getElem?_map, List.length_finRange, h,
    List.getElem?_eq_getElem, List.getElem_finRange, Option.map_some, Option.getD_some]
  rw [show (Fin.cast (List.length_finRange (n := m ^ k)) ⟨enc x, _⟩ : Fin (m ^ k)) =
    ⟨enc x, h⟩ from rfl, symm_enc]

theorem toFun_arrOf (c : Tup k m → ℕ) : toFun (arrOf k m c) = c := by
  funext x
  exact get_arrOf c x

/-! ### All digit lists -/

/-- Every list of `acc` extended at the front by each digit `z < m`. -/
def ext (m : ℕ) (acc : List (List ℕ)) : List (List ℕ) :=
  acc.flatMap fun t => (List.range m).map (· :: t)

variable (k m) in
/-- The digit lists of length `k`, built by `k` extensions of `[[]]`. -/
def tupList : List (List ℕ) := (List.range k).foldl (fun acc _ => ext m acc) [[]]

theorem range_mul_eq (a m : ℕ) :
    List.range (a * m) = (List.range a).flatMap fun q => (List.range m).map (q * m + ·) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.succ_mul, List.range_add, ih, List.range_succ, List.flatMap_append]
    simp

theorem digitsOf_succ {m q r : ℕ} (hr : r < m) (k : ℕ) :
    digitsOf (k + 1) m (q * m + r) = r :: digitsOf k m q := by
  simp only [digitsOf, List.ofFn_succ, Fin.val_zero, pow_zero, Nat.div_one, Fin.val_succ]
  congr 1
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]
  · congr 1
    funext j
    have hm : 0 < m := by omega
    rw [pow_succ', ← Nat.div_div_eq_div_mul, Nat.add_comm, Nat.add_mul_div_right _ _ hm,
      Nat.div_eq_of_lt hr, Nat.zero_add]

/-- **The digit lists in the order of their codes.** -/
theorem tupList_eq (k m : ℕ) : tupList k m = (List.range (m ^ k)).map (digitsOf k m) := by
  induction k with
  | zero => simp [tupList, digitsOf]
  | succ k ih =>
    have h : tupList (k + 1) m = ext m (tupList k m) := by
      simp [tupList, List.range_succ, List.foldl_append]
    rw [h, ih, ext, List.flatMap_map, pow_succ, range_mul_eq, List.map_flatMap]
    refine List.flatMap_congr fun q _ => ?_
    rw [List.map_map]
    refine List.map_congr_left fun r hr => ?_
    simp only [Function.comp_apply]
    exact (digitsOf_succ (List.mem_range.1 hr) k).symm

theorem length_tupList (k m : ℕ) : (tupList k m).length = m ^ k := by
  simp [tupList_eq]

theorem getD_tupList {t : ℕ} (ht : t < m ^ k) : (tupList k m).getD t [] = digitsOf k m t := by
  simp [tupList_eq, ht]

/-! ### Products of digits and powers -/

/-- The row `[0, p, 2 p, …, (m − 1) p]`. -/
def pwRow (m p : ℕ) : Array ℕ := ((List.range m).map (· * p)).toArray

variable (k m) in
/-- The table of the products `z · mʲ`, `j < k`, `z < m`. -/
def pwTab : Array (Array ℕ) := ((List.range k).map fun j => pwRow m (m ^ j)).toArray

/-- A read of a table of rows. -/
def get2 (pw : Array (Array ℕ)) (j v : ℕ) : ℕ := (pw.getD j #[]).getD v 0

theorem get2_pwTab {j v : ℕ} (hj : j < k) (hv : v < m) : get2 (pwTab k m) j v = v * m ^ j := by
  simp [get2, pwTab, pwRow, hj, hv]

/-! ### The rows of a tuple -/

/-- The codes of the tuples `x ∘ τ`, from the digits `dA` of `x` and those of `τ`. -/
def codeM (pw : Array (Array ℕ)) (dA τA : Array ℕ) (k : ℕ) : ℕ :=
  (List.range k).foldl (fun acc i => acc + get2 pw i (get dA (get τA i))) 0

/-- The codes of the tuples `update x j z`, for every `z` and then every `j`. -/
def nbrRowM (pw : Array (Array ℕ)) (t : ℕ) (dA : Array ℕ) (k m : ℕ) : List (List ℕ) :=
  (List.range m).map fun z => (List.range k).map fun j => t - get2 pw j (get dA j) + get2 pw j z

/-- The codes of the tuples `x ∘ τ` for all maps of positions `τ`, given by their digits. -/
def monoRowM (pw : Array (Array ℕ)) (dA : Array ℕ) (mapsA : List (Array ℕ)) (k : ℕ) :
    List ℕ :=
  mapsA.map fun τA => codeM pw dA τA k

/-- The equality pattern from the digits. -/
def patRowM (dA : Array ℕ) (k : ℕ) : List ℕ :=
  (List.range k).flatMap fun i => (List.range k).map fun j => if get dA i = get dA j then 1 else 0

/-- What a round needs to know about the tuple of code `t`: its code, its equality pattern, the
codes of its neighbours and the codes of its rearrangements. -/
abbrev Info := ℕ × List ℕ × List (List ℕ) × List ℕ

variable (k) in
/-- The digit arrays of all maps of positions, in the order of their codes. -/
def mapsArr : List (Array ℕ) := (tupList k k).map List.toArray

variable (k m) in
/-- The information on the tuple of code `t`. -/
def infoAt (t : ℕ) : Info :=
  (t, patRowM ((tupList k m).getD t []).toArray k,
    nbrRowM (pwTab k m) t ((tupList k m).getD t []).toArray k m,
    monoRowM (pwTab k m) ((tupList k m).getD t []).toArray (mapsArr k) k)

variable (k m) in
/-- The information on all tuples, in the order of their codes. -/
def infoL : List Info := (List.range (m ^ k)).map (infoAt k m)

/-! ### Meaning of the rows -/

theorem get_digits (x : Tup k m) {j : ℕ} (hj : j < k) :
    get (digits x).toArray j = x ⟨j, hj⟩ := by
  simp [get, digits, hj]

theorem getD_tupList_enc (x : Tup k m) : (tupList k m).getD (enc x) [] = digits x := by
  rw [getD_tupList (enc_lt x), ← digits_symm ⟨enc x, enc_lt x⟩, symm_enc]

theorem map_finRange_eq_range {β : Type*} (n : ℕ) (f : ℕ → β) :
    (List.finRange n).map (fun i : Fin n => f (i : ℕ)) = (List.range n).map f := by
  rw [← List.map_coe_finRange_eq_range, List.map_map]
  rfl

theorem patRowM_eq (x : Tup k m) : patRowM (digits x).toArray k = pattern x := by
  unfold patRowM pattern
  rw [← List.map_coe_finRange_eq_range, List.flatMap_map]
  refine List.flatMap_congr fun i _ => ?_
  rw [List.map_map]
  refine List.map_congr_left fun j _ => ?_
  simp only [Function.comp_apply]
  rw [get_digits x i.2, get_digits x j.2]
  simp [Fin.val_inj]

theorem enc_update (x : Tup k m) (j : Fin k) (z : Fin m) :
    enc (update x j z) + (x j : ℕ) * m ^ (j : ℕ) = enc x + (z : ℕ) * m ^ (j : ℕ) := by
  rw [enc_eq_sum, enc_eq_sum, ← Finset.add_sum_erase _ _ (mem_univ j),
    ← Finset.add_sum_erase _ _ (mem_univ j)]
  have : ∑ i ∈ univ.erase j, ((update x j z i : Fin m) : ℕ) * m ^ (i : ℕ) =
      ∑ i ∈ univ.erase j, (x i : ℕ) * m ^ (i : ℕ) :=
    Finset.sum_congr rfl fun i hi => by rw [update_of_ne (Finset.ne_of_mem_erase hi)]
  rw [this, update_self]
  ring

theorem nbrRowM_eq (x : Tup k m) :
    nbrRowM (pwTab k m) (enc x) (digits x).toArray k m =
      (List.finRange m).map fun z => (List.finRange k).map fun j => enc (update x j z) := by
  unfold nbrRowM
  rw [← map_finRange_eq_range m]
  refine List.map_congr_left fun z _ => ?_
  rw [← map_finRange_eq_range k]
  refine List.map_congr_left fun j _ => ?_
  rw [get_digits x j.2, get2_pwTab j.2 (x j).2, get2_pwTab j.2 z.2]
  have h := enc_update x j z
  have hle : (x j : ℕ) * m ^ (j : ℕ) ≤ enc x := by
    rw [enc_eq_sum, ← Finset.add_sum_erase _ _ (mem_univ j)]
    exact Nat.le_add_right _ _
  omega

theorem foldl_add_eq (f : ℕ → ℕ) :
    ∀ (l : List ℕ) (a : ℕ), l.foldl (fun acc i => acc + f i) a = a + (l.map f).sum
  | [], a => by simp
  | i :: l, a => by
    simp only [List.foldl_cons, foldl_add_eq f l, List.map_cons, List.sum_cons]
    ring

theorem codeM_eq (x : Tup k m) (τ : Fin k → Fin k) :
    codeM (pwTab k m) (digits x).toArray (digits τ).toArray k = enc (x ∘ τ) := by
  unfold codeM
  rw [foldl_add_eq, Nat.zero_add, enc_eq_sum, Fin.sum_univ_def, ← map_finRange_eq_range k]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  rw [get_digits τ i.2, get_digits x (τ i).2, get2_pwTab i.2 (x (τ i)).2]
  rfl

theorem mapsArr_eq : mapsArr k = (posMaps k).map fun τ => (digits τ).toArray := by
  rw [mapsArr, tupList_eq, posMaps, List.map_map, List.map_map, ← map_finRange_eq_range]
  refine List.map_congr_left fun t _ => ?_
  simp only [Function.comp_apply]
  rw [← digits_symm t]

theorem monoRowM_eq (x : Tup k m) :
    monoRowM (pwTab k m) (digits x).toArray (mapsArr k) k =
      (posMaps k).map fun τ => enc (x ∘ τ) := by
  rw [monoRowM, mapsArr_eq, List.map_map]
  exact List.map_congr_left fun τ _ => codeM_eq x τ

/-- **The information on the tuple of code `enc x`.** -/
theorem infoAt_enc (x : Tup k m) :
    infoAt k m (enc x) = (enc x, pattern x,
      (List.finRange m).map (fun z => (List.finRange k).map fun j => enc (update x j z)),
      (posMaps k).map fun τ => enc (x ∘ τ)) := by
  simp only [infoAt, getD_tupList_enc, patRowM_eq, nbrRowM_eq, monoRowM_eq]

theorem infoL_eq : infoL k m = (List.finRange (m ^ k)).map fun t =>
    infoAt k m (enc (finFunctionFinEquiv.symm t)) := by
  rw [infoL, ← map_finRange_eq_range]
  refine List.map_congr_left fun t _ => ?_
  rw [enc_symm]

end GraphIso.Coherent
