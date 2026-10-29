module

public import GraphIso.Graph.SimpleGraph
public import GraphIso.Main.M5CJData
public import GraphIso.Reductions.RestrictionData
public import Mathlib.GroupTheory.Perm.Closure
public import Mathlib.GroupTheory.Perm.Fin

/-!
# The graph-isomorphism entry: the encoding and the decoding

Stage 14j-6c-3, items 1 and 2 (`PLAN-14.md` §14.15). Two graphs on `n` vertices become strings
on `N = n + n · n` points under the lift of `Sym(V)`.

* **The points** (`ptEquiv`): the vertex `u` is the point `u`, and the ordered pair `(u, v)` is
  the point `n + (v + n u)`.
* **The lift** `liftPerm n : Perm (Fin n) →* Perm (Fin N)`: `φ` on the vertices and
  `(u, v) ↦ (φ u, φ v)` on the pairs. It is injective (`liftPerm_injective`).
* **The strings** `gStr n X`: `0` at the vertices, and at `(u, v)` `1` if `Adj X u v` and `0`
  otherwise (`gStr_inl`, `gStr_inr`).
* **The generators** `gensData n`: the lifts of the `n`-cycle `finRotate n` and of the
  transposition of `0` and `1`, none for `n ≤ 1`. They generate the image of `liftPerm`
  (`gensData_denote`), by mathlib's `closure_cycle_adjacent_swap`.
* **The reduction** (`iso_graph`): for valid data, the solutions on the whole domain in the image
  of `liftPerm`, with the identity as representative, are the lifts of the isomorphisms.
* **Decoding** (`decodeAns`): the restriction of the representative and of the generators to the
  first `n` points. `GICosetOK n X Y r` says that `r` is `none` exactly when there is no
  isomorphism, and that otherwise it is valid data of a coset `φ₀ • ⟨hs⟩` equal to the set of
  isomorphisms, with at most `(2N)²` generators. `decode_ok`: the decoding of a correct answer
  of the encoded instance is `GICosetOK`.

The data are built by writes into arrays (`Prim.applyWrites`): the pair offsets `n + n u` come
from the array `offArr n`, so the programs of `GraphEntryProg.lean` compute them by addition.
-/

@[expose] public section

namespace GraphIso.Main

open Equiv Pointwise GraphIso GraphIso.Cost GraphIso.Graph Sims

/-! ### The points and the lift -/

section Lift

/-- The number of points: `n` vertices and `n · n` ordered pairs. -/
abbrev gN (n : ℕ) : ℕ := n + n * n

/-- The points: the vertex `u` is `u`, and the pair `(u, v)` is `n + (v + n u)`. -/
def ptEquiv (n : ℕ) : Fin n ⊕ (Fin n × Fin n) ≃ Fin (gN n) :=
  (Equiv.sumCongr (Equiv.refl _) finProdFinEquiv).trans finSumFinEquiv

theorem ptEquiv_inl (n : ℕ) (u : Fin n) : (ptEquiv n (.inl u)).val = u.val := by
  simp [ptEquiv]

theorem ptEquiv_inr (n : ℕ) (u v : Fin n) :
    (ptEquiv n (.inr (u, v))).val = n + (v.val + n * u.val) := by
  simp [ptEquiv]

/-- **The lift of `Sym(V)`**: `φ` on the vertices and `(u, v) ↦ (φ u, φ v)` on the pairs. -/
def liftPerm (n : ℕ) : Perm (Fin n) →* Perm (Fin (gN n)) where
  toFun φ := (ptEquiv n).permCongr (Equiv.sumCongr φ (Equiv.prodCongr φ φ))
  map_one' := by
    ext x
    obtain ⟨s, rfl⟩ := (ptEquiv n).surjective x
    rcases s with u | ⟨u, v⟩ <;> simp [Equiv.permCongr_apply]
  map_mul' φ ψ := by
    ext x
    obtain ⟨s, rfl⟩ := (ptEquiv n).surjective x
    rcases s with u | ⟨u, v⟩ <;> simp [Equiv.permCongr_apply, Perm.mul_apply]

theorem liftPerm_apply (n : ℕ) (φ : Perm (Fin n)) (s : Fin n ⊕ (Fin n × Fin n)) :
    liftPerm n φ (ptEquiv n s) = ptEquiv n (Sum.map φ (Prod.map φ φ) s) := by
  rcases s with u | ⟨u, v⟩ <;> simp [liftPerm, Equiv.permCongr_apply]

theorem liftPerm_inl (n : ℕ) (φ : Perm (Fin n)) (u : Fin n) :
    (liftPerm n φ (ptEquiv n (.inl u))).val = (φ u).val := by
  rw [liftPerm_apply]
  exact ptEquiv_inl n _

theorem liftPerm_inr (n : ℕ) (φ : Perm (Fin n)) (u v : Fin n) :
    (liftPerm n φ (ptEquiv n (.inr (u, v)))).val = n + ((φ v).val + n * (φ u).val) := by
  rw [liftPerm_apply]
  exact ptEquiv_inr n _ _

theorem liftPerm_injective (n : ℕ) : Function.Injective (liftPerm n) := by
  intro φ ψ h
  ext u
  have := congrArg (fun g : Perm (Fin (gN n)) => (g (ptEquiv n (.inl u))).val) h
  simpa only [liftPerm_inl] using this

/-- The lift on numbers, for a vertex map `f`. -/
def liftFun (n : ℕ) (f : ℕ → ℕ) (p : ℕ) : ℕ :=
  if p < n then f p else n + (f ((p - n) % n) + n * f ((p - n) / n))

theorem div_mod_pair {n u v : ℕ} (hv : v < n) :
    (v + n * u) % n = v ∧ (v + n * u) / n = u := by
  have hn : 0 < n := by omega
  refine ⟨?_, ?_⟩
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hv]
  · rw [Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt hv, Nat.zero_add]

/-- Every point is a vertex or a pair. -/
theorem pt_cases {n p : ℕ} (hp : p < gN n) :
    p < n ∨ ∃ u v, u < n ∧ v < n ∧ p = n + (v + n * u) := by
  unfold gN at hp
  by_cases h : p < n
  · exact Or.inl h
  · have hn : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; simp at hp)
    refine Or.inr ⟨(p - n) / n, (p - n) % n, ?_, Nat.mod_lt _ hn, ?_⟩
    · exact (Nat.div_lt_iff_lt_mul hn).2 (by omega)
    · have := Nat.mod_add_div (p - n) n
      omega

theorem liftFun_pair (n : ℕ) (f : ℕ → ℕ) {u v : ℕ} (hv : v < n) :
    liftFun n f (n + (v + n * u)) = n + (f v + n * f u) := by
  obtain ⟨h₁, h₂⟩ := div_mod_pair (u := u) hv
  simp only [liftFun, show ¬ n + (v + n * u) < n by omega, ↓reduceIte, Nat.add_sub_cancel_left,
    h₁, h₂]

/-- The lift in numbers: `act φ` lifted by `liftFun`. -/
theorem val_liftPerm (n : ℕ) (φ : Perm (Fin n)) (p : Fin (gN n)) :
    (liftPerm n φ p).val = liftFun n (act φ) p.val := by
  obtain ⟨s, rfl⟩ := (ptEquiv n).surjective p
  rcases s with u | ⟨u, v⟩
  · rw [liftPerm_inl, ptEquiv_inl, liftFun, Recursion.if_pos' u.2, act_of_lt _ u.2]
  · rw [liftPerm_inr, ptEquiv_inr, liftFun_pair _ _ v.2, act_of_lt _ u.2, act_of_lt _ v.2]

end Lift

/-! ### Writes -/

section Writes

/-- Membership in a list built by prepending blocks. -/
theorem mem_foldl_prepend {α β : Type} (F : β → List α) :
    ∀ (xs : List β) (acc : List α) (y : α),
      y ∈ xs.foldl (fun acc x => F x ++ acc) acc ↔ y ∈ acc ∨ ∃ x ∈ xs, y ∈ F x
  | [], acc, y => by simp
  | x :: xs, acc, y => by
    rw [List.foldl_cons, mem_foldl_prepend F xs, List.mem_append]
    simp only [List.mem_cons, exists_eq_or_imp]
    tauto

/-- The pair offsets: `n + n u` at `u`. -/
def offArr (n : ℕ) : Array ℕ := ((List.range n).map fun u => n + n * u).toArray

theorem get_offArr {n u : ℕ} (hu : u < n) : get (offArr n) u = n + n * u := by
  rw [offArr, get_toArray, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hu]
  rfl

theorem size_replicate_writes (m : ℕ) (ws : List (ℕ × ℕ)) :
    (Prim.applyWrites (a := .nat) (Array.replicate m 0) ws).size = m := by
  rw [size_applyWrites, Array.size_replicate]

end Writes

/-! ### Lifted permutation data -/

section LiftData

variable {n : ℕ}

/-- The block of writes of the vertex `u`: the vertex, then the pairs `(u, v)`. -/
def liftRow (n : ℕ) (o a : Array ℕ) (u : ℕ) : List (ℕ × ℕ) :=
  (u, get a u) :: (List.range n).map fun v => (get o u + v, get o (get a u) + get a v)

/-- The writes of the lifted array. -/
def liftWrites (n : ℕ) (o a : Array ℕ) : List (ℕ × ℕ) :=
  (List.range n).foldl (fun acc u => liftRow n o a u ++ acc) []

/-- The lift of an array of vertex images, with offsets `o`. -/
def liftArr (n : ℕ) (o a : Array ℕ) : Array ℕ :=
  Prim.applyWrites (a := .nat) (Array.replicate (gN n) 0) (liftWrites n o a)

theorem size_liftArr (n : ℕ) (o a : Array ℕ) : (liftArr n o a).size = gN n :=
  size_replicate_writes _ _

/-- The lift of permutation data. -/
def liftData (n : ℕ) (g : PermData) : PermData :=
  (liftArr n (offArr n) g.1, liftArr n (offArr n) g.2)

theorem get_liftArr {a : Array ℕ} (ψ : Perm (Fin n)) (ha : ∀ u < n, get a u = act ψ u)
    {p : ℕ} (hp : p < gN n) : get (liftArr n (offArr n) a) p = (liftPerm n ψ ⟨p, hp⟩).val := by
  have hlt : ∀ u < n, get a u < n := fun u hu => by
    rw [ha u hu, act_of_lt _ hu]
    exact (ψ _).2
  have hval : ∀ w ∈ liftWrites n (offArr n) a, w.2 = liftFun n (get a) w.1 := by
    intro w hw
    obtain h | ⟨u, hu, hw⟩ := (mem_foldl_prepend _ _ _ _).1 hw
    · simp at h
    · rw [List.mem_range] at hu
      rcases List.mem_cons.1 hw with rfl | hw
      · simp [liftFun, hu]
      · obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hw
        rw [List.mem_range] at hv
        simp only
        rw [get_offArr hu, get_offArr (hlt u hu), show n + n * u + v = n + (v + n * u) by ring,
          liftFun_pair _ _ hv]
        ring
  have hmem : p ∈ (liftWrites n (offArr n) a).map Prod.fst := by
    rw [List.mem_map]
    rcases pt_cases hp with h | ⟨u, v, hu, hv, rfl⟩
    · refine ⟨(p, get a p), (mem_foldl_prepend _ _ _ _).2 (Or.inr ⟨p, List.mem_range.2 h, ?_⟩),
        rfl⟩
      exact List.mem_cons_self
    · refine ⟨(get (offArr n) u + v, get (offArr n) (get a u) + get a v),
        (mem_foldl_prepend _ _ _ _).2 (Or.inr ⟨u, List.mem_range.2 hu, ?_⟩), ?_⟩
      · exact List.mem_cons_of_mem _ (List.mem_map.2 ⟨v, List.mem_range.2 hv, rfl⟩)
      · simp only
        rw [get_offArr hu]
        ring
  rw [liftArr, get_applyWrites_fun _ _ _ hval, Recursion.if_pos' ⟨hmem, by simpa using hp⟩,
    val_liftPerm]
  rcases pt_cases hp with h | ⟨u, v, hu, hv, rfl⟩
  · simp [liftFun, h, ha p h]
  · rw [liftFun_pair _ _ hv, liftFun_pair _ _ hv, ha u hu, ha v hv]

/-- **Lifted data is the data of the lift.** -/
theorem liftData_eq {g : PermData} (hg : g.Valid n) :
    liftData n g = PermData.ofPerm (liftPerm n (PermData.denote n g)) := by
  have h₁ : ∀ u < n, get g.1 u = act (PermData.denote n g) u := fun u hu => by
    rw [act_of_lt _ hu, PermData.val_denote_apply hg]
  have h₂ : ∀ u < n, get g.2 u = act (PermData.denote n g)⁻¹ u := fun u hu => by
    rw [act_of_lt _ hu, PermData.val_denote_inv_apply hg]
  refine Prod.ext (Array.ext ?_ fun p hp _ => ?_) (Array.ext ?_ fun p hp _ => ?_)
  · rw [liftData, size_liftArr]
    simp [PermData.ofPerm]
  · have hp' : p < gN n := by
      simp only [liftData] at hp
      rwa [size_liftArr] at hp
    rw [← get_eq_getElem hp, liftData, get_liftArr _ h₁ hp']
    simp [PermData.ofPerm]
  · rw [liftData, size_liftArr]
    simp [PermData.ofPerm]
  · have hp' : p < gN n := by
      simp only [liftData] at hp
      rwa [size_liftArr] at hp
    rw [← get_eq_getElem hp, liftData, get_liftArr _ h₂ hp']
    simp [PermData.ofPerm, map_inv]

theorem valid_liftData {g : PermData} (hg : g.Valid n) : (liftData n g).Valid (gN n) := by
  rw [liftData_eq hg]
  exact PermData.valid_ofPerm _

theorem denote_liftData {g : PermData} (hg : g.Valid n) :
    PermData.denote (gN n) (liftData n g) = liftPerm n (PermData.denote n g) := by
  rw [liftData_eq hg, PermData.denote_ofPerm]

end LiftData

/-! ### The strings -/

section Strings

variable {Δ n : ℕ} {X : GraphData}

/-- The writes of the string of `X`: `1` at the pairs `(u, v)` with `v` a neighbour of `u`. -/
def strWrites (n : ℕ) (o : Array ℕ) (X : GraphData) : List (ℕ × ℕ) :=
  (List.range n).foldl (fun acc u => (nbrs X u).map (fun v => (get o u + v, 1)) ++ acc) []

/-- **The string of `X`** on the `N` points. -/
def gStr (n : ℕ) (X : GraphData) : StrData :=
  Prim.applyWrites (a := .nat) (Array.replicate (gN n) 0) (strWrites n (offArr n) X)

theorem mem_strWrites {p : ℕ} :
    p ∈ (strWrites n (offArr n) X).map Prod.fst ↔
      ∃ u v, u < n ∧ Adj X u v ∧ p = n + (v + n * u) := by
  rw [List.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain h | ⟨u, hu, hw⟩ := (mem_foldl_prepend _ _ _ _).1 hw
    · simp at h
    · obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hw
      rw [List.mem_range] at hu
      refine ⟨u, v, hu, hv, ?_⟩
      simp only
      rw [get_offArr hu]
      ring
  · rintro ⟨u, v, hu, huv, rfl⟩
    refine ⟨(get (offArr n) u + v, 1),
      (mem_foldl_prepend _ _ _ _).2 (Or.inr ⟨u, List.mem_range.2 hu,
        List.mem_map.2 ⟨v, huv, rfl⟩⟩), ?_⟩
    simp only
    rw [get_offArr hu]
    ring

theorem get_gStr {p : ℕ} (hp : p < gN n) :
    get (gStr n X) p = if p ∈ (strWrites n (offArr n) X).map Prod.fst then 1 else 0 := by
  have hval : ∀ w ∈ strWrites n (offArr n) X, w.2 = (fun _ => 1) w.1 := by
    intro w hw
    obtain h | ⟨u, -, hw⟩ := (mem_foldl_prepend _ _ _ _).1 hw
    · simp at h
    · obtain ⟨v, -, rfl⟩ := List.mem_map.1 hw
      rfl
  rw [gStr, get_applyWrites_fun (fun _ => 1) _ _ hval, Array.size_replicate, get_replicate_zero]
  by_cases h : p ∈ (strWrites n (offArr n) X).map Prod.fst
  · rw [Recursion.if_pos' ⟨h, hp⟩, Recursion.if_pos' h]
  · rw [Recursion.if_neg' (fun h' => h h'.1), Recursion.if_neg' h]

theorem gStr_inl (u : Fin n) :
    StrData.denote (gN n) (gStr n X) (ptEquiv n (.inl u)) = 0 := by
  rw [StrData.denote, get_gStr (ptEquiv n (.inl u)).2, Recursion.if_neg']
  rw [mem_strWrites, ptEquiv_inl]
  rintro ⟨_, _, _, _, h⟩
  have := u.2
  omega

theorem gStr_inr (hX : X.ValidD Δ n) (u v : Fin n) :
    StrData.denote (gN n) (gStr n X) (ptEquiv n (.inr (u, v))) =
      if Adj X u v then 1 else 0 := by
  rw [StrData.denote, get_gStr (ptEquiv n (.inr (u, v))).2]
  refine if_congr ?_ rfl rfl
  rw [mem_strWrites, ptEquiv_inr]
  constructor
  · rintro ⟨u', v', hu', huv, h⟩
    have hv' := hX.lt _ _ huv
    obtain ⟨h₁, h₂⟩ := div_mod_pair (u := u') hv'
    obtain ⟨h₃, h₄⟩ := div_mod_pair (u := u.val) v.2
    have e : v.val + n * u.val = v' + n * u' := by omega
    rw [e] at h₃ h₄
    rw [h₁] at h₃
    rw [h₂] at h₄
    rw [← h₃, ← h₄]
    exact huv
  · intro h
    exact ⟨u, v, u.2, h, rfl⟩

end Strings

/-! ### The generators -/

section Gens

variable {n : ℕ}

/-- The forward images of the `n`-cycle `u ↦ u + 1 mod n`. -/
def rotF (n : ℕ) : Array ℕ :=
  Prim.applyWrites (a := .nat) ((List.range n).map (· + 1)).toArray [(n - 1, 0)]

/-- The inverse images of the `n`-cycle. -/
def rotI (n : ℕ) : Array ℕ :=
  Prim.applyWrites (a := .nat) ((List.range n).map (· - 1)).toArray [(0, n - 1)]

/-- The transposition of `0` and `1`. -/
def swF (n : ℕ) : Array ℕ :=
  Prim.applyWrites (a := .nat) (List.range n).toArray [(0, 1), (1, 0)]

theorem size_rotF (n : ℕ) : (rotF n).size = n := by
  rw [rotF, size_applyWrites]
  simp

theorem size_rotI (n : ℕ) : (rotI n).size = n := by
  rw [rotI, size_applyWrites]
  simp

theorem size_swF (n : ℕ) : (swF n).size = n := by
  rw [swF, size_applyWrites]
  simp

theorem get_range_toArray {u : ℕ} (hu : u < n) : get (List.range n).toArray u = u := by
  rw [get_toArray, List.getD_eq_getElem?_getD, List.getElem?_range hu]
  rfl

theorem get_write_one {l : List ℕ} {i v j : ℕ} (hj : j < l.length) :
    get (Prim.applyWrites (a := .nat) l.toArray [(i, v)]) j = if j = i then v else l[j] := by
  simp only [Prim.applyWrites, List.foldl_cons, List.foldl_nil]
  rw [get_setIfInBounds]
  by_cases h : j = i
  · subst h
    simp [hj]
  · rw [Recursion.if_neg' (fun h' => h h'.1), Recursion.if_neg' h, get_toArray,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    rfl

theorem get_rotF {u : ℕ} (hu : u < n) : get (rotF n) u = if u = n - 1 then 0 else u + 1 := by
  rw [rotF, get_write_one (by simpa using hu)]
  simp

theorem get_rotI {u : ℕ} (hu : u < n) : get (rotI n) u = if u = 0 then n - 1 else u - 1 := by
  rw [rotI, get_write_one (by simpa using hu)]
  simp

theorem get_swF {u : ℕ} (hu : u < n) :
    get (swF n) u = if u = 0 then 1 else if u = 1 then 0 else u := by
  simp only [swF, Prim.applyWrites, List.foldl_cons, List.foldl_nil]
  rw [get_setIfInBounds, get_setIfInBounds, Array.size_setIfInBounds]
  simp only [List.size_toArray, List.length_range]
  rcases (by omega : u = 0 ∨ u = 1 ∨ 2 ≤ u) with rfl | rfl | h
  · simp [show 0 < n by omega]
  · simp [show 1 < n by omega]
  · rw [Recursion.if_neg' (by omega), Recursion.if_neg' (by omega), Recursion.if_neg' (by omega),
      Recursion.if_neg' (by omega), get_range_toArray hu]

/-- The `n`-cycle as data. -/
theorem rot_eq (hn : 1 ≤ n) : (rotF n, rotI n) = PermData.ofPerm (finRotate n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hf : ∀ u (hu : u < m + 1), get (rotF (m + 1)) u = (finRotate (m + 1) ⟨u, hu⟩).val := by
    intro u hu
    rw [get_rotF hu, finRotate_apply, Fin.val_add_one]
    by_cases h : u = m
    · subst h
      simp [Fin.last]
    · rw [Recursion.if_neg' (by simpa using h),
        Recursion.if_neg' (by intro e; apply h; simpa [Fin.ext_iff] using e)]
  refine Prod.ext (Array.ext (by rw [size_rotF]; simp [PermData.ofPerm]) fun u hu _ => ?_)
    (Array.ext (by rw [size_rotI]; simp [PermData.ofPerm]) fun u hu _ => ?_)
  · have hu' : u < m + 1 := by rwa [size_rotF] at hu
    rw [← get_eq_getElem hu, hf u hu']
    simp [PermData.ofPerm]
  · have hu' : u < m + 1 := by rwa [size_rotI] at hu
    rw [← get_eq_getElem hu]
    simp only [PermData.ofPerm, Array.getElem_ofFn]
    have hw : get (rotI (m + 1)) u < m + 1 := by
      rw [get_rotI hu']
      split <;> omega
    have e : finRotate (m + 1) ⟨get (rotI (m + 1)) u, hw⟩ = ⟨u, hu'⟩ := by
      apply Fin.ext
      rw [← hf _ hw, get_rotF hw, get_rotI hu']
      by_cases h : u = 0
      · simp [h]
      · rw [Recursion.if_neg' h, Recursion.if_neg' (by omega)]
        show u - 1 + 1 = u
        omega
    rw [← e]
    simp

/-- The transposition of `0` and `1` as data. -/
theorem sw_eq (h2 : 2 ≤ n) :
    (swF n, swF n) = PermData.ofPerm (swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩) := by
  have hf : ∀ u (hu : u < n), get (swF n) u =
      (swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ ⟨u, hu⟩).val := by
    intro u hu
    rw [get_swF hu, swap_apply_def]
    by_cases h0 : u = 0
    · subst h0
      simp
    · by_cases h1 : u = 1
      · subst h1
        simp
      · rw [Recursion.if_neg' h0, Recursion.if_neg' h1,
          Recursion.if_neg' (by simpa [Fin.ext_iff] using h0),
          Recursion.if_neg' (by simpa [Fin.ext_iff] using h1)]
  refine Prod.ext (Array.ext (by rw [size_swF]; simp [PermData.ofPerm]) fun u hu _ => ?_)
    (Array.ext (by rw [size_swF]; simp [PermData.ofPerm]) fun u hu _ => ?_)
  · have hu' : u < n := by rwa [size_swF] at hu
    rw [← get_eq_getElem hu, hf u hu']
    simp [PermData.ofPerm]
  · have hu' : u < n := by rwa [size_swF] at hu
    rw [← get_eq_getElem hu, hf u hu']
    simp [PermData.ofPerm, swap_inv]

/-- **The generators**: the lifts of the `n`-cycle and of the transposition of `0` and `1`, none
for `n ≤ 1`. -/
def gensData (n : ℕ) : GensData :=
  if 1 < n then [liftData n (rotF n, rotI n), liftData n (swF n, swF n)] else []

theorem gensData_valid (n : ℕ) : GensData.AllValid (gN n) (gensData n) := by
  unfold gensData
  split
  · rename_i h
    refine GensData.AllValid.cons (valid_liftData ?_) (GensData.AllValid.cons
      (valid_liftData ?_) (GensData.allValid_nil _))
    · rw [rot_eq (by omega)]
      exact PermData.valid_ofPerm _
    · rw [sw_eq (by omega)]
      exact PermData.valid_ofPerm _
  · exact GensData.allValid_nil _

/-- **The generators generate the image of the lift.** -/
theorem gensData_denote (n : ℕ) : GensData.denote (gN n) (gensData n) = (liftPerm n).range := by
  unfold gensData
  split
  · rename_i h
    have hr : PermData.denote (gN n) (liftData n (rotF n, rotI n)) = liftPerm n (finRotate n) := by
      rw [denote_liftData (by rw [rot_eq (by omega)]; exact PermData.valid_ofPerm _),
        rot_eq (by omega), PermData.denote_ofPerm]
    have hs : PermData.denote (gN n) (liftData n (swF n, swF n)) =
        liftPerm n (swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩) := by
      rw [denote_liftData (by rw [sw_eq (by omega)]; exact PermData.valid_ofPerm _),
        sw_eq (by omega), PermData.denote_ofPerm]
    have h1 : finRotate n ⟨0, by omega⟩ = ⟨1, by omega⟩ := by
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
      apply Fin.ext
      rw [finRotate_apply]
      simp
    have htop := Perm.closure_cycle_adjacent_swap (isCycle_finRotate_of_le (by omega))
      (support_finRotate_of_le (by omega)) (⟨0, by omega⟩ : Fin n)
    rw [h1] at htop
    rw [GensData.denote, GensData.denoteSet_cons, GensData.denoteSet_cons,
      GensData.denoteSet_nil, hr, hs, MonoidHom.range_eq_map, ← htop, MonoidHom.map_closure]
    congr 1
    simp [Set.image_insert_eq]
  · rename_i h
    rw [GensData.denote, GensData.denoteSet_nil, Subgroup.closure_empty, eq_comm,
      MonoidHom.range_eq_bot_iff]
    ext φ p
    have : Subsingleton (Fin n) := Fin.subsingleton_iff_le_one.2 (by omega)
    simp [Subsingleton.elim φ 1]

end Gens

/-! ### The reduction -/

section Reduction

variable {Δ n : ℕ} {X Y : GraphData}

/-- **The reduction**: on the whole domain, in the image of the lift with the identity as
representative, the solutions are the lifts of the isomorphisms. -/
theorem iso_graph (hX : X.ValidD Δ n) (hY : Y.ValidD Δ n) :
    iso Set.univ 1 (liftPerm n).range (StrData.denote (gN n) (gStr n X))
        (StrData.denote (gN n) (gStr n Y)) = liftPerm n '' {φ | IsIso n X Y φ} := by
  ext g
  rw [mem_iso, inv_one, one_mul]
  constructor
  · rintro ⟨⟨φ, rfl⟩, hm⟩
    refine ⟨φ, fun u v hu hv => ?_, rfl⟩
    have := hm (ptEquiv n (.inr (⟨u, hu⟩, ⟨v, hv⟩))) (Set.mem_univ _)
    rw [gStr_inr hX, liftPerm_apply, Sum.map_inr, Prod.map_apply, gStr_inr hY] at this
    rw [act_of_lt _ hu, act_of_lt _ hv]
    by_cases h₁ : Adj X u v <;> by_cases h₂ : Adj Y (φ ⟨u, hu⟩) (φ ⟨v, hv⟩) <;>
      simp_all
  · rintro ⟨φ, hφ, rfl⟩
    refine ⟨⟨φ, rfl⟩, fun p _ => ?_⟩
    obtain ⟨s, rfl⟩ := (ptEquiv n).surjective p
    rcases s with u | ⟨u, v⟩
    · rw [gStr_inl, liftPerm_apply, Sum.map_inl, gStr_inl]
    · rw [gStr_inr hX, liftPerm_apply, Sum.map_inr, Prod.map_apply, gStr_inr hY]
      have := hφ u v u.2 v.2
      rw [act_of_lt _ u.2, act_of_lt _ v.2] at this
      simp only [Fin.eta] at this
      by_cases h₁ : Adj X u v <;> simp_all

end Reduction

/-! ### Decoding -/

section Decode

variable {n : ℕ}

/-- The first `n` entries of an array. -/
def restrictArr (n : ℕ) (a : Array ℕ) : Array ℕ := ((List.range n).map (get a)).toArray

/-- The restriction of permutation data to the first `n` points. -/
def restrictData (n : ℕ) (d : PermData) : PermData := (restrictArr n d.1, restrictArr n d.2)

theorem get_restrictArr {a : Array ℕ} {u : ℕ} (hu : u < n) : get (restrictArr n a) u = get a u := by
  rw [restrictArr, get_toArray, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hu]
  rfl

/-- **Restriction inverts the lift.** -/
theorem restrict_lift {d : PermData} (hd : d.Valid (gN n)) {φ : Perm (Fin n)}
    (h : PermData.denote (gN n) d = liftPerm n φ) : restrictData n d = PermData.ofPerm φ := by
  have hpt : ∀ u (hu : u < n),
      (⟨u, Nat.lt_of_lt_of_le hu (Nat.le_add_right _ _)⟩ : Fin (gN n)) = ptEquiv n (.inl ⟨u, hu⟩) :=
    fun u hu => Fin.ext (ptEquiv_inl n ⟨u, hu⟩).symm
  refine Prod.ext (Array.ext (by simp [restrictData, restrictArr, PermData.ofPerm])
    fun u hu _ => ?_) (Array.ext (by simp [restrictData, restrictArr, PermData.ofPerm])
    fun u hu _ => ?_)
  · have hu' : u < n := by simpa [restrictData, restrictArr] using hu
    rw [← get_eq_getElem hu, restrictData, get_restrictArr hu',
      ← PermData.val_denote_apply hd ⟨u, Nat.lt_of_lt_of_le hu' (Nat.le_add_right _ _)⟩, h,
      hpt u hu', liftPerm_inl]
    simp [PermData.ofPerm]
  · have hu' : u < n := by simpa [restrictData, restrictArr] using hu
    rw [← get_eq_getElem hu, restrictData, get_restrictArr hu',
      ← PermData.val_denote_inv_apply hd ⟨u, Nat.lt_of_lt_of_le hu' (Nat.le_add_right _ _)⟩, h,
      ← map_inv, hpt u hu', liftPerm_inl]
    simp [PermData.ofPerm]

/-- The decoded answer: the restrictions of the representative and of the generators. -/
def decodeAns {D : Cost.Ty} (n : ℕ) : AnswerData D → Option (PermData × GensData)
  | none => none
  | some (τ, H) => some (restrictData n τ, H.gens.map (restrictData n))

/-- **A correct answer of the graph problem**: `none` exactly when there is no isomorphism;
otherwise valid data of a coset `φ₀ • ⟨hs⟩`, with at most `(2N)²` generators, that is exactly
the set of isomorphisms from `X` to `Y`. -/
def GICosetOK (n : ℕ) (X Y : GraphData) (r : Option (PermData × GensData)) : Prop :=
  (r = none ↔ ¬ ∃ φ, IsIso n X Y φ) ∧
    ∀ τ hs, r = some (τ, hs) → τ.Valid n ∧ GensData.AllValid n hs ∧
      hs.length ≤ 2 * gN n * (2 * gN n) ∧
      {φ | IsIso n X Y φ} = PermData.denote n τ • (GensData.denote n hs : Set (Perm (Fin n)))

/-- A coset pulled back along an injective homomorphism. -/
theorem coset_pullback {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) {t : G} {T A : Set G} {S : Subgroup H}
    (h : f t • (S : Set H) = f '' A) (hT : Subgroup.closure (f '' T) = S) :
    A = t • (Subgroup.closure T : Set G) := by
  apply Set.image_injective.2 hf
  rw [← h, Set.image_smul_distrib, ← Subgroup.coe_map, MonoidHom.map_closure, hT]

variable {D : Cost.Ty} {DV : ℕ → GensData → D.denote → Prop} {Δ : ℕ} {X Y : GraphData}

/-- **Decoding a correct answer of the encoded instance.** -/
theorem decode_ok (hX : X.ValidD Δ n) (hY : Y.ValidD Δ n) {a : AnswerData D}
    (h : AnsOK DV (gN n) Set.univ 1 (liftPerm n).range (StrData.denote (gN n) (gStr n X))
      (StrData.denote (gN n) (gStr n Y)) a)
    (hg : ∀ c : CosetData D, a = some c → c.2.gens.length ≤ 2 * gN n * (2 * gN n)) :
    GICosetOK n X Y (decodeAns n a) := by
  rcases a with _ | ⟨τ, H⟩
  · have he : liftPerm n '' {φ | IsIso n X Y φ} = ∅ := by
      rw [← iso_graph hX hY]
      exact h
    refine ⟨⟨fun _ ⟨φ, hφ⟩ => ?_, fun _ => rfl⟩, fun _ _ h' => by cases h'⟩
    have : liftPerm n φ ∈ liftPerm n '' {φ | IsIso n X Y φ} := ⟨φ, hφ, rfl⟩
    rw [he] at this
    exact this
  · obtain ⟨hτ, -, ⟨hgv, -⟩, hset⟩ := h
    rw [iso_graph hX hY] at hset
    set T := PermData.denote (gN n) τ
    set S := GensData.denote (gN n) H.gens
    have hT : T ∈ liftPerm n '' {φ | IsIso n X Y φ} := by
      rw [← hset]
      exact ⟨1, S.one_mem, mul_one T⟩
    obtain ⟨φ₀, hφ₀, hφ₀T⟩ := hT
    have hgen : ∀ h ∈ H.gens, ∃ ψ, PermData.denote (gN n) h = liftPerm n ψ := by
      intro h hh
      have hm : T * PermData.denote (gN n) h ∈ liftPerm n '' {φ | IsIso n X Y φ} := by
        rw [← hset]
        exact ⟨_, Subgroup.subset_closure ⟨h, hh, rfl⟩, rfl⟩
      obtain ⟨ψ, -, hψ⟩ := hm
      refine ⟨φ₀⁻¹ * ψ, ?_⟩
      rw [map_mul, hψ, map_inv, hφ₀T, inv_mul_cancel_left]
    have hres : ∀ h ∈ H.gens, (restrictData n h).Valid n ∧
        liftPerm n (PermData.denote n (restrictData n h)) = PermData.denote (gN n) h := by
      intro h hh
      obtain ⟨ψ, hψ⟩ := hgen h hh
      rw [restrict_lift (hgv h hh) hψ, PermData.denote_ofPerm, hψ]
      exact ⟨PermData.valid_ofPerm _, rfl⟩
    have hτr : restrictData n τ = PermData.ofPerm φ₀ := restrict_lift hτ hφ₀T.symm
    refine ⟨⟨fun h' => (by cases h'), fun h' => absurd ⟨φ₀, hφ₀⟩ h'⟩, ?_⟩
    rintro τ' hs ⟨⟩
    refine ⟨by rw [hτr]; exact PermData.valid_ofPerm _, ?_, ?_, ?_⟩
    · intro g hg'
      obtain ⟨h, hh, rfl⟩ := List.mem_map.1 hg'
      exact (hres h hh).1
    · rw [List.length_map]
      exact hg _ rfl
    · rw [hτr, PermData.denote_ofPerm]
      refine coset_pullback (liftPerm n) (liftPerm_injective n) (by rw [hφ₀T]; exact hset) ?_
      congr 1
      ext g
      simp only [GensData.denoteSet, List.mem_map, Set.mem_image, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨_, ⟨_, ⟨h, hh, rfl⟩, rfl⟩, rfl⟩
        exact ⟨h, hh, (hres h hh).2.symm⟩
      · rintro ⟨h, hh, rfl⟩
        exact ⟨_, ⟨_, ⟨h, hh, rfl⟩, rfl⟩, (hres h hh).2⟩

end Decode

end GraphIso.Main
