module

public import GraphIso.Case2b.ChoiceProg
public import GraphIso.SoJProg.DLTest

/-!
# Case 3 on data: the structures of the Design Lemma

Stage 14i, item 4 (`PLAN-14.md` §13), the data level. The points of `V = Γ ∖ S` are the base
indices of the increasing list `V`, numbered `Fin m'` (`m' = |V|`). A colouring of the
`k`-tuples of `Fin m'` is an array in milestone 10's tuple-code order.

1. The `k`-ary Weisfeiler–Leman refinement (`wlCD`, milestone 10's `wlA`); its colour function is
   `wl` (`toFun_wlCD`).
2. The good lists: the candidates (lists of fewer than `k` points) where the conclusion of the
   Design Lemma holds for the refinement with threshold `t = (m' + 1) / 2` (`goodListsD`,
   stage 14c's `goodList`). Decoded, they are exactly the lists `x` with
   `DesignGood (wl k m' c).1 t x`, each once (`mem_goodListsD`, `goodListsD_nodup`).
3. At a good list `z`, the vertex colouring (`col1D`, milestone 10's `col1A`, decoding to
   `skel1`):
   * if every class has at most `t` points, the colored partition by the vertex colouring
     (`smallLeafD`, decoding to `colPart univ (skel1 …)`), extended to the base by stage 14h's
     `extD` along `V` (the rest, `S`, one block of colour `0`);
   * otherwise the dominant class `C` (the class of the least point of a class of more than `t`
     points, milestone 10's `classA`), the individualized 2-skeleton restricted to `C`
     (`skelCD`, decoding to `skel2`, `colOf_skelCD`), stage 14h's `leavesOfD` on it (the
     components of the least disconnected colour, or the trimmed leaves of `soj`), each
     extended to the base along the base indices of `C` (`classB`; the rest one block of
     colour `0`).
4. `allStructsD`: the structures over all good lists; `firstStructD`: the first structure of
   the first good list; `twinsD`: whether there is no good list, which happens only when the
   colouring has a class of more than `t` pairwise twins (`twinsD_spec`, from the Design
   Lemma).
-/

@[expose] public section

namespace GraphIso.Case3

open Finset GraphIso GraphIso.SplitJohnson GraphIso.SoJProg GraphIso.SoJTree GraphIso.Coherent
  GraphIso.Case2b

/-! ### Data -/

/-- The threshold `t = ⌈m'/2⌉`. -/
def tOf (m : ℕ) : ℕ := (m + 1) / 2

theorem le_two_mul_tOf (m : ℕ) : m ≤ 2 * tOf m := by
  unfold tOf
  omega

/-- The `k`-ary refinement of a colouring of the `k`-tuples of `Fin m`. -/
def wlCD (k m : ℕ) (col : Array ℕ) : Array ℕ := (wlA k m col).1

/-- The good lists of the refinement `W`. -/
def goodListsD (k m : ℕ) (W : Array ℕ) : List (List ℕ) := goodList W k m (tOf m)

/-- The vertex colouring at the digits `z`. -/
def col1D (k m : ℕ) (W : Array ℕ) (z : List ℕ) : List ℕ :=
  col1A W (pwTab k m) k m z.length z.toArray

/-- The colored partition by a vertex colouring: each class one block. -/
def smallLeafD (col : List ℕ) : OutD :=
  partD col.toArray ((List.range col.length).map (classA col)).toArray

/-- The base indices of a list of indices of `V`. -/
def classB (V C : List ℕ) : List ℕ := C.map fun i => V.getD i 0

/-- The individualized 2-skeleton at `z` restricted to the class `C` (indices of `Fin m`), as an
`s × s` row-major array. -/
def skelCD (k m : ℕ) (W : Array ℕ) (z C : List ℕ) (s : ℕ) : Array ℕ :=
  Toolkit.matrixOf s fun i j =>
    get W (codePad2 (pwTab k m) k z.length z.toArray (C.getD i 0) (C.getD j 0))

/-- **The structures at a good list `z`**, extended to the base `Fin m`. -/
def outcomeD (m k : ℕ) (V : List ℕ) (W : Array ℕ) (z : List ℕ) : List OutD :=
  match domA (col1D k V.length W z) (tOf V.length) with
  | none => [extD m V (smallLeafD (col1D k V.length W z))]
  | some u₀ =>
    (leavesOfD (classB V (classA (col1D k V.length W z) u₀)).length
      (skelCD k V.length W z (classA (col1D k V.length W z) u₀)
        (classB V (classA (col1D k V.length W z) u₀)).length)).map
      (extD m (classB V (classA (col1D k V.length W z) u₀)))

/-- The size of the `soj` tree built at `z` (`0` if none is built). -/
def outSzD (k : ℕ) (V : List ℕ) (W : Array ℕ) (z : List ℕ) : ℕ :=
  match domA (col1D k V.length W z) (tOf V.length) with
  | none => 0
  | some u₀ =>
    sojSz (classB V (classA (col1D k V.length W z) u₀)).length
      (skelCD k V.length W z (classA (col1D k V.length W z) u₀)
        (classB V (classA (col1D k V.length W z) u₀)).length)

/-- **All structures**: over all good lists of the refinement of `col`. -/
def allStructsD (m k : ℕ) (V : List ℕ) (col : Array ℕ) : List OutD :=
  (goodListsD k V.length (wlCD k V.length col)).flatMap (outcomeD m k V (wlCD k V.length col))

/-- **The first structure**: the first structure of the first good list. -/
def firstStructD (m k : ℕ) (V : List ℕ) (col : Array ℕ) : Option OutD :=
  match goodListsD k V.length (wlCD k V.length col) with
  | [] => none
  | z :: _ => (outcomeD m k V (wlCD k V.length col) z).head?

/-- **The twins flag**: no good list. -/
def twinsD (k m : ℕ) (col : Array ℕ) : Bool := (goodListsD k m (wlCD k m col)).isEmpty

/-! ### The refinement and the good lists -/

section Good

variable {k m : ℕ}

/-- **The refinement on data is `wl`.** -/
theorem toFun_wlCD (col : Array ℕ) : toFun (k := k) (wlCD k m col) = (wl k m (toFun col)).1 := by
  unfold wlCD
  rw [wlA_eq, toFun_arrOf]

/-- **The good lists are the lists where the Design Lemma's conclusion holds.** -/
theorem mem_goodListsD {W : Array ℕ} {xd : List ℕ} :
    xd ∈ goodListsD k m W ↔ ∃ x : List (Fin m), x.length < k ∧ xd = x.map Fin.val ∧
      DesignGood (toFun (k := k) W) (tOf m) x := by
  unfold goodListsD goodList
  rw [List.mem_filter]
  constructor
  · rintro ⟨hc, hg⟩
    obtain ⟨x, hx, rfl⟩ := mem_cands.1 hc
    exact ⟨x, hx, rfl, (goodA_iff W (le_two_mul_tOf m) x).1 hg⟩
  · rintro ⟨x, hx, rfl, hg⟩
    exact ⟨mem_cands.2 ⟨x, hx, rfl⟩, (goodA_iff W (le_two_mul_tOf m) x).2 hg⟩

theorem c3p_digits_injective : Function.Injective (digits (k := k) (m := m)) := by
  intro x y h
  unfold digits at h
  have h' := List.ofFn_injective h
  funext j
  exact Fin.ext (congrFun h' j)

theorem c3p_tupList_nodup (l m : ℕ) : (tupList l m).Nodup := by
  rw [tupList_eq]
  refine List.Nodup.map_on ?_ List.nodup_range
  intro a ha b hb h
  rw [List.mem_range] at ha hb
  rw [← digits_symm ⟨a, ha⟩, ← digits_symm ⟨b, hb⟩] at h
  have := finFunctionFinEquiv.symm.injective (c3p_digits_injective h)
  exact congrArg Fin.val this

theorem c3p_cands_nodup (k m : ℕ) : (cands k m).Nodup := by
  unfold cands
  rw [List.nodup_flatMap]
  refine ⟨fun l _ => c3p_tupList_nodup l m, ?_⟩
  refine List.nodup_range.pairwise_of_forall_ne fun a _ b _ hab => ?_
  rw [Function.onFun, List.disjoint_left]
  intro d hda hdb
  exact hab ((Coherent.length_of_mem_tupList hda).symm.trans
    (Coherent.length_of_mem_tupList hdb))

/-- **The good lists are listed once each.** -/
theorem goodListsD_nodup (W : Array ℕ) : (goodListsD k m W).Nodup :=
  (c3p_cands_nodup k m).filter _

/-- The good lists, as decoded lists of points, without repetition. -/
theorem goodListsD_decode_inj {x y : List (Fin m)}
    (h : x.map Fin.val = y.map Fin.val) : x = y :=
  List.map_injective_iff.2 Fin.val_injective h

/-- **No good list only with large twins** (milestone 10's Design Lemma): if every set of
pairwise twins of the colouring has at most `t` points, there is a good list. -/
theorem goodListsD_ne_nil (hk : 2 ≤ k) (col : Array ℕ)
    (htw : ∀ T : Finset (Fin m), (∀ u ∈ T, ∀ v ∈ T, IsTwin (toFun (k := k) col) u v) →
      T.card ≤ tOf m) :
    goodListsD k m (wlCD k m col) ≠ [] := by
  intro hnil
  obtain ⟨x, hx, hgood⟩ := design_lemma (V := Fin m) (t := tOf m) hk
    (wl_isCoherent (toFun col)) (by simpa using le_two_mul_tOf m) fun T hT =>
      htw T fun u hu v hv => (isTwin_wl_iff _ u v).1 (hT u hu v hv)
  have hmem : x.map Fin.val ∈ goodListsD k m (wlCD k m col) :=
    mem_goodListsD.2 ⟨x, hx, rfl, by rw [toFun_wlCD]; exact hgood⟩
  rw [hnil] at hmem
  simp at hmem

/-- **The twins outcome**: without a good list, the colouring has more than `t` pairwise
twins. -/
theorem twinsD_spec (hk : 2 ≤ k) (col : Array ℕ) (h : twinsD k m col = true) :
    ∃ T : Finset (Fin m), tOf m < T.card ∧
      ∀ u ∈ T, ∀ v ∈ T, IsTwin (toFun (k := k) col) u v := by
  by_contra hT
  push Not at hT
  refine goodListsD_ne_nil hk col (fun T hT' => ?_) (List.isEmpty_iff.1 h)
  by_contra hlt
  obtain ⟨u, hu, v, hv, hnt⟩ := hT T (not_le.1 hlt)
  exact hnt (hT' u hu v hv)

end Good

/-! ### The vertex colouring and the structures -/

section Outcome

variable {k m : ℕ}

theorem col1D_eq (W : Array ℕ) (x : List (Fin m)) :
    col1D k m W (x.map Fin.val) = (List.finRange m).map fun u => skel1 (toFun (k := k) W) x u := by
  unfold col1D
  rw [List.length_map]
  exact col1A_eq W x

theorem length_col1D (W : Array ℕ) (z : List ℕ) : (col1D k m W z).length = m :=
  length_col1A _ _ _ _ _ _

theorem c3p_get_toArray_finRange (f : Fin m → ℕ) (u : Fin m) :
    get ((List.finRange m).map f).toArray u.val = f u := by
  simp [get, Array.getD_eq_getD_getElem?]

theorem c3p_mem_classA_finRange (f : Fin m → ℕ) (u : Fin m) (w : ℕ) :
    w ∈ classA ((List.finRange m).map f) u ↔ ∃ hw : w < m, f ⟨w, hw⟩ = f u := by
  simp only [classA, List.mem_filter, List.mem_range, List.length_map, List.length_finRange,
    decide_eq_true_eq]
  constructor
  · rintro ⟨hw, he⟩
    refine ⟨hw, ?_⟩
    simpa [List.getD_eq_getElem?_getD, hw, u.2] using he
  · rintro ⟨hw, he⟩
    refine ⟨hw, ?_⟩
    simpa [List.getD_eq_getElem?_getD, hw, u.2] using he

theorem setOf_classA_finRange (f : Fin m → ℕ) (u : Fin m) :
    setOf m (classA ((List.finRange m).map f) u) = univ.filter fun w => f w = f u := by
  ext w
  rw [mem_setOf, c3p_mem_classA_finRange]
  simp

/-- **The small-classes structure decodes to the colored partition by the colouring.** -/
theorem decodeOut_smallLeafD (f : Fin m → ℕ) :
    decodeOut m (smallLeafD ((List.finRange m).map f)) = some (.inl (colPart univ f)) := by
  unfold smallLeafD
  rw [decodeOut_partD]
  simp only [cpartOf, colPart, Option.some.injEq, Sum.inl.injEq, CPart.mk.injEq]
  refine ⟨funext fun u => c3p_get_toArray_finRange f u, funext fun u => ?_⟩
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, ← List.getD_eq_getElem?_getD,
    List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_range]
  exact setOf_classA_finRange f u

/-- The classes of the vertex colouring are classes of milestone 10's `cls1`. -/
theorem setOf_classA_col1D (W : Array ℕ) (x : List (Fin m)) (u : Fin m) :
    setOf m (classA (col1D k m W (x.map Fin.val)) u) = cls1 (toFun (k := k) W) x u := by
  rw [col1D_eq, setOf_classA_finRange]
  rfl

theorem lt_of_mem_classA {col : List ℕ} {u w : ℕ} (h : w ∈ classA col u) : w < col.length := by
  simp only [classA, List.mem_filter, List.mem_range] at h
  exact h.1

theorem classA_nodup (col : List ℕ) (u : ℕ) : (classA col u).Nodup :=
  List.nodup_range.filter _

theorem classA_sorted (col : List ℕ) (u : ℕ) : (classA col u).Pairwise (· < ·) :=
  (List.pairwise_lt_range).filter _

theorem c3p_getD_mem {l : List ℕ} {i : ℕ} (h : i < l.length) : l.getD i 0 ∈ l := by
  rw [List.getD_eq_getElem _ _ h]
  exact List.getElem_mem h

theorem length_classB (V C : List ℕ) : (classB V C).length = C.length := List.length_map _

/-- **The vertex colouring has no large class** exactly when `domA` finds none. -/
theorem domA_col1D_none_iff (W : Array ℕ) (x : List (Fin m)) {t : ℕ} :
    domA (col1D k m W (x.map Fin.val)) t = none ↔ ∀ u, (cls1 (toFun (k := k) W) x u).card ≤ t := by
  rw [domA_eq_none, length_col1D]
  constructor
  · intro h u
    have := h u u.2
    unfold col1D at this
    rwa [List.length_map, cntA_eq] at this
  · intro h u hu
    have := h ⟨u, hu⟩
    unfold col1D
    rw [List.length_map, show u = (⟨u, hu⟩ : Fin m).val from rfl, cntA_eq]
    exact this

/-- **The dominant class**: `domA` returns a point of a class of more than `t` points. -/
theorem domA_col1D_some (W : Array ℕ) (x : List (Fin m)) {t u₀ : ℕ}
    (h : domA (col1D k m W (x.map Fin.val)) t = some u₀) :
    ∃ hu : u₀ < m, t < (cls1 (toFun (k := k) W) x ⟨u₀, hu⟩).card := by
  obtain ⟨hu, hc⟩ := domA_eq_some h
  rw [length_col1D] at hu
  refine ⟨hu, ?_⟩
  have := cntA_eq (k := k) W x ⟨u₀, hu⟩
  unfold col1D at hc
  rw [List.length_map] at hc
  rwa [this] at hc

/-- **The restricted 2-skeleton decodes to `skel2`.** -/
theorem colOf_skelCD (W : Array ℕ) (x : List (Fin m)) {C : List ℕ} (hC : ∀ v ∈ C, v < m)
    {s : ℕ} (hs : s ≤ C.length) (i j : Fin s) :
    colOf s (skelCD k m W (x.map Fin.val) C s) i j =
      skel2 (toFun (k := k) W) x ⟨C.getD i 0, hC _ (c3p_getD_mem (by omega))⟩
        ⟨C.getD j 0, hC _ (c3p_getD_mem (by omega))⟩ := by
  unfold colOf skelCD
  rw [Toolkit.get_matrixOf i.2 j.2, List.length_map]
  have h := codePad2_eq (k := k) x ⟨C.getD i 0, hC _ (c3p_getD_mem (by omega))⟩
    ⟨C.getD j 0, hC _ (c3p_getD_mem (by omega))⟩
  simp only at h
  rw [h]
  rfl

/-- The base indices of `C`, for indices of `V` below `|V|`, lie below `m` when `V` does. -/
theorem classB_lt {M : ℕ} {V C : List ℕ} (hV : ∀ v ∈ V, v < M) (hC : ∀ i ∈ C, i < V.length) :
    ∀ v ∈ classB V C, v < M := by
  intro v hv
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hv
  exact hV _ (c3p_getD_mem (hC i hi))

/-- The numbering of the base indices of `C` is `V` after `C`. -/
theorem eFin_classB_val {M : ℕ} {V C : List ℕ} (h : ∀ v ∈ classB V C, v < M)
    (i : Fin (classB V C).length) :
    (eFin (classB V C) h i).val = V.getD (C.getD i 0) 0 := by
  have hi : i.val < C.length := by simpa [length_classB] using i.2
  simp only [eFin, classB]
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_map _

/-- **The structures of a good list, small classes**: one structure, the extension of the
colored partition by the vertex colouring. -/
theorem outcomeD_small {M : ℕ} {V : List ℕ} (hV : ∀ v ∈ V, v < M) (W : Array ℕ)
    (x : List (Fin V.length))
    (h : domA (col1D k V.length W (x.map Fin.val)) (tOf V.length) = none) :
    (outcomeD M k V W (x.map Fin.val)).map (decodeOut M) =
      [pipeExt (eFin V hV) (eInv V)
        (some (.inl (colPart univ fun u => skel1 (toFun (k := k) W) x u)))] := by
  unfold outcomeD
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [decodeOut_extD hV, col1D_eq, decodeOut_smallLeafD]

/-- **The structures of a good list, a dominant class**: the leaves of stage 14h's `leavesOfD`
on the restricted 2-skeleton, extended along the base indices of the class. -/
theorem outcomeD_dom {M : ℕ} {V : List ℕ} (hV : ∀ v ∈ V, v < M) (W : Array ℕ) (z : List ℕ)
    {u₀ : ℕ} (h : domA (col1D k V.length W z) (tOf V.length) = some u₀) :
    (outcomeD M k V W z).map (decodeOut M) =
      ((leavesOfD (classB V (classA (col1D k V.length W z) u₀)).length
          (skelCD k V.length W z (classA (col1D k V.length W z) u₀)
            (classB V (classA (col1D k V.length W z) u₀)).length)).map
        (decodeOut (classB V (classA (col1D k V.length W z) u₀)).length)).map
        (pipeExt (eFin (classB V (classA (col1D k V.length W z) u₀))
          (classB_lt hV fun i hi => by
            have := lt_of_mem_classA hi
            rwa [length_col1D] at this))
          (eInv (classB V (classA (col1D k V.length W z) u₀)))) := by
  unfold outcomeD
  rw [h]
  simp only [List.map_map]
  refine List.map_congr_left fun o _ => ?_
  simp only [Function.comp]
  exact decodeOut_extD _ o

/-- The structures of a good list: at most one more than the `soj` size. -/
theorem length_outcomeD_le (M : ℕ) (V : List ℕ) (W : Array ℕ) (z : List ℕ) :
    (outcomeD M k V W z).length ≤ outSzD k V W z + 1 := by
  unfold outcomeD outSzD
  split
  · simp
  · rw [List.length_map]
    exact length_leavesOfD_le _ _

end Outcome

/-! ### All structures -/

section All

variable {k : ℕ}

theorem mem_allStructsD {M : ℕ} {V : List ℕ} {col : Array ℕ} {o : OutD} :
    o ∈ allStructsD M k V col ↔
      ∃ z ∈ goodListsD k V.length (wlCD k V.length col),
        o ∈ outcomeD M k V (wlCD k V.length col) z := by
  unfold allStructsD
  rw [List.mem_flatMap]

/-- The first structure is a structure of the first good list. -/
theorem firstStructD_mem {M : ℕ} {V : List ℕ} {col : Array ℕ} {o : OutD}
    (h : firstStructD M k V col = some o) : o ∈ allStructsD M k V col := by
  unfold firstStructD at h
  split at h
  · cases h
  · rename_i z zs hz
    rw [mem_allStructsD, hz]
    exact ⟨z, List.mem_cons_self, List.mem_of_mem_head? h⟩

theorem length_allStructsD_le (M : ℕ) (V : List ℕ) (col : Array ℕ) {Z : ℕ}
    (hZ : ∀ z ∈ goodListsD k V.length (wlCD k V.length col),
      outSzD k V (wlCD k V.length col) z ≤ Z) :
    (allStructsD M k V col).length ≤ k * (V.length ^ k + 1) * (Z + 1) := by
  unfold allStructsD
  rw [List.length_flatMap]
  have hlen : (goodListsD k V.length (wlCD k V.length col)).length ≤ k * (V.length ^ k + 1) :=
    (List.length_filter_le _ _).trans (length_cands_le k V.length)
  calc ((goodListsD k V.length (wlCD k V.length col)).map fun z =>
        (outcomeD M k V (wlCD k V.length col) z).length).sum
      ≤ ((goodListsD k V.length (wlCD k V.length col)).map fun _ => Z + 1).sum :=
        List.sum_le_sum fun z hz =>
          (length_outcomeD_le M V _ z).trans (Nat.add_le_add_right (hZ z hz) 1)
    _ = (goodListsD k V.length (wlCD k V.length col)).length * (Z + 1) := by
        rw [List.map_const', List.sum_replicate, smul_eq_mul]
    _ ≤ k * (V.length ^ k + 1) * (Z + 1) := Nat.mul_le_mul_right _ hlen

end All

end GraphIso.Case3
