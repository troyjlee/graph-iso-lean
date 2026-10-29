module

public import GraphIso.Case3.Model
public import GraphIso.Case3.Pipeline
public import GraphIso.Case2b.Link

/-!
# Case 3: the data pipeline is the model tree

Stage 14i (`PLAN-14.md` §13): the structures computed on data by `allStructsD` and
`firstStructD` (`Pipeline.lean`) are the reachable leaves of the model `case3Tree`
(`Model.lean`), for the base `Fin M`, the points `V` of `Γ ∖ S` listed without repetition
(numbered by `lkE`; for the increasing listing this is `eOf (univ \ S)`, `c3l_eFin_eq_eOf`) and
a colouring array `col` of the `k`-tuples (`c = toFun col`).

* `allStructsD_leafMs`: the decoded list of all structures is the leaf multiset of
  `case3Tree c (lkE V …)`. At a good list, the small-classes structure is the extended vertex
  colouring, and the structures of a dominant class are Split-or-UPCC on the restricted
  2-skeleton (`c3l_leaves_split`), numbered by the data along the base indices of the class; the
  numbering changes nothing (`splitTree_relabel'` with `σ = 1`, `c3l_dom_eq`).
* `firstStructD_reach`, `firstStructD_ne_none`: the first structure is a reachable leaf, and
  exists when no `t + 1` points are pairwise twins.
* `allStructsD_valid`, `firstStructD_valid`: every listed structure satisfies `OutValid`
  (colored partitions from the model; Johnson embeddings with stage 14h's data facts `LkJD`).
* `outSzD_le`: the `soj` tree built at a good list has size at most `sojZ M`.
* `twinsD_eq_false`, `htw_of_thresholds`: the twins flag is false without `t + 1` pairwise
  twins, which the thresholds of the interface supply (`no_twins_of_thresholds`) when
  `k ≤ t`.
* `firstStructD_partLe` (stage 14j-6b-1): without `t + 1` pairwise twins, a first structure that
  is not a Johnson one decodes to a colored `t`-partition with
  `t ≤ max ((|V| + 3) / 2) (M − thr |V| − 1)` (`case3Tree_partLe`).
-/

@[expose] public section

namespace GraphIso.Case3

open Equiv MulAction Pointwise Finset GraphIso GraphIso.SplitJohnson GraphIso.SoJProg
  GraphIso.SoJTree GraphIso.Coherent GraphIso.Align GraphIso.Case2b

/-! ### The numbering of a list -/

section Emb

variable {M : ℕ}

/-- The numbering of a duplicate-free list of base indices, as an embedding. -/
def lkE (L : List ℕ) (hL : ∀ v ∈ L, v < M) (hnd : L.Nodup) : Fin L.length ↪ Fin M :=
  ⟨eFin L hL, fun i j h => by
    have := congrArg Fin.val h
    simp only [eFin] at this
    exact Fin.ext ((List.Nodup.getElem_inj_iff hnd).1 this)⟩

theorem lkE_apply (L : List ℕ) (hL : ∀ v ∈ L, v < M) (hnd : L.Nodup) (i : Fin L.length) :
    lkE L hL hnd i = eFin L hL i := rfl

theorem lkE_val (L : List ℕ) (hL : ∀ v ∈ L, v < M) (hnd : L.Nodup) (i : Fin L.length) :
    (lkE L hL hnd i).val = L[i] := rfl

theorem lkE_range (L : List ℕ) (hL : ∀ v ∈ L, v < M) (hnd : L.Nodup) (v : Fin M) :
    (∃ i, lkE L hL hnd i = v) ↔ v.val ∈ L := by
  constructor
  · rintro ⟨i, rfl⟩
    exact List.getElem_mem _
  · intro hv
    obtain ⟨i, hi, hiv⟩ := List.getElem_of_mem hv
    exact ⟨⟨i, hi⟩, Fin.ext hiv⟩

theorem c3l_eInv (L : List ℕ) (hL : ∀ v ∈ L, v < M) (hnd : L.Nodup) (v : Fin M) :
    eInv L v = epre (lkE L hL hnd) v := by
  by_cases hv : v.val ∈ L
  · obtain ⟨i, hi, -, hiv⟩ := cp2_eInv_some hL hv
    rw [hi, eq_comm, epre_eq_some]
    exact hiv
  · rw [cp2_eInv_none hv, eq_comm, epre_eq_none]
    rintro i rfl
    exact hv (List.getElem_mem _)

/-- **The extension along the numbering is `extOut`.** -/
theorem c3l_pipeExt (L : List ℕ) (hL : ∀ v ∈ L, v < M) (hnd : L.Nodup)
    (o : Option (Out (Fin L.length))) :
    pipeExt (eFin L hL) (eInv L) o = extOut (lkE L hL hnd) o := by
  have hei : eInv L = epre (lkE L hL hnd) := funext (c3l_eInv L hL hnd)
  rw [hei]
  rcases o with _ | p | J
  · rfl
  · simp only [pipeExt, extOut, extPart, Option.some.injEq, Sum.inl.injEq, CPart.mk.injEq]
    refine ⟨rfl, funext fun v => ?_⟩
    rcases epre (lkE L hL hnd) v with _ | i
    · ext w
      simp only [mem_filter, mem_univ, true_and, mem_sdiff, mem_map, not_exists, epre_eq_none]
    · exact (Finset.map_eq_image (lkE L hL hnd) _).symm
  · simp only [pipeExt, extOut, extJohn, Option.some.injEq, Sum.inr.injEq, JEmb.mk.injEq]
    refine ⟨(Finset.map_eq_image (lkE L hL hnd) _).symm, ?_, trivial, funext fun v => ?_⟩
    · exact image_congr fun A _ => (Finset.map_eq_image (lkE L hL hnd) A).symm
    · rcases epre (lkE L hL hnd) v with _ | i
      · rfl
      · exact image_congr fun A _ => (Finset.map_eq_image (lkE L hL hnd) A).symm

theorem c3l_decodeOut_extD (L : List ℕ) (hL : ∀ v ∈ L, v < M) (hnd : L.Nodup) (o : OutD) :
    decodeOut M (extD M L o) = extOut (lkE L hL hnd) (decodeOut L.length o) := by
  rw [decodeOut_extD hL, c3l_pipeExt L hL hnd]

/-- **The increasing listing of `univ \ S` is numbered as `eOf (univ \ S)`.** -/
theorem c3l_eFin_eq_eOf (S : Finset (Fin M)) {V : List ℕ} (hV : ∀ v ∈ V, v < M)
    (hsort : V.Pairwise (· < ·)) (hset : ∀ v : Fin M, v.val ∈ V ↔ v ∉ S)
    (hlen : V.length = (univ \ S).card) (i : Fin V.length) :
    eFin V hV i = eOf (univ \ S) (Fin.cast hlen i) := by
  have hmono : StrictMono (eFin V hV) := fun i j hij => by
    show V[i.val] < V[j.val]
    exact List.pairwise_iff_getElem.1 hsort _ _ _ _ hij
  have hfs : ∀ i, eFin V hV i ∈ univ \ S := fun i => by
    rw [Finset.mem_sdiff]
    exact ⟨mem_univ _, (hset _).1 (List.getElem_mem _)⟩
  have h := Finset.orderEmbOfFin_unique hlen.symm hfs hmono
  rw [h]
  rfl

end Emb

/-! ### Split-or-UPCC on data -/

section Split

variable {M : ℕ}

/-- **The leaves of `leavesOfD`, extended along a list, are the leaves of Split-or-UPCC.** -/
theorem c3l_leaves_split (L : List ℕ) (hL : ∀ v ∈ L, v < M) (hnd : L.Nodup) (C : Array ℕ) :
    ((((leavesOfD L.length C).map (extD M L)).map (decodeOut M) :
        List (Option (Out (Fin M)))) : Multiset (Option (Out (Fin M)))) =
      (splitTree (colOf L.length C) (lkE L hL hnd)).leafMs := by
  rw [List.map_map,
    List.map_congr_left (f := decodeOut M ∘ extD M L)
      (g := extOut (lkE L hL hnd) ∘ decodeOut L.length)
      fun o _ => c3l_decodeOut_extD L hL hnd o, ← List.map_map, ← Multiset.map_coe]
  unfold splitTree
  by_cases hd : (disconn univ (colOf L.length C)).Nonempty
  · rw [dite_eq_left hd, leavesOfD_decode_comp _ _ hd]
    rfl
  · rw [dite_eq_right hd, leavesOfD_decode_soj _ _ (not_nonempty_iff_eq_empty.1 hd),
      CTree.leafMs_trans _ _ _ (chBack_chMap _), Multiset.map_map]
    rfl

end Split

/-! ### The structures of one good list -/

section Outcome

variable {M k : ℕ} {V : List ℕ}

theorem c3l_classA_lt (W : Array ℕ) (z : List ℕ) (u₀ : ℕ) :
    ∀ i ∈ classA (col1D k V.length W z) u₀, i < V.length := fun i hi => by
  have := lt_of_mem_classA hi
  rwa [length_col1D] at this

theorem c3l_classB_lt (hV : ∀ v ∈ V, v < M) (W : Array ℕ) (z : List ℕ) (u₀ : ℕ) :
    ∀ v ∈ classB V (classA (col1D k V.length W z) u₀), v < M :=
  classB_lt hV (c3l_classA_lt W z u₀)

theorem c3l_classB_nodup (hnd : V.Nodup) (W : Array ℕ) (z : List ℕ) (u₀ : ℕ) :
    (classB V (classA (col1D k V.length W z) u₀)).Nodup := by
  unfold classB
  refine (classA_nodup _ u₀).map_on fun i hi j hj hij => ?_
  have hi' := c3l_classA_lt W z u₀ i hi
  have hj' := c3l_classA_lt W z u₀ j hj
  rw [List.getD_eq_getElem _ _ hi', List.getD_eq_getElem _ _ hj'] at hij
  exact (List.Nodup.getElem_inj_iff hnd).1 hij

theorem c3l_classA_getD_lt (W : Array ℕ) (z : List ℕ) (u₀ : ℕ) {i : ℕ}
    (hi : i < (classA (col1D k V.length W z) u₀).length) :
    (classA (col1D k V.length W z) u₀).getD i 0 < V.length :=
  c3l_classA_lt W z u₀ _ (c3p_getD_mem hi)

/-- **At a dominant class, the data's Split-or-UPCC is the model's outcome.** -/
theorem c3l_dom_eq (hV : ∀ v ∈ V, v < M) (hnd : V.Nodup) (W : Array ℕ)
    (x : List (Fin V.length)) {u₀ : ℕ}
    (hsome : domA (col1D k V.length W (x.map Fin.val)) (tOf V.length) = some u₀) :
    splitTree (colOf (classB V (classA (col1D k V.length W (x.map Fin.val)) u₀)).length
        (skelCD k V.length W (x.map Fin.val) (classA (col1D k V.length W (x.map Fin.val)) u₀)
          (classB V (classA (col1D k V.length W (x.map Fin.val)) u₀)).length))
        (lkE (classB V (classA (col1D k V.length W (x.map Fin.val)) u₀))
          (c3l_classB_lt hV W _ u₀) (c3l_classB_nodup hnd W _ u₀)) =
      outTree (toFun (k := k) W) (lkE V hV hnd) x := by
  obtain ⟨hu, hcard⟩ := domA_col1D_some W x hsome
  set Cl := classA (col1D k V.length W (x.map Fin.val)) u₀ with hCl
  set L := classB V Cl with hL
  have hdom : (domPts (toFun (k := k) W) x).Nonempty := ⟨⟨u₀, hu⟩, mem_domPts.2 hcard⟩
  have hC : domCls (toFun (k := k) W) x hdom = cls1 (toFun (k := k) W) x ⟨u₀, hu⟩ :=
    domCls_eq hdom hcard
  have hsetCl : setOf V.length Cl = cls1 (toFun (k := k) W) x ⟨u₀, hu⟩ :=
    setOf_classA_col1D W x ⟨u₀, hu⟩
  have hClnd : Cl.Nodup := classA_nodup _ u₀
  have hCllt : ∀ i ∈ Cl, i < V.length := c3l_classA_lt W _ u₀
  have hlen : L.length = (domCls (toFun (k := k) W) x hdom).card := by
    rw [hL, length_classB, hC, ← hsetCl, lk_setOf_card hClnd hCllt]
  unfold outTree
  rw [dite_eq_left hdom]
  have h := splitTree_relabel' (1 : Perm (Fin M)) hlen
    (skelOn (toFun (k := k) W) x (domCls (toFun (k := k) W) x hdom))
    (colOf L.length (skelCD k V.length W (x.map Fin.val) Cl L.length))
    ((eOf (domCls (toFun (k := k) W) x hdom)).trans (lkE V hV hnd))
    (lkE L (c3l_classB_lt hV W _ u₀) (c3l_classB_nodup hnd W _ u₀)) (fun v => ?_)
    (fun u v u' v' hu' hv' => ?_)
  · rw [h, Case2b.lk_act_one]
  · rw [inv_one, Perm.one_apply, lkE_range]
    simp only [Function.Embedding.trans_apply]
    constructor
    · intro hv
      obtain ⟨i, hi, hiv⟩ := List.mem_map.1 hv
      have hiV := hCllt i hi
      have hmem : (⟨i, hiV⟩ : Fin V.length) ∈ domCls (toFun (k := k) W) x hdom := by
        rw [hC, ← hsetCl, mem_setOf]
        exact hi
      obtain ⟨j, hj⟩ := (mem_eOf_range _ _).2 hmem
      refine ⟨j, Fin.ext ?_⟩
      rw [hj, lkE_val, ← hiv, List.getD_eq_getElem _ _ hiV]
      rfl
    · rintro ⟨j, hj⟩
      obtain ⟨w, hw, hwj⟩ : ∃ w ∈ domCls (toFun (k := k) W) x hdom,
          eOf (domCls (toFun (k := k) W) x hdom) j = w := ⟨_, c3m_eOf_mem _ j, rfl⟩
      rw [hwj] at hj
      rw [hC, ← hsetCl, mem_setOf] at hw
      refine List.mem_map.2 ⟨_, hw, ?_⟩
      rw [← hj, lkE_val, List.getD_eq_getElem _ _ w.2]
      rfl
  · rw [Perm.one_apply] at hu' hv'
    simp only [Function.Embedding.trans_apply] at hu' hv'
    have hs : L.length ≤ Cl.length := by rw [hL, length_classB]
    rw [colOf_skelCD W x hCllt hs u' v']
    show _ = skel2 (toFun (k := k) W) x (eOf _ u) (eOf _ v)
    have key : ∀ (w : Fin L.length) (y : Fin V.length),
        lkE L (c3l_classB_lt hV W _ u₀) (c3l_classB_nodup hnd W _ u₀) w = lkE V hV hnd y →
        (⟨Cl.getD w 0, hCllt _ (c3p_getD_mem (by omega))⟩ : Fin V.length) = y := by
      intro w y hwy
      have hw : w.val < Cl.length := by omega
      have hb : Cl.getD w 0 < V.length := hCllt _ (c3p_getD_mem hw)
      have hval := congrArg Fin.val hwy
      rw [lkE_apply, eFin_classB_val, lkE_val, List.getD_eq_getElem _ _ hb] at hval
      exact Fin.ext ((List.Nodup.getElem_inj_iff hnd).1 hval)
    rw [key u' _ hu', key v' _ hv']

/-- **The structures of one list are the leaves of the model's outcome.** -/
theorem c3l_outcome (hV : ∀ v ∈ V, v < M) (hnd : V.Nodup) (col : Array ℕ)
    (x : List (Fin V.length)) :
    (((outcomeD M k V (wlCD k V.length col) (x.map Fin.val)).map (decodeOut M) :
        List (Option (Out (Fin M)))) : Multiset (Option (Out (Fin M)))) =
      (outTree (wl k V.length (toFun col)).1 (lkE V hV hnd) x).leafMs := by
  rw [← toFun_wlCD (k := k)]
  set W := wlCD k V.length col
  unfold outcomeD
  split
  · rename_i hnone
    have hall := (domA_col1D_none_iff W x).1 hnone
    have hdom : ¬ (domPts (toFun (k := k) W) x).Nonempty := by
      rintro ⟨u, hu⟩
      exact absurd (hall u) (not_le.2 (mem_domPts.1 hu))
    unfold outTree
    rw [dite_eq_right hdom]
    simp only [List.map_cons, List.map_nil, CTree.leafMs]
    rw [c3l_decodeOut_extD V hV hnd, col1D_eq, decodeOut_smallLeafD]
    rfl
  · rename_i u₀ hsome
    rw [← c3l_dom_eq hV hnd W x hsome]
    exact c3l_leaves_split _ _ _ _

end Outcome

/-! ### All structures -/

section All

variable {M k : ℕ} {V : List ℕ}

theorem c3l_good_iff {W : Array ℕ} {x : List (Fin V.length)} :
    DLGood (toFun (k := k) W) (thr V.length) x ↔ DesignGood (toFun (k := k) W) (tOf V.length) x :=
  Iff.rfl

/-- **The structures listed on data are the leaves of the model tree**, as multisets. -/
theorem allStructsD_leafMs (hV : ∀ v ∈ V, v < M) (hnd : V.Nodup) (col : Array ℕ) :
    (((allStructsD M k V col).map (decodeOut M) : List (Option (Out (Fin M)))) :
        Multiset (Option (Out (Fin M)))) =
      (case3Tree (toFun (k := k) col) (lkE V hV hnd)).leafMs := by
  unfold allStructsD
  rw [lk_flatMap_coe (goodListsD_nodup _)]
  simp only [case3Tree, CTree.leafMs]
  symm
  refine Finset.sum_bij (fun ch _ => (zOf (lkE V hV hnd) ch).map Fin.val)
    (fun ch hch => ?_) (fun ch hch ch' hch' h => ?_) (fun zd hzd => ?_) (fun ch hch => ?_)
  · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hch
    rw [zOf_zChoice, List.mem_toFinset]
    obtain ⟨hlt, hgood⟩ := Finset.mem_filter.1 hz
    refine mem_goodListsD.2 ⟨z, (SplitJohnson.BipRelabel.mem_tuplesLt.1 hlt).1, rfl, ?_⟩
    rw [toFun_wlCD]
    exact hgood
  · obtain ⟨z, -, rfl⟩ := Finset.mem_image.1 hch
    obtain ⟨z', -, rfl⟩ := Finset.mem_image.1 hch'
    rw [zOf_zChoice, zOf_zChoice] at h
    rw [goodListsD_decode_inj h]
  · obtain ⟨x, hx, rfl, hgood⟩ := mem_goodListsD.1 (List.mem_toFinset.1 hzd)
    refine ⟨zChoice (lkE V hV hnd) x, Finset.mem_image.2 ⟨x, Finset.mem_filter.2
      ⟨SplitJohnson.BipRelabel.mem_tuplesLt.2 ⟨hx, fun _ _ => mem_univ _⟩, ?_⟩,
      rfl⟩, ?_⟩
    · rw [← toFun_wlCD]
      exact hgood
    · rw [zOf_zChoice]
  · obtain ⟨z, -, rfl⟩ := Finset.mem_image.1 hch
    rw [zOf_zChoice]
    exact (c3l_outcome hV hnd col z).symm

/-- **The first structure is a reachable leaf of the model tree.** -/
theorem firstStructD_reach (hV : ∀ v ∈ V, v < M) (hnd : V.Nodup) (col : Array ℕ) {o : OutD}
    (h : firstStructD M k V col = some o) :
    (case3Tree (toFun (k := k) col) (lkE V hV hnd)).Reach (decodeOut M o) := by
  rw [← CTree.mem_leafMs, ← allStructsD_leafMs hV hnd col, Multiset.mem_coe]
  exact List.mem_map_of_mem (firstStructD_mem h)

/-- **The first structure exists** when no `t + 1` points are pairwise twins. -/
theorem firstStructD_ne_none (hV : ∀ v ∈ V, v < M) (hnd : V.Nodup) (col : Array ℕ)
    (hk : 2 ≤ k) (hm : 6 ≤ V.length)
    (htw : ∀ T : Finset (Fin V.length),
      (∀ u ∈ T, ∀ v ∈ T, IsTwin (toFun (k := k) col) u v) → T.card ≤ thr V.length) :
    firstStructD M k V col ≠ none := by
  have hne := goodListsD_ne_nil hk col htw
  unfold firstStructD
  rcases hg : goodListsD k V.length (wlCD k V.length col) with _ | ⟨zd, rest⟩
  · exact absurd hg hne
  have hzd : zd ∈ goodListsD k V.length (wlCD k V.length col) := by
    rw [hg]
    exact List.mem_cons_self
  obtain ⟨x, -, rfl, hgood⟩ := mem_goodListsD.1 hzd
  have hc := c3l_outcome (M := M) (k := k) hV hnd col x
  have hlive := (outTree_spec (wl k V.length (toFun col)).1 (wl_isCoherent _) (lkE V hV hnd) hm
    (by rw [← toFun_wlCD]; exact hgood)).1
  have hcount := (CTree.meas_size_live hlive).2
  show (outcomeD M k V (wlCD k V.length col) (x.map Fin.val)).head? ≠ none
  rw [Ne, List.head?_eq_none_iff]
  intro hnil
  rw [hnil, List.map_nil] at hc
  have h0 := congrArg Multiset.card hc
  rw [CTree.card_leafMs] at h0
  rw [← h0] at hcount
  simp at hcount

/-- Every listed Johnson structure has the data facts of stage 14h. -/
theorem c3l_shape (hV : ∀ v ∈ V, v < M) (hnd : V.Nodup) (col : Array ℕ) :
    ∀ o ∈ allStructsD M k V col, o.1 = 2 → LkJD M o.2.2 := by
  intro o ho h2
  obtain ⟨zd, -, ho⟩ := mem_allStructsD.1 ho
  unfold outcomeD at ho
  split at ho
  · rw [List.mem_singleton] at ho
    subst ho
    have := lk_extD_tag h2
    simp [smallLeafD, partD] at this
  · obtain ⟨o', ho', rfl⟩ := List.mem_map.1 ho
    have h2' := lk_extD_tag h2
    exact (lk_ext (c3l_classB_nodup hnd _ _ _) (c3l_classB_lt hV _ _ _) h2'
      (lk_leaves_shape _ o' ho' h2')).2

/-- **Every listed structure is valid** (`OutValid`), when no `t + 1` points are pairwise
twins. -/
theorem allStructsD_valid (hV : ∀ v ∈ V, v < M) (hnd : V.Nodup) (col : Array ℕ)
    (hk : 2 ≤ k) (hm : 6 ≤ V.length)
    (htw : ∀ T : Finset (Fin V.length),
      (∀ u ∈ T, ∀ v ∈ T, IsTwin (toFun (k := k) col) u v) → T.card ≤ thr V.length) :
    ∀ o ∈ allStructsD M k V col, OutValid M o := by
  intro o ho
  have hreach : (case3Tree (toFun (k := k) col) (lkE V hV hnd)).Reach (decodeOut M o) := by
    rw [← CTree.mem_leafMs, ← allStructsD_leafMs hV hnd col, Multiset.mem_coe]
    exact List.mem_map_of_mem ho
  exact lk_outValid (CTree.allLeaves_iff_reach.1
    (case3Tree_valid _ _ hk hm htw) _ hreach) (c3l_shape hV hnd col o ho)

/-- **The first structure is valid.** -/
theorem firstStructD_valid (hV : ∀ v ∈ V, v < M) (hnd : V.Nodup) (col : Array ℕ)
    (hk : 2 ≤ k) (hm : 6 ≤ V.length)
    (htw : ∀ T : Finset (Fin V.length),
      (∀ u ∈ T, ∀ v ∈ T, IsTwin (toFun (k := k) col) u v) → T.card ≤ thr V.length)
    {o : OutD} (h : firstStructD M k V col = some o) : OutValid M o :=
  allStructsD_valid hV hnd col hk hm htw o (firstStructD_mem h)

/-- **The first structure's partition is small** (stage 14j-6b-1, `PLAN-14.md` §14.11 item 1):
when no `t + 1` points are pairwise twins, a first structure that is not a Johnson structure
decodes to a colored `t`-partition of the base with
`t ≤ max ((|V| + 3) / 2) (M − thr |V| − 1)` (`case3Tree_partLe`). -/
theorem firstStructD_partLe (hV : ∀ v ∈ V, v < M) (hnd : V.Nodup) (col : Array ℕ)
    (hk : 2 ≤ k) (hm : 6 ≤ V.length)
    (htw : ∀ T : Finset (Fin V.length),
      (∀ u ∈ T, ∀ v ∈ T, IsTwin (toFun (k := k) col) u v) → T.card ≤ thr V.length)
    {o : OutD} (h : firstStructD M k V col = some o) (h2 : o.1 ≠ 2) :
    ∃ (p : CPart (Fin M)) (t : ℕ), decodeOut M o = some (Sum.inl p) ∧
      IsColPart univ t p ∧ t ≤ max ((V.length + 3) / 2) (M - thr V.length - 1) := by
  have h1 : o.1 = 1 := by
    rcases firstStructD_valid hV hnd col hk hm htw h with ⟨h1, -⟩ | ⟨h2', -⟩
    · exact h1
    · exact absurd h2' h2
  have hP := CTree.allLeaves_iff_reach.1 (case3Tree_partLe (toFun (k := k) col) (lkE V hV hnd)
    hm) _ (firstStructD_reach hV hnd col h)
  rw [ld_decodeOut_one h1] at hP ⊢
  obtain ⟨t, ht, hp⟩ := hP _ rfl
  rw [Fintype.card_fin] at ht
  exact ⟨_, t, rfl, hp, ht⟩

/-- **The `soj` tree built at a good list is small**: of size at most `sojZ M`. -/
theorem outSzD_le (hV : ∀ v ∈ V, v < M) (hnd : V.Nodup) (col : Array ℕ) (hm : 6 ≤ V.length)
    {zd : List ℕ} (hz : zd ∈ goodListsD k V.length (wlCD k V.length col)) :
    outSzD k V (wlCD k V.length col) zd ≤ sojZ M := by
  obtain ⟨x, -, rfl, hgood⟩ := mem_goodListsD.1 hz
  have hVM : V.length ≤ M := by
    have := lk_setOf_card hnd hV
    rw [← this]
    simpa using Finset.card_le_univ (setOf M V)
  unfold outSzD
  split
  · exact Nat.zero_le _
  · rename_i u₀ hsome
    have heq := c3l_dom_eq hV hnd (wlCD k V.length col) x hsome
    have hspec := outTree_spec (toFun (k := k) (wlCD k V.length col))
      (by rw [toFun_wlCD]; exact wl_isCoherent _) (lkE V hV hnd) hm hgood
    rw [← heq] at hspec
    obtain ⟨hlive, hcount, -⟩ := hspec
    set Cl := classA (col1D k V.length (wlCD k V.length col) (x.map Fin.val)) u₀
    set L := classB V Cl
    set C := skelCD k V.length (wlCD k V.length col) (x.map Fin.val) Cl L.length
    have hLm : L.length ≤ V.length := by
      simp only [L, length_classB, Cl, classA]
      exact (List.length_filter_le _ _).trans (by simp [length_col1D])
    unfold sojSz
    split
    · rename_i hnil
      have hd : ¬ (disconn univ (colOf L.length C)).Nonempty := by
        rw [disconn_wlCol, hnil]
        simp
      unfold splitTree at hlive hcount
      rw [dite_eq_right hd] at hlive hcount
      have hl := lk_live_of_trans (chBack_chMap _) hlive
      rw [CTree.cb_count_trans (chBack_chMap _)] at hcount
      have hpow : 2 ^ (129 * (Nat.clog 2 V.length + 2) ^ 2) ≤
          2 ^ (129 * (Nat.clog 2 M + 2) ^ 2) := by
        have := Nat.clog_mono_right 2 hVM
        exact Nat.pow_le_pow_right two_pos
          (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
      have key : ∀ (n : ℕ) (c : Fin n → Fin n → ℕ) (t : ℕ), (soj c t).Live →
          (soj c t).count ≤ 2 ^ (129 * (Nat.clog 2 M + 2) ^ 2) → n ≤ M →
          (soj c t).size ≤ sojZ M := by
        intro n c t hl' hc' hn
        have hh := height_soj_le c t
        rw [Fintype.card_fin] at hh
        refine (CTree.size_le_of_live hl').trans ?_
        unfold sojZ
        exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 (by omega)) hc'
      exact key _ _ _ hl (hcount.trans hpow) (hLm.trans hVM)
    · exact Nat.zero_le _

end All

/-! ### Twins -/

section Twins

variable {k m : ℕ}

/-- **The twins flag is false** when no `t + 1` points are pairwise twins. -/
theorem twinsD_eq_false (hk : 2 ≤ k) (col : Array ℕ)
    (htw : ∀ T : Finset (Fin m),
      (∀ u ∈ T, ∀ v ∈ T, IsTwin (toFun (k := k) col) u v) → T.card ≤ thr m) :
    twinsD k m col = false := by
  unfold twinsD
  rw [List.isEmpty_eq_false_iff]
  exact goodListsD_ne_nil hk col htw

/-- **No `t + 1` pairwise twins from the thresholds** (`no_twins_of_thresholds`), when
`k ≤ t`. -/
theorem htw_of_thresholds {Ω Γ : Type} [Fintype Ω] [DecidableEq Ω] [Fintype Γ]
    [DecidableEq Γ] {G : Subgroup (Perm Ω)} (φ : G →* Perm Γ) {L : Type*} {K : ℕ → ℕ}
    (x : Ω → L) (hT : Certificates.Thresholds K (Fintype.card Ω) k) (e : Fin m ↪ Γ)
    (hsupp : ∀ v, v ∉ Certificates.supp φ (Certificates.fullGroupK φ k x) ↔ ∃ i, e i = v)
    {c : (Fin k → Fin m) → ℕ}
    (hc : ∀ T T', c T = c T' ↔ Certificates.SameColour φ x (⇑e ∘ T) (⇑e ∘ T'))
    (hkt : k ≤ thr m) :
    ∀ T : Finset (Fin m), (∀ u ∈ T, ∀ v ∈ T, IsTwin c u v) → T.card ≤ thr m :=
  fun T hTw => (no_twins_of_thresholds φ x hT e hsupp hc T hTw).le.trans hkt

end Twins

end GraphIso.Case3
