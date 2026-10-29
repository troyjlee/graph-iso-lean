module

public import GraphIso.Case2b.Tree
public import GraphIso.Solver.Coherent
public import GraphIso.SplitJohnson.BipRelabelAux
public import GraphIso.SplitJohnson.BipartiteCount
public import GraphIso.Giant.FullGroup

/-!
# Case 3: the structures

Stage 14i, items 2–3 (`PLAN-14.md` §13), at the level of the model. Case 3 of the giant
macro-step: the support `S` of the full group has fewer than `m/2` points, and the ordered
`k`-tuples of `V = Γ ∖ S` are coloured by certificate equivalence. `V` is numbered by `Fin m'` in
increasing order (`e : Fin m' ↪ Γ`), and the colouring is `c : (Fin k → Fin m') → ℕ`.

* `case3Tree c e`: a node over the good lists `z` of the Design Lemma (milestone 11's `DLGood`,
  which is milestone 10's `DesignGood`, for the refinement `W = (wl k m' c).1` and the threshold
  `t = (m' + 1) / 2`), then the outcome at `z` (`outTree`):
  - if every vertex colour class at `z` has at most `t` points, the vertex colouring
    `colPart univ (skel1 W z)`, extended to `Γ` (`extPart`);
  - otherwise the dominant class `C` (the class of the least point with more than `t` points;
    it is the only class of more than `t` points), numbered by `Fin m''` in increasing order, and
    Split-or-UPCC on the restricted 2-skeleton `skel2 W z` (`splitTree`): the components of the
    least disconnected colour, or Split-or-Johnson with `t'' = (m'' + 3) / 2` and trimmed leaves;
    extended to `Γ` along `Fin m'' ↪ Fin m' ↪ Γ`.
* `case3Tree_relabel`: **naturality**. For a permutation `σ` of `Γ` carrying the numbered set
  of the first colouring onto that of the second, with `c₂ T' = c₁ T` whenever
  `e₂ ∘ T' = σ ∘ e₁ ∘ T`, the second tree is the first moved by `σ`. `case3_reach`: so `σ`
  carries every reachable leaf of the first tree to a reachable leaf of the second — the
  alignment hypothesis of `alignProg` for the consistently named colourings of `x` and `y`.
* `case3Tree_spec`: if no `t + 1` points are pairwise twins, the tree is live, every reachable
  leaf is valid (`ValidLeaf`, stage 14h), and its count is at most
  `m'^k · 2^(129 (⌈log₂ m'⌉ + 2)²)`.
* `no_twins_of_thresholds`: for the certificate colouring (`SameColour`) of the points outside
  the support of the full group, the thresholds of the CFSG-free interface leave fewer than `k`
  pairwise twins (milestone 13's `no_large_twins`).
* **The size of the partitions** (stage 14j-6b-1, `PLAN-14.md` §14.11 item 1): Split-or-UPCC's
  partition leaves have `t ≤ max ((n + 3) / 2) (|Γ| − n)` (`splitTree_partLe`); at a good list,
  on the dominant class of more than `thr m` points or the vertex colouring with classes of at
  most `thr m` points, `t ≤ max ((m + 3) / 2) (|Γ| − thr m − 1)` (`outTree_partLe`,
  `case3Tree_partLe`).
-/

@[expose] public section

namespace GraphIso.Case3

open Equiv MulAction Pointwise Finset GraphIso.SplitJohnson GraphIso.Coherent GraphIso.Recursion
  GraphIso.Align GraphIso.Case2b

/-! ### Split-or-UPCC on a classical configuration -/

section Split

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ] {n : ℕ}

/-- **Split-or-UPCC on a configuration of `Fin n`, extended along `e`**: the partition into the
components of the least disconnected colour, or Split-or-Johnson with trimmed leaves. -/
def splitTree (c : Fin n → Fin n → ℕ) (e : Fin n ↪ Γ) : STree Γ :=
  if h : (disconn univ c).Nonempty then
    .leaf (some (.inl (extPart e ⟨fun _ => 0, comp univ c ((disconn univ c).min' h)⟩)))
  else
    (soj c ((n + 3) / 2)).trans (chMap e) (chBack e) fun o => extOut e (trimOut o)

/-- Split-or-UPCC moves with a permutation of `Fin n` and a compatible permutation of `Γ`. -/
theorem splitTree_relabel (σ : Perm Γ) (π : Perm (Fin n)) (c : Fin n → Fin n → ℕ)
    {e e' : Fin n ↪ Γ} (he : ∀ i, e' (π i) = σ (e i)) :
    splitTree (relab2 π c) e' = (splitTree c e).act σ := by
  unfold splitTree
  have hdis : disconn univ (relab2 π c) = disconn univ c := by
    rw [← disconn_smul π univ c, Finset.smul_finset_univ]
  by_cases hd : (disconn univ c).Nonempty
  · have hd' : (disconn univ (relab2 π c)).Nonempty := hdis ▸ hd
    rw [dite_eq_left hd', dite_eq_left hd, cb_act_leaf, cb_smul_inl, ← extPart_relabel σ π he,
      compPart_relabel π c hd hd' hdis]
  · have hd' : ¬ (disconn univ (relab2 π c)).Nonempty := hdis ▸ hd
    rw [dite_eq_right hd', dite_eq_right hd, split_or_johnson_relabel]
    exact CTree.cb_act_trans π σ (chMap_relabel σ π he) (chBack_relabel σ π he)
      (fun o => by rw [trimOut_smul, extOut_relabel σ π he]) _

/-- **Split-or-UPCC is natural** for two numberings related through `σ`: if the second
embedding's range is the image under `σ` of the first's, and the configurations agree along
the induced bijection, the second tree is the first moved by `σ`. -/
theorem splitTree_relabel' (σ : Perm Γ) {n₁ n₂ : ℕ} (hn : n₂ = n₁) (c₁ : Fin n₁ → Fin n₁ → ℕ)
    (c₂ : Fin n₂ → Fin n₂ → ℕ) (e₁ : Fin n₁ ↪ Γ) (e₂ : Fin n₂ ↪ Γ)
    (hrange : ∀ v, (∃ j, e₂ j = v) ↔ ∃ i, e₁ i = σ⁻¹ v)
    (hc : ∀ u v u' v', e₂ u' = σ (e₁ u) → e₂ v' = σ (e₁ v) → c₂ u' v' = c₁ u v) :
    splitTree c₂ e₂ = (splitTree c₁ e₁).act σ := by
  subst hn
  have hex : ∀ i, ∃ j, e₂ j = σ (e₁ i) := fun i =>
    (hrange (σ (e₁ i))).2 ⟨i, by rw [perm_inv_apply_self]⟩
  choose fπ hfπ using hex
  have hinj : Function.Injective fπ := fun i j hij => by
    have := congrArg e₂ hij
    rw [hfπ, hfπ] at this
    exact e₁.injective (σ.injective this)
  set π : Perm (Fin n₂) := Equiv.ofBijective fπ (Finite.injective_iff_bijective.1 hinj)
  have he : ∀ i, e₂ (π i) = σ (e₁ i) := fun i => hfπ i
  have hcc : c₂ = relab2 π c₁ := by
    funext u' v'
    show c₂ u' v' = c₁ (π⁻¹ u') (π⁻¹ v')
    refine hc _ _ _ _ ?_ ?_
    · rw [← he, perm_apply_inv_self]
    · rw [← he, perm_apply_inv_self]
  rw [hcc]
  exact splitTree_relabel σ π c₁ he

omit [Fintype Γ] [DecidableEq Γ] in
/-- A homogeneous configuration that is not a clique, with no disconnected colour, is
uniprimitive. -/
theorem splitTree_uniprim {c : Fin n → Fin n → ℕ} (hhom : IsHomog univ c)
    (hncl : ¬ IsClique c univ) (hd : ¬ (disconn univ c).Nonempty) : IsUniprimitive univ c := by
  refine ⟨⟨hhom, fun r hr x _ y _ => ?_⟩, hncl⟩
  have hx : comp univ c r x = univ := by
    by_contra hne
    have hmem : r ∈ disconn univ c := by
      unfold disconn
      convert (Finset.mem_filter (s := offCols univ c)
        (p := fun r => ∃ x ∈ (univ : Finset (Fin n)), comp univ c r x ≠ univ)).2
        ⟨hr, x, Finset.mem_univ _, hne⟩
    exact hd ⟨r, hmem⟩
  have hy : y ∈ comp univ c r x := by
    rw [hx]
    exact Finset.mem_univ _
  exact (mem_comp.1 hy).2

/-- **Split-or-UPCC on a coherent homogeneous configuration that is not a clique** is live, its
leaves are valid, and its count is Split-or-Johnson's. -/
theorem splitTree_spec (c : Fin n → Fin n → ℕ) (e : Fin n ↪ Γ) (hn : 4 ≤ n)
    (hcoh : IsCoherent2 c) (hhom : IsHomog univ c) (hncl : ¬ IsClique c univ) :
    (splitTree c e).Live ∧ (splitTree c e).count ≤ 2 ^ (129 * (Nat.clog 2 n + 2) ^ 2) ∧
      (splitTree c e).AllLeaves ValidLeaf := by
  unfold splitTree
  by_cases hd : (disconn univ c).Nonempty
  · rw [dite_eq_left hd]
    exact ⟨trivial, Nat.one_le_two_pow, Or.inl ⟨_, _, rfl, extPart_valid e
      (GraphIso.SplitJohnson.isColPart_comp (GraphIso.SplitJohnson.isCoh2On_univ hcoh) hhom
        ((disconn univ _).min'_mem hd))⟩⟩
  · rw [dite_eq_right hd]
    have hu := splitTree_uniprim hhom hncl hd
    obtain ⟨hlive, hcount, hvalid⟩ := split_or_johnson hcoh hu
      (t := (n + 3) / 2) (by rw [Fintype.card_fin]; omega) (by rw [Fintype.card_fin]; omega)
    rw [Fintype.card_fin] at hcount
    refine ⟨CTree.cb_live_trans (chBack_chMap e) hlive,
      (CTree.cb_count_trans (chBack_chMap e) _).trans_le hcount, ?_⟩
    rw [SplitJohnson.CTree.allLeaves_iff_reach]
    intro o ho
    obtain ⟨o₀, ho₀, rfl⟩ := (CTree.cb_reach_trans (chBack_chMap e)).1 ho
    have hv := (SplitJohnson.CTree.allLeaves_iff_reach.1 hvalid) o₀ ho₀
    rcases o₀ with _ | p | J
    · exact hv.elim
    · exact Or.inl ⟨_, _, rfl, extPart_valid e hv⟩
    · have hdisj := soj_johnson_disjoint _ _ ho₀
      refine Or.inr ⟨_, _, rfl, extJohn_valid e (isJohnson_trimJ hv),
        extJohn_trim e (fun i hi => ?_), extJohn_disj e hdisj⟩
      show (if i ∈ J.V0 then J.f i else ∅) = ∅
      exact ite_eq_right_iff.2 fun h => absurd h hi

/-- **The size of Split-or-UPCC's partitions** (stage 14j-6b-1, `PLAN-14.md` §14.11 item 1):
every partition leaf is a colored `t`-partition with `t ≤ max ((n + 3) / 2) (|Γ| − n)`. -/
theorem splitTree_partLe (c : Fin n → Fin n → ℕ) (e : Fin n ↪ Γ) (hn : 4 ≤ n)
    (hcoh : IsCoherent2 c) (hhom : IsHomog univ c) (hncl : ¬ IsClique c univ) :
    (splitTree c e).AllLeaves (PartLe (max ((n + 3) / 2) (Fintype.card Γ - n))) := by
  unfold splitTree
  by_cases hd : (disconn univ c).Nonempty
  · rw [dite_eq_left hd]
    intro p hp
    cases Sum.inl.inj (Option.some.inj hp)
    refine extPart_partLe e (GraphIso.SplitJohnson.isColPart_comp
      (GraphIso.SplitJohnson.isCoh2On_univ hcoh) hhom ((disconn univ _).min'_mem hd)) ?_
    rw [card_univ, Fintype.card_fin]
    omega
  · rw [dite_eq_right hd]
    obtain ⟨-, -, hvalid⟩ := split_or_johnson hcoh (splitTree_uniprim hhom hncl hd)
      (t := (n + 3) / 2) (by rw [Fintype.card_fin]; omega) (by rw [Fintype.card_fin]; omega)
    rw [SplitJohnson.CTree.allLeaves_iff_reach]
    intro o ho
    obtain ⟨o₀, ho₀, rfl⟩ := (CTree.cb_reach_trans (chBack_chMap e)).1 ho
    have hv := (SplitJohnson.CTree.allLeaves_iff_reach.1 hvalid) o₀ ho₀
    rcases o₀ with _ | p | J
    · intro p hp
      cases hp
    · intro p' hp'
      cases Sum.inl.inj (Option.some.inj hp')
      exact extPart_partLe e hv le_rfl
    · intro p hp
      cases hp

end Split

/-! ### The outcome at a good list -/

section Outcome

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ] {k m : ℕ}

/-- The threshold `t = (m + 1) / 2`. -/
def thr (m : ℕ) : ℕ := (m + 1) / 2

/-- The points whose vertex colour class at `z` has more than `t` points. -/
def domPts (W : (Fin k → Fin m) → ℕ) (z : List (Fin m)) : Finset (Fin m) :=
  univ.filter fun u => thr m < (cls1 W z u).card

/-- **The dominant class** at `z`: the class of the least point of a class of more than `t`
points. -/
def domCls (W : (Fin k → Fin m) → ℕ) (z : List (Fin m)) (h : (domPts W z).Nonempty) :
    Finset (Fin m) :=
  cls1 W z ((domPts W z).min' h)

/-- The 2-skeleton at `z` restricted to `C`, numbered increasingly. -/
def skelOn (W : (Fin k → Fin m) → ℕ) (z : List (Fin m)) (C : Finset (Fin m)) :
    Fin C.card → Fin C.card → ℕ :=
  fun u v => skel2 W z (eOf C u) (eOf C v)

/-- **The outcome at the list `z`**, extended to `Γ` along `e`: Split-or-UPCC on the dominant
class, or the vertex colouring when every class has at most `t` points. -/
def outTree (W : (Fin k → Fin m) → ℕ) (e : Fin m ↪ Γ) (z : List (Fin m)) : STree Γ :=
  if h : (domPts W z).Nonempty then
    splitTree (skelOn W z (domCls W z h)) ((eOf (domCls W z h)).trans e)
  else .leaf (some (.inl (extPart e (colPart univ (skel1 W z)))))

omit [Fintype Γ] [DecidableEq Γ] in
theorem mem_cls1 {W : (Fin k → Fin m) → ℕ} {z : List (Fin m)} {u w : Fin m} :
    w ∈ cls1 W z u ↔ skel1 W z w = skel1 W z u := by
  simp [cls1]

omit [Fintype Γ] [DecidableEq Γ] in
/-- **The dominant class is unique**: two classes of more than `t = (m + 1) / 2` points are
equal. -/
theorem cls1_eq_of_dom {W : (Fin k → Fin m) → ℕ} {z : List (Fin m)} {u u' : Fin m}
    (hu : thr m < (cls1 W z u).card) (hu' : thr m < (cls1 W z u').card) :
    cls1 W z u = cls1 W z u' := by
  by_cases h : skel1 W z u = skel1 W z u'
  · ext w
    rw [mem_cls1, mem_cls1, h]
  · exfalso
    have hdisj : Disjoint (cls1 W z u) (cls1 W z u') := by
      rw [Finset.disjoint_left]
      intro w hw hw'
      rw [mem_cls1] at hw hw'
      exact h (hw.symm.trans hw')
    have hcard := Finset.card_union_of_disjoint hdisj
    have hle : (cls1 W z u ∪ cls1 W z u').card ≤ m := by
      simpa using Finset.card_le_univ (cls1 W z u ∪ cls1 W z u')
    unfold thr at hu hu'
    omega

omit [Fintype Γ] [DecidableEq Γ] in
theorem mem_domPts {W : (Fin k → Fin m) → ℕ} {z : List (Fin m)} {u : Fin m} :
    u ∈ domPts W z ↔ thr m < (cls1 W z u).card := by
  simp [domPts]

omit [Fintype Γ] [DecidableEq Γ] in
/-- The dominant class is the class of any point of a class of more than `t` points. -/
theorem domCls_eq {W : (Fin k → Fin m) → ℕ} {z : List (Fin m)} (h : (domPts W z).Nonempty)
    {u : Fin m} (hu : thr m < (cls1 W z u).card) : domCls W z h = cls1 W z u :=
  cls1_eq_of_dom (mem_domPts.1 ((domPts W z).min'_mem h)) hu

/-! #### Naturality -/

variable (σ : Perm Γ) (π : Perm (Fin m)) {W₁ W₂ : (Fin k → Fin m) → ℕ}

omit [Fintype Γ] [DecidableEq Γ] in
theorem cls1_relabel (hW : ∀ y, W₂ (⇑π ∘ y) = W₁ y) (z : List (Fin m)) (u : Fin m) :
    cls1 W₂ (z.map π) (π u) = (cls1 W₁ z u).map (π : Fin m ≃ Fin m).toEmbedding :=
  SplitJohnson.BipRelabel.cls1_map (π : Fin m ≃ Fin m) hW z u

omit [Fintype Γ] [DecidableEq Γ] in
theorem domPts_relabel (hW : ∀ y, W₂ (⇑π ∘ y) = W₁ y) (z : List (Fin m)) (u : Fin m) :
    π u ∈ domPts W₂ (z.map π) ↔ u ∈ domPts W₁ z := by
  rw [mem_domPts, mem_domPts, cls1_relabel π hW, Finset.card_map]

omit [Fintype Γ] [DecidableEq Γ] in
theorem domPts_nonempty_relabel (hW : ∀ y, W₂ (⇑π ∘ y) = W₁ y) (z : List (Fin m)) :
    (domPts W₂ (z.map π)).Nonempty ↔ (domPts W₁ z).Nonempty := by
  constructor
  · rintro ⟨u, hu⟩
    rw [← perm_apply_inv_self π u, domPts_relabel π hW] at hu
    exact ⟨_, hu⟩
  · rintro ⟨u, hu⟩
    exact ⟨π u, (domPts_relabel π hW z u).2 hu⟩

omit [Fintype Γ] [DecidableEq Γ] in
theorem domCls_relabel (hW : ∀ y, W₂ (⇑π ∘ y) = W₁ y) (z : List (Fin m))
    (h₁ : (domPts W₁ z).Nonempty) (h₂ : (domPts W₂ (z.map π)).Nonempty) :
    domCls W₂ (z.map π) h₂ = (domCls W₁ z h₁).map (π : Fin m ≃ Fin m).toEmbedding := by
  set u₂ := (domPts W₂ (z.map π)).min' h₂
  have hu₂ : π (π⁻¹ u₂) ∈ domPts W₂ (z.map π) := by
    rw [perm_apply_inv_self]
    exact (domPts W₂ (z.map π)).min'_mem h₂
  have hu₁ : π⁻¹ u₂ ∈ domPts W₁ z := (domPts_relabel π hW z _).1 hu₂
  show cls1 W₂ (z.map π) u₂ = _
  rw [← perm_apply_inv_self π u₂, cls1_relabel π hW, domCls_eq h₁ (mem_domPts.1 hu₁)]

omit [Fintype Γ] [DecidableEq Γ] in
theorem colPart_relabel (hW : ∀ y, W₂ (⇑π ∘ y) = W₁ y) (z : List (Fin m)) :
    colPart univ (skel1 W₂ (z.map π)) = π • colPart univ (skel1 W₁ z) := by
  have hs : ∀ v, skel1 W₂ (z.map π) v = skel1 W₁ z (π⁻¹ v) := fun v => by
    rw [← SplitJohnson.BipRelabel.skel1_map (π : Fin m ≃ Fin m) hW z (π⁻¹ v)]
    simp
  rw [cb_cpart_smul]
  show CPart.mk _ _ = CPart.mk _ _
  congr 1
  · funext v
    exact hs v
  · funext v
    ext w
    simp only [colPart, mem_filter, mem_univ, true_and, hs, Finset.mem_smul_finset,
      Perm.smul_def]
    constructor
    · intro hw
      exact ⟨π⁻¹ w, hw, perm_apply_inv_self π w⟩
    · rintro ⟨w₀, hw₀, rfl⟩
      rwa [perm_inv_apply_self]

/-- **The outcome is natural**: relabelling the structure and the list by `π`, and `Γ` by `σ`
compatibly with the embeddings, moves the outcome by `σ`. -/
theorem outTree_relabel (hW : ∀ y, W₂ (⇑π ∘ y) = W₁ y) {e₁ e₂ : Fin m ↪ Γ}
    (he : ∀ i, e₂ (π i) = σ (e₁ i)) (z : List (Fin m)) :
    outTree W₂ e₂ (z.map π) = (outTree W₁ e₁ z).act σ := by
  unfold outTree
  by_cases h₁ : (domPts W₁ z).Nonempty
  · have h₂ : (domPts W₂ (z.map π)).Nonempty := (domPts_nonempty_relabel π hW z).2 h₁
    rw [dite_eq_left h₂, dite_eq_left h₁]
    have hC := domCls_relabel π hW z h₁ h₂
    refine splitTree_relabel' σ (by rw [hC, Finset.card_map]) _ _ _ _ (fun v => ?_)
      (fun u v u' v' hu hv => ?_)
    · simp only [Function.Embedding.trans_apply]
      constructor
      · rintro ⟨j, rfl⟩
        obtain ⟨w, hw, hwj⟩ : ∃ w ∈ domCls W₂ (z.map π) h₂,
            eOf (domCls W₂ (z.map π) h₂) j = w :=
          ⟨_, (mem_eOf_range _ _).1 ⟨j, rfl⟩, rfl⟩
        rw [hwj]
        rw [hC, Finset.mem_map_equiv] at hw
        obtain ⟨i, hi⟩ := (mem_eOf_range (domCls W₁ z h₁) _).2 hw
        refine ⟨i, ?_⟩
        rw [hi]
        have := he (π.symm w)
        rw [show π (π.symm w) = w from π.apply_symm_apply w] at this
        rw [this, perm_inv_apply_self]
      · rintro ⟨i, hi⟩
        have hmem : π (eOf (domCls W₁ z h₁) i) ∈ domCls W₂ (z.map π) h₂ := by
          rw [hC, Finset.mem_map_equiv]
          simpa using (mem_eOf_range _ _).1 ⟨i, rfl⟩
        obtain ⟨j, hj⟩ := (mem_eOf_range _ _).2 hmem
        refine ⟨j, ?_⟩
        rw [hj, he, hi, perm_apply_inv_self]
    · simp only [Function.Embedding.trans_apply] at hu hv
      rw [← he] at hu hv
      have hu' := e₂.injective hu
      have hv' := e₂.injective hv
      show skel2 W₂ (z.map π) _ _ = skel2 W₁ z _ _
      rw [hu', hv']
      exact SplitJohnson.BipRelabel.skel2_map (π : Fin m ≃ Fin m) hW z _ _
  · have h₂ : ¬ (domPts W₂ (z.map π)).Nonempty := fun h =>
      h₁ ((domPts_nonempty_relabel π hW z).1 h)
    rw [dite_eq_right h₂, dite_eq_right h₁, cb_act_leaf, cb_smul_inl, ← extPart_relabel σ π he,
      colPart_relabel π hW z]

end Outcome

/-! ### Validity of the outcome -/

section OutcomeSpec

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ] {k m : ℕ}

omit [Fintype Γ] [DecidableEq Γ] in
/-- A colouring whose classes have at most `t` points is a colored `t`-partition, each class one
block. -/
theorem c3m_isColPart_colPart {V : Type*} [Fintype V] [DecidableEq V] (f : V → ℕ) {t : ℕ}
    (h : ∀ u, (univ.filter fun w => f w = f u).card ≤ t) : IsColPart univ t (colPart univ f) where
  mem_blk v _ := by simp [colPart]
  blk_sub _ _ := subset_univ _
  blk_eq v _ w hw := by
    simp only [colPart, mem_filter, mem_univ, true_and] at hw ⊢
    ext y
    simp [hw]
  col_eq v _ w hw := by simpa [colPart] using hw
  card_eq v _ w _ hvw := by
    show (univ.filter fun y => f y = f v).card = (univ.filter fun y => f y = f w).card
    rw [show f v = f w from hvw]
  admissible v _ h1 w _ hw := by
    have hw' : w ∈ (colPart univ f).blk v := by simpa [colPart] using hw
    have hv : v ∈ (colPart univ f).blk v := by simp [colPart]
    obtain ⟨a, ha⟩ := Finset.card_eq_one.1 h1
    rw [ha, Finset.mem_singleton] at hw' hv
    rw [hw', hv]
  card_le v _ := h v

omit [Fintype Γ] [DecidableEq Γ] in
/-- Classical coherent configurations move along bijections. -/
theorem c3m_isCoherent2_equiv {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β)
    {c : β → β → ℕ} (hc : IsCoherent2 c) : IsCoherent2 fun u v => c (e u) (e v) := by
  refine ⟨fun x y x' y' h => ?_, fun x y x' y' h r s => ?_⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hc.1 _ _ _ _ h
    exact ⟨by rw [← e.injective.eq_iff, h1, e.injective.eq_iff], h2, h3, h4⟩
  · have := hc.2 _ _ _ _ h r s
    rw [Finset.card_equiv e (t := univ.filter fun w => c (e x) w = r ∧ c w (e y) = s)
      (fun i => by simp), Finset.card_equiv e
      (t := univ.filter fun w => c (e x') w = r ∧ c w (e y') = s) (fun i => by simp)]
    exact this

/-- The increasing numbering of a finite set of `Fin m`, as an equivalence with a subtype
describing it. -/
def c3m_eqv (C : Finset (Fin m)) (P : Fin m → Prop) (hP : ∀ w, w ∈ C ↔ P w) :
    Fin C.card ≃ {w // P w} :=
  (C.orderIsoOfFin rfl).toEquiv.trans (Equiv.subtypeEquivRight hP)

omit [Fintype Γ] [DecidableEq Γ] in
theorem c3m_eqv_apply (C : Finset (Fin m)) (P : Fin m → Prop) (hP : ∀ w, w ∈ C ↔ P w)
    (u : Fin C.card) : (c3m_eqv C P hP u : Fin m) = eOf C u := rfl

omit [Fintype Γ] [DecidableEq Γ] in
theorem c3m_eOf_mem (C : Finset (Fin m)) (u : Fin C.card) : eOf C u ∈ C :=
  (mem_eOf_range C _).1 ⟨u, rfl⟩

omit [Fintype Γ] [DecidableEq Γ] in
/-- **The dominant class at a good list**: more than `t` (so at least four) of the `m` points,
and the restricted 2-skeleton is coherent, homogeneous and not a clique. -/
theorem outTree_dom (W : (Fin k → Fin m) → ℕ) (hW : IsCoherent W) (hm : 6 ≤ m)
    {z : List (Fin m)} (hz : DLGood W (thr m) z) (h : (domPts W z).Nonempty) :
    4 ≤ (domCls W z h).card ∧ thr m < (domCls W z h).card ∧ (domCls W z h).card ≤ m ∧
      IsCoherent2 (skelOn W z (domCls W z h)) ∧ IsHomog univ (skelOn W z (domCls W z h)) ∧
      ¬ IsClique (skelOn W z (domCls W z h)) univ := by
  have hmin := mem_domPts.1 ((domPts W z).min'_mem h)
  obtain ⟨hlen, u, hu, hncl⟩ : z.length + 2 ≤ k ∧ ∃ u, thr m < (cls1 W z u).card ∧
      ¬ IsClique (skel2 W z) (cls1 W z u) := by
    rcases hz with hall | h2
    · exact absurd (hall _) (not_le.2 hmin)
    · exact h2
  have hC : domCls W z h = cls1 W z u := domCls_eq h hu
  set C := domCls W z h with hCdef
  have hP : ∀ w, w ∈ C ↔ skel2 W z w w = skel1 W z u := fun w => by
    rw [hC, mem_cls1, skel2_self]
  have hcoh : IsCoherent2 (skelOn W z C) :=
    c3m_isCoherent2_equiv (c3m_eqv C _ hP)
      (isCoherent2_restrict (isCoherent2_skel2 hW hlen) (skel1 W z u))
  have hhom : IsHomog univ (skelOn W z C) := fun x _ y _ => by
    show skel2 W z _ _ = skel2 W z _ _
    rw [(hP _).1 (c3m_eOf_mem C x), (hP _).1 (c3m_eOf_mem C y)]
  have hncl' : ¬ IsClique (skelOn W z C) univ := by
    intro hcl
    apply hncl
    rw [← hC]
    intro a ha b hb a' ha' b' hb' hab hab'
    obtain ⟨i, rfl⟩ := (mem_eOf_range C a).2 ha
    obtain ⟨j, rfl⟩ := (mem_eOf_range C b).2 hb
    obtain ⟨i', rfl⟩ := (mem_eOf_range C a').2 ha'
    obtain ⟨j', rfl⟩ := (mem_eOf_range C b').2 hb'
    exact hcl i (mem_univ _) j (mem_univ _) i' (mem_univ _) j' (mem_univ _)
      (fun h => hab (by rw [h])) (fun h => hab' (by rw [h]))
  have hcard : thr m < C.card := by rw [hC]; exact hu
  have hn : 4 ≤ C.card := by unfold thr at hcard; omega
  have hCm : C.card ≤ m := by simpa using Finset.card_le_univ C
  exact ⟨hn, hcard, hCm, hcoh, hhom, hncl'⟩

/-- **The outcome at a good list is live and valid, with Split-or-Johnson's count.** -/
theorem outTree_spec (W : (Fin k → Fin m) → ℕ) (hW : IsCoherent W) (e : Fin m ↪ Γ)
    (hm : 6 ≤ m) {z : List (Fin m)} (hz : DLGood W (thr m) z) :
    (outTree W e z).Live ∧ (outTree W e z).count ≤ 2 ^ (129 * (Nat.clog 2 m + 2) ^ 2) ∧
      (outTree W e z).AllLeaves ValidLeaf := by
  unfold outTree
  by_cases h : (domPts W z).Nonempty
  · rw [dite_eq_left h]
    obtain ⟨hn, -, hCm, hcoh, hhom, hncl'⟩ := outTree_dom W hW hm hz h
    set C := domCls W z h
    obtain ⟨hl, hc, hv⟩ := splitTree_spec (skelOn W z C) ((eOf C).trans e) hn hcoh hhom hncl'
    refine ⟨hl, hc.trans (Nat.pow_le_pow_right two_pos ?_), hv⟩
    have := Nat.clog_mono_right 2 hCm
    have : (Nat.clog 2 C.card + 2) ^ 2 ≤ (Nat.clog 2 m + 2) ^ 2 :=
      Nat.pow_le_pow_left (by omega) 2
    omega
  · rw [dite_eq_right h]
    refine ⟨trivial, Nat.one_le_two_pow, Or.inl ⟨_, _, rfl, extPart_valid e
      (c3m_isColPart_colPart (skel1 W z) (t := thr m) fun u => ?_)⟩⟩
    exact not_lt.1 fun hu => h ⟨u, mem_domPts.2 hu⟩

/-- **The size of the outcome's partitions** (stage 14j-6b-1): every partition leaf at a good
list is a colored `t`-partition with `t ≤ max ((m + 3) / 2) (|Γ| − t₀ − 1)`, `t₀ = thr m`: on
the dominant class of more than `t₀` points (`splitTree_partLe`), or the vertex colouring with
classes of at most `t₀` points. -/
theorem outTree_partLe (W : (Fin k → Fin m) → ℕ) (hW : IsCoherent W) (e : Fin m ↪ Γ)
    (hm : 6 ≤ m) {z : List (Fin m)} (hz : DLGood W (thr m) z) :
    (outTree W e z).AllLeaves (PartLe (max ((m + 3) / 2) (Fintype.card Γ - thr m - 1))) := by
  unfold outTree
  by_cases h : (domPts W z).Nonempty
  · rw [dite_eq_left h]
    obtain ⟨hn, hcard, hCm, hcoh, hhom, hncl'⟩ := outTree_dom W hW hm hz h
    refine (splitTree_partLe (skelOn W z (domCls W z h)) ((eOf (domCls W z h)).trans e) hn hcoh
      hhom hncl').mono fun o ho p hp => ?_
    obtain ⟨t, ht, hp⟩ := ho p hp
    exact ⟨t, ht.trans (max_le_max (by omega) (by omega)), hp⟩
  · rw [dite_eq_right h]
    intro p hp
    cases Sum.inl.inj (Option.some.inj hp)
    obtain ⟨t, ht, hp⟩ := extPart_partLe e
      (c3m_isColPart_colPart (skel1 W z) (t := thr m) fun u =>
        not_lt.1 fun hu => h ⟨u, mem_domPts.2 hu⟩) le_rfl
    refine ⟨t, ht.trans (max_le_max ?_ ?_), hp⟩
    · unfold thr
      omega
    · unfold thr
      omega

end OutcomeSpec

/-! ### The tree -/

section Tree

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ] {k m : ℕ}

/-- The good lists of the Design Lemma for the refinement `W`, threshold `t = (m + 1) / 2`. -/
def goodLists (W : (Fin k → Fin m) → ℕ) : Finset (List (Fin m)) :=
  (tuplesLt univ k).filter (DLGood W (thr m))

/-- A list of points of `Fin m` as a choice on `Γ`. -/
def zChoice (e : Fin m ↪ Γ) (z : List (Fin m)) : Choice Γ :=
  chMap e (show Choice (Fin m) from z.map Sum.inl)

/-- The points of `Fin m` of a choice on `Γ`. -/
def zOf (e : Fin m ↪ Γ) (ch : Choice Γ) : List (Fin m) :=
  (show List (Fin m ⊕ Finset (Fin m)) from chBack e ch).filterMap Sum.getLeft?

/-- **The structures of Case 3** for the colouring `c` of the `k`-tuples of `Fin m`, extended
to `Γ` along `e`: a node over the good lists of the refinement, then the outcome. -/
def case3Tree (c : (Fin k → Fin m) → ℕ) (e : Fin m ↪ Γ) : STree Γ :=
  .node ((goodLists (wl k m c).1).image (zChoice e)) fun ch => outTree (wl k m c).1 e (zOf e ch)

omit [Fintype Γ] in
theorem c3m_filterMap_inl (z : List (Fin m)) :
    (z.map (Sum.inl : Fin m → Fin m ⊕ Finset (Fin m))).filterMap Sum.getLeft? = z := by
  induction z with
  | nil => rfl
  | cons a z ih => simp [ih]

omit [Fintype Γ] in
theorem zOf_zChoice (e : Fin m ↪ Γ) (z : List (Fin m)) : zOf e (zChoice e z) = z := by
  unfold zOf zChoice
  rw [chBack_chMap]
  exact c3m_filterMap_inl z

omit [Fintype Γ] in
theorem zChoice_injective (e : Fin m ↪ Γ) : Function.Injective (zChoice e) := fun z z' h => by
  rw [← zOf_zChoice e z, h, zOf_zChoice]

omit [Fintype Γ] in
theorem c3m_filterMap_smul (π : Perm (Fin m)) (L : List (Fin m ⊕ Finset (Fin m))) :
    (L.map (π • ·)).filterMap Sum.getLeft? = (L.filterMap Sum.getLeft?).map π := by
  induction L with
  | nil => rfl
  | cons q L ih =>
    rcases q with i | s
    · simp [ih, Perm.smul_def]
    · simpa [List.filterMap_cons] using ih

variable (σ : Perm Γ) (π : Perm (Fin m)) {e₁ e₂ : Fin m ↪ Γ}

omit [Fintype Γ] in
theorem zChoice_relabel (he : ∀ i, e₂ (π i) = σ (e₁ i)) (z : List (Fin m)) :
    zChoice e₂ (z.map π) = σ • zChoice e₁ z := by
  unfold zChoice
  rw [← chMap_relabel σ π he]
  congr 1
  show List.map _ (List.map _ z) = List.map _ (List.map _ z)
  simp [List.map_map, Function.comp_def, Perm.smul_def]

omit [Fintype Γ] in
theorem zOf_relabel (he : ∀ i, e₂ (π i) = σ (e₁ i)) (ch : Choice Γ) :
    zOf e₂ (σ • ch) = (zOf e₁ ch).map π := by
  unfold zOf
  rw [chBack_relabel σ π he]
  exact c3m_filterMap_smul π _

omit [Fintype Γ] [DecidableEq Γ] in
theorem goodLists_relabel {W₁ W₂ : (Fin k → Fin m) → ℕ} (hW : ∀ y, W₂ (⇑π ∘ y) = W₁ y) :
    goodLists W₂ = (goodLists W₁).image (List.map π) := by
  ext z'
  simp only [goodLists, mem_filter, mem_image, SplitJohnson.BipRelabel.mem_tuplesLt,
    mem_univ, implies_true, and_true]
  constructor
  · rintro ⟨hlen, hz'⟩
    refine ⟨z'.map π.symm, ⟨by simpa using hlen, ?_⟩, by simp [List.map_map]⟩
    rw [← SplitJohnson.BipRelabel.dlGood_map (π : Fin m ≃ Fin m) hW]
    simpa [List.map_map] using hz'
  · rintro ⟨z, ⟨hlen, hz⟩, rfl⟩
    exact ⟨by simpa using hlen,
      (SplitJohnson.BipRelabel.dlGood_map (π : Fin m ≃ Fin m) hW _ z).2 hz⟩

/-- **Naturality of the structures of Case 3**: if the range of `e₂` is the image under `σ` of
the range of `e₁`, and the colourings agree on tuples related through the embeddings and `σ`,
the tree of the second colouring is the tree of the first moved by `σ`. -/
theorem case3Tree_relabel {m₁ m₂ : ℕ} (hm : m₂ = m₁) (c₁ : (Fin k → Fin m₁) → ℕ)
    (c₂ : (Fin k → Fin m₂) → ℕ) (e₁ : Fin m₁ ↪ Γ) (e₂ : Fin m₂ ↪ Γ)
    (hrange : ∀ v, (∃ j, e₂ j = v) ↔ ∃ i, e₁ i = σ⁻¹ v)
    (hc : ∀ T T', (∀ i, e₂ (T' i) = σ (e₁ (T i))) → c₂ T' = c₁ T) :
    case3Tree c₂ e₂ = (case3Tree c₁ e₁).act σ := by
  subst hm
  have hex : ∀ i, ∃ j, e₂ j = σ (e₁ i) := fun i =>
    (hrange (σ (e₁ i))).2 ⟨i, by rw [perm_inv_apply_self]⟩
  choose fπ hfπ using hex
  have hinj : Function.Injective fπ := fun i j hij => by
    have := congrArg e₂ hij
    rw [hfπ, hfπ] at this
    exact e₁.injective (σ.injective this)
  set π : Perm (Fin m₂) := Equiv.ofBijective fπ (Finite.injective_iff_bijective.1 hinj)
  have he : ∀ i, e₂ (π i) = σ (e₁ i) := fun i => hfπ i
  have hc' : c₂ = fun x => c₁ (⇑π⁻¹ ∘ x) := by
    funext T'
    refine hc _ _ fun i => ?_
    rw [Function.comp_apply, ← he, perm_apply_inv_self]
  have hW : ∀ y, (wl k m₂ c₂).1 (⇑π ∘ y) = (wl k m₂ c₁).1 y := fun y => by
    rw [hc', wl_relabel]
    show (wl k m₂ c₁).1 (⇑π⁻¹ ∘ ⇑π ∘ y) = _
    rw [show ⇑π⁻¹ ∘ ⇑π ∘ y = y from funext fun i => by simp]
  unfold case3Tree
  simp only [SplitJohnson.CTree.act]
  congr 1
  · rw [goodLists_relabel π hW, Finset.image_image, Finset.smul_finset_def, Finset.image_image]
    refine Finset.image_congr fun z _ => ?_
    exact zChoice_relabel σ π he z
  · funext ch
    rw [← smul_inv_smul σ ch, zOf_relabel σ π he, inv_smul_smul]
    exact outTree_relabel σ π hW he _

/-- **Alignment**: under the hypotheses of `case3Tree_relabel`, `σ` carries every reachable
leaf of the first tree to a reachable leaf of the second. -/
theorem case3_reach {m₁ m₂ : ℕ} (hm : m₂ = m₁) (c₁ : (Fin k → Fin m₁) → ℕ)
    (c₂ : (Fin k → Fin m₂) → ℕ) (e₁ : Fin m₁ ↪ Γ) (e₂ : Fin m₂ ↪ Γ)
    (hrange : ∀ v, (∃ j, e₂ j = v) ↔ ∃ i, e₁ i = σ⁻¹ v)
    (hc : ∀ T T', (∀ i, e₂ (T' i) = σ (e₁ (T i))) → c₂ T' = c₁ T) {o : Option (Out Γ)}
    (ho : (case3Tree c₁ e₁).Reach o) : (case3Tree c₂ e₂).Reach (σ • o) := by
  rw [case3Tree_relabel σ hm c₁ c₂ e₁ e₂ hrange hc]
  exact (SplitJohnson.CTree.reach_act σ).2 ho

/-- **Alignment, for the increasing numberings of the complements of the supports.** If `σ`
maps the support `S₁` of `x`'s full group to the support `S₂` of `y`'s, and the colourings agree
along `σ`, then `σ` carries every reachable structure of `x` to a reachable structure of `y`. -/
theorem case3_reach_eOf {Γ : Type*} [Fintype Γ] [LinearOrder Γ] (σ : Perm Γ)
    {S₁ S₂ : Finset Γ} (hS : σ • S₁ = S₂)
    (c₁ : (Fin k → Fin (univ \ S₁).card) → ℕ) (c₂ : (Fin k → Fin (univ \ S₂).card) → ℕ)
    (hc : ∀ T T', (∀ i, eOf (univ \ S₂) (T' i) = σ (eOf (univ \ S₁) (T i))) → c₂ T' = c₁ T)
    {o : Option (Out Γ)} (ho : (case3Tree c₁ (eOf (univ \ S₁))).Reach o) :
    (case3Tree c₂ (eOf (univ \ S₂))).Reach (σ • o) := by
  have hm : (univ \ S₂).card = (univ \ S₁).card := by
    rw [Finset.card_univ_sdiff, Finset.card_univ_sdiff, ← hS, Finset.card_smul_finset]
  refine case3_reach σ hm c₁ c₂ _ _ (fun v => ?_) hc ho
  rw [mem_eOf_range, mem_eOf_range, Finset.mem_sdiff, Finset.mem_sdiff, ← hS,
    Finset.mem_smul_finset]
  simp only [mem_univ, true_and]
  constructor
  · intro h h'
    exact h ⟨σ⁻¹ v, h', perm_apply_inv_self σ v⟩
  · rintro h ⟨w, hw, rfl⟩
    exact h (by rwa [Perm.smul_def, perm_inv_apply_self])

/-- **The structures of Case 3 are live and valid, with the count bound**, when no `t + 1` points
are pairwise twins of the colouring. -/
theorem case3Tree_spec (c : (Fin k → Fin m) → ℕ) (e : Fin m ↪ Γ) (hk : 2 ≤ k) (hm : 6 ≤ m)
    (htw : ∀ T : Finset (Fin m), (∀ u ∈ T, ∀ v ∈ T, IsTwin c u v) → T.card ≤ thr m) :
    (case3Tree c e).Live ∧
      (case3Tree c e).count ≤ m ^ k * 2 ^ (129 * (Nat.clog 2 m + 2) ^ 2) ∧
      (case3Tree c e).AllLeaves ValidLeaf := by
  have hgood : ∀ ch ∈ (goodLists (wl k m c).1).image (zChoice e),
      (outTree (wl k m c).1 e (zOf e ch)).Live ∧
        (outTree (wl k m c).1 e (zOf e ch)).count ≤ 2 ^ (129 * (Nat.clog 2 m + 2) ^ 2) ∧
        (outTree (wl k m c).1 e (zOf e ch)).AllLeaves ValidLeaf := by
    intro ch hch
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hch
    rw [zOf_zChoice]
    exact outTree_spec _ (wl_isCoherent c) e hm (Finset.mem_filter.1 hz).2
  refine ⟨⟨?_, fun ch hch => (hgood ch hch).1⟩, ?_, fun ch hch => (hgood ch hch).2.2⟩
  · obtain ⟨x, hx, hgx⟩ := design_lemma (V := Fin m) (t := thr m) hk (wl_isCoherent c)
      (by rw [Fintype.card_fin]; unfold thr; omega) fun T hT =>
        htw T fun u hu v hv => (isTwin_wl_iff c u v).1 (hT u hu v hv)
    refine ⟨zChoice e x, Finset.mem_image.2 ⟨x, Finset.mem_filter.2
      ⟨SplitJohnson.BipRelabel.mem_tuplesLt.2 ⟨hx, fun _ _ => mem_univ _⟩, ?_⟩, rfl⟩⟩
    unfold DLGood
    exact hgx
  · show ∑ ch ∈ (goodLists (wl k m c).1).image (zChoice e), _ ≤ _
    calc ∑ ch ∈ (goodLists (wl k m c).1).image (zChoice e),
          (outTree (wl k m c).1 e (zOf e ch)).count
        ≤ ∑ _ch ∈ (goodLists (wl k m c).1).image (zChoice e),
            2 ^ (129 * (Nat.clog 2 m + 2) ^ 2) :=
          Finset.sum_le_sum fun ch hch => (hgood ch hch).2.1
      _ = ((goodLists (wl k m c).1).image (zChoice e)).card *
            2 ^ (129 * (Nat.clog 2 m + 2) ^ 2) := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ m ^ k * 2 ^ (129 * (Nat.clog 2 m + 2) ^ 2) := by
          refine Nat.mul_le_mul_right _ ?_
          refine (Finset.card_image_le).trans ((Finset.card_filter_le _ _).trans ?_)
          have := SplitJohnson.BCount.card_tuplesLt_le (univ : Finset (Fin m))
            (by rw [Finset.card_univ, Fintype.card_fin]; omega) k
          rwa [Finset.card_univ, Fintype.card_fin] at this

/-- **The size of Case 3's partitions** (stage 14j-6b-1, `PLAN-14.md` §14.11 item 1): every
reachable partition leaf is a colored `t`-partition with
`t ≤ max ((m + 3) / 2) (|Γ| − thr m − 1)` (`outTree_partLe`). -/
theorem case3Tree_partLe (c : (Fin k → Fin m) → ℕ) (e : Fin m ↪ Γ) (hm : 6 ≤ m) :
    (case3Tree c e).AllLeaves (PartLe (max ((m + 3) / 2) (Fintype.card Γ - thr m - 1))) := by
  intro ch hch
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hch
  show (outTree (wl k m c).1 e (zOf e (zChoice e z))).AllLeaves _
  rw [zOf_zChoice]
  exact outTree_partLe _ (wl_isCoherent c) e hm (Finset.mem_filter.1 hz).2

theorem case3Tree_live (c : (Fin k → Fin m) → ℕ) (e : Fin m ↪ Γ) (hk : 2 ≤ k) (hm : 6 ≤ m)
    (htw : ∀ T : Finset (Fin m), (∀ u ∈ T, ∀ v ∈ T, IsTwin c u v) → T.card ≤ thr m) :
    (case3Tree c e).Live :=
  (case3Tree_spec c e hk hm htw).1

theorem case3Tree_valid (c : (Fin k → Fin m) → ℕ) (e : Fin m ↪ Γ) (hk : 2 ≤ k) (hm : 6 ≤ m)
    (htw : ∀ T : Finset (Fin m), (∀ u ∈ T, ∀ v ∈ T, IsTwin c u v) → T.card ≤ thr m) :
    (case3Tree c e).AllLeaves ValidLeaf :=
  (case3Tree_spec c e hk hm htw).2.2

theorem case3Tree_count_le (c : (Fin k → Fin m) → ℕ) (e : Fin m ↪ Γ) (hk : 2 ≤ k)
    (hm : 6 ≤ m)
    (htw : ∀ T : Finset (Fin m), (∀ u ∈ T, ∀ v ∈ T, IsTwin c u v) → T.card ≤ thr m) :
    (case3Tree c e).count ≤ m ^ k * 2 ^ (129 * (Nat.clog 2 m + 2) ^ 2) :=
  (case3Tree_spec c e hk hm htw).2.1

end Tree

/-! ### Twins under the thresholds -/

section Twins

open GraphIso.Certificates

/-- **No large twin class** (milestone 13's `no_large_twins`). For the colouring of the
`k`-tuples of the points outside the support of the full group by certificate equivalence
(`SameColour`), through the numbering `e` of those points, the thresholds leave fewer than `k`
pairwise twins. -/
theorem no_twins_of_thresholds {Ω Γ : Type} [Fintype Ω] [DecidableEq Ω] [Fintype Γ]
    [DecidableEq Γ] {G : Subgroup (Perm Ω)} (φ : G →* Perm Γ) {L : Type*} {K : ℕ → ℕ}
    {k m : ℕ} (x : Ω → L) (hT : Thresholds K (Fintype.card Ω) k) (e : Fin m ↪ Γ)
    (hsupp : ∀ v, v ∉ supp φ (fullGroupK φ k x) ↔ ∃ i, e i = v)
    {c : (Fin k → Fin m) → ℕ} (hc : ∀ T T', c T = c T' ↔ SameColour φ x (⇑e ∘ T) (⇑e ∘ T'))
    (T₀ : Finset (Fin m)) (htw : ∀ u ∈ T₀, ∀ v ∈ T₀, IsTwin c u v) : T₀.card < k := by
  have hsupp' : ∀ v, v ∉ supp φ (fullGroup φ k x) ↔ ∃ i, e i = v := by
    rw [← fullGroupK_eq_fullGroup φ x hT]
    exact hsupp
  by_contra hlt
  refine no_large_twins φ x hT (U := T₀.map e) (by rw [Finset.card_map]; omega) ?_ ?_
  · intro u hu
    obtain ⟨a, -, rfl⟩ := Finset.mem_map.1 hu
    exact (hsupp' _).2 ⟨a, rfl⟩
  · intro u hu v hv T hT
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.1 hu
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.1 hv
    have hex : ∀ i, ∃ j, e j = T i := fun i => (hsupp' (T i)).1 (hT i)
    choose T₁ hT₁ using hex
    have hT : T = ⇑e ∘ T₁ := funext fun i => (hT₁ i).symm
    have hsw : ⇑(Equiv.swap (e a) (e b)) ∘ T = ⇑e ∘ (⇑(Equiv.swap a b) ∘ T₁) := by
      rw [hT]
      funext i
      simp only [Function.comp_apply]
      exact e.injective.swap_apply a b (T₁ i)
    rw [hsw, hT]
    exact (hc T₁ _).1 (htw a ha b hb T₁).symm

end Twins

end GraphIso.Case3
