module

public import GraphIso.SoJTree.Measure

/-!
# Trimmed Johnson embeddings

Stage 14f, item 1 (`PLAN-14.md` §10), at the level of milestone 11's model. A Johnson leaf
`J = ⟨V₀, Λ, s, f⟩` of Split-or-Johnson carries `f` at every point, but only `f` on `V₀`
matters. Align works with the trimmed embedding `trimJ J`, which keeps `V₀`, `Λ`, `s` and `f`
on `V₀` and is empty off `V₀`; its stabilizer has explicit generators.

* `trimJ_smul`, `trimOut_smul`: trimming commutes with the action, so a canonical structure stays
  canonical after trimming (`trim_canonical` for `soj`).
* `isJohnson_trimJ`, `validOut_trimOut`: trimming keeps validity, so the progress lemmas still
  apply.
* `bsoj_johnson_disjoint`: if the cells are disjoint from the points, every reachable Johnson
  leaf of `bsoj` has its points among them and its cells disjoint from its points.
* `soj_johnson_disjoint`: every reachable Johnson leaf of `soj` has its cells disjoint from `V₀`.
-/

@[expose] public section

namespace GraphIso.Align

open Equiv Finset Pointwise GraphIso.SplitJohnson GraphIso.Coherent

section Trim

variable {α : Type*} [DecidableEq α]

/-- **The trimmed Johnson embedding**: `f` on `V₀`, empty off `V₀`. -/
def trimJ (J : JEmb α) : JEmb α := ⟨J.V0, J.Λ, J.s, fun v => if v ∈ J.V0 then J.f v else ∅⟩

/-- Trim the Johnson leaves, keep the others. -/
def trimOut : Option (Out α) → Option (Out α)
  | some (Sum.inr J) => some (Sum.inr (trimJ J))
  | o => o

theorem tj_mem_smul_iff (σ : Perm α) (s : Finset α) (v : α) : v ∈ σ • s ↔ σ⁻¹ • v ∈ s := by
  conv_lhs => rw [← smul_inv_smul σ v]
  exact smul_mem_smul_finset_iff σ

/-- **Trimming commutes with the action.** -/
theorem trimJ_smul (σ : Perm α) (J : JEmb α) : trimJ (σ • J) = σ • trimJ J := by
  show JEmb.mk _ _ _ _ = JEmb.mk _ _ _ _
  congr 1
  funext v
  show (if v ∈ σ • J.V0 then σ • J.f (σ⁻¹ • v) else ∅) =
    σ • (if σ⁻¹ • v ∈ J.V0 then J.f (σ⁻¹ • v) else ∅)
  simp only [tj_mem_smul_iff]
  split_ifs
  · rfl
  · exact (smul_finset_empty σ).symm

theorem trimOut_smul (σ : Perm α) (o : Option (Out α)) : trimOut (σ • o) = σ • trimOut o := by
  rcases o with _ | p | J
  · rfl
  · rfl
  · show some (Sum.inr (trimJ (σ • J))) = some (Sum.inr (σ • trimJ J))
    rw [trimJ_smul]

/-- **Trimming keeps a Johnson embedding valid.** -/
theorem isJohnson_trimJ {V : Finset α} {t : ℕ} {J : JEmb α} (h : IsJohnson V t J) :
    IsJohnson V t (trimJ J) where
  sub := h.sub
  card_gt := h.card_gt
  two_le := h.two_le
  le_half := h.le_half
  cells_ne := h.cells_ne
  cells_disj := h.cells_disj
  maps_to v hv := by
    have hv' : v ∈ J.V0 := hv
    show (if v ∈ J.V0 then J.f v else ∅) ∈ _
    simp only [hv', ↓reduceIte]
    exact h.maps_to v hv
  inj v hv w hw e := by
    have hv' : v ∈ J.V0 := hv
    have hw' : w ∈ J.V0 := hw
    change (if v ∈ J.V0 then J.f v else ∅) = (if w ∈ J.V0 then J.f w else ∅) at e
    simp only [hv', hw', ↓reduceIte] at e
    exact h.inj v hv w hw e
  surj T hT := by
    obtain ⟨v, hv, e⟩ := h.surj T hT
    refine ⟨v, hv, ?_⟩
    show (if v ∈ J.V0 then J.f v else ∅) = T
    simp only [hv, ↓reduceIte, e]

theorem validOut_trimOut {V : Finset α} {t : ℕ} {o : Option (Out α)} (h : ValidOut V t o) :
    ValidOut V t (trimOut o) := by
  rcases o with _ | p | J
  · exact h
  · exact h
  · exact isJohnson_trimJ h

end Trim

/-! ### Cells disjoint from the points -/

section Disjoint

variable {α : Type*} [DecidableEq α]

/-- A leaf whose Johnson embedding, if it is one, has its points in `V` and its cells disjoint
from its points. -/
def tj_JDisj (V : Finset α) (o : Option (Out α)) : Prop :=
  ∀ J : JEmb α, o = some (Sum.inr J) → J.V0 ⊆ V ∧ ∀ a ∈ J.Λ, Disjoint a J.V0

omit [DecidableEq α] in
theorem tj_JDisj_none (V : Finset α) : tj_JDisj V none := fun _ h => by cases h

omit [DecidableEq α] in
theorem tj_JDisj_inl (V : Finset α) (p : CPart α) : tj_JDisj V (some (Sum.inl p)) :=
  fun _ h => by cases h

omit [DecidableEq α] in
theorem tj_JDisj_mono {V V' : Finset α} (hV : V ⊆ V') {o : Option (Out α)}
    (h : tj_JDisj V o) : tj_JDisj V' o := fun J hJ =>
  ⟨(h J hJ).1.trans hV, (h J hJ).2⟩

theorem tj_JDisj_addPieceOut {V D : Finset α} {o : Option (Out α)} (h : tj_JDisj V o) :
    tj_JDisj V (addPieceOut D o) := by
  rcases o with _ | p | J
  · exact h
  · exact tj_JDisj_inl V _
  · exact h

theorem tj_allLeaves_withPiece {V D : Finset α} {T : STree α}
    (h : T.AllLeaves (tj_JDisj V)) : (withPiece D T).AllLeaves (tj_JDisj V) :=
  CTree.allLeaves_bind (h.mono fun _ ho => tj_JDisj_addPieceOut ho)

/-- The recursion hypothesis: calls on points inside `V` with cells disjoint from their points
give leaves satisfying `tj_JDisj V`. -/
def tj_Rec (V : Finset α)
    (rec : Finset α → Finset (Finset α) → (α → Finset α → Bool) → STree α) : Prop :=
  ∀ V₁'' V₂'' A'', V₁'' ⊆ V → (∀ a ∈ V₂'', Disjoint a V₁'') →
    (rec V₁'' V₂'' A'').AllLeaves (tj_JDisj V)

omit [DecidableEq α] in
theorem tj_Rec_shrink {V : Finset α} {V₂ : Finset (Finset α)}
    {rec : Finset α → Finset (Finset α) → (α → Finset α → Bool) → STree α}
    (hrec : tj_Rec V rec) : tj_Rec V (shrink V₂ rec) := by
  intro V₁'' V₂'' A'' hV hd
  unfold shrink
  split_ifs
  · exact hrec V₁'' V₂'' A'' hV hd
  · exact tj_JDisj_none V

theorem tj_selThird_subset {β : Type*} [DecidableEq β] (S : Finset β) (col : β → ℕ) :
    selThird S col ⊆ S := by
  unfold selThird
  dsimp only
  split
  · exact filter_subset _ _
  · exact filter_subset _ _

omit [DecidableEq α] in
/-- The bipartite leaves of Coherent Split-or-Johnson lie in its two sides. -/
theorem tj_cohSoj_bip {R : Type*} [DecidableEq R] (C₁ C₂ : Finset R) (c : R → R → ℕ) :
    (cohSoj C₁ C₂ c).AllLeaves fun o => ∀ W₁ W₂ A', o = some (.bip W₁ W₂ A') →
      W₁ ⊆ C₁ ∧ ∀ B ∈ W₂, B ⊆ C₂ := by
  unfold cohSoj
  dsimp only
  split_ifs
  · intro W₁ W₂ A' h
    cases h
  · intro y _ W₁ W₂ A' h
    cases h
    refine ⟨subset_refl _, fun B hB => ?_⟩
    obtain ⟨e, he, rfl⟩ := mem_image.1 hB
    exact singleton_subset_iff.2 (comp_subset _ _ _ _ he)
  · intro W₁ W₂ A' h
    cases h
    refine ⟨subset_refl _, fun B hB => ?_⟩
    obtain ⟨w, -, rfl⟩ := mem_image.1 hB
    exact comp_subset _ _ _ _
  · intro W₁ W₂ A' h
    cases h
  · intro w _ W₁ W₂ A' h
    cases h
  · intro y _
    show CTree.AllLeaves _ (dite _ _ _)
    split_ifs
    · intro W₁ W₂ A' h
      cases h
      refine ⟨filter_subset _ _, fun B hB => ?_⟩
      obtain ⟨e, he, rfl⟩ := mem_image.1 hB
      exact singleton_subset_iff.2 (mem_filter.1 he).1
    · intro W₁ W₂ A' h
      cases h
    · intro W₁ W₂ A' h
      cases h

/-- The cell of an ideal point made of cells disjoint from `V` is disjoint from `V`. -/
theorem tj_cellOf_disjoint {V : Finset α} {C₂ : Finset (Finset α)}
    (hd : ∀ a ∈ C₂, Disjoint a V) {B : Finset (α ⊕ Finset α)}
    (hB : B ⊆ C₂.map ⟨Sum.inr, Sum.inr_injective⟩) : Disjoint (cellOf B) V := by
  rw [disjoint_left]
  intro y hy
  unfold cellOf at hy
  obtain ⟨s, hs, hys⟩ := mem_sup.1 hy
  have hs' : Sum.inr s ∈ C₂.map ⟨Sum.inr, Sum.inr_injective⟩ := hB (mem_toRight.1 hs)
  obtain ⟨s', hs'', e⟩ := mem_map.1 hs'
  obtain rfl : s' = s := Sum.inr_injective e
  exact disjoint_left.1 (hd _ hs'') hys

omit [DecidableEq α] in
theorem tj_allLeaves_ite {C O : Type*} {P : O → Prop} {p : Prop} [Decidable p]
    {a b : CTree C O} (ha : a.AllLeaves P) (hb : b.AllLeaves P) :
    (if p then a else b).AllLeaves P := by
  split_ifs
  · exact ha
  · exact hb

/-- `cohCont` keeps the invariant. -/
theorem tj_cohCont {t : ℕ} {V₁ V₁' C₁ : Finset α} {C₂ : Finset (Finset α)}
    {rec : Finset α → Finset (Finset α) → (α → Finset α → Bool) → STree α}
    (hC₁ : C₁ ⊆ V₁) (hd : ∀ a ∈ C₂, Disjoint a V₁) (hrec : tj_Rec V₁ rec)
    (o : Option (CohOut (α ⊕ Finset α)))
    (ho : ∀ W₁ W₂ A', o = some (.bip W₁ W₂ A') →
      W₁ ⊆ C₁.map ⟨Sum.inl, Sum.inl_injective⟩ ∧
        ∀ B ∈ W₂, B ⊆ C₂.map ⟨Sum.inr, Sum.inr_injective⟩) :
    (cohCont t V₁ V₁' C₁ rec o).AllLeaves (tj_JDisj V₁) := by
  rcases o with _ | p | ⟨W₁, W₂, A'⟩
  · exact tj_JDisj_none V₁
  · exact tj_JDisj_inl V₁ _
  · obtain ⟨hW₁, hW₂⟩ := ho W₁ W₂ A' rfl
    have hW : W₁.toLeft ⊆ V₁ := by
      intro x hx
      obtain ⟨x', hx', e⟩ := mem_map.1 (hW₁ (mem_toLeft.1 hx))
      obtain rfl : x' = x := Sum.inl_injective e
      exact hC₁ hx'
    simp only [cohCont]
    split_ifs
    · exact tj_JDisj_inl V₁ _
    · refine tj_allLeaves_withPiece (tj_allLeaves_withPiece (tj_allLeaves_withPiece ?_))
      refine hrec _ _ _ hW fun a ha => ?_
      obtain ⟨B, hB, rfl⟩ := mem_image.1 ha
      exact (tj_cellOf_disjoint hd (hW₂ B hB)).mono_right hW

/-- `dlCont` keeps the invariant. -/
theorem tj_dlCont {t : ℕ} {V₁ V₁' : Finset α} {V₂ : Finset (Finset α)}
    {A : α → Finset α → Bool} {d : ℕ} (W : (Fin d → V₂) → ℕ)
    {rec : Finset α → Finset (Finset α) → (α → Finset α → Bool) → STree α}
    (hV₁' : V₁' ⊆ V₁) (hd : ∀ a ∈ V₂, Disjoint a V₁) (hrec : tj_Rec V₁ rec) (x : List V₂) :
    (dlCont t V₁ V₁' V₂ A W rec x).AllLeaves (tj_JDisj V₁) := by
  have hsh : tj_Rec V₁ (shrink V₂ rec) := tj_Rec_shrink hrec
  have hd' : ∀ S ⊆ V₂, ∀ a ∈ S, Disjoint a V₁' := fun S hS a ha =>
    (hd a (hS ha)).mono_right hV₁'
  have hsub : ∀ (S : Finset V₂), S.map (Function.Embedding.subtype _) ⊆ V₂ := by
    intro S s hs
    obtain ⟨u, -, rfl⟩ := mem_map.1 hs
    exact u.2
  unfold dlCont
  dsimp only
  split_ifs
  all_goals first
    | exact tj_JDisj_inl V₁ _
    | exact tj_allLeaves_withPiece (hsh _ _ _ hV₁' (hd' _ (pickSide_subset _ _ (hsub _))))
    | exact tj_allLeaves_withPiece
        (hsh _ _ _ hV₁' (hd' _ (pickSide_subset _ _ (tj_selThird_subset _ _))))
    | refine tj_allLeaves_ite ?_ ?_
      · exact tj_allLeaves_withPiece (hsh _ _ _ hV₁' (hd' _ sdiff_subset))
      · refine CTree.allLeaves_bind (CTree.allLeaves_trans (fun q => rfl) ?_)
        refine (tj_cohSoj_bip _ _ _).mono fun o ho => ?_
        exact tj_cohCont ((filter_subset _ _).trans hV₁')
          (fun a ha => hd a (mem_filter.1 ha).1) hsh o ho

/-- One level of `bsoj` keeps the invariant. -/
theorem tj_bstep {t : ℕ} {V₁ : Finset α} {V₂ : Finset (Finset α)} {A : α → Finset α → Bool}
    {rec : Finset α → Finset (Finset α) → (α → Finset α → Bool) → STree α}
    (hd : ∀ a ∈ V₂, Disjoint a V₁) (hrec : tj_Rec V₁ rec) :
    (bstep t V₁ V₂ A rec).AllLeaves (tj_JDisj V₁) := by
  unfold bstep
  dsimp only
  split_ifs with hdg hJ hb hS
  · intro J hJ'
    cases hJ'
    exact ⟨filter_subset _ _, fun a ha => (hd a ha).mono_right (filter_subset _ _)⟩
  · intro e _
    exact tj_JDisj_inl V₁ _
  · exact tj_allLeaves_withPiece (hrec _ _ _ (filter_subset _ _) fun a ha =>
      (hd a (pickSide_subset _ _ (bigTwins_subset _ _) ha)).mono_right (filter_subset _ _))
  · intro ch _
    exact tj_dlCont _ (filter_subset _ _) hd hrec _
  · exact tj_JDisj_inl V₁ _

/-- The invariant for every leaf of `bsoj`. -/
theorem tj_bsoj_allLeaves (t : ℕ) (V₁ : Finset α) (V₂ : Finset (Finset α))
    (A : α → Finset α → Bool) (hd : ∀ a ∈ V₂, Disjoint a V₁) :
    (bsoj t V₁ V₂ A).AllLeaves (tj_JDisj V₁) := by
  suffices h : ∀ n (V₁ : Finset α) (V₂ : Finset (Finset α)) (A : α → Finset α → Bool),
      V₂.card = n → (∀ a ∈ V₂, Disjoint a V₁) → (bsoj t V₁ V₂ A).AllLeaves (tj_JDisj V₁) from
    h _ V₁ V₂ A rfl hd
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro V₁ V₂ A hn hd
    rw [bsoj]
    refine tj_bstep hd fun V₁'' V₂'' A'' hV hd'' => ?_
    split_ifs with hlt
    · exact (ih _ (hn ▸ hlt) V₁'' V₂'' A'' rfl hd'').mono fun _ ho => tj_JDisj_mono hV ho
    · exact tj_JDisj_none V₁

/-- **The cells of a Johnson leaf of `bsoj` are disjoint from its points**, if the cells are
disjoint from the points at the start; its points lie among the points. -/
theorem bsoj_johnson_disjoint (t : ℕ) (V₁ : Finset α) (V₂ : Finset (Finset α))
    (A : α → Finset α → Bool) (hd : ∀ a ∈ V₂, Disjoint a V₁) {J : JEmb α}
    (hJ : (bsoj t V₁ V₂ A).Reach (some (Sum.inr J))) :
    J.V0 ⊆ V₁ ∧ ∀ a ∈ J.Λ, Disjoint a J.V0 :=
  CTree.allLeaves_iff_reach.1 (tj_bsoj_allLeaves t V₁ V₂ A hd) _ hJ J rfl

end Disjoint

section Soj

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ]

/-- The Johnson leaves of `sojAt` have their cells disjoint from their points. -/
theorem tj_sojAt (c : Γ → Γ → ℕ) (t : ℕ) (x : Γ) :
    (sojAt c t x).AllLeaves (tj_JDisj univ) := by
  unfold sojAt
  dsimp only
  split_ifs with h1 hp
  · exact tj_JDisj_inl _ _
  · refine CTree.allLeaves_bind ?_
    have hdisj : ∀ a ∈ (univ.filter fun y => c x y = (Nat.unpair (Finset.min' _ hp)).1).image
        singleton, Disjoint a (univ.filter fun y => t < (univ.filter fun z =>
          c x z = c x y).card) := by
      intro a ha
      obtain ⟨y, hy, rfl⟩ := mem_image.1 ha
      rw [disjoint_singleton_left]
      intro hbig
      obtain ⟨p, hp', hpk⟩ := mem_image.1 (Finset.min'_mem _ hp)
      have hk : (Nat.unpair (Finset.min' _ hp)).1 = c x p.2 := by
        rw [← hpk, Nat.unpair_pair]
      have hnot := (mem_filter.1 hp').2.1
      apply hnot
      rw [← hk, ← (mem_filter.1 hy).2]
      exact mem_image_of_mem _ hbig
    refine (tj_bsoj_allLeaves _ _ _ _ hdisj).mono fun o ho => ?_
    rcases o with _ | q | J
    · exact tj_JDisj_none _
    · exact tj_JDisj_inl _ _
    · intro J' hJ'
      cases hJ'
      exact ⟨subset_univ _, (ho J rfl).2⟩
  · exact tj_JDisj_none _

/-- **The cells of a Johnson leaf of `soj` are disjoint from its points.** -/
theorem soj_johnson_disjoint (c : Γ → Γ → ℕ) (t : ℕ) {J : JEmb Γ}
    (hJ : (soj c t).Reach (some (Sum.inr J))) : ∀ a ∈ J.Λ, Disjoint a J.V0 := by
  have h : (soj c t).AllLeaves (tj_JDisj univ) := by
    unfold soj
    intro ch hch
    obtain ⟨x, -, rfl⟩ := mem_image.1 hch
    exact tj_sojAt c t x
  exact (CTree.allLeaves_iff_reach.1 h _ hJ J rfl).2

/-- **Trimming keeps `soj` canonical.** -/
theorem trim_canonical (σ : Perm Γ) (c : Γ → Γ → ℕ) (t : ℕ) :
    (soj (relab2 σ c) t).bind (fun o => .leaf (trimOut o)) =
      ((soj c t).bind fun o => .leaf (trimOut o)).act σ := by
  rw [split_or_johnson_relabel, CTree.act_bind]
  intro o
  show CTree.leaf (trimOut (σ • o)) = CTree.leaf (σ • trimOut o)
  rw [trimOut_smul]

end Soj

end GraphIso.Align
