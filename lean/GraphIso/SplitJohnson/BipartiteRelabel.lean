module

public import GraphIso.SplitJohnson.BipRelabelAux
public import GraphIso.SplitJohnson.CoherentSpec

/-!
# Bipartite Split-or-Johnson: canonicity

`bipartite_split_or_johnson_relabel`: relabelling the input by `σ ∈ Sym(α)` relabels the choice
tree (`CTree.act`), an equality of trees. Every step is built from canonical data: degrees,
twin classes and colours are invariant, Weisfeiler–Leman is natural under the equivalence
`↥V₂ ≃ ↥(σ • V₂)` (`wlOn_natural`), and Coherent Split-or-Johnson is canonical
(`coherent_split_or_johnson_relabel`). The steps are relabelled in `BipRelabelAux.lean`;
`dlCont_relabel` and `bstep_relabel` assemble them, and the theorem follows by strong
induction on the number of cells.
-/

@[expose] public section

namespace GraphIso.SplitJohnson

open Finset Pointwise GraphIso.Coherent

variable {α : Type*} [DecidableEq α]

namespace BipRelabel

/-- The retraction of choices used by `dlCont`, named. -/
def headQ (ch : Choice α) : α ⊕ Finset α :=
  (show List (α ⊕ Finset α) from ch).headD (.inr (∅ : Finset α))

/-- Rewriting an `if` against a function of an `if` with an equivalent condition. -/
theorem ite_eq_app {β : Sort*} {c c' : Prop} [Decidable c] [Decidable c'] (f : β → β)
    {a b a' b' : β} (h : c ↔ c') (ha : c' → a = f a') (hb : ¬ c' → b = f b') :
    (if c then a else b) = f (if c' then a' else b') := by
  by_cases hc : c'
  · rw [ite_eq_left (h.2 hc), ite_eq_left hc]
    exact ha hc
  · rw [ite_eq_right (fun h' => hc (h.1 h')), ite_eq_right hc]
    exact hb hc

theorem headQ_smul (σ : Equiv.Perm α) (c' : Choice α) :
    headQ (σ⁻¹ • c') = (τ σ)⁻¹ • headQ c' := by
  let l : List (α ⊕ Finset α) := c'
  show (List.map (σ⁻¹ • ·) l).headD (Sum.inr (∅ : Finset α)) =
    (τ σ)⁻¹ • l.headD (Sum.inr (∅ : Finset α))
  cases l with
  | nil =>
    show Sum.inr (∅ : Finset α) = σ⁻¹ • (Sum.inr (∅ : Finset α) : α ⊕ Finset α)
    rw [Sum.smul_inr, smul_finset_empty]
  | cons q l => rfl

theorem map_inl_smul (σ : Equiv.Perm α) (C : Finset α) :
    (σ • C).map ⟨Sum.inl, Sum.inl_injective⟩ =
      τ σ • C.map (⟨Sum.inl, Sum.inl_injective⟩ : α ↪ α ⊕ Finset α) := by
  rw [τ_smul_finset]
  ext q
  rw [mem_smul_iff]
  cases q with
  | inl a =>
    simp only [mem_map, Function.Embedding.coeFn_mk, Sum.inl.injEq, exists_eq_right,
      Sum.smul_inl, mem_smul_iff]
  | inr s => simp [Sum.smul_inr]

theorem map_inr_smul (σ : Equiv.Perm α) (C : Finset (Finset α)) :
    (σ • C).map ⟨Sum.inr, Sum.inr_injective⟩ =
      τ σ • C.map (⟨Sum.inr, Sum.inr_injective⟩ : Finset α ↪ α ⊕ Finset α) := by
  rw [τ_smul_finset]
  ext q
  rw [mem_smul_iff]
  cases q with
  | inl a => simp [Sum.smul_inl]
  | inr s =>
    simp only [mem_map, Function.Embedding.coeFn_mk, Sum.inr.injEq, exists_eq_right,
      Sum.smul_inr, mem_smul_iff]

/-- **After the Design Lemma's choice, canonically.** -/
theorem dlCont_relabel (σ : Equiv.Perm α) (t : ℕ) (V₁ V₁' : Finset α)
    (V₂ : Finset (Finset α)) (A : α → Finset α → Bool) {d : ℕ} (W : (Fin d → V₂) → ℕ)
    (W' : (Fin d → ↥(σ • V₂)) → ℕ) (hW : ∀ y, W' (⇑(eS σ V₂) ∘ y) = W y)
    {rec rec' : Finset α → Finset (Finset α) → (α → Finset α → Bool) → STree α}
    (hrec : ∀ a b c, rec' (σ • a) (σ • b) (relabA σ c) = (rec a b c).act σ) (x : List V₂) :
    dlCont t (σ • V₁) (σ • V₁') (σ • V₂) (relabA σ A) W' rec' (x.map (eS σ V₂)) =
      (dlCont t V₁ V₁' V₂ A W rec x).act σ := by
  have hrc := shrink_smul σ V₂ hrec
  unfold dlCont
  rw [show (fun ch : Choice α => (show List (α ⊕ Finset α) from ch).headD (Sum.inr ∅)) =
    headQ from rfl]
  dsimp only
  rw [card_smul_finset]
  have ha : (∀ u, (cls1 W' (x.map (eS σ V₂)) u).card ≤ 2 * V₂.card / 3) ↔
      ∀ u, (cls1 W x u).card ≤ 2 * V₂.card / 3 := by
    constructor
    · intro h u
      have := h (eS σ V₂ u)
      rwa [cls1_map _ hW, card_map] at this
    · intro h u'
      obtain ⟨u, rfl⟩ := (eS σ V₂).surjective u'
      rw [cls1_map _ hW, card_map]
      exact h u
  by_cases h₁ : ∀ u, (cls1 W x u).card ≤ 2 * V₂.card / 3
  · rw [ite_eq_left (ha.2 h₁), ite_eq_left h₁]
    have hsel : selThird (univ : Finset ↥(σ • V₂)) (skel1 W' (x.map (eS σ V₂))) =
        (selThird univ (skel1 W x)).map (eS σ V₂).toEmbedding := by
      rw [← selThird_map _ _ _ _ fun u => skel1_map _ hW x u, map_univ_equiv]
    rw [hsel, map_eS_subtype, pickSide_smul, ← smul_finset_sdiff, hrc, withPiece_act]
  · rw [ite_eq_right (fun h => h₁ (ha.1 h)), ite_eq_right h₁]
    have hcQ : ∀ a b, cohOn ((σ • V₁').disjSum (σ • V₂))
        (code (relabA σ A) (extCells (σ • V₂) (skel2 W' (x.map (eS σ V₂))))) (σ • a) (σ • b) =
        cohOn (V₁'.disjSum V₂) (code A (extCells V₂ (skel2 W x))) a b := by
      intro a b
      rw [← disjSum_smul]
      exact cohOn_smul σ _ (code_smul σ A (extCells_smul σ V₂ (skel2_map _ hW x))) a b
    generalize cohOn ((σ • V₁').disjSum (σ • V₂))
      (code (relabA σ A) (extCells (σ • V₂) (skel2 W' (x.map (eS σ V₂))))) = cQ' at hcQ ⊢
    generalize cohOn (V₁'.disjSum V₂) (code A (extCells V₂ (skel2 W x))) = cQ at hcQ ⊢
    have hc₂ : ∀ s, cQ' (.inr (σ • s)) (.inr (σ • s)) = cQ (.inr s) (.inr s) := fun s =>
      hcQ (.inr s) (.inr s)
    have hc₁ : ∀ y, cQ' (.inl (σ • y)) (.inl (σ • y)) = cQ (.inl y) (.inl y) := fun y =>
      hcQ (.inl y) (.inl y)
    have hf₂ : ∀ s, ((σ • V₂).filter fun s' => cQ' (.inr s') (.inr s') =
        cQ' (.inr (σ • s)) (.inr (σ • s))) =
        σ • V₂.filter fun s' => cQ (.inr s') (.inr s') = cQ (.inr s) (.inr s) := fun s =>
      filter_smul_eq σ V₂ fun s' => by rw [hc₂, hc₂]
    have hf₁ : ∀ y, ((σ • V₁').filter fun y' => cQ' (.inl y') (.inl y') =
        cQ' (.inl (σ • y)) (.inl (σ • y))) =
        σ • V₁'.filter fun y' => cQ (.inl y') (.inl y') = cQ (.inl y) (.inl y) := fun y =>
      filter_smul_eq σ V₁' fun y' => by rw [hc₁, hc₁]
    have hb₁ : (∀ s ∈ σ • V₂, ((σ • V₂).filter fun s' => cQ' (.inr s') (.inr s') =
        cQ' (.inr s) (.inr s)).card ≤ 2 * V₂.card / 3) ↔
        ∀ s ∈ V₂, (V₂.filter fun s' => cQ (.inr s') (.inr s') = cQ (.inr s) (.inr s)).card ≤
          2 * V₂.card / 3 := by
      constructor
      · intro h s hs
        have := h (σ • s) (smul_mem_smul_finset hs)
        rwa [hf₂, card_smul_finset] at this
      · intro h s hs
        obtain ⟨s, rfl⟩ := exists_smul_eq σ s
        rw [hf₂, card_smul_finset]
        exact h s ((smul_mem_smul_finset_iff σ).1 hs)
    by_cases h₂ : ∀ s ∈ V₂, (V₂.filter fun s' => cQ (.inr s') (.inr s') =
        cQ (.inr s) (.inr s)).card ≤ 2 * V₂.card / 3
    · rw [ite_eq_left (hb₁.2 h₂), ite_eq_left h₂]
      have hsel : selThird (σ • V₂) (fun s => cQ' (.inr s) (.inr s)) =
          σ • selThird V₂ (fun s => cQ (.inr s) (.inr s)) := by
        rw [smul_eq_map, smul_eq_map, selThird_map _ _ _ _ fun s => hc₂ s]
      rw [hsel, pickSide_smul, ← smul_finset_sdiff, hrc, withPiece_act]
    · rw [ite_eq_right (fun h => h₂ (hb₁.1 h)), ite_eq_right h₂]
      have hC₂ : ((σ • V₂).filter fun s => 2 * V₂.card / 3 <
          ((σ • V₂).filter fun s' => cQ' (.inr s') (.inr s') = cQ' (.inr s) (.inr s)).card) =
          σ • V₂.filter fun s => 2 * V₂.card / 3 <
            (V₂.filter fun s' => cQ (.inr s') (.inr s') = cQ (.inr s) (.inr s)).card :=
        filter_smul_eq σ V₂ fun s => by rw [hf₂, card_smul_finset]
      have hC₁ : ((σ • V₁').filter fun y => t <
          ((σ • V₁').filter fun y' => cQ' (.inl y') (.inl y') = cQ' (.inl y) (.inl y)).card) =
          σ • V₁'.filter fun y => t <
            (V₁'.filter fun y' => cQ (.inl y') (.inl y') = cQ (.inl y) (.inl y)).card :=
        filter_smul_eq σ V₁' fun y => by rw [hf₁, card_smul_finset]
      rw [hC₂, hC₁]
      generalize V₂.filter (fun s => 2 * V₂.card / 3 <
        (V₂.filter fun s' => cQ (.inr s') (.inr s') = cQ (.inr s) (.inr s)).card) = C₂
      generalize V₁'.filter (fun y => t <
        (V₁'.filter fun y' => cQ (.inl y') (.inl y') = cQ (.inl y) (.inl y)).card) = C₁
      by_cases h₃ : C₁ = ∅
      · rw [ite_eq_left (by rw [h₃, smul_finset_empty]), ite_eq_left h₃]
        rw [BipRelabel.colPart_smul σ V₁' (f := fun y => cQ (.inl y) (.inl y)) hc₁,
          ← smul_finset_sdiff, ← addPiece_smul]
        rfl
      · rw [ite_eq_right (fun h => h₃ (smul_finset_eq_empty.1 h)), ite_eq_right h₃]
        have hk : (∀ y ∈ σ • C₁, ∀ s ∈ σ • C₂, ∀ y' ∈ σ • C₁, ∀ s' ∈ σ • C₂,
            cQ' (.inl y) (.inr s) = cQ' (.inl y') (.inr s')) ↔
            ∀ y ∈ C₁, ∀ s ∈ C₂, ∀ y' ∈ C₁, ∀ s' ∈ C₂,
              cQ (.inl y) (.inr s) = cQ (.inl y') (.inr s') := by
          have e : ∀ y s, cQ' (.inl (σ • y)) (.inr (σ • s)) = cQ (.inl y) (.inr s) :=
            fun y s => hcQ (.inl y) (.inr s)
          constructor
          · intro h y hy s hs y' hy' s' hs'
            have := h _ (smul_mem_smul_finset hy) _ (smul_mem_smul_finset hs) _
              (smul_mem_smul_finset hy') _ (smul_mem_smul_finset hs')
            rwa [e, e] at this
          · intro h y hy s hs y' hy' s' hs'
            obtain ⟨y, rfl⟩ := exists_smul_eq σ y
            obtain ⟨s, rfl⟩ := exists_smul_eq σ s
            obtain ⟨y', rfl⟩ := exists_smul_eq σ y'
            obtain ⟨s', rfl⟩ := exists_smul_eq σ s'
            rw [e, e]
            exact h y ((smul_mem_smul_finset_iff σ).1 hy) s ((smul_mem_smul_finset_iff σ).1 hs)
              y' ((smul_mem_smul_finset_iff σ).1 hy') s' ((smul_mem_smul_finset_iff σ).1 hs')
        refine ite_eq_app (fun T : STree α => T.act σ) hk (fun _ => ?_) (fun _ => ?_)
        · rw [← smul_finset_sdiff, ← smul_finset_sdiff, hrc, withPiece_act]
        · have hrel : cQ' = relab2 (τ σ) cQ := by
            funext a b
            show cQ' a b = cQ ((τ σ)⁻¹ • a) ((τ σ)⁻¹ • b)
            rw [τ_inv_smul, τ_inv_smul, ← hcQ, smul_inv_smul, smul_inv_smul]
          have key := trans_bind_act (C' := Choice α) (τ σ) σ (f := fun q => [q]) (r := headQ)
            (fun q => rfl) (headQ_smul σ) (k := cohCont t V₁ V₁' C₁ (shrink V₂ rec))
            (k' := cohCont t (σ • V₁) (σ • V₁') (σ • C₁) (shrink (σ • V₂) rec'))
            (fun o => cohCont_smul σ t V₁ V₁' C₁ hrc o)
            (cohSoj (C₁.map ⟨Sum.inl, Sum.inl_injective⟩) (C₂.map ⟨Sum.inr, Sum.inr_injective⟩)
              cQ)
          rw [← coherent_split_or_johnson_relabel, ← map_inl_smul, ← map_inr_smul, ← hrel]
            at key
          exact key

/-- **One level of Bipartite Split-or-Johnson, canonically.** -/
theorem bstep_relabel (σ : Equiv.Perm α) (t : ℕ) (V₁ : Finset α) (V₂ : Finset (Finset α))
    (A : α → Finset α → Bool)
    {rec rec' : Finset α → Finset (Finset α) → (α → Finset α → Bool) → STree α}
    (hrec : ∀ a b c, rec' (σ • a) (σ • b) (relabA σ c) = (rec a b c).act σ) :
    bstep t (σ • V₁) (σ • V₂) (relabA σ A) rec' = (bstep t V₁ V₂ A rec).act σ := by
  unfold bstep
  rw [card_smul_finset]
  by_cases h : (bigDegs t V₁ V₂ A).Nonempty
  · rw [dite_eq_left (show (bigDegs t (σ • V₁) (σ • V₂) (relabA σ A)).Nonempty by
      rwa [bigDegs_smul]), dite_eq_left h, min'_eq_of_eq (bigDegs_smul σ t V₁ V₂ A) _ h]
    generalize (bigDegs t V₁ V₂ A).min' h = d₁
    dsimp only
    rw [tfDeg_smul, card_smul_finset]
    by_cases hJ : (tfDeg V₁ V₂ A d₁).card = V₂.card.choose (sOf V₂.card d₁)
    · rw [ite_eq_left hJ, ite_eq_left hJ]
      show CTree.leaf _ = CTree.leaf (σ • _)
      have hf : fOf (σ • V₂) (relabA σ A) d₁ = fun v => σ • fOf V₂ A d₁ (σ⁻¹ • v) := by
        funext v
        obtain ⟨v, rfl⟩ := exists_smul_eq σ v
        rw [fOf_smul, inv_smul_smul]
      rw [hf]
      rfl
    rw [ite_eq_right hJ, ite_eq_right hJ]
    by_cases hb : IsBase t V₂.card
    · rw [ite_eq_left hb, ite_eq_left hb]
      show CTree.node _ _ = CTree.node _ _
      rw [enums_smul]
      congr 1
      funext e
      show CTree.leaf _ = CTree.leaf (σ • _)
      obtain ⟨e₀, rfl⟩ := exists_smul_eq σ e
      rw [inv_smul_smul, choiceCells_smul,
        BipRelabel.colPart_smul σ V₁ (f := nbrCode A (choiceCells e₀))
          fun y => nbrCode_smul σ A _ y]
      rfl
    rw [ite_eq_right hb, ite_eq_right hb, image_fOf_smul]
    generalize (tfDeg V₁ V₂ A d₁).image (fOf V₂ A d₁) = H
    generalize arity V₂.card (sOf V₂.card d₁) (tfDeg V₁ V₂ A d₁).card = d
    have hcd := daryCol_smul σ V₂ H d
    rw [bigTwins_smul σ V₂ _ _ hcd]
    by_cases hS : (bigTwins V₂ (daryCol V₂ H d)).Nonempty
    · rw [ite_eq_left (smul_finset_nonempty.2 hS), ite_eq_left hS, pickSide_smul,
        ← smul_finset_sdiff, hrec, withPiece_act]
    · rw [ite_eq_right (fun h' => hS (smul_finset_nonempty.1 h')), ite_eq_right hS]
      have hW : ∀ y, wlOn d (daryCol (σ • V₂) (σ • H) d) (⇑(eS σ V₂) ∘ y) =
          wlOn d (daryCol V₂ H d) y := by
        intro y
        have hn := wlOn_natural (k := d) (eS σ V₂) (daryCol (σ • V₂) (σ • H) d)
        have hfun : (fun x => daryCol (σ • V₂) (σ • H) d (⇑(eS σ V₂) ∘ x)) =
            daryCol V₂ H d := funext hcd
        rw [hfun] at hn
        rw [hn]
      show CTree.node _ _ = CTree.node _ _
      rw [nodeSet_smul σ V₂ _ _ hW]
      congr 1
      funext ch
      obtain ⟨ch₀, rfl⟩ := exists_smul_eq σ ch
      rw [inv_smul_smul, decodeV₂_smul]
      exact dlCont_relabel σ t V₁ _ V₂ A _ _ hW hrec _
  · rw [dite_eq_right (show ¬ (bigDegs t (σ • V₁) (σ • V₂) (relabA σ A)).Nonempty by
      rwa [bigDegs_smul]), dite_eq_right h]
    show CTree.leaf _ = CTree.leaf (σ • _)
    rw [twinPart_smul]
    rfl

end BipRelabel

open BipRelabel in
/-- **Bipartite Split-or-Johnson is canonical.** -/
theorem bipartite_split_or_johnson_relabel (σ : Equiv.Perm α) (t : ℕ) (V₁ : Finset α)
    (V₂ : Finset (Finset α)) (A : α → Finset α → Bool) :
    bsoj t (σ • V₁) (σ • V₂) (relabA σ A) = (bsoj t V₁ V₂ A).act σ := by
  induction hn : V₂.card using Nat.strong_induction_on generalizing V₁ V₂ A with
  | _ n ih =>
    rw [bsoj.eq_1 t (σ • V₁), bsoj.eq_1 t V₁]
    refine bstep_relabel σ t V₁ V₂ A fun a b c => ?_
    rw [card_smul_finset, card_smul_finset]
    by_cases hb : b.card < V₂.card
    · rw [dite_eq_left hb, dite_eq_left hb]
      exact ih b.card (hn ▸ hb) a b c rfl
    · rw [dite_eq_right hb, dite_eq_right hb]
      rfl

end GraphIso.SplitJohnson
