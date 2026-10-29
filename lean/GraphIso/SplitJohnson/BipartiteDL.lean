module

public import GraphIso.SplitJohnson.BipartiteBasic
public import GraphIso.SplitJohnson.CoherentSpec
public import GraphIso.SplitJohnson.DLAux
public import GraphIso.Coherent.Skeleton

/-!
# Bipartite Split-or-Johnson: after the Design Lemma's choice

`dlCont_valid`: after a good choice `x` (Design Lemma, threshold `t₂ = ⌊2v/3⌋`), every branch of
`dlCont` gives valid leaves, given valid recursive calls on fewer cells.
* (a) Without a dominant colour, `selThird` takes more than a third and at most two thirds of
  `V₂`, and Exercise 5.5 (`pickSide`) keeps the twin classes of `V₁'` below `|V₁'|/2 + 1`.
* (b) The classical Weisfeiler–Leman refinement `cQ` of the graph on `V₁' ⊔ V₂` (with the
  2-skeleton `Y` on `V₂`) is coherent and refines `Y`. Without a dominant class on `V₂`, as in
  (a). Otherwise the dominant class `C₂` lies in the Design Lemma's class `C`, so `X[C₂]` is not
  a clique (Exercise 2.15). Without a class `C₁ ⊆ V₁'` of more than `t` points, the colouring of
  `V₁'` is a colored `t`-partition. A constant colour on `C₁ × C₂` makes `C₁` a twin class with
  respect to `C₂`, and Exercise 5.5 sends the recursion to `V₂ \ C₂`. Otherwise Coherent
  Split-or-Johnson applies to `C₁ ⊔ C₂`, and its bipartite graph, with ideal points turned into
  cells by union, satisfies the invariant (`cohCont_valid`).

The branch (b) is stated for an abstract refinement `cQ` (`contB`, `contB_valid`).
-/

@[expose] public section

namespace GraphIso.SplitJohnson

open Finset Pointwise GraphIso.Coherent

variable {α : Type*} [DecidableEq α]

/-! ### Leaves and pieces -/

omit [DecidableEq α] in
theorem leaf_valid {V : Finset α} {t : ℕ} {p : CPart α} (hp : IsColPart V t p) :
    (CTree.leaf (some (Sum.inl p)) : STree α).Live ∧
      (CTree.leaf (some (Sum.inl p)) : STree α).AllLeaves (ValidOut V t) :=
  ⟨trivial, hp⟩

omit [DecidableEq α] in
theorem IsColPart.mono {V : Finset α} {k t : ℕ} {p : CPart α} (hp : IsColPart V k p)
    (hkt : k ≤ t) : IsColPart V t p :=
  ⟨hp.mem_blk, hp.blk_sub, hp.blk_eq, hp.col_eq, hp.card_eq, hp.admissible,
    fun v hv => (hp.card_le v hv).trans hkt⟩

/-- Adding the complement of `W` in `V` as a piece. -/
theorem isColPart_addPiece' {W V : Finset α} {t : ℕ} {p : CPart α} (hp : IsColPart W t p)
    (hWV : W ⊆ V) (hD : (V \ W).card ≤ t) : IsColPart V t (addPiece (V \ W) p) := by
  have := isColPart_addPiece hp sdiff_disjoint hD
  rwa [sdiff_union_of_subset hWV] at this

/-- A tree with the complement of `W` in `V` as a piece. -/
theorem withPiece_valid' {W V : Finset α} {t : ℕ} {T : STree α}
    (hT : T.Live ∧ T.AllLeaves (ValidOut W t)) (hWV : W ⊆ V) (hD : (V \ W).card ≤ t) :
    (withPiece (V \ W) T).Live ∧ (withPiece (V \ W) T).AllLeaves (ValidOut V t) := by
  have := withPiece_valid hT sdiff_disjoint hD
  rwa [sdiff_union_of_subset hWV] at this

omit [DecidableEq α] in
/-- Validity of both branches of an `if`. -/
theorem ite_valid {c : Prop} [Decidable c] {V : Finset α} {t : ℕ} {a b : STree α}
    (ha : c → a.Live ∧ a.AllLeaves (ValidOut V t))
    (hb : ¬ c → b.Live ∧ b.AllLeaves (ValidOut V t)) :
    (if c then a else b).Live ∧ (if c then a else b).AllLeaves (ValidOut V t) := by
  split_ifs with h
  · exact ha h
  · exact hb h

/-! ### Recursion on a part of `V₂` -/

/-- **A recursive call on `V₁'` and a part of `V₂`**, with the piece `V₁ \ V₁'`. -/
theorem recPiece_valid {t : ℕ} {V₁ V₁' : Finset α} {V₂ V₂' : Finset (Finset α)}
    {A : α → Finset α → Bool} (h : BInv t V₁ V₂ A) (hV₁' : V₁' ⊆ V₁) (htV₁' : t < V₁'.card)
    (hv : 6 ≤ V₂.card) (hsub : V₂' ⊆ V₂) (h3 : 3 * V₂'.card ≤ 2 * V₂.card)
    (htw : ∀ x ∈ V₁', 2 * (twinCls V₁' V₂' A x).card < V₁'.card + 2)
    {rec : Finset α → Finset (Finset α) → (α → Finset α → Bool) → STree α}
    (hrec : ∀ V₁'' V₂'' A'', V₂''.card < V₂.card → BInv t V₁'' V₂'' A'' →
      (rec V₁'' V₂'' A'').Live ∧ (rec V₁'' V₂'' A'').AllLeaves (ValidOut V₁'' t)) :
    (withPiece (V₁ \ V₁') (shrink V₂ rec V₁' V₂' A)).Live ∧
      (withPiece (V₁ \ V₁') (shrink V₂ rec V₁' V₂' A)).AllLeaves (ValidOut V₁ t) := by
  have hcard := card_le_card hV₁'
  have hv1 := h.v₁_le
  have hinv : BInv t V₁' V₂' A :=
    ⟨fun s hs => h.cells_ne s (hsub hs),
      fun s hs s' hs' => h.cells_disj s (hsub hs) s' (hsub hs'),
      (card_le_card hsub).trans h.v_le, by omega, htV₁',
      fun x hx => by have := htw x hx; omega⟩
  have hr := hrec V₁' V₂' A (by omega) hinv
  unfold shrink
  rw [ite_eq_left h3]
  exact withPiece_valid' hr hV₁' (by rw [card_sdiff_of_subset hV₁']; omega)

/-- **Recursion on the side of a third `S` chosen by Exercise 5.5.** -/
theorem third_valid {t : ℕ} {V₁ V₁' : Finset α} {V₂ S : Finset (Finset α)}
    {A : α → Finset α → Bool} (h : BInv t V₁ V₂ A) (hV₁' : V₁' ⊆ V₁) (htV₁' : t < V₁'.card)
    (htf : ∀ x ∈ V₁', twinCls V₁' V₂ A x = {x}) (hv : 6 ≤ V₂.card) (hS : S ⊆ V₂)
    (h1 : V₂.card < 3 * S.card) (h2 : 3 * S.card ≤ 2 * V₂.card)
    {rec : Finset α → Finset (Finset α) → (α → Finset α → Bool) → STree α}
    (hrec : ∀ V₁'' V₂'' A'', V₂''.card < V₂.card → BInv t V₁'' V₂'' A'' →
      (rec V₁'' V₂'' A'').Live ∧ (rec V₁'' V₂'' A'').AllLeaves (ValidOut V₁'' t)) :
    (withPiece (V₁ \ V₁') (shrink V₂ rec V₁' (pickSide V₁' V₂ S A) A)).Live ∧
      (withPiece (V₁ \ V₁') (shrink V₂ rec V₁' (pickSide V₁' V₂ S A) A)).AllLeaves
        (ValidOut V₁ t) := by
  refine recPiece_valid h hV₁' htV₁' hv (pickSide_subset _ _ hS) ?_ (pickSide_twin htf hS) hrec
  have hsd := card_sdiff_of_subset hS
  rcases pickSide_card V₁' V₂ S A with e | e <;> rw [e] <;> omega

/-! ### Uniqueness of a large class -/

/-- Two classes of a colouring with more than `k` points each, in a set of fewer than
`2k + 2` points, are the same class. -/
theorem eq_of_big {β : Type*} [DecidableEq β] {S : Finset β} {f : β → ℕ} {k : ℕ}
    (hk : S.card < 2 * k + 2)
    {a b : β} (hka : k < (S.filter fun y => f y = f a).card)
    (hkb : k < (S.filter fun y => f y = f b).card) : f a = f b := by
  by_contra hab
  have hdis : Disjoint (S.filter fun y => f y = f a) (S.filter fun y => f y = f b) := by
    rw [Finset.disjoint_left]
    intro y h1 h2
    rw [mem_filter] at h1 h2
    exact hab (h1.2.symm.trans h2.2)
  have := card_union_of_disjoint hdis
  have hsub : (S.filter fun y => f y = f a) ∪ (S.filter fun y => f y = f b) ⊆ S :=
    union_subset (filter_subset _ _) (filter_subset _ _)
  have := card_le_card hsub
  omega

/-! ### After Coherent Split-or-Johnson -/

/-- **After Coherent Split-or-Johnson on `C₁ ⊔ C₂`.** -/
theorem cohCont_valid {t : ℕ} {V₁ V₁' C₁ : Finset α} {V₂ C₂ : Finset (Finset α)}
    {A : α → Finset α → Bool} (h : BInv t V₁ V₂ A) (hV₁' : V₁' ⊆ V₁) (htV₁' : t < V₁'.card)
    (hC₁ : C₁ ⊆ V₁') (htC₁ : t < C₁.card) (hC₂ : C₂ ⊆ V₂) (hv : 6 ≤ V₂.card)
    {rec : Finset α → Finset (Finset α) → (α → Finset α → Bool) → STree α}
    (hrec : ∀ V₁'' V₂'' A'', V₂''.card < V₂.card → BInv t V₁'' V₂'' A'' →
      (rec V₁'' V₂'' A'').Live ∧ (rec V₁'' V₂'' A'').AllLeaves (ValidOut V₁'' t))
    {o : Option (CohOut (α ⊕ Finset α))}
    (ho : CohValid (C₁.map ⟨Sum.inl, Sum.inl_injective⟩) (C₂.map ⟨Sum.inr, Sum.inr_injective⟩)
      o) :
    (cohCont t V₁ V₁' C₁ (shrink V₂ rec) o).Live ∧
      (cohCont t V₁ V₁' C₁ (shrink V₂ rec) o).AllLeaves (ValidOut V₁ t) := by
  have hcV₁' := card_le_card hV₁'
  have hcC₁ := card_le_card hC₁
  have hcC₂ := card_le_card hC₂
  have hv1 := h.v₁_le
  have hvt := h.v_le
  have hpV₁ : (V₁ \ V₁').card ≤ t := by rw [card_sdiff_of_subset hV₁']; omega
  have hpC₁ : (V₁' \ C₁).card ≤ t := by rw [card_sdiff_of_subset hC₁]; omega
  match o, ho with
  | none, ho => exact ho.elim
  | some (.part p), ho =>
    have hp := isColPart_toLeft ho
    rw [card_map] at hp
    refine leaf_valid (isColPart_addPiece' (isColPart_addPiece' (hp.mono ?_) hC₁ hpC₁)
      hV₁' hpV₁)
    omega
  | some (.bip W₁ W₂ A'), ho =>
    obtain ⟨hW₁, hcW₁, hB, hBd, hcW₂, htw⟩ := ho
    rw [card_map] at hcW₁ hcW₂
    have hcW := card_toLeft_of_subset hW₁
    have hWC : W₁.toLeft ⊆ C₁ := by
      intro y hy
      obtain ⟨z, hz, e⟩ := mem_map.1 (hW₁ (mem_toLeft.1 hy))
      simp only [Function.Embedding.coeFn_mk, Sum.inl.injEq] at e
      exact e ▸ hz
    have hpW : (C₁ \ W₁.toLeft).card ≤ t := by rw [card_sdiff_of_subset hWC]; omega
    unfold cohCont
    dsimp only
    by_cases hW : W₁.toLeft.card ≤ t
    · rw [ite_eq_left hW]
      refine leaf_valid (isColPart_addPiece' (isColPart_addPiece' (isColPart_addPiece'
        (colPart_valid fun y _ => ?_) hWC hpW) hC₁ hpC₁) hV₁' hpV₁)
      exact (card_le_card (filter_subset _ _)).trans hW
    · rw [ite_eq_right hW]
      have hBsub : ∀ B ∈ W₂, B ⊆ V₂.map ⟨Sum.inr, Sum.inr_injective⟩ := fun B hB' =>
        (hB B hB').2.trans (map_subset_map.2 hC₂)
      have hinj : ∀ B ∈ W₂, ∀ B' ∈ W₂, cellOf B = cellOf B' → B = B' := by
        intro B hB' B' hB'' e
        by_contra hne
        have hd := cellOf_disjoint h.cells_disj (hBsub B hB') (hBsub B' hB'')
          (hBd B hB' B' hB'' hne)
        rw [e, disjoint_self_iff_empty] at hd
        have := cellOf_nonempty h.cells_ne (hB B' hB'').1 (hBsub B' hB'')
        rw [hd] at this
        exact Finset.not_nonempty_empty this
      have hci : (W₂.image cellOf).card ≤ W₂.card := card_image_le
      have h3 : 3 * (W₂.image cellOf).card ≤ 2 * V₂.card := by omega
      set A'' : α → Finset α → Bool :=
        fun x s => decide (∃ B ∈ W₂, cellOf B = s ∧ A' (.inl x) B = true) with hA''
      have hA : ∀ y, ∀ B ∈ W₂, A'' y (cellOf B) = A' (.inl y) B := by
        intro y B hB'
        rw [hA'']
        by_cases hy : A' (.inl y) B = true
        · rw [hy]
          exact decide_eq_true ⟨B, hB', rfl, hy⟩
        · rw [Bool.not_eq_true] at hy
          rw [hy]
          refine decide_eq_false ?_
          rintro ⟨B', hB'', e, h'⟩
          rw [hinj B' hB'' B hB' e, hy] at h'
          exact Bool.false_ne_true h'
      have hinv : BInv t W₁.toLeft (W₂.image cellOf) A'' := by
        refine ⟨fun s hs => ?_, fun s hs s' hs' hne => ?_, by omega,
          by have := card_le_card hWC; omega, by omega, fun y hy => ?_⟩
        · obtain ⟨B, hB', rfl⟩ := mem_image.1 hs
          exact cellOf_nonempty h.cells_ne (hB B hB').1 (hBsub B hB')
        · obtain ⟨B, hB', rfl⟩ := mem_image.1 hs
          obtain ⟨B', hB'', rfl⟩ := mem_image.1 hs'
          exact cellOf_disjoint h.cells_disj (hBsub B hB') (hBsub B' hB'')
            (hBd B hB' B' hB'' fun e => hne (e ▸ rfl))
        · have hsub : twinCls W₁.toLeft (W₂.image cellOf) A'' y ⊆
              (twinCls W₁ W₂ A' (.inl y)).toLeft := by
            intro y' hy'
            rw [mem_twinCls] at hy'
            rw [mem_toLeft, mem_twinCls]
            refine ⟨mem_toLeft.1 hy'.1, fun B hB' => ?_⟩
            have := hy'.2 (cellOf B) (mem_image_of_mem _ hB')
            rwa [hA y B hB', hA y' B hB'] at this
          have h1 := card_le_card hsub
          have h2 : (twinCls W₁ W₂ A' (.inl y)).toLeft.card ≤
              (twinCls W₁ W₂ A' (.inl y)).card := by
            have := card_toLeft_add_card_toRight (u := twinCls W₁ W₂ A' (.inl y))
            omega
          have h3 := htw _ (mem_toLeft.1 hy)
          have h4 := card_le_card hWC
          omega
      have hr := hrec _ _ _ (by omega) hinv
      have hr' : (shrink V₂ rec W₁.toLeft (W₂.image cellOf) A'').Live ∧
          (shrink V₂ rec W₁.toLeft (W₂.image cellOf) A'').AllLeaves
            (ValidOut W₁.toLeft t) := by
        unfold shrink
        rw [ite_eq_left h3]
        exact hr
      exact withPiece_valid' (withPiece_valid' (withPiece_valid' hr' hWC hpW) hC₁ hpC₁) hV₁'
        hpV₁

/-! ### The branch with a dominant class -/

/-- The branch (b) of `dlCont`, with the classical refinement `cQ` abstracted. -/
def contB (t : ℕ) (V₁ V₁' : Finset α) (V₂ : Finset (Finset α)) (A : α → Finset α → Bool)
    (rc : Finset α → Finset (Finset α) → (α → Finset α → Bool) → STree α)
    (cQ : α ⊕ Finset α → α ⊕ Finset α → ℕ) : STree α :=
  let t₂ := 2 * V₂.card / 3
  let col₂ := fun s => cQ (.inr s) (.inr s)
  if ∀ s ∈ V₂, (V₂.filter fun s' => col₂ s' = col₂ s).card ≤ t₂ then
    withPiece (V₁ \ V₁') (rc V₁' (pickSide V₁' V₂ (selThird V₂ col₂) A) A)
  else
    let C₂ := V₂.filter fun s => t₂ < (V₂.filter fun s' => col₂ s' = col₂ s).card
    let col₁ := fun y => cQ (.inl y) (.inl y)
    let C₁ := V₁'.filter fun y => t < (V₁'.filter fun y' => col₁ y' = col₁ y).card
    if C₁ = ∅ then
      .leaf (some (.inl (addPiece (V₁ \ V₁') (colPart V₁' col₁))))
    else if ∀ y ∈ C₁, ∀ s ∈ C₂, ∀ y' ∈ C₁, ∀ s' ∈ C₂,
        cQ (.inl y) (.inr s) = cQ (.inl y') (.inr s') then
      withPiece (V₁ \ V₁') (rc V₁' (V₂ \ C₂) A)
    else
      ((cohSoj (C₁.map ⟨Sum.inl, Sum.inl_injective⟩) (C₂.map ⟨Sum.inr, Sum.inr_injective⟩)
          cQ).trans (fun q => [q]) (fun ch : Choice α =>
            (show List (α ⊕ Finset α) from ch).headD (.inr ∅)) id).bind
        (cohCont t V₁ V₁' C₁ rc)

theorem dlCont_eq_contB (t : ℕ) (V₁ V₁' : Finset α) (V₂ : Finset (Finset α))
    (A : α → Finset α → Bool) {d : ℕ} (W : (Fin d → V₂) → ℕ)
    (rec : Finset α → Finset (Finset α) → (α → Finset α → Bool) → STree α) (x : List V₂)
    (ha : ¬ ∀ u, (cls1 W x u).card ≤ 2 * V₂.card / 3) :
    dlCont t V₁ V₁' V₂ A W rec x = contB t V₁ V₁' V₂ A (shrink V₂ rec)
      (cohOn (V₁'.disjSum V₂) (code A (extCells V₂ (skel2 W x)))) := by
  simp only [dlCont, contB, ite_eq_right ha]

/-- **The branch with a dominant class**, for any coherent refinement `cQ` on `V₁' ⊔ V₂` of
the initial colours with a non-clique 2-skeleton `Y` on its dominant class `C`. -/
theorem contB_valid {t : ℕ} {V₁ V₁' : Finset α} {V₂ : Finset (Finset α)}
    {A : α → Finset α → Bool} (h : BInv t V₁ V₂ A) (hV₁' : V₁' ⊆ V₁) (htV₁' : t < V₁'.card)
    (htf : ∀ x ∈ V₁', twinCls V₁' V₂ A x = {x}) (hv : 6 ≤ V₂.card)
    {Y : V₂ → V₂ → ℕ} (hY : IsCoherent2 Y) {C : Finset V₂} (hCt : 2 * V₂.card / 3 < C.card)
    (hCcls : ∀ w ∈ C, ∀ w', w' ∈ C ↔ Y w' w' = Y w w) (hnc : ¬ IsClique Y C)
    {cQ : α ⊕ Finset α → α ⊕ Finset α → ℕ} (hcoh : IsCoh2On (V₁'.disjSum V₂) cQ)
    (href : ∀ a ∈ V₁'.disjSum V₂, ∀ b ∈ V₁'.disjSum V₂, ∀ a' ∈ V₁'.disjSum V₂,
      ∀ b' ∈ V₁'.disjSum V₂, cQ a b = cQ a' b' →
        code A (extCells V₂ Y) a b = code A (extCells V₂ Y) a' b')
    {rec : Finset α → Finset (Finset α) → (α → Finset α → Bool) → STree α}
    (hrec : ∀ V₁'' V₂'' A'', V₂''.card < V₂.card → BInv t V₁'' V₂'' A'' →
      (rec V₁'' V₂'' A'').Live ∧ (rec V₁'' V₂'' A'').AllLeaves (ValidOut V₁'' t)) :
    (contB t V₁ V₁' V₂ A (shrink V₂ rec) cQ).Live ∧
      (contB t V₁ V₁' V₂ A (shrink V₂ rec) cQ).AllLeaves (ValidOut V₁ t) := by
  have hcV₁' := card_le_card hV₁'
  have hv1 := h.v₁_le
  have hvt := h.v_le
  have hml : ∀ y, (Sum.inl y : α ⊕ Finset α) ∈ V₁'.disjSum V₂ ↔ y ∈ V₁' :=
    fun _ => inl_mem_disjSum
  have hmr : ∀ s, (Sum.inr s : α ⊕ Finset α) ∈ V₁'.disjSum V₂ ↔ s ∈ V₂ :=
    fun _ => inr_mem_disjSum
  have hside : ∀ y ∈ V₁', ∀ s ∈ V₂, cQ (.inl y) (.inl y) ≠ cQ (.inr s) (.inr s) := by
    intro y hy s hs e
    exact code_diag_ne A _ y s
      (href _ ((hml y).2 hy) _ ((hml y).2 hy) _ ((hmr s).2 hs) _ ((hmr s).2 hs) e)
  have hext : ∀ s (hs : s ∈ V₂) s' (hs' : s' ∈ V₂),
      extCells V₂ Y s s' = Y ⟨s, hs⟩ ⟨s', hs'⟩ := by
    intro s hs s' hs'
    unfold extCells
    rw [dite_eq_left ⟨hs, hs'⟩]
  have hY2 : ∀ s (hs : s ∈ V₂) s' (hs' : s' ∈ V₂) r (hr : r ∈ V₂) r' (hr' : r' ∈ V₂),
      cQ (.inr s) (.inr s') = cQ (.inr r) (.inr r') →
        Y ⟨s, hs⟩ ⟨s', hs'⟩ = Y ⟨r, hr⟩ ⟨r', hr'⟩ := by
    intro s hs s' hs' r hr r' hr' e
    have := code_inr_inr (href _ ((hmr s).2 hs) _ ((hmr s').2 hs') _ ((hmr r).2 hr) _
      ((hmr r').2 hr') e)
    rwa [hext s hs s' hs', hext r hr r' hr'] at this
  have hAeq : ∀ y ∈ V₁', ∀ s ∈ V₂, ∀ y' ∈ V₁', ∀ s' ∈ V₂,
      cQ (.inl y) (.inr s) = cQ (.inl y') (.inr s') → A y s = A y' s' :=
    fun y hy s hs y' hy' s' hs' e => code_inl_inr (href _ ((hml y).2 hy) _ ((hmr s).2 hs) _
      ((hml y').2 hy') _ ((hmr s').2 hs') e)
  unfold contB
  dsimp only
  by_cases hb1 : ∀ s ∈ V₂, (V₂.filter fun s' =>
      cQ (.inr s') (.inr s') = cQ (.inr s) (.inr s)).card ≤ 2 * V₂.card / 3
  · rw [ite_eq_left hb1]
    have hne : V₂.Nonempty := card_pos.1 (by omega)
    obtain ⟨hsub, h1, h2⟩ := selThird_spec V₂ (fun s => cQ (.inr s) (.inr s)) hne
      (fun s hs => by have := hb1 s hs; omega)
    exact third_valid h hV₁' htV₁' htf hv hsub h1 h2 hrec
  rw [ite_eq_right hb1]
  push Not at hb1
  obtain ⟨s₀, hs₀, hbig⟩ := hb1
  set C₂ := V₂.filter fun s => 2 * V₂.card / 3 <
    (V₂.filter fun s' => cQ (.inr s') (.inr s') = cQ (.inr s) (.inr s)).card with hC₂def
  have hk₂ : V₂.card < 2 * (2 * V₂.card / 3) + 2 := by omega
  have hiff₂ : ∀ s ∈ V₂, 2 * V₂.card / 3 <
      (V₂.filter fun s' => cQ (.inr s') (.inr s') = cQ (.inr s) (.inr s)).card ↔
        cQ (.inr s) (.inr s) = cQ (.inr s₀) (.inr s₀) := by
    intro s hs
    constructor
    · intro hb
      exact eq_of_big (f := fun s => cQ (.inr s) (.inr s)) hk₂ hb hbig
    · intro e
      have : (V₂.filter fun s' => cQ (.inr s') (.inr s') = cQ (.inr s) (.inr s)) =
          V₂.filter fun s' => cQ (.inr s') (.inr s') = cQ (.inr s₀) (.inr s₀) := by
        rw [e]
      rw [this]
      exact hbig
  have hmemC₂ : ∀ s ∈ V₂, s ∈ C₂ ↔ cQ (.inr s) (.inr s) = cQ (.inr s₀) (.inr s₀) := by
    intro s hs
    rw [hC₂def, mem_filter]
    exact ⟨fun h' => (hiff₂ s hs).1 h'.2, fun e => ⟨hs, (hiff₂ s hs).2 e⟩⟩
  have hC₂sub : C₂ ⊆ V₂ := filter_subset _ _
  have hC₂eq : C₂ = V₂.filter fun s' => cQ (.inr s') (.inr s') = cQ (.inr s₀) (.inr s₀) := by
    rw [hC₂def]
    exact filter_congr hiff₂
  have hcC₂ : 2 * V₂.card / 3 < C₂.card := by rw [hC₂eq]; exact hbig
  -- `C₂` lies in the Design Lemma's class `C`
  set C' := C.map (Function.Embedding.subtype _) with hC'def
  have hC'sub : C' ⊆ V₂ := by
    intro s hs
    obtain ⟨w, -, rfl⟩ := mem_map.1 hs
    exact w.2
  have hcC' : C'.card = C.card := card_map _
  obtain ⟨s₁, hs₁C₂, hs₁C'⟩ : ∃ s₁, s₁ ∈ C₂ ∧ s₁ ∈ C' := by
    by_contra hno
    push Not at hno
    have hdis : Disjoint C₂ C' := Finset.disjoint_left.2 hno
    have := card_union_of_disjoint hdis
    have := card_le_card (union_subset hC₂sub hC'sub)
    omega
  obtain ⟨w₁, hw₁, rfl⟩ := mem_map.1 hs₁C'
  have hC₂C : ∀ s (hs : s ∈ C₂), (⟨s, hC₂sub hs⟩ : V₂) ∈ C := by
    intro s hs
    have e : cQ (.inr s) (.inr s) = cQ (.inr w₁.val) (.inr w₁.val) :=
      ((hmemC₂ s (hC₂sub hs)).1 hs).trans ((hmemC₂ _ w₁.2).1 hs₁C₂).symm
    have := hY2 s (hC₂sub hs) s (hC₂sub hs) w₁.val w₁.2 w₁.val w₁.2 e
    exact (hCcls w₁ hw₁ _).2 this
  -- `X[C₂]` is not a clique
  have hnclQ : ¬ IsClique cQ (C₂.map ⟨Sum.inr, Sum.inr_injective⟩) := by
    intro hcl
    set C₂' := C.filter fun w => w.val ∈ C₂ with hC₂'def
    have hB : C₂' ⊆ C := filter_subset _ _
    have hcl' : IsClique Y C₂' := by
      intro w₁ hw₁ w₂ hw₂ w₃ hw₃ w₄ hw₄ hne hne'
      rw [hC₂'def, mem_filter] at hw₁ hw₂ hw₃ hw₄
      have hne₁ : (Sum.inr w₁.val : α ⊕ Finset α) ≠ .inr w₂.val := fun e =>
        hne (Subtype.ext (Sum.inr_injective e))
      have hne₂ : (Sum.inr w₃.val : α ⊕ Finset α) ≠ .inr w₄.val := fun e =>
        hne' (Subtype.ext (Sum.inr_injective e))
      have e := hcl _ (mem_map_of_mem _ hw₁.2) _ (mem_map_of_mem _ hw₂.2) _
        (mem_map_of_mem _ hw₃.2) _ (mem_map_of_mem _ hw₄.2) hne₁ hne₂
      exact hY2 _ w₁.2 _ w₂.2 _ w₃.2 _ w₄.2 e
    have hle : C₂.card ≤ C₂'.card := by
      have : C₂ ⊆ C₂'.map (Function.Embedding.subtype _) := by
        intro s hs
        refine mem_map.2 ⟨⟨s, hC₂sub hs⟩, ?_, rfl⟩
        rw [hC₂'def, mem_filter]
        exact ⟨hC₂C s hs, hs⟩
      exact (card_le_card this).trans (card_map _).le
    have hCv : C.card ≤ V₂.card := by
      have := card_le_univ C
      rwa [Fintype.card_coe] at this
    have hcY : IsCoh2On C Y := (isCoh2On_univ hY).subset (subset_univ C)
      (fun w hw w' _ e => (hCcls w hw w').2 e.symm)
    have hhY : IsHomog C Y := fun w hw w' hw' => ((hCcls w hw w').1 hw').symm
    exact hcY.not_isClique_of_large hhY hnc hB (by omega) hcl'
  -- the dominant class `C₁` of `V₁'`
  by_cases hC₁e : (V₁'.filter fun y => t <
      (V₁'.filter fun y' => cQ (.inl y') (.inl y') = cQ (.inl y) (.inl y)).card) = ∅
  · rw [ite_eq_left hC₁e]
    refine leaf_valid (isColPart_addPiece' (colPart_valid fun y hy => ?_) hV₁'
      (by rw [card_sdiff_of_subset hV₁']; omega))
    by_contra hlt
    push Not at hlt
    have : y ∈ (V₁'.filter fun y => t <
        (V₁'.filter fun y' => cQ (.inl y') (.inl y') = cQ (.inl y) (.inl y)).card) :=
      mem_filter.2 ⟨hy, hlt⟩
    rw [hC₁e] at this
    exact Finset.notMem_empty _ this
  rw [ite_eq_right hC₁e]
  set C₁ := V₁'.filter fun y => t <
    (V₁'.filter fun y' => cQ (.inl y') (.inl y') = cQ (.inl y) (.inl y)).card with hC₁def
  obtain ⟨y₀, hy₀⟩ := nonempty_iff_ne_empty.2 hC₁e
  have hk₁ : V₁'.card < 2 * t + 2 := by omega
  have hy₀' := (mem_filter.1 hy₀)
  have hiff₁ : ∀ y ∈ V₁', t <
      (V₁'.filter fun y' => cQ (.inl y') (.inl y') = cQ (.inl y) (.inl y)).card ↔
        cQ (.inl y) (.inl y) = cQ (.inl y₀) (.inl y₀) := by
    intro y hy
    constructor
    · intro hb
      exact eq_of_big (f := fun y => cQ (.inl y) (.inl y)) hk₁ hb hy₀'.2
    · intro e
      have : (V₁'.filter fun y' => cQ (.inl y') (.inl y') = cQ (.inl y) (.inl y)) =
          V₁'.filter fun y' => cQ (.inl y') (.inl y') = cQ (.inl y₀) (.inl y₀) := by
        rw [e]
      rw [this]
      exact hy₀'.2
  have hmemC₁ : ∀ y ∈ V₁', y ∈ C₁ ↔ cQ (.inl y) (.inl y) = cQ (.inl y₀) (.inl y₀) := by
    intro y hy
    rw [hC₁def, mem_filter]
    exact ⟨fun h' => (hiff₁ y hy).1 h'.2, fun e => ⟨hy, (hiff₁ y hy).2 e⟩⟩
  have hC₁sub : C₁ ⊆ V₁' := filter_subset _ _
  have hC₁eq : C₁ = V₁'.filter fun y' => cQ (.inl y') (.inl y') = cQ (.inl y₀) (.inl y₀) := by
    rw [hC₁def]
    exact filter_congr hiff₁
  have htC₁ : t < C₁.card := by rw [hC₁eq]; exact hy₀'.2
  refine ite_valid (fun hconst => ?_) (fun hconst => ?_)
  · have hT : C₁ ⊆ twinCls V₁' C₂ A y₀ := fun y hy => mem_twinCls.2 ⟨hC₁sub hy,
      fun s hs => hAeq y₀ (hC₁sub hy₀) s (hC₂sub hs) y (hC₁sub hy) s (hC₂sub hs)
        (hconst y₀ hy₀ s hs y hy s hs)⟩
    have htf' : ∀ x ∈ V₁', twinCls V₁' (C₂ ∪ (V₂ \ C₂)) A x = {x} := by
      rw [union_sdiff_of_subset hC₂sub]
      exact htf
    rcases twin_split htf' with h1 | h2
    · have := h1 y₀ (hC₁sub hy₀)
      have := card_le_card hT
      omega
    · exact recPiece_valid h hV₁' htV₁' hv sdiff_subset
        (by rw [card_sdiff_of_subset hC₂sub]; omega) h2 hrec
  push Not at hconst
  obtain ⟨y₁, hy₁, s₂, hs₂, y₂, hy₂, s₃, hs₃, hne⟩ := hconst
  have hU : C₁.map ⟨Sum.inl, Sum.inl_injective⟩ ∪ C₂.map ⟨Sum.inr, Sum.inr_injective⟩ ⊆
      V₁'.disjSum V₂ := by
    intro q hq
    rcases mem_union.1 hq with hq | hq <;> obtain ⟨z, hz, rfl⟩ := mem_map.1 hq
    · exact (hml z).2 (hC₁sub hz)
    · exact (hmr z).2 (hC₂sub hz)
  have hclos : ∀ q ∈ C₁.map ⟨Sum.inl, Sum.inl_injective⟩ ∪ C₂.map ⟨Sum.inr, Sum.inr_injective⟩,
      ∀ q' ∈ V₁'.disjSum V₂, cQ q q = cQ q' q' →
        q' ∈ C₁.map ⟨Sum.inl, Sum.inl_injective⟩ ∪ C₂.map ⟨Sum.inr, Sum.inr_injective⟩ := by
    intro q hq q' hq' e
    rcases mem_union.1 hq with hq | hq <;> obtain ⟨z, hz, rfl⟩ := mem_map.1 hq <;>
      rcases q' with y' | s'
    · have hy' := (hml y').1 hq'
      refine mem_union_left _ (mem_map_of_mem _ ((hmemC₁ y' hy').2 ?_))
      exact e.symm.trans ((hmemC₁ z (hC₁sub hz)).1 hz)
    · exact absurd e (hside z (hC₁sub hz) s' ((hmr s').1 hq'))
    · exact absurd e.symm (hside y' ((hml y').1 hq') z (hC₂sub hz))
    · have hs' := (hmr s').1 hq'
      refine mem_union_right _ (mem_map_of_mem _ ((hmemC₂ s' hs').2 ?_))
      exact e.symm.trans ((hmemC₂ z (hC₂sub hz)).1 hz)
  have hdisj : Disjoint (C₁.map ⟨Sum.inl, Sum.inl_injective⟩)
      (C₂.map ⟨Sum.inr, Sum.inr_injective⟩) := by
    rw [Finset.disjoint_left]
    intro q hq hq'
    obtain ⟨z, -, rfl⟩ := mem_map.1 hq
    obtain ⟨z', -, e⟩ := mem_map.1 hq'
    simp at e
  obtain ⟨hlive, -, hall⟩ := coherent_split_or_johnson (hcoh.subset hU hclos) hdisj
    (fun q hq q' hq' => by
      obtain ⟨z, hz, rfl⟩ := mem_map.1 hq
      obtain ⟨z', hz', rfl⟩ := mem_map.1 hq'
      exact ((hmemC₁ z (hC₁sub hz)).1 hz).trans ((hmemC₁ z' (hC₁sub hz')).1 hz').symm)
    (fun q hq q' hq' => by
      obtain ⟨z, hz, rfl⟩ := mem_map.1 hq
      obtain ⟨z', hz', rfl⟩ := mem_map.1 hq'
      exact ((hmemC₂ z (hC₂sub hz)).1 hz).trans ((hmemC₂ z' (hC₂sub hz')).1 hz').symm)
    (fun q hq q' hq' => by
      obtain ⟨z, hz, rfl⟩ := mem_map.1 hq
      obtain ⟨z', hz', rfl⟩ := mem_map.1 hq'
      exact hside z (hC₁sub hz) z' (hC₂sub hz'))
    (by rw [card_map, card_map]; have := card_le_card hC₂sub; omega)
    ⟨_, mem_map_of_mem _ hy₁, _, mem_map_of_mem _ hs₂, _, mem_map_of_mem _ hy₂, _,
      mem_map_of_mem _ hs₃, hne⟩
    hnclQ
  have hr : ∀ q : α ⊕ Finset α,
      (fun ch : Choice α => (show List (α ⊕ Finset α) from ch).headD (.inr ∅))
        ((fun q => [q]) q) = q := fun _ => rfl
  exact ⟨CTree.live_bind (CTree.live_trans hr hlive) (CTree.allLeaves_trans hr
      (hall.mono fun o ho => (cohCont_valid h hV₁' htV₁' hC₁sub htC₁ hC₂sub hv hrec ho).1)),
    CTree.allLeaves_bind (CTree.allLeaves_trans hr
      (hall.mono fun o ho => (cohCont_valid h hV₁' htV₁' hC₁sub htC₁ hC₂sub hv hrec ho).2))⟩

/-! ### The step after the Design Lemma's choice -/

/-- **After the Design Lemma's choice.** -/
theorem dlCont_valid {t : ℕ} {V₁ V₁' : Finset α} {V₂ : Finset (Finset α)}
    {A : α → Finset α → Bool} (h : BInv t V₁ V₂ A) (hV₁' : V₁' ⊆ V₁) (htV₁' : t < V₁'.card)
    (htf : ∀ x ∈ V₁', twinCls V₁' V₂ A x = {x}) (hv : 6 ≤ V₂.card) {d : ℕ}
    (cd : (Fin d → V₂) → ℕ) {x : List V₂} (hgood : DLGood (wlOn d cd) (2 * V₂.card / 3) x)
    {rec : Finset α → Finset (Finset α) → (α → Finset α → Bool) → STree α}
    (hrec : ∀ V₁'' V₂'' A'', V₂''.card < V₂.card → BInv t V₁'' V₂'' A'' →
      (rec V₁'' V₂'' A'').Live ∧ (rec V₁'' V₂'' A'').AllLeaves (ValidOut V₁'' t)) :
    (dlCont t V₁ V₁' V₂ A (wlOn d cd) rec x).Live ∧
      (dlCont t V₁ V₁' V₂ A (wlOn d cd) rec x).AllLeaves (ValidOut V₁ t) := by
  by_cases ha : ∀ u, (cls1 (wlOn d cd) x u).card ≤ 2 * V₂.card / 3
  · -- (a) no dominant colour
    have e : dlCont t V₁ V₁' V₂ A (wlOn d cd) rec x = withPiece (V₁ \ V₁') (shrink V₂ rec V₁'
        (pickSide V₁' V₂ ((selThird univ (skel1 (wlOn d cd) x)).map
          (Function.Embedding.subtype _)) A) A) := by
      simp only [dlCont, ite_eq_left ha]
    rw [e]
    have hne : (univ : Finset V₂).Nonempty := by
      obtain ⟨s, hs⟩ := card_pos.1 (show 0 < V₂.card by omega)
      exact ⟨⟨s, hs⟩, mem_univ _⟩
    have hcu : (univ : Finset V₂).card = V₂.card := by rw [card_univ, Fintype.card_coe]
    obtain ⟨-, h1, h2⟩ := selThird_spec (univ : Finset V₂) (skel1 (wlOn d cd) x) hne
      (fun u _ => by have := ha u; unfold cls1 at this; rw [hcu]; omega)
    refine third_valid h hV₁' htV₁' htf hv ?_ ?_ ?_ hrec
    · intro s hs
      obtain ⟨w, -, rfl⟩ := mem_map.1 hs
      exact w.2
    · rw [card_map]
      omega
    · rw [card_map]
      omega
  · -- (b) a dominant class with a non-clique 2-skeleton
    rw [dlCont_eq_contB _ _ _ _ _ _ _ _ ha]
    obtain ⟨hlen, u₀, hu₀, hnc⟩ := hgood.resolve_left ha
    refine contB_valid h hV₁' htV₁' htf hv (isCoherent2_skel2 (wlOn_isCoherent cd) hlen) hu₀
      ?_ hnc (isCoh2On_cohOn _ _)
      (fun a ha b hb a' ha' b' hb' e => cohOn_refines ha hb ha' hb' e) hrec
    intro w hw w'
    simp only [cls1, mem_filter, mem_univ, true_and] at hw ⊢
    rw [skel2_self, skel2_self, hw]

end GraphIso.SplitJohnson
