module

public import GraphIso.SoJTree.LeafData
public import GraphIso.SoJProg.Dary
public import GraphIso.SoJProg.DLTest

/-!
# Frames of Split-or-Johnson on data

Stage 14d, item 3 (`PLAN-14.md` §8). The tree programs of stage 14d enumerate the leaves of
milestone 11's `bsoj`, `sojAt` and `soj` with a worklist of **frames**. A frame
(`FrameD`) is a pending call `bsoj t V₁ V₂ A` on the points `Fin m` (points `V₁`, cells `cs`,
relation array `a`, as in stage 14c) together with the wrapper operations (pieces and an
extension) to apply to its leaves; its tree is `FrameD.tree`.

* `stepD m t fr`: one level of `bsoj` on data, composed of the stage 14c steps: `bstep` with
  its steps 0–3, `dlCont` with its pieces, the `cohSoj` level (`cohSojD` on all points and
  cells, `cohI`) and `cohCont` (`contI`), with the guards of `shrink` and `bsoj`. It returns
  the produced leaves, already wrapped, and the child frames.
* `stepWork m t fr`: the choices handled at this level (base-case enumerations, Design Lemma
  options and their `cohSoj` options).
* `stepD_leafMs`, `stepD_children`, `stepD_size`: the frame's leaf multiset is the produced
  leaves plus the children's; the children are valid with fewer cells; the work, the produced
  leaves and the children's sizes fit in the frame's size.
* `sojAtD`: the frame (or leaf) of `sojAt` after individualizing a point (`sojAtD_leaf`,
  `sojAtD_frame`).

Two model facts are proved on the way:

* **`bsoj` reads the relation only on its cells** (`bsoj_congr`). The trees for two relations
  that agree on the cells are equal on their reachable branches (`TEq`): the base case's
  node maps unreachable enumerations to leaves that may differ. The child frames carry the
  relation restricted to their cells, so `stepD`'s statements are about leaf multisets and
  sizes, which `TEq` preserves, and `sojAtD_frame` is stated with `TEq`.
* **`cohSoj` is natural along injective maps** (`cohSoj_agree`): on the image of
  `e : R' ↪ R` its tree agrees with the tree of the pulled-back colouring. Stage 14c's
  `cohSojD` runs on all points and cells (`u < m` a point, `m + j` the `j`-th cell), numbered
  into `Fin m ⊕ Finset (Fin m)` by `eQ`; `cQd` reads the classical refinement of `dlCont`
  there (`0` off `V₁' ⊔ V₂`, like `cohOn`), so `cohCont` reads the whole leaf colourings.
-/

@[expose] public section

namespace GraphIso.SoJTree

open Finset GraphIso GraphIso.SplitJohnson GraphIso.SoJProg GraphIso.Coherent

namespace FrameAux

section Congr0



variable {α : Type*} [DecidableEq α] {V₂ : Finset (Finset α)} {A A' : α → Finset α → Bool}

section Congr

variable (hA : ∀ x, ∀ s ∈ V₂, A x s = A' x s)
include hA

omit [DecidableEq α] in
theorem fr_deg_congr : deg V₂ A = deg V₂ A' := by
  funext x
  unfold deg
  rw [filter_congr fun s hs => by rw [hA x s hs]]

omit [DecidableEq α] in
theorem fr_twinCls_congr (V₁ : Finset α) : twinCls V₁ V₂ A = twinCls V₁ V₂ A' := by
  funext x
  unfold twinCls
  refine filter_congr fun x' _ => ?_
  exact forall₂_congr fun s hs => by rw [hA x s hs, hA x' s hs]

omit [DecidableEq α] in
theorem fr_tw_congr (V₁ : Finset α) : tw V₁ V₂ A = tw V₁ V₂ A' := by
  funext x
  unfold tw
  rw [fr_twinCls_congr hA]

omit [DecidableEq α] in
theorem fr_tfDeg_congr (V₁ : Finset α) : tfDeg V₁ V₂ A = tfDeg V₁ V₂ A' := by
  funext d
  unfold tfDeg
  rw [fr_tw_congr hA, fr_deg_congr hA]

omit [DecidableEq α] in
theorem fr_bigDegs_congr (t : ℕ) (V₁ : Finset α) : bigDegs t V₁ V₂ A = bigDegs t V₁ V₂ A' := by
  unfold bigDegs
  rw [fr_deg_congr hA, fr_tfDeg_congr hA]

omit [DecidableEq α] in
theorem fr_twinPart_congr (V₁ : Finset α) : twinPart V₁ V₂ A = twinPart V₁ V₂ A' := by
  unfold twinPart
  rw [fr_tw_congr hA, fr_deg_congr hA, fr_tfDeg_congr hA, fr_twinCls_congr hA]

omit [DecidableEq α] in
theorem fr_nbr_congr : nbr V₂ A = nbr V₂ A' := by
  funext x
  unfold nbr
  rw [filter_congr fun s hs => by rw [hA x s hs]]

theorem fr_fOf_congr (d₁ : ℕ) : fOf V₂ A d₁ = fOf V₂ A' d₁ := by
  funext x
  unfold fOf
  rw [fr_nbr_congr hA]

omit hA in
theorem fr_pickSide_congr (V₁ : Finset α) {S : Finset (Finset α)}
    (hS : ∀ x, ∀ s ∈ S, A x s = A' x s) :
    pickSide V₁ V₂ S A = pickSide V₁ V₂ S A' := by
  unfold pickSide
  rw [fr_twinCls_congr hS]

theorem fr_cohOn_congr (V₁' : Finset α) (Y : Finset α → Finset α → ℕ) :
    cohOn (V₁'.disjSum V₂) (code A Y) = cohOn (V₁'.disjSum V₂) (code A' Y) := by
  funext a b
  unfold cohOn
  split_ifs with h
  · congr 1
    funext p
    have h0 := (p 0).2
    have h1 := (p 1).2
    generalize (p 0).val = u at h0
    generalize (p 1).val = v at h1
    rcases u with u | u <;> rcases v with v | v
    · rfl
    · simp only [code, hA u v (Finset.inr_mem_disjSum.1 h1)]
    · simp only [code, hA v u (Finset.inr_mem_disjSum.1 h0)]
    · rfl
  · rfl

end Congr

omit [DecidableEq α] in
theorem fr_nbrCode_congr {e : List (Finset α)} (he : ∀ s ∈ e, s ∈ V₂)
    (hA : ∀ x, ∀ s ∈ V₂, A x s = A' x s) : nbrCode A e = nbrCode A' e := by
  funext x
  unfold nbrCode
  congr 1
  exact List.map_congr_left fun s hs => by rw [hA x s (he s hs)]

theorem fr_mem_of_mem_choiceCells {e : Choice α} (he : e ∈ enums V₂) :
    ∀ s ∈ choiceCells e, s ∈ V₂ := by
  intro s hs
  obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 he
  rw [Multiset.mem_toFinset, Multiset.mem_lists_iff] at hl
  simp only [choiceCells, List.mem_filterMap, List.mem_map] at hs
  obtain ⟨q, ⟨s', hs', rfl⟩, hq⟩ := hs
  simp only [Sum.getRight?_inr, Option.some.injEq] at hq
  subst hq
  rw [← Finset.mem_val, hl]
  exact Multiset.mem_coe.2 hs'

/-! ### Trees equal on their reachable branches -/

/-- Two trees with the same node sets and the same leaves, compared only on the choices of
their node sets. -/
def TEq {C O : Type*} : CTree C O → CTree C O → Prop
  | .leaf o, .leaf o' => o = o'
  | .node S k, .node S' k' => S = S' ∧ ∀ c ∈ S, TEq (k c) (k' c)
  | _, _ => False

theorem TEq.refl {C O : Type*} : ∀ t : CTree C O, TEq t t
  | .leaf _ => rfl
  | .node _ k => ⟨rfl, fun c _ => TEq.refl (k c)⟩

theorem TEq.of_eq {C O : Type*} {t t' : CTree C O} (h : t = t') : TEq t t' := h ▸ TEq.refl t

theorem TEq.leafMs_eq {C O : Type*} : ∀ {t t' : CTree C O}, TEq t t' → t.leafMs = t'.leafMs
  | .leaf o, .leaf o', h => by
    show ({o} : Multiset O) = {o'}
    rw [show o = o' from h]
  | .node S k, .node S' k', h => by
    obtain ⟨rfl, h⟩ := h
    exact sum_congr rfl fun c hc => TEq.leafMs_eq (h c hc)
  | .leaf _, .node _ _, h => h.elim
  | .node _ _, .leaf _, h => h.elim

theorem TEq.size_eq {C O : Type*} : ∀ {t t' : CTree C O}, TEq t t' → t.size = t'.size
  | .leaf _, .leaf _, _ => rfl
  | .node S k, .node S' k', h => by
    obtain ⟨rfl, h⟩ := h
    exact congrArg (1 + ·) (sum_congr rfl fun c hc => by rw [TEq.size_eq (h c hc)])
  | .leaf _, .node _ _, h => h.elim
  | .node _ _, .leaf _, h => h.elim

theorem TEq.bind {C O O' : Type*} {f g : O → CTree C O'} (hfg : ∀ o, TEq (f o) (g o)) :
    ∀ {t t' : CTree C O}, TEq t t' → TEq (t.bind f) (t'.bind g)
  | .leaf o, .leaf o', h => by
    show TEq (f o) (g o')
    rw [show o = o' from h]
    exact hfg o'
  | .node S k, .node S' k', h => by
    obtain ⟨rfl, h⟩ := h
    exact ⟨rfl, fun c hc => TEq.bind hfg (h c hc)⟩
  | .leaf _, .node _ _, h => h.elim
  | .node _ _, .leaf _, h => h.elim

theorem TEq.ite {C O : Type*} {p : Prop} [Decidable p] {a a' b b' : CTree C O}
    (h₁ : p → TEq a a') (h₂ : ¬ p → TEq b b') :
    TEq (if p then a else b) (if p then a' else b') := by
  by_cases hp : p
  · rw [ite_eq_left hp, ite_eq_left hp]
    exact h₁ hp
  · rw [ite_eq_right hp, ite_eq_right hp]
    exact h₂ hp

theorem TEq.withPiece {D : Finset α} {t t' : STree α} (h : TEq t t') :
    TEq (withPiece D t) (withPiece D t') :=
  TEq.bind (fun _ => TEq.refl _) h

/-- The guarded recursion, equal on the reachable branches for the subsets of `V₂`. -/
def RecCongr (V₂ : Finset (Finset α)) (A A' : α → Finset α → Bool)
    (rec : Finset α → Finset (Finset α) → (α → Finset α → Bool) → STree α) : Prop :=
  ∀ a b, b ⊆ V₂ → TEq (rec a b A) (rec a b A')

omit [DecidableEq α] in
theorem fr_shrink_congr {rec : Finset α → Finset (Finset α) → (α → Finset α → Bool) → STree α}
    (hrec : RecCongr V₂ A A' rec) : RecCongr V₂ A A' (shrink V₂ rec) := by
  intro a b hb
  unfold shrink
  split_ifs
  · exact hrec a b hb
  · exact TEq.refl _

theorem fr_pickSide_sub (V₁ : Finset α) (S : Finset (Finset α)) :
    pickSide V₁ V₂ S A ⊆ V₂ ∨ pickSide V₁ V₂ S A = S := by
  unfold pickSide
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl sdiff_subset

theorem fr_pickSide_subset (V₁ : Finset α) {S : Finset (Finset α)} (hS : S ⊆ V₂) :
    pickSide V₁ V₂ S A ⊆ V₂ := by
  rcases fr_pickSide_sub (A := A) V₁ S with h | h
  · exact h
  · rw [h]
    exact hS

theorem fr_pick_congr {rec : Finset α → Finset (Finset α) → (α → Finset α → Bool) → STree α}
    (hrec : RecCongr V₂ A A' rec) (D V₁ : Finset α) {S : Finset (Finset α)} (hS : S ⊆ V₂)
    (hA : ∀ x, ∀ s ∈ V₂, A x s = A' x s) :
    TEq (withPiece D (rec V₁ (pickSide V₁ V₂ S A) A))
      (withPiece D (rec V₁ (pickSide V₁ V₂ S A') A')) := by
  rw [fr_pickSide_congr V₁ (fun x s hs => hA x s (hS hs))]
  exact (hrec _ _ (fr_pickSide_subset V₁ hS)).withPiece

theorem fr_bigTwins_subset {d : ℕ} (c : (Fin d → V₂) → ℕ) : bigTwins V₂ c ⊆ V₂ := by
  intro s hs
  unfold bigTwins at hs
  obtain ⟨u, -, rfl⟩ := Finset.mem_map.1 hs
  exact u.2

theorem fr_dlCont_congr (t : ℕ) (V₁ V₁' : Finset α) {d : ℕ} (W : (Fin d → V₂) → ℕ)
    (hA : ∀ x, ∀ s ∈ V₂, A x s = A' x s)
    {rec : Finset α → Finset (Finset α) → (α → Finset α → Bool) → STree α}
    (hrec : RecCongr V₂ A A' rec) (x : List V₂) :
    TEq (dlCont t V₁ V₁' V₂ A W rec x) (dlCont t V₁ V₁' V₂ A' W rec x) := by
  have hrc := fr_shrink_congr hrec
  unfold dlCont
  dsimp only
  rw [fr_cohOn_congr hA]
  refine TEq.ite (fun _ => ?_) (fun _ => ?_)
  · refine fr_pick_congr hrc _ _ ?_ hA
    intro s hs
    obtain ⟨u, -, rfl⟩ := Finset.mem_map.1 hs
    exact u.2
  refine TEq.ite (fun _ => ?_) (fun _ => ?_)
  · refine fr_pick_congr hrc _ _ ?_ hA
    unfold selThird
    dsimp only
    split <;> exact filter_subset _ _
  refine TEq.ite (fun _ => TEq.refl _) (fun _ => ?_)
  exact TEq.ite (fun _ => (hrc _ _ sdiff_subset).withPiece) (fun _ => TEq.refl _)

theorem fr_bstep_congr (t : ℕ) (V₁ : Finset α) (hA : ∀ x, ∀ s ∈ V₂, A x s = A' x s)
    {rec : Finset α → Finset (Finset α) → (α → Finset α → Bool) → STree α}
    (hrec : RecCongr V₂ A A' rec) : TEq (bstep t V₁ V₂ A rec) (bstep t V₁ V₂ A' rec) := by
  unfold bstep
  rw [fr_bigDegs_congr hA]
  by_cases h : (bigDegs t V₁ V₂ A').Nonempty
  · rw [dite_eq_left h, dite_eq_left h]
    generalize (bigDegs t V₁ V₂ A').min' h = d₁
    dsimp only
    rw [fr_tfDeg_congr hA, fr_fOf_congr hA]
    refine TEq.ite (fun _ => TEq.refl _) (fun _ => ?_)
    refine TEq.ite (fun _ => ⟨rfl, fun e he => ?_⟩) (fun _ => ?_)
    · simp only [TEq]
      rw [fr_nbrCode_congr (fr_mem_of_mem_choiceCells he) hA]
    refine TEq.ite (fun _ => fr_pick_congr hrec _ _ (fr_bigTwins_subset _) hA) (fun _ => ?_)
    exact ⟨rfl, fun ch _ => fr_dlCont_congr t V₁ _ _ hA hrec _⟩
  · rw [dite_eq_right h, dite_eq_right h, fr_twinPart_congr hA]
    exact TEq.refl _

/-- **Bipartite Split-or-Johnson reads the relation only on the cells of `V₂`.** -/
theorem bsoj_congr (t : ℕ) (V₁ : Finset α) (V₂ : Finset (Finset α)) {A A' : α → Finset α → Bool}
    (hA : ∀ x, ∀ s ∈ V₂, A x s = A' x s) : TEq (bsoj t V₁ V₂ A) (bsoj t V₁ V₂ A') := by
  induction hn : V₂.card using Nat.strong_induction_on generalizing V₁ V₂ A A' with
  | _ n ih =>
    rw [bsoj.eq_1 t V₁ V₂ A, bsoj.eq_1 t V₁ V₂ A']
    refine fr_bstep_congr t V₁ hA fun a b hb => ?_
    by_cases hlt : b.card < V₂.card
    · rw [dite_eq_left hlt, dite_eq_left hlt]
      exact ih b.card (hn ▸ hlt) a b (fun x s hs => hA x s (hb hs)) rfl
    · rw [dite_eq_right hlt, dite_eq_right hlt]
      exact TEq.refl _





end Congr0

/-! ### Coherent Split-or-Johnson along an injective map -/

section Agree

variable {R R' : Type*} [DecidableEq R] [DecidableEq R'] (e : R' ↪ R)

/-- Outputs that agree along `e` at the points of `R'`. -/
def OutAgree : Option (CohOut R) → Option (CohOut R') → Prop
  | none, none => True
  | some (.part p), some (.part p') =>
    ∀ x', p.col (e x') = p'.col x' ∧ p.blk (e x') = (p'.blk x').map e
  | some (.bip W₁ W₂ A), some (.bip W₁' W₂' A') =>
    W₁ = W₁'.map e ∧ W₂ = W₂'.image (fun B => B.map e) ∧ ∀ x' B', A (e x') (B'.map e) = A' x' B'
  | _, _ => False

/-- Trees that agree along `e`: node sets mapped by `e`, agreeing leaves. -/
def TreeAgree : CTree R (Option (CohOut R)) → CTree R' (Option (CohOut R')) → Prop
  | .leaf o, .leaf o' => OutAgree e o o'
  | .node S k, .node S' k' => S = S'.map e ∧ ∀ y ∈ S', TreeAgree (k (e y)) (k' y)
  | _, _ => False

variable (c : R → R → ℕ)

/-- The colouring pulled back along `e`. -/
def pull : R' → R' → ℕ := fun u v => c (e u) (e v)

theorem compStep_map (S T : Finset R') (r : ℕ) :
    compStep (S.map e) c r (T.map e) = (compStep S (pull e c) r T).map e := by
  unfold compStep
  rw [map_union, filter_map]
  congr 1
  ext y
  simp only [mem_map, mem_filter]
  constructor
  · rintro ⟨y', ⟨hy', x, ⟨x', hx', rfl⟩, h⟩, rfl⟩
    exact ⟨y', ⟨hy', x', hx', h⟩, rfl⟩
  · rintro ⟨y', ⟨hy', x', hx', h⟩, rfl⟩
    exact ⟨y', ⟨hy', e x', ⟨x', hx', rfl⟩, h⟩, rfl⟩

theorem iterate_compStep_map (S T : Finset R') (r n : ℕ) :
    (compStep (S.map e) c r)^[n] (T.map e) = ((compStep S (pull e c) r)^[n] T).map e := by
  induction n generalizing T with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, compStep_map, ih]

theorem comp_map (S : Finset R') (r : ℕ) (x : R') :
    comp (S.map e) c r (e x) = (comp S (pull e c) r x).map e := by
  unfold comp
  rw [card_map]
  have h0 : (if e x ∈ S.map e then ({e x} : Finset R) else ∅) =
      (if x ∈ S then ({x} : Finset R') else ∅).map e := by
    by_cases hx : x ∈ S
    · rw [ite_eq_left (mem_map_of_mem e hx), ite_eq_left hx, map_singleton]
    · rw [ite_eq_right (fun h => hx ((mem_map' e).1 h)), ite_eq_right hx, map_empty]
  rw [h0, iterate_compStep_map]

theorem offCols_map (S : Finset R') : offCols (S.map e) c = offCols S (pull e c) := by
  unfold offCols
  ext k
  simp only [mem_image, mem_filter, mem_product, mem_map, Prod.exists, pull]
  constructor
  · rintro ⟨a, b, ⟨⟨⟨a', ha', rfl⟩, ⟨b', hb', rfl⟩⟩, hab⟩, rfl⟩
    exact ⟨a', b', ⟨⟨ha', hb'⟩, fun h => hab (by rw [h])⟩, rfl⟩
  · rintro ⟨a', b', ⟨⟨ha', hb'⟩, hab⟩, rfl⟩
    exact ⟨e a', e b', ⟨⟨⟨a', ha', rfl⟩, ⟨b', hb', rfl⟩⟩, fun h => hab (e.injective h)⟩, rfl⟩

theorem disconn_map (S : Finset R') : disconn (S.map e) c = disconn S (pull e c) := by
  unfold disconn
  rw [offCols_map]
  refine filter_congr fun r _ => ?_
  constructor
  · rintro ⟨x, hx, h⟩
    obtain ⟨x', hx', rfl⟩ := mem_map.1 hx
    refine ⟨x', hx', fun h' => h ?_⟩
    rw [comp_map, h']
  · rintro ⟨x', hx', h⟩
    refine ⟨e x', mem_map_of_mem e hx', fun h' => h ?_⟩
    rw [comp_map] at h'
    exact map_injective e h'

omit [DecidableEq R] [DecidableEq R'] in
theorem cols_map (C₁ C₂ : Finset R') :
    ((C₁.map e) ×ˢ (C₂.map e)).image (fun p => c p.1 p.2) =
      (C₁ ×ˢ C₂).image fun p => pull e c p.1 p.2 := by
  ext k
  simp only [mem_image, mem_product, mem_map, Prod.exists, pull]
  constructor
  · rintro ⟨a, b, ⟨⟨a', ha', rfl⟩, ⟨b', hb', rfl⟩⟩, rfl⟩
    exact ⟨a', b', ⟨ha', hb'⟩, rfl⟩
  · rintro ⟨a', b', ⟨ha', hb'⟩, rfl⟩
    exact ⟨e a', e b', ⟨⟨a', ha', rfl⟩, ⟨b', hb', rfl⟩⟩, rfl⟩

omit [DecidableEq R] [DecidableEq R'] in
theorem filter_map_e (S : Finset R') (P : R → Prop) [DecidablePred P] :
    (S.map e).filter P = (S.filter fun x => P (e x)).map e := by
  rw [filter_map]
  rfl

omit [DecidableEq R] [DecidableEq R'] in
theorem card_filter_map_e (S : Finset R') (P : R → Prop) [DecidablePred P] :
    ((S.map e).filter P).card = (S.filter fun x => P (e x)).card := by
  rw [filter_map_e, card_map]

omit [DecidableEq R] [DecidableEq R'] in
theorem twinCls_map (C₁ B : Finset R') (g : ℕ) (x : R') :
    twinCls (C₁.map e) (B.map e) (fun x y => decide (c x y = g)) (e x) =
      (twinCls C₁ B (fun x y => decide (pull e c x y = g)) x).map e := by
  unfold twinCls
  rw [filter_map_e]
  congr 1
  refine filter_congr fun x' _ => ?_
  simp only [mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, pull]
  exact Iff.rfl

omit [DecidableEq R] [DecidableEq R'] in
theorem bipEdge_map (g : ℕ) (x : R') (B : Finset R') :
    bipEdge c g (e x) (B.map e) = bipEdge (pull e c) g x B := by
  unfold bipEdge
  simp only [mem_map, exists_exists_and_eq_and, pull]
  rfl

omit [DecidableEq R] [DecidableEq R'] in
theorem exists_mem_map_e (C : Finset R') (P : R → Prop) :
    (∃ w ∈ C.map e, P w) ↔ ∃ w ∈ C, P (e w) := by
  simp only [mem_map, exists_exists_and_eq_and]

omit [DecidableEq R] [DecidableEq R'] in
theorem forall_mem_map_e (C : Finset R') (P : R → Prop) :
    (∀ w ∈ C.map e, P w) ↔ ∀ w ∈ C, P (e w) := by
  simp only [mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]

omit [DecidableEq R'] in
theorem colPart_agree (C₁ : Finset R') (f : R → ℕ) :
    OutAgree e (some (.part (colPart (C₁.map e) f)))
      (some (.part (colPart C₁ fun x => f (e x)))) := by
  intro x'
  refine ⟨rfl, ?_⟩
  show (C₁.map e).filter (fun y => f y = f (e x')) = (C₁.filter fun y => f (e y) = f (e x')).map e
  rw [filter_map_e]

theorem image_comp_map (C : Finset R') (r : ℕ) :
    (C.map e).image (comp (C.map e) c r) = (C.image (comp C (pull e c) r)).image (·.map e) := by
  rw [image_image]
  ext B
  simp only [mem_image, mem_map, Function.comp]
  constructor
  · rintro ⟨y, ⟨y', hy', rfl⟩, rfl⟩
    exact ⟨y', hy', (comp_map e c C r y').symm⟩
  · rintro ⟨y', hy', rfl⟩
    exact ⟨e y', ⟨y', hy', rfl⟩, comp_map e c C r y'⟩

omit [DecidableEq R'] in
theorem bip_agree (W₁ : Finset R') (W₂ : Finset (Finset R')) (g : ℕ) :
    OutAgree e (some (.bip (W₁.map e) (W₂.image (·.map e)) (bipEdge c g)))
      (some (.bip W₁ W₂ (bipEdge (pull e c) g))) :=
  ⟨rfl, rfl, fun x' B' => bipEdge_map e c g x' B'⟩

theorem cohSoj_agree (C₁ C₂ : Finset R') :
    TreeAgree e (cohSoj (C₁.map e) (C₂.map e) c) (cohSoj C₁ C₂ (pull e c)) := by
  unfold cohSoj
  rw [disconn_map, disconn_map]
  by_cases h₁ : (disconn C₁ (pull e c)).Nonempty
  · rw [dite_eq_left h₁, dite_eq_left h₁]
    intro x'
    exact ⟨rfl, comp_map e c C₁ _ x'⟩
  rw [dite_eq_right h₁, dite_eq_right h₁]
  dsimp only
  rw [cols_map]
  generalize (C₁ ×ˢ C₂).image (fun p => pull e c p.1 p.2) = cols
  by_cases h₂ : (disconn C₂ (pull e c)).Nonempty
  · rw [dite_eq_left h₂, dite_eq_left h₂]
    generalize (disconn C₂ (pull e c)).min' h₂ = red
    have hbig : (cols.filter fun k => ∃ w ∈ C₂.map e,
        (C₁.map e).card < 2 * ((C₁.map e).filter fun x => c x w = k).card) =
        cols.filter fun k => ∃ w ∈ C₂,
          C₁.card < 2 * (C₁.filter fun x => pull e c x w = k).card := by
      refine filter_congr fun k _ => ?_
      rw [exists_mem_map_e]
      simp only [card_map, card_filter_map_e, pull]
      exact Iff.rfl
    rw [hbig]
    by_cases hv : (cols.filter fun k => ∃ w ∈ C₂,
        C₁.card < 2 * (C₁.filter fun x => pull e c x w = k).card).Nonempty
    · rw [dite_eq_left hv, dite_eq_left hv]
      generalize (cols.filter fun k => ∃ w ∈ C₂,
        C₁.card < 2 * (C₁.filter fun x => pull e c x w = k).card).min' hv = violet
      have hgood : ((C₂.map e).image (comp (C₂.map e) c red)).filter (fun B =>
          ∀ x ∈ C₁.map e, 2 * (twinCls (C₁.map e) B (fun x y => decide (c x y = violet)) x).card
            ≤ (C₁.map e).card) =
          ((C₂.image (comp C₂ (pull e c) red)).filter fun B => ∀ x ∈ C₁,
            2 * (twinCls C₁ B (fun x y => decide (pull e c x y = violet)) x).card ≤ C₁.card).image
            (·.map e) := by
        rw [image_comp_map, filter_image]
        congr 1
        refine filter_congr fun B _ => ?_
        rw [forall_mem_map_e]
        simp only [twinCls_map, card_map]
      rw [hgood]
      generalize (C₂.image (comp C₂ (pull e c) red)).filter (fun B => ∀ x ∈ C₁,
        2 * (twinCls C₁ B (fun x y => decide (pull e c x y = violet)) x).card ≤ C₁.card) = good
      by_cases hg : good.Nonempty
      · rw [ite_eq_left (image_nonempty.2 hg), ite_eq_left hg]
        refine ⟨?_, fun y' _ => ?_⟩
        · rw [filter_map_e]
          congr 1
          refine filter_congr fun y _ => ?_
          rw [comp_map]
          exact (map_injective e).mem_finset_image
        · show OutAgree e _ _
          rw [comp_map, show ((comp C₂ (pull e c) red y').map e).image singleton =
            ((comp C₂ (pull e c) red y').image singleton).image (fun B : Finset R' => B.map e) by
              rw [image_image]
              ext B
              simp]
          exact bip_agree e c _ _ _
      · rw [ite_eq_right (fun h => hg (image_nonempty.1 h)), ite_eq_right hg]
        by_cases hg' : (cols.erase violet).Nonempty
        · rw [dite_eq_left hg', dite_eq_left hg', image_comp_map]
          exact bip_agree e c _ _ _
        · rw [dite_eq_right hg', dite_eq_right hg']
          trivial
    · rw [dite_eq_right hv, dite_eq_right hv]
      refine ⟨rfl, fun w' _ => colPart_agree e C₁ (fun x => c x (e w'))⟩
  · rw [dite_eq_right h₂, dite_eq_right h₂]
    refine ⟨rfl, fun y' _ => ?_⟩
    dsimp only
    have hbig : (cols.filter fun k => (C₁.map e).card <
        2 * ((C₁.map e).filter fun x => c x (e y') = k).card) =
        cols.filter fun k => C₁.card < 2 * (C₁.filter fun x => pull e c x y' = k).card := by
      refine filter_congr fun k _ => ?_
      simp only [card_map, card_filter_map_e, pull]
      exact Iff.rfl
    rw [hbig]
    by_cases hv : (cols.filter fun k => C₁.card <
        2 * (C₁.filter fun x => pull e c x y' = k).card).Nonempty
    · rw [dite_eq_left hv, dite_eq_left hv]
      generalize (cols.filter fun k => C₁.card <
        2 * (C₁.filter fun x => pull e c x y' = k).card).min' hv = violet
      have hbl : (offCols (C₂.map e) c).filter (fun b =>
          0 < ((C₂.map e).filter fun z => c (e y') z = b).card ∧
            2 * ((C₂.map e).filter fun z => c (e y') z = b).card < (C₂.map e).card) =
          (offCols C₂ (pull e c)).filter fun b =>
            0 < (C₂.filter fun z => pull e c y' z = b).card ∧
              2 * (C₂.filter fun z => pull e c y' z = b).card < C₂.card := by
        rw [offCols_map]
        refine filter_congr fun b _ => ?_
        simp only [card_map, card_filter_map_e, pull]
        exact Iff.rfl
      rw [hbl]
      by_cases hb : ((offCols C₂ (pull e c)).filter fun b =>
          0 < (C₂.filter fun z => pull e c y' z = b).card ∧
            2 * (C₂.filter fun z => pull e c y' z = b).card < C₂.card).Nonempty
      · rw [dite_eq_left hb, dite_eq_left hb]
        generalize ((offCols C₂ (pull e c)).filter fun b =>
          0 < (C₂.filter fun z => pull e c y' z = b).card ∧
            2 * (C₂.filter fun z => pull e c y' z = b).card < C₂.card).min' hb = blue
        show OutAgree e _ _
        rw [filter_map_e, filter_map_e,
          show ((C₂.filter fun z => c (e y') (e z) = blue).map e).image singleton =
            ((C₂.filter fun z => c (e y') (e z) = blue).image singleton).image
              (fun B : Finset R' => B.map e) by
            rw [image_image]
            ext B
            simp]
        exact bip_agree e c _ _ _
      · rw [dite_eq_right hb, dite_eq_right hb]
        trivial
    · rw [dite_eq_right hv, dite_eq_right hv]
      exact colPart_agree e C₁ (fun x => c x (e y'))

end Agree


end FrameAux

/-! ### Frames -/

open FrameAux

/-- A wrapper operation applied to every leaf of a frame: `(false, D, _)` adds the piece `D`
(`addPieceOut`); `(true, V, row)` extends by the colours `row` outside `V` (`extendOut`). -/
abbrev WrapOp := Bool × (List ℕ × Array ℕ)

/-- Wrapper operations in programs. -/
abbrev wrapTy : Cost.Ty := .prod .bool (.prod (.list .nat) (.array .nat))

/-- **A frame**: a pending call `bsoj t V₁ V₂ A` on the points `Fin m`, with the points `V₁`,
the cells `cs` (`V₂ = famOf m cs`), the relation array `a` (`A = relOf m cs a`) and the wrapper
operations to apply to its leaves, innermost first. -/
abbrev FrameD := List ℕ × (List (List ℕ) × (Array Bool × List WrapOp))

/-- Frames in programs. -/
abbrev frameTy : Cost.Ty :=
  .prod (.list .nat) (.prod (.list (.list .nat)) (.prod (.array .bool) (.list wrapTy)))

namespace FrameD

/-- The points. -/
def V₁ (fr : FrameD) : List ℕ := fr.1

/-- The cells. -/
def cs (fr : FrameD) : List (List ℕ) := fr.2.1

/-- The relation array. -/
def a (fr : FrameD) : Array Bool := fr.2.2.1

/-- The wrapper operations. -/
def wr (fr : FrameD) : List WrapOp := fr.2.2.2

end FrameD

/-- A wrapper operation on a leaf. -/
def opOut (m : ℕ) (op : WrapOp) (o : Option (Out (Fin m))) : Option (Out (Fin m)) :=
  if op.1 then extendOut (setOf m op.2.1) (fun y => get op.2.2 y.val) o
  else addPieceOut (setOf m op.2.1) o

/-- The wrapper operations on a leaf, innermost first. -/
def wrapOut (m : ℕ) (ops : List WrapOp) (o : Option (Out (Fin m))) : Option (Out (Fin m)) :=
  ops.foldl (fun o op => opOut m op o) o

/-- A wrapper operation on leaf data. -/
def opD (m : ℕ) (op : WrapOp) (o : OutD) : OutD :=
  if op.1 then extendD m op.2.1 (get op.2.2) o else addPieceD m op.2.1 o

/-- The wrapper operations on leaf data, innermost first. -/
def wrapD (m : ℕ) (ops : List WrapOp) (o : OutD) : OutD := ops.foldl (fun o op => opD m op o) o

/-- The wrapper operations on every leaf of a tree. -/
def wrapT (m : ℕ) (ops : List WrapOp) (T : STree (Fin m)) : STree (Fin m) :=
  T.bind fun o => .leaf (wrapOut m ops o)

/-- **The tree of a frame**: its wrapper applied to `bsoj t V₁ V₂ A`. -/
def FrameD.tree (m t : ℕ) (fr : FrameD) : STree (Fin m) :=
  wrapT m fr.wr (bsoj t (setOf m fr.V₁) (famOf m fr.cs) (relOf m fr.cs fr.a))

/-- **The representation invariant of a frame**: duplicate-free points below `m`, and cells
distinct as sets. -/
structure FrameD.Valid (m : ℕ) (fr : FrameD) : Prop where
  nodup : fr.V₁.Nodup
  lt : ∀ x ∈ fr.V₁, x < m
  cells : (fr.cs.map (setOf m)).Nodup

/-- A piece. -/
def pieceOp (D : List ℕ) : WrapOp := (false, D, #[])

/-! ### Items of a level -/

/-- An item produced by one step: a leaf, or a child frame. -/
abbrev Item := OutD ⊕ FrameD

/-- The leaves an item stands for. -/
def itemMs (m t : ℕ) : Item → Multiset (Option (Out (Fin m)))
  | .inl o => {decodeOut m o}
  | .inr fr => (fr.tree m t).leafMs

/-- The size an item stands for. -/
def itemSize (m t : ℕ) : Item → ℕ
  | .inl _ => 1
  | .inr fr => (fr.tree m t).size

/-- Wrap an item. -/
def wrapItem (m : ℕ) (ops : List WrapOp) : Item → Item
  | .inl o => .inl (wrapD m ops o)
  | .inr fr => .inr (fr.V₁, fr.cs, fr.a, fr.wr ++ ops)

/-- **A level description**: the tree `T` has the leaves of `items`, its size is at least the
work `w` plus the sizes of the items, and the child frames are valid with fewer than `k`
cells. -/
structure Desc (m t k : ℕ) (T : STree (Fin m)) (items : List Item) (w : ℕ) : Prop where
  ms : T.leafMs = (items.map (itemMs m t)).sum
  size : w + (items.map (itemSize m t)).sum ≤ T.size
  ok : ∀ ch, Sum.inr ch ∈ items → ch.Valid m ∧ ch.cs.length < k

/-- A guarded recursive call (`bsoj`'s guard). -/
def recI (k : ℕ) (V : List ℕ) (cs : List (List ℕ)) (a : Array Bool) (ops : List WrapOp) : Item :=
  if cs.length < k then .inr (V, cs, a, ops) else .inl noneD

/-- A recursive call guarded by `shrink` and `bsoj`. -/
def shrinkI (k : ℕ) (V : List ℕ) (cs : List (List ℕ)) (a : Array Bool) (ops : List WrapOp) :
    Item :=
  if 3 * cs.length ≤ 2 * k ∧ cs.length < k then .inr (V, cs, a, ops) else .inl noneD

/-! ### Data of one level -/

/-- The points of `V` not in `V'`. -/
def diffD (V V' : List ℕ) : List ℕ := V.filter fun x => x ∉ V'

/-- The cells with the listed indices. -/
def subCells (cs : List (List ℕ)) (js : List ℕ) : List (List ℕ) := js.map fun j => cs.getD j []

/-- The relation restricted to the cells with the listed indices, for the points below `m`. -/
def restrictRel (m k : ℕ) (a : Array Bool) (js : List ℕ) : Array Bool :=
  ((List.range m).flatMap fun x => js.map fun j => relAt k a x j).toArray

/-- The individualized 2-skeleton of the cells, at `i + j k`. -/
def skelArrD (wl : Array ℕ) (d k : ℕ) (xd : List ℕ) : Array ℕ :=
  ((List.range k).flatMap fun j => (List.range k).map fun i =>
    get wl (codePad2 (pwTab d k) d xd.length xd.toArray i j)).toArray

/-- The index in the numbering `V₁' ⊔ V₂` (points `ps`, then `k` cells) of an element of the
numbering of all points (`u < m`) and cells (`m + j`). -/
def idxQ (m : ℕ) (ps : List ℕ) (k u : ℕ) : Option ℕ :=
  if u < m then (if u ∈ ps then some (ps.idxOf u) else none)
  else if u < m + k then some (ps.length + (u - m)) else none

/-- The refined colouring `cQ` on all points (`u < m`) and cells (`m + j`): read from the
refinement `W2` on `V₁' ⊔ V₂`, and `0` off it. -/
def cQd (m : ℕ) (ps : List ℕ) (k : ℕ) (W2 : Array ℕ) (u v : ℕ) : ℕ :=
  match idxQ m ps k u, idxQ m ps k v with
  | some i, some j => get W2 (i + j * (ps.length + k))
  | _, _ => 0

/-- `cQd` as an `N × N` array, row-major (`N = m + k`). -/
def cQArr (m : ℕ) (ps : List ℕ) (k : ℕ) (W2 : Array ℕ) : Array ℕ :=
  ((List.range (m + k)).flatMap fun u => (List.range (m + k)).map fun v =>
    cQd m ps k W2 u v).toArray

/-- The colours `f y (m + j)` of the points `y < m` and the cells `j < k`, as a table. -/
def rectArr (m k : ℕ) (f : ℕ → ℕ → ℕ) : Array (Array ℕ) :=
  ((List.range m).map fun y => ((List.range k).map fun j => f y (m + j)).toArray).toArray

/-- The cell of an ideal point given by the index list `l` (the union of its cells). -/
def cellUD (m k : ℕ) (cs : List (List ℕ)) (l : List ℕ) : List ℕ :=
  (List.range m).filter fun y =>
    decide (y ∈ (l.filter fun i => decide (m ≤ i ∧ i < m + k)).flatMap fun i => cs.getD (i - m) [])

/-- Keep the first of the cells equal as sets. -/
def dedupCellsD (m : ℕ) (ls : List (List ℕ)) : List (List ℕ) :=
  ls.foldl (fun acc l => if acc.any (setEqD m l) then acc else acc ++ [l]) []

/-- The relation of the bipartite graph of `cohCont`: point `x` and cell `cell` are related when
an ideal point of `W₂` with this cell has a `g`-edge from `x`. -/
def bipRelX (m N k : ℕ) (cs : List (List ℕ)) (f : ℕ → ℕ → ℕ) (g : ℕ) (W₂ : List (List ℕ))
    (cells : List (List ℕ)) : Array Bool :=
  ((List.range m).flatMap fun x => cells.map fun cell =>
    W₂.any fun l => setEqD m (cellUD m k cs l) cell && l.any fun y => decide (y < N) && f x y == g
  ).toArray

/-- **`cohCont` on data**, for a leaf of `cohSojD` on all points and cells: `D₁ = V₁ \ V₁'`,
`D₂ = V₁' \ C₁`. -/
def contI (m t k : ℕ) (cs : List (List ℕ)) (D₁ D₂ C₁ : List ℕ) (f : ℕ → ℕ → ℕ) :
    Option SoJProg.LeafD → Item
  | none => .inl noneD
  | some (tag, (col, blk), (W₁, W₂, g)) =>
    if tag = 0 then .inl (addPieceD m D₁ (addPieceD m D₂ (partD col blk)))
    else
      let W := (List.range m).filter fun y => y ∈ W₁
      if W.length ≤ t then
        .inl (addPieceD m D₁ (addPieceD m D₂ (addPieceD m (diffD C₁ W)
          (partD #[] (colBlkD m W #[])))))
      else
        let cells := dedupCellsD m (W₂.map (cellUD m k cs))
        shrinkI k W cells (bipRelX m (m + k) k cs f g W₂ cells)
          [pieceOp (diffD C₁ W), pieceOp D₂, pieceOp D₁]

/-- **The `cohSoj` level on data**: `cohSojD` on all points and cells, and `cohCont` at its
leaves; the work is the number of options. -/
def cohI (m t k : ℕ) (cs : List (List ℕ)) (D₁ D₂ C₁ C₂ : List ℕ) (f : ℕ → ℕ → ℕ) :
    List Item × ℕ :=
  match cohSojD f (m + k) C₁ (C₂.map (m + ·)) with
  | .leaf o => ([contI m t k cs D₁ D₂ C₁ f o], 0)
  | .node opts kk => (opts.map fun y => contI m t k cs D₁ D₂ C₁ f (kk y), opts.length)

/-- **`dlCont` on data**, after the Design Lemma's choice `xd` (cell indices). -/
def dlI (m t : ℕ) (V₁ V₁' : List ℕ) (cs : List (List ℕ)) (a : Array Bool) (d : ℕ)
    (wl : Array ℕ) (xd : List ℕ) : List Item × ℕ :=
  let k := cs.length
  let t₂ := 2 * k / 3
  let col1 := col1A wl (pwTab d k) d k xd.length xd.toArray
  let D := diffD V₁ V₁'
  match domA col1 t₂ with
  | none =>
    let js := pickSideD V₁' k a (selThirdL (List.range k) (get col1.toArray))
    ([shrinkI k V₁' (subCells cs js) (restrictRel m k a js) [pieceOp D]], 0)
  | some _ =>
    let W2 := (wlA 2 (V₁'.length + k) (sqCodeArr V₁' k a (skelArrD wl d k xd))).1
    let f := fA (offsArr (m + k)) (cQArr m V₁' k W2)
    let col₂ := ((List.range k).map fun j => f (m + j) (m + j)).toArray
    if allSmallL (List.range k) (get col₂) t₂ then
      let js := pickSideD V₁' k a (selThirdL (List.range k) (get col₂))
      ([shrinkI k V₁' (subCells cs js) (restrictRel m k a js) [pieceOp D]], 0)
    else
      let C₂ := bigL (List.range k) (get col₂) t₂
      let colP := ((List.range m).map fun y => f y y).toArray
      let C₁ := bigL V₁' (get colP) t
      if C₁ = [] then
        ([.inl (addPieceD m D (partD colP (colBlkD m V₁' colP)))], 0)
      else if constRectL C₁ C₂ (get2 (rectArr m k f)) then
        let js := (List.range k).filter fun j => j ∉ C₂
        ([shrinkI k V₁' (subCells cs js) (restrictRel m k a js) [pieceOp D]], 0)
      else cohI m t k cs D (diffD V₁' C₁) C₁ C₂ f

/-- **One level of `bsoj` on data** (`bstep` with its continuations), unwrapped: the items and
the work. -/
def bstepI (m t : ℕ) (V₁ : List ℕ) (cs : List (List ℕ)) (a : Array Bool) : List Item × ℕ :=
  let k := cs.length
  match optMin (bigDegsD t V₁ k a) with
  | none => ([.inl (partD (twinColD m V₁ k a) (twinBlkD m V₁ k a))], 0)
  | some d₁ =>
    let V₁' := tfDegD V₁ k a d₁
    let s := sOf k d₁
    if V₁'.length = k.choose s then ([.inl (johnD V₁' cs s (fArrD m k a d₁))], 0)
    else if IsBase t k then
      let es := (List.range k).permutations'
      (es.map fun js => .inl (partD (nbrCodeArrD m k a js) (colBlkD m V₁ (nbrCodeArrD m k a js))),
        es.length)
    else
      let d := arity k s V₁'.length
      let col := daryArr k d (V₁'.map (fOfD k a d₁))
      let S := bigTwinsD k d col
      if S ≠ [] then
        let js := pickSideD V₁' k a S
        ([recI k V₁' (subCells cs js) (restrictRel m k a js) [pieceOp (diffD V₁ V₁')]], 0)
      else
        let wl := (wlA d k col).1
        let xs := goodList wl d k (2 * k / 3)
        let r := xs.map (dlI m t V₁ V₁' cs a d wl)
        (r.flatMap Prod.fst, xs.length + (r.map Prod.snd).sum)

/-- One level of a frame: its items, wrapped, and the work. -/
def stepI (m t : ℕ) (fr : FrameD) : List Item × ℕ :=
  let r := bstepI m t fr.V₁ fr.cs fr.a
  (r.1.map (wrapItem m fr.wr), r.2)

/-- **One step of a frame on data**: the produced leaves and the child frames. -/
def stepD (m t : ℕ) (fr : FrameD) : List OutD × List FrameD :=
  ((stepI m t fr).1.filterMap Sum.getLeft?, (stepI m t fr).1.filterMap Sum.getRight?)

/-- **The work of a step**: the base-case enumerations, the Design Lemma options and their
`cohSoj` options. -/
def stepWork (m t : ℕ) (fr : FrameD) : ℕ := (stepI m t fr).2


/-! ### Wrappers -/

section Wrap

variable {m : ℕ}

theorem opOut_none (op : WrapOp) : opOut m op none = none := by
  unfold opOut
  split_ifs <;> rfl

theorem wrapOut_none (ops : List WrapOp) : wrapOut m ops none = none := by
  induction ops with
  | nil => rfl
  | cons op ops ih =>
    show wrapOut m ops (opOut m op none) = none
    rw [opOut_none, ih]

theorem wrapOut_cons (op : WrapOp) (ops : List WrapOp) (o : Option (Out (Fin m))) :
    wrapOut m (op :: ops) o = wrapOut m ops (opOut m op o) := rfl

theorem wrapOut_append (ops ops' : List WrapOp) (o : Option (Out (Fin m))) :
    wrapOut m (ops ++ ops') o = wrapOut m ops' (wrapOut m ops o) := by
  unfold wrapOut
  rw [List.foldl_append]

theorem decodeOut_opD (op : WrapOp) (o : OutD) :
    decodeOut m (opD m op o) = opOut m op (decodeOut m o) := by
  unfold opD opOut
  split_ifs
  · exact decodeOut_extendD m _ (fun _ => rfl) o
  · exact decodeOut_addPieceD m _ o

theorem decodeOut_wrapD (ops : List WrapOp) (o : OutD) :
    decodeOut m (wrapD m ops o) = wrapOut m ops (decodeOut m o) := by
  induction ops generalizing o with
  | nil => rfl
  | cons op ops ih =>
    show decodeOut m (wrapD m ops (opD m op o)) = _
    rw [ih, decodeOut_opD]
    rfl

theorem wrapT_wrapT (ops ops' : List WrapOp) (T : STree (Fin m)) :
    wrapT m ops' (wrapT m ops T) = wrapT m (ops ++ ops') T := by
  unfold wrapT
  rw [CTree.bind_assoc]
  congr 1
  funext o
  show CTree.leaf _ = CTree.leaf _
  rw [wrapOut_append]

theorem withPiece_eq_wrapT (D : List ℕ) (T : STree (Fin m)) :
    withPiece (setOf m D) T = wrapT m [pieceOp D] T := rfl

theorem wrapT_leaf (ops : List WrapOp) (o : Option (Out (Fin m))) :
    wrapT m ops (.leaf o) = .leaf (wrapOut m ops o) := rfl

theorem leafMs_wrapT (ops : List WrapOp) (T : STree (Fin m)) :
    (wrapT m ops T).leafMs = T.leafMs.map (wrapOut m ops) := by
  unfold wrapT
  rw [CTree.leafMs_bind]
  exact Multiset.bind_singleton _ _

theorem size_wrapT (ops : List WrapOp) (T : STree (Fin m)) : (wrapT m ops T).size = T.size :=
  CTree.size_bind_leaf _ _

theorem TEq.wrapT {ops : List WrapOp} {T T' : STree (Fin m)} (h : TEq T T') :
    TEq (wrapT m ops T) (wrapT m ops T') :=
  TEq.bind (fun _ => TEq.refl _) h

end Wrap

/-! ### Level descriptions -/

section Desc

variable {m t k : ℕ}

theorem sum_map_map_ms (items : List Item) (g : Option (Out (Fin m)) → Option (Out (Fin m)))
    (F : Item → Multiset (Option (Out (Fin m)))) :
    ((items.map F).sum).map g = (items.map fun i => (F i).map g).sum := by
  induction items with
  | nil => simp
  | cons i l ih => simp [Multiset.map_add, ih]

theorem desc_leaf (o : OutD) : Desc m t k (.leaf (decodeOut m o)) [.inl o] 0 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [itemMs, CTree.leafMs]
  · simp [itemSize, CTree.size]
  · simp

theorem desc_of_teq {T T' : STree (Fin m)} {items : List Item} {w : ℕ} (h : TEq T T')
    (d : Desc m t k T' items w) : Desc m t k T items w :=
  ⟨by rw [h.leafMs_eq]; exact d.ms, by rw [h.size_eq]; exact d.size, d.ok⟩

theorem desc_of_eq {T T' : STree (Fin m)} {items : List Item} {w : ℕ} (h : T = T')
    (d : Desc m t k T' items w) : Desc m t k T items w := h ▸ d

theorem desc_frame (fr : FrameD) (hv : fr.Valid m) (hk : fr.cs.length < k) :
    Desc m t k (fr.tree m t) [.inr fr] 0 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [itemMs]
  · simp [itemSize]
  · intro ch hch
    simp only [List.mem_singleton, Sum.inr.injEq] at hch
    subst hch
    exact ⟨hv, hk⟩

theorem itemMs_wrapItem (ops : List WrapOp) (i : Item) :
    itemMs m t (wrapItem m ops i) = (itemMs m t i).map (wrapOut m ops) := by
  cases i with
  | inl o => simp [itemMs, wrapItem, decodeOut_wrapD]
  | inr fr =>
    simp only [itemMs, wrapItem, FrameD.tree, FrameD.V₁, FrameD.cs, FrameD.a, FrameD.wr]
    rw [← wrapT_wrapT, leafMs_wrapT]

theorem itemSize_wrapItem (ops : List WrapOp) (i : Item) :
    itemSize m t (wrapItem m ops i) = itemSize m t i := by
  cases i with
  | inl o => rfl
  | inr fr =>
    simp only [itemSize, wrapItem, FrameD.tree, FrameD.V₁, FrameD.cs, FrameD.a, FrameD.wr]
    rw [← wrapT_wrapT, size_wrapT]

theorem desc_wrapT {T : STree (Fin m)} {items : List Item} {w : ℕ} (ops : List WrapOp)
    (d : Desc m t k T items w) : Desc m t k (wrapT m ops T) (items.map (wrapItem m ops)) w := by
  refine ⟨?_, ?_, ?_⟩
  · rw [leafMs_wrapT, d.ms, sum_map_map_ms, List.map_map]
    congr 1
    exact List.map_congr_left fun i _ => (itemMs_wrapItem ops i).symm
  · rw [size_wrapT, List.map_map]
    have : (items.map (itemSize m t ∘ wrapItem m ops)) = items.map (itemSize m t) :=
      List.map_congr_left fun i _ => itemSize_wrapItem ops i
    rw [this]
    exact d.size
  · intro ch hch
    obtain ⟨i, hi, he⟩ := List.mem_map.1 hch
    cases i with
    | inl o => simp [wrapItem] at he
    | inr fr =>
      simp only [wrapItem, Sum.inr.injEq] at he
      subst he
      obtain ⟨⟨h1, h2, h3⟩, h4⟩ := d.ok fr hi
      exact ⟨⟨h1, h2, h3⟩, h4⟩

theorem desc_node {β : Type*} [DecidableEq β] {S : Finset (Choice (Fin m))}
    {kk : Choice (Fin m) → STree (Fin m)} (L : List β) (h : β → Choice (Fin m))
    (hS : S = (L.map h).toFinset) (hnd : (L.map h).Nodup) (F : β → List Item × ℕ)
    (hF : ∀ c ∈ L, Desc m t k (kk (h c)) (F c).1 (F c).2) :
    Desc m t k (.node S kk) (L.flatMap fun c => (F c).1)
      (L.length + (L.map fun c => (F c).2).sum) := by
  subst hS
  have hsum : ∀ {M : Type} [AddCommMonoid M] (g : Choice (Fin m) → M),
      ∑ s ∈ (L.map h).toFinset, g s = (L.map fun c => g (h c)).sum := by
    intro M _ g
    rw [List.sum_toFinset g hnd, List.map_map]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · show ∑ s ∈ (L.map h).toFinset, (kk s).leafMs = _
    rw [hsum]
    clear hsum hnd
    induction L with
    | nil => simp
    | cons c L ih =>
      simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.map_append,
        List.sum_append]
      rw [(hF c List.mem_cons_self).ms, ih fun c' hc' => hF c' (List.mem_cons_of_mem _ hc')]
  · show _ ≤ 1 + ∑ s ∈ (L.map h).toFinset, ((kk s).size + 1)
    rw [hsum]
    clear hsum hnd
    induction L with
    | nil => simp
    | cons c L ih =>
      have h1 := (hF c List.mem_cons_self).size
      have h2 := ih fun c' hc' => hF c' (List.mem_cons_of_mem _ hc')
      simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.map_append,
        List.sum_append, List.length_cons] at h1 h2 ⊢
      omega
  · intro ch hch
    obtain ⟨c, hc, hch⟩ := List.mem_flatMap.1 hch
    exact (hF c hc).ok ch hch

/-- The guarded recursion of `bsoj`. -/
def recB (t : ℕ) (V₂ : Finset (Finset (Fin m))) :
    Finset (Fin m) → Finset (Finset (Fin m)) → (Fin m → Finset (Fin m) → Bool) →
      STree (Fin m) :=
  fun V₁' V₂' A' => if _h : V₂'.card < V₂.card then bsoj t V₁' V₂' A' else .leaf none

theorem desc_recI {V₂ : Finset (Finset (Fin m))} (hk : V₂.card = k) {V : List ℕ}
    {cs : List (List ℕ)} {a : Array Bool} {A : Fin m → Finset (Fin m) → Bool}
    (hV : V.Nodup) (hVm : ∀ x ∈ V, x < m) (hcs : (cs.map (setOf m)).Nodup)
    (hA : ∀ x, ∀ s ∈ famOf m cs, A x s = relOf m cs a x s) (ops : List WrapOp) :
    Desc m t k (wrapT m ops (recB t V₂ (setOf m V) (famOf m cs) A)) [recI k V cs a ops] 0 := by
  have hc : (famOf m cs).card = cs.length := card_famOf (getD_inj_of_nodup hcs)
  unfold recB recI
  by_cases hlt : cs.length < k
  · rw [dite_eq_left (by rw [hc, hk]; exact hlt), ite_eq_left hlt]
    refine desc_of_teq (TEq.wrapT (bsoj_congr t _ _ hA)) ?_
    exact desc_frame (V, cs, a, ops) ⟨hV, hVm, hcs⟩ hlt
  · rw [dite_eq_right (by rw [hc, hk]; exact hlt), ite_eq_right hlt, wrapT_leaf, wrapOut_none]
    exact (decodeOut_noneD m) ▸ desc_leaf noneD

theorem desc_shrinkI {V₂ : Finset (Finset (Fin m))} (hk : V₂.card = k) {V : List ℕ}
    {cs : List (List ℕ)} {a : Array Bool} {A : Fin m → Finset (Fin m) → Bool}
    (hV : V.Nodup) (hVm : ∀ x ∈ V, x < m) (hcs : (cs.map (setOf m)).Nodup)
    (hA : ∀ x, ∀ s ∈ famOf m cs, A x s = relOf m cs a x s) (ops : List WrapOp) :
    Desc m t k (wrapT m ops (shrink V₂ (recB t V₂) (setOf m V) (famOf m cs) A))
      [shrinkI k V cs a ops] 0 := by
  have hc : (famOf m cs).card = cs.length := card_famOf (getD_inj_of_nodup hcs)
  unfold shrink shrinkI
  by_cases h3 : 3 * cs.length ≤ 2 * k
  · rw [ite_eq_left (by rw [hc, hk]; exact h3)]
    by_cases hlt : cs.length < k
    · rw [ite_eq_left ⟨h3, hlt⟩]
      have := desc_recI (t := t) hk hV hVm hcs hA ops
      rwa [recI, ite_eq_left hlt] at this
    · rw [ite_eq_right fun h => hlt h.2]
      have := desc_recI (t := t) hk hV hVm hcs hA ops
      rwa [recI, ite_eq_right hlt] at this
  · rw [ite_eq_right (by rw [hc, hk]; exact h3), ite_eq_right fun h => h3 h.1, wrapT_leaf,
      wrapOut_none]
    exact (decodeOut_noneD m) ▸ desc_leaf noneD

end Desc


/-! ### Points and cells numbered together -/

section Numbering

variable {m : ℕ} {cs : List (List ℕ)}

/-- The numbering of all points (`u < m`) and the cells (`m + j`). -/
def eQf (m : ℕ) (cs : List (List ℕ)) (u : ℕ) : Fin m ⊕ Finset (Fin m) :=
  if h : u < m then .inl ⟨u, h⟩ else .inr (cellAt m cs (u - m))

theorem eQf_injOn (hcs : (cs.map (setOf m)).Nodup) {u v : ℕ} (hu : u < m + cs.length)
    (hv : v < m + cs.length) (h : eQf m cs u = eQf m cs v) : u = v := by
  unfold eQf at h
  split_ifs at h with h1 h2 h2
  all_goals first
    | exact congrArg Fin.val (Sum.inl_injective h)
    | exact absurd h Sum.inl_ne_inr
    | exact absurd h.symm Sum.inl_ne_inr
    | (have := getD_inj_of_nodup hcs (u - m) (by omega) (v - m) (by omega)
          (Sum.inr_injective h)
       omega)

/-- The numbering as an embedding. -/
def eQ (hcs : (cs.map (setOf m)).Nodup) : Fin (m + cs.length) ↪ Fin m ⊕ Finset (Fin m) :=
  ⟨fun u => eQf m cs u.val, fun u v h => Fin.ext (eQf_injOn hcs u.2 v.2 h)⟩

theorem eQ_apply (hcs : (cs.map (setOf m)).Nodup) (u : Fin (m + cs.length)) :
    eQ hcs u = eQf m cs u.val := rfl

theorem eQ_inl (hcs : (cs.map (setOf m)).Nodup) (x : Fin m) :
    eQ hcs ⟨x.val, by omega⟩ = .inl x := by
  simp [eQ_apply, eQf, x.2]

theorem eQ_eq_inl_iff (hcs : (cs.map (setOf m)).Nodup) (u : Fin (m + cs.length)) (x : Fin m) :
    eQ hcs u = .inl x ↔ u.val = x.val := by
  rw [eQ_apply, eQf]
  split_ifs with h
  · simp only [Sum.inl.injEq]
    exact ⟨fun e => by rw [← e], fun e => Fin.ext e⟩
  · simp only [false_iff]
    intro e
    exact h (e ▸ x.2)

theorem eQ_eq_inr_iff (hcs : (cs.map (setOf m)).Nodup) (u : Fin (m + cs.length))
    (s : Finset (Fin m)) : eQ hcs u = .inr s ↔ m ≤ u.val ∧ cellAt m cs (u.val - m) = s := by
  rw [eQ_apply, eQf]
  split_ifs with h
  · simp only [false_iff, not_and]
    intro h'
    omega
  · simp only [Sum.inr.injEq]
    exact ⟨fun e => ⟨by omega, e⟩, fun e => e.2⟩

theorem setOf_diffD (V V' : List ℕ) : setOf m (diffD V V') = setOf m V \ setOf m V' := by
  ext x
  simp [diffD, mem_setOf]

/-- The points of an index list, after the numbering. -/
theorem toLeft_map_eQ (hcs : (cs.map (setOf m)).Nodup) (l : List ℕ) :
    ((setOf (m + cs.length) l).map (eQ hcs)).toLeft = setOf m l := by
  ext x
  rw [mem_toLeft, mem_map, mem_setOf]
  constructor
  · rintro ⟨u, hu, he⟩
    rw [eQ_eq_inl_iff] at he
    rw [mem_setOf] at hu
    rwa [← he]
  · intro hx
    exact ⟨⟨x.val, by omega⟩, mem_setOf.2 hx, eQ_inl hcs x⟩

/-- The cell of an ideal point, after the numbering. -/
theorem cellOf_map_eQ (hcs : (cs.map (setOf m)).Nodup) (l : List ℕ) :
    cellOf ((setOf (m + cs.length) l).map (eQ hcs)) = setOf m (cellUD m cs.length cs l) := by
  ext x
  rw [mem_cellOf, mem_setOf, cellUD, List.mem_filter, List.mem_range, decide_eq_true_eq,
    List.mem_flatMap]
  simp only [x.2, true_and]
  constructor
  · rintro ⟨s, hs, hx⟩
    obtain ⟨u, hu, he⟩ := mem_map.1 hs
    rw [eQ_eq_inr_iff] at he
    obtain ⟨hmu, rfl⟩ := he
    rw [mem_setOf] at hu
    refine ⟨u.val, List.mem_filter.2 ⟨hu, ?_⟩, ?_⟩
    · simp only [decide_eq_true_eq]
      exact ⟨hmu, u.2⟩
    · rw [cellAt, mem_setOf] at hx
      exact hx
  · rintro ⟨i, hi, hx⟩
    obtain ⟨hil, hc⟩ := List.mem_filter.1 hi
    simp only [decide_eq_true_eq] at hc
    refine ⟨cellAt m cs (i - m), mem_map.2 ⟨⟨i, hc.2⟩, mem_setOf.2 hil, ?_⟩, ?_⟩
    · rw [eQ_eq_inr_iff]
      exact ⟨hc.1, rfl⟩
    · rw [cellAt, mem_setOf]
      exact hx

/-- The colouring of all points and cells as an array. -/
def arrOfD (N : ℕ) (f : ℕ → ℕ → ℕ) : Array ℕ :=
  ((List.range (N * N)).map fun u => f (u / N) (u % N)).toArray

theorem colOf_arrOfD (N : ℕ) (f : ℕ → ℕ → ℕ) (u v : Fin N) : colOf N (arrOfD N f) u v = f u v := by
  have hlt : u.val * N + v.val < N * N := by
    have := u.2
    have := v.2
    nlinarith
  rw [colOf, arrOfD, get, Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
    List.getElem?_range hlt]
  simp only [Option.map_some, Option.getD_some]
  have hN : 0 < N := by have := v.2; omega
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hN, Nat.div_eq_of_lt v.2, Nat.zero_add,
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt v.2]

end Numbering

/-! ### Distinct cells -/

section Dedup

variable {m : ℕ}

theorem dedupCells_spec (ls : List (List ℕ)) :
    ∀ acc : List (List ℕ), (acc.map (setOf m)).Nodup →
      ((ls.foldl (fun acc l => if acc.any (setEqD m l) then acc else acc ++ [l]) acc).map
        (setOf m)).Nodup ∧
      famOf m (ls.foldl (fun acc l => if acc.any (setEqD m l) then acc else acc ++ [l]) acc) =
        famOf m acc ∪ famOf m ls := by
  induction ls with
  | nil => intro acc h; simp [famOf, h]
  | cons l ls ih =>
    intro acc hacc
    rw [List.foldl_cons]
    by_cases hany : acc.any (setEqD m l) = true
    · rw [ite_eq_left hany]
      obtain ⟨h1, h2⟩ := ih acc hacc
      refine ⟨h1, ?_⟩
      rw [h2]
      obtain ⟨l', hl', he⟩ := List.any_eq_true.1 hany
      rw [setEqD_iff] at he
      ext s
      simp only [mem_union, famOf, List.mem_toFinset, List.mem_map, List.mem_cons]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · obtain ⟨l₀, hl₀, rfl⟩ := h
          exact Or.inr ⟨l₀, Or.inr hl₀, rfl⟩
      · rintro (h | ⟨l₀, hl₀ | hl₀, rfl⟩)
        · exact Or.inl h
        · subst hl₀
          exact Or.inl ⟨l', hl', he.symm⟩
        · exact Or.inr ⟨l₀, hl₀, rfl⟩
    · rw [ite_eq_right hany]
      have hnd : ((acc ++ [l]).map (setOf m)).Nodup := by
        rw [List.map_append, List.nodup_append]
        refine ⟨hacc, List.nodup_singleton _, ?_⟩
        intro a ha b hb hab
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
        subst hb hab
        obtain ⟨l', hl', he⟩ := List.mem_map.1 ha
        exact hany (List.any_eq_true.2 ⟨l', hl', (setEqD_iff m l l').2 he.symm⟩)
      obtain ⟨h1, h2⟩ := ih (acc ++ [l]) hnd
      refine ⟨h1, ?_⟩
      rw [h2]
      ext s
      simp only [mem_union, famOf, List.mem_toFinset, List.mem_map, List.mem_cons,
        List.mem_append, List.not_mem_nil, or_false]
      constructor
      · rintro (⟨l₀, hl₀ | rfl, rfl⟩ | ⟨l₀, hl₀, rfl⟩)
        · exact Or.inl ⟨l₀, hl₀, rfl⟩
        · exact Or.inr ⟨l₀, Or.inl rfl, rfl⟩
        · exact Or.inr ⟨l₀, Or.inr hl₀, rfl⟩
      · rintro (⟨l₀, hl₀, rfl⟩ | ⟨l₀, rfl | hl₀, rfl⟩)
        · exact Or.inl ⟨l₀, Or.inl hl₀, rfl⟩
        · exact Or.inl ⟨l₀, Or.inr rfl, rfl⟩
        · exact Or.inr ⟨l₀, hl₀, rfl⟩

theorem nodup_dedupCellsD (ls : List (List ℕ)) : ((dedupCellsD m ls).map (setOf m)).Nodup :=
  (dedupCells_spec ls [] List.nodup_nil).1

theorem famOf_dedupCellsD (ls : List (List ℕ)) : famOf m (dedupCellsD m ls) = famOf m ls := by
  rw [dedupCellsD, (dedupCells_spec ls [] List.nodup_nil).2]
  simp [famOf]

end Dedup


/-! ### Relations on data -/

section Rel

variable {m : ℕ}

/-- Reading a relation array built row by row for the points below `m`. -/
theorem getD_rows (k : ℕ) (F : ℕ → List Bool) (hF : ∀ x, (F x).length = k) {x j : ℕ}
    (hx : x < m) (hj : j < k) :
    ((List.range m).flatMap F).toArray.getD (x * k + j) false = (F x).getD j false := by
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, ← List.getD_eq_getElem?_getD,
    getD_flatMap_const F k false (List.range m) (fun a _ => hF a) x (by simpa using hx) j hj]
  simp

/-- The relation on a listed cell, read from a row-built array. -/
theorem relOf_rows {cs : List (List ℕ)} (hcs : (cs.map (setOf m)).Nodup) (F : ℕ → List Bool)
    (hF : ∀ x, (F x).length = cs.length) (x : Fin m) {j : ℕ} (hj : j < cs.length) :
    relOf m cs ((List.range m).flatMap F).toArray x (setOf m (cs.getD j [])) =
      (F x).getD j false := by
  rw [relOf_cell (getD_inj_of_nodup hcs) hj, getD_rows cs.length F hF x.2 hj]

theorem mem_setOf_range_filter (l : List ℕ) (x : Fin m) :
    x ∈ setOf m ((List.range m).filter fun y => y ∈ l) ↔ x.val ∈ l := by
  rw [mem_setOf, List.mem_filter, List.mem_range]
  simp [x.2]

theorem setOf_range_filter (l : List ℕ) :
    setOf m ((List.range m).filter fun y => y ∈ l) = setOf m l := by
  ext x
  rw [mem_setOf_range_filter, mem_setOf]

theorem nodup_range_filter (p : ℕ → Bool) : ((List.range m).filter p).Nodup :=
  List.nodup_range.filter p

theorem lt_of_mem_range_filter {p : ℕ → Bool} {y : ℕ} (hy : y ∈ (List.range m).filter p) :
    y < m :=
  List.mem_range.1 (List.mem_of_mem_filter hy)

end Rel

/-! ### `cohCont` on data -/

section Cont

variable {m t : ℕ} {cs : List (List ℕ)}

theorem get_empty (i : ℕ) : get #[] i = 0 := by simp [get]

theorem withPiece3 (D₁ D₂ D₃ : List ℕ) (T : STree (Fin m)) :
    withPiece (setOf m D₁) (withPiece (setOf m D₂) (withPiece (setOf m D₃) T)) =
      wrapT m [pieceOp D₃, pieceOp D₂, pieceOp D₁] T := by
  rw [withPiece_eq_wrapT, withPiece_eq_wrapT, withPiece_eq_wrapT, wrapT_wrapT, wrapT_wrapT]
  rfl

/-- The relation of `cohCont`'s recursive call is the data relation on the new cells. -/
theorem bipRelX_spec (hcs : (cs.map (setOf m)).Nodup) {f : ℕ → ℕ → ℕ} (g : ℕ)
    (W₂ : List (List ℕ)) {AR : Fin m ⊕ Finset (Fin m) → Finset (Fin m ⊕ Finset (Fin m)) → Bool}
    (hAR : ∀ (x' : Fin (m + cs.length)) (B' : Finset (Fin (m + cs.length))),
      AR (eQ hcs x') (B'.map (eQ hcs)) =
        bipEdge (colOf (m + cs.length) (arrOfD (m + cs.length) f)) g x' B')
    (x : Fin m) (s : Finset (Fin m))
    (hs : s ∈ famOf m (dedupCellsD m (W₂.map (cellUD m cs.length cs)))) :
    (∃ B ∈ (famOf (m + cs.length) W₂).image fun B => B.map (eQ hcs),
        cellOf B = s ∧ AR (.inl x) B = true) ↔
      relOf m (dedupCellsD m (W₂.map (cellUD m cs.length cs)))
        (bipRelX m (m + cs.length) cs.length cs f g W₂
          (dedupCellsD m (W₂.map (cellUD m cs.length cs)))) x s = true := by
  set cells := dedupCellsD m (W₂.map (cellUD m cs.length cs))
  set N := m + cs.length
  obtain ⟨l, hl, rfl⟩ := mem_famOf.1 hs
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hl
  have hget : cells.getD j [] = cells[j] := List.getD_eq_getElem _ _ hj
  rw [← hget, bipRelX, relOf_rows (nodup_dedupCellsD _) _ (fun _ => List.length_map _) x hj,
    List.getD_eq_getElem (List.map _ cells) false (by simpa using hj), List.getElem_map, hget]
  have hx : eQ hcs ⟨x.val, by omega⟩ = .inl x := eQ_inl hcs x
  have hE : ∀ l' : List ℕ, AR (.inl x) ((setOf N l').map (eQ hcs)) = true ↔
      ∃ y ∈ l', y < N ∧ f x y = g := by
    intro l'
    rw [← hx, hAR]
    simp only [bipEdge, decide_eq_true_eq]
    constructor
    · rintro ⟨y, hy, hyg⟩
      rw [colOf_arrOfD] at hyg
      exact ⟨y.val, mem_setOf.1 hy, y.2, hyg⟩
    · rintro ⟨y, hy, hyN, hyg⟩
      exact ⟨⟨y, hyN⟩, mem_setOf.2 hy, by rw [colOf_arrOfD]; exact hyg⟩
  rw [List.any_eq_true]
  constructor
  · rintro ⟨B, hB, hc, hA⟩
    obtain ⟨B', hB', rfl⟩ := mem_image.1 hB
    obtain ⟨l', hl', rfl⟩ := mem_famOf.1 hB'
    obtain ⟨y, hy, hyN, hyg⟩ := (hE l').1 hA
    refine ⟨l', hl', ?_⟩
    rw [Bool.and_eq_true, setEqD_iff, ← cellOf_map_eQ hcs, hc, List.any_eq_true]
    refine ⟨rfl, y, hy, ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    exact ⟨hyN, hyg⟩
  · rintro ⟨l', hl', h⟩
    rw [Bool.and_eq_true, setEqD_iff, List.any_eq_true] at h
    obtain ⟨hc, y, hy, hyg⟩ := h
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hyg
    exact ⟨(setOf N l').map (eQ hcs), mem_image.2 ⟨setOf N l', mem_famOf.2 ⟨l', hl', rfl⟩, rfl⟩,
      by rw [cellOf_map_eQ hcs]; exact hc, (hE l').2 ⟨y, hy, hyg.1, hyg.2⟩⟩

/-- **`cohCont` on data.** -/
theorem desc_cont (hcs : (cs.map (setOf m)).Nodup) {f : ℕ → ℕ → ℕ} (V₁ V₁' C₁ : List ℕ)
    (o : Option SoJProg.LeafD) (oR : Option (CohOut (Fin m ⊕ Finset (Fin m))))
    (hag : OutAgree (eQ hcs) oR
      (decodeLeaf (m + cs.length) (arrOfD (m + cs.length) f) o)) :
    Desc m t cs.length
      (cohCont t (setOf m V₁) (setOf m V₁') (setOf m C₁)
        (shrink (famOf m cs) (recB t (famOf m cs))) oR)
      [contI m t cs.length cs (diffD V₁ V₁') (diffD V₁' C₁) C₁ f o] 0 := by
  have hk : (famOf m cs).card = cs.length := card_famOf (getD_inj_of_nodup hcs)
  rcases o with _ | ⟨tag, ⟨col, blk⟩, W₁, W₂, g⟩
  · rcases oR with _ | (p | ⟨W₁R, W₂R, AR⟩)
    · have := desc_leaf (m := m) (t := t) (k := cs.length) noneD
      rw [decodeOut_noneD] at this
      exact this
    · exact hag.elim
    · exact hag.elim
  by_cases htag : tag = 0
  · have hdec : decodeLeaf (m + cs.length) (arrOfD (m + cs.length) f)
        (some (tag, (col, blk), (W₁, W₂, g))) = some (.part ⟨fun x => get col x.val,
          fun x => setOf (m + cs.length) (blk.getD x.val [])⟩) := by
      simp [decodeLeaf, htag]
    rw [hdec] at hag
    rcases oR with _ | (p | ⟨W₁R, W₂R, AR⟩)
    · exact hag.elim
    · have hp : (⟨fun x => p.col (.inl x), fun x => (p.blk (.inl x)).toLeft⟩ : CPart (Fin m)) =
          cpartOf m col blk := by
        unfold cpartOf
        congr 1
        · funext x
          rw [← eQ_inl hcs x]
          exact (hag _).1
        · funext x
          rw [← eQ_inl hcs x, (hag _).2, toLeft_map_eQ]
      have e1 : cohCont t (setOf m V₁) (setOf m V₁') (setOf m C₁)
          (shrink (famOf m cs) (recB t (famOf m cs))) (some (.part p)) =
          .leaf (decodeOut m (addPieceD m (diffD V₁ V₁') (addPieceD m (diffD V₁' C₁)
            (partD col blk)))) := by
        rw [decodeOut_addPieceD, decodeOut_addPieceD, decodeOut_partD, setOf_diffD,
          setOf_diffD, ← hp]
        rfl
      rw [e1, contI, ite_eq_left htag]
      exact desc_leaf _
    · exact hag.elim
  · have hdec : decodeLeaf (m + cs.length) (arrOfD (m + cs.length) f)
        (some (tag, (col, blk), (W₁, W₂, g))) = some (.bip (setOf (m + cs.length) W₁)
          (famOf (m + cs.length) W₂)
          (bipEdge (colOf (m + cs.length) (arrOfD (m + cs.length) f)) g)) := by
      simp [decodeLeaf, htag]
    rw [hdec] at hag
    rcases oR with _ | (p | ⟨W₁R, W₂R, AR⟩)
    · exact hag.elim
    · exact hag.elim
    obtain ⟨rfl, rfl, hAR⟩ := hag
    set Wd := (List.range m).filter fun y => y ∈ W₁
    have hW : ((setOf (m + cs.length) W₁).map (eQ hcs)).toLeft = setOf m Wd := by
      rw [toLeft_map_eQ, setOf_range_filter]
    have hWc : (setOf m Wd).card = Wd.length :=
      card_setOf (nodup_range_filter _) fun y hy => lt_of_mem_range_filter hy
    rw [contI, ite_eq_right htag]
    dsimp only
    show Desc m t cs.length (let W := ((setOf (m + cs.length) W₁).map (eQ hcs)).toLeft
      if W.card ≤ t then _ else _) _ 0
    simp only [hW, hWc]
    by_cases hWt : Wd.length ≤ t
    · rw [ite_eq_left hWt, ite_eq_left hWt]
      have e1 : (colPart (setOf m Wd) fun _ => 0) = cpartOf m #[] (colBlkD m Wd #[]) := by
        rw [colPart_decode]
        congr 1
      have := desc_leaf (m := m) (t := t) (k := cs.length) (addPieceD m (diffD V₁ V₁')
        (addPieceD m (diffD V₁' C₁) (addPieceD m (diffD C₁ Wd) (partD #[] (colBlkD m Wd #[])))))
      rwa [decodeOut_addPieceD, decodeOut_addPieceD, decodeOut_addPieceD, decodeOut_partD,
        setOf_diffD, setOf_diffD, setOf_diffD, ← e1] at this
    · rw [ite_eq_right hWt, ite_eq_right hWt, ← setOf_diffD, ← setOf_diffD, ← setOf_diffD,
        withPiece3]
      have hcells : ((famOf (m + cs.length) W₂).image (fun B => B.map (eQ hcs))).image cellOf =
          famOf m (dedupCellsD m (W₂.map (cellUD m cs.length cs))) := by
        rw [famOf_dedupCellsD, image_image]
        ext s
        simp only [mem_image, famOf, List.mem_toFinset, List.mem_map, Function.comp]
        constructor
        · rintro ⟨B, ⟨l, hl, rfl⟩, rfl⟩
          exact ⟨cellUD m cs.length cs l, ⟨l, hl, rfl⟩, (cellOf_map_eQ hcs l).symm⟩
        · rintro ⟨_, ⟨l, hl, rfl⟩, rfl⟩
          exact ⟨setOf (m + cs.length) l, ⟨l, hl, rfl⟩, cellOf_map_eQ hcs l⟩
      rw [hcells]
      refine desc_shrinkI hk (nodup_range_filter _) (fun y hy => lt_of_mem_range_filter hy)
        (nodup_dedupCellsD _) (fun x s hs => by
          rw [Bool.eq_iff_iff, ← bipRelX_spec hcs g W₂ hAR x s hs]
          simp only [decide_eq_true_eq]) _

end Cont


/-! ### The `cohSoj` level on data -/

section CohLevel

variable {m t : ℕ} {cs : List (List ℕ)}

theorem flatMap_singleton_eq {α β : Type*} (l : List α) (f : α → β) :
    l.flatMap (fun x => [f x]) = l.map f := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem desc_congr {T : STree (Fin m)} {items items' : List Item} {w w' : ℕ} {k : ℕ}
    (d : Desc m t k T items w) (hi : items = items') (hw : w = w') : Desc m t k T items' w' :=
  hi ▸ hw ▸ d

/-- The options of a node of `cohSojD` are among `C₂`. -/
theorem cohSojD_node_sublist {f : ℕ → ℕ → ℕ} {N : ℕ} {C₁ C₂ opts : List ℕ}
    {kk : ℕ → Option SoJProg.LeafD} (h : cohSojD f N C₁ C₂ = .node opts kk) :
    opts.Sublist C₂ := by
  unfold cohSojD imprimTree at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (cases h; exact List.Sublist.refl _)
    | (cases h; exact List.filter_sublist)

theorem map_inl_setOf (C₁ : List ℕ) (hC₁m : ∀ y ∈ C₁, y < m) (hcs : (cs.map (setOf m)).Nodup) :
    (setOf m C₁).map ⟨Sum.inl, Sum.inl_injective⟩ =
      (setOf (m + cs.length) C₁).map (eQ hcs) := by
  ext q
  rw [mem_map, mem_map]
  rcases q with x | s
  · constructor
    · rintro ⟨y, hy, he⟩
      simp only [Function.Embedding.coeFn_mk, Sum.inl.injEq] at he
      subst he
      exact ⟨⟨y.val, by omega⟩, mem_setOf.2 (show y.val ∈ C₁ from mem_setOf.1 hy), eQ_inl hcs y⟩
    · rintro ⟨u, hu, he⟩
      rw [eQ_eq_inl_iff] at he
      exact ⟨x, mem_setOf.2 (he ▸ mem_setOf.1 hu), rfl⟩
  · constructor
    · rintro ⟨y, -, h⟩
      exact absurd h Sum.inl_ne_inr
    · rintro ⟨u, hu, he⟩
      rw [eQ_eq_inr_iff] at he
      have := hC₁m _ (mem_setOf.1 hu)
      omega

theorem map_inr_cellsOf (C₂ : List ℕ) (hC₂k : ∀ j ∈ C₂, j < cs.length)
    (hcs : (cs.map (setOf m)).Nodup) :
    (cellsOf m cs C₂).map ⟨Sum.inr, Sum.inr_injective⟩ =
      (setOf (m + cs.length) (C₂.map (m + ·))).map (eQ hcs) := by
  ext q
  rw [mem_map, mem_map]
  rcases q with x | s
  · constructor
    · rintro ⟨y, -, h⟩
      exact absurd h.symm Sum.inl_ne_inr
    · rintro ⟨u, hu, he⟩
      rw [eQ_eq_inl_iff] at he
      obtain ⟨j, -, hj⟩ := List.mem_map.1 (mem_setOf.1 hu)
      have := x.2
      omega
  · constructor
    · rintro ⟨s', hs', he⟩
      simp only [Function.Embedding.coeFn_mk, Sum.inr.injEq] at he
      subst he
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hs')
      refine ⟨⟨m + j, by have := hC₂k j hj; omega⟩, mem_setOf.2 (List.mem_map.2 ⟨j, hj, rfl⟩),
        ?_⟩
      rw [eQ_eq_inr_iff]
      exact ⟨Nat.le_add_right m j, by simp [cellAt]⟩
    · rintro ⟨u, hu, he⟩
      rw [eQ_eq_inr_iff] at he
      obtain ⟨hmu, rfl⟩ := he
      obtain ⟨j, hj, hju⟩ := List.mem_map.1 (mem_setOf.1 hu)
      refine ⟨cellAt m cs (u.val - m), List.mem_toFinset.2 (List.mem_map.2 ⟨j, hj, ?_⟩), rfl⟩
      rw [cellAt, ← hju, Nat.add_sub_cancel_left]

theorem image_chOf (hcs : (cs.map (setOf m)).Nodup) (opts : List ℕ)
    (hoN : ∀ u ∈ opts, u < m + cs.length) :
    ((setOf (m + cs.length) opts).map (eQ hcs)).image (fun q => ([q] : Choice (Fin m))) =
      (opts.map fun u => ([eQf m cs u] : Choice (Fin m))).toFinset := by
  ext ch
  rw [List.mem_toFinset, Finset.mem_image, List.mem_map]
  constructor
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.1 hq
    exact ⟨u.val, mem_setOf.1 hu, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨eQ hcs ⟨u, hoN u hu⟩, Finset.mem_map.2 ⟨⟨u, hoN u hu⟩, mem_setOf.2 hu, rfl⟩, rfl⟩

/-- **The `cohSoj` level of `dlCont` on data**, for a colouring `f` that reads `cQ` on all
points and cells. -/
theorem desc_cohI (hcs : (cs.map (setOf m)).Nodup)
    {cQ : Fin m ⊕ Finset (Fin m) → Fin m ⊕ Finset (Fin m) → ℕ} {f : ℕ → ℕ → ℕ}
    (hf : ∀ u v : Fin (m + cs.length), f u v = cQ (eQ hcs u) (eQ hcs v))
    (V₁ V₁' C₁ C₂ : List ℕ) (hC₁ : C₁.Nodup) (hC₁m : ∀ y ∈ C₁, y < m) (hC₂ : C₂.Nodup)
    (hC₂k : ∀ j ∈ C₂, j < cs.length) :
    Desc m t cs.length
      (((cohSoj ((setOf m C₁).map ⟨Sum.inl, Sum.inl_injective⟩)
          ((cellsOf m cs C₂).map ⟨Sum.inr, Sum.inr_injective⟩) cQ).trans (fun q => [q])
          (fun ch : Choice (Fin m) =>
            (show List (Fin m ⊕ Finset (Fin m)) from ch).headD (.inr ∅)) id).bind
        (cohCont t (setOf m V₁) (setOf m V₁') (setOf m C₁)
          (shrink (famOf m cs) (recB t (famOf m cs)))))
      (cohI m t cs.length cs (diffD V₁ V₁') (diffD V₁' C₁) C₁ C₂ f).1
      (cohI m t cs.length cs (diffD V₁ V₁') (diffD V₁' C₁) C₁ C₂ f).2 := by
  set N := m + cs.length
  have hC₂' : (C₂.map (m + ·)).Nodup := hC₂.map fun a b h => by simpa using h
  have hC₂N : ∀ u ∈ C₂.map (m + ·), u < N := by
    intro u hu
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hu
    have := hC₂k j hj
    omega
  have hpull : pull (eQ hcs) cQ = colOf N (arrOfD N f) := by
    funext u v
    rw [colOf_arrOfD, hf]
    rfl
  have hT := cohSoj_agree (eQ hcs) cQ (setOf N C₁) (setOf N (C₂.map (m + ·)))
  rw [hpull, ← decode_cohSojD (fun u v => (colOf_arrOfD N f u v).symm) hC₁ hC₂'
    (fun y hy => by have := hC₁m y hy; omega) hC₂N, ← map_inl_setOf C₁ hC₁m hcs,
    ← map_inr_cellsOf C₂ hC₂k hcs] at hT
  generalize cohSoj ((setOf m C₁).map ⟨Sum.inl, Sum.inl_injective⟩)
    ((cellsOf m cs C₂).map ⟨Sum.inr, Sum.inr_injective⟩) cQ = T at hT ⊢
  unfold cohI
  rcases hDT : cohSojD f N C₁ (C₂.map (m + ·)) with o | ⟨opts, kk⟩
  · rw [hDT] at hT
    rcases T with oR | ⟨SR, kR⟩
    · exact desc_cont hcs V₁ V₁' C₁ o oR hT
    · exact hT.elim
  · rw [hDT] at hT
    rcases T with oR | ⟨SR, kR⟩
    · exact hT.elim
    obtain ⟨rfl, hk⟩ := hT
    have hsub := cohSojD_node_sublist hDT
    have hoN : ∀ u ∈ opts, u < N := fun u hu => hC₂N u (hsub.subset hu)
    have hond : opts.Nodup := hsub.nodup hC₂'
    refine desc_congr (desc_node (β := ℕ) opts
      (fun u => ([eQf m cs u] : Choice (Fin m))) ?_ ?_
      (fun u => ([contI m t cs.length cs (diffD V₁ V₁') (diffD V₁' C₁) C₁ f (kk u)], 0))
      fun u hu => ?_) ?_ ?_
    · exact image_chOf hcs opts hoN
    · refine hond.map_on fun a ha b hb h => ?_
      have h' : [eQf m cs a] = [eQf m cs b] := h
      exact eQf_injOn hcs (hoN a ha) (hoN b hb) (List.singleton_injective h')
    · have hku := hk ⟨u, hoN u hu⟩ (mem_setOf.2 hu)
      show Desc m t cs.length (((kR (eQ hcs ⟨u, hoN u hu⟩)).trans _ _ id).bind _) _ _
      generalize kR (eQ hcs ⟨u, hoN u hu⟩) = T' at hku ⊢
      rcases T' with oR | ⟨S', k'⟩
      · exact desc_cont hcs V₁ V₁' C₁ (kk u) oR hku
      · exact hku.elim
    · exact flatMap_singleton_eq _ _
    · simp

end CohLevel


/-! ### Restricting the cells -/

section Restrict

variable {m t : ℕ} {cs : List (List ℕ)} {a : Array Bool}

theorem famOf_subCells (cs : List (List ℕ)) (js : List ℕ) :
    famOf m (subCells cs js) = cellsOf m cs js := by
  simp [famOf, subCells, cellsOf, List.map_map, Function.comp_def]

theorem nodup_subCells (hcs : (cs.map (setOf m)).Nodup) {js : List ℕ} (hjs : js.Nodup)
    (hjk : ∀ j ∈ js, j < cs.length) : ((subCells cs js).map (setOf m)).Nodup := by
  rw [subCells, List.map_map]
  refine hjs.map_on fun i hi j hj h => ?_
  exact getD_inj_of_nodup hcs i (hjk i hi) j (hjk j hj) h

theorem relOf_restrict (hcs : (cs.map (setOf m)).Nodup) {js : List ℕ} (hjs : js.Nodup)
    (hjk : ∀ j ∈ js, j < cs.length) (x : Fin m) {s : Finset (Fin m)}
    (hs : s ∈ famOf m (subCells cs js)) :
    relOf m cs a x s = relOf m (subCells cs js) (restrictRel m cs.length a js) x s := by
  have hsub := nodup_subCells hcs hjs hjk
  obtain ⟨l, hl, rfl⟩ := mem_famOf.1 hs
  obtain ⟨j', hj', rfl⟩ := List.getElem_of_mem hl
  have hlen : (subCells cs js).length = js.length := List.length_map _
  have hj'' : j' < js.length := by rwa [hlen] at hj'
  have hget : (subCells cs js).getD j' [] = (subCells cs js)[j'] := List.getD_eq_getElem _ _ hj'
  rw [← hget, restrictRel, relOf_rows hsub _ (fun _ => by rw [hlen]; exact List.length_map _) x
    (by rw [hlen]; exact hj'')]
  have hjs' : (subCells cs js).getD j' [] = cs.getD js[j'] [] := by
    rw [hget]
    simp [subCells]
  rw [hjs', relOf_cell (getD_inj_of_nodup hcs) (hjk _ (List.getElem_mem hj''))]
  rw [List.getD_eq_getElem _ _ (by simpa using hj''), List.getElem_map]
  rfl

/-- The pieces of `pickSideD`'s result. -/
theorem pickSideD_spec {ps : List ℕ} {q : ℕ} (a : Array Bool) {S : List ℕ} (hS : S.Nodup)
    (hSq : ∀ j ∈ S, j < q) :
    (pickSideD ps q a S).Nodup ∧ ∀ j ∈ pickSideD ps q a S, j < q := by
  unfold pickSideD
  split_ifs
  · exact ⟨hS, hSq⟩
  · exact ⟨nodup_range_filter _, fun j hj => lt_of_mem_range_filter hj⟩

/-- **Exercise 5.5's choice and the guarded call, on data.** -/
theorem desc_pick (hcs : (cs.map (setOf m)).Nodup) {V₁ V₁' : List ℕ} (hpn : V₁'.Nodup)
    (hps : ∀ x ∈ V₁', x < m) {S : List ℕ} (hS : S.Nodup) (hSk : ∀ j ∈ S, j < cs.length) :
    Desc m t cs.length
      (withPiece (setOf m V₁ \ setOf m V₁') (shrink (famOf m cs) (recB t (famOf m cs))
        (setOf m V₁') (pickSide (setOf m V₁') (famOf m cs) (cellsOf m cs S) (relOf m cs a))
        (relOf m cs a)))
      [shrinkI cs.length V₁' (subCells cs (pickSideD V₁' cs.length a S))
        (restrictRel m cs.length a (pickSideD V₁' cs.length a S)) [pieceOp (diffD V₁ V₁')]] 0 := by
  obtain ⟨hn, hl⟩ := pickSideD_spec (ps := V₁') a hS hSk
  rw [← pickSide_decode hps hpn hcs a hSk, ← famOf_subCells, ← setOf_diffD, withPiece_eq_wrapT]
  exact desc_shrinkI (card_famOf (getD_inj_of_nodup hcs)) hpn hps (nodup_subCells hcs hn hl)
    (fun x s hs => relOf_restrict hcs hn hl x hs) _

/-- The same with `bsoj`'s guard only. -/
theorem desc_pickRec (hcs : (cs.map (setOf m)).Nodup) {V₁ V₁' : List ℕ} (hpn : V₁'.Nodup)
    (hps : ∀ x ∈ V₁', x < m) {S : List ℕ} (hS : S.Nodup) (hSk : ∀ j ∈ S, j < cs.length) :
    Desc m t cs.length
      (withPiece (setOf m V₁ \ setOf m V₁') (recB t (famOf m cs)
        (setOf m V₁') (pickSide (setOf m V₁') (famOf m cs) (cellsOf m cs S) (relOf m cs a))
        (relOf m cs a)))
      [recI cs.length V₁' (subCells cs (pickSideD V₁' cs.length a S))
        (restrictRel m cs.length a (pickSideD V₁' cs.length a S)) [pieceOp (diffD V₁ V₁')]] 0 := by
  obtain ⟨hn, hl⟩ := pickSideD_spec (ps := V₁') a hS hSk
  rw [← pickSide_decode hps hpn hcs a hSk, ← famOf_subCells, ← setOf_diffD, withPiece_eq_wrapT]
  exact desc_recI (card_famOf (getD_inj_of_nodup hcs)) hpn hps (nodup_subCells hcs hn hl)
    (fun x s hs => relOf_restrict hcs hn hl x hs) _

end Restrict


/-! ### The refined colouring on all points and cells -/

section CQ

variable {m : ℕ} {cs : List (List ℕ)} {a : Array Bool}

theorem enc_two {N : ℕ} (i j : Fin N) : enc ![i, j] = i.val + j.val * N := by
  rw [enc_eq_sum, Fin.sum_univ_two]
  simp

theorem idxQ_some {ps : List ℕ} (hps : ∀ i ∈ ps, i < m) (hcs : (cs.map (setOf m)).Nodup)
    {u : Fin (m + cs.length)} {i : ℕ} (h : idxQ m ps cs.length u = some i) :
    ∃ hi : i < ps.length + cs.length, (sqAt m ps cs hps ⟨i, hi⟩).val = eQ hcs u := by
  unfold idxQ at h
  split_ifs at h with h1 h2 h3
  · cases h
    have hlt : ps.idxOf u.val < ps.length := List.idxOf_lt_length_iff.2 h2
    refine ⟨by omega, ?_⟩
    rw [sqAt_lt (show ps.idxOf u.val < ps.length from hlt), eQ_apply, eQf, dite_eq_left h1]
    congr 1
    exact Fin.ext (List.getElem_idxOf hlt)
  · cases h
    refine ⟨by omega, ?_⟩
    rw [sqAt_ge (show ps.length ≤ ps.length + (u.val - m) by omega), eQ_apply, eQf,
      dite_eq_right h1]
    congr 1
    rw [cellAt]
    simp [List.getD_eq_getElem?_getD, show u.val - m < cs.length by omega]

theorem idxQ_none {ps : List ℕ} (hcs : (cs.map (setOf m)).Nodup) {u : Fin (m + cs.length)}
    (h : idxQ m ps cs.length u = none) :
    eQ hcs u ∉ (setOf m ps).disjSum (famOf m cs) := by
  unfold idxQ at h
  split_ifs at h with h1 h2 h3
  · rw [eQ_apply, eQf, dite_eq_left h1, Finset.inl_mem_disjSum, mem_setOf]
    exact h2
  · exact absurd u.2 h3

/-- **`cQd` reads the classical refinement of `dlCont`** on all points and cells. -/
theorem cQd_spec (hcs : (cs.map (setOf m)).Nodup) {ps : List ℕ} (hps : ∀ i ∈ ps, i < m)
    (hpn : ps.Nodup) {Y : ↥(famOf m cs) → ↥(famOf m cs) → ℕ} {Ydat : Array ℕ}
    (hY : ∀ i j : Fin cs.length,
      Y (cellSub m cs i) (cellSub m cs j) = get Ydat (i + j * cs.length))
    (u v : Fin (m + cs.length)) :
    cQd m ps cs.length (wlA 2 (ps.length + cs.length) (sqCodeArr ps cs.length a Ydat)).1 u v =
      cohOn ((setOf m ps).disjSum (famOf m cs)) (code (relOf m cs a) (extCells (famOf m cs) Y))
        (eQ hcs u) (eQ hcs v) := by
  unfold cQd
  rcases hu : idxQ m ps cs.length u with _ | i
  · simp only
    unfold cohOn
    rw [dite_eq_right fun h => idxQ_none hcs hu h.1]
  rcases hv : idxQ m ps cs.length v with _ | j
  · simp only
    unfold cohOn
    rw [dite_eq_right fun h => idxQ_none hcs hv h.2]
  simp only
  obtain ⟨hi, hsi⟩ := idxQ_some hps hcs hu
  obtain ⟨hj, hsj⟩ := idxQ_some hps hcs hv
  rw [← hsi, ← hsj, show (setOf m ps).disjSum (famOf m cs) = sqSet m ps cs from rfl,
    cohOn_code_eq hps hpn hcs a hY ⟨i, hi⟩ ⟨j, hj⟩, enc_two]

end CQ


/-! ### `dlCont` on data -/

section DL

variable {m t : ℕ} {cs : List (List ℕ)} {a : Array Bool}

theorem coe_cellSub_eq (j : Fin cs.length) :
    (cellSub m cs j : Finset (Fin m)) = cellAt m cs j := by
  simp [cellSub, cellAt, List.getD_eq_getElem?_getD]

theorem decList_spec {V : Type*} {v : ℕ} (e : V ≃ Fin v) {xd : List ℕ}
    (hxd : ∀ i ∈ xd, i < v) :
    ((decList e xd).map e).map Fin.val = xd ∧ ((decList e xd).map e).length = xd.length := by
  have hx : xd = (xd.pmap (fun i h => (⟨i, h⟩ : Fin v)) hxd).map Fin.val := by
    simp [List.map_pmap]
  have h := decList_map_val e (xd.pmap (fun i h => (⟨i, h⟩ : Fin v)) hxd)
  rw [← hx] at h
  rw [h, List.map_map, List.map_map]
  simp only [Function.comp_def, Equiv.apply_symm_apply]
  exact ⟨hx.symm, by simp⟩

theorem selThirdL_sublist (S : List ℕ) (col : ℕ → ℕ) : (selThirdL S col).Sublist S := by
  unfold selThirdL
  dsimp only
  split <;> exact List.filter_sublist

theorem famOf_range (cs : List (List ℕ)) :
    ((List.range cs.length).map (cellAt m cs)).toFinset = famOf m cs := by
  rw [famOf_eq_image]
  ext s
  simp

theorem decOK_cells (hcs : (cs.map (setOf m)).Nodup) {col : ℕ → ℕ} {g : Finset (Fin m) → ℕ}
    (hg : ∀ j < cs.length, g (cellAt m cs j) = col j) :
    DecOK (List.range cs.length) (cellAt m cs) col g :=
  ⟨List.nodup_range, fun i hi j hj h => getD_inj_of_nodup hcs i (List.mem_range.1 hi) j
    (List.mem_range.1 hj) h, fun i hi => hg i (List.mem_range.1 hi)⟩

theorem cellsOf_eq (cs : List (List ℕ)) (js : List ℕ) :
    cellsOf m cs js = (js.map (cellAt m cs)).toFinset := rfl

theorem setOf_bigL {ps : List ℕ} (hpn : ps.Nodup) (hps : ∀ x ∈ ps, x < m) {col : ℕ → ℕ}
    {colF : Fin m → ℕ} (hcol : ∀ y : Fin m, colF y = col y.val) (t : ℕ) :
    setOf m (bigL ps col t) =
      (setOf m ps).filter fun y => t < ((setOf m ps).filter fun y' => colF y' = colF y).card := by
  ext y
  rw [mem_setOf, bigL, List.mem_filter, Finset.mem_filter, mem_setOf]
  have hc : ((setOf m ps).filter fun y' => colF y' = colF y).card = clsCount ps col y.val := by
    have := card_filter_setOf (m := m) hpn hps (fun z => decide (col z = col y.val))
    simp only [decide_eq_true_eq] at this
    rw [clsCount, ← this]
    congr 1
    refine Finset.filter_congr fun z _ => ?_
    rw [hcol, hcol]
  rw [hc]
  simp

theorem setOf_eq_empty_iff {l : List ℕ} (hl : ∀ x ∈ l, x < m) : setOf m l = ∅ ↔ l = [] := by
  constructor
  · intro h
    rcases l with _ | ⟨x, l⟩
    · rfl
    · have : (⟨x, hl x List.mem_cons_self⟩ : Fin m) ∈ setOf m (x :: l) :=
        mem_setOf.2 List.mem_cons_self
      rw [h] at this
      exact absurd this (Finset.notMem_empty _)
  · rintro rfl
    ext y
    simp [mem_setOf]

theorem cellsOf_compl' (hcs : (cs.map (setOf m)).Nodup) {C₂ : List ℕ}
    (hC₂ : ∀ j ∈ C₂, j < cs.length) :
    famOf m cs \ cellsOf m cs C₂ = famOf m (subCells cs ((List.range cs.length).filter
      fun j => j ∉ C₂)) := by
  rw [famOf_subCells]
  ext s
  rw [Finset.mem_sdiff, ← famOf_range, cellsOf_eq, cellsOf_eq, List.mem_toFinset,
    List.mem_toFinset, List.mem_toFinset, List.mem_map, List.mem_map, List.mem_map]
  constructor
  · rintro ⟨⟨j, hj, rfl⟩, hn⟩
    refine ⟨j, List.mem_filter.2 ⟨hj, ?_⟩, rfl⟩
    simp only [decide_eq_true_eq]
    exact fun hjC => hn ⟨j, hjC, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    obtain ⟨hjr, hjn⟩ := List.mem_filter.1 hj
    simp only [decide_eq_true_eq] at hjn
    refine ⟨⟨j, hjr, rfl⟩, ?_⟩
    rintro ⟨j', hj', he⟩
    have := getD_inj_of_nodup hcs j' (hC₂ j' hj') j (List.mem_range.1 hjr) he
    exact hjn (this ▸ hj')

theorem rect_iff {C₁ C₂ : List ℕ} (hC₁ : ∀ y ∈ C₁, y < m) (hC₂ : ∀ j ∈ C₂, j < cs.length)
    {F : Fin m → Finset (Fin m) → ℕ} {fd : ℕ → ℕ → ℕ}
    (hF : ∀ y : Fin m, ∀ j < cs.length, fd y j = F y (cellAt m cs j)) :
    (∀ y ∈ setOf m C₁, ∀ s ∈ cellsOf m cs C₂, ∀ y' ∈ setOf m C₁, ∀ s' ∈ cellsOf m cs C₂,
      F y s = F y' s') ↔ constRectL C₁ C₂ fd = true := by
  rw [constRectL_iff (C₁ := C₁) (C₂ := C₂) (dec₁ := id) (dec₂ := id) (f := fd) (F := fd)
    fun _ _ _ _ => rfl]
  simp only [List.map_id]
  constructor
  · intro h y hy j hj y' hy' j' hj'
    rw [hF ⟨y, hC₁ y hy⟩ j (hC₂ j hj), hF ⟨y', hC₁ y' hy'⟩ j' (hC₂ j' hj')]
    exact h _ (mem_setOf.2 hy) _ (List.mem_toFinset.2 (List.mem_map.2 ⟨j, hj, rfl⟩)) _
      (mem_setOf.2 hy') _ (List.mem_toFinset.2 (List.mem_map.2 ⟨j', hj', rfl⟩))
  · intro h y hy s hs y' hy' s' hs'
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hs)
    obtain ⟨j', hj', rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hs')
    have e1 := hF y j (hC₂ j hj)
    have e2 := hF y' j' (hC₂ j' hj')
    rw [cellAt] at e1 e2
    rw [← e1, ← e2]
    exact h _ (mem_setOf.1 hy) _ hj _ (mem_setOf.1 hy') _ hj'

theorem eQ_cell (hcs : (cs.map (setOf m)).Nodup) {j : ℕ} (hj : j < cs.length) :
    eQ hcs ⟨m + j, by omega⟩ = .inr (cellAt m cs j) := by
  rw [eQ_eq_inr_iff]
  exact ⟨Nat.le_add_right m j, by simp⟩

theorem get_toArray_eq (l : List ℕ) (i : ℕ) : get l.toArray i = l.getD i 0 := by
  simp [get, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

theorem get_map_range {n : ℕ} (g : ℕ → ℕ) {i : ℕ} (hi : i < n) :
    get ((List.range n).map g).toArray i = g i := by
  rw [get_toArray_eq, List.getD_eq_getElem _ _ (by simpa using hi)]
  simp

theorem get_flatMap_range {n n' : ℕ} (g : ℕ → ℕ → ℕ) {u v : ℕ} (hu : u < n) (hv : v < n') :
    get ((List.range n).flatMap fun u => (List.range n').map (g u)).toArray (u * n' + v) =
      g u v := by
  rw [get_toArray_eq, getD_flatMap_const _ n' 0 (List.range n) (fun _ _ => by simp) u
    (by simpa using hu) v hv]
  simp [hv]

theorem fA_cQArr {ps : List ℕ} {k : ℕ} {W2 : Array ℕ} (u v : Fin (m + k)) :
    fA (offsArr (m + k)) (cQArr m ps k W2) u v = cQd m ps k W2 u v := by
  rw [fA_offsArr, colOf, cQArr, get_flatMap_range _ u.2 v.2]

theorem get2_rectArr {k : ℕ} (f : ℕ → ℕ → ℕ) {y j : ℕ} (hy : y < m) (hj : j < k) :
    get2 (rectArr m k f) y j = f y (m + j) := by
  simp [get2, rectArr, Array.getD_eq_getD_getElem?, hy, hj]

theorem skelArrD_get (wl : Array ℕ) (d : ℕ) (xd : List ℕ) {i j : ℕ} (hi : i < cs.length)
    (hj : j < cs.length) :
    get (skelArrD wl d cs.length xd) (i + j * cs.length) =
      get wl (codePad2 (pwTab d cs.length) d xd.length xd.toArray i j) := by
  rw [skelArrD, Nat.add_comm, get_flatMap_range (fun j i =>
    get wl (codePad2 (pwTab d cs.length) d xd.length xd.toArray i j)) hj hi]

theorem desc_dlI (hcs : (cs.map (setOf m)).Nodup) (V₁ : List ℕ) {V₁' : List ℕ}
    (hpn : V₁'.Nodup) (hps : ∀ x ∈ V₁', x < m) {d : ℕ} (wl : Array ℕ) {xd : List ℕ}
    (hxd : ∀ i ∈ xd, i < cs.length) (e : ↥(famOf m cs) ≃ Fin cs.length)
    (he : ∀ j, e (cellSub m cs j) = j) :
    Desc m t cs.length
      (dlCont t (setOf m V₁) (setOf m V₁') (famOf m cs) (relOf m cs a)
        (fun y : Fin d → ↥(famOf m cs) => toFun wl (⇑e ∘ y))
        (recB t (famOf m cs)) (decList e xd))
      (dlI m t V₁ V₁' cs a d wl xd).1 (dlI m t V₁ V₁' cs a d wl xd).2 := by
  obtain ⟨hxv, hxl⟩ := decList_spec e hxd
  have hk : (famOf m cs).card = cs.length := card_famOf (getD_inj_of_nodup hcs)
  have hcol1 := domA_eq_none_iff (d := d) e wl (decList e xd) (2 * cs.length / 3)
  rw [hxl, hxv] at hcol1
  have hsk : ∀ u, skel1 (fun y : Fin d → ↥(famOf m cs) => toFun wl (⇑e ∘ y)) (decList e xd) u =
      (col1A wl (pwTab d cs.length) d cs.length xd.length xd.toArray).getD (e u) 0 := by
    intro u
    rw [skel1_eq_getD_col1A, hxl, hxv]
  have hY : ∀ i j : Fin cs.length,
      skel2 (fun y : Fin d → ↥(famOf m cs) => toFun wl (⇑e ∘ y)) (decList e xd)
        (cellSub m cs i) (cellSub m cs j) =
          get (skelArrD wl d cs.length xd) (i + j * cs.length) := by
    intro i j
    rw [skel2_comp_equiv, he, he, skelArrD_get wl d xd i.2 j.2, skel2, toFun,
      ← codePad2_eq, hxl, hxv]
  have hf := cQd_spec hcs hps hpn (a := a) hY
  unfold dlCont dlI
  dsimp only
  rw [hk]
  generalize col1A wl (pwTab d cs.length) d cs.length xd.length xd.toArray = col1 at hcol1 hsk ⊢
  rcases hdom : domA col1 (2 * cs.length / 3) with _ | u₀
  · rw [ite_eq_left (hcol1.2 hdom)]
    have hD : DecOK (List.range cs.length) (cellAt m cs) (get col1.toArray)
        (fun s => if h : s ∈ famOf m cs then col1.getD (e ⟨s, h⟩) 0 else 0) := by
      refine decOK_cells hcs fun j hj => ?_
      have hm : cellAt m cs j ∈ famOf m cs := by
        rw [famOf_eq_image]
        exact Finset.mem_image_of_mem _ (Finset.mem_range.2 hj)
      rw [dite_eq_left hm]
      have : (⟨cellAt m cs j, hm⟩ : ↥(famOf m cs)) = cellSub m cs ⟨j, hj⟩ :=
        Subtype.ext (coe_cellSub_eq ⟨j, hj⟩).symm
      rw [this, he, get_toArray_eq]
    have hsel : (selThird univ (skel1 (fun y : Fin d → ↥(famOf m cs) => toFun wl (⇑e ∘ y))
        (decList e xd))).map (Function.Embedding.subtype _) =
        cellsOf m cs (selThirdL (List.range cs.length) (get col1.toArray)) := by
      rw [← BipRelabel.selThird_map univ _
          (fun s => if h : s ∈ famOf m cs then col1.getD (e ⟨s, h⟩) 0 else 0)
          (Function.Embedding.subtype _) fun u => by
            rw [Function.Embedding.subtype_apply, dite_eq_left u.2, hsk],
        univ_eq_attach, attach_map_val, cellsOf_eq, selThirdL_decode hD, famOf_range]
    rw [hsel]
    exact desc_pick hcs hpn hps ((List.nodup_range).sublist (selThirdL_sublist _ _))
      fun j hj => List.mem_range.1 ((selThirdL_sublist _ _).subset hj)
  · rw [ite_eq_right fun h => by rw [hcol1.1 h] at hdom; cases hdom]
    dsimp only
    have hf' : ∀ u v : Fin (m + cs.length), fA (offsArr (m + cs.length))
        (cQArr m V₁' cs.length (wlA 2 (V₁'.length + cs.length)
          (sqCodeArr V₁' cs.length a (skelArrD wl d cs.length xd))).1) u v =
        cohOn ((setOf m V₁').disjSum (famOf m cs)) (code (relOf m cs a)
          (extCells (famOf m cs) (skel2 (fun y : Fin d → ↥(famOf m cs) => toFun wl (⇑e ∘ y))
            (decList e xd)))) (eQ hcs u) (eQ hcs v) := fun u v => by
      rw [fA_cQArr, hf]
    clear hf
    generalize cohOn ((setOf m V₁').disjSum (famOf m cs)) (code (relOf m cs a)
      (extCells (famOf m cs) (skel2 (fun y : Fin d → ↥(famOf m cs) => toFun wl (⇑e ∘ y))
        (decList e xd)))) = cQ at hf' ⊢
    generalize fA (offsArr (m + cs.length)) (cQArr m V₁' cs.length (wlA 2
      (V₁'.length + cs.length) (sqCodeArr V₁' cs.length a (skelArrD wl d cs.length xd))).1)
      = f at hf' ⊢
    have hc₁ : ∀ y : Fin m, cQ (.inl y) (.inl y) = f y y := fun y => by
      have := hf' ⟨y.val, by omega⟩ ⟨y.val, by omega⟩
      rw [eQ_inl hcs y] at this
      exact this.symm
    have hcr : ∀ y : Fin m, ∀ j < cs.length,
        get2 (rectArr m cs.length f) y j = cQ (.inl y) (.inr (cellAt m cs j)) :=
      fun y j hj => by
        have := hf' ⟨y.val, by omega⟩ ⟨m + j, by omega⟩
        rw [eQ_inl hcs y, eQ_cell hcs hj] at this
        rw [get2_rectArr f y.2 hj]
        exact this
    generalize hcol₂ : ((List.range cs.length).map fun j => f (m + j) (m + j)).toArray = col₂
    have hc₂ : ∀ j < cs.length,
        cQ (.inr (cellAt m cs j)) (.inr (cellAt m cs j)) = get col₂ j := fun j hj => by
      have := hf' ⟨m + j, by omega⟩ ⟨m + j, by omega⟩
      rw [eQ_cell hcs hj] at this
      rw [← hcol₂, get_map_range _ hj]
      exact this.symm
    generalize hcolP : ((List.range m).map fun y => f y y).toArray = colP
    have hcP : ∀ y : Fin m, cQ (.inl y) (.inl y) = get colP y := fun y => by
      rw [← hcolP, get_map_range _ y.2, hc₁]
    have hD2 : DecOK (List.range cs.length) (cellAt m cs) (get col₂)
        (fun s => cQ (.inr s) (.inr s)) := decOK_cells hcs hc₂
    have hA2 := allSmallL_iff hD2 (2 * cs.length / 3)
    rw [famOf_range] at hA2
    by_cases h2 : allSmallL (List.range cs.length) (get col₂) (2 * cs.length / 3) = true
    · rw [ite_eq_left (hA2.1 h2), ite_eq_left h2]
      have hsel := selThirdL_decode hD2
      rw [famOf_range] at hsel
      rw [← hsel, ← cellsOf_eq]
      exact desc_pick hcs hpn hps ((List.nodup_range).sublist (selThirdL_sublist _ _))
        fun j hj => List.mem_range.1 ((selThirdL_sublist _ _).subset hj)
    · rw [ite_eq_right fun h => h2 (hA2.2 h), ite_eq_right h2]
      have hb2 := bigL_decode hD2 (2 * cs.length / 3)
      rw [famOf_range] at hb2
      rw [← hb2, ← cellsOf_eq]
      have hb1 := setOf_bigL hpn hps (colF := fun y => cQ (.inl y) (.inl y))
        (col := get colP) hcP t
      rw [← hb1]
      have hC₁n : (bigL V₁' (get colP) t).Nodup := hpn.filter _
      have hC₁m : ∀ y ∈ bigL V₁' (get colP) t, y < m :=
        fun y hy => hps y (List.mem_of_mem_filter hy)
      have hC₂n : (bigL (List.range cs.length) (get col₂) (2 * cs.length / 3)).Nodup :=
        List.nodup_range.filter _
      have hC₂k : ∀ j ∈ bigL (List.range cs.length) (get col₂) (2 * cs.length / 3),
          j < cs.length :=
        fun j hj => List.mem_range.1 (List.mem_of_mem_filter hj)
      generalize bigL V₁' (get colP) t = C₁ at hC₁n hC₁m ⊢
      generalize bigL (List.range cs.length) (get col₂) (2 * cs.length / 3) = C₂ at hC₂n hC₂k ⊢
      by_cases h3 : C₁ = []
      · rw [ite_eq_left ((setOf_eq_empty_iff hC₁m).2 h3), ite_eq_left h3]
        have hcol : (fun x : Fin m => get colP x.val) = fun y => cQ (.inl y) (.inl y) := by
          funext y
          rw [hcP]
        have := desc_leaf (m := m) (t := t) (k := cs.length) (addPieceD m (diffD V₁ V₁')
          (partD colP (colBlkD m V₁' colP)))
        rwa [decodeOut_addPieceD, decodeOut_partD, colPart_decode, setOf_diffD, hcol] at this
      · rw [ite_eq_right fun h => h3 ((setOf_eq_empty_iff hC₁m).1 h), ite_eq_right h3]
        have hR := rect_iff (cs := cs) hC₁m hC₂k (F := fun y s => cQ (.inl y) (.inr s))
          (fd := get2 (rectArr m cs.length f)) hcr
        by_cases h4 : constRectL C₁ C₂ (get2 (rectArr m cs.length f)) = true
        · simp only [hR, h4, ite_true]
          rw [cellsOf_compl' hcs hC₂k, ← setOf_diffD, withPiece_eq_wrapT]
          have hjn : ((List.range cs.length).filter fun j => j ∉ C₂).Nodup :=
            List.nodup_range.filter _
          have hjk : ∀ j ∈ (List.range cs.length).filter (fun j => j ∉ C₂), j < cs.length :=
            fun j hj => List.mem_range.1 (List.mem_of_mem_filter hj)
          exact desc_shrinkI hk hpn hps (nodup_subCells hcs hjn hjk)
            (fun x s hs => relOf_restrict hcs hjn hjk x hs) _
        · simp only [hR, h4, Bool.false_eq_true, ite_false]
          exact desc_cohI hcs hf' V₁ V₁' C₁ C₂ hC₁n hC₁m hC₂n hC₂k

end DL


/-! ### One level of `bsoj` on data -/

section Level

variable {m t : ℕ} {cs : List (List ℕ)} {a : Array Bool}

theorem nodup_tupList (l v : ℕ) : (tupList l v).Nodup := by
  rw [tupList_eq]
  refine List.nodup_range.map_on fun s hs s' hs' h => ?_
  have hlt := List.mem_range.1 hs
  have hlt' := List.mem_range.1 hs'
  have e1 : digitsOf l v s = digits (finFunctionFinEquiv.symm ⟨s, hlt⟩ : Tup l v) := by
    rw [← digitsOf_enc]
    simp [enc]
  have e2 : digitsOf l v s' = digits (finFunctionFinEquiv.symm ⟨s', hlt'⟩ : Tup l v) := by
    rw [← digitsOf_enc]
    simp [enc]
  rw [e1, e2] at h
  have hy : (finFunctionFinEquiv.symm ⟨s, hlt⟩ : Tup l v) =
      finFunctionFinEquiv.symm ⟨s', hlt'⟩ := by
    funext j
    have := congrArg (fun l => l.getD j.val 0) h
    simp only [digits, List.getD_eq_getElem?_getD, List.getElem?_ofFn] at this
    simp only [Fin.is_lt, Option.getD_some, dite_true] at this
    exact Fin.ext (by simpa using this)
  have := congrArg (fun y => (finFunctionFinEquiv y : ℕ)) hy
  simpa using this

theorem nodup_cands (k v : ℕ) : (cands k v).Nodup := by
  unfold cands
  rw [List.nodup_flatMap]
  refine ⟨fun l _ => nodup_tupList l v, ?_⟩
  refine List.nodup_range.pairwise_of_forall_ne fun l _ l' _ hne => ?_
  rw [Function.onFun, List.disjoint_left]
  intro x hx hx'
  rw [tupList_eq] at hx hx'
  obtain ⟨s, -, rfl⟩ := List.mem_map.1 hx
  obtain ⟨s', -, he⟩ := List.mem_map.1 hx'
  have := congrArg List.length he
  rw [length_digitsOf, length_digitsOf] at this
  exact hne this.symm

theorem choiceOf_injOn (hcs : (cs.map (setOf m)).Nodup) {js js' : List ℕ}
    (hjs : ∀ j ∈ js, j < cs.length) (hjs' : ∀ j ∈ js', j < cs.length)
    (h : choiceOf m cs js = choiceOf m cs js') : js = js' := by
  have key : ∀ l : List ℕ, (∀ j ∈ l, j < cs.length) →
      (choiceCells (choiceOf m cs l)).map (cellIdx m cs) = l := by
    intro l hl
    rw [choiceCells_choiceOf, List.map_map]
    conv_rhs => rw [← List.map_id l]
    exact List.map_congr_left fun j hj => cellIdx_cellAt (getD_inj_of_nodup hcs) (hl j hj)
  rw [← key js hjs, ← key js' hjs', h]

theorem nodup_permutations'_range (k : ℕ) : ((List.range k).permutations').Nodup :=
  (List.permutations_perm_permutations' _).nodup_iff.1
    (List.nodup_permutations _ List.nodup_range)

theorem mem_permutations'_range {k : ℕ} {js : List ℕ} (h : js ∈ (List.range k).permutations') :
    ∀ j ∈ js, j < k := fun _ hj =>
  List.mem_range.1 ((List.mem_permutations'.1 h).subset hj)

theorem cellsOf_nonempty_iff (l : List ℕ) : (cellsOf m cs l).Nonempty ↔ l ≠ [] := by
  rw [cellsOf, Finset.nonempty_iff_ne_empty, Ne, List.toFinset_eq_empty_iff, List.map_eq_nil_iff]

/-- The hyperedges of `daryCol`, on data. -/
theorem image_fOf_eq (hcs : (cs.map (setOf m)).Nodup) {V₁ : List ℕ} (hV₁ : V₁.Nodup)
    (hV₁m : ∀ x ∈ V₁, x < m) (d₁ : ℕ) :
    (tfDeg (setOf m V₁) (famOf m cs) (relOf m cs a) d₁).image
        (fOf (famOf m cs) (relOf m cs a) d₁) =
      (((tfDegD V₁ cs.length a d₁).map (fOfD cs.length a d₁)).map (cellsOf m cs)).toFinset := by
  rw [tfDeg_decode hV₁ hV₁m (getD_inj_of_nodup hcs)]
  ext s
  rw [Finset.mem_image, List.mem_toFinset, List.map_map, List.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.val, mem_setOf.1 hx, ?_⟩
    rw [fOf_decode (getD_inj_of_nodup hcs)]
    rfl
  · rintro ⟨x, hx, rfl⟩
    have hxm : x < m := hV₁m x (List.mem_of_mem_filter hx)
    refine ⟨⟨x, hxm⟩, mem_setOf.2 hx, ?_⟩
    rw [fOf_decode (getD_inj_of_nodup hcs)]
    rfl

theorem nodup_hyper (hcs : (cs.map (setOf m)).Nodup) {V₁ : List ℕ} (hV₁ : V₁.Nodup)
    (hV₁m : ∀ x ∈ V₁, x < m) (d₁ : ℕ) :
    (((tfDegD V₁ cs.length a d₁).map (fOfD cs.length a d₁)).map (cellsOf m cs)).Nodup := by
  rw [List.map_map]
  refine (hV₁.filter _).map_on fun x hx y hy h => ?_
  have hxm : x < m := hV₁m x (List.mem_of_mem_filter hx)
  have hym : y < m := hV₁m y (List.mem_of_mem_filter hy)
  have hx' : (⟨x, hxm⟩ : Fin m) ∈ tfDeg (setOf m V₁) (famOf m cs) (relOf m cs a) d₁ := by
    rw [tfDeg_decode hV₁ hV₁m (getD_inj_of_nodup hcs)]
    exact mem_setOf.2 hx
  have hy' : (⟨y, hym⟩ : Fin m) ∈ tfDeg (setOf m V₁) (famOf m cs) (relOf m cs a) d₁ := by
    rw [tfDeg_decode hV₁ hV₁m (getD_inj_of_nodup hcs)]
    exact mem_setOf.2 hy
  have := fOf_injOn d₁ hx' hy' (by
    rw [fOf_decode (getD_inj_of_nodup hcs), fOf_decode (getD_inj_of_nodup hcs)]
    exact h)
  exact congrArg Fin.val this

theorem lt_of_mem_fOfD {d₁ x : ℕ} {j : ℕ} (hj : j ∈ fOfD cs.length a d₁ x) : j < cs.length := by
  unfold fOfD nbrD at hj
  split_ifs at hj <;> exact List.mem_range.1 (List.mem_of_mem_filter hj)

end Level


/-! ### One level, assembled -/

section Assemble

variable {m t : ℕ} {cs : List (List ℕ)} {a : Array Bool}

theorem flatMap_fst_map {β : Type*} (L : List β) (F : β → List Item × ℕ) :
    (L.map F).flatMap Prod.fst = L.flatMap fun c => (F c).1 := by
  induction L with
  | nil => rfl
  | cons c L ih => simp [ih]

theorem desc_bstepI (hcs : (cs.map (setOf m)).Nodup) {V₁ : List ℕ} (hV₁ : V₁.Nodup)
    (hV₁m : ∀ x ∈ V₁, x < m) :
    Desc m t cs.length (bstep t (setOf m V₁) (famOf m cs) (relOf m cs a) (recB t (famOf m cs)))
      (bstepI m t V₁ cs a).1 (bstepI m t V₁ cs a).2 := by
  have hcs' := getD_inj_of_nodup hcs
  have hk : (famOf m cs).card = cs.length := card_famOf hcs'
  have hmin := optMin_bigDegs (a := a) hV₁ hV₁m hcs' t
  unfold bstep bstepI
  dsimp only
  rcases hopt : optMin (bigDegsD t V₁ cs.length a) with _ | d₁
  · rw [hopt] at hmin
    have hne : ¬ (bigDegs t (setOf m V₁) (famOf m cs) (relOf m cs a)).Nonempty := by
      intro h
      rw [dite_eq_left h] at hmin
      cases hmin
    rw [dite_eq_right hne]
    have := desc_leaf (m := m) (t := t) (k := cs.length)
      (partD (twinColD m V₁ cs.length a) (twinBlkD m V₁ cs.length a))
    rwa [decodeOut_partD, twinPart_decode hV₁ hV₁m hcs'] at this
  rw [hopt] at hmin
  have hne : (bigDegs t (setOf m V₁) (famOf m cs) (relOf m cs a)).Nonempty := by
    by_contra h
    rw [dite_eq_right h] at hmin
    cases hmin
  rw [dite_eq_left hne] at hmin ⊢
  have hd : (bigDegs t (setOf m V₁) (famOf m cs) (relOf m cs a)).min' hne = d₁ :=
    (Option.some_injective _ hmin).symm
  rw [hd, hk, card_tfDeg hV₁ hV₁m hcs']
  dsimp only
  by_cases hJ : (tfDegD V₁ cs.length a d₁).length = cs.length.choose (sOf cs.length d₁)
  · rw [ite_eq_left hJ, ite_eq_left hJ]
    have hj := johnson_decode (a := a) hV₁ hV₁m hcs' d₁
    rw [hk] at hj
    have := desc_leaf (m := m) (t := t) (k := cs.length)
      (johnD (tfDegD V₁ cs.length a d₁) cs (sOf cs.length d₁) (fArrD m cs.length a d₁))
    rwa [decodeOut_johnD, hj] at this
  rw [ite_eq_right hJ, ite_eq_right hJ]
  by_cases hb : IsBase t cs.length
  · rw [ite_eq_left hb, ite_eq_left hb]
    refine desc_congr (desc_node (β := List ℕ) ((List.range cs.length).permutations')
      (choiceOf m cs) (enums_decode hcs').symm ?_
      (fun js => ([.inl (partD (nbrCodeArrD m cs.length a js)
        (colBlkD m V₁ (nbrCodeArrD m cs.length a js)))], 0)) fun js hjs => ?_) ?_ ?_
    · exact (nodup_permutations'_range _).map_on fun js h js' h' e =>
        choiceOf_injOn hcs (mem_permutations'_range h) (mem_permutations'_range h') e
    · have := desc_leaf (m := m) (t := t) (k := cs.length)
        (partD (nbrCodeArrD m cs.length a js) (colBlkD m V₁ (nbrCodeArrD m cs.length a js)))
      rwa [decodeOut_partD, baseLeaf_decode hcs' (mem_permutations'_range hjs)] at this
    · exact flatMap_singleton_eq _ _
    · simp
  rw [ite_eq_right hb, ite_eq_right hb, image_fOf_eq hcs hV₁ hV₁m d₁]
  have hlt : ∀ h ∈ (tfDegD V₁ cs.length a d₁).map (fOfD cs.length a d₁), ∀ j ∈ h,
      j < cs.length := by
    intro h hh j hj
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 hh
    exact lt_of_mem_fOfD hj
  have hnd := nodup_hyper (a := a) hcs hV₁ hV₁m d₁
  rw [← bigTwins_daryCol hcs hlt hnd, tfDeg_decode hV₁ hV₁m hcs']
  have hd1 : cs.length = 1 → arity cs.length (sOf cs.length d₁) (tfDegD V₁ cs.length a d₁).length
      = 0 := fun h => by rw [h, arity, Nat.clog_one_left]; simp
  generalize arity cs.length (sOf cs.length d₁) (tfDegD V₁ cs.length a d₁).length = d at hd1
  have hpn : (tfDegD V₁ cs.length a d₁).Nodup := hV₁.filter _
  have hps : ∀ x ∈ tfDegD V₁ cs.length a d₁, x < m :=
    fun x hx => hV₁m x (List.mem_of_mem_filter hx)
  by_cases hS : bigTwinsD cs.length d (daryArr cs.length d
      ((tfDegD V₁ cs.length a d₁).map (fOfD cs.length a d₁))) ≠ []
  · rw [ite_eq_left ((cellsOf_nonempty_iff _).2 hS), ite_eq_left hS]
    exact desc_pickRec hcs hpn hps (List.nodup_range.filter _)
      fun j hj => List.mem_range.1 (List.mem_of_mem_filter hj)
  rw [ite_eq_right (fun h => hS ((cellsOf_nonempty_iff _).1 h)), ite_eq_right hS]
  obtain ⟨e, he⟩ : ∃ e : ↥(famOf m cs) ≃ Fin cs.length, ∀ j, e (cellSub m cs j) = j :=
    ⟨(Equiv.ofBijective _ (cellSub_bijective hcs)).symm,
      fun j => (Equiv.ofBijective _ (cellSub_bijective hcs)).symm_apply_apply j⟩
  have hes : ∀ i, cellSub m cs (e i) = i := fun i => by
    obtain ⟨j, rfl⟩ := (cellSub_bijective hcs).2 i
    rw [he]
  generalize hwl : (wlA d cs.length (daryArr cs.length d
    ((tfDegD V₁ cs.length a d₁).map (fOfD cs.length a d₁)))).1 = wl
  have hW : wlOn d (daryCol (famOf m cs) ((((tfDegD V₁ cs.length a d₁).map
      (fOfD cs.length a d₁)).map (cellsOf m cs)).toFinset) d) =
      fun y => toFun wl (⇑e ∘ y) := by
    funext y
    have hy : cellSub m cs ∘ (⇑e ∘ y) = y := by
      funext i
      exact hes (y i)
    rw [← hy, ← wlOn_daryCol_eq hcs hlt hnd (⇑e ∘ y), hwl, hy]
    rfl
  rw [hW]
  have hset : ((tuplesLt univ d).filter (DLGood (fun y : Fin d → ↥(famOf m cs) =>
      toFun wl (⇑e ∘ y)) (2 * cs.length / 3))).image (fun x => (x.map fun u =>
        (Sum.inr u.val : Fin m ⊕ Finset (Fin m)) : Choice (Fin m))) =
      ((goodList wl d cs.length (2 * cs.length / 3)).map fun xd =>
        ((decList e xd).map fun u => (Sum.inr u.val : Fin m ⊕ Finset (Fin m)) :
          Choice (Fin m))).toFinset := by
    by_cases h1 : cs.length = 1
    · have h0 := hd1 h1
      subst h0
      have e1 : tuplesLt (univ : Finset ↥(famOf m cs)) 0 = ∅ := by simp [tuplesLt]
      have e2 : goodList wl 0 cs.length (2 * cs.length / 3) = [] := by simp [goodList, cands]
      rw [e1, e2, Finset.filter_empty]
      rfl
    · rw [← goodList_decode e wl (le_two_mul_two_mul_div_three h1)]
      ext ch
      constructor
      · intro h
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 h
        obtain ⟨xd, hxd, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hx)
        exact List.mem_toFinset.2 (List.mem_map.2 ⟨xd, hxd, rfl⟩)
      · intro h
        obtain ⟨xd, hxd, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 h)
        exact Finset.mem_image.2
          ⟨decList e xd, List.mem_toFinset.2 (List.mem_map.2 ⟨xd, hxd, rfl⟩), rfl⟩
  have hmem : ∀ xd ∈ goodList wl d cs.length (2 * cs.length / 3),
      ∃ x : List (Fin cs.length), x.length < d ∧ xd = x.map Fin.val :=
    fun xd hxd => mem_cands.1 (List.mem_of_mem_filter hxd)
  have hnodup : ((goodList wl d cs.length (2 * cs.length / 3)).map fun xd =>
      ((decList e xd).map fun u => (Sum.inr u.val : Fin m ⊕ Finset (Fin m)) :
        Choice (Fin m))).Nodup := by
    refine ((nodup_cands d cs.length).filter _).map_on fun xd hxd xd' hxd' h => ?_
    obtain ⟨x, -, rfl⟩ := hmem xd hxd
    obtain ⟨x', -, rfl⟩ := hmem xd' hxd'
    have h' : (decList e (x.map Fin.val)).map (fun u : ↥(famOf m cs) =>
        (Sum.inr u.val : Fin m ⊕ Finset (Fin m))) =
        (decList e (x'.map Fin.val)).map fun u : ↥(famOf m cs) =>
          (Sum.inr u.val : Fin m ⊕ Finset (Fin m)) := h
    rw [decList_map_val, decList_map_val, List.map_map, List.map_map] at h'
    have hinj : Function.Injective
        ((fun u : ↥(famOf m cs) => (Sum.inr u.val : Fin m ⊕ Finset (Fin m))) ∘ ⇑e.symm) :=
      fun i j hij => e.symm.injective (Subtype.ext (Sum.inr_injective hij))
    rw [(List.map_injective_iff.2 hinj) h']
  have hF : ∀ xd ∈ goodList wl d cs.length (2 * cs.length / 3),
      Desc m t cs.length (dlCont t (setOf m V₁) (setOf m (tfDegD V₁ cs.length a d₁))
        (famOf m cs) (relOf m cs a) (fun y : Fin d → ↥(famOf m cs) => toFun wl (⇑e ∘ y))
        (recB t (famOf m cs)) (decodeV₂ (famOf m cs) ((decList e xd).map fun u =>
          (Sum.inr u.val : Fin m ⊕ Finset (Fin m)))))
        (dlI m t V₁ (tfDegD V₁ cs.length a d₁) cs a d wl xd).1
        (dlI m t V₁ (tfDegD V₁ cs.length a d₁) cs a d wl xd).2 := by
    intro xd hxd
    rw [decodeV₂_map]
    obtain ⟨x, -, rfl⟩ := hmem xd hxd
    exact desc_dlI hcs V₁ hpn hps wl (fun i hi => by
      obtain ⟨j, -, rfl⟩ := List.mem_map.1 hi
      exact j.2) e he
  have key := desc_node (β := List ℕ) (goodList wl d cs.length (2 * cs.length / 3))
    (kk := fun ch => dlCont t (setOf m V₁) (setOf m (tfDegD V₁ cs.length a d₁)) (famOf m cs)
      (relOf m cs a) (fun y : Fin d → ↥(famOf m cs) => toFun wl (⇑e ∘ y)) (recB t (famOf m cs))
      (decodeV₂ (famOf m cs) ch))
    _ hset hnodup (dlI m t V₁ (tfDegD V₁ cs.length a d₁) cs a d wl) hF
  refine desc_congr key ?_ ?_
  · exact (flatMap_fst_map _ _).symm
  · rw [List.map_map]
    rfl

end Assemble


/-! ### The step of a frame -/

section Step

variable {m t : ℕ}

theorem items_ms (l : List Item) :
    (l.map (itemMs m t)).sum = ((l.filterMap Sum.getLeft?).map (decodeOut m) : Multiset _) +
      ((l.filterMap Sum.getRight?).map fun ch => (ch.tree m t).leafMs).sum := by
  induction l with
  | nil => simp
  | cons i l ih =>
    cases i with
    | inl o =>
      simp only [List.map_cons, List.sum_cons, ih, List.filterMap_cons, Sum.getLeft?_inl,
        Sum.getRight?_inl, itemMs]
      rw [← Multiset.cons_coe, ← add_assoc, Multiset.singleton_add]
    | inr fr =>
      simp only [List.map_cons, List.sum_cons, ih, List.filterMap_cons, Sum.getLeft?_inr,
        Sum.getRight?_inr, itemMs]
      abel

theorem items_size (l : List Item) :
    (l.map (itemSize m t)).sum = (l.filterMap Sum.getLeft?).length +
      ((l.filterMap Sum.getRight?).map fun ch => (ch.tree m t).size).sum := by
  induction l with
  | nil => simp
  | cons i l ih =>
    cases i with
    | inl o =>
      simp only [List.map_cons, List.sum_cons, ih, List.filterMap_cons, Sum.getLeft?_inl,
        Sum.getRight?_inl, itemSize, List.length_cons]
      omega
    | inr fr =>
      simp only [List.map_cons, List.sum_cons, ih, List.filterMap_cons, Sum.getLeft?_inr,
        Sum.getRight?_inr, itemSize]
      omega

theorem desc_frameLevel {fr : FrameD} (hfr : fr.Valid m) :
    Desc m t fr.cs.length (fr.tree m t) (stepI m t fr).1 (stepI m t fr).2 := by
  unfold FrameD.tree stepI
  rw [bsoj.eq_1]
  exact desc_wrapT fr.wr (desc_bstepI hfr.cells hfr.nodup hfr.lt)

/-- **The leaves of a frame** are the leaves its step produces plus the leaves of its child
frames. -/
theorem stepD_leafMs {fr : FrameD} (hfr : fr.Valid m) :
    (fr.tree m t).leafMs = ((stepD m t fr).1.map (decodeOut m) : Multiset _) +
      ((stepD m t fr).2.map fun ch => (ch.tree m t).leafMs).sum := by
  rw [(desc_frameLevel hfr).ms, items_ms]
  rfl

/-- **The child frames are valid and have fewer cells.** -/
theorem stepD_children {fr : FrameD} (hfr : fr.Valid m) :
    ∀ ch ∈ (stepD m t fr).2, ch.Valid m ∧ ch.cs.length < fr.cs.length := by
  intro ch hch
  have hch' : Sum.inr ch ∈ (stepI m t fr).1 := by
    obtain ⟨i, hi, he⟩ := List.mem_filterMap.1 hch
    cases i with
    | inl o => simp at he
    | inr fr' =>
      simp only [Sum.getRight?_inr, Option.some.injEq] at he
      exact he ▸ hi
  exact (desc_frameLevel (t := t) hfr).ok ch hch'

/-- **The work of a step, its leaves and its children fit in the frame's size.** -/
theorem stepD_size {fr : FrameD} (hfr : fr.Valid m) :
    stepWork m t fr + (stepD m t fr).1.length +
      ((stepD m t fr).2.map fun ch => (ch.tree m t).size).sum ≤ (fr.tree m t).size := by
  have h := (desc_frameLevel (t := t) hfr).size
  rw [items_size] at h
  unfold stepWork stepD
  dsimp only
  omega

end Step


/-! ### The frames of `sojAt` -/

section SojAt

variable {m t : ℕ}

/-- The colours `c x y` of the row of `x`, read from the `m × m` array `c`. -/
def rowD (m : ℕ) (c : Array ℕ) (x : ℕ) : Array ℕ :=
  ((List.range m).map fun y => get c (x * m + y)).toArray

/-- The points of colour classes of more than `t` points in the row of `x`. -/
def sojBigD (m t : ℕ) (c : Array ℕ) (x : ℕ) : List ℕ :=
  (List.range m).filter fun y =>
    decide (t < ((List.range m).filter fun z => get c (x * m + z) = get c (x * m + y)).length)

/-- The pairs of colours of `sojAt`, coded by `Nat.pair`. -/
def sojPairsD (m : ℕ) (c : Array ℕ) (x : ℕ) (big : List ℕ) : List ℕ :=
  big.flatMap fun y => ((List.range m).filter fun z =>
    decide (get c (x * m + z) ∉ big.map (fun y' => get c (x * m + y')) ∧
      get c (y * m + z) ∉ big.map (fun y' => get c (x * m + y')))).map fun z =>
    Nat.pair (get c (x * m + z)) (get c (y * m + z))

/-- The cells of the `bsoj` call of `sojAt`: the singletons of the points of colour `k₁`. -/
def sojCellsD (m : ℕ) (c : Array ℕ) (x k₁ : ℕ) : List (List ℕ) :=
  ((List.range m).filter fun y => get c (x * m + y) = k₁).map fun y => [y]

/-- The relation of the `bsoj` call of `sojAt`: a point and a cell are related by colour `k₂`. -/
def sojRelD (m : ℕ) (c : Array ℕ) (cells : List (List ℕ)) (k₂ : ℕ) : Array Bool :=
  ((List.range m).flatMap fun z => cells.map fun cell =>
    cell.any fun y => get c (z * m + y) == k₂).toArray

/-- **`sojAt` on data**: a leaf, or the frame of its `bsoj` call with the extension as
wrapper. -/
def sojAtD (m t : ℕ) (c : Array ℕ) (x : ℕ) : OutD ⊕ FrameD :=
  if sojBigD m t c x = [] then
    .inl (partD (rowD m c x) (colBlkD m (List.range m) (rowD m c x)))
  else
    match optMin (sojPairsD m c x (sojBigD m t c x)) with
    | none => .inl noneD
    | some p =>
      .inr (sojBigD m t c x, sojCellsD m c x (Nat.unpair p).1,
        sojRelD m c (sojCellsD m c x (Nat.unpair p).1) (Nat.unpair p).2,
        [(true, sojBigD m t c x, rowD m c x)])

theorem get_rowD (c : Array ℕ) (x : ℕ) (y : Fin m) :
    get (rowD m c x) y.val = get c (x * m + y.val) := by
  rw [rowD, get, Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
    List.getElem?_range y.2]
  rfl

theorem setOf_range : setOf m (List.range m) = univ := by
  ext y
  simp [mem_setOf, y.2]

theorem setOf_sojBigD (c : Array ℕ) {x : ℕ} (hx : x < m) :
    setOf m (sojBigD m t c x) = univ.filter fun y : Fin m =>
      t < (univ.filter fun z => colOf m c ⟨x, hx⟩ z = colOf m c ⟨x, hx⟩ y).card := by
  ext y
  rw [mem_setOf, sojBigD, List.mem_filter, Finset.mem_filter]
  have hc := card_filter_setOf (m := m) List.nodup_range (fun z hz => List.mem_range.1 hz)
    (fun z => decide (get c (x * m + z) = get c (x * m + y.val)))
  simp only [decide_eq_true_eq, setOf_range] at hc
  simp only [colOf, List.mem_range, y.2, true_and, decide_eq_true_eq, Finset.mem_univ]
  rw [← hc]
  exact Iff.rfl

theorem sojBigD_lt (c : Array ℕ) (x : ℕ) : ∀ y ∈ sojBigD m t c x, y < m :=
  fun _ hy => lt_of_mem_range_filter hy

theorem sojPairsD_eq (c : Array ℕ) {x : ℕ} (hx : x < m) :
    (sojPairsD m c x (sojBigD m t c x)).toFinset =
      let big := univ.filter fun y : Fin m =>
        t < (univ.filter fun z => colOf m c ⟨x, hx⟩ z = colOf m c ⟨x, hx⟩ y).card
      let aqua := big.image (colOf m c ⟨x, hx⟩)
      ((big ×ˢ univ).filter fun p =>
          colOf m c ⟨x, hx⟩ p.2 ∉ aqua ∧ colOf m c p.1 p.2 ∉ aqua).image
        fun p => Nat.pair (colOf m c ⟨x, hx⟩ p.2) (colOf m c p.1 p.2) := by
  rw [← setOf_sojBigD c hx]
  dsimp only
  have haq : ∀ v, v ∈ (setOf m (sojBigD m t c x)).image (colOf m c ⟨x, hx⟩) ↔
      v ∈ (sojBigD m t c x).map fun y' => get c (x * m + y') := by
    intro v
    rw [Finset.mem_image, List.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.val, mem_setOf.1 hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, sojBigD_lt c x y hy⟩, mem_setOf.2 hy, rfl⟩
  ext n
  rw [List.mem_toFinset, sojPairsD, List.mem_flatMap, Finset.mem_image]
  constructor
  · rintro ⟨y, hy, hn⟩
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hn
    obtain ⟨hzr, hzc⟩ := List.mem_filter.1 hz
    simp only [decide_eq_true_eq] at hzc
    refine ⟨(⟨y, sojBigD_lt c x y hy⟩, ⟨z, List.mem_range.1 hzr⟩), ?_, rfl⟩
    rw [Finset.mem_filter, Finset.mem_product, haq, haq]
    exact ⟨⟨mem_setOf.2 hy, Finset.mem_univ _⟩, hzc⟩
  · rintro ⟨⟨y, z⟩, hp, rfl⟩
    rw [Finset.mem_filter, Finset.mem_product, haq, haq] at hp
    refine ⟨y.val, mem_setOf.1 hp.1.1, List.mem_map.2 ⟨z.val, List.mem_filter.2
      ⟨List.mem_range.2 z.2, ?_⟩, rfl⟩⟩
    simp only [decide_eq_true_eq]
    exact hp.2

theorem famOf_sojCellsD (c : Array ℕ) {x : ℕ} (hx : x < m) (k₁ : ℕ) :
    famOf m (sojCellsD m c x k₁) =
      (univ.filter fun y : Fin m => colOf m c ⟨x, hx⟩ y = k₁).image singleton := by
  ext s
  rw [famOf, List.mem_toFinset, sojCellsD, List.map_map, List.mem_map, Finset.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hyr, hyc⟩ := List.mem_filter.1 hy
    simp only [decide_eq_true_eq] at hyc
    refine ⟨⟨y, List.mem_range.1 hyr⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, hyc⟩, ?_⟩
    ext z
    simp [mem_setOf, Fin.ext_iff]
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.val, List.mem_filter.2 ⟨List.mem_range.2 y.2, ?_⟩, ?_⟩
    · simp only [decide_eq_true_eq]
      exact (Finset.mem_filter.1 hy).2
    · ext z
      simp [mem_setOf, Fin.ext_iff]

theorem nodup_sojCellsD (c : Array ℕ) (x k₁ : ℕ) :
    ((sojCellsD m c x k₁).map (setOf m)).Nodup := by
  rw [sojCellsD, List.map_map]
  refine (List.nodup_range.filter _).map_on fun y hy y' hy' h => ?_
  have hy'm := lt_of_mem_range_filter hy'
  have : (⟨y', hy'm⟩ : Fin m) ∈ setOf m [y] := by
    rw [Function.comp_apply, Function.comp_apply] at h
    rw [h]
    exact mem_setOf.2 (List.mem_singleton_self _)
  rw [mem_setOf, List.mem_singleton] at this
  exact this.symm

theorem relOf_sojRelD (c : Array ℕ) (x k₁ k₂ : ℕ) (z : Fin m) {s : Finset (Fin m)}
    (hs : s ∈ famOf m (sojCellsD m c x k₁)) :
    (∃ y ∈ s, colOf m c z y = k₂) ↔
      relOf m (sojCellsD m c x k₁) (sojRelD m c (sojCellsD m c x k₁) k₂) z s = true := by
  have hnd := nodup_sojCellsD (m := m) c x k₁
  obtain ⟨l, hl, rfl⟩ := mem_famOf.1 hs
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hl
  have hget : (sojCellsD m c x k₁).getD j [] = (sojCellsD m c x k₁)[j] :=
    List.getD_eq_getElem _ _ hj
  rw [← hget, sojRelD, relOf_rows hnd _ (fun _ => List.length_map _) z hj,
    List.getD_eq_getElem (List.map _ _) false (by simpa using hj), List.getElem_map, hget]
  obtain ⟨y, hy, hyl⟩ := List.mem_map.1 (List.getElem_mem hj :
    (sojCellsD m c x k₁)[j] ∈ sojCellsD m c x k₁)
  rw [← hyl]
  have hym := lt_of_mem_range_filter hy
  rw [List.any_eq_true]
  constructor
  · rintro ⟨y', hy', he⟩
    rw [mem_setOf, List.mem_singleton] at hy'
    refine ⟨y, List.mem_singleton_self _, ?_⟩
    rw [colOf] at he
    rw [← hy']
    exact beq_iff_eq.2 he
  · rintro ⟨y', hy', he⟩
    rw [List.mem_singleton] at hy'
    subst hy'
    exact ⟨⟨y', hym⟩, mem_setOf.2 (List.mem_singleton_self _), by rw [colOf]; exact beq_iff_eq.1 he⟩

/-- **`sojAt` on data, the leaf case.** -/
theorem sojAtD_leaf (c : Array ℕ) {x : ℕ} (hx : x < m) {o : OutD}
    (h : sojAtD m t c x = .inl o) : sojAt (colOf m c) t ⟨x, hx⟩ = .leaf (decodeOut m o) := by
  unfold sojAtD at h
  unfold sojAt
  dsimp only
  rw [← setOf_sojBigD c hx]
  by_cases hb : sojBigD m t c x = []
  · rw [ite_eq_left hb] at h
    cases h
    rw [ite_eq_left ((setOf_eq_empty_iff (sojBigD_lt c x)).2 hb), decodeOut_partD,
      colPart_decode, setOf_range]
    congr 2
    rw [show (fun y : Fin m => get (rowD m c x) y.val) = colOf m c ⟨x, hx⟩ from
      funext fun y => by rw [get_rowD]; rfl]
  · rw [ite_eq_right hb] at h
    rw [ite_eq_right fun h' => hb ((setOf_eq_empty_iff (sojBigD_lt c x)).1 h')]
    have hp := sojPairsD_eq (t := t) c hx
    rw [← setOf_sojBigD c hx] at hp
    dsimp only at hp
    rw [← hp]
    rcases ho : optMin (sojPairsD m c x (sojBigD m t c x)) with _ | p
    · rw [ho] at h
      cases h
      rw [optMin_eq] at ho
      have hne : ¬ (sojPairsD m c x (sojBigD m t c x)).toFinset.Nonempty := by
        intro hne
        rw [dite_eq_left hne] at ho
        cases ho
      rw [dite_eq_right hne, decodeOut_noneD]
    · rw [ho] at h
      cases h

/-- **`sojAt` on data, the frame case**: the frame is valid and its tree equals `sojAt` on the
reachable branches. -/
theorem sojAtD_frame (c : Array ℕ) {x : ℕ} (hx : x < m) {fr : FrameD}
    (h : sojAtD m t c x = .inr fr) :
    fr.Valid m ∧ TEq (sojAt (colOf m c) t ⟨x, hx⟩) (fr.tree m t) := by
  unfold sojAtD at h
  by_cases hb : sojBigD m t c x = []
  · rw [ite_eq_left hb] at h
    cases h
  rw [ite_eq_right hb] at h
  rcases ho : optMin (sojPairsD m c x (sojBigD m t c x)) with _ | p
  · rw [ho] at h
    cases h
  rw [ho] at h
  cases h
  refine ⟨⟨List.nodup_range.filter _, sojBigD_lt c x, nodup_sojCellsD c x _⟩, ?_⟩
  unfold sojAt FrameD.tree
  simp only [FrameD.V₁, FrameD.cs, FrameD.a, FrameD.wr]
  rw [← setOf_sojBigD c hx]
  rw [ite_eq_right fun h' => hb ((setOf_eq_empty_iff (sojBigD_lt c x)).1 h')]
  have hp := sojPairsD_eq (t := t) c hx
  rw [← setOf_sojBigD c hx] at hp
  dsimp only at hp
  rw [← hp]
  rw [optMin_eq] at ho
  have hne : (sojPairsD m c x (sojBigD m t c x)).toFinset.Nonempty := by
    by_contra hne
    rw [dite_eq_right hne] at ho
    cases ho
  rw [dite_eq_left hne] at ho ⊢
  have hpe : (sojPairsD m c x (sojBigD m t c x)).toFinset.min' hne = p :=
    (Option.some_injective _ ho)
  rw [hpe, ← famOf_sojCellsD c hx]
  refine TEq.bind (fun o => ?_) (bsoj_congr t _ _ fun z s hs => by
    rw [Bool.eq_iff_iff, ← relOf_sojRelD c x _ _ z hs]
    simp only [decide_eq_true_eq])
  show TEq (CTree.leaf _) (CTree.leaf _)
  simp only [TEq, wrapOut, List.foldl_cons, List.foldl_nil, opOut, ite_true]
  congr 1
  funext y
  rw [get_rowD]
  rfl

theorem sojAtD_frame_leafMs (c : Array ℕ) {x : ℕ} (hx : x < m) {fr : FrameD}
    (h : sojAtD m t c x = .inr fr) :
    (sojAt (colOf m c) t ⟨x, hx⟩).leafMs = (fr.tree m t).leafMs :=
  (sojAtD_frame c hx h).2.leafMs_eq

theorem sojAtD_frame_size (c : Array ℕ) {x : ℕ} (hx : x < m) {fr : FrameD}
    (h : sojAtD m t c x = .inr fr) :
    (sojAt (colOf m c) t ⟨x, hx⟩).size = (fr.tree m t).size :=
  (sojAtD_frame c hx h).2.size_eq

end SojAt

end GraphIso.SoJTree
