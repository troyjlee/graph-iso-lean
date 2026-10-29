module

public import GraphIso.SplitJohnson.CoherentDef

/-!
# Relabelling lemmas

How the constructions of Split-or-Johnson move under a group `G` acting on the points:
filters, images and cardinalities of translated sets (`filter_smul_finset`,
`image_smul_finset`, `card_filter_smul_finset`), the off-diagonal colours and the components of
a colour graph (`offCols_smul`, `comp_smul`, `disconn_smul`), twin classes (`twinCls_smul`),
and the colour partitions and edge relations of `cohSoj` (`colPart_smul`, `bipEdge_smul`).
Relabelling a colouring of pairs is `relab2 g c x y = c (g⁻¹ • x) (g⁻¹ • y)`.
-/

@[expose] public section

namespace GraphIso.SplitJohnson

open Finset Pointwise GraphIso.Coherent

section Generic

variable {G X β : Type*} [Group G] [MulAction G X] [DecidableEq X]

theorem mem_smul_finset_iff_inv {g : G} {S : Finset X} {x : X} : x ∈ g • S ↔ g⁻¹ • x ∈ S :=
  inv_smul_mem_iff.symm

theorem filter_smul_finset (g : G) (S : Finset X) (p : X → Prop) [DecidablePred p] :
    (g • S).filter p = g • S.filter fun x => p (g • x) := by
  ext y
  simp only [mem_filter, mem_smul_finset_iff_inv, smul_inv_smul]

theorem image_smul_finset [DecidableEq β] (g : G) (S : Finset X) (f : X → β) :
    (g • S).image f = S.image fun x => f (g • x) := by
  rw [smul_finset_def, image_image]
  rfl

theorem card_filter_smul_finset (g : G) (S : Finset X) (p : X → Prop) [DecidablePred p] :
    ((g • S).filter p).card = (S.filter fun x => p (g • x)).card := by
  rw [filter_smul_finset, card_smul_finset]

theorem exists_mem_smul_finset {g : G} {S : Finset X} {p : X → Prop} :
    (∃ x ∈ g • S, p x) ↔ ∃ x ∈ S, p (g • x) := by
  constructor
  · rintro ⟨x, hx, h⟩
    exact ⟨g⁻¹ • x, mem_smul_finset_iff_inv.1 hx, by rwa [smul_inv_smul]⟩
  · rintro ⟨x, hx, h⟩
    exact ⟨g • x, smul_mem_smul_finset hx, h⟩

theorem forall_mem_smul_finset {g : G} {S : Finset X} {p : X → Prop} :
    (∀ x ∈ g • S, p x) ↔ ∀ x ∈ S, p (g • x) := by
  constructor
  · intro h x hx
    exact h _ (smul_mem_smul_finset hx)
  · intro h x hx
    have := h _ (mem_smul_finset_iff_inv.1 hx)
    rwa [smul_inv_smul] at this

/-- The image of a translate under singletons. -/
theorem image_singleton_smul_finset (g : G) (S : Finset X) :
    (g • S).image (singleton : X → Finset X) = g • S.image singleton := by
  rw [image_smul_finset, smul_finset_def, image_image]
  exact image_congr fun x _ => (smul_finset_singleton (a := g) x).symm

omit [MulAction G X] [DecidableEq X] in
/-- The image of `S` under `x ↦ g • f x`. -/
theorem image_smul_comp [DecidableEq β] [MulAction G β] (g : G) (S : Finset X) (f : X → β) :
    S.image (fun x => g • f x) = g • S.image f := by
  rw [smul_finset_def, image_image]
  rfl

/-- The minimum of equal nonempty sets. -/
theorem min'_congr {s t : Finset ℕ} (h : s = t) (hs : s.Nonempty) :
    s.min' hs = t.min' (h ▸ hs) := by
  subst h
  rfl

end Generic

section Classical

variable {R G : Type*} [DecidableEq R] [Group G] [MulAction G R]

omit [DecidableEq R] in
@[simp]
theorem relab2_smul (g : G) (c : R → R → ℕ) (x y : R) : relab2 g c (g • x) (g • y) = c x y := by
  simp [relab2]

theorem mem_offCols {S : Finset R} {c : R → R → ℕ} {k : ℕ} :
    k ∈ offCols S c ↔ ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ c x y = k := by
  simp only [offCols, mem_image, mem_filter, mem_product, Prod.exists]
  constructor
  · rintro ⟨x, y, ⟨⟨hx, hy⟩, hxy⟩, rfl⟩
    exact ⟨x, hx, y, hy, hxy, rfl⟩
  · rintro ⟨x, hx, y, hy, hxy, rfl⟩
    exact ⟨x, y, ⟨⟨hx, hy⟩, hxy⟩, rfl⟩

theorem offCols_smul (g : G) (S : Finset R) (c : R → R → ℕ) :
    offCols (g • S) (relab2 g c) = offCols S c := by
  ext k
  simp only [mem_offCols, exists_mem_smul_finset, relab2_smul, ne_eq, smul_left_cancel_iff]

theorem compStep_smul (g : G) (S : Finset R) (c : R → R → ℕ) (r : ℕ) (T : Finset R) :
    compStep (g • S) (relab2 g c) r (g • T) = g • compStep S c r T := by
  unfold compStep
  rw [smul_finset_union, filter_smul_finset]
  congr 2
  ext y
  simp only [mem_filter, exists_mem_smul_finset, relab2_smul]

theorem comp_smul (g : G) (S : Finset R) (c : R → R → ℕ) (r : ℕ) (x : R) :
    comp (g • S) (relab2 g c) r (g • x) = g • comp S c r x := by
  unfold comp
  rw [card_smul_finset]
  have h0 : (if g • x ∈ g • S then ({g • x} : Finset R) else ∅) =
      g • (if x ∈ S then ({x} : Finset R) else ∅) := by
    by_cases hx : x ∈ S
    · simp [hx, smul_mem_smul_finset_iff]
    · simp [hx, smul_mem_smul_finset_iff]
  rw [h0]
  generalize (if x ∈ S then ({x} : Finset R) else ∅) = T
  induction S.card generalizing T with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, compStep_smul, ih]

/-- The component of any point of a translated configuration. -/
theorem comp_smul' (g : G) (S : Finset R) (c : R → R → ℕ) (r : ℕ) (x : R) :
    comp (g • S) (relab2 g c) r x = g • comp S c r (g⁻¹ • x) := by
  rw [← comp_smul, smul_inv_smul]

theorem disconn_smul (g : G) (S : Finset R) (c : R → R → ℕ) :
    disconn (g • S) (relab2 g c) = disconn S c := by
  unfold disconn
  rw [offCols_smul]
  refine filter_congr fun r _ => ?_
  rw [exists_mem_smul_finset]
  simp only [comp_smul, ne_eq, smul_left_cancel_iff]

theorem bipEdge_smul (g : G) (c : R → R → ℕ) (k : ℕ) (x : R) (B : Finset R) :
    bipEdge (relab2 g c) k (g • x) (g • B) = bipEdge c k x B := by
  unfold bipEdge
  simp only [exists_mem_smul_finset, relab2_smul]

/-- The edge relation of a translated colouring. -/
theorem bipEdge_relab (g : G) (c : R → R → ℕ) (k : ℕ) :
    bipEdge (relab2 g c) k = fun x B => bipEdge c k (g⁻¹ • x) (g⁻¹ • B) := by
  funext x B
  rw [← bipEdge_smul g c k, smul_inv_smul, smul_inv_smul]

omit [DecidableEq R] in
theorem relab2_apply (g : G) (c : R → R → ℕ) (x y : R) :
    relab2 g c x y = c (g⁻¹ • x) (g⁻¹ • y) := rfl

theorem colPart_smul (σ : Equiv.Perm R) (S : Finset R) (f : R → ℕ) :
    colPart (σ • S) (fun x => f (σ⁻¹ • x)) = σ • colPart S f := by
  show CPart.mk _ _ = CPart.mk _ _
  congr 1
  funext x
  rw [filter_smul_finset]
  simp only [inv_smul_smul]
  rfl

theorem colPart_smul' (σ : Equiv.Perm R) (S : Finset R) (f : R → ℕ) :
    colPart (σ • S) f = σ • colPart S fun x => f (σ • x) := by
  rw [← colPart_smul]
  simp only [smul_inv_smul]

end Classical

section Twins

variable {G X Y : Type*} [Group G] [MulAction G X] [MulAction G Y] [DecidableEq X]
  [DecidableEq Y]

/-- Twin classes move with the points. -/
theorem twinCls_smul (g : G) (V₁ : Finset X) (V₂ : Finset Y) (A : X → Y → Bool) (x : X) :
    twinCls (g • V₁) (g • V₂) (fun a b => A (g⁻¹ • a) (g⁻¹ • b)) (g • x) =
      g • twinCls V₁ V₂ A x := by
  unfold twinCls
  rw [filter_smul_finset]
  congr 1
  refine filter_congr fun x' _ => ?_
  rw [forall_mem_smul_finset]
  simp only [inv_smul_smul]

omit [MulAction G Y] [DecidableEq Y] in
/-- Twin classes for the edges of one colour. -/
theorem twinCls_colour_smul (g : G) (V₁ V₂ : Finset X) (c : X → X → ℕ)
    (k : ℕ) (x : X) :
    twinCls (g • V₁) (g • V₂) (fun a b => decide (c (g⁻¹ • a) (g⁻¹ • b) = k)) (g • x) =
      g • twinCls V₁ V₂ (fun a b => decide (c a b = k)) x :=
  twinCls_smul g V₁ V₂ (fun a b => decide (c a b = k)) x

end Twins

/-! ### The outputs of `cohSoj` -/

section Out

variable {R : Type*} [DecidableEq R]

theorem CPart.smul_mk (σ : Equiv.Perm R) (col : R → ℕ) (blk : R → Finset R) :
    σ • (CPart.mk col blk) = ⟨fun v => col (σ⁻¹ • v), fun v => σ • blk (σ⁻¹ • v)⟩ := rfl

theorem CohOut.smul_part (σ : Equiv.Perm R) (p : CPart R) :
    σ • CohOut.part p = CohOut.part (σ • p) := rfl

theorem CohOut.smul_bip (σ : Equiv.Perm R) (W₁ : Finset R) (W₂ : Finset (Finset R))
    (A : R → Finset R → Bool) :
    σ • CohOut.bip W₁ W₂ A = CohOut.bip (σ • W₁) (σ • W₂) fun x B => A (σ⁻¹ • x) (σ⁻¹ • B) :=
  rfl

end Out

end GraphIso.SplitJohnson
