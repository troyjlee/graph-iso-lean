module

public import GraphIso.SplitJohnson.Relabel

/-!
# Coherent Split-or-Johnson: correctness and canonicity

`coherent_split_or_johnson` (Helfgott, Prop. 5.8): under the hypotheses of the proposition the
procedure `cohSoj` is live, makes at most `|C₂|` choices, and every reachable leaf is valid
(`CohValid`). `coherent_split_or_johnson_relabel`: it is canonical under every permutation of
the point type.

The hypotheses are bundled as `CohHyp`. One lemma per kind of leaf:
* `isColPart_comp`: the components of a disconnected colour of `X[C₁]`;
* `isColPart_colPart`: a colouring of `C₁` by the colours into one point of `C₂`;
* `CohHyp.valid_good`: the singletons of a block of `X[C₂]` with small twin classes;
* `CohHyp.valid_contract`: the contraction of the blocks of `X[C₂]` (Exercises 2.18 and 5.4);
  the twin class witnessing that no block is good is joined to its block by `violet` only,
  so the contraction is not complete;
* `CohHyp.valid_prim`: the primitive case (Exercise 5.4 for `(L_violet(y), L_blue(y))`). The
  bipartite graph is not complete: otherwise the twin relation of the `violet` graph into `C₂`,
  which depends only on the colour of the pair (Exercise 5.6), would contain the connected
  `blue` graph, making `c` constant on `C₁ × C₂`.
`CohHyp.blues_nonempty` gives the colour `blue` because `X[C₂]` is not a clique.
-/

@[expose] public section

namespace GraphIso.SplitJohnson

open Finset Pointwise GraphIso.Coherent

variable {R : Type*} [DecidableEq R]

/-! ### Colour partitions -/

omit [DecidableEq R] in
/-- A colouring whose classes have at most `t` points, each class one block, is a colored
`t`-partition. -/
theorem isColPart_colPart {S : Finset R} {f : R → ℕ} {t : ℕ}
    (h : ∀ v ∈ S, (S.filter fun y => f y = f v).card ≤ t) : IsColPart S t (colPart S f) where
  mem_blk v hv := by simp [colPart, hv]
  blk_sub v _ := filter_subset _ _
  blk_eq v _ w hw := by
    simp only [colPart, mem_filter] at hw ⊢
    rw [hw.2]
  col_eq v _ w hw := (mem_filter.1 hw).2
  card_eq v _ w _ hvw := by
    change f v = f w at hvw
    simp only [colPart, hvw]
  admissible v hv h1 w hw hwv := by
    change f w = f v at hwv
    have hvb : v ∈ (colPart S f).blk v := by simp [colPart, hv]
    have hwb : w ∈ (colPart S f).blk v := by simp [colPart, hw, hwv]
    obtain ⟨a, ha⟩ := card_eq_one.1 h1
    rw [ha, mem_singleton] at hvb hwb
    rw [hvb, hwb]
  card_le v hv := h v hv

/-- A component of a disconnected colour is not the whole set. -/
theorem comp_ne_of_mem_disconn {S : Finset R} {c : R → R → ℕ} (hc : IsCoh2On S c)
    (hh : IsHomog S c) {r : ℕ} (hr : r ∈ disconn S c) {v : R} (hv : v ∈ S) :
    comp S c r v ≠ S := by
  obtain ⟨x, hx, hne⟩ := (mem_filter.1 hr).2
  intro hv'
  apply hne
  refine eq_of_subset_of_card_le (comp_subset S c r x) ?_
  rw [hc.card_comp_eq hh r hx hv, hv']

/-- **The components of a disconnected colour form a colored `|S|/2`-partition** with one
colour. -/
theorem isColPart_comp {S : Finset R} {c : R → R → ℕ} (hc : IsCoh2On S c) (hh : IsHomog S c)
    {r : ℕ} (hr : r ∈ disconn S c) :
    IsColPart S (S.card / 2) ⟨fun _ => 0, comp S c r⟩ where
  mem_blk v hv := self_mem_comp hv
  blk_sub v _ := comp_subset S c r v
  blk_eq v _ w hw := comp_eq_of_mem hw
  col_eq _ _ _ _ := rfl
  card_eq v hv w hw _ := hc.card_comp_eq hh r hv hw
  admissible v hv h1 := by
    have := hc.two_le_card_comp hh (mem_filter.1 hr).1 hv
    simp only at h1
    omega
  card_le v hv := by
    have := hc.two_mul_card_comp_le hh r hv (comp_ne_of_mem_disconn hc hh hr hv)
    simp only
    omega

/-- Distinct components are disjoint. -/
theorem disjoint_comp {S : Finset R} {c : R → R → ℕ} {r : ℕ} {B B' : Finset R}
    (hB : B ∈ S.image (comp S c r)) (hB' : B' ∈ S.image (comp S c r)) (hne : B ≠ B') :
    Disjoint B B' := by
  obtain ⟨y, -, rfl⟩ := mem_image.1 hB
  obtain ⟨y', -, rfl⟩ := mem_image.1 hB'
  rw [disjoint_left]
  intro z hz hz'
  exact hne ((comp_eq_of_mem hz).symm.trans (comp_eq_of_mem hz'))

/-- There are at most half as many components of an off-diagonal colour as points. -/
theorem two_mul_card_comps_le {S : Finset R} {c : R → R → ℕ} (hc : IsCoh2On S c)
    (hh : IsHomog S c) {r : ℕ} (hr : r ∈ offCols S c) :
    2 * (S.image (comp S c r)).card ≤ S.card := by
  have hU : (S.image (comp S c r)).biUnion id = S := by
    apply subset_antisymm
    · intro z hz
      obtain ⟨B, hB, hzB⟩ := mem_biUnion.1 hz
      obtain ⟨y, -, rfl⟩ := mem_image.1 hB
      exact comp_subset S c r y hzB
    · intro z hz
      exact mem_biUnion.2 ⟨comp S c r z, mem_image_of_mem _ hz, self_mem_comp hz⟩
  have hcard := card_biUnion (s := S.image (comp S c r)) (t := id)
    fun B hB B' hB' hne => disjoint_comp hB hB' hne
  rw [hU] at hcard
  rw [hcard, mul_comm, ← smul_eq_mul, ← sum_const]
  refine sum_le_sum fun B hB => ?_
  obtain ⟨y, hy, rfl⟩ := mem_image.1 hB
  exact hc.two_le_card_comp hh hr hy

omit [DecidableEq R] in
theorem bipEdge_eq_true {c : R → R → ℕ} {g : ℕ} {x : R} {B : Finset R} :
    bipEdge c g x B = true ↔ ∃ y ∈ B, c x y = g := by
  simp [bipEdge]

/-- Twins with respect to singletons are twins with respect to the points. -/
theorem twinCls_image_singleton (V B : Finset R) (c : R → R → ℕ) (g : ℕ) (x : R) :
    twinCls V (B.image singleton) (bipEdge c g) x =
      twinCls V B (fun x y => decide (c x y = g)) x := by
  ext x'
  simp only [mem_twinCls, forall_mem_image, bipEdge, mem_singleton, exists_eq_left]

/-! ### The hypotheses of Prop. 5.8 -/

/-- The hypotheses of Coherent Split-or-Johnson. -/
structure CohHyp (C₁ C₂ : Finset R) (c : R → R → ℕ) : Prop where
  coh : IsCoh2On (C₁ ∪ C₂) c
  disj : Disjoint C₁ C₂
  hom₁ : ∀ x ∈ C₁, ∀ y ∈ C₁, c x x = c y y
  hom₂ : ∀ x ∈ C₂, ∀ y ∈ C₂, c x x = c y y
  sep : ∀ x ∈ C₁, ∀ y ∈ C₂, c x x ≠ c y y
  card_lt : C₂.card < C₁.card
  nonconst : ∃ x ∈ C₁, ∃ y ∈ C₂, ∃ x' ∈ C₁, ∃ y' ∈ C₂, c x y ≠ c x' y'
  noclique : ¬ IsClique c C₂

namespace CohHyp

variable {C₁ C₂ : Finset R} {c : R → R → ℕ} (H : CohHyp C₁ C₂ c)
include H

theorem coh₁ : IsCoh2On C₁ c :=
  H.coh.subset subset_union_left fun x hx y hy hxy => by
    rcases mem_union.1 hy with hy | hy
    · exact hy
    · exact absurd hxy (H.sep x hx y hy)

theorem coh₂ : IsCoh2On C₂ c :=
  H.coh.subset subset_union_right fun x hx y hy hxy => by
    rcases mem_union.1 hy with hy | hy
    · exact absurd hxy.symm (H.sep y hy x hx)
    · exact hy

theorem two_le_card₂ : 2 ≤ C₂.card := by
  by_contra h
  apply H.noclique
  intro u hu v hv u' hu' v' hv' huv _
  have : C₂.card ≤ 1 := by omega
  exact absurd (card_le_one.1 this u hu v hv) huv

theorem nonempty₂ : C₂.Nonempty := card_pos.1 (by have := H.two_le_card₂; omega)

/-- A pair with a colour of `C₁ × C₂` lies in `C₁ × C₂`. -/
theorem mem_of_colour {x y x₀ y₀ : R} (hx : x ∈ C₁ ∪ C₂) (hy : y ∈ C₁ ∪ C₂) (hx₀ : x₀ ∈ C₁)
    (hy₀ : y₀ ∈ C₂) (h : c x y = c x₀ y₀) : x ∈ C₁ ∧ y ∈ C₂ := by
  obtain ⟨-, -, h1, h2⟩ := H.coh.config hx hy (mem_union_left _ hx₀) (mem_union_right _ hy₀) h
  constructor
  · rcases mem_union.1 hx with hx | hx
    · exact hx
    · exact absurd h1.symm (H.sep x₀ hx₀ x hx)
  · rcases mem_union.1 hy with hy | hy
    · exact absurd h2 (H.sep y hy y₀ hy₀)
    · exact hy

/-- Counting the points of `C₁` with a given colour into a point of `C₂`. -/
theorem filter_in_eq {z x₀ y₀ : R} (hz : z ∈ C₂) (hx₀ : x₀ ∈ C₁) (hy₀ : y₀ ∈ C₂) :
    (C₁ ∪ C₂).filter (fun x => c x z = c x₀ y₀) = C₁.filter fun x => c x z = c x₀ y₀ := by
  ext x
  simp only [mem_filter]
  constructor
  · rintro ⟨hx, h⟩
    exact ⟨(H.mem_of_colour hx (mem_union_right _ hz) hx₀ hy₀ h).1, h⟩
  · rintro ⟨hx, h⟩
    exact ⟨mem_union_left _ hx, h⟩

/-- Counting the points of `C₂` with a given colour from a point of `C₁`. -/
theorem filter_out_eq {x x₀ y₀ : R} (hx : x ∈ C₁) (hx₀ : x₀ ∈ C₁) (hy₀ : y₀ ∈ C₂) :
    (C₁ ∪ C₂).filter (fun z => c x z = c x₀ y₀) = C₂.filter fun z => c x z = c x₀ y₀ := by
  ext z
  simp only [mem_filter]
  constructor
  · rintro ⟨hz, h⟩
    exact ⟨(H.mem_of_colour (mem_union_left _ hx) hz hx₀ hy₀ h).2, h⟩
  · rintro ⟨hz, h⟩
    exact ⟨mem_union_right _ hz, h⟩

/-- **In-degrees** of a colour of `C₁ × C₂` are constant on `C₂`. -/
theorem indeg_eq {z w x₀ y₀ : R} (hz : z ∈ C₂) (hw : w ∈ C₂) (hx₀ : x₀ ∈ C₁) (hy₀ : y₀ ∈ C₂) :
    (C₁.filter fun x => c x z = c x₀ y₀).card = (C₁.filter fun x => c x w = c x₀ y₀).card := by
  rw [← H.filter_in_eq hz hx₀ hy₀, ← H.filter_in_eq hw hx₀ hy₀]
  exact H.coh.indeg (mem_union_right _ hz) (mem_union_right _ hw) (H.hom₂ z hz w hw) _

/-- **Out-degrees** of a colour of `C₁ × C₂` are constant on `C₁`. -/
theorem outdeg_eq {x x' x₀ y₀ : R} (hx : x ∈ C₁) (hx' : x' ∈ C₁) (hx₀ : x₀ ∈ C₁)
    (hy₀ : y₀ ∈ C₂) :
    (C₂.filter fun z => c x z = c x₀ y₀).card = (C₂.filter fun z => c x' z = c x₀ y₀).card := by
  rw [← H.filter_out_eq hx hx₀ hy₀, ← H.filter_out_eq hx' hx₀ hy₀]
  exact H.coh.outdeg (mem_union_left _ hx) (mem_union_left _ hx') (H.hom₁ x hx x' hx') _

/-- The points of vertex colour `κ₂` are `C₂`. -/
theorem filter_vertex₂ {y₀ : R} (hy₀ : y₀ ∈ C₂) :
    (C₁ ∪ C₂).filter (fun w => c w w = c y₀ y₀) = C₂ := by
  ext w
  simp only [mem_filter, mem_union]
  constructor
  · rintro ⟨hw | hw, h⟩
    · exact absurd h (H.sep w hw y₀ hy₀)
    · exact hw
  · intro hw
    exact ⟨Or.inr hw, H.hom₂ w hw y₀ hy₀⟩

/-- The points of vertex colour `κ₁` satisfying `P` are those of `C₁`. -/
theorem filter_vertex₁ {x₀ : R} (hx₀ : x₀ ∈ C₁) (P : R → Prop) [DecidablePred P] :
    (C₁ ∪ C₂).filter (fun x => c x x = c x₀ x₀ ∧ P x) = C₁.filter P := by
  ext x
  simp only [mem_filter, mem_union]
  constructor
  · rintro ⟨hx | hx, h, hP⟩
    · exact ⟨hx, hP⟩
    · exact absurd h.symm (H.sep x₀ hx₀ x hx)
  · rintro ⟨hx, hP⟩
    exact ⟨Or.inl hx, H.hom₁ x hx x₀ hx₀, hP⟩

/-- Off-diagonal colours of `X[C₂]` have positive out-degree at every point of `C₂`. -/
theorem outdeg₂_pos {y : R} {k : ℕ} (hk : k ∈ offCols C₂ c) (hy : y ∈ C₂) :
    0 < (C₂.filter fun z => c y z = k).card := by
  obtain ⟨u, hu, v, hv, -, rfl⟩ := mem_offCols.1 hk
  rw [H.coh₂.outdeg hy hu (H.hom₂ y hy u hu)]
  exact card_pos.2 ⟨v, mem_filter.2 ⟨hv, rfl⟩⟩

/-! ### The leaves of `cohSoj` -/

/-- **A good block** (`X[C₂]` imprimitive): the singletons of a block whose twin classes in
`C₁` are small. -/
theorem valid_good {r v : ℕ} {y : R} (hy : y ∈ C₂) (hr : r ∈ disconn C₂ c)
    (hgood : ∀ x ∈ C₁,
      2 * (twinCls C₁ (comp C₂ c r y) (fun x y => decide (c x y = v)) x).card ≤ C₁.card) :
    CohValid C₁ C₂ (some (.bip C₁ ((comp C₂ c r y).image singleton) (bipEdge c v))) := by
  refine ⟨subset_refl _, by omega, ?_, ?_, ?_, ?_⟩
  · intro B hB
    obtain ⟨z, hz, rfl⟩ := mem_image.1 hB
    exact ⟨singleton_nonempty z, singleton_subset_iff.2 (comp_subset _ _ _ _ hz)⟩
  · intro B hB B' hB' hne
    obtain ⟨z, -, rfl⟩ := mem_image.1 hB
    obtain ⟨z', -, rfl⟩ := mem_image.1 hB'
    exact disjoint_singleton.2 fun h => hne (by rw [h])
  · rw [card_image_of_injective _ singleton_injective]
    exact H.coh₂.two_mul_card_comp_le H.hom₂ r hy (comp_ne_of_mem_disconn H.coh₂ H.hom₂ hr hy)
  · intro x hx
    rw [twinCls_image_singleton]
    exact hgood x hx

/-- **The contraction** (`X[C₂]` imprimitive, no good block): the blocks of `X[C₂]` with the
edges of a colour `g ≠ v`. -/
theorem valid_contract {r v g : ℕ} (hr : r ∈ disconn C₂ c)
    (hv : v ∈ ((C₁ ×ˢ C₂).image fun p => c p.1 p.2) ∧
      ∃ w ∈ C₂, C₁.card < 2 * (C₁.filter fun x => c x w = v).card)
    (hgood : ∀ y ∈ C₂, ∃ x ∈ C₁,
      C₁.card < 2 * (twinCls C₁ (comp C₂ c r y) (fun x y => decide (c x y = v)) x).card)
    (hg : g ∈ ((C₁ ×ˢ C₂).image fun p => c p.1 p.2).erase v) :
    CohValid C₁ C₂ (some (.bip C₁ (C₂.image (comp C₂ c r)) (bipEdge c g))) := by
  have hroff : r ∈ offCols C₂ c := (mem_filter.1 hr).1
  obtain ⟨hgv, hgcols⟩ := mem_erase.1 hg
  obtain ⟨⟨x₀, y₀⟩, hp₀, hg₀⟩ := mem_image.1 hgcols
  obtain ⟨hx₀, hy₀⟩ := mem_product.1 hp₀
  simp only at hg₀ hx₀ hy₀
  obtain ⟨hvcols, w, hw, hvw⟩ := hv
  obtain ⟨⟨x₁, y₁⟩, hp₁, hv₁⟩ := mem_image.1 hvcols
  obtain ⟨hx₁, hy₁⟩ := mem_product.1 hp₁
  simp only at hv₁ hx₁ hy₁
  refine ⟨subset_refl _, by omega, ?_, ?_, two_mul_card_comps_le H.coh₂ H.hom₂ hroff, ?_⟩
  · intro B hB
    obtain ⟨y, hy, rfl⟩ := mem_image.1 hB
    exact ⟨⟨y, self_mem_comp hy⟩, comp_subset _ _ _ _⟩
  · exact fun B hB B' hB' hne => disjoint_comp hB hB' hne
  · -- Exercise 5.4 for the contraction
    have hS₂ := H.filter_vertex₂ hy₀
    have e₁ : ∀ x, ((C₂.image (comp C₂ c r)).filter fun B => bipEdge c g x B = true) =
        (C₂.image (comp C₂ c r)).filter fun B => ∃ z ∈ B, c x z = g :=
      fun x => filter_congr fun B _ => bipEdge_eq_true
    have e₂ : ∀ B, (C₁.filter fun x => bipEdge c g x B = true) =
        C₁.filter fun x => ∃ z ∈ B, c x z = g :=
      fun B => filter_congr fun x _ => bipEdge_eq_true
    have hdeg₁ : ∀ x ∈ C₁, ((C₂.image (comp C₂ c r)).filter fun B => bipEdge c g x B).card =
        ((C₂.image (comp C₂ c r)).filter fun B => bipEdge c g x₀ B).card := by
      intro x hx
      have := H.coh.contract_deg_points (c y₀ y₀) r g (mem_union_left _ hx)
        (mem_union_left _ hx₀) (H.hom₁ x hx x₀ hx₀)
      rw [hS₂] at this
      rw [e₁, e₁]
      exact this
    have hdeg₂ : ∀ B ∈ C₂.image (comp C₂ c r), (C₁.filter fun x => bipEdge c g x B).card =
        (C₁.filter fun x => bipEdge c g x (comp C₂ c r y₀)).card := by
      intro B hB
      obtain ⟨y, hy, rfl⟩ := mem_image.1 hB
      have := H.coh.contract_deg_blocks (c x₀ x₀) (c y₀ y₀) r g (mem_union_right _ hy)
        (mem_union_right _ hy₀) (H.hom₂ y hy y₀ hy₀) rfl
      rw [hS₂, H.filter_vertex₁ hx₀, H.filter_vertex₁ hx₀] at this
      rw [e₂, e₂]
      exact this
    have hne : ∃ x ∈ C₁, ∃ B ∈ C₂.image (comp C₂ c r), bipEdge c g x B = true :=
      ⟨x₀, hx₀, comp C₂ c r y₀, mem_image_of_mem _ hy₀,
        bipEdge_eq_true.2 ⟨y₀, self_mem_comp hy₀, hg₀⟩⟩
    have hnc : ∃ x ∈ C₁, ∃ B ∈ C₂.image (comp C₂ c r), bipEdge c g x B = false := by
      obtain ⟨x, hx, hT⟩ := hgood y₀ hy₀
      refine ⟨x, hx, comp C₂ c r y₀, mem_image_of_mem _ hy₀, ?_⟩
      -- the twin class of `x` is violet into the whole block
      have hall : ∀ z ∈ comp C₂ c r y₀, c x z = v := by
        intro z hz
        by_contra hxz
        have hz₂ : z ∈ C₂ := comp_subset _ _ _ _ hz
        have hTsub : twinCls C₁ (comp C₂ c r y₀) (fun x y => decide (c x y = v)) x ⊆
            C₁.filter fun x' => ¬ c x' z = v := by
          intro x' hx'
          obtain ⟨hx'1, hx'2⟩ := mem_twinCls.1 hx'
          have := hx'2 z hz
          refine mem_filter.2 ⟨hx'1, fun h => hxz ?_⟩
          simpa [h] using this
        have hsplit := card_filter_add_card_filter_not (s := C₁) (fun x' => c x' z = v)
        have hin := H.indeg_eq hz₂ hw hx₁ hy₁
        rw [hv₁] at hin
        have := card_le_card hTsub
        omega
      rw [Bool.eq_false_iff]
      intro h
      obtain ⟨z, hz, hxz⟩ := bipEdge_eq_true.1 h
      exact hgv (hxz.symm.trans (hall z hz))
    intro x hx
    exact two_mul_card_twinCls_le hdeg₁ hdeg₂ hne hnc hx

/-- The colour of `(y, z)` determines that of `(z, y)`, for points of `C₁ ∪ C₂`. -/
theorem rev_iff {x y x₀ y₀ : R} (hx : x ∈ C₁ ∪ C₂) (hy : y ∈ C₁ ∪ C₂) (hx₀ : x₀ ∈ C₁ ∪ C₂)
    (hy₀ : y₀ ∈ C₁ ∪ C₂) : c x y = c x₀ y₀ ↔ c y x = c y₀ x₀ :=
  ⟨fun h => (H.coh.config hx hy hx₀ hy₀ h).2.1,
    fun h => (H.coh.config hy hx hy₀ hx₀ h).2.1⟩

/-- **The primitive case** (Babai's corrected argument, Helfgott footnote 17): for `y ∈ C₂`,
the points `V₁` of `C₁` joined to `y` by a colour `v` of more than half of `C₁`, and the points
`V₂` of `C₂` joined from `y` by a colour `b` of `X[C₂]` of positive degree below `|C₂|/2`. -/
theorem valid_prim {y : R} {v b : ℕ} (hy : y ∈ C₂) (hprim : disconn C₂ c = ∅)
    (hv : v ∈ ((C₁ ×ˢ C₂).image fun p => c p.1 p.2) ∧
      C₁.card < 2 * (C₁.filter fun x => c x y = v).card)
    (hb : b ∈ offCols C₂ c ∧ 0 < (C₂.filter fun z => c y z = b).card ∧
      2 * (C₂.filter fun z => c y z = b).card < C₂.card) :
    CohValid C₁ C₂ (some (.bip (C₁.filter fun x => c x y = v)
      ((C₂.filter fun z => c y z = b).image singleton) (bipEdge c v))) := by
  set V₁ := C₁.filter fun x => c x y = v with hV₁
  set V₂ := C₂.filter fun z => c y z = b with hV₂
  obtain ⟨hvcols, hV₁big⟩ := hv
  obtain ⟨hboff, hbpos, hbsmall⟩ := hb
  obtain ⟨⟨x₁, y₁⟩, hp₁, hv₁⟩ := mem_image.1 hvcols
  obtain ⟨hx₁, hy₁⟩ := mem_product.1 hp₁
  simp only at hv₁ hx₁ hy₁
  obtain ⟨u, hu, u', hu', -, hbu⟩ := mem_offCols.1 hboff
  have hS : ∀ {a}, a ∈ C₁ → a ∈ C₁ ∪ C₂ := fun h => mem_union_left _ h
  have hS' : ∀ {a}, a ∈ C₂ → a ∈ C₁ ∪ C₂ := fun h => mem_union_right _ h
  -- points joined from `y` by `b` are in `C₂`
  have hmemb : ∀ z ∈ C₁ ∪ C₂, c y z = b → z ∈ C₂ := by
    intro z hz hyz
    obtain ⟨-, -, -, h2⟩ := H.coh.config (hS' hy) hz (hS' hu) (hS' hu') (hyz.trans hbu.symm)
    rcases mem_union.1 hz with hz | hz
    · exact absurd h2 (H.sep z hz u' hu')
    · exact hz
  -- points joined to `y` by `v` are in `C₁`
  have hmemv : ∀ x ∈ C₁ ∪ C₂, c x y = v → x ∈ C₁ := fun x hx h =>
    (H.mem_of_colour hx (hS' hy) hx₁ hy₁ (h.trans hv₁.symm)).1
  refine ⟨filter_subset _ _, by omega, ?_, ?_, ?_, ?_⟩
  · intro B hB
    obtain ⟨z, hz, rfl⟩ := mem_image.1 hB
    exact ⟨singleton_nonempty z, singleton_subset_iff.2 (filter_subset _ _ hz)⟩
  · intro B hB B' hB' hne
    obtain ⟨z, -, rfl⟩ := mem_image.1 hB
    obtain ⟨z', -, rfl⟩ := mem_image.1 hB'
    exact disjoint_singleton.2 fun h => hne (by rw [h])
  · rw [card_image_of_injective _ singleton_injective]
    omega
  · -- Exercise 5.4 for `(V₁, V₂; v)`
    have e₁ : ∀ x, ((V₂.image singleton).filter fun B => bipEdge c v x B = true) =
        (V₂.filter fun z => c x z = v).image singleton := by
      intro x
      rw [filter_image]
      congr 1
      exact filter_congr fun z _ => by simp [bipEdge]
    have e₂ : ∀ z, (V₁.filter fun x => bipEdge c v x {z} = true) =
        (C₁ ∪ C₂).filter fun x => c x y = v ∧ c x z = v := by
      intro z
      ext x
      simp only [hV₁, mem_filter, bipEdge, mem_singleton, exists_eq_left, decide_eq_true_eq]
      constructor
      · rintro ⟨⟨hx, h1⟩, h2⟩
        exact ⟨hS hx, h1, h2⟩
      · rintro ⟨hx, h1, h2⟩
        exact ⟨⟨hmemv x hx h1, h1⟩, h2⟩
    obtain ⟨x₂, hx₂⟩ : V₁.Nonempty := card_pos.1 (by omega)
    obtain ⟨z₂, hz₂⟩ : V₂.Nonempty := card_pos.1 hbpos
    have hx₂C : x₂ ∈ C₁ := (mem_filter.1 hx₂).1
    have hz₂C : z₂ ∈ C₂ := (mem_filter.1 hz₂).1
    have hdeg₁ : ∀ x ∈ V₁, ((V₂.image singleton).filter fun B => bipEdge c v x B).card =
        ((V₂.image singleton).filter fun B => bipEdge c v x₂ B).card := by
      have key : ∀ x ∈ V₁, V₂.filter (fun z => c x z = v) = (C₁ ∪ C₂).filter fun z =>
          c x z = v ∧ ∃ p ∈ C₁ ∪ C₂, ∃ q ∈ C₁ ∪ C₂, c p q = c z y ∧ c q p = b := by
        intro x _
        ext z
        simp only [hV₂, mem_filter]
        constructor
        · rintro ⟨⟨hz, hyz⟩, hxz⟩
          exact ⟨hS' hz, hxz, z, hS' hz, y, hS' hy, rfl, hyz⟩
        · rintro ⟨hz, hxz, p, hp, q, hq, h1, h2⟩
          have hyz : c y z = b := by
            rw [← h2]
            exact (H.rev_iff hz (hS' hy) hp hq).1 h1.symm
          exact ⟨⟨hmemb z hz hyz, hyz⟩, hxz⟩
      intro x hx
      rw [e₁, e₁, card_image_of_injective _ singleton_injective,
        card_image_of_injective _ singleton_injective, key x hx, key x₂ hx₂]
      exact H.coh.card_filter_pred (hS (mem_filter.1 hx).1) (hS' hy) (hS hx₂C) (hS' hy)
        ((mem_filter.1 hx).2.trans (mem_filter.1 hx₂).2.symm)
        (fun a e => a = v ∧ ∃ p ∈ C₁ ∪ C₂, ∃ q ∈ C₁ ∪ C₂, c p q = e ∧ c q p = b)
    have hdeg₂ : ∀ B ∈ V₂.image singleton, (V₁.filter fun x => bipEdge c v x B).card =
        (V₁.filter fun x => bipEdge c v x {z₂}).card := by
      have key : ∀ z ∈ C₂, ((C₁ ∪ C₂).filter fun x => c x y = v ∧ c x z = v) =
          (C₁ ∪ C₂).filter fun x =>
            (∃ p ∈ C₁ ∪ C₂, ∃ q ∈ C₁ ∪ C₂, c p q = c z x ∧ c q p = v) ∧ c x y = v := by
        intro z hz
        refine filter_congr fun x hx => ?_
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨⟨z, hS' hz, x, hx, rfl, h2⟩, h1⟩
        · rintro ⟨⟨p, hp, q, hq, h1, h2⟩, h3⟩
          refine ⟨h3, ?_⟩
          rw [← h2]
          exact (H.rev_iff (hS' hz) hx hp hq).1 h1.symm
      intro B hB
      obtain ⟨z, hz, rfl⟩ := mem_image.1 hB
      have hzC : z ∈ C₂ := (mem_filter.1 hz).1
      rw [e₂, e₂, key z hzC, key z₂ hz₂C]
      refine H.coh.card_filter_pred (hS' hzC) (hS' hy) (hS' hz₂C) (hS' hy) ?_
        (fun a e => (∃ p ∈ C₁ ∪ C₂, ∃ q ∈ C₁ ∪ C₂, c p q = a ∧ c q p = v) ∧ e = v)
      exact (H.rev_iff (hS' hy) (hS' hzC) (hS' hy) (hS' hz₂C)).1
        ((mem_filter.1 hz).2.trans (mem_filter.1 hz₂).2.symm)
    -- the in-degree of `v` at points of `C₂` is `|V₁|`
    have hin : ∀ z ∈ C₂, (C₁.filter fun x => c x z = v).card = V₁.card := by
      intro z hz
      have := H.indeg_eq hz hy hx₁ hy₁
      rw [hv₁] at this
      exact this
    have hne : ∃ x ∈ V₁, ∃ B ∈ V₂.image singleton, bipEdge c v x B = true := by
      obtain ⟨x, hx⟩ := inter_nonempty_of_card_lt_card_add_card
        (filter_subset (fun x => c x y = v) C₁) (filter_subset (fun x => c x z₂ = v) C₁)
        (by rw [hin z₂ hz₂C]; change C₁.card < V₁.card + V₁.card; omega)
      obtain ⟨hx1, hx2⟩ := mem_inter.1 hx
      exact ⟨x, hx1, {z₂}, mem_image_of_mem _ hz₂, by simp [bipEdge, (mem_filter.1 hx2).2]⟩
    have hnc : ∃ x ∈ V₁, ∃ B ∈ V₂.image singleton, bipEdge c v x B = false := by
      by_contra hall
      push Not at hall
      -- every point of `V₂` has `V₁` as its `v`-in-neighbourhood
      have hcol : ∀ z ∈ V₂, ∀ x ∈ C₁, (c x z = v ↔ c x y = v) := by
        intro z hz x hx
        have hsub : V₁ ⊆ C₁.filter fun x => c x z = v := by
          intro x' hx'
          have := hall x' hx' {z} (mem_image_of_mem _ hz)
          simp only [ne_eq, Bool.not_eq_false, bipEdge, mem_singleton, exists_eq_left,
            decide_eq_true_eq] at this
          exact mem_filter.2 ⟨(mem_filter.1 hx').1, this⟩
        have heq := eq_of_subset_of_card_le hsub (hin z (mem_filter.1 hz).1).le
        constructor
        · intro h
          have : x ∈ V₁ := heq ▸ mem_filter.2 ⟨hx, h⟩
          exact (mem_filter.1 this).2
        · intro h
          have : x ∈ C₁.filter fun x => c x z = v := heq ▸ (mem_filter.2 ⟨hx, h⟩ : x ∈ V₁)
          exact (mem_filter.1 this).2
      -- twins of the `v`-graph into `C₂` are determined by the colour of the pair
      let Tw : R → R → Prop := fun a w => ∀ x ∈ C₁, (c x a = v ↔ c x w = v)
      have hTw : ∀ a ∈ C₁ ∪ C₂, ∀ w ∈ C₁ ∪ C₂, Tw a w ↔
          ∀ x ∈ C₁ ∪ C₂, c x x = c x₁ x₁ → (c a x = c y₁ x₁ ↔ c w x = c y₁ x₁) := by
        intro a ha w hw
        constructor
        · intro h x hx hxx
          have hxC : x ∈ C₁ := by
            rcases mem_union.1 hx with hx | hx
            · exact hx
            · exact absurd hxx.symm (H.sep x₁ hx₁ x hx)
          rw [← H.rev_iff hx ha (hS hx₁) (hS' hy₁), ← H.rev_iff hx hw (hS hx₁) (hS' hy₁), hv₁]
          exact h x hxC
        · intro h x hx
          have := h x (hS hx) (H.hom₁ x hx x₁ hx₁)
          rwa [← H.rev_iff (hS hx) ha (hS hx₁) (hS' hy₁),
            ← H.rev_iff (hS hx) hw (hS hx₁) (hS' hy₁), hv₁] at this
      have htrans : ∀ a ∈ C₁ ∪ C₂, ∀ w ∈ C₁ ∪ C₂, ∀ a' ∈ C₁ ∪ C₂, ∀ w' ∈ C₁ ∪ C₂,
          c a w = c a' w' → Tw a w → Tw a' w' := by
        intro a ha w hw a' ha' w' hw' h hT
        rw [hTw a ha w hw] at hT
        rw [hTw a' ha' w' hw']
        exact (H.coh.twin_iff (c x₁ x₁) (c y₁ x₁) ha hw ha' hw' h).1 hT
      have hTyz : Tw y z₂ := fun x hx => (hcol z₂ hz₂ x hx).symm
      -- the `b`-graph of `X[C₂]` is connected, so `Tw y w` for all `w ∈ C₂`
      have hcomp : comp C₂ c b y = C₂ := by
        by_contra hne
        have : b ∈ disconn C₂ c := mem_filter.2 ⟨hboff, y, hy, hne⟩
        rw [hprim] at this
        exact absurd this (notMem_empty b)
      have hall' : ∀ w ∈ C₂, Tw y w := by
        intro w hw
        have hreach := (mem_comp.1 (hcomp.symm ▸ hw : w ∈ comp C₂ c b y)).2
        clear hw
        induction hreach with
        | refl => exact fun x _ => Iff.rfl
        | @tail a a' _ hab ih =>
          obtain ⟨haC, ha'C, hab'⟩ := hab
          have hTaa' : Tw a a' := by
            rcases hab' with h | h
            · exact htrans y (hS' hy) z₂ (hS' hz₂C) a (hS' haC) a' (hS' ha'C)
                (((mem_filter.1 hz₂).2).trans h.symm) hTyz
            · have := htrans y (hS' hy) z₂ (hS' hz₂C) a' (hS' ha'C) a (hS' haC)
                (((mem_filter.1 hz₂).2).trans h.symm) hTyz
              exact fun x hx => (this x hx).symm
          exact fun x hx => (ih x hx).trans (hTaa' x hx)
      -- so every point of `C₁` is joined to all of `C₂` by `v`
      have hconst : ∀ x ∈ C₁, ∀ w ∈ C₂, c x w = v := by
        have hx₂all : ∀ w ∈ C₂, c x₂ w = v := fun w hw =>
          (hall' w hw x₂ hx₂C).1 (mem_filter.1 hx₂).2
        intro x hx
        by_cases hxy : c x y = v
        · exact fun w hw => (hall' w hw x hx).1 hxy
        · exfalso
          have hdeg := H.outdeg_eq hx hx₂C hx₁ hy₁
          rw [hv₁] at hdeg
          have h1 : C₂.filter (fun z => c x₂ z = v) = C₂ := filter_true_of_mem hx₂all
          have h2 : C₂.filter (fun z => c x z = v) = ∅ :=
            filter_false_of_mem fun w hw h => hxy ((hall' w hw x hx).2 h)
          rw [h1, h2, card_empty] at hdeg
          have := H.two_le_card₂
          omega
      obtain ⟨x, hx, w, hw, x', hx', w', hw', hne⟩ := H.nonconst
      exact hne ((hconst x hx w hw).trans (hconst x' hx' w' hw').symm)

    intro x hx
    exact two_mul_card_twinCls_le hdeg₁ hdeg₂ hne hnc hx

/-- Since `X[C₂]` is not a clique, some colour of `X[C₂]` has positive out-degree below
`|C₂|/2` at every point. -/
theorem blues_nonempty {y : R} (hy : y ∈ C₂) :
    ((offCols C₂ c).filter fun b => 0 < (C₂.filter fun z => c y z = b).card ∧
      2 * (C₂.filter fun z => c y z = b).card < C₂.card).Nonempty := by
  have hcl := H.noclique
  unfold IsClique at hcl
  push Not at hcl
  obtain ⟨u, hu, v, hv, u', hu', v', hv', huv, hu'v', hne⟩ := hcl
  have hb₁ : c u v ∈ offCols C₂ c := mem_offCols.2 ⟨u, hu, v, hv, huv, rfl⟩
  have hb₂ : c u' v' ∈ offCols C₂ c := mem_offCols.2 ⟨u', hu', v', hv', hu'v', rfl⟩
  have hnoty : ∀ {p q : R}, p ∈ C₂ → q ∈ C₂ → p ≠ q →
      y ∉ C₂.filter fun z => c y z = c p q := by
    intro p q hp hq hpq hmem
    have := (H.coh₂.config hy hy hp hq (mem_filter.1 hmem).2).1
    exact hpq (this.1 rfl)
  have hsub : (C₂.filter fun z => c y z = c u v) ∪ (C₂.filter fun z => c y z = c u' v') ⊆
      C₂.erase y := by
    intro z hz
    rcases mem_union.1 hz with hz | hz
    · exact mem_erase.2 ⟨fun h => hnoty hu hv huv (h ▸ hz), (mem_filter.1 hz).1⟩
    · exact mem_erase.2 ⟨fun h => hnoty hu' hv' hu'v' (h ▸ hz), (mem_filter.1 hz).1⟩
  have hdisj : Disjoint (C₂.filter fun z => c y z = c u v)
      (C₂.filter fun z => c y z = c u' v') :=
    disjoint_filter.2 fun z _ h1 h2 => hne (h1.symm.trans h2)
  have hcard := card_le_card hsub
  rw [card_union_of_disjoint hdisj, card_erase_of_mem hy] at hcard
  have hp₁ := H.outdeg₂_pos hb₁ hy
  have hp₂ := H.outdeg₂_pos hb₂ hy
  by_cases h₁ : 2 * (C₂.filter fun z => c y z = c u v).card < C₂.card
  · exact ⟨c u v, mem_filter.2 ⟨hb₁, hp₁, h₁⟩⟩
  · refine ⟨c u' v', mem_filter.2 ⟨hb₂, hp₂, ?_⟩⟩
    have := H.two_le_card₂
    omega

end CohHyp

/-- **Coherent Split-or-Johnson** (Helfgott, Prop. 5.8). -/
theorem coherent_split_or_johnson {C₁ C₂ : Finset R} {c : R → R → ℕ}
    (hc : IsCoh2On (C₁ ∪ C₂) c) (hdisj : Disjoint C₁ C₂)
    (h₁ : ∀ x ∈ C₁, ∀ y ∈ C₁, c x x = c y y) (h₂ : ∀ x ∈ C₂, ∀ y ∈ C₂, c x x = c y y)
    (h₁₂ : ∀ x ∈ C₁, ∀ y ∈ C₂, c x x ≠ c y y) (hcard : C₂.card < C₁.card)
    (hnc : ∃ x ∈ C₁, ∃ y ∈ C₂, ∃ x' ∈ C₁, ∃ y' ∈ C₂, c x y ≠ c x' y')
    (hcl : ¬ IsClique c C₂) :
    (cohSoj C₁ C₂ c).Live ∧ (cohSoj C₁ C₂ c).count ≤ C₂.card ∧
      (cohSoj C₁ C₂ c).AllLeaves (CohValid C₁ C₂) := by
  have H : CohHyp C₁ C₂ c := ⟨hc, hdisj, h₁, h₂, h₁₂, hcard, hnc, hcl⟩
  have h2C := H.two_le_card₂
  unfold cohSoj
  by_cases hd₁ : (disconn C₁ c).Nonempty
  · rw [dite_eq_left hd₁]
    exact ⟨trivial, by show 1 ≤ C₂.card; omega, isColPart_comp H.coh₁ H.hom₁ (min'_mem _ _)⟩
  rw [dite_eq_right hd₁]
  dsimp only
  by_cases hd₂ : (disconn C₂ c).Nonempty
  · rw [dite_eq_left hd₂]
    have hred := min'_mem _ hd₂
    generalize (disconn C₂ c).min' hd₂ = r at hred ⊢
    by_cases hv : (((C₁ ×ˢ C₂).image fun p => c p.1 p.2).filter fun k =>
        ∃ w ∈ C₂, C₁.card < 2 * (C₁.filter fun x => c x w = k).card).Nonempty
    · rw [dite_eq_left hv]
      have hvmem := min'_mem _ hv
      generalize (((C₁ ×ˢ C₂).image fun p => c p.1 p.2).filter fun k =>
        ∃ w ∈ C₂, C₁.card < 2 * (C₁.filter fun x => c x w = k).card).min' hv = v at hvmem ⊢
      rw [mem_filter] at hvmem
      by_cases hG : ((C₂.image (comp C₂ c r)).filter fun B =>
          ∀ x ∈ C₁, 2 * (twinCls C₁ B (fun x y => decide (c x y = v)) x).card ≤
            C₁.card).Nonempty
      · rw [ite_eq_left hG]
        refine ⟨⟨?_, fun _ _ => trivial⟩, ?_, ?_⟩
        · obtain ⟨B, hB⟩ := hG
          obtain ⟨y, hy, rfl⟩ := mem_image.1 (mem_filter.1 hB).1
          exact ⟨y, mem_filter.2 ⟨hy, hB⟩⟩
        · simp only [CTree.count, sum_const, smul_eq_mul, mul_one]
          exact card_le_card (filter_subset _ _)
        · intro y hy
          obtain ⟨hyC, hyG⟩ := mem_filter.1 hy
          exact H.valid_good hyC hred (mem_filter.1 hyG).2
      · rw [ite_eq_right hG]
        have hg : (((C₁ ×ˢ C₂).image fun p => c p.1 p.2).erase v).Nonempty := by
          obtain ⟨x, hx, w, hw, x', hx', w', hw', hne⟩ := H.nonconst
          by_cases hxw : c x w = v
          · exact ⟨c x' w', mem_erase.2 ⟨fun h => hne (hxw.trans h.symm),
              mem_image.2 ⟨(x', w'), mem_product.2 ⟨hx', hw'⟩, rfl⟩⟩⟩
          · exact ⟨c x w, mem_erase.2 ⟨hxw, mem_image.2 ⟨(x, w), mem_product.2 ⟨hx, hw⟩, rfl⟩⟩⟩
        rw [dite_eq_left hg]
        refine ⟨trivial, by show 1 ≤ C₂.card; omega,
          H.valid_contract hred hvmem ?_ (min'_mem _ hg)⟩
        intro y hy
        by_contra hnot
        push Not at hnot
        exact hG ⟨comp C₂ c r y, mem_filter.2 ⟨mem_image_of_mem _ hy, hnot⟩⟩
    · rw [dite_eq_right hv]
      refine ⟨⟨H.nonempty₂, fun _ _ => trivial⟩, ?_, fun w hw => ?_⟩
      · simp [CTree.count]
      · show IsColPart C₁ (C₁.card / 2) (colPart C₁ fun x => c x w)
        refine isColPart_colPart fun x hx => ?_
        rw [Nat.le_div_iff_mul_le (by omega)]
        by_contra hlt
        push Not at hlt
        exact hv ⟨c x w, mem_filter.2 ⟨mem_image.2 ⟨(x, w), mem_product.2 ⟨hx, hw⟩, rfl⟩, w, hw,
          by omega⟩⟩
  · rw [dite_eq_right hd₂]
    have hprim : disconn C₂ c = ∅ := not_nonempty_iff_eq_empty.1 hd₂
    refine ⟨⟨H.nonempty₂, fun y _ => ?_⟩, ?_, fun y hy => ?_⟩
    · dsimp only
      split_ifs <;> trivial
    · simp only [CTree.count]
      refine (sum_le_sum fun y _ => (?_ : _ ≤ 1)).trans (by simp)
      split_ifs <;> simp [CTree.count]
    · dsimp only
      by_cases hvy : (((C₁ ×ˢ C₂).image fun p => c p.1 p.2).filter fun k =>
          C₁.card < 2 * (C₁.filter fun x => c x y = k).card).Nonempty
      · rw [dite_eq_left hvy]
        have hvmem := min'_mem _ hvy
        generalize (((C₁ ×ˢ C₂).image fun p => c p.1 p.2).filter fun k =>
          C₁.card < 2 * (C₁.filter fun x => c x y = k).card).min' hvy = v at hvmem ⊢
        rw [mem_filter] at hvmem
        have hb := H.blues_nonempty hy
        rw [dite_eq_left hb]
        exact H.valid_prim hy hprim hvmem (mem_filter.1 (min'_mem _ hb))
      · rw [dite_eq_right hvy]
        show IsColPart C₁ (C₁.card / 2) (colPart C₁ fun x => c x y)
        refine isColPart_colPart fun x hx => ?_
        rw [Nat.le_div_iff_mul_le (by omega)]
        by_contra hlt
        push Not at hlt
        exact hvy ⟨c x y, mem_filter.2 ⟨mem_image.2 ⟨(x, y), mem_product.2 ⟨hx, hy⟩, rfl⟩,
          by omega⟩⟩

/-- **Coherent Split-or-Johnson is canonical.** -/
theorem coherent_split_or_johnson_relabel (σ : Equiv.Perm R) (C₁ C₂ : Finset R)
    (c : R → R → ℕ) :
    cohSoj (σ • C₁) (σ • C₂) (relab2 σ c) = (cohSoj C₁ C₂ c).act σ := by
  have E1 := disconn_smul σ C₁ c
  have E2 := disconn_smul σ C₂ c
  have E3 : ((σ • C₁) ×ˢ (σ • C₂)).image (fun p => relab2 σ c p.1 p.2) =
      (C₁ ×ˢ C₂).image fun p => c p.1 p.2 := by
    ext k
    simp only [mem_image, mem_product, Prod.exists]
    constructor
    · rintro ⟨a, b, ⟨ha, hb⟩, rfl⟩
      exact ⟨σ⁻¹ • a, σ⁻¹ • b, ⟨mem_smul_finset_iff_inv.1 ha, mem_smul_finset_iff_inv.1 hb⟩, rfl⟩
    · rintro ⟨a, b, ⟨ha, hb⟩, rfl⟩
      exact ⟨σ • a, σ • b, ⟨smul_mem_smul_finset ha, smul_mem_smul_finset hb⟩, relab2_smul ..⟩
  unfold cohSoj
  by_cases h₁ : (disconn C₁ c).Nonempty
  · rw [dite_eq_left (show (disconn (σ • C₁) (relab2 σ c)).Nonempty by rw [E1]; exact h₁),
      dite_eq_left h₁]
    simp only [CTree.act, Option.smul_some, CohOut.smul_part, CPart.smul_mk, CTree.leaf.injEq,
      Option.some.injEq, CohOut.part.injEq, CPart.mk.injEq, true_and]
    rw [min'_congr E1]
    funext v
    exact comp_smul' ..
  rw [dite_eq_right (show ¬ (disconn (σ • C₁) (relab2 σ c)).Nonempty by rw [E1]; exact h₁),
      dite_eq_right h₁]
  dsimp only
  rw [E3]
  generalize (C₁ ×ˢ C₂).image (fun p => c p.1 p.2) = cols
  by_cases h₂ : (disconn C₂ c).Nonempty
  · rw [dite_eq_left (show (disconn (σ • C₂) (relab2 σ c)).Nonempty by rw [E2]; exact h₂),
      dite_eq_left h₂, min'_congr E2]
    generalize (disconn C₂ c).min' _ = r
    have Ebig : (cols.filter fun k => ∃ w ∈ σ • C₂,
        (σ • C₁).card < 2 * ((σ • C₁).filter fun x => relab2 σ c x w = k).card) =
        cols.filter fun k => ∃ w ∈ C₂, C₁.card < 2 * (C₁.filter fun x => c x w = k).card := by
      refine filter_congr fun k _ => ?_
      simp only [exists_mem_smul_finset, card_smul_finset, card_filter_smul_finset, relab2_smul]
    by_cases hv : (cols.filter fun k =>
        ∃ w ∈ C₂, C₁.card < 2 * (C₁.filter fun x => c x w = k).card).Nonempty
    · rw [dite_eq_left (show _ by rw [Ebig]; exact hv), dite_eq_left hv, min'_congr Ebig]
      generalize (cols.filter fun k =>
        ∃ w ∈ C₂, C₁.card < 2 * (C₁.filter fun x => c x w = k).card).min' hv = v
      have Egood : ((σ • C₂).image (comp (σ • C₂) (relab2 σ c) r)).filter (fun B =>
          ∀ x ∈ σ • C₁, 2 * (twinCls (σ • C₁) B (fun x y => decide (relab2 σ c x y = v)) x).card
            ≤ (σ • C₁).card) =
          σ • (C₂.image (comp C₂ c r)).filter (fun B =>
            ∀ x ∈ C₁, 2 * (twinCls C₁ B (fun x y => decide (c x y = v)) x).card ≤ C₁.card) := by
        rw [image_smul_finset]
        simp only [comp_smul]
        rw [image_smul_comp, filter_smul_finset]
        congr 1
        refine filter_congr fun B _ => ?_
        rw [forall_mem_smul_finset, card_smul_finset]
        refine forall₂_congr fun x _ => ?_
        rw [show (fun x y => decide (relab2 σ c x y = v)) =
          fun a b => decide (c (σ⁻¹ • a) (σ⁻¹ • b) = v) from rfl,
          twinCls_colour_smul, card_smul_finset]
      rw [Egood]
      by_cases hG : ((C₂.image (comp C₂ c r)).filter (fun B =>
            ∀ x ∈ C₁, 2 * (twinCls C₁ B (fun x y => decide (c x y = v)) x).card ≤
              C₁.card)).Nonempty
      · rw [ite_eq_left (smul_finset_nonempty.2 hG), ite_eq_left hG]
        simp only [CTree.act]
        congr 1
        · rw [filter_smul_finset]
          congr 1
          refine filter_congr fun y _ => ?_
          rw [comp_smul, smul_mem_smul_finset_iff]
        · funext y
          simp only [Option.smul_some, CohOut.smul_bip, comp_smul',
            image_singleton_smul_finset, bipEdge_relab]
      · rw [ite_eq_right (fun h => hG (smul_finset_nonempty.1 h)), ite_eq_right hG]
        by_cases hg : (cols.erase v).Nonempty
        · rw [dite_eq_left hg, dite_eq_left hg]
          simp only [CTree.act, Option.smul_some, CohOut.smul_bip, bipEdge_relab]
          rw [image_smul_finset]
          simp only [comp_smul]
          rw [image_smul_comp]
        · rw [dite_eq_right hg, dite_eq_right hg]
          rfl
    · rw [dite_eq_right (show ¬ _ by rw [Ebig]; exact hv), dite_eq_right hv]
      simp only [CTree.act]
      congr 1
      funext w
      simp only [Option.smul_some, CohOut.smul_part, colPart_smul', relab2_apply,
        inv_smul_smul]
  · rw [dite_eq_right (show ¬ (disconn (σ • C₂) (relab2 σ c)).Nonempty by rw [E2]; exact h₂),
      dite_eq_right h₂]
    simp only [CTree.act]
    congr 1
    funext y
    obtain ⟨y, rfl⟩ : ∃ y₀, y = σ • y₀ := ⟨σ⁻¹ • y, (smul_inv_smul σ y).symm⟩
    rw [inv_smul_smul]
    have Ebig : (cols.filter fun k =>
        (σ • C₁).card < 2 * ((σ • C₁).filter fun x => relab2 σ c x (σ • y) = k).card) =
        cols.filter fun k => C₁.card < 2 * (C₁.filter fun x => c x y = k).card := by
      refine filter_congr fun k _ => ?_
      simp only [card_smul_finset, card_filter_smul_finset, relab2_smul]
    by_cases hv : (cols.filter fun k =>
        C₁.card < 2 * (C₁.filter fun x => c x y = k).card).Nonempty
    · rw [dite_eq_left (show _ by rw [Ebig]; exact hv), dite_eq_left hv, min'_congr Ebig]
      generalize (cols.filter fun k =>
        C₁.card < 2 * (C₁.filter fun x => c x y = k).card).min' hv = v
      have Eblue : ((offCols (σ • C₂) (relab2 σ c)).filter fun b =>
          0 < ((σ • C₂).filter fun z => relab2 σ c (σ • y) z = b).card ∧
            2 * ((σ • C₂).filter fun z => relab2 σ c (σ • y) z = b).card < (σ • C₂).card) =
          (offCols C₂ c).filter fun b => 0 < (C₂.filter fun z => c y z = b).card ∧
            2 * (C₂.filter fun z => c y z = b).card < C₂.card := by
        rw [offCols_smul]
        refine filter_congr fun b _ => ?_
        simp only [card_smul_finset, card_filter_smul_finset, relab2_smul]
      by_cases hb : ((offCols C₂ c).filter fun b => 0 < (C₂.filter fun z => c y z = b).card ∧
            2 * (C₂.filter fun z => c y z = b).card < C₂.card).Nonempty
      · rw [dite_eq_left (show _ by rw [Eblue]; exact hb), dite_eq_left hb, min'_congr Eblue]
        simp only [CTree.act, Option.smul_some, CohOut.smul_bip, bipEdge_relab]
        rw [filter_smul_finset, filter_smul_finset, image_singleton_smul_finset]
        simp only [relab2_smul]
      · rw [dite_eq_right (show ¬ _ by rw [Eblue]; exact hb), dite_eq_right hb]
        rfl
    · rw [dite_eq_right (show ¬ _ by rw [Ebig]; exact hv), dite_eq_right hv]
      simp only [CTree.act, Option.smul_some, CohOut.smul_part, colPart_smul', relab2_smul]


end GraphIso.SplitJohnson
