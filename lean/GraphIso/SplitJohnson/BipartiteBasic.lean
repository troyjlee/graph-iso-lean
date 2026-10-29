module

public import GraphIso.SplitJohnson.BipartiteDef

/-!
# Bipartite Split-or-Johnson: the invariant and dropped pieces

`BInv t V₁ V₂ A` is the invariant of the recursion (Helfgott, Prop. 5.7, with a fixed threshold
`t`): the cells of `V₂` are nonempty and pairwise disjoint, `|V₂| ≤ t`, `|V₁| + 2 ≤ 2t`,
`t < |V₁|`, and no twin class of `V₁` has more than `t` points.

Dropped pieces preserve validity: adding a set `D` of at most `t` points, disjoint from `W`, as
a new colour class with one block turns a colored `t`-partition of `W` into one of `D ∪ W`
(`isColPart_addPiece`), and a Johnson embedding in `W` is one in any superset
(`isJohnson_mono`). `colPart_valid`: a colouring whose classes have at most `t` points, each
class one block, is a colored `t`-partition.
-/

@[expose] public section

namespace GraphIso.SplitJohnson

open Finset Pointwise GraphIso.Coherent

variable {α : Type*} [DecidableEq α]

/-- **The invariant of Bipartite Split-or-Johnson.** -/
structure BInv (t : ℕ) (V₁ : Finset α) (V₂ : Finset (Finset α)) (A : α → Finset α → Bool) :
    Prop where
  cells_ne : ∀ s ∈ V₂, s.Nonempty
  cells_disj : ∀ s ∈ V₂, ∀ s' ∈ V₂, s ≠ s' → Disjoint s s'
  v_le : V₂.card ≤ t
  v₁_le : V₁.card + 2 ≤ 2 * t
  t_lt : t < V₁.card
  twin_le : ∀ x ∈ V₁, (twinCls V₁ V₂ A x).card ≤ t

omit [DecidableEq α] in
/-- A colouring whose classes have at most `t` points, each class one block. -/
theorem colPart_valid {V : Finset α} {t : ℕ} {f : α → ℕ}
    (h : ∀ x ∈ V, (V.filter fun y => f y = f x).card ≤ t) : IsColPart V t (colPart V f) where
  mem_blk v hv := mem_filter.2 ⟨hv, rfl⟩
  blk_sub v _ := filter_subset _ _
  blk_eq v _ w hw := by
    have hw' := (mem_filter.1 hw).2
    simp only [colPart, hw']
  col_eq v _ w hw := (mem_filter.1 hw).2
  card_eq v _ w _ hvw := by
    change f v = f w at hvw
    simp only [colPart, hvw]
  admissible v hv h1 w hw hwv := by
    have hvb : v ∈ (colPart V f).blk v := mem_filter.2 ⟨hv, rfl⟩
    have hwb : w ∈ (colPart V f).blk v := mem_filter.2 ⟨hw, hwv⟩
    exact card_le_one.1 h1.le w hwb v hvb
  card_le v hv := h v hv

/-- **Adding a dropped piece.** -/
theorem isColPart_addPiece {W D : Finset α} {t : ℕ} {p : CPart α} (hp : IsColPart W t p)
    (hD : Disjoint D W) (hDt : D.card ≤ t) : IsColPart (D ∪ W) t (addPiece D p) := by
  have hW : ∀ v ∈ D ∪ W, v ∉ D → v ∈ W := fun v hv hvD => (mem_union.1 hv).resolve_left hvD
  have hnD : ∀ v ∈ W, v ∉ D := fun v hv hvD => disjoint_left.1 hD hvD hv
  refine ⟨fun v hv => ?_, fun v hv => ?_, fun v hv w hw => ?_, fun v hv w hw => ?_,
    fun v hv w hw hvw => ?_, fun v hv h1 w hw hwv => ?_, fun v hv => ?_⟩
  · by_cases hvD : v ∈ D
    · simp only [addPiece, hvD, ↓reduceIte]
    · simp only [addPiece, hvD, ↓reduceIte]
      exact hp.mem_blk v (hW v hv hvD)
  · by_cases hvD : v ∈ D
    · simp only [addPiece, hvD, ↓reduceIte]
      exact subset_union_left
    · simp only [addPiece, hvD, ↓reduceIte]
      exact (hp.blk_sub v (hW v hv hvD)).trans subset_union_right
  · by_cases hvD : v ∈ D
    · simp only [addPiece, hvD, ↓reduceIte] at hw ⊢
      simp only [hw, ↓reduceIte]
    · simp only [addPiece, hvD, ↓reduceIte] at hw ⊢
      have hwW := hp.blk_sub v (hW v hv hvD) hw
      simp only [hnD w hwW, ↓reduceIte]
      exact hp.blk_eq v (hW v hv hvD) w hw
  · by_cases hvD : v ∈ D
    · simp only [addPiece, hvD, ↓reduceIte] at hw ⊢
      simp only [hw, ↓reduceIte]
    · simp only [addPiece, hvD, ↓reduceIte] at hw ⊢
      have hwW := hp.blk_sub v (hW v hv hvD) hw
      simp only [hnD w hwW, ↓reduceIte]
      rw [hp.col_eq v (hW v hv hvD) w hw]
  · by_cases hvD : v ∈ D
    · by_cases hwD : w ∈ D
      · simp only [addPiece, hvD, hwD, ↓reduceIte]
      · simp only [addPiece, hvD, hwD, ↓reduceIte] at hvw
        omega
    · by_cases hwD : w ∈ D
      · simp only [addPiece, hvD, hwD, ↓reduceIte] at hvw
        omega
      · simp only [addPiece, hvD, hwD, ↓reduceIte] at hvw ⊢
        exact hp.card_eq v (hW v hv hvD) w (hW w hw hwD) (by omega)
  · by_cases hvD : v ∈ D
    · simp only [addPiece, hvD, ↓reduceIte] at h1 hwv
      by_cases hwD : w ∈ D
      · exact card_le_one.1 h1.le w hwD v hvD
      · simp only [hwD, ↓reduceIte] at hwv
        omega
    · simp only [addPiece, hvD, ↓reduceIte] at h1 hwv
      by_cases hwD : w ∈ D
      · simp only [hwD, ↓reduceIte] at hwv
        omega
      · simp only [hwD, ↓reduceIte] at hwv
        exact hp.admissible v (hW v hv hvD) h1 w (hW w hw hwD) (by omega)
  · by_cases hvD : v ∈ D
    · simp only [addPiece, hvD, ↓reduceIte]
      exact hDt
    · simp only [addPiece, hvD, ↓reduceIte]
      exact hp.card_le v (hW v hv hvD)

omit [DecidableEq α] in
theorem isJohnson_mono {W V : Finset α} {t : ℕ} {J : JEmb α} (h : IsJohnson W t J)
    (hWV : W ⊆ V) : IsJohnson V t J :=
  { h with sub := h.sub.trans hWV }

theorem validOut_addPieceOut {W D : Finset α} {t : ℕ} {o : Option (Out α)}
    (h : ValidOut W t o) (hD : Disjoint D W) (hDt : D.card ≤ t) :
    ValidOut (D ∪ W) t (addPieceOut D o) := by
  match o, h with
  | some (Sum.inl p), h => exact isColPart_addPiece h hD hDt
  | some (Sum.inr J), h => exact isJohnson_mono h subset_union_right

/-- **A tree with a dropped piece.** -/
theorem withPiece_valid {W D : Finset α} {t : ℕ} {T : STree α}
    (hT : T.Live ∧ T.AllLeaves (ValidOut W t)) (hD : Disjoint D W) (hDt : D.card ≤ t) :
    (withPiece D T).Live ∧ (withPiece D T).AllLeaves (ValidOut (D ∪ W) t) :=
  ⟨CTree.live_bind hT.1 (hT.2.mono fun _ _ => trivial),
    CTree.allLeaves_bind (hT.2.mono fun _ ho => validOut_addPieceOut ho hD hDt)⟩

theorem count_withPiece (D : Finset α) (T : STree α) : (withPiece D T).count = T.count := by
  unfold withPiece
  induction T with
  | leaf o => rfl
  | node S k ih =>
    simp only [CTree.bind, CTree.count]
    exact sum_congr rfl fun c _ => ih c

end GraphIso.SplitJohnson
