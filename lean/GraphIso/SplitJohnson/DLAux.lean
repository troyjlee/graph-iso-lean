module

public import GraphIso.SplitJohnson.BipartiteBasic
public import GraphIso.Coherent.Skeleton
public import Mathlib.Tactic.FinCases

/-!
# Bipartite Split-or-Johnson: auxiliary facts for the step after the Design Lemma

* `selThird_spec`: if every colour class of `S` has at most `2|S|/3` points, `selThird` takes
  more than a third and at most two thirds of `S`.
* `pickSide_twin`: if `V₁` has no twins with respect to `V₂ ⊇ S`, the side chosen by
  `pickSide` leaves twin classes below `|V₁|/2 + 1` (Exercise 5.5).
* `isCoherent2_pair`, `isCoh2On_univ`, `isCoh2On_cohOn`, `cohOn_refines`: the classical
  Weisfeiler–Leman refinement `cohOn S c₀` is a classical coherent configuration on `S` that
  refines `c₀`; facts about the initial colours `code`.
* `isColPart_toLeft`: a colored partition of `S.map inl` pulls back to one of `S`.
* `cellOf`: the union of the cells of an ideal point.
-/

@[expose] public section

namespace GraphIso.SplitJohnson

open Finset Pointwise GraphIso.Coherent

variable {α : Type*} [DecidableEq α]

/-! ### `selThird` -/

/-- **`selThird` takes a third.** -/
theorem selThird_spec {β : Type*} [DecidableEq β] (S : Finset β) (col : β → ℕ)
    (hS : S.Nonempty) (h : ∀ x ∈ S, 3 * (S.filter fun y => col y = col x).card ≤ 2 * S.card) :
    selThird S col ⊆ S ∧ S.card < 3 * (selThird S col).card ∧
      3 * (selThird S col).card ≤ 2 * S.card := by
  suffices H : ∀ T, selThird S col = T →
      T ⊆ S ∧ S.card < 3 * T.card ∧ 3 * T.card ≤ 2 * S.card from H _ rfl
  intro T hT
  have hmem : ∀ k, k ∈ (S.image col).sort (· ≤ ·) ↔ ∃ x ∈ S, col x = k := fun k => by
    rw [Finset.mem_sort, mem_image]
  unfold selThird at hT
  dsimp only at hT
  split at hT
  · rename_i k hk
    subst hT
    have hp := List.find?_some hk
    obtain ⟨x, hx, rfl⟩ := (hmem _).1 (List.mem_of_find?_eq_some hk)
    simp only [decide_eq_true_eq] at hp
    exact ⟨filter_subset _ _, hp, h x hx⟩
  · rename_i hk
    rw [List.find?_eq_none] at hk
    set cols := (S.image col).sort (· ≤ ·) with hcols
    have hall : S.filter (fun x => col x ∈ cols) = S :=
      filter_true_of_mem fun x hx => (hmem _).2 ⟨x, hx, rfl⟩
    have hlen : S.card < 3 * (S.filter fun x => col x ∈ cols.take cols.length).card := by
      rw [List.take_length, hall]
      have := hS.card_pos
      omega
    have hsome : ((List.range (cols.length + 1)).find? fun m =>
        decide (S.card < 3 * (S.filter fun x => col x ∈ cols.take m).card)).isSome := by
      rw [List.find?_isSome]
      exact ⟨cols.length, List.mem_range.2 (by omega), by simpa using hlen⟩
    obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1 hsome
    rw [hm, Option.getD_some] at hT
    subst hT
    rw [List.find?_range_eq_some] at hm
    obtain ⟨hq, hmr, hlt⟩ := hm
    simp only [decide_eq_true_eq] at hq
    have hm0 : m ≠ 0 := by
      rintro rfl
      simp at hq
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    have hj := hlt j (by omega)
    simp only [Bool.not_eq_true', decide_eq_false_iff_not, not_lt] at hj
    have hjl : j < cols.length := by
      have := List.mem_range.1 hmr
      omega
    have hk' := hk cols[j] (List.getElem_mem hjl)
    simp only [decide_eq_true_eq, not_lt] at hk'
    have hsub : (S.filter fun x => col x ∈ cols.take (j + 1)) ⊆
        (S.filter fun x => col x ∈ cols.take j) ∪ S.filter fun x => col x = cols[j] := by
      intro x hx
      rw [mem_filter, List.take_add_one, List.getElem?_eq_getElem hjl] at hx
      simp only [Option.toList_some, List.mem_append, List.mem_singleton] at hx
      rcases hx.2 with h1 | h1
      · exact mem_union_left _ (mem_filter.2 ⟨hx.1, h1⟩)
      · exact mem_union_right _ (mem_filter.2 ⟨hx.1, h1⟩)
    have := (card_le_card hsub).trans (card_union_le _ _)
    exact ⟨filter_subset _ _, hq, by omega⟩

/-! ### `pickSide` -/

theorem pickSide_subset (V₁ : Finset α) {V₂ S : Finset (Finset α)} (A : α → Finset α → Bool)
    (hS : S ⊆ V₂) : pickSide V₁ V₂ S A ⊆ V₂ := by
  unfold pickSide
  split_ifs
  · exact hS
  · exact sdiff_subset

theorem pickSide_card (V₁ : Finset α) (V₂ S : Finset (Finset α)) (A : α → Finset α → Bool) :
    (pickSide V₁ V₂ S A).card = S.card ∨ (pickSide V₁ V₂ S A).card = (V₂ \ S).card := by
  unfold pickSide
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- **Exercise 5.5 for `pickSide`.** -/
theorem pickSide_twin {V₁ : Finset α} {V₂ S : Finset (Finset α)} {A : α → Finset α → Bool}
    (htf : ∀ x ∈ V₁, twinCls V₁ V₂ A x = {x}) (hS : S ⊆ V₂) :
    ∀ x ∈ V₁, 2 * (twinCls V₁ (pickSide V₁ V₂ S A) A x).card < V₁.card + 2 := by
  unfold pickSide
  split_ifs with hc
  · exact hc
  · have htf' : ∀ x ∈ V₁, twinCls V₁ (S ∪ (V₂ \ S)) A x = {x} := by
      rw [union_sdiff_of_subset hS]
      exact htf
    rcases twin_split htf' with h1 | h2
    · exact absurd h1 hc
    · exact h2

/-! ### The classical refinement -/

/-- A binary coherent configuration, read on pairs, is a classical one. -/
theorem isCoherent2_pair {V : Type*} [Fintype V] {c : (Fin 2 → V) → ℕ} (hc : IsCoherent c) :
    IsCoherent2 fun a b => c ![a, b] := by
  have h := isCoherent2_skel2 hc (x := []) (by simp)
  have e : (fun a b => c ![a, b]) = skel2 c [] := by
    funext a b
    unfold skel2
    congr 1
    funext i
    fin_cases i <;> simp [pad2]
  rw [e]
  exact h

/-- A classical coherent configuration on a finite type is one on `univ`. -/
theorem isCoh2On_univ {V : Type*} [Fintype V] [DecidableEq V] {c : V → V → ℕ}
    (hc : IsCoherent2 c) : IsCoh2On (univ : Finset V) c := by
  refine ⟨fun x y x' y' h => ?_, fun x y x' y' h r s => ?_⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hc.1 x y x' y' h
    refine ⟨?_, h2, h3, h4⟩
    rw [Subtype.ext_iff, Subtype.ext_iff]
    exact h1
  · have e := card_univ_filter_val (univ : Finset V) (fun z => c x z = r ∧ c z y = s)
    have e' := card_univ_filter_val (univ : Finset V) (fun z => c x' z = r ∧ c z y' = s)
    rw [e, e']
    exact hc.2 x y x' y' h r s

theorem cohOn_apply (S : Finset (α ⊕ Finset α)) (c₀ : α ⊕ Finset α → α ⊕ Finset α → ℕ)
    {a b : α ⊕ Finset α} (ha : a ∈ S) (hb : b ∈ S) :
    cohOn S c₀ a b =
      wlOn 2 (fun p : Fin 2 → S => c₀ (p 0).val (p 1).val) ![⟨a, ha⟩, ⟨b, hb⟩] := by
  unfold cohOn
  rw [dite_eq_left ⟨ha, hb⟩]

/-- **The classical refinement is coherent.** -/
theorem isCoh2On_cohOn (S : Finset (α ⊕ Finset α)) (c₀ : α ⊕ Finset α → α ⊕ Finset α → ℕ) :
    IsCoh2On S (cohOn S c₀) := by
  unfold IsCoh2On
  have e : (fun x y : S => cohOn S c₀ x y) =
      fun x y => wlOn 2 (fun p : Fin 2 → S => c₀ (p 0).val (p 1).val) ![x, y] := by
    funext x y
    rw [cohOn_apply S c₀ x.2 y.2]
  rw [e]
  exact isCoherent2_pair (wlOn_isCoherent _)

/-- **The classical refinement refines its input.** -/
theorem cohOn_refines {S : Finset (α ⊕ Finset α)} {c₀ : α ⊕ Finset α → α ⊕ Finset α → ℕ}
    {a b a' b' : α ⊕ Finset α} (ha : a ∈ S) (hb : b ∈ S) (ha' : a' ∈ S) (hb' : b' ∈ S)
    (h : cohOn S c₀ a b = cohOn S c₀ a' b') : c₀ a b = c₀ a' b' := by
  rw [cohOn_apply S c₀ ha hb, cohOn_apply S c₀ ha' hb'] at h
  have := wlOn_refines _ h
  simpa using this

omit [DecidableEq α] in
theorem code_inl_inr {A : α → Finset α → Bool} {Y : Finset α → Finset α → ℕ} {y y' : α}
    {s s' : Finset α} (h : code A Y (.inl y) (.inr s) = code A Y (.inl y') (.inr s')) :
    A y s = A y' s' := by
  simp only [code] at h
  rcases Bool.eq_false_or_eq_true (A y s) with h1 | h1 <;>
    rcases Bool.eq_false_or_eq_true (A y' s') with h2 | h2 <;> simp [h1, h2] at h ⊢

omit [DecidableEq α] in
theorem code_diag_ne (A : α → Finset α → Bool) (Y : Finset α → Finset α → ℕ) (y : α)
    (s : Finset α) : code A Y (.inl y) (.inl y) ≠ code A Y (.inr s) (.inr s) := by
  simp only [code]
  omega

omit [DecidableEq α] in
theorem code_inr_inr {A : α → Finset α → Bool} {Y : Finset α → Finset α → ℕ}
    {s s' r r' : Finset α} (h : code A Y (.inr s) (.inr s') = code A Y (.inr r) (.inr r')) :
    Y s s' = Y r r' := by
  simp only [code] at h
  omega

/-! ### Pulling partitions back along `inl` -/

omit [DecidableEq α] in
theorem card_toLeft_of_subset {S : Finset α} {B : Finset (α ⊕ Finset α)}
    (h : B ⊆ S.map ⟨Sum.inl, Sum.inl_injective⟩) : B.toLeft.card = B.card := by
  have hr : B.toRight = ∅ := by
    ext s
    simp only [mem_toRight, Finset.notMem_empty, iff_false]
    intro hs
    obtain ⟨y, -, hy⟩ := mem_map.1 (h hs)
    simp at hy
  have := card_toLeft_add_card_toRight (u := B)
  rw [hr, card_empty, add_zero] at this
  exact this

omit [DecidableEq α] in
/-- **A colored partition of `S.map inl` pulls back to one of `S`.** -/
theorem isColPart_toLeft {S : Finset α} {k : ℕ} {p : CPart (α ⊕ Finset α)}
    (hp : IsColPart (S.map ⟨Sum.inl, Sum.inl_injective⟩) k p) :
    IsColPart S k ⟨fun x => p.col (.inl x), fun x => (p.blk (.inl x)).toLeft⟩ := by
  have hm : ∀ x ∈ S, (Sum.inl x : α ⊕ Finset α) ∈ S.map ⟨Sum.inl, Sum.inl_injective⟩ :=
    fun x hx => mem_map.2 ⟨x, hx, rfl⟩
  have hc : ∀ x ∈ S, (p.blk (.inl x)).toLeft.card = (p.blk (.inl x)).card :=
    fun x hx => card_toLeft_of_subset (hp.blk_sub _ (hm x hx))
  refine ⟨fun x hx => ?_, fun x hx y hy => ?_, fun x hx y hy => ?_, fun x hx y hy => ?_,
    fun x hx y hy e => ?_, fun x hx h1 y hy e => ?_, fun x hx => ?_⟩
  · exact mem_toLeft.2 (hp.mem_blk _ (hm x hx))
  · have := hp.blk_sub _ (hm x hx) (mem_toLeft.1 hy)
    obtain ⟨z, hz, e⟩ := mem_map.1 this
    simp only [Function.Embedding.coeFn_mk, Sum.inl.injEq] at e
    exact e ▸ hz
  · show (p.blk (.inl y)).toLeft = (p.blk (.inl x)).toLeft
    rw [hp.blk_eq _ (hm x hx) _ (mem_toLeft.1 hy)]
  · exact hp.col_eq _ (hm x hx) _ (mem_toLeft.1 hy)
  · show (p.blk (.inl x)).toLeft.card = (p.blk (.inl y)).toLeft.card
    rw [hc x hx, hc y hy]
    exact hp.card_eq _ (hm x hx) _ (hm y hy) e
  · have h1' : (p.blk (.inl x)).card = 1 := by rw [← hc x hx]; exact h1
    have := hp.admissible _ (hm x hx) h1' _ (hm y hy) e
    simpa using this
  · show (p.blk (.inl x)).toLeft.card ≤ k
    rw [hc x hx]
    exact hp.card_le _ (hm x hx)

/-! ### Cells of ideal points -/

theorem mem_cellOf {B : Finset (α ⊕ Finset α)} {a : α} :
    a ∈ cellOf B ↔ ∃ s, (Sum.inr s : α ⊕ Finset α) ∈ B ∧ a ∈ s := by
  unfold cellOf
  rw [Finset.mem_sup]
  simp only [mem_toRight, id]

theorem cellOf_nonempty {V₂ : Finset (Finset α)} (hne : ∀ s ∈ V₂, s.Nonempty)
    {B : Finset (α ⊕ Finset α)} (hB : B.Nonempty)
    (hsub : B ⊆ V₂.map ⟨Sum.inr, Sum.inr_injective⟩) : (cellOf B).Nonempty := by
  obtain ⟨q, hq⟩ := hB
  obtain ⟨s, hs, rfl⟩ := mem_map.1 (hsub hq)
  obtain ⟨a, ha⟩ := hne s hs
  exact ⟨a, mem_cellOf.2 ⟨s, hq, ha⟩⟩

theorem cellOf_disjoint {V₂ : Finset (Finset α)}
    (hdisj : ∀ s ∈ V₂, ∀ s' ∈ V₂, s ≠ s' → Disjoint s s')
    {B B' : Finset (α ⊕ Finset α)} (hsub : B ⊆ V₂.map ⟨Sum.inr, Sum.inr_injective⟩)
    (hsub' : B' ⊆ V₂.map ⟨Sum.inr, Sum.inr_injective⟩) (hBB : Disjoint B B') :
    Disjoint (cellOf B) (cellOf B') := by
  rw [Finset.disjoint_left]
  intro a ha ha'
  obtain ⟨s, hs, has⟩ := mem_cellOf.1 ha
  obtain ⟨s', hs', has'⟩ := mem_cellOf.1 ha'
  obtain ⟨s₀, hs₀, e⟩ := mem_map.1 (hsub hs)
  obtain ⟨s₁, hs₁, e'⟩ := mem_map.1 (hsub' hs')
  simp only [Function.Embedding.coeFn_mk, Sum.inr.injEq] at e e'
  subst e e'
  by_cases hss : s₀ = s₁
  · subst hss
    exact Finset.disjoint_left.1 hBB hs hs'
  · exact Finset.disjoint_left.1 (hdisj _ hs₀ _ hs₁ hss) has has'

end GraphIso.SplitJohnson
