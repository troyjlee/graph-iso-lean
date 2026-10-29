module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Twins in bipartite graphs

A bipartite graph is `(V₁, V₂; A)` with `V₁ : Finset X`, `V₂ : Finset Y` and
`A : X → Y → Bool`. Two points of `V₁` are **twins** if they have the same neighbours in `V₂`;
`twinCls V₁ V₂ A x` is the twin class of `x` in `V₁` (Helfgott, §5.2).

* `two_mul_card_twinCls_le` (Exercise 5.4): in a nontrivial semiregular bipartite graph no
  twin class has more than half of `V₁`.
* `twin_split` (Exercise 5.5): if `V₁` has no twins with respect to `C ∪ C'`, then with respect
  to `C` or to `C'` it has no twin class of `|V₁|/2 + 1` or more points.
-/

@[expose] public section

namespace GraphIso.Coherent

open Finset

variable {X Y : Type*}

/-- The twin class of `x` in `V₁` with respect to `(V₂, A)`. -/
def twinCls (V₁ : Finset X) (V₂ : Finset Y) (A : X → Y → Bool) (x : X) : Finset X :=
  V₁.filter fun x' => ∀ y ∈ V₂, A x y = A x' y

theorem mem_twinCls {V₁ : Finset X} {V₂ : Finset Y} {A : X → Y → Bool} {x x' : X} :
    x' ∈ twinCls V₁ V₂ A x ↔ x' ∈ V₁ ∧ ∀ y ∈ V₂, A x y = A x' y := by
  simp [twinCls]

theorem self_mem_twinCls {V₁ : Finset X} {V₂ : Finset Y} {A : X → Y → Bool} {x : X}
    (hx : x ∈ V₁) : x ∈ twinCls V₁ V₂ A x := by
  simp [twinCls, hx]

theorem twinCls_eq_of_mem {V₁ : Finset X} {V₂ : Finset Y} {A : X → Y → Bool} {x x' : X}
    (h : x' ∈ twinCls V₁ V₂ A x) : twinCls V₁ V₂ A x' = twinCls V₁ V₂ A x := by
  rw [mem_twinCls] at h
  ext z
  rw [mem_twinCls, mem_twinCls]
  constructor
  · rintro ⟨hz, hzy⟩
    exact ⟨hz, fun y hy => (h.2 y hy).trans (hzy y hy)⟩
  · rintro ⟨hz, hzy⟩
    exact ⟨hz, fun y hy => (h.2 y hy).symm.trans (hzy y hy)⟩

/-- Twin classes with respect to a subset of `V₂` are larger. -/
theorem twinCls_mono {V₁ : Finset X} {V₂ W₂ : Finset Y} {A : X → Y → Bool} (h : W₂ ⊆ V₂)
    (x : X) : twinCls V₁ V₂ A x ⊆ twinCls V₁ W₂ A x := by
  intro z hz
  rw [mem_twinCls] at hz ⊢
  exact ⟨hz.1, fun y hy => hz.2 y (h hy)⟩

/-- **Exercise 5.4**: in a nontrivial semiregular bipartite graph no twin class has more than
half of the first side. -/
theorem two_mul_card_twinCls_le {V₁ : Finset X} {V₂ : Finset Y} {A : X → Y → Bool} {a b : ℕ}
    (h₁ : ∀ x ∈ V₁, (V₂.filter fun y => A x y).card = a)
    (h₂ : ∀ y ∈ V₂, (V₁.filter fun x => A x y).card = b)
    (hne : ∃ x ∈ V₁, ∃ y ∈ V₂, A x y = true) (hnc : ∃ x ∈ V₁, ∃ y ∈ V₂, A x y = false)
    {x : X} (hx : x ∈ V₁) : 2 * (twinCls V₁ V₂ A x).card ≤ V₁.card := by
  obtain ⟨x0, hx0, y0, hy0, hA0⟩ := hne
  obtain ⟨x1, hx1, y1, hy1, hA1⟩ := hnc
  -- `x` has a neighbour `y` and a non-neighbour `y'`
  have hy : ∃ y ∈ V₂, A x y = true := by
    have hpos : 0 < (V₂.filter fun y => A x y).card := by
      rw [h₁ x hx, ← h₁ x0 hx0]
      exact card_pos.2 ⟨y0, mem_filter.2 ⟨hy0, hA0⟩⟩
    obtain ⟨y, hy⟩ := card_pos.1 hpos
    exact ⟨y, (mem_filter.1 hy).1, (mem_filter.1 hy).2⟩
  have hy' : ∃ y ∈ V₂, A x y = false := by
    by_contra hcon
    push Not at hcon
    have h1 : (V₂.filter fun y => A x y).card = V₂.card := by
      rw [filter_true_of_mem]
      intro y hy
      simpa using hcon y hy
    have h2 : (V₂.filter fun y => A x1 y).card < V₂.card :=
      card_lt_card (filter_ssubset.2 ⟨y1, hy1, by simp [hA1]⟩)
    rw [h₁ x1 hx1, ← h₁ x hx, h1] at h2
    exact lt_irrefl _ h2
  obtain ⟨y, hyV, hAy⟩ := hy
  obtain ⟨y', hy'V, hAy'⟩ := hy'
  -- the class lies among the neighbours of `y` and among the non-neighbours of `y'`
  have hT1 : twinCls V₁ V₂ A x ⊆ V₁.filter fun x' => A x' y = true := by
    intro x' hx'
    rw [mem_twinCls] at hx'
    exact mem_filter.2 ⟨hx'.1, by rw [← hx'.2 y hyV]; exact hAy⟩
  have hT2 : twinCls V₁ V₂ A x ⊆ V₁.filter fun x' => ¬ (A x' y' = true) := by
    intro x' hx'
    rw [mem_twinCls] at hx'
    exact mem_filter.2 ⟨hx'.1, by rw [← hx'.2 y' hy'V, hAy']; simp⟩
  have hc1 := card_le_card hT1
  have hc2 := card_le_card hT2
  have hsplit := card_filter_add_card_filter_not (s := V₁) fun x' => A x' y' = true
  rw [h₂ y hyV] at hc1
  rw [h₂ y' hy'V] at hsplit
  omega

/-- **Exercise 5.5**: if `V₁` has no twins with respect to `C ∪ C'`, then with respect to `C`
or to `C'` it has no twin class of `|V₁|/2 + 1` or more points. -/
theorem twin_split {V₁ : Finset X} [DecidableEq Y] {C C' : Finset Y} {A : X → Y → Bool}
    (htf : ∀ x ∈ V₁, twinCls V₁ (C ∪ C') A x = {x}) :
    (∀ x ∈ V₁, 2 * (twinCls V₁ C A x).card < V₁.card + 2) ∨
      (∀ x ∈ V₁, 2 * (twinCls V₁ C' A x).card < V₁.card + 2) := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨x, hx, hT⟩, ⟨x', hx', hT'⟩⟩ := hcon
  have hTV : twinCls V₁ C A x ⊆ V₁ := filter_subset _ _
  have hT'V : twinCls V₁ C' A x' ⊆ V₁ := filter_subset _ _
  have hu := card_le_card (union_subset hTV hT'V)
  have hui := card_union_add_card_inter (twinCls V₁ C A x) (twinCls V₁ C' A x')
  have h2 : 1 < (twinCls V₁ C A x ∩ twinCls V₁ C' A x').card := by omega
  obtain ⟨z₁, hz₁, z₂, hz₂, hne⟩ := one_lt_card.1 h2
  rw [mem_inter, mem_twinCls, mem_twinCls] at hz₁ hz₂
  have hmem : z₂ ∈ twinCls V₁ (C ∪ C') A z₁ := by
    rw [mem_twinCls]
    refine ⟨hz₂.1.1, fun y hy => ?_⟩
    rcases mem_union.1 hy with hy | hy
    · exact (hz₁.1.2 y hy).symm.trans (hz₂.1.2 y hy)
    · exact (hz₁.2.2 y hy).symm.trans (hz₂.2.2 y hy)
  rw [htf z₁ hz₁.1.1, mem_singleton] at hmem
  exact hne hmem.symm

end GraphIso.Coherent
