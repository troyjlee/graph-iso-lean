module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# Commutators of permutations with overlapping supports

Stage 16a. For permutations `x, y` with `I = supp x ∩ supp y`, the commutator `⁅x, y⁆` moves only
points of `I ∪ x(I) ∪ y(I)` (`support_commutatorElement_subset`), so at most `3 |I|` points
(`card_support_commutatorElement_le`). If `I` is a single point and `⁅x, y⁆ ≠ 1`, then `⁅x, y⁆`
is a `3`-cycle (`isThreeCycle_commutatorElement`): it is even and moves at most three points.
-/

@[expose] public section

namespace GraphIso.Wielandt

open Equiv Equiv.Perm Finset
open scoped commutatorElement

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **The support of a commutator:** `supp ⁅x, y⁆ ⊆ I ∪ x(I) ∪ y(I)`, `I = supp x ∩ supp y`. -/
theorem support_commutatorElement_subset (x y : Perm α) :
    ⁅x, y⁆.support ⊆ (x.support ∩ y.support) ∪ (x.support ∩ y.support).image x ∪
      (x.support ∩ y.support).image y := by
  intro w hw
  rw [mem_support, commutatorElement_def] at hw
  simp only [Perm.coe_mul, Perm.coe_inv, Function.comp_apply] at hw
  simp only [mem_union, mem_image, mem_inter, mem_support]
  by_cases hxw : x w = w <;> by_cases hyw : y w = w
  · exfalso
    apply hw
    have h1 : y.symm w = w := by rw [Equiv.symm_apply_eq]; exact hyw.symm
    have h2 : x.symm w = w := by rw [Equiv.symm_apply_eq]; exact hxw.symm
    rw [h1, h2, hyw, hxw]
  · -- `x` fixes `w` and `y` moves it: `y⁻¹ w` is moved by `x`
    by_cases h2 : x (y.symm w) = y.symm w
    · exfalso
      apply hw
      have h3 : x.symm (y.symm w) = y.symm w := by rw [Equiv.symm_apply_eq]; exact h2.symm
      rw [h3, Equiv.apply_symm_apply, hxw]
    · refine Or.inr ⟨y.symm w, ⟨h2, ?_⟩, Equiv.apply_symm_apply _ _⟩
      rw [Equiv.apply_symm_apply]
      intro h
      apply hyw
      calc y w = y (y.symm w) := by rw [← h]
        _ = w := Equiv.apply_symm_apply _ _
  · -- `x` moves `w` and `y` fixes it: `x⁻¹ w` is moved by `y`
    have h1 : y.symm w = w := by rw [Equiv.symm_apply_eq]; exact hyw.symm
    by_cases h2 : y (x.symm w) = x.symm w
    · exfalso
      apply hw
      rw [h1, h2, Equiv.apply_symm_apply]
    · refine Or.inl (Or.inr ⟨x.symm w, ⟨?_, h2⟩, Equiv.apply_symm_apply _ _⟩)
      rw [Equiv.apply_symm_apply]
      intro h
      apply hxw
      calc x w = x (x.symm w) := by rw [← h]
        _ = w := Equiv.apply_symm_apply _ _
  · exact Or.inl (Or.inl ⟨hxw, hyw⟩)

/-- `|supp ⁅x, y⁆| ≤ 3 |supp x ∩ supp y|`. -/
theorem card_support_commutatorElement_le (x y : Perm α) :
    #⁅x, y⁆.support ≤ 3 * #(x.support ∩ y.support) := by
  refine (card_le_card (support_commutatorElement_subset x y)).trans ?_
  refine (card_union_le _ _).trans ?_
  have h1 := card_union_le (x.support ∩ y.support) ((x.support ∩ y.support).image x)
  have h2 := card_image_le (s := x.support ∩ y.support) (f := x)
  have h3 := card_image_le (s := x.support ∩ y.support) (f := y)
  omega

/-- A commutator of permutations is even. -/
theorem sign_commutatorElement (x y : Perm α) : sign ⁅x, y⁆ = 1 := by
  rw [map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)

/-- **A `3`-cycle from a single overlap:** if `supp x ∩ supp y` has one point and `⁅x, y⁆ ≠ 1`,
then `⁅x, y⁆` is a `3`-cycle. -/
theorem isThreeCycle_commutatorElement {x y : Perm α} (h1 : #(x.support ∩ y.support) = 1)
    (hne : ⁅x, y⁆ ≠ 1) : ⁅x, y⁆.IsThreeCycle := by
  have hle := card_support_commutatorElement_le x y
  rw [h1] at hle
  have h2 := two_le_card_support_of_ne_one hne
  rw [← card_support_eq_three_iff]
  rcases (show #⁅x, y⁆.support = 2 ∨ #⁅x, y⁆.support = 3 by omega) with h | h
  · have hs := (card_support_eq_two.mp h).sign_eq
    rw [sign_commutatorElement] at hs
    exact absurd hs (by decide)
  · exact h

end GraphIso.Wielandt
