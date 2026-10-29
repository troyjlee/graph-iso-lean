module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Rat.Defs
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Fisher's inequality

**Fisher's inequality** (Helfgott, Prop. 2.19): a family of blocks `A : B → Finset P` in which
every point lies in `r` blocks and every pair of distinct points in `l < r` blocks has at least
as many blocks as points (`fisher_inequality`). Repeated blocks are allowed, and `l = 0` is
allowed (the degenerate case).

The proof is the classical linear-algebra one. The `ℚ`-linear map
`x ↦ (b ↦ Σ_{p ∈ A b} x p)` from `P → ℚ` to `B → ℚ` satisfies
`Σ_b (Σ_{p ∈ A b} x p)² = (r − l) Σ_p x_p² + l (Σ_p x_p)²` (`sum_sq_blocks`), so it is
injective when `l < r`, and the dimension of its domain is at most that of its codomain.
-/

@[expose] public section

namespace GraphIso.Coherent

open Finset

section Fisher

variable {P B : Type*} [Fintype P] [DecidableEq P] [Fintype B]

/-- The sum of the squares of the block sums of `x`. -/
theorem sum_sq_blocks (A : B → Finset P) {r l : ℕ}
    (hr : ∀ p, (univ.filter fun b => p ∈ A b).card = r)
    (hl : ∀ p q, p ≠ q → (univ.filter fun b => p ∈ A b ∧ q ∈ A b).card = l) (x : P → ℚ) :
    ∑ b, (∑ p ∈ A b, x p) ^ 2 = ((r : ℚ) - l) * ∑ p, x p ^ 2 + l * (∑ p, x p) ^ 2 := by
  have h1 : ∀ b, (∑ p ∈ A b, x p) ^ 2 =
      ∑ p, ∑ q, if p ∈ A b ∧ q ∈ A b then x p * x q else 0 := by
    intro b
    have e : ∑ p ∈ A b, x p = ∑ p, if p ∈ A b then x p else 0 := by
      rw [sum_ite_mem, univ_inter]
    rw [e, sq, sum_mul_sum]
    refine sum_congr rfl fun p _ => sum_congr rfl fun q _ => ?_
    by_cases hp : p ∈ A b <;> by_cases hq : q ∈ A b <;> simp [hp, hq]
  have h2 : ∀ p q, (∑ b, if p ∈ A b ∧ q ∈ A b then x p * x q else (0 : ℚ)) =
      x p * x q * ((if p = q then (r : ℚ) else l)) := by
    intro p q
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
    congr 1
    by_cases hpq : p = q
    · subst hpq
      simp only [and_self, ite_true, hr p]
    · simp only [hpq, ite_false, hl p q hpq]
  simp_rw [h1]
  rw [sum_comm]
  simp_rw [sum_comm (s := (univ : Finset B)), h2]
  have h3 : ∀ p q, x p * x q * (if p = q then (r : ℚ) else l) =
      l * (x p * x q) + if p = q then ((r : ℚ) - l) * x p ^ 2 else 0 := by
    intro p q
    by_cases hpq : p = q
    · subst hpq
      simp only [ite_true]
      ring
    · simp only [hpq, ite_false]
      ring
  simp_rw [h3, sum_add_distrib, sum_ite_eq, mem_univ, ite_true, ← mul_sum]
  rw [sq (∑ p, x p), sum_mul_sum]
  simp_rw [← mul_sum]
  ring

end Fisher

/-- **Fisher's inequality** (Helfgott, Prop. 2.19), with repeated blocks allowed: if every point
lies in `r` blocks, every pair of distinct points in `l` blocks, and `l < r`, then there are at
least as many blocks as points. -/
theorem fisher_inequality {P B : Type*} [Fintype P] [DecidableEq P] [Fintype B]
    (A : B → Finset P) {r l : ℕ} (hr : ∀ p, (univ.filter fun b => p ∈ A b).card = r)
    (hl : ∀ p q, p ≠ q → (univ.filter fun b => p ∈ A b ∧ q ∈ A b).card = l) (hlr : l < r) :
    Fintype.card P ≤ Fintype.card B := by
  let f : (P → ℚ) →ₗ[ℚ] (B → ℚ) :=
    { toFun := fun x b => ∑ p ∈ A b, x p
      map_add' := fun x y => by
        funext b
        simp [sum_add_distrib]
      map_smul' := fun a x => by
        funext b
        simp [mul_sum] }
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have hb : ∀ b, ∑ p ∈ A b, x p = 0 := fun b => congrFun hx b
    have hs := sum_sq_blocks A hr hl x
    simp only [hb, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sum_const_zero]
      at hs
    have hrl : (0 : ℚ) < (r : ℚ) - l := by
      have : (l : ℚ) < r := by exact_mod_cast hlr
      linarith
    have hnn1 : 0 ≤ ∑ p, x p ^ 2 := sum_nonneg fun p _ => sq_nonneg _
    have hnn2 : (0 : ℚ) ≤ l * (∑ p, x p) ^ 2 := mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
    have hsum : ∑ p, x p ^ 2 = 0 := by nlinarith
    funext p
    have := (sum_eq_zero_iff_of_nonneg fun q _ => sq_nonneg (x q)).1 hsum p (mem_univ p)
    simpa using this
  have := LinearMap.finrank_le_finrank_of_injective hinj
  simpa only [Module.finrank_fintype_fun_eq_card] using this

end GraphIso.Coherent
