module

public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.GroupTheory.Perm.Cycle.PossibleTypes
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.Tactic.Linarith

/-!
# The primes of Lemma 12

Stage 15d. Pyber's Proposition 11 is replaced by Chebyshev's elementary lower bound, in the
natural-number form of mathlib: `2^N ≤ (N + 1) lcm(1, …, N)`
(`Chebyshev.two_pow_le_mul_lcmUpto`), and `lcm(1, …, N) = ∏_{p ≤ N} p^{⌊log_p N⌋} ≤ N^{π(N)}`
(`Nat.lcmUpto_eq_prod_pow_log`).

* **Many primes** (`card_primesLE_ge`): for `L ≥ 1`, `π(64 L³) ≥ 2 L² + 1`.
* **Odd primes** (`exists_odd_primes`): for `L ≥ 1` and `R ≤ 2 L²`, there are `R` distinct odd
  primes, each at most `64 L³`.
* **The permutation** (`exists_mem_alternatingGroup`): for a finite set `s` of odd primes with
  `∑ s ≤ |Λ|`, some even permutation of `Λ` has order divisible by every `p ∈ s`: its cycle
  type is `s` (`Equiv.Perm.exists_with_cycleType_iff`), and it is even because the cycle lengths
  are odd (`Equiv.Perm.sign_of_cycleType`).
-/

@[expose] public section

namespace GraphIso.Pyber

open Finset

/-- `lcm(1, …, N) ≤ N^{π(N)}`. -/
theorem lcmUpto_le_pow (N : ℕ) : Nat.lcmUpto N ≤ N ^ #(Nat.primesLE N) := by
  rw [Nat.lcmUpto_eq_prod_pow_log]
  apply Finset.prod_le_pow_card
  intro p hp
  have h1 := Nat.le_of_mem_primesLE hp
  have h2 := Nat.two_le_of_mem_primesLE hp
  exact Nat.pow_log_le_self p (by omega)

/-- **Chebyshev's elementary bound:** `2^N ≤ (N + 1) N^{π(N)}`. -/
theorem two_pow_le_mul_pow_card (N : ℕ) : 2 ^ N ≤ (N + 1) * N ^ #(Nat.primesLE N) :=
  (Chebyshev.two_pow_le_mul_lcmUpto N).trans (Nat.mul_le_mul_left _ (lcmUpto_le_pow N))

/-- **Many primes:** `π(64 L³) ≥ 2 L² + 1` for `L ≥ 1`. -/
theorem card_primesLE_ge {L : ℕ} (hL : 1 ≤ L) : 2 * L ^ 2 + 1 ≤ #(Nat.primesLE (64 * L ^ 3)) := by
  by_contra h
  have hc : #(Nat.primesLE (64 * L ^ 3)) ≤ 2 * L ^ 2 := by omega
  have h1 := two_pow_le_mul_pow_card (64 * L ^ 3)
  have hL3 : L ^ 3 < 2 ^ (3 * L) := by
    rw [pow_mul']
    exact Nat.pow_lt_pow_left Nat.lt_two_pow_self (by norm_num)
  have h64 : (2 : ℕ) ^ (3 * L + 6) = 2 ^ (3 * L) * 64 := by rw [pow_add]; norm_num
  have hN : 64 * L ^ 3 + 1 ≤ 2 ^ (3 * L + 6) := by omega
  have hN' : 64 * L ^ 3 ≤ 2 ^ (3 * L + 6) := by omega
  have hpos : 1 ≤ 64 * L ^ 3 := by
    have := Nat.one_le_pow 3 L hL
    omega
  have h2 : (64 * L ^ 3 + 1) * (64 * L ^ 3) ^ #(Nat.primesLE (64 * L ^ 3)) ≤
      2 ^ (3 * L + 6) * (2 ^ (3 * L + 6)) ^ (2 * L ^ 2) :=
    Nat.mul_le_mul hN ((Nat.pow_le_pow_right hpos hc).trans (Nat.pow_le_pow_left hN' _))
  have h3 : 2 ^ (3 * L + 6) * (2 ^ (3 * L + 6)) ^ (2 * L ^ 2) =
      2 ^ ((3 * L + 6) * (2 * L ^ 2 + 1)) := by
    rw [← pow_mul, ← pow_add]
    ring_nf
  have h4 : (3 * L + 6) * (2 * L ^ 2 + 1) < 64 * L ^ 3 := by
    have e1 : L ^ 2 ≤ L ^ 3 := Nat.pow_le_pow_right hL (by norm_num)
    have e2 : L ≤ L ^ 2 := by nlinarith
    nlinarith
  have h5 : 2 ^ ((3 * L + 6) * (2 * L ^ 2 + 1)) < 2 ^ (64 * L ^ 3) :=
    Nat.pow_lt_pow_right (by norm_num) h4
  omega

/-- **Odd primes for Lemma 12:** for `L ≥ 1` and `R ≤ 2 L²` there is a set of `R` odd primes,
each at most `64 L³`. -/
theorem exists_odd_primes {L R : ℕ} (hL : 1 ≤ L) (hR : R ≤ 2 * L ^ 2) :
    ∃ s : Finset ℕ, #s = R ∧ ∀ p ∈ s, p.Prime ∧ p ≠ 2 ∧ p ≤ 64 * L ^ 3 := by
  have h := card_primesLE_ge hL
  have h1 : R ≤ #((Nat.primesLE (64 * L ^ 3)).erase 2) := by
    have := Finset.pred_card_le_card_erase (s := Nat.primesLE (64 * L ^ 3)) (a := 2)
    omega
  obtain ⟨s, hs, hcard⟩ := Finset.exists_subset_card_eq h1
  refine ⟨s, hcard, fun p hp => ?_⟩
  have hp' := hs hp
  rw [Finset.mem_erase, Nat.mem_primesLE] at hp'
  exact ⟨hp'.2.2, hp'.1, hp'.2.1⟩

/-- **The permutation of Lemma 12:** for a finite set `s` of odd primes with `∑ s ≤ |Λ|`, there
is an even permutation of `Λ` whose order is divisible by every `p ∈ s`. -/
theorem exists_mem_alternatingGroup {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ p ≠ 2) (hsum : ∑ p ∈ s, p ≤ Fintype.card Λ) :
    ∃ σ ∈ alternatingGroup Λ, ∀ p ∈ s, p ∣ orderOf σ := by
  have hsum' : s.val.sum ≤ Fintype.card Λ := by
    rw [Finset.sum_val]
    exact hsum
  obtain ⟨σ, hσ⟩ := (Equiv.Perm.exists_with_cycleType_iff Λ).mpr
    ⟨hsum', fun a ha => (hs a ha).1.two_le⟩
  refine ⟨σ, ?_, fun p hp => Equiv.Perm.dvd_of_mem_cycleType (hσ ▸ hp)⟩
  rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_of_cycleType, hσ]
  apply Even.neg_one_pow
  have he : s.val.sum + Multiset.card s.val = ∑ p ∈ s, (p + 1) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one, Finset.sum_val]
    rfl
  rw [he]
  exact Finset.even_sum _ fun p hp => ((hs p hp).1.odd_of_ne_two (hs p hp).2).add_one

end GraphIso.Pyber
