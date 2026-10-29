module

public import GraphIso.Wielandt.Support
public import GraphIso.Wielandt.Power
public import GraphIso.AltQuot.Interfaces
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.GroupTheory.Perm.Cycle.PossibleTypes

/-!
# A logarithmic-squared transitivity bound

Stage 16a. **`transitivityBound_quad`**: `TransitivityBound Tq` with `Tq m = 256 (λ(m) + 1)²`,
`λ = Nat.log 2`. A `t`-transitive group of degree `n` not containing `Alt(n)` has
`t ≤ 256 (λ(n) + 1)²`. This is weaker than Wielandt's `t < 3 ln n` and is proved without his
theory: let `x = 7 λ(n) + 14` and suppose `t > Tq n ≥ x²`.

* **A permutation of large order** (`exists_perm_lcmUpto_dvd`): on `t ≥ x²` points, the cycle
  type `p^{⌊log_p x⌋}` (`p ≤ x` prime) gives `τ` with `lcm(1, …, x) ∣ ord τ`.
* **Lifting** (`exists_mem_orderOf_dvd`): `t`-transitivity maps `t` points as `τ` does, so some
  `g ∈ G` has `ord τ ∣ ord g`. By Chebyshev (`Chebyshev.two_pow_le_mul_lcmUpto`),
  `ord g ≥ lcm(1, …, x) ≥ 2^x / (x + 1) ≥ n^6`.
* **Small support:** by Babai–Seress (`exists_pow_support_lt`, with `s = ⌊n/6⌋ + 1`), some
  `g^m ≠ 1` moves at most `n / 6` points, and by `alternatingGroup_le_of_support_le`,
  `Alt(n) ≤ G`.
-/

@[expose] public section

namespace GraphIso.Wielandt

open Equiv Equiv.Perm Finset MulAction

/-- The cycle lengths `p^{⌊log_p x⌋}` for the primes `p ≤ x`. -/
def lcmCycles (x : ℕ) : Multiset ℕ := (Nat.primesLE x).val.map fun p => p ^ Nat.log p x

theorem card_primesLE_le (x : ℕ) : #(Nat.primesLE x) ≤ x := by
  have h : Nat.primesLE x ⊆ (range (x + 1)).erase 0 := fun p hp => by
    rw [Nat.mem_primesLE] at hp
    exact mem_erase.mpr ⟨hp.2.ne_zero, mem_range.mpr (by omega)⟩
  have := card_le_card h
  rwa [card_erase_of_mem (mem_range.mpr (by omega)), card_range, Nat.add_sub_cancel] at this

theorem sum_lcmCycles_le {x : ℕ} (hx : 1 ≤ x) : (lcmCycles x).sum ≤ x * x := by
  unfold lcmCycles
  rw [← Finset.sum_eq_multiset_sum]
  calc ∑ p ∈ Nat.primesLE x, p ^ Nat.log p x ≤ ∑ _p ∈ Nat.primesLE x, x :=
        sum_le_sum fun p _ => Nat.pow_log_le_self p (by omega)
    _ = #(Nat.primesLE x) * x := by rw [sum_const, smul_eq_mul]
    _ ≤ x * x := Nat.mul_le_mul_right _ (card_primesLE_le x)

theorem two_le_of_mem_lcmCycles {x a : ℕ} (ha : a ∈ lcmCycles x) : 2 ≤ a := by
  unfold lcmCycles at ha
  obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp ha
  have hp' := Nat.mem_primesLE.mp hp
  have h1 : 1 ≤ Nat.log p x := Nat.log_pos hp'.2.one_lt hp'.1
  calc 2 ≤ p := hp'.2.two_le
    _ = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ Nat.log p x := Nat.pow_le_pow_right hp'.2.pos h1

/-- **A permutation of large order:** on `t ≥ x²` points some `τ` has `lcm(1, …, x) ∣ ord τ`. -/
theorem exists_perm_lcmUpto_dvd {t x : ℕ} (hx : 1 ≤ x) (ht : x * x ≤ t) :
    ∃ τ : Perm (Fin t), Nat.lcmUpto x ∣ orderOf τ := by
  obtain ⟨τ, hτ⟩ := (exists_with_cycleType_iff (Fin t)).mpr
    ⟨by rw [Fintype.card_fin]; exact (sum_lcmCycles_le hx).trans ht,
      fun a ha => two_le_of_mem_lcmCycles ha⟩
  refine ⟨τ, ?_⟩
  rw [Nat.lcmUpto_eq_prod_pow_log]
  refine prod_dvd_of_pairwise_coprime ?_ fun p hp => dvd_of_mem_cycleType ?_
  · intro p hp r hr hpr
    exact Nat.coprime_pow_primes _ _ (Nat.mem_primesLE.mp hp).2 (Nat.mem_primesLE.mp hr).2 hpr
  · rw [hτ]
    exact Multiset.mem_map_of_mem _ hp

/-- **Lifting:** a `t`-transitive `G ≤ Sym(Λ)`, `t ≤ |Λ|`, has for each `τ ∈ Sym(t)` an element
`g` with `ord τ ∣ ord g`. -/
theorem exists_mem_orderOf_dvd {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (G : Subgroup (Perm Λ))
    {t : ℕ} [IsMultiplyPretransitive G Λ t] (ht : t ≤ Fintype.card Λ) (τ : Perm (Fin t)) :
    ∃ g ∈ G, orderOf τ ∣ orderOf g := by
  set e : Fin t ↪ Λ := (Fin.castLEEmb ht).trans (Fintype.equivFin Λ).symm.toEmbedding
  obtain ⟨g, hg⟩ := exists_smul_eq G e (τ.toEmbedding.trans e)
  have key : ∀ i, (g : Perm Λ) (e i) = e (τ i) := fun i => by
    have := congrArg (fun f : Fin t ↪ Λ => f i) hg
    simpa [Subgroup.smul_def, Perm.smul_def] using this
  have hpow : ∀ k i, ((g : Perm Λ) ^ k) (e i) = e ((τ ^ k) i) := by
    intro k
    induction k with
    | zero => intro i; rfl
    | succ k ih =>
      intro i
      rw [pow_succ, pow_succ, Perm.mul_apply, Perm.mul_apply, key, ih]
  refine ⟨g, g.2, orderOf_dvd_of_pow_eq_one (Equiv.ext fun i => ?_)⟩
  have := hpow (orderOf (g : Perm Λ)) i
  rw [pow_orderOf_eq_one, Perm.one_apply] at this
  exact (e.injective this).symm

/-- `7 a + 15 ≤ 2^(a + 8)`. -/
theorem seven_mul_add_le (a : ℕ) : 7 * a + 15 ≤ 2 ^ (a + 8) := by
  induction a with
  | zero => norm_num
  | succ a ih =>
    rw [show a + 1 + 8 = (a + 8) + 1 by ring, pow_succ]
    have : 1 ≤ 2 ^ (a + 8) := Nat.one_le_two_pow
    omega

/-- **The threshold** `Tq m = 256 (λ(m) + 1)²`. -/
def Tq (m : ℕ) : ℕ := 256 * (Nat.log 2 m + 1) ^ 2

/-- **The transitivity bound:** `TransitivityBound Tq`. -/
theorem transitivityBound_quad : AltQuot.TransitivityBound Tq := by
  intro Λ _ _ G t ht hG hA
  have : IsMultiplyPretransitive G Λ t := hG
  by_contra hlt
  push Not at hlt
  set n := Fintype.card Λ with hn
  set l := Nat.log 2 n
  set x := 7 * l + 14 with hx
  have hT : Tq n = 256 * (l + 1) ^ 2 := rfl
  have hxx : x * x ≤ t := by
    have : x * x ≤ 256 * (l + 1) ^ 2 := by nlinarith
    omega
  have h3t : 3 ≤ t := by nlinarith
  have hn2 : 2 ≤ n := by omega
  -- the permutation and its lift
  obtain ⟨τ, hτ⟩ := exists_perm_lcmUpto_dvd (show 1 ≤ x by omega) hxx
  obtain ⟨g, hgG, hgτ⟩ := exists_mem_orderOf_dvd G ht τ
  have hord : Nat.lcmUpto x ≤ orderOf g :=
    Nat.le_of_dvd (orderOf_pos g) (hτ.trans hgτ)
  -- `n^6 ≤ ord g`
  have hn6 : n ^ 6 ≤ orderOf g := by
    have h1 : n < 2 ^ (l + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
    have h2 : n ^ 6 * (x + 1) ≤ 2 ^ x := by
      have e : 2 ^ x = (2 ^ (l + 1)) ^ 6 * 2 ^ (l + 8) := by
        rw [← pow_mul, ← pow_add]
        congr 1
        omega
      rw [e]
      exact Nat.mul_le_mul (Nat.pow_le_pow_left h1.le 6) (by
        have := seven_mul_add_le l
        omega)
    have h3 := Chebyshev.two_pow_le_mul_lcmUpto x
    have h4 : n ^ 6 ≤ Nat.lcmUpto x := by
      by_contra hc
      push Not at hc
      have : (x + 1) * Nat.lcmUpto x < (x + 1) * n ^ 6 := Nat.mul_lt_mul_of_pos_left hc (by omega)
      nlinarith
    exact h4.trans hord
  -- a power of small support
  set s := n / 6 + 1
  have hpow : n ^ n < orderOf g ^ s := by
    calc n ^ n < n ^ (6 * s) := Nat.pow_lt_pow_right (by omega) (by omega)
      _ = (n ^ 6) ^ s := by rw [pow_mul]
      _ ≤ orderOf g ^ s := Nat.pow_le_pow_left hn6 s
  obtain ⟨m, hm1, hms⟩ := exists_pow_support_lt g hpow
  have : IsMultiplyPretransitive G Λ 3 :=
    isMultiplyPretransitive_of_le (n := t) h3t (by rwa [Nat.card_eq_fintype_card])
  exact hA (alternatingGroup_le_of_support_le G (G.pow_mem hgG m) hm1 (by omega))

end GraphIso.Wielandt
