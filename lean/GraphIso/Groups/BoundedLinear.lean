module

public import GraphIso.Groups.NoAbelian
public import GraphIso.Groups.Radical

/-!
# Linear groups with bounded sections

`card_le_of_boundedSections_linear`: a group with simple sections of order at most `k`, acting
faithfully and linearly on a finite `ZMod p`-vector space `V`, with no nontrivial normal
`p`-subgroup, has order at most `|V|^{3 k³ + 3 k² + 12 k}`.

* Its solvable radical `R` has no nontrivial normal `p`-subgroup either, and at most `k` primes
  divide its order; so `|R| ≤ |V|^{12 k}` (`card_le_of_isSolvable_linear`).
* `H / R` has no nontrivial abelian normal subgroup, so `|H / R| ≤ (k! 2^k)^t` with `2^t` at most
  the `p′`-part of `|H / R|` (`exists_card_le_of_noAbelianNormal`).
* The `p′`-part of `|H|` is at most `|V|^{3 k}`: each Sylow `r`-subgroup with `r ≠ p` has order
  at most `|V|³` (`card_le_of_isPGroup'`).
* So `|H| ≤ |V|^{12 k} (2^t)^{k² + k} ≤ |V|^{12 k + 3 k (k² + k)}`, as `k! ≤ 2^{k²}`.
-/

@[expose] public section

namespace GraphIso.Groups

open LinearMap

/-- **The `p′`-part of a linear group** in characteristic `p`. -/
theorem ordCompl_card_le_linear {p : ℕ} [hp : Fact p.Prime] {V : Type*} [AddCommGroup V]
    [Module (ZMod p) V] [Finite V] {H : Type*} [Group H] [Finite H]
    (ρ : H →* GeneralLinearGroup (ZMod p) V) (hρ : Function.Injective ρ) :
    ordCompl[p] (Nat.card H) ≤ Nat.card V ^ (3 * (Nat.card H).primeFactors.card) := by
  classical
  have hV1 : 1 ≤ Nat.card V := Nat.card_pos
  have hb : ∀ r ∈ (Nat.card H).primeFactors, ∀ S : Sylow r H,
      Nat.card S ≤ (if r = p then p ^ (Nat.card H).factorization p else 1) * Nat.card V ^ 3 := by
    intro r hr S
    have : Fact r.Prime := ⟨Nat.prime_of_mem_primeFactors hr⟩
    by_cases hrp : r = p
    · subst hrp
      rw [ite_eq_left rfl, Sylow.card_eq_multiplicity S]
      exact Nat.le_mul_of_pos_right _ (pow_pos hV1 3)
    · rw [ite_eq_right hrp, one_mul, ← Subgroup.card_map_of_injective (K := (S : Subgroup H)) hρ]
      exact card_le_of_isPGroup' (Ne.symm hrp) _ (S.isPGroup'.map ρ)
  have h1 := card_le_prod_of_sylow _ hb
  rw [Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.prod_const] at h1
  have h2 : Nat.card H ≤ p ^ (Nat.card H).factorization p *
      Nat.card V ^ (3 * (Nat.card H).primeFactors.card) := by
    refine h1.trans (Nat.mul_le_mul ?_ (by rw [← pow_mul, mul_comm]))
    split_ifs
    · exact le_rfl
    · exact Nat.one_le_pow _ _ hp.out.pos
  have h3 := Nat.ordProj_mul_ordCompl_eq_self (Nat.card H) p
  have h4 : p ^ (Nat.card H).factorization p * ordCompl[p] (Nat.card H) ≤
      p ^ (Nat.card H).factorization p * Nat.card V ^ (3 * (Nat.card H).primeFactors.card) := by
    rw [h3]
    exact h2
  exact Nat.le_of_mul_le_mul_left h4 (pow_pos hp.out.pos _)

/-- **Linear groups with bounded sections and no normal `p`-subgroup are small.** -/
theorem card_le_of_boundedSections_linear {p : ℕ} [hp : Fact p.Prime] {V : Type*}
    [AddCommGroup V] [Module (ZMod p) V] [Finite V] {H : Type*} [Group H] [Finite H] {k : ℕ}
    (hk : BoundedSections k H) (ρ : H →* GeneralLinearGroup (ZMod p) V)
    (hρ : Function.Injective ρ) (hpH : ∀ Q : Subgroup H, Q.Normal → IsPGroup p Q → Q = ⊥) :
    Nat.card H ≤ Nat.card V ^ (3 * k ^ 3 + 3 * k ^ 2 + 12 * k) := by
  have hV1 : 1 ≤ Nat.card V := Nat.card_pos
  obtain ⟨R, hRn, hRs, hRmax⟩ := exists_radical H
  -- the radical
  have hR : Nat.card R ≤ Nat.card V ^ (12 * k) := by
    have := card_le_of_isSolvable_linear (ρ.comp R.subtype) (hρ.comp R.subtype_injective)
      fun Q hQ hQp => eq_bot_of_normal_isPGroup_of_normal hpH R Q hQ hQp
    refine this.trans (Nat.pow_le_pow_right hV1 ?_)
    have h1 := (hk.subgroup R).card_primeFactors_le
    have h2 := Finset.card_erase_le (s := (Nat.card R).primeFactors) (a := p)
    omega
  -- the quotient
  obtain ⟨t, ht1, ht2⟩ := exists_card_le_of_noAbelianNormal (p := p)
    (hk.of_surjective (QuotientGroup.mk' R) (QuotientGroup.mk'_surjective R)) ⊤
    fun A hA hAc => eq_bot_of_abelian_normal_quotient hRmax A (nnormal_top_iff.1 hA) hAc
  rw [Subgroup.card_top] at ht1 ht2
  have hHR : Nat.card H = Nat.card (H ⧸ R) * Nat.card R :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup R
  -- `2^t` is at most the `p′`-part of `|H|`
  have h2t : 2 ^ t ≤ Nat.card V ^ (3 * k) := by
    have hdvd : Nat.card (H ⧸ R) ∣ Nat.card H := ⟨_, hHR⟩
    have h1 := Nat.le_of_dvd (Nat.ordCompl_pos p Nat.card_pos.ne')
      (Nat.ordCompl_dvd_ordCompl_of_dvd hdvd p)
    have h2 := ordCompl_card_le_linear ρ hρ
    have h3 : Nat.card V ^ (3 * (Nat.card H).primeFactors.card) ≤ Nat.card V ^ (3 * k) :=
      Nat.pow_le_pow_right hV1 (Nat.mul_le_mul_left 3 hk.card_primeFactors_le)
    exact ht2.trans (h1.trans (h2.trans h3))
  have hfac : k.factorial * 2 ^ k ≤ 2 ^ (k ^ 2 + k) := by
    rw [pow_add]
    exact Nat.mul_le_mul_right _ (factorial_le_two_pow_sq k)
  calc Nat.card H = Nat.card R * Nat.card (H ⧸ R) := hHR.trans (mul_comm _ _)
    _ ≤ Nat.card V ^ (12 * k) * (2 ^ (k ^ 2 + k)) ^ t :=
        Nat.mul_le_mul hR (ht1.trans (Nat.pow_le_pow_left hfac t))
    _ = Nat.card V ^ (12 * k) * (2 ^ t) ^ (k ^ 2 + k) := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm (k ^ 2 + k) t]
    _ ≤ Nat.card V ^ (12 * k) * (Nat.card V ^ (3 * k)) ^ (k ^ 2 + k) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h2t _)
    _ = Nat.card V ^ (3 * k ^ 3 + 3 * k ^ 2 + 12 * k) := by
        rw [← pow_mul, ← pow_add]
        congr 1
        ring

end GraphIso.Groups
