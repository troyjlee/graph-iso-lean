module

public import GraphIso.Groups.Coprime
public import GraphIso.Groups.PCore

/-!
# Solvable linear groups

* `card_le_prod_of_sylow`: the order of a finite group is at most the product, over the primes
  dividing it, of bounds on its Sylow subgroups.
* `card_le_of_isSolvable_linear`: a solvable group acting faithfully and linearly on a finite
  `ZMod p`-vector space `V`, with no nontrivial normal `p`-subgroup, has order at most
  `|V|^{12 s′}`, where `s′` is the number of primes other than `p` dividing its order.
  - Every Sylow `r`-subgroup with `r ≠ p` has order at most `|V|³` (`card_le_of_isPGroup'`),
    so the `p′`-core `N` has order at most `|V|^{3 s′}`.
  - A Sylow `p`-subgroup meets the centralizer of `N`, which lies in `N`
    (`centralizer_le_of_pcore`), trivially. So it acts faithfully on `N` by conjugation, and
    has order at most `|N|³ ≤ |V|^{9 s′}` (`card_le_of_coprime`).
-/

@[expose] public section

namespace GraphIso.Groups

open LinearMap Subgroup

/-- **The order of a finite group from its Sylow subgroups**: if every Sylow `r`-subgroup has
order at most `b r`, the group has order at most `∏ b r` over the primes `r` dividing its
order. -/
theorem card_le_prod_of_sylow {G : Type*} [Group G] [Finite G] (b : ℕ → ℕ)
    (hb : ∀ r ∈ (Nat.card G).primeFactors, ∀ S : Sylow r G, Nat.card S ≤ b r) :
    Nat.card G ≤ ∏ r ∈ (Nat.card G).primeFactors, b r := by
  have h0 : Nat.card G ≠ 0 := Nat.card_pos.ne'
  calc Nat.card G = ∏ r ∈ (Nat.card G).primeFactors, r ^ (Nat.card G).factorization r :=
        (Nat.prod_factorization_pow_eq_self h0).symm
    _ ≤ ∏ r ∈ (Nat.card G).primeFactors, b r := by
      refine Finset.prod_le_prod fun r hr => ?_
      have : Fact r.Prime := ⟨Nat.prime_of_mem_primeFactors hr⟩
      obtain ⟨S⟩ : Nonempty (Sylow r G) := Sylow.nonempty
      rw [← Sylow.card_eq_multiplicity S]
      exact hb r hr S

/-- **Solvable linear groups with no normal `p`-subgroup are small.** -/
theorem card_le_of_isSolvable_linear {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V]
    [Module (ZMod p) V] [Finite V] {H : Type*} [Group H] [Finite H] [Group.IsSolvable H]
    (ρ : H →* GeneralLinearGroup (ZMod p) V) (hρ : Function.Injective ρ)
    (hp : ∀ Q : Subgroup H, Q.Normal → IsPGroup p Q → Q = ⊥) :
    Nat.card H ≤ Nat.card V ^ (12 * ((Nat.card H).primeFactors.erase p).card) := by
  classical
  have hpp : p.Prime := Fact.out
  set s := ((Nat.card H).primeFactors.erase p).card
  have hV1 : 1 ≤ Nat.card V := Nat.card_pos
  -- `r`-subgroups for `r ≠ p`
  have hr : ∀ r, r.Prime → r ≠ p → ∀ S : Subgroup H, IsPGroup r S →
      Nat.card S ≤ Nat.card V ^ 3 := by
    intro r hr hrp S hS
    have : Fact r.Prime := ⟨hr⟩
    rw [← card_map_of_injective (K := S) hρ]
    exact card_le_of_isPGroup' (Ne.symm hrp) (S.map ρ) (hS.map ρ)
  -- the `p′`-core
  obtain ⟨N, hN, hNp, hmax⟩ := exists_pcore p H
  have hCN := centralizer_le_of_pcore hp hN hNp hmax
  have hNcard : Nat.card N ≤ Nat.card V ^ (3 * s) := by
    have hsub : (Nat.card N).primeFactors ⊆ (Nat.card H).primeFactors.erase p := by
      intro r hrN
      have hrp : r ≠ p := by
        rintro rfl
        exact hNp (Nat.dvd_of_mem_primeFactors hrN)
      exact Finset.mem_erase.mpr ⟨hrp, Nat.primeFactors_mono (card_subgroup_dvd_card N)
        Nat.card_pos.ne' hrN⟩
    calc Nat.card N ≤ ∏ r ∈ (Nat.card N).primeFactors, Nat.card V ^ 3 := by
          refine card_le_prod_of_sylow _ fun r hrN S => ?_
          have hrp : r ≠ p := (Finset.mem_erase.mp (hsub hrN)).1
          rw [← card_map_of_injective (K := (S : Subgroup N)) N.subtype_injective]
          exact hr r (Nat.prime_of_mem_primeFactors hrN) hrp _ (S.isPGroup'.map _)
      _ = Nat.card V ^ (3 * (Nat.card N).primeFactors.card) := by
          rw [Finset.prod_const, ← pow_mul, mul_comm 3]
      _ ≤ Nat.card V ^ (3 * s) :=
          Nat.pow_le_pow_right hV1 (Nat.mul_le_mul_left 3 (Finset.card_le_card hsub))
  -- a Sylow `p`-subgroup acts faithfully on the core by conjugation
  have hP : ∀ P : Sylow p H, Nat.card P ≤ Nat.card V ^ (9 * s) := by
    intro P
    let φ : (P : Subgroup H) →* MulAut N := MulAut.conjNormal.comp (P : Subgroup H).subtype
    have hφ : Function.Injective φ := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro g hg
      have hgC : (g : H) ∈ Subgroup.centralizer (N : Set H) :=
        mem_centralizer_of_conjNormal_eq_one hg
      have hgN : (g : H) ∈ N := hCN hgC
      obtain ⟨k, hk⟩ := P.isPGroup' g
      have hdP : orderOf g ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk
      have hdN : orderOf g ∣ Nat.card N := by
        rw [← Subgroup.orderOf_coe, show (g : H) = ((⟨g, hgN⟩ : N) : H) from rfl,
          Subgroup.orderOf_coe]
        exact orderOf_dvd_natCard _
      have hcop : (p ^ k).Coprime (Nat.card N) :=
        Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hpp).mpr hNp)
      exact (Subgroup.mem_bot).mpr (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hdP hdN))
    have hrange : IsPGroup p φ.range :=
      P.isPGroup'.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
    calc Nat.card P = Nat.card φ.range := Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv
      _ ≤ Nat.card N ^ 3 := card_le_of_coprime hNp φ.range hrange
      _ ≤ (Nat.card V ^ (3 * s)) ^ 3 := Nat.pow_le_pow_left hNcard 3
      _ = Nat.card V ^ (9 * s) := by rw [← pow_mul]; ring_nf
  -- multiply the Sylow bounds
  let b : ℕ → ℕ := fun r => if r = p then Nat.card V ^ (9 * s) else Nat.card V ^ 3
  have hb : ∀ r ∈ (Nat.card H).primeFactors, ∀ S : Sylow r H, Nat.card S ≤ b r := by
    intro r hrH S
    by_cases hrp : r = p
    · subst hrp
      simpa [b] using hP S
    · simpa [b, hrp] using hr r (Nat.prime_of_mem_primeFactors hrH) hrp _ S.isPGroup'
  have herase : ∏ r ∈ (Nat.card H).primeFactors.erase p, b r = Nat.card V ^ (3 * s) := by
    rw [Finset.prod_congr rfl (g := fun _ => Nat.card V ^ 3)
      fun r hr => by simp [b, (Finset.mem_erase.mp hr).1], Finset.prod_const, ← pow_mul,
      mul_comm 3]
  have hsplit : ∏ r ∈ (Nat.card H).primeFactors, b r ≤
      Nat.card V ^ (9 * s) * ∏ r ∈ (Nat.card H).primeFactors.erase p, b r := by
    by_cases hpH : p ∈ (Nat.card H).primeFactors
    · rw [← Finset.mul_prod_erase _ _ hpH]
      simp [b]
    · rw [Finset.erase_eq_of_notMem hpH]
      exact Nat.le_mul_of_pos_left _ (pow_pos hV1 _)
  calc Nat.card H ≤ ∏ r ∈ (Nat.card H).primeFactors, b r := card_le_prod_of_sylow b hb
    _ ≤ Nat.card V ^ (9 * s) * Nat.card V ^ (3 * s) := herase ▸ hsplit
    _ = Nat.card V ^ (12 * s) := by rw [← pow_add]; ring_nf

end GraphIso.Groups
