module

public import GraphIso.Pyber.Theorem7
public import GraphIso.Pyber.Primes
public import GraphIso.AltQuot.Interfaces

/-!
# Pyber's Lemma 12: the CFSG-free Lemma 4.1

Stage 15d. The threshold is `Kpy n = 192 (λ(n) + 1)⁵`, with `λ = Nat.log 2`.

* **Lemma 12** (`injective_of_surjective_alt`): let `G` be finite, acting faithfully and
  primitively on a finite `Ω` of size `n`, and `φ : G →* Alt(Λ)` onto with `|Λ| ≥ Kpy n`. Then
  `φ` is injective. Suppose `N = ker φ ≠ ⊥`. With `ℓ = λ(n)`, take `R = 2 ℓ² + ℓ + 2` odd primes
  of at most `64 (ℓ + 1)³` each (`exists_odd_primes`); their sum is at most `Kpy n`, so some
  `σ ∈ Alt(Λ)` has order divisible by each of them (`exists_mem_alternatingGroup`). Then
  `H = φ⁻¹(⟨σ⟩)` contains `N`, which is transitive (15c), so `H` is transitive and faithful, and
  `H` maps onto `⟨σ⟩`, so `compA H` contains the `R` primes. Theorem 7 bounds `|compA H|` by
  `2 ℓ² + ℓ + 1`, a contradiction.
* **The interface** (`altQuotientIso_pyber`): `AltQuotientIso Kpy`, with `Kpy` monotone
  (`Kpy_mono`).
-/

@[expose] public section

namespace GraphIso.Pyber

open Subgroup MulAction Finset

/-- **Pyber's threshold:** `Kpy n = 192 (λ(n) + 1)⁵`. -/
def Kpy (n : ℕ) : ℕ := 192 * (Nat.log 2 n + 1) ^ 5

theorem Kpy_mono : Monotone Kpy := fun _ _ h =>
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right (Nat.log_mono_right h) 1) 5)

/-- The arithmetic of Lemma 12: `R (64 (ℓ + 1)³) ≤ 192 (ℓ + 1)⁵` for `R = 2 ℓ² + ℓ + 2`. -/
theorem lemma12_arith (l : ℕ) :
    (2 * l ^ 2 + l + 2) * (64 * (l + 1) ^ 3) ≤ 192 * (l + 1) ^ 5 := by
  have h : 2 * l ^ 2 + l + 2 ≤ 3 * (l + 1) ^ 2 := by nlinarith
  calc (2 * l ^ 2 + l + 2) * (64 * (l + 1) ^ 3) ≤ 3 * (l + 1) ^ 2 * (64 * (l + 1) ^ 3) :=
        Nat.mul_le_mul_right _ h
    _ = 192 * (l + 1) ^ 5 := by ring

/-- **Pyber's Lemma 12.** A surjection `φ` from a finite group acting faithfully and primitively
on a finite `Ω` onto `Alt(Λ)`, with `|Λ| ≥ Kpy |Ω|`, is injective. -/
theorem injective_of_surjective_alt {G Ω Λ : Type} [Group G] [Finite G] [MulAction G Ω]
    [Finite Ω] [IsPreprimitive G Ω] (hf : Faithful G Ω) [Fintype Λ] [DecidableEq Λ]
    (φ : G →* alternatingGroup Λ) (hφ : Function.Surjective φ)
    (hk : Kpy (Nat.card Ω) ≤ Fintype.card Λ) : Function.Injective φ := by
  rw [← MonoidHom.ker_eq_bot_iff]
  by_contra hN
  set l := Nat.log 2 (Nat.card Ω)
  -- the primes and the permutation
  obtain ⟨s, hs, hp⟩ := exists_odd_primes (L := l + 1) (R := 2 * l ^ 2 + l + 2) (by omega)
    (by nlinarith)
  have hsum : ∑ p ∈ s, p ≤ Fintype.card Λ := by
    have h1 := Finset.sum_le_card_nsmul s id (64 * (l + 1) ^ 3) fun p h => (hp p h).2.2
    rw [smul_eq_mul, hs] at h1
    exact h1.trans ((lemma12_arith l).trans hk)
  obtain ⟨σ, hσ, hdvd⟩ := exists_mem_alternatingGroup s (fun p h => ⟨(hp p h).1, (hp p h).2.1⟩)
    hsum
  set z : alternatingGroup Λ := ⟨σ, hσ⟩
  set H := (zpowers z).comap φ
  -- `H` is transitive and faithful
  have hNH : φ.ker ≤ H := fun g hg => by
    rw [mem_comap, MonoidHom.mem_ker.mp hg]
    exact one_mem _
  have := isPretransitive_of_normal hf hN
  have : IsPretransitive H Ω := ⟨fun a b => by
    obtain ⟨⟨k, hk⟩, hk'⟩ := exists_smul_eq φ.ker a b
    exact ⟨⟨k, hNH hk⟩, hk'⟩⟩
  have hHf : Faithful H Ω := fun h hh => Subtype.ext (hf h hh)
  have : Nonempty Ω := by
    by_contra hΩ
    rw [not_nonempty_iff] at hΩ
    apply hN
    rw [eq_bot_iff]
    intro g _
    exact hf g fun a => isEmptyElim a
  have h1 : (compA H).ncard ≤ 2 * l ^ 2 + l + 1 := ncard_compA_le_of_transitive hHf
  -- `compA H` contains the primes
  set f : H →* zpowers z := (φ.comp H.subtype).codRestrict _ fun h => h.2
  have hsurj : Function.Surjective f := by
    rintro ⟨q, hq⟩
    obtain ⟨g, rfl⟩ := hφ q
    exact ⟨⟨g, hq⟩, rfl⟩
  have hsub : (s : Set ℕ) ⊆ compA H := by
    intro p hps
    apply compA_subset_of_surjective f hsurj
    apply mem_compA_of_comm
      (fun a b => Subtype.ext (setLike_mul_comm a.2 b.2)) (hp p hps).1
    rw [Nat.card_zpowers]
    rw [← Subgroup.orderOf_coe z]
    exact hdvd p hps
  have h2 : #s ≤ (compA H).ncard := by
    rw [← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard hsub compA_finite
  omega

/-- **The CFSG-free Lemma 4.1** (Pyber's Lemma 12): `AltQuotientIso Kpy`. -/
theorem altQuotientIso_pyber : AltQuot.AltQuotientIso Kpy := by
  intro Ω _ _ G hG Λ _ _ φ hφ hk
  exact injective_of_surjective_alt (faithful_perm G) φ hφ (by rwa [Nat.card_eq_fintype_card])

end GraphIso.Pyber
