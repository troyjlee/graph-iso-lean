module

public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.GroupTheory.GroupAction.Period
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Large order gives a power of small support

Stage 16a. The lemma of Babai and Seress (*On the degree of transitivity of permutation groups:
a short proof*, 1987; *Element order versus minimal degree*, 2014), in an integer form:

* **`exists_pow_support_lt`**: for `σ ∈ Sym(Ω)`, `|Ω| = n`, and `s` with `n^n < (ord σ)^s`, some
  power `σ^m ≠ 1` moves fewer than `s` points.

Write `M = ord σ = ∏_p q_p`, `q_p = p^{v_p(M)}`. For each point `w`, the `q_p` dividing the
length `ℓ(w)` of its cycle are coprime, so their product is at most `ℓ(w) ≤ n`; with
`n_p = |{w | q_p ∣ ℓ(w)}|`, this gives `∏_p q_p^{n_p} ≤ n^n`. If every `n_p ≥ s`, then
`M^s ≤ n^n`. So some `n_p < s`, and `σ^{M/p}` (of order `p`) moves exactly the `n_p` points with
`q_p ∣ ℓ(w)`.
-/

@[expose] public section

namespace GraphIso.Wielandt

open Equiv Equiv.Perm Finset MulAction

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A product of pairwise coprime divisors of `z` divides `z`. -/
theorem prod_dvd_of_pairwise_coprime {s : Finset ℕ} {f : ℕ → ℕ} {z : ℕ}
    (hs : (s : Set ℕ).Pairwise fun a b => Nat.Coprime (f a) (f b)) (hd : ∀ a ∈ s, f a ∣ z) :
    ∏ a ∈ s, f a ∣ z := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a r har ih =>
    rw [Finset.prod_insert har]
    refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ (hd a (mem_insert_self _ _))
      (ih (Set.Pairwise.mono (by simp) hs) fun b hb => hd b (mem_insert_of_mem hb))
    exact Nat.Coprime.prod_right fun b hb =>
      hs (by simp) (by simp [hb]) fun e => har (e ▸ hb)

/-- If `d ∣ M` and `d ∤ M / p` for a prime `p ∣ M`, then `p^{v_p(M)} ∣ d`. -/
theorem ordProj_dvd_of_not_dvd_div {d M p : ℕ} (hp : p.Prime) (hpM : p ∣ M) (hM : M ≠ 0)
    (hd : d ∣ M) (hnd : ¬d ∣ M / p) : p ^ M.factorization p ∣ d := by
  have hd0 : d ≠ 0 := fun h => hM (Nat.eq_zero_of_zero_dvd (h ▸ hd))
  rw [hp.pow_dvd_iff_le_factorization hd0]
  by_contra hlt
  push Not at hlt
  apply hnd
  have hMp : M / p ≠ 0 := by
    have := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hM) hpM) hp.pos
    omega
  rw [← Nat.factorization_le_iff_dvd hd0 hMp, Nat.factorization_div hpM]
  intro r
  have hdr := (Nat.factorization_le_iff_dvd hd0 hM).mpr hd r
  simp only [Finsupp.coe_tsub, Pi.sub_apply, hp.factorization]
  by_cases hr : r = p
  · subst hr
    simp only [Finsupp.single_eq_same]
    omega
  · have : (Finsupp.single p 1) r = 0 := by simp [Ne.symm hr]
    rw [this]
    omega

/-- **Babai–Seress:** if `n^n < (ord σ)^s` (`n = |Ω|`), some `σ^m ≠ 1` moves fewer than `s`
points. -/
theorem exists_pow_support_lt (σ : Perm α) {s : ℕ}
    (h : Fintype.card α ^ Fintype.card α < orderOf σ ^ s) :
    ∃ m, σ ^ m ≠ 1 ∧ #(σ ^ m).support < s := by
  classical
  set n := Fintype.card α
  set M := orderOf σ with hMdef
  have hM : M ≠ 0 := (orderOf_pos σ).ne'
  set P := M.primeFactors
  let q : ℕ → ℕ := fun p => p ^ M.factorization p
  let ℓ : α → ℕ := fun w => period σ w
  have hℓM : ∀ w, ℓ w ∣ M := fun w => period_dvd_orderOf σ w
  have hℓpos : ∀ w, 0 < ℓ w := fun w => period_pos_of_orderOf_pos (orderOf_pos σ) w
  have hℓn : ∀ w, ℓ w ≤ n := fun w => by
    simp only [ℓ, period_eq_minimalPeriod]
    exact Function.minimalPeriod_le_card
  let B : ℕ → Finset α := fun p => univ.filter fun w => q p ∣ ℓ w
  -- the product over points
  have hcop : ∀ T ⊆ P, (T : Set ℕ).Pairwise fun a b => Nat.Coprime (q a) (q b) := by
    intro T hT p hp r hr hpr
    exact Nat.coprime_pow_primes _ _ (Nat.prime_of_mem_primeFactors (hT hp))
      (Nat.prime_of_mem_primeFactors (hT hr)) hpr
  have hpt : ∀ w, ∏ p ∈ P.filter (fun p => q p ∣ ℓ w), q p ≤ n := by
    intro w
    have hdvd : ∏ p ∈ P.filter (fun p => q p ∣ ℓ w), q p ∣ ℓ w :=
      prod_dvd_of_pairwise_coprime (hcop _ (filter_subset _ _)) fun p hp => (mem_filter.mp hp).2
    exact (Nat.le_of_dvd (hℓpos w) hdvd).trans (hℓn w)
  have hswap : ∏ p ∈ P, q p ^ #(B p) = ∏ w, ∏ p ∈ P.filter (fun p => q p ∣ ℓ w), q p := by
    have e1 : ∀ p ∈ P, q p ^ #(B p) = ∏ w, if q p ∣ ℓ w then q p else 1 := by
      intro p _
      rw [prod_ite, prod_const_one, mul_one, prod_const]
    rw [prod_congr rfl e1, prod_comm]
    refine prod_congr rfl fun w _ => ?_
    rw [prod_filter]
  have hprod : ∏ p ∈ P, q p ^ #(B p) ≤ n ^ n := by
    rw [hswap]
    calc ∏ w, ∏ p ∈ P.filter (fun p => q p ∣ ℓ w), q p ≤ ∏ _w : α, n :=
          prod_le_prod fun w _ => hpt w
      _ = n ^ n := by rw [prod_const, card_univ]
  -- some `n_p < s`
  have hMprod : ∏ p ∈ P, q p = M := Nat.prod_factorization_pow_eq_self hM
  obtain ⟨p, hpP, hps⟩ : ∃ p ∈ P, #(B p) < s := by
    by_contra hcon
    push Not at hcon
    have hle : M ^ s ≤ ∏ p ∈ P, q p ^ #(B p) := by
      rw [← hMprod, ← prod_pow]
      refine prod_le_prod fun p hp => Nat.pow_le_pow_right ?_ (hcon p hp)
      exact Nat.pow_pos (Nat.prime_of_mem_primeFactors hp).pos
    omega
  have hp := Nat.prime_of_mem_primeFactors hpP
  have hpM := Nat.dvd_of_mem_primeFactors hpP
  refine ⟨M / p, ?_, ?_⟩
  · refine pow_ne_one_of_lt_orderOf ?_ ?_
    · have := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hM) hpM) hp.pos
      omega
    · exact Nat.div_lt_self (Nat.pos_of_ne_zero hM) hp.one_lt
  · refine lt_of_le_of_lt (card_le_card fun w hw => ?_) hps
    rw [mem_support] at hw
    simp only [B, mem_filter, mem_univ, true_and]
    refine ordProj_dvd_of_not_dvd_div hp hpM hM (hℓM w) fun hd => hw ?_
    have := (pow_smul_eq_iff_period_dvd (m := σ) (a := w) (n := M / p)).mpr hd
    simpa [Perm.smul_def] using this

end GraphIso.Wielandt
