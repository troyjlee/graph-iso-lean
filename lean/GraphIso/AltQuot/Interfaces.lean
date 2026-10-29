module

public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import Mathlib.GroupTheory.GroupAction.Primitive
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.Data.Finite.Perm
public import Mathlib.Tactic.Linarith

/-!
# The CFSG-free interfaces

Two results of Babai's analysis depend on the classification of finite simple groups (CFSG).
Following the decision recorded in `PLAN-10.md` and `PLAN-12.md`, the formalization uses them
through explicit hypotheses in their weak, CFSG-free form, to be discharged later.

* `AltQuotientIso K` — Helfgott's Lemma 4.1 (Babai's Lemma 8.2.4) with threshold function `K`:
  every epimorphism from a primitive permutation group of degree `n` onto `Alt(k)`, `k ≥ K n`, is
  injective. With CFSG it holds for `K n = max 9 (⌊log₂ n⌋ + 3)` (Babai, using Schreier's
  hypothesis); without CFSG, Pyber (*A CFSG-free analysis of Babai's quasipolynomial GI
  algorithm*, Lemma 12) proves it for `K n = max C ((⌊log₂ n⌋ + 1)⁵)`, `C` an absolute constant.
* `TransitivityBound T` — Wielandt's bound (1934; Babai, Thm. 13.1.1) with threshold function
  `T`: a `t`-transitive permutation group of degree `k ≥ t` not containing `Alt(k)` has
  `t ≤ T k`. Wielandt gives `t < 3 ln k`, so `T k = 3 (⌊log₂ k⌋ + 1)`. It replaces Cameron's
  theorem (through Babai §13.1) and the bound `d ≤ 5` of Helfgott §6, Case 2b.

Both interfaces are satisfiable (`altQuotientIso_succ`, `transitivityBound_id`), with thresholds
useless for quasipolynomial time; this certifies that neither hypothesis is contradictory.
-/

@[expose] public section

namespace GraphIso.AltQuot

open Equiv MulAction

/-- **Helfgott's Lemma 4.1 with threshold function `K`**: every epimorphism from a primitive
permutation group of degree `n` onto `Alt(k)`, `k ≥ K n`, is injective. -/
def AltQuotientIso (K : ℕ → ℕ) : Prop :=
  ∀ (Ω : Type) [Fintype Ω] [DecidableEq Ω] (G : Subgroup (Perm Ω)), IsPreprimitive G Ω →
    ∀ (Λ : Type) [Fintype Λ] [DecidableEq Λ] (φ : G →* alternatingGroup Λ),
      Function.Surjective φ → K (Fintype.card Ω) ≤ Fintype.card Λ → Function.Injective φ

/-- **Wielandt's bound with threshold function `T`**: a `t`-transitive permutation group of
degree `k ≥ t` not containing `Alt(k)` has `t ≤ T k`. -/
def TransitivityBound (T : ℕ → ℕ) : Prop :=
  ∀ (Λ : Type) [Fintype Λ] [DecidableEq Λ] (G : Subgroup (Perm Λ)) (t : ℕ),
    t ≤ Fintype.card Λ → IsMultiplyPretransitive G Λ t → ¬ alternatingGroup Λ ≤ G →
      t ≤ T (Fintype.card Λ)

/-- **`AltQuotientIso` is satisfiable**: for `k ≥ n + 1` there is no epimorphism from a group of
permutations of `n ≥ 2` points onto `Alt(k)` (`n! < (n + 1)!/2`), and for `n ≤ 1` the group is
trivial. -/
theorem altQuotientIso_succ : AltQuotientIso (· + 1) := by
  intro Ω _ _ G _ Λ _ _ φ hφ hk
  set n := Fintype.card Ω with hn
  set k := Fintype.card Λ with hkdef
  by_cases hn1 : n ≤ 1
  · -- `Perm Ω` is trivial
    have hsub : Subsingleton (Perm Ω) := by
      rw [← Fintype.card_le_one_iff_subsingleton, Fintype.card_perm]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hn1 with h0 | h1
      · rw [← hn, h0, Nat.factorial_zero]
      · rw [← hn, h1, Nat.factorial_one]
    have : Subsingleton G := ⟨fun a b => Subtype.ext (Subsingleton.elim (a : Perm Ω) b)⟩
    exact Function.injective_of_subsingleton _
  · -- `|Alt(Λ)| = k!/2 > n! ≥ |G|`
    exfalso
    have hk' : n + 1 ≤ k := hk
    have : Nontrivial Λ := Fintype.one_lt_card_iff_nontrivial.1 (by omega)
    have h1 := Nat.card_le_card_of_surjective φ hφ
    have h2 : Nat.card G ≤ Nat.card (Perm Ω) :=
      Nat.card_le_card_of_injective G.subtype G.subtype_injective
    have hA : Nat.card (alternatingGroup Λ) = k.factorial / 2 := by
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card]
    have hP : Nat.card (Perm Ω) = n.factorial := by
      rw [Nat.card_perm, Nat.card_eq_fintype_card]
    have hle : k.factorial / 2 ≤ n.factorial := by
      rw [← hA, ← hP]
      exact h1.trans h2
    have hfac : (n + 1).factorial ≤ k.factorial := Nat.factorial_le hk'
    have hsucc : (n + 1).factorial = (n + 1) * n.factorial := Nat.factorial_succ n
    have hev : 2 ∣ k.factorial := Nat.dvd_factorial two_pos (by omega)
    have h2k : 2 * (k.factorial / 2) = k.factorial := Nat.mul_div_cancel' hev
    have hpos : 0 < n.factorial := Nat.factorial_pos n
    nlinarith

/-- **`TransitivityBound` is satisfiable** (`t ≤ k` is assumed). -/
theorem transitivityBound_id : TransitivityBound id := by
  intro Λ _ _ G t ht _ _
  exact ht

end GraphIso.AltQuot
