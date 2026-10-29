module

public import GraphIso.AltQuot.Unaffected
public import GraphIso.AltQuot.Subsets
import all Init.Data.Array.Basic
import all Init.Data.List.Sort.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Mathlib.Data.List.Sort

/-!
# Milestone 12 checks: alternating quotients and the CFSG-free interfaces

The milestone is theory (Babai §§5.2, 8.1, 8.3), proved against the interfaces
`AltQuotientIso` and `TransitivityBound`. The checks:
* the interfaces are inhabited: `altQuotientIso_succ`, `transitivityBound_id`;
* kernel-checked instances of the binomial inequality (Babai, Prop. 5.2.3) on all
  `m₁, m₂ < 9`, `1 ≤ t₁, t₂ < 5` with `2 (t₁ + t₂) ≤ m₁ + m₂`, and of Lemma 5.2.1 (b) on
  `d ≤ m < 9`, `t < 6`;
* the theorems instantiate at the witness threshold `K n = n + 1`. There they are vacuous (no
  permutation group of degree `n` maps onto `Alt(k)` with `k > n ≥ 2`), which is why the
  interface with a quasipolynomial threshold (Pyber, milestone 15) is needed.
-/

@[expose] public section

namespace GraphIsoChecks.AltQuot

open GraphIso.AltQuot

example : AltQuotientIso (· + 1) := altQuotientIso_succ
example : TransitivityBound id := transitivityBound_id

/-- The binomial inequality on a small range, kernel-checked. -/
example : ∀ m₁ ∈ Finset.range 9, ∀ m₂ ∈ Finset.range 9, ∀ t₁ ∈ Finset.range 5,
    ∀ t₂ ∈ Finset.range 5, 1 ≤ t₁ → 1 ≤ t₂ → 2 * (t₁ + t₂) ≤ m₁ + m₂ →
      3 * (m₁.choose t₁ * m₂.choose t₂) ≤ 2 * (m₁ + m₂).choose (t₁ + t₂) := by
  decide +kernel

/-- Lemma 5.2.1 (b) on a small range, kernel-checked. -/
example : ∀ m ∈ Finset.range 9, ∀ d ∈ Finset.range (m + 1), ∀ t ∈ Finset.range 6,
    d.choose t * m ^ t ≤ d ^ t * m.choose t := by
  decide +kernel

/-- The binomial inequality is tight: `m₁ = m₂ = 2`, `t₁ = t₂ = 1` gives `3 · 4 = 2 · 6`. -/
example : 3 * ((2 : ℕ).choose 1 * (2 : ℕ).choose 1) = 2 * (4 : ℕ).choose 2 := by decide

/-- The Unaffected Stabilizer Theorem, instantiated at the witness interface. -/
example {Ω Λ : Type} [Fintype Ω] [DecidableEq Ω] [Fintype Λ] [DecidableEq Λ]
    (G : Subgroup (Equiv.Perm Ω)) (φ : G →* Equiv.Perm Λ) (hφ : IsGiant φ)
    (h5 : 5 ≤ Fintype.card Λ) {N : ℕ} (hN : ∀ x : Ω, Nat.card (MulAction.orbit G x) ≤ N)
    (hk : N + 1 ≤ Fintype.card Λ) (hn : N < (Fintype.card Λ).factorial / 2) :
    alternatingGroup Λ ≤ (fixingSubgroup G ({x | ¬ IsAffected φ x} : Set Ω)).map φ :=
  unaffected_stabilizer altQuotientIso_succ (fun _ _ h => Nat.succ_le_succ h) G φ hφ h5 hN hk
    hn

end GraphIsoChecks.AltQuot
