module

public import GraphIso.Certificates.Aggregate
import all Init.Data.Array.Basic
import all Init.Data.List.Sort.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Mathlib.Data.List.Sort

/-!
# Milestone 13 checks: local certificates and their aggregation

The milestone is theory (Babai §10.1, Helfgott §6), proved against the interface
`AltQuotientIso`. The certificates are subgroups and windows, which are not computable at this
level of abstraction; the programs computing them, and concrete runs, come with milestone 14.
The checks:
* the beard starts from `(∅, G_A)` and is constant from step `|Ω|` on;
* the threshold structure `Thresholds` is inhabited at the witness interface `K n = n + 1` of
  milestone 12 (`thresholds_succ`: `5 ≤ k` and `n + 1 ≤ k` suffice);
* the principal theorems instantiate there. As in milestone 12 they are then vacuous for giant
  representations (the witness forces `k > |Ω|`), which is why the interface with a
  quasipolynomial threshold (Pyber, milestone 15) is needed;
* Case 2b's degree of transitivity instantiates at the witness `T k = k` of
  `TransitivityBound`.
-/

@[expose] public section

namespace GraphIsoChecks.Certificates

open Equiv MulAction GraphIso.AltQuot GraphIso.Certificates

variable {Ω Γ : Type} [Fintype Ω] [DecidableEq Ω] [Fintype Γ] [DecidableEq Γ]
variable {G : Subgroup (Perm Ω)} (φ : G →* Perm Γ) {L : Type}

/-- The beard starts from the empty window and the whole stabilizer. -/
example (A : Finset Γ) (x : Ω → L) : beard φ A x 0 = (∅, ⊤) := rfl

/-- The beard is constant from step `|Ω|` on. -/
example (A : Finset Γ) (x : Ω → L) :
    beard φ A x (Fintype.card Ω + 1) = (beardW φ A x, beardH φ A x) :=
  beard_stable φ A x 1

/-- The thresholds hold at the witness interface once `5 ≤ k` and `n + 1 ≤ k`. -/
theorem thresholds_succ {n k : ℕ} (h5 : 5 ≤ k) (hk : n + 1 ≤ k) :
    Thresholds (· + 1) n k where
  iso := altQuotientIso_succ
  mono := fun _ _ h => Nat.succ_le_succ h
  five := h5
  le := hk
  lt := by
    have h2 : 2 ≤ (k - 1).factorial :=
      le_trans (by omega) (Nat.self_le_factorial (k - 1))
    have hk' : k * 2 ≤ k.factorial := by
      rw [← Nat.mul_factorial_pred (by omega : k ≠ 0)]
      exact Nat.mul_le_mul_left k h2
    rw [Nat.lt_div_iff_mul_lt (by norm_num)]
    omega

/-- The certificates decide fullness, at the witness interface. -/
example {A : Finset Γ} (x : Ω → L) (h5 : 5 ≤ A.card) (hk : Fintype.card Ω + 1 ≤ A.card) :
    IsFull φ A x ↔ IsGiantOn φ A (beardH φ A x) :=
  isFull_iff φ x (thresholds_succ h5 hk)

/-- The certificate of fullness, at the witness interface. -/
example {A : Finset Γ} (x : Ω → L) (h5 : 5 ≤ A.card) (hk : Fintype.card Ω + 1 ≤ A.card)
    (h : IsGiantOn φ A (beardH φ A x)) :
    (certK φ A x).map (stabA φ A).subtype ≤ autG x ∧
      alternatingGroup A ≤ (certK φ A x).map (psiA φ A) :=
  cert_full φ x (thresholds_succ h5 hk) h

/-- The aggregated group is a group of automorphisms, at the witness interface. -/
example {k : ℕ} (x : Ω → L) (h5 : 5 ≤ k) (hk : Fintype.card Ω + 1 ≤ k) :
    fullGroup φ k x ≤ autG x :=
  fullGroup_le_autG φ x (thresholds_succ h5 hk)

/-- Case 3, at the witness interface. -/
example {k : ℕ} (x : Ω → L) (h5 : 5 ≤ k) (hk : Fintype.card Ω + 1 ≤ k) {U : Finset Γ}
    (hU : k ≤ U.card) (hUS : ∀ u ∈ U, u ∉ supp φ (fullGroup φ k x))
    (htw : ∀ u ∈ U, ∀ v ∈ U, ∀ T : Fin k → Γ, (∀ i, T i ∉ supp φ (fullGroup φ k x)) →
      SameColour φ x T (Equiv.swap u v ∘ T)) : False :=
  no_large_twins φ x (thresholds_succ h5 hk) hU hUS htw

/-- Case 2b at the witness interface `T k = k`: the degree of transitivity exists. -/
example {Φ : Type} [Fintype Φ] [DecidableEq Φ] (P : Subgroup (Perm Φ)) [IsPretransitive P Φ]
    (hP : ¬ alternatingGroup Φ ≤ P) :
    ∃ d, 1 ≤ d ∧ d + 2 ≤ Fintype.card Φ ∧ d ≤ Fintype.card Φ ∧
      IsMultiplyPretransitive P Φ d ∧ ¬ IsMultiplyPretransitive P Φ (d + 1) :=
  exists_degree transitivityBound_id P hP

end GraphIsoChecks.Certificates
