module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Data.Finite.Perm

/-!
# Alternating groups: perfect, and no subgroups of small index

For `k = |Λ| ≥ 5`:
* `alternatingGroup_commutator`: `Alt(Λ)` is perfect;
* `card_le_index_of_ne_top`: every proper subgroup of `Alt(Λ)` has index at least `k`;
* `card_le_index_of_not_le`: every subgroup of `Sym(Λ)` not containing `Alt(Λ)` has index at
  least `k`.

The action on the cosets of a proper subgroup is faithful because `Alt(Λ)` is simple (mathlib's
`alternatingGroup.isSimpleGroup`), and `(k − 1)! < k!/2` (Babai, Cor. 8.3.7).
-/

@[expose] public section

namespace GraphIso.AltQuot

open Equiv

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **`Alt(Λ)` is perfect** for `|Λ| ≥ 5`. -/
theorem alternatingGroup_commutator (h : 5 ≤ Fintype.card Λ) :
    ⁅(⊤ : Subgroup (alternatingGroup Λ)), (⊤ : Subgroup (alternatingGroup Λ))⁆ = ⊤ := by
  rw [← commutator_def]
  exact commutator_alternatingGroup_eq_top (by rwa [Nat.card_eq_fintype_card])

/-- **Proper subgroups of `Alt(Λ)` have index at least `|Λ|`** for `|Λ| ≥ 5`. -/
theorem card_le_index_of_ne_top (h : 5 ≤ Fintype.card Λ) {H : Subgroup (alternatingGroup Λ)}
    (hH : H ≠ ⊤) : Fintype.card Λ ≤ H.index := by
  have := alternatingGroup.isSimpleGroup (α := Λ) (by rwa [Nat.card_eq_fintype_card])
  have : Nontrivial Λ := Fintype.one_lt_card_iff_nontrivial.1 (by omega)
  by_contra hlt
  push Not at hlt
  -- the action on the cosets of `H` is faithful
  let ψ := MulAction.toPermHom (alternatingGroup Λ) (alternatingGroup Λ ⧸ H)
  have hker : ψ.ker = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ψ.ker with h' | h'
    · exact h'
    · exfalso
      apply hH
      rw [eq_top_iff]
      intro g _
      have hg : g ∈ ψ.ker := h' ▸ Subgroup.mem_top g
      rw [MonoidHom.mem_ker] at hg
      have hfix : g • (QuotientGroup.mk 1 : alternatingGroup Λ ⧸ H) = QuotientGroup.mk 1 := by
        have := congrArg (fun p : Perm (alternatingGroup Λ ⧸ H) => p (QuotientGroup.mk 1)) hg
        simpa [ψ] using this
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, QuotientGroup.eq, mul_one] at hfix
      simpa using hfix
  have hinj : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).1 hker
  have hcard := Nat.card_le_card_of_injective ψ hinj
  rw [Nat.card_perm, ← Subgroup.index_eq_card, nat_card_alternatingGroup,
    Nat.card_eq_fintype_card] at hcard
  set k := Fintype.card Λ
  have hfac : H.index.factorial ≤ (k - 1).factorial := Nat.factorial_le (by omega)
  have hk : k * (k - 1).factorial = k.factorial := Nat.mul_factorial_pred (by omega)
  have hev : 2 ∣ k.factorial := Nat.dvd_factorial two_pos (by omega)
  have h2 : 2 * (k.factorial / 2) = k.factorial := Nat.mul_div_cancel' hev
  have hpos : 0 < (k - 1).factorial := Nat.factorial_pos _
  nlinarith

/-- **Subgroups of `Sym(Λ)` not containing `Alt(Λ)` have index at least `|Λ|`** for
`|Λ| ≥ 5`. -/
theorem card_le_index_of_not_le (h : 5 ≤ Fintype.card Λ) {H : Subgroup (Perm Λ)}
    (hH : ¬ alternatingGroup Λ ≤ H) : Fintype.card Λ ≤ H.index := by
  have hne : H.subgroupOf (alternatingGroup Λ) ≠ ⊤ := fun e =>
    hH (Subgroup.subgroupOf_eq_top.1 e)
  have h1 := card_le_index_of_ne_top h hne
  have h2 : H.relIndex (alternatingGroup Λ) ≤ H.relIndex ⊤ :=
    Subgroup.relIndex_le_of_le_right le_top (by
      rw [Subgroup.relIndex_top_right]
      exact Subgroup.index_ne_zero_of_finite)
  rw [Subgroup.relIndex_top_right] at h2
  exact h1.trans h2

end GraphIso.AltQuot
