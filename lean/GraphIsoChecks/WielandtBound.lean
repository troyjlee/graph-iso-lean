module

public import GraphIso.Wielandt.Bound
public import GraphIsoChecks.PyberPerm
import all Init.Data.Array.Basic
import all Init.Data.List.Sort.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Mathlib.Data.List.Sort

/-!
# Checks of stage 16a: the transitivity bound

`PLAN-16.md` §3 item 5. As in milestone 15, the checks are instantiations of the library, with
kernel `decide` for concrete permutations and numbers.

* **Commutators:** for the `3`-cycles `(0 1 2)` and `(2 3 4)` of `Fin 5`, which meet in one
  point, the commutator is a `3`-cycle (the library lemma, and kernel `decide` on the
  permutation).
* **Babai–Seress** on `σ = (0 1)(2 3 4)(5 6 7 8 9)` of `Fin 10` (order `30`): since
  `10^10 < 30^7`, a power of `σ` moves fewer than `7` points (here `σ^15 = (0 1)`).
* **A negative control:** the rotations of `Fin 4` act transitively and do not contain `Alt(4)`
  (`|Alt(4)| = 12 > 4`), so `TransitivityBound (fun _ => 0)` fails: the threshold cannot be
  dropped.
* **Numbers:** `Tq 1 = 256`, `Tq 1024 = 30976`.
-/

@[expose] public section

namespace GraphIsoChecks.WielandtBound

open Equiv Equiv.Perm Finset MulAction Subgroup GraphIso.Wielandt GraphIsoChecks.PyberPerm
open scoped commutatorElement

/-! ### Commutators -/

/-- `(0 1 2)` and `(2 3 4)` meet in one point. -/
theorem inter_card_cycles :
    #((c[(0 : Fin 5), 1, 2]).support ∩ (c[(2 : Fin 5), 3, 4]).support) = 1 := by
  decide +kernel

theorem commutator_cycles_ne_one : ⁅c[(0 : Fin 5), 1, 2], c[(2 : Fin 5), 3, 4]⁆ ≠ 1 := by
  decide +kernel

example : (⁅c[(0 : Fin 5), 1, 2], c[(2 : Fin 5), 3, 4]⁆).IsThreeCycle :=
  isThreeCycle_commutatorElement inter_card_cycles commutator_cycles_ne_one

/-! ### Babai–Seress -/

/-- `σ = (0 1)(2 3 4)(5 6 7 8 9)`. -/
def σ10 : Perm (Fin 10) := c[0, 1] * c[2, 3, 4] * c[5, 6, 7, 8, 9]

theorem orderOf_σ10 : orderOf σ10 = 30 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide +kernel, fun m hm h0 => ?_⟩
  interval_cases m <;> decide +kernel

example : ∃ m, σ10 ^ m ≠ 1 ∧ #(σ10 ^ m).support < 7 := by
  refine exists_pow_support_lt σ10 ?_
  rw [orderOf_σ10, Fintype.card_fin]
  norm_num

/-- The power the lemma finds: `σ^15 = (0 1)`. -/
example : σ10 ^ 15 = c[0, 1] := by
  decide +kernel

/-! ### A negative control -/

theorem not_alternatingGroup_le_rot4 : ¬alternatingGroup (Fin 4) ≤ zpowers (finRotate 4) := by
  intro h
  have h1 := Subgroup.card_le_of_le h
  have h4 : orderOf (finRotate 4) = 4 := by
    rw [orderOf_eq_iff (by norm_num)]
    refine ⟨by decide +kernel, fun m hm h0 => ?_⟩
    interval_cases m <;> decide +kernel
  rw [nat_card_alternatingGroup, Nat.card_zpowers, Nat.card_eq_fintype_card, Fintype.card_fin,
    h4] at h1
  norm_num at h1

/-- **Without a threshold, the bound fails:** `TransitivityBound (fun _ => 0)` is false. -/
theorem not_transitivityBound_zero : ¬GraphIso.AltQuot.TransitivityBound fun _ => 0 := by
  intro h
  have := h (Fin 4) (zpowers (finRotate 4)) 1 (by decide)
    (is_one_pretransitive_iff.mpr isPretransitive_rot4) not_alternatingGroup_le_rot4
  exact Nat.not_succ_le_zero 0 this

/-! ### Numbers -/

example : Tq 1 = 256 ∧ Tq 1024 = 30976 := by
  decide +kernel

end GraphIsoChecks.WielandtBound
