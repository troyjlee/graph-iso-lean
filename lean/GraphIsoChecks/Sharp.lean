module

public import GraphIso.Main.SharpWork
import all Init.Data.Array.Basic
import all Init.Data.List.Sort.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Mathlib.Data.List.Sort

/-!
# Checks of stage 14j-6b-2: the sharp dispatcher

`PLAN-14.md` §14.12 item 7, by kernel `decide`.

* **The sharp work at a large base.** At `m = 65536`, with `n = 65536` string positions (degree
  `N = 131072`), a window of `p = 65536` points, `g = 131072` generators, the domain's bound
  `s = (2N)²`, `k = 5`, M4's depth `j = 51`, the label length `t = 2` (union-cell bound
  `t · λ(m) = 32`) and Case 2b's depth bound `jB = supTo wielandtT 65536 = 51`: `caseWorkS` at M4
  and M5 is below `m!` (`sharp_m4_work_lt`, `sharp_m5_work_lt`). The work functions are
  envelopes; their corner bounds (`caseWorkS_m4_le`, `caseWorkS_m5_le`, `GraphIso.Main.SharpWork`)
  are evaluated, and compared with `(m/2)^(m - m/2) ≤ m!` (`pow_half_le_factorial`).
* **Why the base must be large.** M4's work contains the eighth power of the structures' count
  `msCount (m - j) = 2^(129 (⌈log₂ (m - j)⌉ + 2)²)` (`msCount_pow_le_caseWorkS_m4`). At
  `m = 3000` this alone exceeds `3000!`, at any other sizes. It is quasi-polynomial in `m`, so it
  is below `m!` at a large `m`.
* **The sharp factors** `caseFS` at M4 and M5 are below `m!`, at `m = 3000` (`k = 5`, `j = 3`,
  `t = 2`, `jB = supTo wielandtT 3000 = 36`) and at `m = 65536` (the sizes above). A negative
  control: the factors with stuck orbits, `caseF`, are not, at `m = 3000`.
* **The numeric hypothesis `TBelow`** at Wielandt's bound: it holds at `m = 129` and
  `m = 3000`, as `tBelow_wielandt` proves for every `m > 128`, and fails at `m = 64`, so a
  threshold is needed.
-/

@[expose] public section

namespace GraphIsoChecks.Sharp

open GraphIso GraphIso.Main GraphIso.Recursion

/-- Case 2b's depth bound at `m = 65536` and at `m = 3000` under Wielandt's bound, and
`λ(3000) = 11`. -/
example : supTo wielandtT 65536 = 51 ∧ supTo wielandtT 3000 = 36 ∧ lam 3000 = 11 := by
  rw [supTo_wielandtT, supTo_wielandtT]
  decide +kernel

/-- **The sharp work at M4 is below `m!`** at `m = 65536`. -/
theorem sharp_m4_work_lt :
    caseWorkS .m4 65536 131072 65536 131072 68719476736 5 51 2 51 < Nat.factorial 65536 :=
  (caseWorkS_m4_le (by decide)).trans_lt
    (lt_of_lt_of_le (by decide +kernel) (pow_half_le_factorial _))

/-- **The sharp work at M5 is below `m!`** at `m = 65536`. -/
theorem sharp_m5_work_lt :
    caseWorkS .m5 65536 131072 65536 131072 68719476736 5 51 2 51 < Nat.factorial 65536 :=
  (caseWorkS_m5_le (by decide) (by decide) (by decide)).trans_lt
    (lt_of_lt_of_le (by decide +kernel) (pow_half_le_factorial _))

/-- **M4's work is at least the eighth power of the structures' count**, at any sizes: the
structure step charges `1000 · (… + msCount (m - j) + …)⁸` (`m4StructCost`), and the envelope
is at least its value at its own corner. -/
theorem msCount_pow_le_caseWorkS_m4 (n N p g s k j t jB : ℕ) :
    msCount (N - n - j) ^ 8 ≤ caseWorkS .m4 n N p g s k j t jB := by
  refine le_trans ?_ (le_envSup (forall₂_le_refl _) _)
  simp only [List.getD_cons_zero, List.getD_cons_succ]
  have h := Nat.pow_le_pow_left (show msCount (N - n - j) ≤ n + (N - n) + (N - n - j) + s +
    msCount (N - n - j) + SoJTree.outB (N - n - j) ((N - n - j + 3) / 2) + 2 by omega) 8
  unfold m4CostSS m4StepCost m4StructCost
  omega

/-- **At `m = 3000` M4's work is above `3000!`**, at any other sizes. -/
example (n p g s k t jB : ℕ) : Nat.factorial 3000 < caseWorkS .m4 n (n + 3000) p g s k 3 t jB :=
  (by decide +kernel : Nat.factorial 3000 < msCount (3000 - 3) ^ 8).trans_le
    (by simpa using msCount_pow_le_caseWorkS_m4 n (n + 3000) p g s k 3 t jB)

/-- **The sharp factors are below `m!`** at M4 and M5, at `m = 3000` and at `m = 65536`. -/
example : caseFS .m4 0 3000 5 3 2 36 < Nat.factorial 3000 ∧
    caseFS .m5 0 3000 5 3 2 36 < Nat.factorial 3000 :=
  ⟨by decide +kernel, by decide +kernel⟩

example : caseFS .m4 65536 131072 5 51 2 51 < Nat.factorial 65536 ∧
    caseFS .m5 65536 131072 5 51 2 51 < Nat.factorial 65536 :=
  ⟨lt_of_lt_of_le (by decide +kernel) (pow_half_le_factorial _),
    lt_of_lt_of_le (by decide +kernel) (pow_half_le_factorial _)⟩

/-- **A negative control**: the factors with stuck orbits are at least `m!`. -/
example : Nat.factorial 3000 ≤ caseF .m4 0 3000 5 3 ∧ Nat.factorial 3000 ≤ caseF .m5 0 3000 5 3 :=
  ⟨by decide +kernel, by decide +kernel⟩

/-- **`TBelow` at Wielandt's bound**: it holds at `m = 129` and `m = 3000`, and fails at
`m = 64`. -/
example : 4 * supTo wielandtT 129 + 6 ≤ 129 ∧ 4 * supTo wielandtT 3000 + 6 ≤ 3000 ∧
    ¬ 4 * supTo wielandtT 64 + 6 ≤ 64 := by decide +kernel

end GraphIsoChecks.Sharp
