module

public import GraphIso.Main.FullPot
import all Init.Data.Array.Basic
import all Init.Data.List.Sort.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Mathlib.Data.List.Sort

/-!
# Checks of stage 14j-6c-1: the potential

`PLAN-14.md` §14.13 item 7, by kernel `decide`. The constants are examples: `C = 1` for the
certificates' threshold and `C' = 3` for the transitivity bound (Wielandt's `3 (λ(k) + 1)`).

* **The threshold program** `thrQP 1 3`, run by the evaluator:
  - at `n₀ = 0` it returns `(kQP 1 0, ℓQP 1 3 0) = (7, 3101)` at cost `66 ≤ cTQP 1 0 = 85`;
  - at `n₀ = 30` it returns `(3135, 15737)` at cost `2588 ≤ cTQP 1 30 = 2893`.

  `ThrSpec` (`thrQP_spec`) proves the run for every `n₀`. The kernel evaluates it here at small
  `n₀` only: the logarithm folds over `n₀ + 2` elements, and the kernel's recursion depth
  is exceeded by `n₀ = 100`. The thresholds' values are also checked at `n₀ = 1000`
  (`(100015, 404132)`, `cTQP 1 1000 = 49403`).

  At `n₀ = 2¹⁶` the thresholds are `k = 1419879` and `ℓ = 5687501`, far above the domain's base
  sizes (`m ≤ 2n₀`). So at such sizes every large base goes to M3: the thresholds grow as
  `(log n₀)⁵`, and M4 and M5 occur only at much larger `n₀`.
* **The numeric hypotheses** at these `n₀`: `4k ≤ ℓ`, `ell0 n₀ ≤ ℓ`, and `TBelow` at
  Wielandt's `T`. `TBelow` is proved for every `ℓ ≥ ℓT 3 = 1024` (`tBelow_qp`) and checked at
  `m = 1025`.
* **The inequalities with the offset** at explicit values: a step with branching, a step
  without, and the chain rule.
* **Negative controls**:
  - a step without branching whose child has the parent's measure is not paid for;
  - a step with branching is not paid for with `90000` children at `Q = 3`, without the bounds
    `c ≤ Q²` and `|ch| ≤ Q³`;
  - the trivial transitivity bound `T = id` of this repository (`transitivityBound_id`) does not
    have the growth bound `T m ≤ 3 (λ(m) + 1)` of `QPHyp`.
* **The magnitude of `Q`**: `2^25809 ≤ QQP 1 3 4 < 2^25810` and
  `2^95171 ≤ QQP 1 3 16 < 2^95172`.
-/

@[expose] public section

namespace GraphIsoChecks.Pot

open GraphIso GraphIso.Main GraphIso.Cost GraphIso.Recursion GraphIso.Sims

/-! ### The threshold program -/

/-- **`thrQP 1 3` at `n₀ = 30`**: the thresholds `(3135, 15737)` at cost `2588`. -/
example : ((eval ssCtx.O (mainBody (thrQP 1 3) Ty.denote) 100 (thrQP 1 3 Ty.denote 30)).map
    fun r => (r.1, Trace.cost ssCtx.B r.2)) = some ((3135, 15737), 2588) := by decide +kernel

/-- **`thrQP 1 3` at `n₀ = 0`**: the thresholds `(7, 3101)` at cost `66`. -/
example : ((eval ssCtx.O (mainBody (thrQP 1 3) Ty.denote) 100 (thrQP 1 3 Ty.denote 0)).map
    fun r => (r.1, Trace.cost ssCtx.B r.2)) = some ((7, 3101), 66) := by decide +kernel

/-- The values and the cost bounds of `ThrSpec (thrQP 1 3)` at `n₀ = 0, 30, 1000, 2¹⁶`. -/
example : kQP 1 0 = 7 ∧ ℓQP 1 3 0 = 3101 ∧ cTQP 1 0 = 85 ∧ kQP 1 30 = 3135 ∧
    ℓQP 1 3 30 = 15737 ∧ cTQP 1 30 = 2893 ∧ kQP 1 1000 = 100015 ∧
    ℓQP 1 3 1000 = 404132 ∧ cTQP 1 1000 = 49403 ∧ kQP 1 65536 = 1419879 ∧
    ℓQP 1 3 65536 = 5687501 := by decide +kernel

/-! ### The numeric hypotheses -/

example : 4 * kQP 1 1000 ≤ ℓQP 1 3 1000 ∧ ell0 1000 ≤ ℓQP 1 3 1000 ∧
    4 * kQP 1 65536 ≤ ℓQP 1 3 65536 ∧ ell0 65536 ≤ ℓQP 1 3 65536 := by decide +kernel

/-- `TBelow` at Wielandt's bound, at the thresholds (`tBelow_qp`, with `C' = 3`). -/
example (n₀ : ℕ) : TBelow wielandtT (ℓQP 1 3 n₀) :=
  (tBelow_qp fun _ => le_rfl).mono (ℓT_le_ℓQP 1 3 n₀)

example : ℓT 3 = 1024 ∧ 4 * supTo wielandtT 1025 + 6 ≤ 1025 := by
  rw [supTo_wielandtT]
  decide +kernel

/-! ### The inequalities with the offset -/

/-- With branching: a child keeping the hint on a smaller base, and one without a hint on half
the window. -/
example : ([((1 : ℕ), some 1), (1, none)].map fun x => potO 5 2 x.1 x.2 + 6).sum + 5 ≤
    pot 5 2 2 2 + 5 := by decide +kernel

/-- Without branching: a child on a smaller window with the same base. -/
example : ([((1 : ℕ), some 2)].map fun x => potO 5 2 x.1 x.2 + 6).sum + 5 ≤
    pot 5 2 2 2 + 5 := by decide +kernel

/-- The chain rule: two children without a hint. -/
example : ([((1 : ℕ), (none : Option ℕ)), (1, none)].map fun x => potO 5 2 x.1 x.2 + 6).sum + 5 ≤
    potO 5 2 2 none + 5 := by decide +kernel

/-! ### Negative controls -/

/-- **A child with the parent's measure** is not paid for. -/
example : ¬ ([((2 : ℕ), some 2)].map fun x => potO 5 2 x.1 x.2 + 6).sum + 5 ≤
    pot 5 2 2 2 + 5 := by decide +kernel

/-- **Too many children**: `90000` children on a base of three quarters, at `Q = 3`. -/
example : ¬ ((List.replicate 90000 ((1 : ℕ), some 1)).map fun x => potO 3 2 x.1 x.2 + 4).sum +
    3 ≤ pot 3 2 1 2 + 3 := by
  rw [List.map_replicate, List.sum_replicate, smul_eq_mul]
  decide +kernel

/-- **The trivial transitivity bound has no growth bound**: `T = id` exceeds `3 (λ(m) + 1)` at
`m = 64`. -/
example : ¬ ∀ m, id m ≤ 3 * (lam m + 1) := fun h => absurd (h 64) (by decide +kernel)

/-! ### The magnitude of `Q` -/

example : 2 ^ 25809 ≤ QQP 1 3 4 ∧ QQP 1 3 4 < 2 ^ 25810 := by decide +kernel

example : 2 ^ 95171 ≤ QQP 1 3 16 ∧ QQP 1 3 16 < 2 ^ 95172 := by decide +kernel

end GraphIsoChecks.Pot
