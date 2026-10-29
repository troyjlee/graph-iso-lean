module

public import GraphIsoChecks.LuksSolvable
meta import GraphIsoChecks.LuksSolvable
public import GraphIso.Solver.LuksBounded
meta import GraphIso.Solver.LuksBounded
import all Init.Data.Array.Basic
import all Init.Data.List.Sort.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Mathlib.Data.List.Sort

/-!
# Milestone 8 checks: groups with bounded simple sections

Interpreter runs (each `#eval` throws on a failure) of `luksSolver`, the solver with Luks's
strategy and the Schreier–Sims backend, on nonsolvable groups: `A₅` and `S₅` on five points,
and `A₅ ≅ PSL(2, 5)` on the six points of the projective line over `ZMod 5`.

* Each answer is compared with brute force over the group, and with the default strategy.
* The group's order `g` is computed from a complete Sims table and compared with the expected
  order. Every simple section of a group of order `g` has order at most `g`
  (`Groups.boundedSections_card`), so `solve_luks_bounded` applies with `k = g`.
* The cost is within `6640 (n + 1)^{9 k³ + 9 k² + 36 k + 8} + 60 L (n + 1)²`, the bound of
  `solve_luks_bounded`, for `k = g` (the bound itself is too long to print).

The groups' largest simple section is `A₅`, so `k = 60` would do as well; the bound is far above
the costs either way.
-/

@[expose] public section

namespace GraphIsoChecks.LuksBounded

open Equiv GraphIso GraphIso.Cost GraphIso.Programs GraphIso.Solver GraphIso.Sims GraphIso.Luks
  GraphIsoChecks.Sims GraphIsoChecks.Luks

/-- The exponent `9 k³ + 9 k² + 36 k + 8` of `solve_luks_bounded`. -/
def boundedExp (k : ℕ) : ℕ := 9 * k ^ 3 + 9 * k ^ 2 + 36 * k + 8

/-- The cost bound of `solve_luks_bounded`. -/
def boundedBound (n k L : ℕ) : ℕ := 6640 * (n + 1) ^ boundedExp k + 60 * L * (n + 1) ^ 2

/-- Luks's strategy and the default strategy on a group of the expected order `g`, against
brute force; the Luks cost within the bound for `k = g`. -/
def checkBounded (name : String) (n : ℕ) (gs : GensData) (g : ℕ) (x y : List ℕ) : IO Unit := do
  let c : Sweep.Case := ⟨n, gs.map Sweep.img, List.range n, List.range n, x, y⟩
  let ord := order n (build n (Array.range n) gs).1
  unless ord == g do
    throw <| IO.userError s!"{name}: order {ord}, expected {g}"
  match runLuks (wholeInst n gs x y), runSims (wholeInst n gs x y) with
  | some (a, cl), some (b, cd) =>
    unless answerOK n c.solutions a && answerOK n c.solutions b do
      throw <| IO.userError s!"{name}: disagreement with brute force"
    unless decide (cl ≤ boundedBound n ord gs.length) do
      throw <| IO.userError s!"{name}: cost {cl} above the bound"
    IO.println s!"{name}: order {ord}, {c.solutions.length} solutions; Luks cost {cl} \
      (bound 6640 * {n + 1}^{boundedExp ord} + {60 * gs.length * (n + 1) ^ 2}), \
      default cost {cd}"
  | _, _ => throw <| IO.userError s!"{name}: out of fuel"

/-- `PSL(2, 5)` on the projective line `{0, …, 4, ∞ = 5}`: `x ↦ x + 1` and `x ↦ −1/x`. -/
def psl25Gens : GensData := [ofCycles 6 [[0, 1, 2, 3, 4]], ofCycles 6 [[0, 5], [1, 4]]]

#eval checkBounded "A5" 5 (altGens 5) 60 [0, 0, 1, 1, 2] [1, 0, 2, 0, 1]
#eval checkBounded "A5, odd permutation only" 5 (altGens 5) 60 [0, 1, 2, 3, 4] [1, 0, 2, 3, 4]
#eval checkBounded "S5" 5 (symGens 5) 120 [0, 1, 2, 3, 4] [1, 0, 2, 3, 4]
#eval checkBounded "PSL(2,5)" 6 psl25Gens 60 [0, 0, 1, 1, 2, 2] [2, 0, 0, 1, 1, 2]
#eval checkBounded "PSL(2,5), no solution" 6 psl25Gens 60 [0, 0, 1, 1, 2, 2] [2, 1, 0, 1, 2, 0]

end GraphIsoChecks.LuksBounded
