module

public import GraphIsoChecks.Luks
meta import GraphIsoChecks.Luks
public import GraphIso.Solver.LuksSolvable
meta import GraphIso.Solver.LuksSolvable
import all Init.Data.Array.Basic
import all Init.Data.List.Sort.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Mathlib.Data.List.Sort

/-!
# Milestone 6 checks: solvable groups

Interpreter runs (each `#eval` throws on a failure) of `luksSolver`, the solver with Luks's
strategy and the Schreier–Sims backend, on solvable groups that are not nilpotent:

* each answer is compared with brute force over the group, and with the default strategy;
* the group's order, from a complete Sims table, has at most `s + 1` prime divisors;
* the cost is within `6640 (n + 1)^{36 s + 8} + 60 L (n + 1)²`, the bound of
  `solve_luks_solvable`.

The groups are `S₄` (order `2³·3`), `AGL(1, 5)` (`2²·5`) and `S₃ wr S₂` (`2³·3²`), all with
`s = 1`, and `AGL(1, 7)` (`2·3·7`, `s = 2`). On these small groups Luks's strategy costs more
than the default strategy; the polynomial bound concerns large degrees.
-/

@[expose] public section

namespace GraphIsoChecks.LuksSolvable

open Equiv GraphIso GraphIso.Cost GraphIso.Programs GraphIso.Solver GraphIso.Sims GraphIso.Luks
  GraphIsoChecks.Sims GraphIsoChecks.Luks

/-- The cost bound of `solve_luks_solvable`. -/
def solvBound (n s L : ℕ) : ℕ := 6640 * (n + 1) ^ (36 * s + 8) + 60 * L * (n + 1) ^ 2

/-- Luks's strategy and the default strategy on a solvable group whose order has at most
`s + 1` prime divisors, against brute force; the Luks cost within the solvable bound. -/
def checkSolvable (name : String) (n s : ℕ) (gs : GensData) (x y : List ℕ) : IO Unit := do
  let c : Sweep.Case := ⟨n, gs.map Sweep.img, List.range n, List.range n, x, y⟩
  let ord := order n (build n (Array.range n) gs).1
  unless ord.primeFactors.card ≤ s + 1 do
    throw <| IO.userError s!"{name}: order {ord} has more than {s + 1} prime divisors"
  match runLuks (wholeInst n gs x y), runSims (wholeInst n gs x y) with
  | some (a, cl), some (b, cd) =>
    unless answerOK n c.solutions a && answerOK n c.solutions b do
      throw <| IO.userError s!"{name}: disagreement with brute force"
    unless decide (cl ≤ solvBound n s gs.length) do
      throw <| IO.userError s!"{name}: cost {cl} above the bound {solvBound n s gs.length}"
    IO.println s!"{name}: order {ord}, {c.solutions.length} solutions; Luks cost {cl} \
      (bound {solvBound n s gs.length}), default cost {cd}"
  | _, _ => throw <| IO.userError s!"{name}: out of fuel"

/-- `AGL(1, p)` on `ZMod p`: translation and multiplication by `a`. -/
def aglGens (p a : ℕ) : GensData :=
  [cycleOf p, Sweep.ofList ((List.range p).map fun i => a * i % p)]

#eval checkSolvable "S4" 4 1 (symGens 4) [0, 0, 1, 1] [1, 0, 1, 0]
#eval checkSolvable "S4, no solution" 4 1 (symGens 4) [0, 0, 1, 1] [1, 0, 0, 0]
#eval checkSolvable "AGL(1,5)" 5 1 (aglGens 5 2) [0, 1, 1, 0, 2] [2, 1, 0, 0, 1]
#eval checkSolvable "AGL(1,5), no solution" 5 1 (aglGens 5 2) [0, 1, 1, 0, 2] [1, 0, 2, 1, 0]
#eval checkSolvable "S3 wr S2" 6 1 [ofCycles 6 [[0, 1]], ofCycles 6 [[0, 1, 2]],
  ofCycles 6 [[0, 3], [1, 4], [2, 5]]] [0, 0, 1, 2, 2, 2] [2, 2, 2, 1, 0, 0]
#eval checkSolvable "AGL(1,7)" 7 2 (aglGens 7 3) [0, 1, 1, 0, 1, 0, 0] [1, 1, 0, 1, 0, 0, 0]

end GraphIsoChecks.LuksSolvable
