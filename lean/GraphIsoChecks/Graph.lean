module

public import GraphIsoChecks.GraphBrute
meta import GraphIsoChecks.GraphBrute
public import GraphIso.Solver.Graph
meta import GraphIso.Solver.Graph
import all Init.Data.Array.Basic
import all Init.Data.List.Sort.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Mathlib.Data.List.Sort

/-!
# Milestone 4 checks: graphs of maximum degree three

Runs of `gi3Checked`, the checked entry with the Schreier–Sims backend substituted, run inside
`luksSolver`. `runGI_spec` ties every run to `gi3_checked`: its answer is correct and its cost is
within `17500 (2n + 1)²⁶`.

* **Kernel-evaluated runs** on one point and on none. The empty input passes the input checks,
  since `Conn 0` holds vacuously, although mathlib's graphs on `Fin 0` are not connected.
* **Interpreter runs** (each `#eval` throws on a failure), compared with brute force over all
  `n!` permutations; a returned isomorphism is checked to be a bijection preserving adjacency:
  - `K₂`; the paths `P₃` and `P₄` against relabellings (non-identity isomorphisms); `P₄`
    against the star `K₁,₃`, with as many edges (not isomorphic); `K₄` against itself with
    permuted adjacency lists (every permutation is an isomorphism);
  - inputs rejected by the input checks (validity, then connectivity): a vertex of degree four,
    a disconnected graph, a wrong number of lists, an asymmetric list, a loop.

Each run on two or more points costs 30–300 million units, dominated by the first layer,
whose domain has `2n` points and the 14 nonempty subsets of the four roots with at most three
points.
-/

@[expose] public section

namespace GraphIsoChecks.Graph

open Equiv GraphIso GraphIso.Cost GraphIso.Sims GraphIso.Graph

/-- Run the checked entry: the result and the charged cost. -/
def runGI (n : ℕ) (X Y : GraphData) : Option (Option (Option (Array ℕ)) × ℕ) :=
  (eval Ctx.empty.O (luksSolver.proc Ty.denote) 1000000000
    ((gi3Checked Ty.unit Ty.denote (n, X, Y)).subst ssImpl)).map
      fun r => (r.1, Trace.localCost r.2)

/-- A completed run is the run of `gi3_checked`: its result is correct and its cost is within
the closed-form bound. -/
theorem runGI_spec {n : ℕ} {X Y : GraphData} {r : Option (Option (Array ℕ))} {c : ℕ}
    (h : runGI n X Y = some (r, c)) :
    c ≤ 17500 * (2 * n + 1) ^ 26 ∧ (r = none ↔ ¬ GIValid n X Y) ∧
      ∀ res, r = some res → GIAnswer n X Y res := by
  obtain ⟨r', tr, hr, hc, hnone, hsome⟩ := gi3_checked n X Y
  unfold runGI at h
  rcases he : eval Ctx.empty.O (luksSolver.proc Ty.denote) 1000000000
    ((gi3Checked Ty.unit Ty.denote (n, X, Y)).subst ssImpl) with _ | ⟨a, tr'⟩
  · rw [he] at h
    cases h
  · rw [he] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    obtain ⟨rfl, rfl⟩ := Runs.unique ⟨_, he⟩ hr
    exact ⟨hc, hnone, hsome⟩

/-! ### A kernel-evaluated run -/

/-- One point: the identity. -/
theorem runK1 : runGI 1 #[[]] #[[]] = some (some (some #[0]), 174) := by
  decide +kernel

example := runGI_spec runK1

/-- No points: the empty map. -/
theorem runK0 : runGI 0 #[] #[] = some (some (some #[]), 80) := by
  decide +kernel

/-- The empty input is valid for the checked entry, unlike for mathlib's connectivity. -/
example : GIValid 0 #[] #[] ∧ ¬ (GraphData.toSimpleGraph 0 #[]).Connected :=
  ⟨by simpa using (runGI_spec runK0).2.1, fun h => h.nonempty.elim Fin.elim0⟩

/-! ### Brute force (`isIsoB`, `bruteIso`, `isBijB` in `GraphBrute.lean`) -/

/-- Run the checked entry on valid data and compare with brute force. -/
def checkGI (name : String) (n : ℕ) (X Y : GraphData) : IO Unit := do
  let some (r, c) := runGI n X Y | throw <| IO.userError s!"{name}: out of fuel"
  let some res := r | throw <| IO.userError s!"{name}: valid input rejected"
  unless c ≤ 17500 * (2 * n + 1) ^ 26 do throw <| IO.userError s!"{name}: cost {c}"
  let iso := bruteIso n X Y
  match res with
  | none =>
    if iso then throw <| IO.userError s!"{name}: missed an isomorphism"
    IO.println s!"{name}: not isomorphic, as brute force; cost {c}"
  | some arr =>
    unless iso && isBijB n arr && isIsoB n X Y arr.toList do
      throw <| IO.userError s!"{name}: wrong isomorphism {arr}"
    IO.println s!"{name}: isomorphism {arr}, checked; cost {c}"

/-- Run the checked entry on invalid data: it must be rejected. -/
def checkInvalid (name : String) (n : ℕ) (X Y : GraphData) : IO Unit := do
  let some (r, c) := runGI n X Y | throw <| IO.userError s!"{name}: out of fuel"
  unless r = none do throw <| IO.userError s!"{name}: invalid input accepted"
  IO.println s!"{name}: rejected; cost {c}"

/-! ### Interpreter runs -/

#eval checkGI "K2" 2 #[[1], [0]] #[[1], [0]]
#eval checkGI "P3 against a relabelling" 3 #[[1], [0, 2], [1]] #[[2], [2], [0, 1]]
#eval checkGI "P4 against a relabelling" 4 #[[1], [0, 2], [1, 3], [2]]
  #[[2], [3], [0, 3], [1, 2]]
#eval checkGI "P4 against the star K1,3" 4 #[[1], [0, 2], [1, 3], [2]]
  #[[1, 2, 3], [0], [0], [0]]
#eval checkGI "K4 against itself, with permuted lists" 4
  #[[1, 2, 3], [0, 2, 3], [0, 1, 3], [0, 1, 2]] #[[2, 1, 3], [3, 0, 2], [0, 3, 1], [2, 1, 0]]

#eval checkInvalid "a vertex of degree four" 5 #[[1, 2, 3, 4], [0], [0], [0], [0]]
  #[[1, 2, 3, 4], [0], [0], [0], [0]]
#eval checkInvalid "a disconnected graph" 4 #[[1], [0], [3], [2]] #[[1], [0], [3], [2]]
#eval checkInvalid "a wrong number of lists" 3 #[[1], [0]] #[[1], [0], []]
#eval checkInvalid "an asymmetric list" 2 #[[1], []] #[[1], [0]]
#eval checkInvalid "a loop" 2 #[[0, 1], [0]] #[[1], [0]]

end GraphIsoChecks.Graph
