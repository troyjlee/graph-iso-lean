module

public import GraphIsoChecks.GraphBrute
meta import GraphIsoChecks.GraphBrute
public import GraphIso.Solver.GraphAll
meta import GraphIso.Solver.GraphAll
import all Init.Data.Array.Basic
import all Init.Data.List.Sort.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Mathlib.Data.List.Sort

/-!
# Milestone 5 checks: all graphs of maximum degree three

Runs of `gi3AllChecked`, the checked entry for graphs of maximum degree three, connected or
not, with the Schreier–Sims backend substituted, run inside `luksSolver`. `runAll_spec` ties
every run to `gi3_all_checked`: its answer is correct and its cost is within
`5100 (2n + 1)²⁸`.

* **Kernel-evaluated runs** on no points and on two isolated points.
* **Interpreter runs** (each `#eval` throws on a failure), compared with brute force over all
  `n!` permutations (`checkAll`); a returned isomorphism is checked to be a bijection
  preserving adjacency:
  - three isolated points, matched by a non-identity map;
  - `K₂ ⊔ K₁` against a relabelling (components of different sizes in different orders);
  - `2K₂` against a relabelling with components `{0, 2}` and `{1, 3}`, not intervals, so
    the component data relabel by position;
  - `2K₂` against `P₄` (component sizes differ: not isomorphic, no connected test);
  - `K₃ ⊔ K₁` against `P₃ ⊔ K₁` (equal sizes, not isomorphic);
  - `P₃ ⊔ K₃` against `K₃ ⊔ P₃`: the partner of `P₃` is found after a failed test against
    `K₃`;
  - inputs rejected by the validity check: a vertex of degree four, a wrong number of lists,
    an asymmetric list, a loop. A disconnected graph is now accepted.
-/

@[expose] public section

namespace GraphIsoChecks.GraphAll

open Equiv GraphIso GraphIso.Cost GraphIso.Sims GraphIso.Graph GraphIsoChecks.Graph

/-- Run the checked entry: the result and the charged cost. -/
def runAll (n : ℕ) (X Y : GraphData) : Option (Option (Option (Array ℕ)) × ℕ) :=
  (eval Ctx.empty.O (luksSolver.proc Ty.denote) 1000000000
    ((gi3AllChecked Ty.unit Ty.denote (n, X, Y)).subst ssImpl)).map
      fun r => (r.1, Trace.localCost r.2)

/-- A completed run is the run of `gi3_all_checked`: its result is correct and its cost is
within the closed-form bound. -/
theorem runAll_spec {n : ℕ} {X Y : GraphData} {r : Option (Option (Array ℕ))} {c : ℕ}
    (h : runAll n X Y = some (r, c)) :
    c ≤ 5100 * (2 * n + 1) ^ 28 ∧ (r = none ↔ ¬ GIValidAll n X Y) ∧
      ∀ res, r = some res → GIAnswer n X Y res := by
  obtain ⟨r', tr, hr, hc, hnone, hsome⟩ := gi3_all_checked n X Y
  unfold runAll at h
  rcases he : eval Ctx.empty.O (luksSolver.proc Ty.denote) 1000000000
    ((gi3AllChecked Ty.unit Ty.denote (n, X, Y)).subst ssImpl) with _ | ⟨a, tr'⟩
  · rw [he] at h
    cases h
  · rw [he] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    obtain ⟨rfl, rfl⟩ := Runs.unique ⟨_, he⟩ hr
    exact ⟨hc, hnone, hsome⟩

/-! ### Kernel-evaluated runs -/

/-- No points: the empty map. Without a connectivity condition, the empty input is valid. -/
theorem runAll0 : runAll 0 #[] #[] = some (some (some #[]), 39) := by
  decide +kernel

example : GIValidAll 0 #[] #[] := by simpa using (runAll_spec runAll0).2.1

/-- Two isolated points: a disconnected graph, matched component by component. -/
theorem runAll2 : runAll 2 #[[], []] #[[], []] = some (some (some #[0, 1]), 691) := by
  decide +kernel

example := runAll_spec runAll2

/-! ### Brute force -/

/-- Run the checked entry on valid data and compare with brute force. -/
def checkAll (name : String) (n : ℕ) (X Y : GraphData) : IO Unit := do
  let some (r, c) := runAll n X Y | throw <| IO.userError s!"{name}: out of fuel"
  let some res := r | throw <| IO.userError s!"{name}: valid input rejected"
  unless c ≤ 5100 * (2 * n + 1) ^ 28 do throw <| IO.userError s!"{name}: cost {c}"
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
def checkAllInvalid (name : String) (n : ℕ) (X Y : GraphData) : IO Unit := do
  let some (r, c) := runAll n X Y | throw <| IO.userError s!"{name}: out of fuel"
  unless r = none do throw <| IO.userError s!"{name}: invalid input accepted"
  IO.println s!"{name}: rejected; cost {c}"

/-! ### Interpreter runs -/

#eval checkAll "three isolated points" 3 #[[], [], []] #[[], [], []]
#eval checkAll "K2 + K1 against a relabelling" 3 #[[1], [0], []] #[[], [2], [1]]
#eval checkAll "2K2 against an interleaved relabelling" 4 #[[1], [0], [3], [2]]
  #[[2], [3], [0], [1]]
#eval checkAll "2K2 against P4" 4 #[[1], [0], [3], [2]] #[[1], [0, 2], [1, 3], [2]]
#eval checkAll "K3 + K1 against P3 + K1" 4 #[[1, 2], [0, 2], [0, 1], []] #[[1], [0, 2], [1], []]
#eval checkAll "P3 + K3 against K3 + P3" 6 #[[1], [0, 2], [1], [4, 5], [3, 5], [3, 4]]
  #[[1, 2], [0, 2], [0, 1], [4], [3, 5], [4]]

#eval checkAllInvalid "a vertex of degree four" 5 #[[1, 2, 3, 4], [0], [0], [0], [0]]
  #[[1, 2, 3, 4], [0], [0], [0], [0]]
#eval checkAllInvalid "a wrong number of lists" 3 #[[1], [0]] #[[1], [0], []]
#eval checkAllInvalid "an asymmetric list" 2 #[[1], []] #[[1], [0]]
#eval checkAllInvalid "a loop" 2 #[[0, 1], [0]] #[[1], [0]]

end GraphIsoChecks.GraphAll
