module

public import GraphIsoChecks.MainSteps
public import GraphIsoChecks.Exec
import all Init.Data.Array.Basic
import all Init.Data.List.Sort.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Mathlib.Data.List.Sort

/-!
# Kernel-checked executions of the macro-step programs

The bridge between the kernel execution toolkit (`GraphIsoChecks.Exec`) and the instrumented
sub-solver of the macro-step checks (`GraphIsoChecks.MainSteps`): the children records of a run,
event by event (`recF`), whose `flatMap` over a trace is `MainSteps.records`
(`flatMap_recF`). A theorem `∃ v s, RunsS ssOracle body0 recF p v s ∧ Q v s` proved from
`execRuns` is then a statement about the actual run of `p` with milestone 1's solver as the
recursive procedure: its value `v` and its recorded children `s = MainSteps.records tr`.
-/

@[expose] public section

namespace GraphIsoChecks.ExecSteps

open GraphIso GraphIso.Cost GraphIso.Sims GraphIsoChecks.Sweep GraphIsoChecks.Exec

deriving instance DecidableEq, Lean.ToExpr for MainSteps.Child

/-- The children records of one event: the instrumented sub-solver's opening marker call carries
the record of its child (`MainSteps.recordOf`). -/
def recF : Event (groupSig Ty.unit) → List MainSteps.Child := fun e => match e with
  | .call .generate x _ =>
    if x.1 == 0 && (x.2.headD (#[], #[])).1.getD 0 0 == MainSteps.SENT then
      [MainSteps.decode (x.2.map img)]
    else []
  | _ => []

/-- **The summary is the children records**: `MainSteps.records` is the `flatMap` of `recF`. -/
theorem flatMap_recF (tr : Trace (groupSig Ty.unit)) : tr.flatMap recF = MainSteps.records tr := by
  induction tr with
  | nil => rfl
  | cons e tr ih =>
    rw [List.flatMap_cons, ih]
    unfold MainSteps.records
    rw [List.filterMap_cons]
    rcases e with _ | ⟨op, x, y⟩
    · rfl
    · cases op <;> try rfl
      simp only [recF]
      split <;> rfl

/-- Milestone 1's solver, the recursive procedure of the checks. -/
abbrev body0 : (Ty.inst Ty.unit).denote →
    Prog (groupSig Ty.unit) (Solver.Rec Ty.unit) Ty.denote (Ty.answer Ty.unit) :=
  Solver.solveBody Ty.unit Ty.denote

/-- The split of the checks: pieces of at most 5000 trace events. -/
def cfg5 : Exec.Config := { budget := 5000 }

end GraphIsoChecks.ExecSteps
