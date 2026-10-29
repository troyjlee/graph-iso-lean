module

public import GraphIso
meta import GraphIso

/-!
# Execution regressions: compiled evaluation does only the recorded work

`eval` is an ordinary Lean function, and compiled Lean code is strict: a branch passed as an
argument is evaluated before the call. Evaluating a case branch that is not taken changes
neither the result nor the trace, only the running time, so the theorems cannot see it. These
checks time compiled runs (Lean's IR interpreter, which shares the evaluation order of native
code) and fail when a run at large fuel is much slower than the same run at small fuel:

* synthetic procedures that return at once, but whose untaken `caseList` or `caseOption`
  branch calls the procedure twice, so evaluating that branch takes time exponential in the
  fuel (about 5 seconds at fuel 100 for the eager `caseList` that `eval` once had);
* the reference solver on `G = ⟨(1 2)⟩`, window `[0, 1, 2]` and equal constant strings, where
  that eager `caseList` re-solved the unchanged problem in the untaken branch: time linear
  in the fuel (about 6 seconds at fuel 100000) at constant answer and cost.

The allowed time (ten times the small run, plus half a second) is far above the few
milliseconds these runs take now and far below the slowdowns above.

A last check sums a trace of 1.8 million events, from the block reduction for `S₄`: the trace
sums once mapped the trace and took its `List.sum`, which compiled to non-tail recursion that
exhausted the interpreter's stack on this run.
-/

@[expose] public section

namespace GraphIsoChecks.Execution

open GraphIso GraphIso.Cost GraphIso.Programs GraphIso.Solver GraphIso.Reference GraphIso.Enum

/-- Returns its argument; the untaken `caseList` branch calls the procedure twice. -/
def listTwice : Proc Signature.empty .nat .nat := fun _ x =>
  .bind (.op0 (Prim.nil (a := .nat))) fun e => .bind (.op2 .cons x e) fun l =>
  .caseList l (.bind (.recur x) fun _ => .recur x) fun y _ => .ret y

/-- Returns its argument; the untaken `caseOption` branch calls the procedure twice. -/
def optionTwice : Proc Signature.empty .nat .nat := fun _ x =>
  .bind (.op1 .some x) fun o =>
  .caseOption o (.bind (.recur x) fun _ => .recur x) fun y => .ret y

/-- Run a procedure on `7`: the value and the charged cost. -/
def runProc (P : Proc Signature.empty .nat .nat) (fuel : ℕ) : Option (ℕ × ℕ) :=
  (eval Ctx.empty.O (P Ty.denote) fuel (P Ty.denote 7)).map fun r => (r.1, Trace.localCost r.2)

/-- The instance `G = ⟨(1 2)⟩`, window `[0, 1, 2]`, `x = y = 000`. -/
def fixedInput : Ty.input.denote :=
  ((#[0, 0, 0], #[0, 0, 0]), ([0, 1, 2], #[true, true, true]), PermData.one 3, 3,
    [(#[0, 2, 1], #[0, 2, 1])])

/-- Run the reference solver: whether it succeeds, and the charged cost. -/
def runRefFuel (inp : Ty.input.denote) (fuel : ℕ) : Option (Bool × ℕ) :=
  (eval Ctx.empty.O (referenceSolver.proc Ty.denote) fuel
    ((solveEntry Ty.gens Ty.denote inp).subst refImpl)).map
      fun r => (r.1.isSome, Trace.localCost r.2)

/-- The value of `f fuel` and the milliseconds taken to compute it. The fuel is read from a
reference, so the run cannot be computed ahead of time, and the value is stored before the
clock is read again, so it cannot be computed later. -/
def timed {α : Type} (f : ℕ → α) (fuel : ℕ) : IO (α × ℕ) := do
  let fuelRef ← IO.mkRef fuel
  let sink ← IO.mkRef (none : Option α)
  let t₀ ← IO.monoMsNow
  let a := f (← fuelRef.get)
  sink.set (some a)
  let t₁ ← IO.monoMsNow
  return (a, t₁ - t₀)

/-- Fail unless the runs at both fuels agree and the large one is not much slower. -/
def checkFlat {α : Type} [BEq α] [Repr α] (name : String) (f : ℕ → α) (small large : ℕ) :
    IO Unit := do
  let (a₁, t₁) ← timed f small
  let (a₂, t₂) ← timed f large
  unless a₁ == a₂ do
    throw <| IO.userError s!"{name}: {repr a₁} at fuel {small}, {repr a₂} at fuel {large}"
  unless t₂ ≤ 10 * t₁ + 500 do
    throw <| IO.userError s!"{name}: {t₂} ms at fuel {large}, {t₁} ms at fuel {small}"

#eval checkFlat "caseList" (runProc listTwice) 30 100
#eval checkFlat "caseOption" (runProc optionTwice) 30 100
#eval checkFlat "reference solver" (runRefFuel fixedInput) 1000 100000

/-! ### Long traces -/

/-- `S₄ = ⟨(0 1), (0 1 2 3)⟩`. -/
def s4 : GensData := [(#[1, 0, 2, 3], #[1, 0, 2, 3]), (#[1, 2, 3, 0], #[3, 0, 1, 2])]

/-- The block reduction for `S₄` on the empty window with no blocks: the number of trace events
and the charged cost. -/
def runLong (fuel : ℕ) : Option (ℕ × ℕ) :=
  (eval Ctx.empty.O (referenceSolver.proc Ty.denote) fuel
    ((blockReduceProg (fun J => .recur J) (#[0, 0, 0, 0], #[0, 0, 0, 0]) (WinData.ofPoints 4 [])
      (PermData.one 4) (4, s4, enumerate 4 s4) []).subst refImpl)).map
        fun r => (r.2.length, Trace.localCost r.2)

#eval show IO Unit from do
  let r := runLong 10000
  unless r == some (1803694, 2088866) do
    throw <| IO.userError s!"long trace: {repr r}"

end GraphIsoChecks.Execution
