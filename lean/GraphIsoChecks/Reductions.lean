module

public import GraphIsoChecks.WellFormed
import all Init.Data.Array.Basic
import all Init.Data.List.Sort.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Mathlib.Data.List.Sort

/-!
# Phase 4 checks: reduction programs

Concrete evaluations of the sequential and branching programs with a toy backend over
`Unit` data whose `generate` returns its input generators, and well-formedness of recursive
procedures that use the reductions with their own recursive call as the sub-solver.
-/

@[expose] public section

namespace GraphIsoChecks.Reductions

open Equiv GraphIso GraphIso.Cost GraphIso.Programs GraphIsoChecks.Cost

/-! Decidable equality of answers, declared in steps to keep instance search small. -/
instance : DecidableEq (Ty.denote .unit) := inferInstanceAs (DecidableEq Unit)
instance : DecidableEq (CosetData .unit) := inferInstance
instance : DecidableEq (AnswerData .unit) :=
  inferInstanceAs (DecidableEq (Option (CosetData .unit)))
instance : DecidableEq (AnswerData .unit × ℕ) := inferInstance

/-- A toy backend over `Unit` data: `generate` returns its input generators; the other
operations are unused here and return default values. -/
def idOracle : Oracle (groupSig .unit) := ⟨fun op x =>
  match op, x with
  | .generate, (n, gs) => (n, gs, ())
  | _, _ => Ty.default _⟩

/-! ### Combining branch answers

The branch answers of the `S₃` example in `GraphIsoChecks/Semantics.lean`: representatives
`c` and `(0 2)` with trivial subgroups, and one empty branch. The combined answer keeps `c`
and the single representative difference `c⁻¹ (0 2) = (0 1)`. -/

def branchAnswers : List (AnswerData .unit) :=
  [some (PermData.ofPerm c3, (3, [], ())), some (PermData.ofPerm (swap (0 : Fin 3) 2), (3, [], ())),
    none]

def runCombine : Option (AnswerData .unit × ℕ) :=
  (eval idOracle (fun x => .ret x) 1000
    (combineProg (var := Ty.denote) (rec := (.unit, .unit)) (D := .unit) 3 branchAnswers)).map
    fun r => (r.1, Trace.localCost r.2)

example : runCombine =
    some (some (PermData.ofPerm c3, (3, [PermData.ofPerm (swap (0 : Fin 3) 1)], ())), 85) := by
  decide

-- The generator list has `Σ sᵢ + k - 1 = 0 + 2 - 1` entries, and the cost is within the bound.
example : (combineGens (PermData.ofPerm c3) (branchSuccesses branchAnswers)).length = 1 := by
  decide
example : 85 ≤ combineCost 3 branchAnswers 0 := by decide

-- The model used by the correctness theorem gives the same answer.
example : combineModel idOracle 3 branchAnswers =
    some (PermData.ofPerm c3, (3, [PermData.ofPerm (swap (0 : Fin 3) 1)], ())) := by
  decide

/-! ### Sequential processing

A placeholder sub-solver that returns its input coset, used only to evaluate the program's
bookkeeping: two windows `{0, 1}` and `{2}` in degree 3. -/

def trivialSub (I : (Ty.inst .unit).denote) :
    Prog (groupSig .unit) (.unit, .unit) Ty.denote (Ty.answer .unit) :=
  .bind (.op1 .snd I) fun wc => .bind (.op1 .snd wc) fun c => .op1 .some c

def coset₀ : CosetData .unit := (PermData.ofPerm c3, (3, [PermData.ofPerm t01], ()))

def runSeq : Option (AnswerData .unit × ℕ) :=
  (eval idOracle (fun x => .ret x) 1000
    (seqProg trivialSub (#[0, 0, 1], #[1, 0, 0]) coset₀ [[0, 1], [2]])).map
    fun r => (r.1, Trace.localCost r.2)

-- Cost `1 + Σ (C o + 2 n + 5 |o| + 13)` with `C = 3`: exactly the proved bound.
example : runSeq = some (some coset₀, 60) := by decide
example : 1 + ([[0, 1], [2]].map (seqCost 3 fun _ => 3)).sum = 60 := by decide

/-! ### Reductions with the recursive call as sub-solver -/

/-- Branch over a supplied cover, solving every branch by the enclosing procedure. -/
def branchRec : Proc (groupSig .unit) (.prod (Ty.inst .unit) Ty.gens) (Ty.answer .unit) :=
  fun _ Irs =>
    .bind (.op1 .fst Irs) fun I => .bind (.op1 .snd Irs) fun rs =>
    .bind (.op1 .fst I) fun xy => .bind (.op1 .snd I) fun wc =>
    .bind (.op1 .fst wc) fun w => .bind (.op1 .snd wc) fun c =>
    .bind (.op1 .fst c) fun σ => .bind (.op1 .snd c) fun K =>
    branchProg (fun J => .bind (.op2 .pair J rs) fun Jrs => .recur Jrs) xy w σ K rs

theorem branchRec_wf : branchRec.Wf := by
  intro var₁ var₂ x₁ x₂
  unfold branchRec
  prog_wf

/-- Process supplied windows sequentially, solving each by the enclosing procedure. -/
def seqRec : Proc (groupSig .unit) (Ty.inst .unit) (Ty.answer .unit) := fun _ I =>
  .bind (.op1 .fst I) fun xy => .bind (.op1 .snd I) fun wc =>
  .bind (.op1 .snd wc) fun c => .bind (.op0 .nil) fun os =>
  seqProg (fun J => .recur J) xy c os

theorem seqRec_wf : seqRec.Wf := by
  intro var₁ var₂ x₁ x₂
  unfold seqRec
  prog_wf

end GraphIsoChecks.Reductions
