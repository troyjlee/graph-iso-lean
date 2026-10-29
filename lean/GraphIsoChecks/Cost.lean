module

public import GraphIso
meta import GraphIso
public import Mathlib.Data.Fin.VecNotation
meta import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Perm
meta import Mathlib.Data.Fintype.Perm
import all Init.Data.Array.Basic
import all Init.Data.List.Sort.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Mathlib.Data.List.Sort

/-!
# Phase 2 and 3 checks: representations, evaluation, costs and substitution

* Validity checks and denotations of concrete represented data.
* Concrete evaluations of permutation programs: the result agrees with the functional model
  and the actual charged cost respects the proved bound.
* A toy backend with one operation, its implementation by a program, and the substitution
  theorem instantiated: the contract-charged and the implementation-charged costs.
-/

@[expose] public section

namespace GraphIsoChecks.Cost

open Equiv GraphIso GraphIso.Cost GraphIso.Programs

/-! ### Represented data -/

/-- The 3-cycle `0 ↦ 1 ↦ 2 ↦ 0`. -/
def c3 : Perm (Fin 3) := swap 0 1 * swap 1 2
/-- A transposition. -/
def t01 : Perm (Fin 3) := swap 0 1

example : PermData.ofPerm c3 = (#[1, 2, 0], #[2, 0, 1]) := by decide
example : PermData.validB 3 (#[1, 2, 0], #[2, 0, 1]) = true := by decide
-- Not mutually inverse:
example : PermData.validB 3 (#[1, 2, 0], #[1, 2, 0]) = false := by decide
-- Wrong length:
example : PermData.validB 3 (#[1, 0], #[1, 0]) = false := by decide

example : PermData.mul (PermData.ofPerm c3) (PermData.ofPerm t01) = PermData.ofPerm (c3 * t01) := by
  decide
example : PermData.mul (PermData.ofPerm t01) (PermData.ofPerm c3) ≠ PermData.ofPerm (c3 * t01) := by
  decide

/-- The window `{0, 1}` of `Fin 3`. -/
def w01 : WinData := ([0, 1], #[true, true, false])

example : WinData.validB 3 w01 = true := by decide
example : WinData.validB 3 ([0, 1], #[true, false, false]) = false := by decide
example : WinData.validB 3 ([0, 0], #[true, false, false]) = false := by decide

-- `(0 1)` preserves the window; the 3-cycle does not; neither fixes it pointwise.
example : GensData.invariantB [PermData.ofPerm t01] w01 = true := by decide
example : GensData.invariantB [PermData.ofPerm c3] w01 = false := by decide
example : GensData.fixesB [PermData.ofPerm t01] w01 = false := by decide
example : GensData.fixesB [PermData.ofPerm t01] ([2], #[false, false, true]) = true := by decide

-- Matching without inverses, and the normalized target `y ∘ σ`.
example : matchesB ([0, 1, 2], #[true, true, true]) (PermData.ofPerm c3) #[5, 6, 7] #[7, 5, 6] =
    true := by decide
example : StrData.comp #[7, 5, 6] (PermData.ofPerm c3) = #[5, 6, 7] := by decide

/-- A full represented instance with backend data of type `Unit`. -/
def inst : InstanceData Unit :=
  ⟨#[0, 1, 0], #[0, 0, 1], w01, PermData.ofPerm c3, [PermData.ofPerm t01], ()⟩

example : inst.validB 2 = true := by decide
-- The same instance with a generator that breaks the window's invariance is rejected.
example : ({ inst with gens := [PermData.ofPerm c3] } : InstanceData Unit).validB 2 = false := by
  decide

/-! ### Evaluating permutation programs -/

/-- A program over the empty signature, inside a trivial procedure. -/
abbrev LProg (t : Ty) := Prog Signature.empty (.unit, .unit) Ty.denote t

/-- Evaluate a local program; return its value and its local cost. -/
def run {t : Ty} (p : LProg t) : Option (t.denote × ℕ) :=
  (eval Ctx.empty.O (fun x => .ret x) 1000 p).map fun r => (r.1, Trace.localCost r.2)

def g : PermData := PermData.ofPerm c3
def h : PermData := PermData.ofPerm t01

example : run (permMul g h) = some (PermData.mul g h, 49) := by decide
example : 49 ≤ 12 * 3 + 13 := by decide
example : run (permInv g) = some (PermData.inv g, 3) := by decide
example : run (permApply g 2) = some (0, 2) := by decide
example : run (permOne 3) = some (PermData.one 3, 9) := by decide
example : run (permBeq g g) = some (true, 26) := by decide
example : run (permBeq g h) = some (false, 26) := by decide
example : 26 ≤ 6 * 3 + 10 := by decide

#guard (run (permMul g h)).map Prod.fst == some (PermData.mul g h)

/-! ### A toy backend and substitution

One operation `inc : nat → nat`. Its contract is `inc x = x + 1`, charged 10 per call; its
implementation is the primitive `add` with a literal, charged by its actual trace. -/

def incSig : Signature where
  Op := Unit
  arg _ := .nat
  res _ := .nat

/-- The successor function on the argument of `inc`. -/
def incFn (x : ℕ) : ℕ := x + 1

def incOracle : Oracle incSig := ⟨fun _ x => incFn x⟩
def incSchedule : CostSchedule incSig := ⟨fun _ _ _ => 10⟩

/-- The implementation of `inc`: build the literal `1` and add. -/
def incImpl : Impl incSig Signature.empty := fun _ _ _ x =>
  .bind (.op0 (.natLit 1)) fun one => .op2 .add x one

theorem incImpl_implements :
    Implements incOracle incSchedule (fun _ _ => True) incImpl Ctx.empty.O Ctx.empty.B := by
  intro op x _ a b body
  refine ⟨_, runs_bind.2 ⟨1, _, _, runs_prim.2 ⟨rfl, rfl⟩, runs_prim.2 ⟨rfl, rfl⟩, rfl⟩, ?_⟩
  simp [Trace.cost, Event.cost, Prim.cost, incSchedule]

/-- A client program calling `inc` twice. -/
def twice : Proc incSig .nat .nat := fun _ x =>
  .bind (.call () x) fun y => .call () y

def runTwice (x : ℕ) : Option (ℕ × ℕ) :=
  (eval incOracle (twice Ty.denote) 100 (twice Ty.denote x)).map fun r =>
    (r.1, Trace.cost incSchedule r.2)

def runTwiceSubst (x : ℕ) : Option (ℕ × ℕ) :=
  (eval Ctx.empty.O ((twice.subst incImpl) Ty.denote) 100 ((twice.subst incImpl) Ty.denote x)).map
    fun r => (r.1, Trace.localCost r.2)

-- Charged by contract: two calls at 10 each. Charged by implementation: 2 units per call.
example : runTwice 5 = some (7, 20) := by decide
example : runTwiceSubst 5 = some (7, 4) := by decide

-- The substitution theorem, instantiated.
example (x v : ℕ) (tr : Trace incSig)
    (h : Runs incOracle (twice Ty.denote) (twice Ty.denote x) v tr) :
    ∃ tr', Runs Ctx.empty.O ((twice.subst incImpl) Ty.denote) ((twice.subst incImpl) Ty.denote x)
      v tr' ∧ Trace.cost Ctx.empty.B tr' ≤ Trace.cost incSchedule tr :=
  Proc.runs_subst incImpl_implements twice h (fun _ _ => trivial)

end GraphIsoChecks.Cost
