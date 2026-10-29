module

public import GraphIso.Programs.Checks
public import GraphIso.Solver.Facts

/-!
# The recursive solver

`solveBody D` is one closed recursive procedure from represented instances to represented
answers, over the group-backend signature `groupSig D`. On the instance `(x, y, W, σ • G)`:

1. **Empty window.** Return the input coset.
2. **Pointwise-fixed window.** If every generator fixes every point of `W` (so `G` fixes `W`
   pointwise), check whether `σ` carries `x` to `y` on `W`: return the input coset or `none`.
3. **Several orbits.** Otherwise ask the backend for the orbits of `G` on `W`. If there are at
   least two, process them sequentially in the updated cosets (`seqProg`), solving each by a
   recursive call.
4. **Transitive window.** If there is one orbit, take the first window point `u`, ask the
   backend for the stabilizer `G_u` and an orbit transversal, and branch (`branchProg`),
   solving each branch coset `(σ * r) • G_u` by a recursive call.

Recursive calls happen only through `recur`, as the sub-solver of the two reductions. Orbit
calls have smaller windows; branch calls keep the window and pass to the point stabilizer,
whose order is the group order divided by the orbit length (at least 2). The procedure is
well-formed (`solveBody_wf`).
-/

@[expose] public section

namespace GraphIso.Solver

open Cost Programs

variable {var : Ty → Type} {D : Ty}

/-- The recursion type of the solver. -/
abbrev Rec (D : Ty) : Ty × Ty := (Ty.inst D, Ty.answer D)

/-- The transitive case: branch over the stabilizer of the window point `u`. -/
def transitiveCase (xy : var Ty.strs) (w : var Ty.win) (σ : var Ty.perm)
    (G : var (Ty.group D)) (u : var .nat) : Prog (groupSig D) (Rec D) var (Ty.answer D) :=
  .bind (.op2 .pair G u) fun Gu =>
  .bind (Prog.call (S := groupSig D) GroupOp.stabilizer Gu) fun K =>
  .bind (Prog.call (S := groupSig D) GroupOp.orbitTransversal Gu) fun trs =>
  .bind (mapList trs fun vr => .op1 .snd vr) fun rs =>
  branchProg (fun J => .recur J) xy w σ K rs

/-- The window is not fixed pointwise: split into orbits, or branch if transitive. -/
def movedCase (xy : var Ty.strs) (w : var Ty.win) (c : var (Ty.coset D)) (σ : var Ty.perm)
    (G : var (Ty.group D)) (u : var .nat) : Prog (groupSig D) (Rec D) var (Ty.answer D) :=
  .bind (.op2 .pair G w) fun Gw =>
  .bind (Prog.call (S := groupSig D) GroupOp.orbits Gw) fun os =>
  .caseList os (.op0 .none) fun _ orest =>
    .caseList orest (transitiveCase xy w σ G u) fun _ _ => seqProg (fun J => .recur J) xy c os

/-- The group fixes the window pointwise: the answer is the input coset or `none`. -/
def fixedCase (xy : var Ty.strs) (pts : var (.list .nat)) (σ : var Ty.perm)
    (c : var (Ty.coset D)) : Prog (groupSig D) (Rec D) var (Ty.answer D) :=
  .bind (matchesProg pts σ xy) fun ok => .ite ok (.op1 .some c) (.op0 .none)

/-- A nonempty window: test pointwise fixing by the generators, then dispatch. -/
def nonemptyCase (xy : var Ty.strs) (w : var Ty.win) (pts : var (.list .nat))
    (c : var (Ty.coset D)) (σ : var Ty.perm) (G : var (Ty.group D)) (u : var .nat) :
    Prog (groupSig D) (Rec D) var (Ty.answer D) :=
  .bind (.op1 .snd G) fun gd => .bind (.op1 .fst gd) fun gens =>
  .bind (fixesProg gens pts) fun fixed =>
  .ite fixed (fixedCase xy pts σ c) (movedCase xy w c σ G u)

/-- The solver. -/
def solveBody (D : Ty) : Proc (groupSig D) (Ty.inst D) (Ty.answer D) := fun _ I =>
  .bind (.op1 .fst I) fun xy => .bind (.op1 .snd I) fun wc =>
  .bind (.op1 .fst wc) fun w => .bind (.op1 .snd wc) fun c =>
  .bind (.op1 .fst c) fun σ => .bind (.op1 .snd c) fun G =>
  .bind (.op1 .fst w) fun pts =>
  .caseList pts (.op1 .some c) fun u _ => nonemptyCase xy w pts c σ G u

/-- The solver is a well-formed procedure. -/
theorem solveBody_wf : (solveBody D).Wf := by
  intro var₁ var₂ x₁ x₂
  unfold solveBody nonemptyCase fixedCase movedCase transitiveCase
  prog_wf

end GraphIso.Solver
