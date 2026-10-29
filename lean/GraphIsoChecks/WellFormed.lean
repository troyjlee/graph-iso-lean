module

public import GraphIsoChecks.Cost
import all Init.Data.Array.Basic
import all Init.Data.List.Sort.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Mathlib.Data.List.Sort

/-!
# Well-formedness checks

Regression checks for two gaps found in review, and for the accepted programs:

1. A raw `Proc` can inspect its variable type by classical case analysis on `var .nat = ℕ` and
   apply an arbitrary Lean function to a runtime value at zero charged cost
   (`hidden_runs_uncharged`). It is rejected by `Proc.Wf` (`hidden_not_wf`).
2. An executable implementation can match on the client's recursion type and call `recur`
   (`sneaky`). It is rejected by `Impl.Wf` (`sneaky_not_wf`).
3. The library and example programs are well-formed, and well-formedness survives
   substitution.
-/

@[expose] public section

namespace GraphIsoChecks.WellFormed

open GraphIso GraphIso.Cost GraphIso.Programs GraphIsoChecks.Cost

/-! ### A raw procedure that computes outside the charged constructors -/

/-- The procedure from the review, as a family of programs: at `var := Ty.denote` it returns
`f x` with no charged step. -/
theorem hidden_runs_uncharged (f : ℕ → ℕ) (x : ℕ) :
    ∃ P : Proc Signature.empty .nat .nat,
      RunsWithin Ctx.empty (P Ty.denote) (P Ty.denote x) (f x) 0 := by
  classical
  refine ⟨fun var y => if h : var .nat = ℕ then .ret (cast h.symm (f (cast h y))) else .ret y,
    ?_⟩
  simp only [dite_true, cast_eq]
  exact RunsWithin.ret _

/-- The same procedure is not well-formed, for any `f` that is not the identity at `0`. -/
theorem hidden_not_wf (f : ℕ → ℕ) (hf : f 0 ≠ 0) :
    ¬ Proc.Wf (S := Signature.empty) (a := .nat) (b := .nat) (fun var y =>
      haveI := Classical.propDecidable (var .nat = ℕ)
      if h : var .nat = ℕ then .ret (cast h.symm (f (cast h y))) else .ret y) := by
  intro hw
  have h := hw Ty.denote Ty.denote 0 0
  simp only [dite_true, cast_eq] at h
  have hx := Prog.Wf.ret_inv h
  simp only [List.mem_singleton, Sigma.mk.injEq, Prod.mk.injEq, heq_eq_eq, true_and] at hx
  exact hf hx.1

/-! ### An implementation that calls back into the client -/

/-- Matches on the client's recursion type and, at `(.nat, .nat)`, calls `recur`. -/
def sneaky : Impl incSig Signature.empty := fun _ rec _ x =>
  match rec with
  | (.nat, .nat) => .recur x
  | _ => .bind (.op0 (.natLit 1)) fun one => .op2 .add x one

theorem sneaky_recurs {var : Ty → Type} (x : var .nat) :
    sneaky () (.nat, .nat) var x = .recur x := rfl

theorem sneaky_not_wf : ¬ sneaky.Wf := by
  intro hw
  have h := hw () (.nat, .nat) Ty.denote Ty.denote (0 : ℕ) (0 : ℕ)
  exact Prog.Wf.not_recur h

/-! ### Accepted programs -/

theorem incImpl_wf : incImpl.Wf := by
  intro op rec var₁ var₂ x₁ x₂
  unfold incImpl
  prog_wf

theorem twice_wf : twice.Wf := by
  intro var₁ var₂ x₁ x₂
  unfold twice
  prog_wf

/-- `twice`, with `inc` implemented, is still well-formed. -/
def twiceImplemented : WfProc Signature.empty .nat .nat :=
  WfProc.subst ⟨twice, twice_wf⟩ ⟨incImpl, incImpl_wf⟩

example : (twiceImplemented.proc Ty.denote 5) = (twice.subst incImpl) Ty.denote 5 := rfl

/-- A procedure using the permutation library: square a permutation. -/
def square : Proc Signature.empty Ty.perm Ty.perm := fun _ g => permMul g g

theorem square_wf : square.Wf := fun _ _ _ _ =>
  wf_permMul List.mem_cons_self List.mem_cons_self

/-- A recursive procedure: count down to zero. -/
def countdown : Proc Signature.empty .nat .nat := fun _ k =>
  .bind (.op0 (.natLit 0)) fun z =>
  .bind (.op2 .natEq k z) fun done =>
  .ite done (.ret k)
    (.bind (.op0 (.natLit 1)) fun one => .bind (.op2 .sub k one) fun k' => .recur k')

theorem countdown_wf : countdown.Wf := by
  intro var₁ var₂ x₁ x₂
  unfold countdown
  prog_wf

example : (eval Ctx.empty.O (countdown Ty.denote) 100 (countdown Ty.denote 3)).map
    (fun r => (r.1, Trace.localCost r.2)) = some (0, 21) := by decide

/-! ### Encoded sizes of transversals -/

/-- A transversal with two pairs at degree 3 has `1 + 2 * (2 * 3 + 3) = 19` cells. -/
example : Ty.size (.list (.prod .nat Ty.perm))
    [(1, PermData.ofPerm c3), (2, PermData.ofPerm (c3 * c3))] = 19 := by decide

example : Ty.size (.list (.prod .nat Ty.perm))
    [(1, PermData.ofPerm c3), (2, PermData.ofPerm (c3 * c3))] = 1 + 2 * (2 * 3 + 3) :=
  Ty.size_transversal (n := 3) (by
    intro vr hvr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hvr
    rcases hvr with rfl | rfl <;> exact PermData.valid_ofPerm _)

end GraphIsoChecks.WellFormed
