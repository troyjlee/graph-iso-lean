module

public import GraphIso.Reductions.Data

/-!
# Local checks used by the solver

* `fixesProg gens pts`: do all generators fix all listed points? Its value is
  `GensData.fixesB gens (pts, _)`, which decides pointwise fixing by the generated group
  (`GensData.fixesB_iff`). Cost at most `s (5 m + 3) + 1` for `s` generators and `m` points.
* `matchesProg pts σ xy`: does `σ` carry `x` to `y` on the listed points? Its value is
  `matchesB (pts, _) σ x y` (`matchesB_iff`), computed without inverting `σ`. Cost at most
  `7 m + 3`.
-/

@[expose] public section

namespace GraphIso.Programs

open Cost

variable {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- Do all generators fix all listed points? -/
def fixesProg (gens : var Ty.gens) (pts : var (.list .nat)) : Prog S rec var .bool :=
  allList gens fun g => allList pts fun u => .bind (permApply g u) fun gu => .op2 .natEq gu u

/-- Does `σ` carry `x` to `y` at every listed point? -/
def matchesProg (pts : var (.list .nat)) (σ : var Ty.perm) (xy : var Ty.strs) :
    Prog S rec var .bool :=
  .bind (.op1 .fst xy) fun x => .bind (.op1 .snd xy) fun y =>
  allList pts fun u =>
    .bind (.op2 .arrayGet x u) fun xu =>
    .bind (permApply σ u) fun σu =>
    .bind (.op2 .arrayGet y σu) fun yσu =>
    .op2 .natEq xu yσu

section Specs

variable {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

theorem RunsWithin.fixesProg (gs : GensData) (w : WinData) :
    RunsWithin X body (Programs.fixesProg gs w.1) (GensData.fixesB gs w)
      (gs.length * (5 * w.1.length + 3) + 1) := by
  refine (RunsWithin.allList_le (c := 5 * w.1.length + 1) fun g _ => ?_).mono
    (by simp only [Nat.add_assoc, Nat.reduceAdd]; omega)
  refine (RunsWithin.allList_le (c := 3) fun u _ => ?_).mono (by omega)
  exact RunsWithin.bind_le (RunsWithin.permApply _ _) (RunsWithin.prim _ _) (by simp [Prim.cost])

theorem RunsWithin.matchesProg (w : WinData) (σ : PermData) (xy : StrData × StrData) :
    RunsWithin X body (Programs.matchesProg w.1 σ xy) (matchesB w σ xy.1 xy.2)
      (7 * w.1.length + 3) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    refine RunsWithin.allList_le (c := 5) fun u _ => ?_
    refine RunsWithin.bind_le (c₂ := 4) (RunsWithin.prim _ _) ?_ (by simp [Prim.cost])
    refine RunsWithin.bind_le (c₂ := 2) (RunsWithin.permApply _ _) ?_ le_rfl
    refine RunsWithin.bind_le (c₂ := 1) (RunsWithin.prim _ _) ?_ (by simp [Prim.cost])
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost]
    omega

end Specs

section Wf

variable {var₁ var₂ : Ty → Type} {r : Bool} {Γ : WfCtx var₁ var₂}

theorem wf_fixesProg {g₁ : var₁ Ty.gens} {g₂ : var₂ Ty.gens} {p₁ : var₁ (.list .nat)}
    {p₂ : var₂ (.list .nat)} (hg : ⟨Ty.gens, g₁, g₂⟩ ∈ Γ) (hp : ⟨.list .nat, p₁, p₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (fixesProg g₁ p₁) (fixesProg g₂ p₂) := by
  unfold fixesProg allList permApply
  prog_wf

theorem wf_matchesProg {p₁ : var₁ (.list .nat)} {p₂ : var₂ (.list .nat)} {σ₁ : var₁ Ty.perm}
    {σ₂ : var₂ Ty.perm} {xy₁ : var₁ Ty.strs} {xy₂ : var₂ Ty.strs}
    (hp : ⟨.list .nat, p₁, p₂⟩ ∈ Γ) (hσ : ⟨Ty.perm, σ₁, σ₂⟩ ∈ Γ) (hxy : ⟨Ty.strs, xy₁, xy₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (matchesProg p₁ σ₁ xy₁) (matchesProg p₂ σ₂ xy₂) := by
  unfold matchesProg allList permApply
  prog_wf

end Wf

end GraphIso.Programs
