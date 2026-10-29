module

public import GraphIso.Solver.Correctness

/-!
# The solver theorems against an abstract backend

For a backend meeting its contract on the four operations the solver calls
(`MeetsContractOn DV solverOps X.O`), whose calls are allowed by the context's preconditions
and whose charges and output generator counts are bounded
(`BackendBounds X DV n s`), the run of `solveBody` on a valid instance `I` of degree `n` with
at most `s` generators satisfies:

* `solve_correct`: the returned answer denotes exactly `iso W σ G x y`;
* `solve_none_iff`: it is `none` exactly when there is no solution;
* `solve_some_group`: a successful answer's generators generate `aut W G x`, the full
  automorphism subgroup of `x` in `G`, and its representative is a solution;
* `solve_cost_le`: its cost under the schedule `X.B` is at most `solveBound Q m N`, with
  `m = |W|`, `N = |G|` and `Q = solveQ n s …`: `Q` for the empty window and `2 m N Q - Q`
  otherwise; every backend call is charged on its actual argument and result.

The run exists, is unique (`Runs.unique`), and all its backend calls satisfy the
preconditions (`solve_calls_ok`), which is what backend substitution requires.
-/

@[expose] public section

namespace GraphIso.Solver

open Equiv Pointwise Cost Programs

variable {D : Ty} {X : Ctx (groupSig D)} {DV : ℕ → GensData → D.denote → Prop} {n s : ℕ}
  {xy : StrData × StrData} {w : WinData} {σd : PermData} {gs : GensData} {d : D.denote}

/-- The run of the solver on an instance, with its properties. -/
theorem solve_exists (hO : MeetsContractOn DV solverOps X.O)
    (hPre : ∀ op x, solverOps op → GroupPre DV op x → X.Pre op x)
    {G₀ : Subgroup (Perm (Fin n))} (B : BackendBounds X DV n s G₀)
    (hv : InstData.Valid (D := D) (xy, w, σd, n, gs, d) DV) (hs : gs.length ≤ s)
    (hG₀ : GensData.denote n gs ≤ G₀) :
    ∃ (ans : AnswerData D) (tr : Trace (groupSig D)),
      Runs X.O (solveBody D Ty.denote) (solveBody D Ty.denote (xy, w, σd, n, gs, d)) ans tr ∧
      Trace.cost X.B tr ≤
        solveBound (solveQ n s B.Borb B.Bstab B.Btr B.Bgen) w.1.length
          (Nat.card (GensData.denote n gs)) ∧
      Trace.CallsSatisfy X.Pre tr ∧
      AnsOK DV n (w.denote n) (σd.denote n) (gs.denote n) (xy.1.denote n) (xy.2.denote n) ans ∧
      ∀ c : CosetData D, ans = some c → c.2.gens.length ≤ s := by
  obtain ⟨ans, ⟨tr, hr, hc, hpre⟩, hok, hg⟩ :=
    solve_spec hO hPre B _ _ xy w σd gs d hv hs hG₀ rfl rfl
  exact ⟨ans, tr, hr, hc, hpre, hok, hg⟩

section Results

variable (hO : MeetsContractOn DV solverOps X.O)
  (hPre : ∀ op x, solverOps op → GroupPre DV op x → X.Pre op x)
  {G₀ : Subgroup (Perm (Fin n))} (B : BackendBounds X DV n s G₀)
  (hv : InstData.Valid (D := D) (xy, w, σd, n, gs, d) DV) (hs : gs.length ≤ s)
  (hG₀ : GensData.denote n gs ≤ G₀) {ans : AnswerData D} {tr : Trace (groupSig D)}
  (hrun : Runs X.O (solveBody D Ty.denote) (solveBody D Ty.denote (xy, w, σd, n, gs, d)) ans tr)
include hO hPre B hv hs hG₀ hrun

/-- The answer of any run, with the properties of `solve_exists`. -/
private theorem solve_props :
    Trace.cost X.B tr ≤
        solveBound (solveQ n s B.Borb B.Bstab B.Btr B.Bgen) w.1.length
          (Nat.card (GensData.denote n gs)) ∧
      Trace.CallsSatisfy X.Pre tr ∧
      AnsOK DV n (w.denote n) (σd.denote n) (gs.denote n) (xy.1.denote n) (xy.2.denote n) ans ∧
      ∀ c : CosetData D, ans = some c → c.2.gens.length ≤ s := by
  obtain ⟨ans', tr', hr', hc, hpre, hok, hg⟩ := solve_exists hO hPre B hv hs hG₀
  obtain ⟨rfl, rfl⟩ := hr'.unique hrun
  exact ⟨hc, hpre, hok, hg⟩

/-- **`solve_correct`**: the answer denotes exactly the solution set. -/
theorem solve_correct :
    Answer.denote (AnswerData.denote n ans) =
      iso (w.denote n) (σd.denote n) (gs.denote n) (xy.1.denote n) (xy.2.denote n) :=
  (solve_props hO hPre B hv hs hG₀ hrun).2.2.1.isCorrect

/-- **`solve_none_iff`**: the answer is `none` exactly when there is no solution. -/
theorem solve_none_iff :
    ans = none ↔
      iso (w.denote n) (σd.denote n) (gs.denote n) (xy.1.denote n) (xy.2.denote n) = ∅ := by
  have h := (solve_props hO hPre B hv hs hG₀ hrun).2.2.1.isCorrect
  constructor
  · rintro rfl
    exact h.symm
  · intro he
    rcases ans with _ | c
    · rfl
    · have := (Answer.IsCorrect.eq_none_iff h).2 he
      simp [AnswerData.denote] at this

/-- **`solve_some_group`**: a successful answer has a solution as representative, and its
generators generate the full automorphism subgroup of `x` in `G` on `W`. -/
theorem solve_some_group {c : CosetData D} (hc : ans = some c) :
    PermData.denote n c.1 ∈
        iso (w.denote n) (σd.denote n) (gs.denote n) (xy.1.denote n) (xy.2.denote n) ∧
      GensData.denote n c.2.gens = aut hv.invariant (xy.1.denote n) := by
  have h := (solve_props hO hPre B hv hs hG₀ hrun).2.2.1
  subst hc
  exact Answer.IsCorrect.of_some hv.invariant h.isCorrect

/-- **`solve_cost_le`**: the cost bound, with every backend call charged on its actual
argument and result. -/
theorem solve_cost_le :
    Trace.cost X.B tr ≤
      solveBound (solveQ n s B.Borb B.Bstab B.Btr B.Bgen) w.1.length
        (Nat.card (GensData.denote n gs)) :=
  (solve_props hO hPre B hv hs hG₀ hrun).1

/-- Every backend call of the run satisfies the preconditions. -/
theorem solve_calls_ok : Trace.CallsSatisfy X.Pre tr :=
  (solve_props hO hPre B hv hs hG₀ hrun).2.1

/-- The answer is valid represented data with at most `s` generators. -/
theorem solve_answer_valid {c : CosetData D} (hc : ans = some c) :
    c.1.Valid n ∧ c.2.degree = n ∧ GroupValid DV n c.2.gens c.2.data ∧ c.2.gens.length ≤ s := by
  have h := solve_props hO hPre B hv hs hG₀ hrun
  subst hc
  exact ⟨h.2.2.1.1, h.2.2.1.2.1, h.2.2.1.2.2.1, h.2.2.2 _ rfl⟩

end Results

end GraphIso.Solver
