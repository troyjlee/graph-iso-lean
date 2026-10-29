module

public import GraphIso.Solver.Main

/-!
# The public entry point

`solveEntry D` takes the instance with the group given by generators only:
`(x, y, W, σ, n, gs)`. It asks the backend to `generate` the group (building its backend data,
charged on the actual generators), then solves the instance by the recursive solver.

`solveEntry_spec`: for a backend meeting the contracts of the solver's operations, with bounds
`BackendBounds X DV n s ⟨gs⟩`, the entry returns a correct answer for
`iso W σ ⟨gs⟩ x y` at cost at most

  `11 + (charge of the initial generate) + solveBound Q |W| |⟨gs⟩|`.
-/

@[expose] public section

namespace GraphIso.Solver

open Equiv Pointwise Cost Programs

/-- The public input: strings, window, representative, degree and generators. -/
abbrev Ty.input : Cost.Ty :=
  .prod Cost.Ty.strs (.prod Cost.Ty.win (.prod Cost.Ty.perm (.prod .nat Cost.Ty.gens)))

variable {D : Cost.Ty}

/-- Generate the group, then solve. -/
def solveEntry (D : Cost.Ty) : (var : Cost.Ty → Type) → var Ty.input →
    Prog (groupSig D) (Rec D) var (Cost.Ty.answer D) := fun _ inp =>
  .bind (.op1 .fst inp) fun xy => .bind (.op1 .snd inp) fun r₁ =>
  .bind (.op1 .fst r₁) fun w => .bind (.op1 .snd r₁) fun r₂ =>
  .bind (.op1 .fst r₂) fun σ => .bind (.op1 .snd r₂) fun ng =>
  .bind (Prog.call (S := groupSig D) GroupOp.generate ng) fun G =>
  .bind (.op2 .pair σ G) fun c => .bind (.op2 .pair w c) fun wc => .bind (.op2 .pair xy wc) fun I =>
  .recur I

theorem solveEntry_wf {var₁ var₂ : Cost.Ty → Type} (x₁ : var₁ Ty.input) (x₂ : var₂ Ty.input) :
    Prog.Wf true [⟨Ty.input, x₁, x₂⟩] (solveEntry D var₁ x₁) (solveEntry D var₂ x₂) := by
  unfold solveEntry
  prog_wf

variable {X : Ctx (groupSig D)} {DV : ℕ → GensData → D.denote → Prop}

/-- **The public solver against an abstract backend.** -/
theorem solveEntry_spec (hO : MeetsContractOn DV solverOps X.O)
    (hPre : ∀ op x, solverOps op → GroupPre DV op x → X.Pre op x) {n s : ℕ}
    {xy : StrData × StrData} {w : WinData} {σd : PermData} {gs : GensData}
    (B : BackendBounds X DV n s (GensData.denote n gs)) (hw : w.Valid n) (hσ : σd.Valid n)
    (hgs : GensData.AllValid n gs) (hinv : IsInvariant (GensData.denote n gs) (w.denote n)) :
    ∃ ans : AnswerData D,
      RunsWithin X (solveBody D Cost.Ty.denote) (solveEntry D Cost.Ty.denote (xy, w, σd, n, gs))
        ans
        (11 + X.B.call .generate (n, gs) (X.O.run .generate (n, gs)) +
          solveBound (solveQ n s B.Borb B.Bstab B.Btr B.Bgen) w.1.length
            (Nat.card (GensData.denote n gs))) ∧
      AnsOK DV n (w.denote n) (σd.denote n) (gs.denote n) (xy.1.denote n) (xy.2.denote n) ans ∧
      ∀ c : CosetData D, ans = some c → c.2.gens.length ≤ s := by
  have hpreG : GroupPre DV .generate (n, gs) := hgs
  have hpost := hO .generate (n, gs) (Or.inr (Or.inr (Or.inr rfl))) hpreG
  have hsG := B.genOut gs hgs le_rfl
  rcases hG : X.O.run GroupOp.generate (n, gs) with ⟨n', gs', d⟩
  rw [hG] at hpost hsG
  obtain ⟨hn', hGv, hden⟩ := hpost
  change n' = n at hn'
  subst n'
  change GensData.denote n gs' = GensData.denote n gs at hden
  have hv : InstData.Valid (D := D) (xy, w, σd, n, gs', d) DV :=
    ⟨hw, hσ, hGv, by change IsInvariant (GensData.denote n gs') _; rw [hden]; exact hinv⟩
  obtain ⟨ans, hr, hok, hg⟩ := solve_spec hO hPre B _ _ xy w σd gs' d hv hsG
    (by rw [hden]) rfl rfl
  refine ⟨ans, ?_, ?_, hg⟩
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.call (X := X) (op := GroupOp.generate) (x := (n, gs))
        (hPre _ _ (Or.inr (Or.inr (Or.inr rfl))) hpreG))
      rw [hG]
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      exact RunsWithin.recur hr
    case hc =>
      simp only [Prim.cost, hG]
      rw [hden]
      omega
  · change AnsOK DV n (w.denote n) (σd.denote n) (GensData.denote n gs') _ _ ans at hok
    rw [hden] at hok
    exact hok

/-- **`solve_backend_refinement`**: substituting well-formed implementations that compute a
backend meeting the contracts, within its schedule on the allowed calls, gives a well-formed
solver over the implementations' signature that returns a correct answer within the generic
bound of `solveEntry_spec`. -/
theorem solve_backend_refinement {S' : Signature} (hO : MeetsContractOn DV solverOps X.O)
    (hPre : ∀ op x, solverOps op → GroupPre DV op x → X.Pre op x) {I : WfImpl (groupSig D) S'}
    {O' : Oracle S'} {B' : CostSchedule S'} (himpl : Implements X.O X.B X.Pre I.impl O' B')
    {n s : ℕ} {xy : StrData × StrData} {w : WinData} {σd : PermData} {gs : GensData}
    (B : BackendBounds X DV n s (GensData.denote n gs)) (hw : w.Valid n) (hσ : σd.Valid n)
    (hgs : GensData.AllValid n gs) (hinv : IsInvariant (GensData.denote n gs) (w.denote n)) :
    ∃ (ans : AnswerData D) (tr : Trace S'),
      Runs O' ((WfProc.subst ⟨solveBody D, solveBody_wf⟩ I).proc Cost.Ty.denote)
        ((solveEntry D Cost.Ty.denote (xy, w, σd, n, gs)).subst I.impl) ans tr ∧
      Trace.cost B' tr ≤
        11 + X.B.call .generate (n, gs) (X.O.run .generate (n, gs)) +
          solveBound (solveQ n s B.Borb B.Bstab B.Btr B.Bgen) w.1.length
            (Nat.card (GensData.denote n gs)) ∧
      AnsOK DV n (w.denote n) (σd.denote n) (gs.denote n) (xy.1.denote n) (xy.2.denote n) ans := by
  obtain ⟨ans, ⟨tr, hr, hc, hpre⟩, hok, -⟩ := solveEntry_spec hO hPre B hw hσ hgs hinv
  obtain ⟨tr', hr', hc'⟩ := Runs.subst himpl hr hpre
  exact ⟨ans, tr', hr', hc'.trans hc, hok⟩

end GraphIso.Solver
