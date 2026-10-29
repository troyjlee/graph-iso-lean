module

public import GraphIso.Solver.Entry
public import GraphIso.Programs.Validate

/-!
# The validating entry point

`solveEntry` decodes its input totally and checks nothing: a string is read through
`StrData.denote n`, so entries past the array read as `0`, entries past the degree `n` are
ignored, and symbols are unbounded naturals. Its theorems assume valid window, representative
and generators and an invariant window, and say nothing about the strings' lengths.

`solveChecked D` takes an alphabet bound `q` together with the input and first checks the
whole input contract `InputValid q`:

* both strings have length `n` and symbols below `q` (`StrData.Valid n q`);
* the window, the representative and the generators are valid data of degree `n`;
* the window is invariant under the group.

The check is `InstanceData.validB` for the degree `n` (`inputValidB_eq_validB`). On invalid
input the result is `none`; otherwise it is `some` of the answer of `solveEntry`. The check is
a program in the cost language, charged at most `validCost n m s` for window size `m` and `s`
generators: quadratic in `m`, and linear in `n` and in `s` otherwise.

`solveChecked_spec` states correctness and cost against a backend meeting the contracts, with
no hypothesis on the input.
-/

@[expose] public section

namespace GraphIso.Solver

open Equiv Pointwise Cost Programs

/-- The checked input: an alphabet bound and the public input. -/
abbrev Ty.checked : Cost.Ty := .prod .nat Ty.input

/-- The input contract for the alphabet bound `q`. -/
def InputValid (q : ℕ) : Ty.input.denote → Prop
  | (xy, w, σd, n, gs) => StrData.Valid n q xy.1 ∧ StrData.Valid n q xy.2 ∧ WinData.Valid n w ∧
      PermData.Valid n σd ∧ GensData.AllValid n gs ∧
      IsInvariant (GensData.denote n gs) (WinData.denote n w)

/-- The executable input check. -/
def inputValidB (q : ℕ) : Ty.input.denote → Bool
  | (xy, w, σd, n, gs) => StrData.validB n q xy.1 && StrData.validB n q xy.2 &&
      WinData.validB n w && PermData.validB n σd && GensData.allValidB n gs &&
      GensData.invariantB gs w

theorem inputValidB_iff {q n : ℕ} {xy : StrData × StrData} {w : WinData} {σd : PermData}
    {gs : GensData} :
    inputValidB q (xy, w, σd, n, gs) = true ↔ InputValid q (xy, w, σd, n, gs) := by
  simp only [inputValidB, InputValid, Bool.and_eq_true, StrData.validB_iff, WinData.validB_iff,
    PermData.validB_iff, GensData.allValidB_iff]
  constructor
  · rintro ⟨⟨⟨⟨⟨hx, hy⟩, hw⟩, hσ⟩, hgs⟩, hi⟩
    exact ⟨hx, hy, hw, hσ, hgs, (GensData.invariantB_iff hgs hw).1 hi⟩
  · rintro ⟨hx, hy, hw, hσ, hgs, hi⟩
    exact ⟨⟨⟨⟨⟨hx, hy⟩, hw⟩, hσ⟩, hgs⟩, (GensData.invariantB_iff hgs hw).2 hi⟩

/-- The check is the instance check `InstanceData.validB` at the degree `|x|`. -/
theorem inputValidB_eq_validB {E : Type} (q : ℕ) (x y : StrData) (w : WinData) (σd : PermData)
    (gs : GensData) (e : E) :
    inputValidB q ((x, y), w, σd, x.size, gs) = InstanceData.validB q ⟨x, y, w, σd, gs, e⟩ :=
  rfl

/-- The cost bound of the input check, for degree `n`, window size `m` and `s` generators. -/
def validCost (n m s : ℕ) : ℕ :=
  (m + 1) * (3 * m + 9) + n * (3 * m + 10) + s * (14 * n + 4 * m + 16) + 24 * n + 4 * m + 54

variable {S : Signature} {rec : Cost.Ty × Cost.Ty} {var : Cost.Ty → Type}

/-- The input check as a program. -/
def inputValidProg (q : var .nat) (inp : var Ty.input) : Prog S rec var .bool :=
  .bind (.op1 .fst inp) fun xy => .bind (.op1 .snd inp) fun r₁ =>
  .bind (.op1 .fst r₁) fun w => .bind (.op1 .snd r₁) fun r₂ =>
  .bind (.op1 .fst r₂) fun σ => .bind (.op1 .snd r₂) fun ng =>
  .bind (.op1 .fst ng) fun n => .bind (.op1 .snd ng) fun gs =>
  .bind (.op1 .fst xy) fun x => .bind (.op1 .snd xy) fun y =>
  .bind (strValidProg n q x) fun vx => .bind (strValidProg n q y) fun vy =>
  .bind (winValidProg n w) fun vw => .bind (permValidProg n σ) fun vσ =>
  .bind (gensValidProg n gs) fun vg => .bind (invariantProg gs w) fun vi =>
  .bind (.op2 .and vx vy) fun c₁ => .bind (.op2 .and c₁ vw) fun c₂ =>
  .bind (.op2 .and c₂ vσ) fun c₃ => .bind (.op2 .and c₃ vg) fun c₄ => .op2 .and c₄ vi

theorem RunsWithin.inputValidProg {a b : Cost.Ty} {X : Ctx S}
    {body : a.denote → Prog S (a, b) Cost.Ty.denote b} (q n : ℕ) (xy : StrData × StrData)
    (w : WinData) (σd : PermData) (gs : GensData) :
    RunsWithin X body (Solver.inputValidProg q (xy, w, σd, n, gs))
      (inputValidB q (xy, w, σd, n, gs)) (validCost n w.1.length gs.length) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.strValidProg n q xy.1)
    run_step (RunsWithin.strValidProg n q xy.2)
    run_step (RunsWithin.winValidProg n w)
    run_step (RunsWithin.permValidProg n σd)
    run_step (RunsWithin.gensValidProg n gs)
    run_step (RunsWithin.invariantProg gs w)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, validCost]
    nlinarith

/-- Check the input contract, then solve. -/
def solveChecked (D : Cost.Ty) : (var : Cost.Ty → Type) → var Ty.checked →
    Prog (groupSig D) (Rec D) var (.option (Cost.Ty.answer D)) := fun var qi =>
  .bind (.op1 .fst qi) fun q => .bind (.op1 .snd qi) fun inp =>
  .bind (inputValidProg q inp) fun ok =>
  .ite ok (.bind (solveEntry D var inp) fun ans => .op1 .some ans) (.op0 .none)

theorem solveChecked_wf {D : Cost.Ty} {var₁ var₂ : Cost.Ty → Type} (x₁ : var₁ Ty.checked)
    (x₂ : var₂ Ty.checked) :
    Prog.Wf true [⟨Ty.checked, x₁, x₂⟩] (solveChecked D var₁ x₁) (solveChecked D var₂ x₂) := by
  unfold solveChecked inputValidProg strValidProg winValidProg nodupProg nodupStep permValidProg
    gensValidProg invariantProg allList anyList solveEntry
  prog_wf

variable {D : Cost.Ty} {X : Ctx (groupSig D)} {DV : ℕ → GensData → D.denote → Prop}

/-- **The validating entry against an abstract backend.** On every input, the result is
`none` exactly when the input contract fails; otherwise it is a correct answer. The cost is
the check plus, on valid input, the bound of `solveEntry_spec`. -/
theorem solveChecked_spec (hO : MeetsContractOn DV solverOps X.O)
    (hPre : ∀ op x, solverOps op → GroupPre DV op x → X.Pre op x) {q n s : ℕ}
    {xy : StrData × StrData} {w : WinData} {σd : PermData} {gs : GensData}
    (B : BackendBounds X DV n s (GensData.denote n gs)) :
    ∃ r : Option (AnswerData D),
      RunsWithin X (solveBody D Cost.Ty.denote)
        (solveChecked D Cost.Ty.denote (q, xy, w, σd, n, gs)) r
        (validCost n w.1.length gs.length + 4 +
          if inputValidB q (xy, w, σd, n, gs) then
            11 + X.B.call .generate (n, gs) (X.O.run .generate (n, gs)) +
              solveBound (solveQ n s B.Borb B.Bstab B.Btr B.Bgen) w.1.length
                (Nat.card (GensData.denote n gs))
          else 0) ∧
      (r = none ↔ ¬ InputValid q (xy, w, σd, n, gs)) ∧
      ∀ ans : AnswerData D, r = some ans →
        AnsOK DV n (w.denote n) (σd.denote n) (gs.denote n) (xy.1.denote n) (xy.2.denote n) ans ∧
          ∀ c : CosetData D, ans = some c → c.2.gens.length ≤ s := by
  have hv := RunsWithin.inputValidProg (X := X) (body := solveBody D Cost.Ty.denote) q n xy w σd gs
  cases hb : inputValidB q (xy, w, σd, n, gs) with
  | false =>
    refine ⟨none, ?_, ⟨fun _ hi => absurd (inputValidB_iff.2 hi) (by rw [hb]; simp),
      fun _ => rfl⟩, fun _ h => absurd h (by simp)⟩
    rw [hb] at hv
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step hv
      exact RunsWithin.ite_false (RunsWithin.prim _ _)
    case hc =>
      simp only [Prim.cost]
      omega
  | true =>
    obtain ⟨-, -, hw, hσ, hgs, hinv⟩ := inputValidB_iff.1 hb
    obtain ⟨ans, hr, hok, hg⟩ := solveEntry_spec hO hPre B hw hσ hgs hinv
    refine ⟨some ans, ?_, ⟨fun h => absurd h (by simp), fun h => absurd (inputValidB_iff.1 hb) h⟩,
      fun a ha => ?_⟩
    · rw [hb] at hv
      apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step hv
        apply RunsWithin.ite_true
        run_step hr
        exact RunsWithin.prim _ _
      case hc =>
        simp only [Prim.cost, ↓reduceIte]
        omega
    · cases ha
      exact ⟨hok, hg⟩

end GraphIso.Solver
