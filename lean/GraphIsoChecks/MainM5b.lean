module

public import GraphIsoChecks.MainM5
meta import GraphIsoChecks.MainM5
import all Init.Data.Array.Basic
import all Init.Data.List.Sort.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Mathlib.Data.List.Sort

/-!
# Milestone 14, stage 14j-4 checks (2): Cases 2b and 3, and the whole step at `m = 5`

Kernel-checked executions of the stage 14j-4 programs that are too large for a single kernel
check, each proved in pieces by the kernel execution toolkit (`GraphIsoChecks.Exec`,
`execRuns`): every theorem has the form `∃ v s, RunsS ssOracle body0 recF P v s ∧ Q v s`
for the **actual program** `P`, run with the verified Schreier–Sims oracle answering the backend
calls and milestone 1's solver as the recursive procedure (`body0`); sub-calls go to the
instrumented sub-solver `MainSteps.spySub`, `s` is the list of its recorded children
(`flatMap_recF`: the `MainSteps.records` of the trace), and `Q` (decided by the kernel) compares
the answer `v` with the brute-force solution set and the children `s` with the stated bounds of
the program's spec (`MainM5.kidsOK`). Each piece of the run (at most 5000 trace events) and
each composition step is a separate declaration, so no single kernel check exceeds a few GB.

* **Case 3** (`m5Case3Prog`, called with hand-built fixed points `Vx`, `Vy`, as stage 14i's
  `case3Prog` checks): `S₃` acting on three window strings and the base alike (labels `{i}`),
  `k = 1`: one distinguished point (`Vx = {0}`, `Vy = {1}`: two isomorphisms), a non-isomorphic
  pair, and the fallback (`V = [0, 1, 2]`: no good list, the kernel reduction `m3Prog`); the
  children meet `RunsWithin.m5Case3Prog`'s bounds (`c3Count |Vx| k n` comparisons, `StepChild`
  children with the factor `c3R k |Vy| (sojZ m) · m! + m!`).
* **Case 2b** (`m5Case2bProg`, called with the full groups `F(x) = F(y)` the Klein group, normal
  in `G = S₄`, as stage 14h's `case2bProg` check, on the large orbit `Φ = [4]`, which the Klein
  group does not act on `2`-transitively): `S₄` on four window strings and the base alike,
  `x = y` constant: the answer is all of `S₄`, the children are `StepChild` children with the
  factor `c2bR … · m!`.
* **The whole step at base size `5`** (`m5StepProg` on `S₅` acting on five window strings and the
  base alike, labels `{i}`, `x = 0 0 0 1 2`, `y = 0 1 0 2 0`), with the relaxed certificate size
  `k = 3` (see `MainM5` for why the admissible size is out of reach): the certificates of the
  restricted instance's strings compute `S₃` on the large orbit of each (`cert_x5`, `cert_y5`,
  the values `Fx5`, `Fy5`), and the whole step's answer is the brute-force coset (six
  isomorphisms), with the children meeting the stated bounds of `RunsWithin.m5StepProg` for
  these full groups.
-/

@[expose] public section

namespace GraphIsoChecks.MainM5b

open Equiv GraphIso GraphIso.Cost GraphIso.Programs GraphIso.Sims GraphIso.Main GraphIso.Toolkit
  GraphIsoChecks.Sweep GraphIsoChecks.Exec GraphIsoChecks.ExecSteps GraphIsoChecks.MainM5

/-! ### Case 3 -/

def s3 : List (List ℕ) := alike [[1, 0, 2], [1, 2, 0]]
def l3 : Array (List ℕ) := #[[0], [1], [2]]
/-- `S₃` on three window strings and the base alike, labels `{i}`. -/
def mk3 (x y : List ℕ) : MainSteps.SFix := ⟨3, 6, s3, [0, 1, 2], List.range 6, x ++ [0, 0, 0],
  y ++ [0, 0, 0], some l3⟩

/-- **Case 3** (`m5Case3Prog`, with `spySub`, the fixed points `Vx`, `Vy` and `k`). -/
def c3P (f : MainSteps.SFix) (k : ℕ) (Vx Vy : List ℕ) :
    Prog (groupSig Ty.unit) (Solver.Rec Ty.unit) Ty.denote (Ty.answer Ty.unit) :=
  m5Case3Prog MainSteps.spySub f.hinst f.n f.n l3 noSt k (f.x.toArray, f.y.toArray)
    (WinData.ofPoints f.N f.w) (f.N, gD f.gs, ()) Vx Vy

/-- Case 3's answer and children against brute force and `RunsWithin.m5Case3Prog`'s bounds. -/
def c3Q (f : MainSteps.SFix) (k : ℕ) (Vx Vy : List ℕ) (v : AnswerData Ty.unit)
    (cs : List MainSteps.Child) : Bool :=
  let m := f.N - f.n
  f.ok && MainSteps.ansOK f.N f.sols v &&
    kidsOK f f.n k (c3Count Vx.length k f.n) 0
      (Case3.c3R k Vy.length (Case2b.sojZ m) * m.factorial + m.factorial) cs

/-- One distinguished point. -/
def f3a : MainSteps.SFix := mk3 [1, 0, 0] [0, 1, 0]
/-- A non-isomorphic pair. -/
def f3b : MainSteps.SFix := mk3 [1, 0, 0] [0, 0, 0]

run_cmd
  execRuns `c3_iso.run
    (← `(RunsS ssOracle body0 recF (c3P f3a 1 [0] [1])))
    ssOracle body0 recF (c3P f3a 1 [0] [1]) cfg5
/-- **Case 3, one distinguished point** (`Vx = {0}`, `Vy = {1}`): two isomorphisms. -/
theorem c3_iso : ∃ v s, RunsS ssOracle body0 recF (c3P f3a 1 [0] [1]) v s ∧
    c3Q f3a 1 [0] [1] v s = true :=
  ⟨_, _, c3_iso.run, by decide +kernel⟩
run_cmd
  execRuns `c3_noniso.run
    (← `(RunsS ssOracle body0 recF (c3P f3b 1 [0] [1])))
    ssOracle body0 recF (c3P f3b 1 [0] [1]) cfg5
/-- **Case 3, a non-isomorphic pair.** -/
theorem c3_noniso : ∃ v s, RunsS ssOracle body0 recF (c3P f3b 1 [0] [1]) v s ∧
    c3Q f3b 1 [0] [1] v s = true :=
  ⟨_, _, c3_noniso.run, by decide +kernel⟩
run_cmd
  execRuns `c3_fallback.run
    (← `(RunsS ssOracle body0 recF (c3P f3a 1 [0, 1, 2] [0, 1, 2])))
    ssOracle body0 recF (c3P f3a 1 [0, 1, 2] [0, 1, 2]) cfg5
/-- **Case 3, the fallback**: no good list for `V = [0, 1, 2]`, `k = 1`; the kernel reduction. -/
theorem c3_fallback : ∃ v s, RunsS ssOracle body0 recF (c3P f3a 1 [0, 1, 2] [0, 1, 2]) v s ∧
    c3Q f3a 1 [0, 1, 2] [0, 1, 2] v s = true :=
  ⟨_, _, c3_fallback.run, by decide +kernel⟩

/-! ### Case 2b -/

/-- The Klein group on `[4]`, on the strings and the base alike. -/
def klein : List (List ℕ) := alike [[1, 0, 3, 2], [2, 3, 0, 1]]

/-- **Case 2b** (`m5Case2bProg`, with `spySub` and `F(x) = F(y) = ⟨fs⟩` on the large orbit
`Φ`). -/
def c2bP (f : MainSteps.SFix) (fs : List (List ℕ)) (Φ : List ℕ) :
    Prog (groupSig Ty.unit) (Solver.Rec Ty.unit) Ty.denote (Ty.answer Ty.unit) :=
  let F : GroupData Ty.unit.denote := (f.N, gD fs, ())
  m5Case2bProg MainSteps.spySub f.n f.n l4 noSt (f.x.toArray, f.y.toArray)
    (WinData.ofPoints f.N f.w) (f.N, gD f.gs, ()) F F Φ Φ

/-- Case 2b's answer and children: `F` is not `(|Φ| − 2)`-transitive on `Φ` (Case 2b:
`degD < |Φ| − 2`), the answer is the brute-force coset, and the children are `StepChild`
children with the factor `c2bR … · m!`. -/
def c2bQ (f : MainSteps.SFix) (fs : List (List ℕ)) (Φ : List ℕ) (v : AnswerData Ty.unit)
    (cs : List MainSteps.Child) : Bool :=
  let m := f.N - f.n
  let F : GroupData Ty.unit.denote := (f.N, gD fs, ())
  f.ok && decide (Case2b.degD ssOracle f.N f.n F Φ < Φ.length - 2) &&
    MainSteps.ansOK f.N f.sols v &&
    kidsOK f f.n 1 0 0
      (Case2b.c2bR f.N f.n Φ.length (Case2b.degD ssOracle f.N f.n F Φ - 1) (Case2b.sojZ m) *
        m.factorial) cs

/-- `S₄` on four window strings and the base alike, `x = y` constant. -/
def f2b : MainSteps.SFix := mk4 s4 [0, 0, 0, 0] [0, 0, 0, 0]

run_cmd
  execRuns `c2b_klein.run
    (← `(RunsS ssOracle body0 recF (c2bP f2b klein [0, 1, 2, 3])))
    ssOracle body0 recF (c2bP f2b klein [0, 1, 2, 3]) cfg5
/-- **Case 2b** on `S₄` with `F` the Klein group: the answer is all of `S₄`. -/
theorem c2b_klein : ∃ v s, RunsS ssOracle body0 recF (c2bP f2b klein [0, 1, 2, 3]) v s ∧
    c2bQ f2b klein [0, 1, 2, 3] v s = true :=
  ⟨_, _, c2b_klein.run, by decide +kernel⟩

/-! ### The whole step at base size 5 -/

/-- `S₅` on five window strings and the base alike; `x = 0 0 0 1 2`, `y = 0 1 0 2 0` (six
isomorphisms). -/
def f5 : MainSteps.SFix := mkD [0, 0, 0, 1, 2] [0, 1, 0, 2, 0]

/-- The full groups the certificates compute (`k = 3`): `S₃` on the large orbit of each string
(`{0, 1, 2}` and `{0, 2, 4}`). -/
def Fx5 : GroupData Ty.unit.denote := (10, gD ([[0, 2, 1, 3, 4, 5, 7, 6, 8, 9],
  [1, 2, 0, 3, 4, 6, 7, 5, 8, 9], [2, 1, 0, 3, 4, 7, 6, 5, 8, 9]] ++ ids 10 10), ())
def Fy5 : GroupData Ty.unit.denote := (10, gD ([[0, 1, 4, 3, 2, 5, 6, 9, 8, 7],
  [2, 1, 4, 3, 0, 7, 6, 9, 8, 5], [4, 1, 2, 3, 0, 9, 6, 7, 8, 5]] ++ ids 10 10), ())

/-- The restricted instance of `f5` (`rbR f5 lD`, by `R5_eq`), written out: the strings on the
five window points and the base, the window `[0, 5)`, the identity, the restricted group (the
restrictions of the generators of `S₅`, then the identity), `n₀ = n = 5`, the labels `{i}`. -/
def R5 : HInstData Ty.unit :=
  (((#[0, 0, 0, 1, 2, 0, 0, 0, 0, 0], #[0, 1, 0, 2, 0, 0, 0, 0, 0, 0]),
    (([0, 1, 2, 3, 4], #[true, true, true, true, true, false, false, false, false, false]),
      (ofList (List.range 10), (10, gD ([[0, 1, 2, 4, 3, 5, 6, 7, 9, 8],
        [0, 1, 4, 3, 2, 5, 6, 9, 8, 7], [3, 0, 4, 2, 1, 8, 5, 9, 7, 6],
        [0, 3, 4, 2, 1, 5, 8, 9, 7, 6], [0, 1, 3, 4, 2, 5, 6, 8, 9, 7],
        [4, 0, 2, 3, 1, 9, 5, 7, 8, 6], [0, 4, 2, 3, 1, 5, 9, 7, 8, 6],
        [2, 0, 3, 4, 1, 7, 5, 8, 9, 6], [0, 2, 3, 4, 1, 5, 7, 8, 9, 6],
        [1, 0, 2, 3, 4, 6, 5, 7, 8, 9]] ++ ids 10 10), ())))),
    (5, (5, some #[[0], [1], [2], [3], [4]])))

/-- **The restricted instance is `R5`** (a kernel check of the serialized values). -/
theorem R5_eq : rbR f5 lD = R5 :=
  serV_injective (hinstTy Ty.unit) (SerTree.eq_of_beq (by decide +kernel))

/-- The certificates of a restricted instance `R` (as `certP`, on `R` itself). -/
def certPR (R : HInstData Ty.unit) (k : ℕ) (isX : Bool) :
    Prog (groupSig Ty.unit) (Solver.Rec Ty.unit) Ty.denote (Ty.group Ty.unit) :=
  m5CertProg MainSteps.spySub R.2.2.1 R.2.2.1 R.1.2.2.2.1 k (if isX then R.1.1.1 else R.1.1.2)
    R.1.2.2.2

theorem certP_f5 (isX : Bool) : certP f5 lD 3 isX = certPR R5 3 isX := by
  unfold certP certPR
  rw [R5_eq]

run_cmd
  execRuns `cert_x5R.run
    (← `(RunsS ssOracle body0 recF (certPR R5 3 true)))
    ssOracle body0 recF (certPR R5 3 true) cfg5
/-- The certificates of `R5`'s source string. -/
theorem cert_x5R : ∃ v s, RunsS ssOracle body0 recF (certPR R5 3 true) v s ∧
    certQ f5 lD 3 Fx5 v s = true :=
  ⟨_, _, cert_x5R.run, by decide +kernel⟩
run_cmd
  execRuns `cert_y5R.run
    (← `(RunsS ssOracle body0 recF (certPR R5 3 false)))
    ssOracle body0 recF (certPR R5 3 false) cfg5
/-- The certificates of `R5`'s target string. -/
theorem cert_y5R : ∃ v s, RunsS ssOracle body0 recF (certPR R5 3 false) v s ∧
    certQ f5 lD 3 Fy5 v s = true :=
  ⟨_, _, cert_y5R.run, by decide +kernel⟩

/-- **The certificates of the restricted instance's source string** compute `Fx5`. -/
theorem cert_x5 : ∃ v s, RunsS ssOracle body0 recF (certP f5 lD 3 true) v s ∧
    certQ f5 lD 3 Fx5 v s = true := by
  rw [certP_f5]
  exact cert_x5R
/-- **The certificates of the restricted instance's target string** compute `Fy5`. -/
theorem cert_y5 : ∃ v s, RunsS ssOracle body0 recF (certP f5 lD 3 false) v s ∧
    certQ f5 lD 3 Fy5 v s = true := by
  rw [certP_f5]
  exact cert_y5R

run_cmd
  execRuns `step5.run
    (← `(RunsS ssOracle body0 recF (stepP f5 lD 3)))
    ssOracle body0 recF (stepP f5 lD 3) cfg5
/-- **The whole step at base size 5** (`k = 3`): the answer is the brute-force coset, and the
children meet the stated bounds of `RunsWithin.m5StepProg` for the full groups `Fx5`, `Fy5`
(the certificates' values: `cert_x5`, `cert_y5`). -/
theorem step5 : ∃ v s, RunsS ssOracle body0 recF (stepP f5 lD 3) v s ∧
    stepQ f5 lD 3 Fx5 Fy5 v s = true :=
  ⟨_, _, step5.run, by decide +kernel⟩

end GraphIsoChecks.MainM5b
