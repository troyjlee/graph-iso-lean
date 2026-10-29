module

public import GraphIsoChecks.ExecSteps
meta import GraphIsoChecks.ExecSteps
public import GraphIso.Main.M5Step
meta import GraphIso.Main.M5Step
import all Init.Data.Array.Basic
import all Init.Data.List.Sort.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Mathlib.Data.List.Sort

/-!
# Milestone 14, stage 14j-4 checks: M5, the giant step

Checks of the stage 14j-4 programs (`GraphIso/Main/M5*.lean`), each against brute force computed
in the same term. Programs run with the verified Schreier–Sims oracle answering the backend
calls and milestone 1's solver as the recursive procedure; sub-calls go to the instrumented
sub-solver `MainSteps.spySub`, which records each child and solves it by milestone 1's solver.

**Relaxed parameters.** The specs assume `5 ≤ k`, `k + 2 ≤ m`, `2k ≤ m` and `12 ≤ m` (for the
cost bounds and the certificates' Alt-test); the programs run for any `k`, and comparing the
answer with brute force needs none of these conditions. The admissible size is out of reach:
at `m = 12`, `k = 5` (with at least `m` strings, as the faithful giant needs) an interpreter run
of the whole step on `S₁₂` did not finish in thirty minutes; even at `m = 5`, `k = 5` the step
does not finish in fifteen (one certificate subset takes a second; Case 3's `k`-tuples at
`k = 5` are what explodes). So the whole step is checked at `m = 4`, `k = 3` (and `m = 5`,
`k = 2, 3` by the interpreter).

**Kernel checks.** Small checks are single kernel checks (`decide +kernel`). The executions of
the dispatch and of the whole step are too large for one kernel check (16–60 GB each,
measured under `scripts/guard.sh`); they are theorems `∃ v s, RunsS ssOracle body0 recF P v s ∧ Q v s`
about the **actual program** `P`, proved in pieces by the kernel execution toolkit
(`GraphIsoChecks.Exec`, `execRuns`: the run `P.run`, every piece of at most 5000 trace events
and every composition step its own declaration; `Q` by `decide +kernel`). `s` is the list of
the children recorded by `spySub` (`flatMap_recF`: `MainSteps.records` of the run's trace),
and `Q`, decided by the kernel, compares the answer `v` with the brute-force solution set and
the children `s` with the stated bounds of the program's spec (`kidsOK`: valid instances with
the size facts and a smaller measure; the counted calls, no hint, with `k · window ≤ n`
(`cmpB`) or `2 · window ≤ |W|` (`halfB`); and `StepChild |W| m`
children whose windows sum to at most the stated factor times `|W|`).
* **The restriction** (`restrictBaseProg`, `rbHInst`, `m5s_giant`; `restrictOK`, single check):
  `S₄` on four window strings and the base alike, times the swap `(4 5)` of two strings outside
  the window (degree `10`, labels `{i}`). The restricted instance (`rbHInst`) is a valid hinted
  instance (window in its strings and invariant, base invariant, faithful on the strings,
  transitive on the window, valid labels), its window is every string position, its measure is
  `(|w|, m)`; its base action contains `Alt(m)` (`m5s_giant`); the program's one sub-call is
  exactly this instance (recorded); the answer lifted back is the brute-force coset, and its
  group contains the restriction's kernel `(4 5)`.
* **The case decision** (`m5CaseProg`, `m5CaseD`; `caseOK`, single check) on groups `F` of the
  base `[5]`: `S₅` and `A₅` (Case 2, `isA`), `C₅` (Case 2b), `⟨(0 1)⟩` (Case 3), `⟨(0 1), (2 3)⟩`
  (Case 1); the program computes the model, and both agree with brute force. `alt_le_of_tupTrans`
  on data: `A₅` and `S₅` are `3`-transitive on `[5]` and realize every even permutation; `C₅` is
  neither.
* **The dispatch** (`m5Dispatch`, the core after the certificates; `disp_case1`, `disp_differ`,
  `disp_case2a`, in pieces), with the full groups `F(x)`, `F(y)` replaced by `Aut_G(x)`,
  `Aut_G(y)` (canonical, by brute force), on `S₅` (`m = 5`) and `S₄` (`m = 4`) acting on the
  window strings and the base alike (labels `{i}`): Case 1 (`S₅`, `x = 0 0 1 1 2`), Case 2
  against Case 1 (`S₅`: the decisions differ, `none`), Case 2a (`S₄`, `x = 0 0 0 1`); the answer
  is the brute-force coset, and the children meet the stated bounds (`dispKids`: `m5CK`,
  `m5CH`, `m5CF`).
* **The whole step** (`m5StepProg`: the restriction, the certificates of `x` and `y`, their case
  decisions, and the dispatch; `step_iso`, `step_noniso`, in pieces) on `S₄` (`m = 4`, relaxed
  `k = 3`): `x = 0 0 0 1` (the certificates give `F = S₃`, Case 2a for `x` and `y`) and a
  non-isomorphic pair (Case 2a for `x`, Case 3 for `y`: `none`); the answer is the brute-force
  coset, and the children meet the stated bounds of `RunsWithin.m5StepProg`
  (`2 · certCount + m5CK`, `m5CH`, `m5CF`) for the full groups `FxA`, `FyA`, `FyB` — the values of
  the certificates on the restricted instance, themselves proved (`cert_xA`, `cert_yA`,
  `cert_xB`, `cert_yB`, with their children meeting `certCount`).

**The stated bounds at relaxed parameters.** The counts of the spec hold under its hypotheses
(`5 ≤ k`, `k + 2 ≤ m`, `2k ≤ m`, `12 ≤ m`), which no fixture here meets; the checks show that
the runs above stay within them anyway. One supplementary run does not: on `A₄` with `x`
constant the certificates make `576` calls for each string, against `certCount = 384` (the count
of `RunsWithin.fullProg` assumes `5 ≤ k`, `k + 2 ≤ m`, `2k ≤ m`); its answer is still the
brute-force coset.

`GraphIsoChecks.MainM5b` adds Cases 2b and 3 and the whole step at base size `5`.

**Interpreter runs only** (`#eval`, supplementary): the dispatch in further Case 2a, Case 3 and
Case 2b configurations (`S₅`, `A₄`, `S₅` and `S₄` on pairs), the whole step's children
on `S₄` acting on pairs (Case 2b) and with `k = 2` (Case 3), the whole step's answer on `A₄`
with `x` constant, and the whole step at `m = 5` on further strings.
-/

@[expose] public section

namespace GraphIsoChecks.MainM5

open Equiv GraphIso GraphIso.Cost GraphIso.Programs GraphIso.Sims GraphIso.Main GraphIso.Toolkit
  GraphIsoChecks.Sweep GraphIsoChecks.Exec GraphIsoChecks.ExecSteps

def gD (gs : List (List ℕ)) : GensData := gs.map ofList

/-- A group on `[k]` acting on the string positions `[0, k)` and the base `[k, 2k)` alike. -/
def alike (gs : List (List ℕ)) : List (List ℕ) := gs.map fun p => p ++ p.map (· + p.length)

def setEq (u v : List ℕ) : Bool := u.all (· ∈ v) && v.all (· ∈ u)

def sameSet (A B : List (List ℕ)) : Bool := A.all (· ∈ B) && B.all (· ∈ A)

def ap (p : List ℕ) (v : ℕ) : ℕ := p.getD v v

/-- The action on `[n, N)` of an element (image list on `[0, N − n)`). -/
def act (n N : ℕ) (g : List ℕ) : List ℕ := (List.range (N - n)).map fun t => ap g (n + t) - n

/-- Run a program with the verified oracle (no recursion). -/
def runDirect {t : Ty} (p : Prog (groupSig Ty.unit) (Ty.unit, Ty.unit) Ty.denote t) :
    Option t.denote :=
  (eval ssOracle (fun _ => Prog.ret ()) 10000000 p).map Prod.fst

/-- Every even permutation of `[m]` is the action of an element of `A` (image lists). -/
def altInB (m : ℕ) (A : List (List ℕ)) : Bool :=
  (GraphIsoChecks.Align.perms m).all fun p => !GraphIsoChecks.Align.isEven m p || p ∈ A

/-! ### The restriction -/

/-- **The restriction** against brute force, for a valid hinted instance `f` with labels `L`
whose base action contains `Alt(m)`, and an element `ker` of the restriction's kernel: the
restricted instance `rbHInst` is a valid hinted instance (`MainSteps.instOK`: the data of
`HInstValid`) of degree `|w| + m` with the window `[0, |w|)` (every string position), the
re-indexed labels and the identity as representative; its base action contains `Alt(m)`
(`m5s_giant`); `restrictBaseProg` with `spySub` makes exactly one sub-call, on this instance
(measure `(|w|, m)`); the answer is the brute-force coset and contains `ker`. -/
def restrictOK (f : MainSteps.SFix) (L : Array (List ℕ)) (ker : List ℕ) : Bool :=
  let m := f.N - f.n
  let k := f.w.length
  let R := rbHInst ssOracle (f.x.toArray, f.y.toArray) (WinData.ofPoints f.N f.w) (ofList f.σ)
    f.N (gD f.gs) f.n f.n L
  let H := closure (k + m) (R.1.2.2.2.2.1.map img)
  f.ok && f.L == some L && altInB m (f.grp.map (act f.n f.N)) &&
    R.1.2.2.2.1 == k + m && R.1.2.1.1 == List.range k && R.2.2.1 == k &&
    (R.2.2.2.map Array.toList) == some (f.w.map fun u => L.getD u []) &&
    R.1.2.2.1.1.toList == List.range (k + m) &&
    MainSteps.instOK k (k + m) H (List.range k) (R.2.2.2) && altInB m (H.map (act k (k + m))) &&
    match MainSteps.runT (restrictBaseProg MainSteps.spySub f.hinst L) with
    | some (a, tr) =>
      let cs := MainSteps.records tr
      MainSteps.ansOK f.N f.sols a &&
        (cs.map fun r => (r.meas, r.n₀, r.n, r.deg, r.pts, r.labs)) ==
          [((k, some m), f.n, k, k + m, List.range k, f.w.map fun u => L.getD u [])] &&
        cs.all (fun r => sameSet (closure r.deg r.gens) H) &&
        match a with
        | some (_, (_, hs, _)) => ker ∈ closure f.N (hs.map img)
        | none => false
    | none => false

/-- `S₄` on the window strings `0–3` and the base `6–9` alike, times `(4 5)` on two strings
outside the window. -/
def s4w : List (List ℕ) := [[1, 0, 2, 3, 4, 5, 7, 6, 8, 9], [1, 2, 3, 0, 4, 5, 7, 8, 9, 6],
  [0, 1, 2, 3, 5, 4, 6, 7, 8, 9]]
def lR : Array (List ℕ) := #[[0], [1], [2], [3]]
/-- Four isomorphisms (`0, 3 ↦ 1, 3` in either order, `1 ↦ 0`, `2 ↦ 2`, and `(4 5)` free). -/
def fR : MainSteps.SFix := ⟨6, 10, s4w, [0, 1, 2, 3], List.range 10,
  [0, 1, 2, 0, 7, 8, 0, 0, 0, 0], [1, 0, 2, 0, 7, 8, 0, 0, 0, 0], some lR⟩

example : restrictOK fR lR [0, 1, 2, 3, 5, 4, 6, 7, 8, 9] = true := by decide +kernel

/-! ### The case decision -/

/-- The orbits of the elements `A` on `[m]`, each in increasing order. -/
def orbitsB (m : ℕ) (A : List (List ℕ)) : List (List ℕ) :=
  ((List.range m).map fun u => (List.range m).filter fun v => A.any fun g => ap g u == v).dedup

/-- `A` is `d`-transitive on `Φ`: the images of the first `d` points of `Φ` are all `d`-tuples of
distinct points of `Φ`. -/
def tupTransB (A : List (List ℕ)) (Φ : List ℕ) (d : ℕ) : Bool :=
  (A.map fun g => (Φ.take d).map (ap g)).dedup.length ==
    (List.range d).foldl (fun acc i => acc * (Φ.length - i)) 1

/-- **The case decision** against brute force, for `F = ⟨gs⟩` on the base `[0, m)` (`n = 0`):
`m5CaseProg` computes `m5CaseD`; the orbits are the brute-force orbits; the case is `2` with
`Φ` the orbit of more than `m/2` points if there is one, otherwise `3` if the points in
nontrivial orbits are fewer than `m/2`, otherwise `1`; `isA` holds exactly in Case 2 when `F`
is `(|Φ| − 2)`-transitive on `Φ`. The expected values are `tag` and `isA`. -/
def caseOK (m : ℕ) (gs : List (List ℕ)) (tag : ℕ) (isA : Bool) : Bool :=
  let A := closure m gs
  let r := m5CaseD ssOracle 0 m (m, gD gs, ())
  let os := orbitsB m A
  let big := os.filter fun o => m < 2 * o.length
  let supp := (os.filter (2 ≤ ·.length)).foldl (· + ·.length) 0
  (runDirect (m5CaseProg (D := Ty.unit) 0 m (m, gD gs, ()))) == some r &&
    os.all (fun o => r.1.2.any (setEq o)) && r.1.2.all (fun o => os.any (setEq o)) &&
    r.1.1.1 == tag && r.2 == isA &&
    (if big.isEmpty then tag == (if 2 * supp < m then 3 else 1)
      else tag == 2 && setEq r.1.1.2 (big.headD [])) &&
    isA == (tag == 2 && tupTransB A r.1.1.2 (r.1.1.2.length - 2))

def s5 : List (List ℕ) := [[1, 0, 2, 3, 4], [1, 2, 3, 4, 0]]
def a5 : List (List ℕ) := [[1, 2, 0, 3, 4], [1, 2, 3, 4, 0]]
def c5 : List (List ℕ) := [[1, 2, 3, 4, 0]]

example : (caseOK 5 s5 2 true && caseOK 5 a5 2 true && caseOK 5 c5 2 false &&
    caseOK 5 [[1, 0, 2, 3, 4]] 3 false && caseOK 5 [[1, 0, 2, 3, 4], [0, 1, 3, 2, 4]] 1 false) =
    true := by decide +kernel

/-- `alt_le_of_tupTrans` on data: `A₅` and `S₅` are `3`-transitive on `[5]` and realize every
even permutation; `C₅` is neither. -/
example : (tupTransB (closure 5 a5) (List.range 5) 3 && altInB 5 (closure 5 a5) &&
    tupTransB (closure 5 s5) (List.range 5) 3 && altInB 5 (closure 5 s5) &&
    !tupTransB (closure 5 c5) (List.range 5) 3 && !altInB 5 (closure 5 c5)) = true := by
  decide +kernel

/-! ### The children against the stated bounds -/

/-- No hint, `k · window ≤ n`: a certificate call or a Case 3 comparison. -/
def cmpB (n k : ℕ) (x : ℕ × Option ℕ) : Bool := x.2.isNone && decide (k * x.1 ≤ n)

/-- No hint, `2 · window ≤ |W|`: a call of Case 2a's pullback. -/
def halfB (w : ℕ) (x : ℕ × Option ℕ) : Bool := x.2.isNone && decide (2 * x.1 ≤ w)

/-- **The children of M5 against its stated bounds**, independent of the observed number of
children: every child is a valid instance with the size facts (at most `N²` generators, the
Schreier–Sims value of the spec's bound) and a smaller measure (`MainSteps.kidsSizeOK`), and the
children split into at most `cK` calls with `cmpB n k` (the certificates' calls, Case 3's
comparisons), at most `cH` calls with `halfB |W|` (Case 2a's pullback), and nonempty
`StepChild |W| m` children whose windows sum to at most `cF · |W|` (the spec's `ChildList`). The split is found greedily, in the order of the children: a child
goes to the first bucket with room whose predicate it meets, and otherwise to the `StepChild`
bucket. This is sound: when the check passes, the children split as the spec states. -/
def kidsOK (f : MainSteps.SFix) (n k cK cH cF : ℕ) (cs : List MainSteps.Child) : Bool :=
  let W := f.w.length
  let m := f.N - f.n
  let r := (cs.map MainSteps.Child.meas).foldl (fun (acc : ℕ × ℕ × ℕ × Bool) x =>
    if cmpB n k x && decide (acc.1 < cK) then (acc.1 + 1, acc.2.1, acc.2.2.1, acc.2.2.2)
    else if halfB W x && decide (acc.2.1 < cH) then (acc.1, acc.2.1 + 1, acc.2.2.1, acc.2.2.2)
    else (acc.1, acc.2.1, acc.2.2.1 + x.1,
      acc.2.2.2 && MainSteps.stepB W m x && decide (1 ≤ x.1))) (0, 0, 0, true)
  MainSteps.kidsSizeOK f (f.N * f.N) cs && r.2.2.2 && decide (r.2.2.1 ≤ cF * W)

/-- The dispatch's children for the full groups `Fx`, `Fy` (`m5Sel` decides the case): at most
`m5CK` comparisons, `m5CH` pullback calls (with `sIn = N²`), and `StepChild` children with the
factor `m5CF`. -/
def dispKids (f : MainSteps.SFix) (k : ℕ) (Fx Fy : GroupData Ty.unit.denote)
    (cs : List MainSteps.Child) : Bool :=
  kidsOK f f.n k (m5CK ssOracle f.n f.N k Fx Fy)
    (m5CH ssOracle f.n f.N (f.N * f.N) f.w.length Fx Fy) (m5CF ssOracle f.n f.N k Fx Fy) cs

/-! ### The dispatch -/

/-- No structure (any tag but `2`). -/
def noSt : ℕ × CJData := (0, (([], [], 0, #[]), #[]))

/-- The automorphisms of `x` in `⟨gs⟩` (degree `N`) on the window `w`, by brute force. -/
def autB (N : ℕ) (gs : List (List ℕ)) (x w : List ℕ) : List (List ℕ) :=
  (closure N gs).filter fun g => w.all fun u => x.getD (ap g u) 0 == x.getD u 0

/-- The full groups of the dispatch checks: `F(x) = Aut_G(x)` and `F(y) = Aut_G(y)` (canonical,
by brute force). -/
def dispFx (f : MainSteps.SFix) : GroupData Ty.unit.denote :=
  (f.N, gD (autB f.N f.gs f.x f.w), ())
def dispFy (f : MainSteps.SFix) : GroupData Ty.unit.denote :=
  (f.N, gD (autB f.N f.gs f.y f.w), ())

/-- **The dispatch** (`m5Dispatch`, with `spySub` and the certificate size `k`) on the
restricted-form instance `f` (representative `1`, the window all string positions), with
`F(x) = Aut_G(x)`, `F(y) = Aut_G(y)` and their case decisions (`m5CaseD`). -/
def dispP (f : MainSteps.SFix) (L : Array (List ℕ)) (k : ℕ) :
    Prog (groupSig Ty.unit) (Solver.Rec Ty.unit) Ty.denote (Ty.answer Ty.unit) :=
  m5Dispatch MainSteps.spySub f.hinst f.n f.n L noSt k (f.x.toArray, f.y.toArray)
    (WinData.ofPoints f.N f.w) (f.N, gD f.gs, ()) (dispFx f) (dispFy f)
    (m5CaseD ssOracle f.n f.N (dispFx f)) (m5CaseD ssOracle f.n f.N (dispFy f))

/-- The dispatch's answer `v` and recorded children `cs` against brute force: the fixture is in
restricted form, the case decisions are `tx`, `ty`, the answer is the brute-force coset, and the
children meet the stated bounds (`dispKids`). -/
def dispQ (f : MainSteps.SFix) (k tx ty : ℕ) (v : AnswerData Ty.unit)
    (cs : List MainSteps.Child) : Bool :=
  f.ok && f.w == List.range f.n && f.σ == List.range f.N &&
    (m5CaseD ssOracle f.n f.N (dispFx f)).1.1.1 == tx &&
    (m5CaseD ssOracle f.n f.N (dispFy f)).1.1.1 == ty &&
    MainSteps.ansOK f.N f.sols v && dispKids f k (dispFx f) (dispFy f) cs

/-- `dispQ` on the interpreter's run (for the supplementary `#eval` checks). -/
def dispOK (f : MainSteps.SFix) (L : Array (List ℕ)) (k tx ty : ℕ) : Bool :=
  match MainSteps.runT (dispP f L k) with
  | some (a, tr) => dispQ f k tx ty a (MainSteps.records tr)
  | none => false

def lD : Array (List ℕ) := #[[0], [1], [2], [3], [4]]
/-- `S₅` on five window strings and the base alike, labels `{i}`. -/
def mkD (x y : List ℕ) : MainSteps.SFix := ⟨5, 10, alike s5, List.range 5, List.range 10,
  x ++ [0, 0, 0, 0, 0], y ++ [0, 0, 0, 0, 0], some lD⟩

/-- Case 1: `Aut(x) = S₂ × S₂` (orbits `{0, 1}, {2, 3}, {4}`), `y` isomorphic. -/
def fD1 : MainSteps.SFix := mkD [0, 0, 1, 1, 2] [1, 2, 0, 1, 0]
/-- The decisions differ (Case 2 for `x`, Case 1 for `y`). -/
def fD2 : MainSteps.SFix := mkD [0, 0, 0, 0, 0] [0, 0, 1, 1, 2]

run_cmd
  execRuns `disp_case1.run
    (← `(RunsS ssOracle body0 recF (dispP fD1 lD 5)))
    ssOracle body0 recF (dispP fD1 lD 5) cfg5
/-- **The dispatch in Case 1** (`S₅`): the run of the program, its answer (the brute-force coset)
and its children (the stated bounds), kernel-checked in pieces. -/
theorem disp_case1 : ∃ v s, RunsS ssOracle body0 recF (dispP fD1 lD 5) v s ∧
    dispQ fD1 5 1 1 v s = true :=
  ⟨_, _, disp_case1.run, by decide +kernel⟩

run_cmd
  execRuns `disp_differ.run
    (← `(RunsS ssOracle body0 recF (dispP fD2 lD 5)))
    ssOracle body0 recF (dispP fD2 lD 5) cfg5
/-- **The decisions differ** (`S₅`, Case 2 for `x`, Case 1 for `y`): the answer is `none`, and
there is no isomorphism. -/
theorem disp_differ : ∃ v s, RunsS ssOracle body0 recF (dispP fD2 lD 5) v s ∧
    dispQ fD2 5 2 1 v s = true :=
  ⟨_, _, disp_differ.run, by decide +kernel⟩

def s4 : List (List ℕ) := [[1, 0, 2, 3], [1, 2, 3, 0]]
def a4 : List (List ℕ) := [[1, 2, 0, 3], [0, 2, 3, 1]]
def l4 : Array (List ℕ) := #[[0], [1], [2], [3]]
/-- A group on `[4]` acting on four window strings and the base alike, labels `{i}`. -/
def mk4 (gs : List (List ℕ)) (x y : List ℕ) : MainSteps.SFix := ⟨4, 8, alike gs, List.range 4,
  List.range 8, x ++ [0, 0, 0, 0], y ++ [0, 0, 0, 0], some l4⟩

/-- `S₄`, `x = 0 0 0 1`, `y = 0 1 0 0`: four isomorphisms. -/
def fA : MainSteps.SFix := mk4 s4 [0, 0, 0, 1] [0, 1, 0, 0]
/-- `S₄`, `x = 0 0 0 1`, `y = 0 0 1 1`: no isomorphism. -/
def fB : MainSteps.SFix := mk4 s4 [0, 0, 0, 1] [0, 0, 1, 1]

run_cmd
  execRuns `disp_case2a.run
    (← `(RunsS ssOracle body0 recF (dispP fA l4 3)))
    ssOracle body0 recF (dispP fA l4 3) cfg5
/-- **The dispatch in Case 2a** (`m = 4`): `S₄`, `x = 0 0 0 1` (`F = S₃` on the large orbit
`{0, 1, 2}`). -/
theorem disp_case2a : ∃ v s, RunsS ssOracle body0 recF (dispP fA l4 3) v s ∧
    dispQ fA 3 2 2 v s = true :=
  ⟨_, _, disp_case2a.run, by decide +kernel⟩

/-! ### The whole step, with relaxed parameters -/

/-- **The whole step** (`m5StepProg`: the restriction, the certificates of `x` and `y` with the
certificate size `k`, their case decisions, and the dispatch), with `spySub`. -/
def stepP (f : MainSteps.SFix) (L : Array (List ℕ)) (k : ℕ) :
    Prog (groupSig Ty.unit) (Solver.Rec Ty.unit) Ty.denote (Ty.answer Ty.unit) :=
  m5StepProg MainSteps.spySub f.hinst L k noSt

/-- The restricted instance of the fixture (`rbHInst`, the model of the restriction's
construction; `RunsWithin.restrictBaseProg` calls the continuation on it). -/
def rbR (f : MainSteps.SFix) (L : Array (List ℕ)) : HInstData Ty.unit :=
  rbHInst ssOracle (f.x.toArray, f.y.toArray) (WinData.ofPoints f.N f.w) (ofList f.σ) f.N
    (gD f.gs) f.n f.n L

/-- **The certificates** of the restricted instance's source (`isX`) or target string: the
program `m5CertProg` that the core runs on the restricted instance. -/
def certP (f : MainSteps.SFix) (L : Array (List ℕ)) (k : ℕ) (isX : Bool) :
    Prog (groupSig Ty.unit) (Solver.Rec Ty.unit) Ty.denote (Ty.group Ty.unit) :=
  let R := rbR f L
  m5CertProg MainSteps.spySub R.2.2.1 R.2.2.1 R.1.2.2.2.1 k (if isX then R.1.1.1 else R.1.1.2)
    R.1.2.2.2

/-- The certificates' value is the full group `F`, and their children meet the stated bound
(`certCount` calls, no hint, `k · window ≤ n`). -/
def certQ (f : MainSteps.SFix) (L : Array (List ℕ)) (k : ℕ) (F v : GroupData Ty.unit.denote)
    (cs : List MainSteps.Child) : Bool :=
  let R := rbR f L
  SerTree.beq (serV (Ty.group Ty.unit) v) (serV (Ty.group Ty.unit) F) &&
    kidsOK f R.2.2.1 k (certCount R.1.2.2.2.1 R.2.2.1 k) 0 0 cs

/-- The whole step's answer and children: the answer is the brute-force coset, and the children
meet the stated bounds of `RunsWithin.m5StepProg` (`2 · certCount + m5CK` calls with `cmpB`,
`m5CH` with `halfB`, and `StepChild` children with the factor `m5CF`), for the full groups `Fx`,
`Fy` of the restricted instance — the values of its certificates (`cert_*` theorems). -/
def stepQ (f : MainSteps.SFix) (L : Array (List ℕ)) (k : ℕ) (Fx Fy : GroupData Ty.unit.denote)
    (v : AnswerData Ty.unit) (cs : List MainSteps.Child) : Bool :=
  let R := rbR f L
  let nr := R.2.2.1
  let Nr := R.1.2.2.2.1
  f.ok && MainSteps.ansOK f.N f.sols v &&
    kidsOK f nr k (2 * certCount Nr nr k + m5CK ssOracle nr Nr k Fx Fy)
      (m5CH ssOracle nr Nr (Nr * Nr) nr Fx Fy) (m5CF ssOracle nr Nr k Fx Fy) cs

/-- `stepQ` on interpreter runs (for the supplementary `#eval` checks). -/
def stepFull (f : MainSteps.SFix) (L : Array (List ℕ)) (k : ℕ) : Bool :=
  match MainSteps.runV (certP f L k true), MainSteps.runV (certP f L k false),
      MainSteps.runT (stepP f L k) with
  | some Fx, some Fy, some (a, tr) => stepQ f L k Fx Fy a (MainSteps.records tr)
  | _, _, _ => false

/-- The answer of the whole step on an interpreter run. -/
def stepAns (f : MainSteps.SFix) (L : Array (List ℕ)) (k : ℕ) : Bool :=
  f.ok && match MainSteps.runT (stepP f L k) with
    | some (a, _) => MainSteps.ansOK f.N f.sols a
    | none => false

/-- The identity of degree `N`, `r` times. -/
def ids (N r : ℕ) : List (List ℕ) := List.replicate r (List.range N)

/-- The full groups the certificates compute on `fA`, `fB` (`k = 3`): `S₃` on the large orbit of
`x` (also `fB`'s `x`), `S₃` on that of `fA`'s `y`, the trivial group for `fB`'s `y`. -/
def FxA : GroupData Ty.unit.denote := (8, gD ([[2, 1, 0, 3, 6, 5, 4, 7],
  [1, 2, 0, 3, 5, 6, 4, 7], [0, 2, 1, 3, 4, 6, 5, 7]] ++ ids 8 8), ())
def FyA : GroupData Ty.unit.denote := (8, gD ([[2, 1, 0, 3, 6, 5, 4, 7],
  [3, 1, 0, 2, 7, 5, 4, 6], [0, 1, 3, 2, 4, 5, 7, 6]] ++ ids 8 8), ())
def FyB : GroupData Ty.unit.denote := (8, gD (ids 8 8), ())

run_cmd
  execRuns `cert_xA.run
    (← `(RunsS ssOracle body0 recF (certP fA l4 3 true)))
    ssOracle body0 recF (certP fA l4 3 true) cfg5
/-- The certificates of `fA`'s and `fB`'s source string (`x = 0 0 0 1`). -/
theorem cert_xA : ∃ v s, RunsS ssOracle body0 recF (certP fA l4 3 true) v s ∧
    certQ fA l4 3 FxA v s = true :=
  ⟨_, _, cert_xA.run, by decide +kernel⟩
run_cmd
  execRuns `cert_yA.run
    (← `(RunsS ssOracle body0 recF (certP fA l4 3 false)))
    ssOracle body0 recF (certP fA l4 3 false) cfg5
/-- The certificates of `fA`'s target string. -/
theorem cert_yA : ∃ v s, RunsS ssOracle body0 recF (certP fA l4 3 false) v s ∧
    certQ fA l4 3 FyA v s = true :=
  ⟨_, _, cert_yA.run, by decide +kernel⟩
run_cmd
  execRuns `cert_xB.run
    (← `(RunsS ssOracle body0 recF (certP fB l4 3 true)))
    ssOracle body0 recF (certP fB l4 3 true) cfg5
/-- The certificates of `fB`'s source string (the same string as `fA`'s). -/
theorem cert_xB : ∃ v s, RunsS ssOracle body0 recF (certP fB l4 3 true) v s ∧
    certQ fB l4 3 FxA v s = true :=
  ⟨_, _, cert_xB.run, by decide +kernel⟩
run_cmd
  execRuns `cert_yB.run
    (← `(RunsS ssOracle body0 recF (certP fB l4 3 false)))
    ssOracle body0 recF (certP fB l4 3 false) cfg5
/-- The certificates of `fB`'s target string. -/
theorem cert_yB : ∃ v s, RunsS ssOracle body0 recF (certP fB l4 3 false) v s ∧
    certQ fB l4 3 FyB v s = true :=
  ⟨_, _, cert_yB.run, by decide +kernel⟩

run_cmd
  execRuns `step_iso.run
    (← `(RunsS ssOracle body0 recF (stepP fA l4 3)))
    ssOracle body0 recF (stepP fA l4 3) cfg5
/-- **The whole step on `S₄`** (`m = 4`, `k = 3`), `x = 0 0 0 1`: the certificates give `F = S₃`,
Case 2a for `x` and `y`; the answer is the brute-force coset, and the children meet the stated
bounds for the full groups `FxA`, `FyA` (the certificates' values: `cert_xA`, `cert_yA`). -/
theorem step_iso : ∃ v s, RunsS ssOracle body0 recF (stepP fA l4 3) v s ∧
    stepQ fA l4 3 FxA FyA v s = true :=
  ⟨_, _, step_iso.run, by decide +kernel⟩
run_cmd
  execRuns `step_noniso.run
    (← `(RunsS ssOracle body0 recF (stepP fB l4 3)))
    ssOracle body0 recF (stepP fB l4 3) cfg5
/-- **The whole step on a non-isomorphic pair** (`k = 3`): Case 2a for `x`, Case 3 for `y`; the
answer is `none`, and the children meet the stated bounds for `FxA`, `FyB` (`cert_xB`,
`cert_yB`). -/
theorem step_noniso : ∃ v s, RunsS ssOracle body0 recF (stepP fB l4 3) v s ∧
    stepQ fB l4 3 FxA FyB v s = true :=
  ⟨_, _, step_noniso.run, by decide +kernel⟩

/-! ### Interpreter runs (supplementary) -/

def check (name : String) (b : Unit → Bool) : IO Unit := do
  unless b () do throw <| IO.userError s!"{name}: failed"
  IO.println s!"{name}: ok"

/-- The ten pairs of `[5]`, and `S₅` acting on them (strings `0–9`) and on the base `10–14`. -/
def prs : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)]
def onPairs (p : List ℕ) : List ℕ :=
  prs.map fun ab => prs.idxOf (min (p.getD ab.1 0) (p.getD ab.2 0),
    max (p.getD ab.1 0) (p.getD ab.2 0))
def s5p : List (List ℕ) := s5.map fun p => onPairs p ++ p.map (· + 10)
def lP : Array (List ℕ) := (prs.map fun ab => [ab.1, ab.2]).toArray
/-- Graphs on `[5]` as strings on the pairs: the `5`-cycles `0-1-2-3-4` and `0-2-4-1-3`. -/
def c5x : List ℕ := prs.map fun ab => if ab.2 - ab.1 == 1 || (ab.1, ab.2) == (0, 4) then 1 else 0
def c5y : List ℕ := prs.map fun ab => if ab.2 - ab.1 == 2 || ab.2 - ab.1 == 3 then 1 else 0
def fP : MainSteps.SFix := ⟨10, 15, s5p, List.range 10, List.range 15, c5x ++ [0, 0, 0, 0, 0],
  c5y ++ [0, 0, 0, 0, 0], some lP⟩

#eval check "the dispatch in Case 2a (x constant, and x = 0 0 0 0 1), Case 3 (distinct letters, \
    k = 2) and Case 2b (S₅ on the pairs, two 5-cycles, F = D₅)" fun _ =>
  dispOK (mkD [0, 0, 0, 0, 0] [0, 0, 0, 0, 0]) lD 5 2 2 &&
    dispOK (mkD [0, 0, 0, 0, 1] [0, 1, 0, 0, 0]) lD 5 2 2 &&
    dispOK (mkD [0, 1, 2, 3, 4] [1, 0, 2, 3, 4]) lD 2 3 3 && dispOK fP lP 5 2 2

/-- `S₄` on the six pairs of `[4]` and the base `[4]`; the `4`-cycles `0-1-2-3` and `0-2-1-3`. -/
def prs4 : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
def onPairs4 (p : List ℕ) : List ℕ :=
  prs4.map fun ab => prs4.idxOf (min (p.getD ab.1 0) (p.getD ab.2 0),
    max (p.getD ab.1 0) (p.getD ab.2 0))
def lP4 : Array (List ℕ) := (prs4.map fun ab => [ab.1, ab.2]).toArray
def fP4 : MainSteps.SFix := ⟨6, 10, s4.map fun p => onPairs4 p ++ p.map (· + 6), List.range 6,
  List.range 10, [1, 0, 1, 1, 0, 1, 0, 0, 0, 0], [0, 1, 1, 1, 1, 0, 0, 0, 0, 0], some lP4⟩

#eval check "the dispatch at m = 4: Case 2a (A₄, x constant), Case 3 (S₄, distinct letters, \
    k = 2), Case 2b (S₄ on the pairs, two 4-cycles, F = D₄)" fun _ =>
  dispOK (mk4 a4 [0, 0, 0, 0] [0, 0, 0, 0]) l4 3 2 2 &&
    dispOK (mk4 s4 [0, 1, 2, 3] [1, 0, 2, 3]) l4 2 3 3 && dispOK fP4 lP4 3 2 2
#eval check "the whole step with its children (m = 4, k = 3: S₄ on the pairs, Case 2b; \
    k = 2: Case 3)" fun _ =>
  stepFull fP4 lP4 3 && stepFull (mk4 s4 [0, 0, 0, 1] [0, 1, 0, 0]) l4 2

/- `A₄` with `x` constant (`k = 3`): the answer is the brute-force coset, but the certificates'
calls (`576` for each string) exceed `certCount = 384`: the count of `RunsWithin.fullProg`
assumes `5 ≤ k`, `k + 2 ≤ m` and `2k ≤ m`, which the relaxed parameters violate. -/
#eval check "the whole step on A₄ with x constant (answer; the certificates' count is not \
    promised at the relaxed parameters)" fun _ =>
  stepAns (mk4 a4 [0, 0, 0, 0] [0, 0, 0, 0]) l4 3 &&
    !stepFull (mk4 a4 [0, 0, 0, 0] [0, 0, 0, 0]) l4 3
#eval check "the whole step at m = 5 (k = 3): S₅ with x constant and x = 0 0 0 0 1 (Case 2a), \
    a non-isomorphic pair" fun _ =>
  stepAns (mkD [0, 0, 0, 0, 0] [0, 0, 0, 0, 0]) lD 3 &&
    stepAns (mkD [0, 0, 0, 0, 1] [0, 1, 0, 0, 0]) lD 3 &&
    stepAns (mkD [0, 0, 0, 0, 1] [0, 0, 0, 1, 1]) lD 3

end GraphIsoChecks.MainM5
