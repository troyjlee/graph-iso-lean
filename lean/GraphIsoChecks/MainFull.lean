module

public import GraphIsoChecks.MainSimsSteps
meta import GraphIsoChecks.MainSimsSteps
public import GraphIso.Main.Full
meta import GraphIso.Main.Full
import all Init.Data.Array.Basic
import all Init.Data.List.Sort.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Mathlib.Data.List.Sort

/-!
# Milestone 14, stage 14j-5d checks: the full procedure

Checks of the full procedure (`GraphIso/Main/Full.lean`) at constant thresholds `thrConst k ℓ`,
run with the verified Schreier–Sims oracle answering the backend calls (the interpreter `eval`
with `mainBody` as the recursive procedure). Each check compares, in one term:

* **the answer** with the brute-force solutions (`ansOK`, `SFix.sols` of
  `GraphIsoChecks.MainSteps`);
* **the path**: the number of times each case of the dispatcher ran (`hist`, in the order base,
  chain, M0, M1, M2a, M2b, M3, M4, M5);
* **the work of every node** (the form of `main_step`): the node's own events (outside its
  children's runs, the recursive-call events excluded, which the children's costs `C` count)
  cost at most `mainWork kf ℓf cT NB² I` under `ssB`. For an M4 node the bound is the tests'
  cost plus M4's work function at the node's sizes (`m4CostSS`, as `MainSimsSteps.m4With`),
  which is at most `m4WorkSS` (`le_envSup`): the envelope `m4WorkSS` ranges over `Lg` up to
  `ssLgM4`, of order `2^2064`, and is not evaluated.

The path and the nodes' work are read from a second run whose body (`logBody`) records the case
and the bound of every node in a marker call before running `mainBody`, and closes it after;
the second run's cost, the markers excluded, equals the first's (`sameCost`). With every bound
`0` the nodes' check fails (the negative control).

The headline bound `mainCost` is an envelope over the whole domain and is not evaluated.

**The fixtures.**
* From the entry (`mainEntry`, no hint, `n₀ = n = N`, domain `nB = N`, `NB = 2N`), by kernel
  `decide`: the mini procedure's fixtures, which reach the base case, the chain rule, M0 and M3.
* With a hint, the body on the hinted fixtures of stage 14j-2 (the program the recursion runs on
  a hinted child, domain `nB = n`, `NB = max N 2n`), by kernel `decide`: M1 (`fM1`), M2a
  (`fM2a`), M2b (`fM2b`) and M3 (`fM3`), each followed by its children's steps.
* M4 on `AGL(1, 5)` (`fM4AGL`) at `ℓ = 0`, by `#eval` through `check` (it throws on `false`):
  the base of five points is not a giant, `j = 1`; at `ℓ = 10` the same instance takes M3.
* M5 needs `12 ≤ m` and is not reached: on the `S₄` data (`fA`, `fB`) the base is a giant, and
  M5's numeric test fails, so the dispatcher takes M3 (`bigCase`); `m5OkD 5 12` holds.

**The threshold contract** (`ThrSpec.loc`): `thrConst` is local; a threshold program that calls
the backend before returning literals (`thrCall`) is not (the negative control).
-/

@[expose] public section

namespace GraphIsoChecks.MainFull

open GraphIso GraphIso.Cost GraphIso.Main GraphIso.Sims GraphIso.Toolkit
open GraphIsoChecks.MainSteps GraphIsoChecks.MainSimsSteps GraphIsoChecks.Sweep

/-! ### The runs -/

/-- The number of a case, in the order of `MainCase`. -/
def caseCode : MainCase → ℕ
  | .base => 0 | .chain => 1 | .m0 => 2 | .m1 => 3 | .m2a => 4 | .m2b => 5 | .m3 => 6
  | .m4 => 7 | .m5 => 8

/-- The markers opening and closing a node of `logBody`. -/
def OPEN : ℕ := 2000
def CLOSE : ℕ := 2001

/-- **The bound on a node's own work**: `mainWork`, except for M4, where it is the tests' cost
plus M4's work function at the node's sizes (`m4CostSS`, at most `m4WorkSS`). -/
def nodeBound (k ℓ s : ℕ) (I : HInstData Ty.unit) : ℕ :=
  if mainCase (fun _ => k) (fun _ => ℓ) I = .m4 then
    let n := I.n
    let N := I.inst.degree
    let m := N - n
    let p := I.winSize
    let j := m4J ssOracle n (N, I.inst.2.2.2.gens, ())
    let Lg := ssLgM4 m j s
    mainTestCost n N p I.inst.2.2.2.gens.length s 3 +
      m4CostSS n m j p s Lg (m4WhSS n m p s n s Lg m.factorial (m4W6SS n m p s s Lg))
  else mainWork (fun _ => k) (fun _ => ℓ) (fun _ => 3) s I

/-- The full procedure at `thrConst k ℓ`. -/
abbrev body (k ℓ : ℕ) : (hinstTy Ty.unit).denote →
    Prog (groupSig Ty.unit) (hinstTy Ty.unit, Ty.answer Ty.unit) Ty.denote (Ty.answer Ty.unit) :=
  mainBody (thrConst k ℓ) Ty.denote

/-- **The logging body**: a marker call with the node's case and bound `bnd I`, the full
procedure's body (whose recursive calls come back here), and a closing marker. -/
def logBody (k ℓ : ℕ) (bnd : HInstData Ty.unit → ℕ) : (hinstTy Ty.unit).denote →
    Prog (groupSig Ty.unit) (hinstTy Ty.unit, Ty.answer Ty.unit) Ty.denote (Ty.answer Ty.unit) :=
  fun I =>
  .bind (Prog.call (S := groupSig Ty.unit) GroupOp.generate
    (0, [(#[OPEN, caseCode (mainCase (fun _ => k) (fun _ => ℓ) I), bnd I], #[])])) fun _ =>
  .bind (body k ℓ I) fun a =>
  .bind (Prog.call (S := groupSig Ty.unit) GroupOp.generate (0, [(#[CLOSE], #[])])) fun _ =>
  .ret a

/-- The marker with first entry `c`, and its entries. -/
def marker (e : Event (groupSig Ty.unit)) : Option (List ℕ) :=
  match e with
  | .call .generate x _ => if x.1 == 0 then some (x.2.headD (#[], #[])).1.toList else none
  | _ => none

def isMarker (e : Event (groupSig Ty.unit)) : Bool :=
  match marker e with
  | some (c :: _) => c == OPEN || c == CLOSE
  | _ => false

def isRec (e : Event (groupSig Ty.unit)) : Bool :=
  match e with
  | .local .recCall _ => true
  | _ => false

/-- **The nodes' own work**: along the trace, a stack of the open nodes' bounds and own costs;
every closed node's own cost is at most its bound, and every node is closed. -/
def nodesOK : List (Event (groupSig Ty.unit)) → List (ℕ × ℕ) → Bool
  | [], st => st.isEmpty
  | e :: tr, st =>
    match marker e with
    | some (c :: _ :: b :: _) =>
      if c == OPEN then nodesOK tr ((b, 0) :: st) else nodesOK tr st
    | some (c :: _) =>
      if c == CLOSE then
        match st with
        | (b, o) :: st' => decide (o ≤ b) && nodesOK tr st'
        | [] => false
      else nodesOK tr st
    | _ =>
      if isRec e then nodesOK tr st
      else match st with
        | (b, o) :: st' => nodesOK tr ((b, o + e.cost ssB) :: st')
        | [] => nodesOK tr st

/-- **The path**: the number of nodes of each case. -/
def hist (tr : Trace (groupSig Ty.unit)) : List ℕ :=
  let cs := tr.filterMap fun e => match marker e with
    | some (c :: d :: _) => if c == OPEN then some d else none
    | _ => none
  (List.range 9).map fun c => cs.count c

/-- The logged run's cost without the markers equals the plain run's. -/
def sameCost (tr tr' : Trace (groupSig Ty.unit)) : Bool :=
  Trace.cost ssB tr == Trace.cost ssB (tr'.filter fun e => !isMarker e)

/-- **A run of the full procedure**: the program `p` with the body, and with the logging body
(the nodes' bounds `bnd`); the answer is the brute-force coset, the path is `path`, every node's
own work is within its bound, and the logged run's cost matches. -/
def fullOK (k ℓ : ℕ) (bnd : HInstData Ty.unit → ℕ) (f : SFix)
    (p : Prog (groupSig Ty.unit) (hinstTy Ty.unit, Ty.answer Ty.unit) Ty.denote
      (Ty.answer Ty.unit)) (path : List ℕ) : Bool :=
  f.ok &&
    match eval ssOracle (body k ℓ) 10000000 p, eval ssOracle (logBody k ℓ bnd) 10000000 p with
    | some (a, tr), some (a', tr') =>
      ansOK f.N f.sols a && ansOK f.N f.sols a' && hist tr' == path && nodesOK tr' [] &&
        sameCost tr tr'
    | _, _ => false

/-- The entry's input for a fixture. -/
def entryIn (f : SFix) : Solver.Ty.input.denote :=
  ((f.x.toArray, f.y.toArray), (WinData.ofPoints f.N f.w, (ofList f.σ, (f.N, gD f.gs))))

/-- **From the entry**: a valid instance without a hint, `n = N`, in the domain `nB = N`,
`NB = 2N`. -/
def entryOK (k ℓ : ℕ) (f : SFix) (path : List ℕ) : Bool :=
  f.n == f.N && f.L.isNone &&
    fullOK k ℓ (nodeBound k ℓ (2 * f.N * (2 * f.N))) f (mainEntry Ty.unit Ty.denote (entryIn f))
      path

/-- **On a hinted instance**: the recursive call on the fixture, in the domain `nB = n`,
`NB = max N 2n`. -/
def hintOK (k ℓ : ℕ) (f : SFix) (path : List ℕ) : Bool :=
  f.L.isSome &&
    fullOK k ℓ (nodeBound k ℓ (max f.N (2 * f.n) * max f.N (2 * f.n))) f (Prog.recur f.hinst) path

/-! ### The fixtures -/

/-- An empty window. -/
def fEmpty : SFix := ⟨3, 3, [[1, 2, 0]], [], [1, 0, 2], [5, 6, 7], [7, 7, 7], none⟩
/-- `⟨(2 3)⟩` fixes the window `{0, 1}`. -/
def fFix4 : SFix :=
  ⟨4, 4, [[0, 1, 3, 2]], [0, 1], [1, 0, 2, 3], [5, 6, 7, 8], [6, 5, 9, 9], none⟩
/-- `⟨(0 1), (2 3)⟩`: two orbits. -/
def fCh : SFix :=
  ⟨4, 4, [[1, 0, 2, 3], [0, 1, 3, 2]], [0, 1, 2, 3], [0, 1, 2, 3], [1, 2, 1, 2], [2, 1, 2, 1],
    none⟩
/-- `D₄` on four positions. -/
def fD4 : SFix :=
  ⟨4, 4, [[1, 2, 3, 0], [0, 3, 2, 1]], [0, 1, 2, 3], [0, 1, 2, 3], [0, 1, 0, 1], [1, 0, 1, 0],
    none⟩
/-- `D₄` with no isomorphism. -/
def fD4No : SFix := { fD4 with y := [0, 0, 1, 1] }

/-! ### From the entry: the base case, the chain rule, M0 and M3 -/

example : entryOK 5 0 fEmpty [1, 0, 0, 0, 0, 0, 0, 0, 0] = true := by decide +kernel
example : entryOK 5 0 fFix4 [1, 0, 0, 0, 0, 0, 0, 0, 0] = true := by decide +kernel
example : entryOK 5 0 fCh [6, 1, 2, 0, 0, 0, 2, 0, 0] = true := by decide +kernel
example : entryOK 5 0 fD4 [10, 0, 4, 0, 0, 0, 4, 0, 0] = true := by decide +kernel
example : entryOK 5 0 fD4No [6, 0, 3, 0, 0, 0, 3, 0, 0] = true := by decide +kernel

/-- **The negative control**: with every node's bound `0`, the nodes' check fails. -/
example : fullOK 5 0 (fun _ => 0) fD4 (mainEntry Ty.unit Ty.denote (entryIn fD4))
    [10, 0, 4, 0, 0, 0, 4, 0, 0] = false := by decide +kernel

/-! ### With a hint: M1, M2a, M2b and M3 -/

example : hintOK 5 0 fM1 [3, 0, 0, 1, 0, 0, 1, 0, 0] = true := by decide +kernel
example : hintOK 5 0 fM2a [10, 0, 3, 0, 1, 0, 4, 0, 0] = true := by decide +kernel
example : hintOK 5 0 fM2b [10, 0, 0, 0, 0, 1, 3, 0, 0] = true := by decide +kernel
example : hintOK 5 0 fM3 [9, 0, 3, 0, 0, 0, 4, 0, 0] = true := by decide +kernel

/-! ### M4 on `AGL(1, 5)`; M5's branch on `S₄` -/

#eval check "M4 on AGL(1, 5) at ℓ = 0: the path (one M4 node) and every node's work" fun _ =>
  hintOK 5 0 fM4AGL [33, 0, 11, 0, 0, 0, 16, 1, 0]
#eval check "AGL(1, 5) at ℓ = 10: M3" fun _ => hintOK 5 10 fM4AGL [36, 0, 0, 0, 0, 0, 1, 0, 0]

/-- On `S₄`, the base action is a giant (`m4Deg = m − 2`), M5's numeric test fails at `m = 4`,
and the dispatcher takes M3; at `m = 12`, `k = 5` passes the test. On `AGL(1, 5)`, the base is
not a giant and M4's test passes. -/
example : ((m4Deg ssOracle fA.n (fA.N, gD fA.gs, ()) == fA.N - fA.n - 2) &&
    !m5OkD 5 (fA.N - fA.n) && bigCase 5 0 fA.n fA.N (gD fA.gs) == .m3 && m5OkD 5 12 &&
    bigCase 5 0 fM4AGL.n fM4AGL.N (gD fM4AGL.gs) == .m4) = true := by decide +kernel

#eval check "M5's branch on S₄: a giant, M3 for x = 0001 against 0100 and 0011" fun _ =>
  hintOK 5 0 fA [42, 0, 0, 0, 0, 0, 1, 0, 0] && hintOK 5 0 fB [48, 0, 0, 0, 0, 0, 1, 0, 0]

/-! ### The threshold contract -/

/-- A threshold program that calls the backend (`generate` at degree `n₀` on no generators)
before returning two literals. -/
def thrCall : ThrProg Ty.unit := fun var x =>
  .bind (.op0 (.nil (a := Ty.perm))) fun l => .bind (.op2 .pair x l) fun a =>
    .bind (.call (S := groupSig Ty.unit) GroupOp.generate a) fun _ => thrConst 0 0 var x

example : ∀ (var : Ty → Type) (x : var .nat), (thrConst (D := Ty.unit) 5 10 var x).Local :=
  (thrConst_spec 5 10).loc

/-- The negative control: a calling threshold program is not local, so it has no `ThrSpec`. -/
example : ¬ ∀ (var : Ty → Type) (x : var .nat), (thrCall var x).Local := by
  intro h
  have h0 := h (fun _ => Unit) ()
  unfold thrCall at h0
  cases h0 with
  | bind _ hk =>
    cases hk () with
    | bind _ hk' =>
      cases hk' () with
      | bind hc _ => exact Prog.not_local_call _ _ hc

example : ¬ ∃ kf ℓf cT, ThrSpec thrCall kf ℓf cT := by
  rintro ⟨kf, ℓf, cT, hT⟩
  have h0 := hT.loc (fun _ => Unit) ()
  unfold thrCall at h0
  cases h0 with
  | bind _ hk =>
    cases hk () with
    | bind _ hk' =>
      cases hk' () with
      | bind hc _ => exact Prog.not_local_call _ _ hc

end GraphIsoChecks.MainFull
