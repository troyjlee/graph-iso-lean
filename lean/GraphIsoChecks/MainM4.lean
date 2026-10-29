module

public import GraphIsoChecks.ExecSteps
meta import GraphIsoChecks.ExecSteps
public import GraphIso.Main.M4Step
meta import GraphIso.Main.M4Step
import all Init.Data.Array.Basic
import all Init.Data.List.Sort.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Mathlib.Data.List.Sort

/-!
# Milestone 14, stage 14j-3 checks: the pieces of M4

Checks of the stage 14j-3 programs and data models (`GraphIso/Main/M4Bridge.lean`,
`GraphIso/Main/M4Struct.lean`), each against brute force computed in the same term. Groups act
on string positions `[0, k)` and the base `[k, 2k)` alike (`alike`); backend calls are
answered by the verified Schreier–Sims oracle (`ssOracle`, directly in the programs' runs).

**Kernel-checked examples** (`decide +kernel`):
* **`m4StructProg`, disconnected** (`D₄` on four base points: transitive, not doubly
  transitive, the diagonal orbital graph disconnected): the leaf is the components partition
  `{0, 2}, {1, 3}`, `K = H` and one representative (`structOK`: the program's output equals
  `m4StructModel`'s, `K` is the brute-force stabilizer of the leaf in `H`, the representatives
  cover `H` by cosets of `K`, at most `msCount k` of them, and at most one with `K = H` when an
  orbital graph is disconnected).
* **`m4StructProg`, uniprimitive** (`D₅` and `C₅` on five points, the model): `soj` leaves,
  colored partitions (`{0}`, `{1, 4}`, `{2, 3}` for `D₅`, with `K` the reflection fixing `0` and
  five representatives; the discrete colouring for `C₅`, `K = 1`).
* **The leaves are valid** (`M4Out`, with `t = (k + 3) / 2`): the computed leaf is identified
  (`decide`), then `IsColPart` is decided on the decoded partition, field by field. No Johnson
  leaf occurs at these sizes (`soj` individualizes and splits); `IsJohnson` was decided on a
  constructed embedding in `GraphIsoChecks.MainHints` (`j12_johnson`).
* **`prodRepsD`** (`isLeftCover_prodRepsD`): `S₄` covered by four cosets of the stabilizer `S₃`
  of `0`, `S₃` by three cosets of the stabilizer `S₂` of `0, 1`: the twelve products cover `S₄`
  by cosets of `S₂`; the program `prodRepsLProg` computes them.
* **M4 as a step** (`m4StepProg`) on hinted instances with a primitive base action that is not
  a giant, on the five strings with labels `{i}`: `D₅` (degree `1`, `j = 0`: the leaf `{0},
  {1, 4}, {2, 3}`, five representatives) and `AGL(1, 5)` (degree `2`, `j = 1`: `H = C₄`, its
  components leaf, five representatives) and `C₅` (degree `1`, `j = 0`: the uniprimitive
  branch, asserted by `disconnD` being empty; the discrete leaf, `K = 1`, five representatives,
  at most the five leaves). The pieces (`m4PiecesOK`, all three): the case conditions, `K ≤ G`,
  the cover by `K` within `m4R m j`, the structure handed to reduce-and-derive (`m4St`, by the
  programs `extProg` and `m4StProg`) and its preservation by `K`. The whole step on
  `AGL(1, 5)` (the components branch) and on `C₅` (the uniprimitive branch, from the round-1
  audit's probe) (`m4_step_agl`, `m4_step_c5`, run with `MainSteps.spySub`): theorems
  `∃ v ts, RunsS ssOracle body0 (tokF 5 10) (m4P f) v ts ∧ m4RunQ … v ts`, proved in pieces by
  the kernel execution toolkit (`GraphIsoChecks.Exec`, `execRuns`; as single kernel
  checks each needed more than 24 GB), where `ts` are the run's tokens (`tokF`: the children,
  the steps of the dynamic chains and the `kernel` calls, which are exactly what
  `MainSteps.records`, `MainSteps.dynSteps` and `MainSteps.hasKernel` read from the trace:
  `m4RunQ_flatMap`; so `m4_step_agl_tr`, `m4_step_c5_tr` state the checks on the run's trace);
  the answer is the brute-force coset;
  the recorded children are `StepChild |W| m` with the `ChildList` factor `|reps| · m!`, keep
  `SizeChild`, decrease the measure (`MeasLt`) and are valid instances (the hinted ones
  transitive with valid labels); the reduce-and-derive tags are `{0, 2}` and `{0}`, with no
  kernel reduction (no stuck orbit).
* **Individualization** (`indiv_of_degree`): `AGL(1, 5)` has computed degree `2` (`degreeModel`,
  `cap = m − 2 = 3`): `fixFirst G n 1`, the stabilizer of the first base point (by brute force
  and by `pointStabsModel` on `List.range' n 1`, with at most `m` representatives), is
  transitive and not doubly transitive on the other four; `D₅` has degree `1`, and `G` itself
  is transitive and not doubly transitive.

**Interpreter runs only** (`#eval`, supplementary; everything above is kernel-checked):
* the whole M4 step on `D₅` with the checks of `m4RunOK` (the answer, the children, the tags
  `{0, 1}`): in the kernel it exceeds the kernel's limit (its pieces, `m4PiecesOK`, are
  kernel-checked, as are the whole steps on `AGL(1, 5)` and `C₅`);
* `m4StructProg` on the Petersen action of `S₅` on the ten pairs (the leaf `{01}`, its six
  neighbours, its three non-neighbours; `K = S₂ × S₃`, ten representatives), program and model:
  in the kernel it exceeds the kernel's limit, and the leaf's `M4Out` check the elaborator's
  heartbeats;
* the program `m4StructProg` against the model on `C₅` and `D₅` (`structOK` with `prog`): its
  run costs about forty seconds at `k = 5`, so it is compared with the model in the kernel on
  `D₄` only (it also runs inside the kernel-checked M4 steps on `C₅`, at `k = 5`, and on
  `AGL(1, 5)`, at `k = 4`).

-/

@[expose] public section

namespace GraphIsoChecks.MainM4

open Equiv GraphIso GraphIso.Cost GraphIso.Programs GraphIso.Sims GraphIso.Main GraphIso.Toolkit
  GraphIsoChecks.Exec GraphIsoChecks.ExecSteps
  GraphIso.SoJTree GraphIso.SplitJohnson GraphIsoChecks.Sweep

/-- Run a program with the verified oracle answering the backend calls (no recursion). -/
def runDirect {t : Ty} (p : Prog (groupSig Ty.unit) (Ty.unit, Ty.unit) Ty.denote t) :
    Option t.denote :=
  (eval ssOracle (fun _ => Prog.ret ()) 10000000 p).map Prod.fst

/-- Run a program with no backend calls. -/
def runP {t : Ty} (p : Prog Signature.empty (Ty.unit, Ty.unit) Ty.denote t) : Option t.denote :=
  (eval Ctx.empty.O (fun _ => Prog.ret ()) 10000000 p).map Prod.fst

def gD (gs : List (List ℕ)) : GensData := gs.map ofList

/-- A group on `[k]` acting on the string positions `[0, k)` and the base `[k, 2k)` alike. -/
def alike (gs : List (List ℕ)) : List (List ℕ) := gs.map fun p => p ++ p.map (· + p.length)

def setEq (u v : List ℕ) : Bool := u.all (· ∈ v) && v.all (· ∈ u)

def sameSet (A B : List (List ℕ)) : Bool := A.all (· ∈ B) && B.all (· ∈ A)

def ap (p : List ℕ) (v : ℕ) : ℕ := p.getD v v

/-- `h` is in the coset `r H`. -/
def inCoset (H : List (List ℕ)) (r h : List ℕ) : Bool := H.any fun e => compose r e == h

/-- The cosets `r R` of the representatives cover `P`. -/
def coverB (P R reps : List (List ℕ)) : Bool := P.all fun g => reps.any fun r => inCoset R r g

/-- The action on `[n', N)` of an element (image list on `[0, N − n')`). -/
def act (n' N : ℕ) (g : List ℕ) : List ℕ := (List.range (N - n')).map fun t => ap g (n' + t) - n'

/-- A leaf as lists (the kernel does not reduce equality of arrays). -/
def outL (o : OutD) :=
  (o.1, o.2.1.1.toList, o.2.1.2.toList, o.2.2.1, o.2.2.2.1, o.2.2.2.2.1, o.2.2.2.2.2.toList)

/-- An output of `m4StructProg` as lists. -/
def resL (r : GroupData Ty.unit.denote × (List PermData × OutD)) :=
  (r.1.1, r.1.2.1.map GraphIsoChecks.Align.pdL, r.2.1.map GraphIsoChecks.Align.pdL, outL r.2.2)

/-! ### `m4StructProg` -/

/-- **The structure of M4 against brute force**, for `H = ⟨gs⟩` at degree `N` on the window
`[n', N)` (`k = N − n'` points): `H` is transitive and not doubly transitive there; the program
`m4StructProg` computes `m4StructModel`; its leaf is the first leaf (`msLeaf`) and equals
`leaf`; `K` is the brute-force stabilizer of the leaf in `H` (the elements whose action on the
window carries the leaf to itself); the representatives cover `H` by cosets of `K`, at most
`msCount k` of them; with `disc` (an orbital graph disconnected), at most one, and `K = H`. -/
def structOK (n' N : ℕ) (gs : List (List ℕ)) (leaf : OutD) (disc prog : Bool) : Bool :=
  let H := closure N gs
  let k := N - n'
  let r := m4StructModel ssOracle n' (N, gD gs, ())
  let K := closure N (r.1.2.1.map img)
  let A := H.map (act n' N)
  setEq ((A.map fun σ => ap σ 0).dedup) (List.range k) &&
    !(A.map fun σ => (ap σ 0, ap σ 1)).dedup.length ==
      ((List.range k).flatMap fun a => ((List.range k).filter (· ≠ a)).map (a, ·)).length &&
    (!prog || (runDirect (m4StructProg (D := Ty.unit) n' (N, gD gs, ()))).map resL ==
      some (resL r)) &&
    outL r.2.2 == outL (msLeaf ssOracle n' (N, gD gs, ())) && outL r.2.2 == outL leaf &&
    r.1.1 == N && GensData.allValidB N r.1.2.1 &&
    sameSet K (H.filter fun g =>
      GraphIsoChecks.Align.outMaps k (ofList (act n' N g)) r.2.2 r.2.2) &&
    coverB H K (r.2.1.map img) && decide (r.2.1.length ≤ msCount k) &&
    (!disc || (r.2.1.length ≤ 1 && sameSet K H))

def d4 : List (List ℕ) := alike [[1, 2, 3, 0], [0, 3, 2, 1]]
def c5 : List (List ℕ) := alike [[1, 2, 3, 4, 0]]
def d5 : List (List ℕ) := alike [[1, 2, 3, 4, 0], [0, 4, 3, 2, 1]]

/-- The ten pairs of `[5]`, in order. -/
def prs : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)]

/-- A permutation of `[5]` acting on the ten pairs. -/
def onPairs (p : List ℕ) : List ℕ :=
  prs.map fun ab => prs.idxOf (min (p.getD ab.1 0) (p.getD ab.2 0),
    max (p.getD ab.1 0) (p.getD ab.2 0))

/-- `S₅` on the ten pairs (the Petersen graph's vertices). -/
def pet : List (List ℕ) := alike [onPairs [1, 0, 2, 3, 4], onPairs [1, 2, 3, 4, 0]]

/-- The leaves. -/
def leafD4 : OutD := partD #[0, 0, 0, 0] #[[0, 2], [1, 3], [2, 0], [3, 1]]
def leafC5 : OutD := partD #[4, 3, 2, 1, 0] #[[0], [1], [2], [3], [4]]
def leafD5 : OutD := partD #[2, 1, 0, 0, 1] #[[0], [1, 4], [2, 3], [2, 3], [1, 4]]
def leafPet : OutD := partD #[2, 1, 1, 1, 1, 1, 1, 0, 0, 0]
  #[[0], [1, 2, 3, 4, 5, 6], [1, 2, 3, 4, 5, 6], [1, 2, 3, 4, 5, 6], [1, 2, 3, 4, 5, 6],
    [1, 2, 3, 4, 5, 6], [1, 2, 3, 4, 5, 6], [7, 8, 9], [7, 8, 9], [7, 8, 9]]

example : structOK 4 8 d4 leafD4 true true = true := by decide +kernel
example : structOK 5 10 d5 leafD5 false false = true := by decide +kernel
example : structOK 5 10 c5 leafC5 false false = true := by decide +kernel

/-! ### The leaves are valid (`M4Out`) -/

theorem leafD4_out : M4Out 4 (m4StructModel ssOracle 4 (8, gD d4, ())).2.2 := by
  have h : (m4StructModel ssOracle 4 (8, gD d4, ())).2.2 = leafD4 := by decide +kernel
  rw [h]
  exact Or.inl ⟨_, rfl, by constructor <;> decide +kernel⟩

theorem leafD5_out : M4Out 5 (m4StructModel ssOracle 5 (10, gD d5, ())).2.2 := by
  have h : (m4StructModel ssOracle 5 (10, gD d5, ())).2.2 = leafD5 := by decide +kernel
  rw [h]
  exact Or.inl ⟨_, rfl, by constructor <;> decide +kernel⟩

theorem leafC5_out : M4Out 5 (m4StructModel ssOracle 5 (10, gD c5, ())).2.2 := by
  have h : (m4StructModel ssOracle 5 (10, gD c5, ())).2.2 = leafC5 := by decide +kernel
  rw [h]
  exact Or.inl ⟨_, rfl, by constructor <;> decide +kernel⟩

/-! ### Composed covers -/

/-- **Composed covers** against brute force: `rs` covers `G` by cosets of `K₁ ≤ G`, `rs'` covers
`K₁` by cosets of `K₂ ≤ K₁`; then `prodRepsD rs rs'` (of length `|rs| · |rs'|`, inside `G`)
covers `G` by cosets of `K₂`, and `prodRepsLProg` computes it. -/
def prodOK (N : ℕ) (gs k₁ k₂ rs rs' : List (List ℕ)) : Bool :=
  let G := closure N gs
  let K₁ := closure N k₁
  let K₂ := closure N k₂
  let P := prodRepsD (gD rs) (gD rs')
  K₁.all (· ∈ G) && K₂.all (· ∈ K₁) && coverB G K₁ rs && coverB K₁ K₂ rs' && rs.all (· ∈ G) &&
    rs'.all (· ∈ K₁) && P.length == rs.length * rs'.length &&
    (P.map img).all (· ∈ G) && coverB G K₂ (P.map img) &&
    (runP (prodRepsLProg (gD rs) (gD rs'))).map (·.map GraphIsoChecks.Align.pdL) ==
      some (P.map GraphIsoChecks.Align.pdL)

/-- `S₄`, the stabilizer `S₃` of `0`, the stabilizer `S₂` of `0, 1`, and the transversals. -/
example : prodOK 4 [[1, 0, 2, 3], [1, 2, 3, 0]] [[0, 2, 1, 3], [0, 2, 3, 1]] [[0, 1, 3, 2]]
    [[0, 1, 2, 3], [1, 0, 2, 3], [2, 1, 0, 3], [3, 1, 2, 0]]
    [[0, 1, 2, 3], [0, 2, 1, 3], [0, 3, 2, 1]] = true := by decide +kernel

/-! ### Individualization -/

/-- Transitive on the points `P` (a list), for the elements `H`. -/
def transB (H : List (List ℕ)) (P : List ℕ) : Bool :=
  setEq ((H.map fun g => ap g (P.headD 0)).dedup) P

/-- Doubly transitive on `P`: the images of the first two points are all ordered pairs. -/
def twoTransB (H : List (List ℕ)) (P : List ℕ) : Bool :=
  (H.map fun g => (ap g (P.getD 0 0), ap g (P.getD 1 0))).dedup.length ==
    P.length * (P.length - 1)

/-- **Individualization** against brute force, for `G = ⟨gs⟩` transitive on the base `[n, N)`:
the computed degree is `d` (`degreeModel`, `cap = m − 2`), `1 ≤ d < cap`; `fixFirst G n (d − 1)`
(the elements fixing `n, …, n + d − 2`, by brute force, equal to the group `pointStabsModel`
computes on `List.range' n (d − 1)`, with at most `m^(d − 1)` representatives) is transitive
and not doubly transitive on `[n + d − 1, N)`. -/
def indivOK (n N : ℕ) (gs : List (List ℕ)) (d : ℕ) : Bool :=
  let m := N - n
  let G := closure N gs
  let F := G.filter fun g => (List.range' n (d - 1)).all fun u => ap g u == u
  let ps := pointStabsModel ssOracle (N, gD gs, ()) (List.range' n (d - 1))
  let rest := List.range' (n + d - 1) (N - (n + d - 1))
  transB G (List.range' n m) && degreeModel ssOracle n (m - 2) (N, gD gs, ()) == d &&
    1 ≤ d && d < m - 2 && sameSet (closure N (ps.1.2.1.map img)) F &&
    decide (ps.2.length ≤ m ^ (d - 1)) && transB F rest && !twoTransB F rest

def agl5 : List (List ℕ) := alike [[1, 2, 3, 4, 0], [0, 2, 4, 1, 3]]

example : (indivOK 5 10 agl5 2 && indivOK 5 10 d5 1) = true := by decide +kernel

/-! ### M4 as a step -/

/-- The structure handed to reduce-and-derive, as lists. -/
def stL (st : ℕ × CJData) :=
  (st.1, st.2.1.1, st.2.1.2.1, st.2.1.2.2.1, st.2.1.2.2.2.toList, st.2.2.toList)

/-- **The pieces of M4 against brute force** (the data models of `m4StepProg`): the fixture is a
valid hinted instance, its base action transitive and not a giant (`m4Deg < m − 2`), with `j`
individualized points (`4 + j ≤ m`); `K` (`m4K`) lies in `G`, and the `r` representatives
(`m4Reps`) cover `G` by cosets of `K`, with `r ≤ m4R m j`; the structure handed to
reduce-and-derive is `st` (`m4St`), computed by the programs `extProg` and `m4StProg` from the
leaf extended to the whole base, which `K` preserves (brute force). -/
def m4PiecesOK (f : MainSteps.SFix) (j r : ℕ) (st : ℕ × CJData) : Bool :=
  let G : GroupData Ty.unit.denote := (f.N, gD f.gs, ())
  let m := f.N - f.n
  let K := closure f.N ((m4K ssOracle f.n G).2.1.map img)
  let reps := (m4Reps ssOracle f.n G).map img
  let o := (m4Str ssOracle f.n G).2.2
  let o' := Case2b.extD m (m4L m j) o
  f.ok && f.L.isSome && f.baseTrans && m4J ssOracle f.n G == j &&
    decide (m4Deg ssOracle f.n G < m - 2) && decide (4 + j ≤ m) && K.all (· ∈ f.grp) &&
    coverB f.grp K reps && reps.length == r && decide (r ≤ m4R m j) &&
    stL (m4St ssOracle f.n G) == stL st &&
    (runP (Case2b.extProg m (m4L m j) o)).map outL == some (outL o') &&
    (runP (m4StProg m j o')).map stL == some (stL st) &&
    K.all (fun k => GraphIsoChecks.Align.outMaps m (ofList (act f.n f.N k)) o' o')

/-- **M4 as a step against brute force** (`m4StepProg`, run with `MainSteps.spySub` and
milestone 1's solver as the sub-solver), given the pieces (`m4PiecesOK`: `r` representatives,
the structure `st`): the answer is the brute-force coset; the children (recorded) are
`StepChild |W| m` with the `ChildList` factor `r · m!`, keep `SizeChild`, decrease the measure
and are valid instances (hinted ones transitive with valid labels); the tags of the
reduce-and-derive steps (`deriveModel` with `st`) are `tags`, with the kernel reduction exactly
for tag `6` (`m4RunB`, on a run `(a, tr)`). -/
def m4RunB (f : MainSteps.SFix) (r : ℕ) (st : ℕ × CJData) (tags : List ℕ)
    (a : AnswerData Ty.unit) (tr : Trace (groupSig Ty.unit)) : Bool :=
  let m := f.N - f.n
  let tg := (MainSteps.dynSteps f.n f.N tr).map fun s =>
    (deriveModel ssOracle f.n f.N s.1 s.2 (f.L.getD #[]) st).1
  MainSteps.ansOK f.N f.sols a &&
    MainSteps.childrenOK f (r * m.factorial) (MainSteps.stepB f.w.length m) (f.N * f.N)
      (MainSteps.records tr) &&
    setEq tg tags && tg.contains 6 == MainSteps.hasKernel tr

/-- `m4RunB` on the interpreter's run. -/
def m4RunOK (f : MainSteps.SFix) (r : ℕ) (st : ℕ × CJData) (tags : List ℕ) : Bool :=
  match MainSteps.runT (m4StepProg MainSteps.spySub f.hinst) with
  | some (a, tr) => m4RunB f r st tags a tr
  | none => false

/-! #### The whole step in pieces -/

-- the derived `ToExpr` uses core's `ToExpr Unit`: Mathlib's `ToExpr PUnit` is `meta`, which a
-- definition outside the meta phase may not use (Lean's module system)
attribute [local instance high] Lean.instToExprUnit in
/-- **Tokens of a run**, event by event: what `MainSteps.records` (the children) and
`MainSteps.dynSteps` (the steps of the dynamic chains) read from a trace. The instrumented
sub-solver's opening marker (with its child) and closing marker, a `kernel` call, an `orbits`
call on a group of degree `N` and a nonempty window of string positions (with its group and
its first orbit), and any other backend call. -/
inductive Tok where
  | kid (c : MainSteps.Child)
  | close
  | ker
  | orb (g : ℕ × GensData × Unit) (o : List ℕ)
  | other
  deriving DecidableEq, Lean.ToExpr

/-- The tokens of one event (`n`, `N`: the string positions and the degree of the instance). -/
def tokF (n N : ℕ) : Event (groupSig Ty.unit) → List Tok := fun e => match e with
  | .call .generate x _ =>
    let h := (x.2.headD (#[], #[])).1.getD 0 0
    if x.1 == 0 && h == MainSteps.SENT then [.kid (MainSteps.decode (x.2.map img))]
    else if x.1 == 0 && h == MainSteps.SENT2 then [.close] else [.other]
  | .call .kernel _ _ => [.ker]
  | .call .orbits x y =>
    if x.1.1 == N && !x.2.1.isEmpty && x.2.1.all (· < n) then [.orb x.1 (y.headD [])]
    else [.other]
  | .call _ _ _ => [.other]
  | _ => []

/-- The children of a token list (as `MainSteps.records`). -/
def tokKids (ts : List Tok) : List MainSteps.Child :=
  ts.filterMap fun t => match t with
    | .kid c => some c
    | _ => none

/-- The steps of the dynamic chains of a token list (as `MainSteps.dynSteps`): an `orbits` call
outside the sub-solver's runs and not right after a `kernel` call. -/
def tokSteps (ts : List Tok) : List (GroupData Ty.unit.denote × List ℕ) :=
  (ts.foldl (fun (st : List (GroupData Ty.unit.denote × List ℕ) × Bool × Bool) t =>
    match t with
    | .kid _ => (st.1, true, false)
    | .close => (st.1, false, false)
    | .ker => (st.1, st.2.1, true)
    | .orb g o =>
      if !st.2.1 && !st.2.2 then ((g, o) :: st.1, st.2.1, false)
      else (st.1, st.2.1, false)
    | .other => (st.1, st.2.1, false)) ([], false, false)).1.reverse

/-- The step's answer and tokens against brute force (`m4RunB` on the tokens:
`m4RunQ_flatMap`): the answer is the
brute-force coset; the children are `StepChild |W| m` with the factor `r · m!` (and valid, with
the size facts and a smaller measure); the tags of the reduce-and-derive steps are `tags`, with a
`kernel` call exactly when some tag is `6`. -/
def m4RunQ (f : MainSteps.SFix) (r : ℕ) (st : ℕ × CJData) (tags : List ℕ)
    (v : AnswerData Ty.unit) (ts : List Tok) : Bool :=
  let m := f.N - f.n
  let tg := (tokSteps ts).map fun s => (deriveModel ssOracle f.n f.N s.1 s.2 (f.L.getD #[]) st).1
  MainSteps.ansOK f.N f.sols v &&
    MainSteps.childrenOK f (r * m.factorial) (MainSteps.stepB f.w.length m) (f.N * f.N)
      (tokKids ts) &&
    setEq tg tags && tg.contains 6 == ts.contains .ker

/-- **The tokens read the trace**: their children are `MainSteps.records`. -/
theorem tokKids_flatMap (n N : ℕ) (tr : Trace (groupSig Ty.unit)) :
    tokKids (tr.flatMap (tokF n N)) = MainSteps.records tr := by
  induction tr with
  | nil => rfl
  | cons e tr ih =>
    rw [List.flatMap_cons]
    unfold tokKids at ih ⊢
    rw [List.filterMap_append, ih]
    unfold MainSteps.records
    rw [List.filterMap_cons]
    rcases e with _ | ⟨op, x, y⟩
    · rfl
    · cases op <;> simp only [tokF] <;> (try split_ifs) <;> simp_all

/-- **The tokens read the trace**: their steps are `MainSteps.dynSteps`. -/
theorem tokSteps_flatMap (n N : ℕ) (tr : Trace (groupSig Ty.unit)) :
    tokSteps (tr.flatMap (tokF n N)) = MainSteps.dynSteps n N tr := by
  unfold tokSteps MainSteps.dynSteps
  rw [List.foldl_flatMap]
  congr 2
  apply congrArg (fun g => List.foldl g _ tr)
  funext st e
  obtain ⟨l, b₁, b₂⟩ := st
  rcases e with _ | ⟨op, x, y⟩
  · rfl
  · cases op
    case orbits =>
      have key : (!b₁ && !b₂ && x.1.1 == N && !x.2.1.isEmpty && x.2.1.all (· < n)) =
          (!b₁ && !b₂ && (x.1.1 == N && !x.2.1.isEmpty && x.2.1.all (· < n))) := by
        simp only [Bool.and_assoc]
      simp only [tokF, key]
      cases (x.1.1 == N && !x.2.1.isEmpty && x.2.1.all (· < n)) <;> cases b₁ <;> cases b₂ <;> rfl
    all_goals cases b₁ <;> cases b₂ <;> simp only [tokF] <;> (try split_ifs) <;> simp_all

/-- **The tokens read the trace**: a `kernel` token exactly when `MainSteps.hasKernel`. -/
theorem tokKer_flatMap (n N : ℕ) (tr : Trace (groupSig Ty.unit)) :
    (tr.flatMap (tokF n N)).contains .ker = MainSteps.hasKernel tr := by
  induction tr with
  | nil => rfl
  | cons e tr ih =>
    unfold MainSteps.hasKernel at ih ⊢
    rw [List.flatMap_cons, List.contains_append, ih, List.any_cons]
    congr 1
    rcases e with _ | ⟨op, x, y⟩
    · rfl
    · cases op <;> simp only [tokF] <;> (try split_ifs) <;> rfl

/-- `m4RunQ` on the tokens of a trace is `m4RunB` on the trace. -/
theorem m4RunQ_flatMap (f : MainSteps.SFix) (r : ℕ) (st : ℕ × CJData) (tags : List ℕ)
    (v : AnswerData Ty.unit) (tr : Trace (groupSig Ty.unit)) :
    m4RunQ f r st tags v (tr.flatMap (tokF f.n f.N)) = m4RunB f r st tags v tr := by
  unfold m4RunQ m4RunB
  rw [tokSteps_flatMap, tokKids_flatMap, tokKer_flatMap]

/-- From a token run to a run whose trace meets `m4RunB`. -/
theorem runs_of_tok {f : MainSteps.SFix} {r : ℕ} {st : ℕ × CJData} {tags : List ℕ}
    {p : Prog (groupSig Ty.unit) (Solver.Rec Ty.unit) Ty.denote (Ty.answer Ty.unit)}
    (h : ∃ v ts, RunsS ssOracle body0 (tokF f.n f.N) p v ts ∧ m4RunQ f r st tags v ts = true) :
    ∃ v tr, Runs ssOracle body0 p v tr ∧ m4RunB f r st tags v tr = true := by
  obtain ⟨v, _, ⟨tr, hr, rfl⟩, hq⟩ := h
  exact ⟨v, tr, hr, by rwa [m4RunQ_flatMap] at hq⟩

/-- The program of the whole step. -/
def m4P (f : MainSteps.SFix) :
    Prog (groupSig Ty.unit) (Solver.Rec Ty.unit) Ty.denote (Ty.answer Ty.unit) :=
  m4StepProg MainSteps.spySub f.hinst

/-- `D₅` on the strings and the base alike, labels `{i}` on the five strings; `x = y` symmetric
under the reflection fixing `0` (two isomorphisms). Degree `1`: no individualization. -/
def fM4D5 : MainSteps.SFix := ⟨5, 10, d5, [0, 1, 2, 3, 4], List.range 10,
  [0, 1, 2, 2, 1, 0, 0, 0, 0, 0], [0, 1, 2, 2, 1, 0, 0, 0, 0, 0], some #[[0], [1], [2], [3], [4]]⟩
/-- `C₅` likewise (from the round-1 audit's probe): degree `1`, no individualization; its
orbital configuration has no disconnected colour graph, so the leaf is `soj`'s (the discrete
colouring, `K = 1`, five representatives); one isomorphism. -/
def fM4C5 : MainSteps.SFix := { fM4D5 with gs := c5 }
/-- `AGL(1, 5)` likewise: degree `2`, one individualized point, `H = C₄` regular on the other
four (its components leaf: `K = H`). -/
def fM4AGL : MainSteps.SFix := { fM4D5 with gs := agl5 }

/-- The structures handed to reduce-and-derive: a partition leaf (tag `1`, not read), coloured
by the individualized points. -/
def stD5 : ℕ × CJData := (1, (([], ([], (0, #[]))), #[0, 0, 0, 0, 0]))
def stAGL : ℕ × CJData := (1, (([], ([], (0, #[]))), #[1, 0, 0, 0, 0]))

example : m4PiecesOK fM4D5 0 5 stD5 = true := by decide +kernel
example : m4PiecesOK fM4AGL 1 5 stAGL = true := by decide +kernel
run_cmd
  execRuns `m4_step_agl.run
    (← `(RunsS ssOracle body0 (tokF 5 10) (m4P fM4AGL)))
    ssOracle body0 (tokF 5 10) (m4P fM4AGL) cfg5
/-- **The whole step on `AGL(1, 5)`** (the components branch), kernel-checked in pieces: the
answer, the children and the tags. -/
theorem m4_step_agl : ∃ v ts, RunsS ssOracle body0 (tokF 5 10) (m4P fM4AGL) v ts ∧
    m4RunQ fM4AGL 5 stAGL [0, 2] v ts = true :=
  ⟨_, _, m4_step_agl.run, by decide +kernel⟩
/-- The whole step on `AGL(1, 5)`, on its trace (`m4RunB`: `MainSteps.records`,
`MainSteps.dynSteps`, `MainSteps.hasKernel`). -/
theorem m4_step_agl_tr : ∃ v tr, Runs ssOracle body0 (m4P fM4AGL) v tr ∧
    m4RunB fM4AGL 5 stAGL [0, 2] v tr = true :=
  runs_of_tok m4_step_agl
/-- **The uniprimitive branch** on `C₅`: no colour graph of the orbital configuration is
disconnected (`disconnD` is empty), so the leaves are `soj`'s; the five leaves bound the
representatives. -/
example : (SoJProg.disconnD (Case2b.colFn 5 (orbitalModel ssOracle 5 (10, gD c5, ())))
    (List.range 5) == [] && (msLeaves ssOracle 5 (10, gD c5, ())).length == 5) = true := by
  decide +kernel
example : m4PiecesOK fM4C5 0 5 stD5 = true := by decide +kernel
run_cmd
  execRuns `m4_step_c5.run
    (← `(RunsS ssOracle body0 (tokF 5 10) (m4P fM4C5)))
    ssOracle body0 (tokF 5 10) (m4P fM4C5) cfg5
/-- **The whole step on `C₅`** (the uniprimitive branch), kernel-checked in pieces: the answer,
the children and the tags (`K = 1`: every orbit is a single point, tag `0`). -/
theorem m4_step_c5 : ∃ v ts, RunsS ssOracle body0 (tokF 5 10) (m4P fM4C5) v ts ∧
    m4RunQ fM4C5 5 stD5 [0] v ts = true :=
  ⟨_, _, m4_step_c5.run, by decide +kernel⟩
/-- The whole step on `C₅`, on its trace (`m4RunB`). -/
theorem m4_step_c5_tr : ∃ v tr, Runs ssOracle body0 (m4P fM4C5) v tr ∧
    m4RunB fM4C5 5 stD5 [0] v tr = true :=
  runs_of_tok m4_step_c5

/-! ### Interpreter runs (supplementary) -/

def check (name : String) (b : Unit → Bool) : IO Unit := do
  unless b () do throw <| IO.userError s!"{name}: failed"
  IO.println s!"{name}: ok"

#eval check "m4StructProg on S₅ acting on the ten pairs (program and model, leaf, stabilizer \
    S₂ × S₃, ten representatives)" fun _ =>
  structOK 10 20 pet leafPet false true &&
    (m4StructModel ssOracle 10 (20, gD pet, ())).2.1.length == 10 &&
    (closure 20 ((m4StructModel ssOracle 10 (20, gD pet, ())).1.2.1.map img)).length == 12
#eval check "m4StepProg on D₅: the answer, the children (StepChild, ChildList with the factor \
    |reps| · m!, SizeChild, MeasLt, valid), the tags {0, 1}" fun _ =>
  m4RunOK fM4D5 5 stD5 [0, 1]
#eval check "m4StructProg on C₅ and D₅: the program computes the model" fun _ =>
  structOK 5 10 c5 leafC5 false true && structOK 5 10 d5 leafD5 false true

end GraphIsoChecks.MainM4
