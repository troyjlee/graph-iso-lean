module

public import GraphIsoChecks.Align
public import GraphIso.Main.StepsHint
public import GraphIso.Main.RD
import all Init.Data.Array.Basic
import all Init.Data.List.Sort.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Mathlib.Data.List.Sort

/-!
# Milestone 14, stage 14j-2 checks: the macro-steps

Checks of the stage 14j-2 step programs (`GraphIso/Main/`: `Transfer`, `StepsBase`,
`StepsHint`), each comparing a run with brute force computed in the same term. Programs run
with the verified Schreier–Sims oracle answering the backend calls directly and milestone 1's
solver (`solveBody`) as the recursive procedure (`runT`, as `GraphIsoChecks.Case3.runDirectS`).

**The sub-solver** (`spySub`): it makes a marker call `generate` at degree `0` (cheap, and
distinguished from the genuine calls by its first entry `SENT`) whose permutation data record
the child: its measure `(window size, base)`, its size facts (`n₀`, `n`, degree), its window,
its group's generators and its labels (`recordOf`); then it solves the child's instance by
milestone 1's solver (`.recur`), ignoring the hint. The interpreter's trace keeps every backend
call with its argument, so the recorded children (`records`) are exactly the sub-calls the step
made. The answers are compared with the brute-force solutions (`solsB`: the elements of
`σ • ⟨gs⟩`, enumerated by `closure`, carrying `x` to `y` on the window).

**The children** (`childrenOK`) against the frame's predicates, decided on data by Boolean
versions proved equivalent (`chainB_iff`, `freeB_iff`, `stepB_iff`, `listB_iff`): `ChildList`
(the window sizes sum to at most `c · |w|`, each child satisfies the predicate, every window is
nonempty), the measure decreases (`MeasLt`), the size facts (`SizeChild sC`, with the step's
generator bound `sC`: the spec's expression for the chain rule, M0, M1, M2a and the kernel
reduction, with the sub-solver's output bound `N²`; `N²`, the Schreier–Sims value of `sIn`, for
the steps through reduce-and-derive), and each child is a valid instance (window in its string
positions, invariant; group preserving the base, faithful on the strings; with a hint,
transitive on the window with valid labels).

**Kernel-checked examples** (`decide +kernel`), one per case condition:
* **The base case** (`fixedTestProg`, `fixedStepProg`): `⟨(2 3)⟩` fixes the window `{0, 1}`;
  the answer is the coset `σ • G` or `none`; a moving group is rejected by the test.
* **The chain rule** (`winOrbitsProg`, `chainProg`): `⟨(0 1), (2 3)⟩` on four positions (two
  orbits; one isomorphism; and a pair with none, where the sequence stops after one child):
  `ChainChild` children, `c = 1`.
* **M0** (`m0StepProg`): no hint, `D₄` transitive on four positions: one `FreeChild` child
  (window 4, base 2 `≤ 2 · 4 + 1`), four isomorphisms; and the coset `(0 1) • D₄`.
* **M1** (`m1StepProg`): a hint with an intransitive base action (orbits `{0, 1}, {2}, {3}`):
  one `FreeChild` child with base `2 < 4`.
* **M2a** (`m2aStepProg`): `C₄` on the strings and the base alike, labels `{i}` (not
  equidistributed over the blocks `{0, 2}, {1, 3}`, decided by `blkOKD` and `neqD`): one
  `FreeChild` child with base `2`, `2 · 2 ≤ 4`.
* **M3** (`m3Prog`): `C₂ ≀ C₂` on four positions with a primitive base action on two points
  (labels `{0}, {0}, {1}, {1}`): the kernel `⟨(0 1), (2 3)⟩` of the base action, two cosets
  (`≤ 2!`), `StepChild` children on its orbits (2 points `≤ 4/2`), `c = 2`.
* **The kernel reduction** (`kerRedProg`) of a sub-instance of the M3 parent: `K = ⟨(0 2)(1 3)⟩`
  (base swap), the coset `(0 1) • K`; trivial kernel, singleton orbits, two cosets.
* **Transfer** (`childHInst`, `transferProg`): the M0 (two cosets) and M1 children (from
  `m0Prog`, `m1Prog`) solved by milestone 1's solver at the child's degree (against brute force
  there), and the answer transferred back is the parent's brute-force coset.
* **Same degree** (`sameDegProg`): one child without a hint at the same degree.
* **The dynamic chain** (`dynSeqProg`, each orbit handed to `spySub` without a hint):
  `⟨(0 1)(2 3)⟩` with strings forcing trivial automorphisms on the first orbit, so that the
  group left is not transitive on the second static orbit: three processed orbits (one of two
  points, two singletons), each an orbit of the current group (recorded with it, inside `G`),
  disjoint and covering the window; the answer (one isomorphism, and the identity).
* **The M2b step** (`m2bStepProg`): `C₄` on the strings and the base alike, labels `{i, i + 1}`
  (equidistributed over the maximal blocks `{0, 2}, {1, 3}`, decided by `blkOKD` and `neqD`):
  the block stabilizer against brute force, `c = |reps| = 2 ≤ #blocks` with the
  representatives covering `G`, `StepChild` children (`childrenOK`), hinted children on the
  block's two base points (`2 · 2 ≤ 4`) and unhinted ones on at most `|W|/2` points. With
  strings `0, 1, 0, 1` all children are hinted (the current group stays transitive on the second
  orbit); with `0, 1, 2, 3` it becomes trivial, the second orbit splits into singletons with
  constant labels, and the unhinted branch runs.
* **Reduce-and-derive** (`rdProg`, `rdOK`): a hinted parent, a cover `rs` of `G` by cosets of
  `K ≤ G` (by brute force), a structure, and a factor `F ≥ m`: the answer; the children
  `StepChild |W| m` with `c = |rs| · F` (`childrenOK`); the steps of the dynamic chains
  (`dynSteps`, read from the trace: the top-level `orbits` calls with the current group `H`),
  each an orbit `O ⊆ W` of `H ≤ K`; the tags of their derived hints (`deriveModel` for
  `(H, O)`), with tag `6` exactly when the kernel reduction runs (`hasKernel`). Fixtures:
  tags `0` and `1` (`D₄` alike, labels `{i}`, `K = ⟨(0 2)⟩` preserving the colored partition
  `{0, 2}, {1}, {3}`, four cosets); tag `3` (`C₄` alike, labels `{i, i + 1}`: the
  block-stabilizer loop inside, with hinted and unhinted children); tag `6` (`C₃` alike, no
  structure: the kernel reduction, `F = m!`, as `rd_sem6` states); tags `4` and `5` on the
  Johnson structure `j12` of `GraphIsoChecks.MainHints` (`K = C₂ ≀ C₂` preserving it, degree
  `16`): the child on the four cells, and the fallback's children (two `R`-orbits of two
  points per coset, unhinted, at the cells' degree `8`).

The whole file compiles in about two minutes; the reduce-and-derive examples at degree `16` take
about 25 seconds each.
-/

@[expose] public section

namespace GraphIsoChecks.MainSteps

open Equiv GraphIso GraphIso.Cost GraphIso.Programs GraphIso.Sims GraphIso.Main GraphIso.Solver
  GraphIso.Toolkit GraphIsoChecks.Sweep

/-! ### Running, brute force -/

/-- Run with the verified oracle and milestone 1's solver as the recursive procedure, keeping
the trace. -/
def runT {t : Ty} (p : Prog (groupSig Ty.unit) (Rec Ty.unit) Ty.denote t) :
    Option (t.denote × Trace (groupSig Ty.unit)) :=
  eval ssOracle (Solver.solveBody Ty.unit Ty.denote) 10000000 p

/-- The value of a run. -/
def runV {t : Ty} (p : Prog (groupSig Ty.unit) (Rec Ty.unit) Ty.denote t) : Option t.denote :=
  (runT p).map Prod.fst

def gD (gs : List (List ℕ)) : GensData := gs.map ofList

def setEq (u v : List ℕ) : Bool := u.all (· ∈ v) && v.all (· ∈ u)

def sameSet (A B : List (List ℕ)) : Bool := A.all (· ∈ B) && B.all (· ∈ A)

/-- The image of `v` under the image list `p`. -/
def ap (p : List ℕ) (v : ℕ) : ℕ := p.getD v v

/-- The orbit of `u` under the elements `H`. -/
def orbitB (H : List (List ℕ)) (u : ℕ) : List ℕ := (H.map fun g => ap g u).dedup

/-- **The brute-force solutions**: the elements `σ g` (`g ∈ G`, image lists) with
`y[σ g u] = x[u]` on the window. -/
def solsB (G : List (List ℕ)) (σ x y w : List ℕ) : List (List ℕ) :=
  (G.map (compose σ)).filter fun g => w.all fun u => y.getD (ap g u) 0 == x.getD u 0

/-- **The answer is the brute-force coset** `B` at degree `N` (or `none` when `B` is empty). -/
def ansOK (N : ℕ) (B : List (List ℕ)) : AnswerData Ty.unit → Bool
  | none => B.isEmpty
  | some (τ, (m, hs, _)) =>
    m == N && PermData.validB N τ && GensData.allValidB N hs &&
      sameSet ((closure N (hs.map img)).map (compose (img τ))) B

/-- Valid labels for the group `H` (elements at degree `n + k`) on the window `pts`:
equivariant, not constant, entries below `k` (stage 14b's `HintValid` on data). -/
def labOK (n k : ℕ) (H : List (List ℕ)) (pts : List ℕ) (L : Array (List ℕ)) : Bool :=
  H.all (fun g => pts.all fun i =>
      setEq (L.getD (ap g i) []) ((L.getD i []).map fun t => ap g (n + t) - n)) &&
    pts.any (fun i => pts.any fun j => !setEq (L.getD i []) (L.getD j [])) &&
    pts.all (fun i => (L.getD i []).all (· < k))

/-- **A valid (hinted) instance** on data, by brute force: degree `N ≥ n`, the window in
`[0, n)` without repetitions and invariant, the base `[n, N)` invariant, the group faithful on
the strings, and with labels `L`: transitive on the window, with valid labels. -/
def instOK (n N : ℕ) (G : List (List ℕ)) (w : List ℕ) (L : Option (Array (List ℕ))) : Bool :=
  n ≤ N && G.all (·.length == N) && w.dedup.length == w.length && w.all (· < n) &&
    G.all (fun g => w.all fun u => ap g u ∈ w) &&
    G.all (fun g => (List.range (N - n)).all fun j => n ≤ ap g (n + j)) &&
    G.all (fun g => g.take n != List.range n || g == List.range N) &&
    match L with
    | some L => w.all (fun u => setEq (orbitB G u) w) && labOK n (N - n) G w L
    | none => true

/-! ### The frame's predicates on data -/

def chainB (n : ℕ) (x : ℕ × Option ℕ) : Bool := x.2.isNone && decide (x.1 < n)

theorem chainB_iff {n : ℕ} {x : ℕ × Option ℕ} : chainB n x = true ↔ ChainChild n x := by
  obtain ⟨a, _ | b⟩ := x <;> simp [chainB, ChainChild]

def freeB (n m : ℕ) (x : ℕ × Option ℕ) : Bool :=
  decide (x.1 ≤ n) &&
    match x.2 with
    | some m' => decide (m' ≤ m) && (decide (m' < m) || decide (x.1 < n))
    | none => decide (2 * x.1 ≤ n)

theorem freeB_iff {n m : ℕ} {x : ℕ × Option ℕ} : freeB n m x = true ↔ FreeChild n m x := by
  obtain ⟨a, _ | b⟩ := x <;> simp [freeB, FreeChild]

def stepB (n m : ℕ) (x : ℕ × Option ℕ) : Bool :=
  decide (x.1 ≤ n) &&
    match x.2 with
    | some m' => decide (4 * m' ≤ 3 * m)
    | none => decide (2 * x.1 ≤ n)

theorem stepB_iff {n m : ℕ} {x : ℕ × Option ℕ} : stepB n m x = true ↔ StepChild n m x := by
  obtain ⟨a, _ | b⟩ := x <;> simp [stepB, StepChild]

def listB (n c : ℕ) (p : ℕ × Option ℕ → Bool) (ch : List (ℕ × Option ℕ)) : Bool :=
  decide ((ch.map Prod.fst).sum ≤ c * n) && ch.all p && ch.all fun x => decide (1 ≤ x.1)

theorem listB_iff {n c : ℕ} {p : ℕ × Option ℕ → Bool} {P : ℕ × Option ℕ → Prop}
    (hp : ∀ x, p x = true ↔ P x) {ch : List (ℕ × Option ℕ)} :
    listB n c p ch = true ↔ ChildList n c P ch := by
  simp only [listB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, hp]
  exact ⟨fun h => ⟨h.1.1, h.1.2, h.2⟩, fun h => ⟨⟨h.1, h.2⟩, h.3⟩⟩

/-- `MeasLt` on data. -/
def measLtB (p q : ℕ × ℕ) : Bool := decide (p.1 < q.1) || (p.1 == q.1 && decide (p.2 < q.2))

/-! ### The instrumented sub-solver -/

/-- The marker of a recorded child. -/
def SENT : ℕ := 1000

/-- **The record of a child** `J` as permutation data: `[SENT, |w|, hint?, N − n, n₀, n, N,
#gens]`, the window, the group's generators, and the labels. -/
def recordOf (J : HInstData Ty.unit) : GensData :=
  (#[SENT, J.1.2.1.1.length, J.2.2.2.isSome.toNat, J.1.2.2.2.1 - J.2.2.1, J.2.1, J.2.2.1,
      J.1.2.2.2.1, J.1.2.2.2.2.1.length], #[]) ::
    (J.1.2.1.1.toArray, #[]) :: J.1.2.2.2.2.1 ++
      ((J.2.2.2.getD #[]).toList.map fun l => (l.toArray, #[]))

/-- The marker closing a sub-solver's run. -/
def SENT2 : ℕ := 1001

/-- **The instrumented sub-solver**: the marker call, then milestone 1's solver on the child's
instance (the hint ignored), then the closing marker. -/
def spySub (J : HInstData Ty.unit) :
    Prog (groupSig Ty.unit) (Rec Ty.unit) Ty.denote (Ty.answer Ty.unit) :=
  .bind (Prog.call (S := groupSig Ty.unit) GroupOp.generate (0, recordOf J)) fun _ =>
  .bind (.recur J.1) fun a =>
  .bind (Prog.call (S := groupSig Ty.unit) GroupOp.generate (0, [(#[SENT2], #[])])) fun _ => .ret a

/-- A recorded child. -/
structure Child where
  win : ℕ
  hint : Bool
  base : ℕ
  n₀ : ℕ
  n : ℕ
  deg : ℕ
  pts : List ℕ
  gens : List (List ℕ)
  labs : List (List ℕ)

def decode (r : List (List ℕ)) : Child :=
  let m := r.headD []
  let k := m.getD 7 0
  ⟨m.getD 1 0, m.getD 2 0 == 1, m.getD 3 0, m.getD 4 0, m.getD 5 0, m.getD 6 0, r.getD 1 [],
    (r.drop 2).take k, r.drop (2 + k)⟩

/-- The measure `(J.winSize, J.baseOpt)` of a child. -/
def Child.meas (c : Child) : ℕ × Option ℕ := (c.win, if c.hint then some c.base else none)

/-- **The sub-calls** of a run: the marker calls in its trace. -/
def records (tr : Trace (groupSig Ty.unit)) : List Child :=
  tr.filterMap fun e => match e with
    | .call .generate x _ =>
      if x.1 == 0 && (x.2.headD (#[], #[])).1.getD 0 0 == SENT then some (decode (x.2.map img))
      else none
    | _ => none

/-! ### Fixtures and the checks -/

/-- **A fixture**: the hinted instance `((x, y), (w, (σ, (N, ⟨gs⟩))))` with `n₀ = n` and the
labels `L`. -/
structure SFix where
  n : ℕ
  N : ℕ
  gs : List (List ℕ)
  w : List ℕ
  σ : List ℕ
  x : List ℕ
  y : List ℕ
  L : Option (Array (List ℕ))

def SFix.inst (f : SFix) : InstData Ty.unit :=
  ((f.x.toArray, f.y.toArray), (WinData.ofPoints f.N f.w, (ofList f.σ, (f.N, gD f.gs, ()))))

def SFix.hinst (f : SFix) : HInstData Ty.unit := (f.inst, (f.n, (f.n, f.L)))

/-- The group's elements. -/
def SFix.grp (f : SFix) : List (List ℕ) := closure f.N f.gs

/-- The brute-force solutions. -/
def SFix.sols (f : SFix) : List (List ℕ) := solsB f.grp f.σ f.x f.y f.w

/-- The fixture is a valid hinted instance (`HInstValid`, by brute force). -/
def SFix.ok (f : SFix) : Bool :=
  instOK f.n f.N f.grp f.w f.L && f.x.length == f.N && f.y.length == f.N &&
    PermData.validB f.N (ofList f.σ)

/-- The base `N − n` the potential sees: `2|w| + 1` without a hint. -/
def SFix.base (f : SFix) : ℕ := if f.L.isSome then f.N - f.n else 2 * f.w.length + 1

/-- `LabInvAt` on data (stage 14j-6a). -/
def labInvAtB (n₀ m t : ℕ) : Bool :=
  decide (m ≤ n₀) && (!decide (ell0 n₀ < m) ||
    decide (t * (Recursion.lam m + 1) ^ 2 ≤ 2 * (Recursion.lam n₀ + 1) ^ 2))

theorem labInvAtB_iff {n₀ m t : ℕ} : labInvAtB n₀ m t = true ↔ LabInvAt n₀ m t := by
  simp only [labInvAtB, LabInvAt, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, decide_eq_true_eq]
  constructor
  · rintro ⟨h1, h2 | h2⟩
    · exact ⟨h1, fun h => absurd h h2⟩
    · exact ⟨h1, fun _ => h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    by_cases h : ell0 n₀ < m
    · exact Or.inr (h2 h)
    · exact Or.inl h

/-- `LabInv` on data, for an instance with `n₀`, `n` string positions, degree `N` and labels
`L`. -/
def labInvB (n₀ n N : ℕ) (L : Option (Array (List ℕ))) : Bool :=
  decide (n ≤ n₀) && match L with
    | none => true
    | some L => labInvAtB n₀ (N - n) (labLen L)

/-- **The recorded children's size facts and validity** on the parent `f`: a smaller measure,
the size facts of `SizeChild sC` (with at most `sC` generators, and the label invariant when the
parent has it), and valid child instances. -/
def kidsSizeOK (f : SFix) (sC : ℕ) (cs : List Child) : Bool :=
  cs.all fun r =>
    measLtB (r.win, r.meas.2.getD (2 * r.win + 1)) (f.w.length, f.base) &&
    r.n₀ == f.n && r.n ≤ f.n && r.deg ≤ max f.N (2 * f.n) && decide (r.gens.length ≤ sC) &&
    (!labInvB f.n f.n f.N f.L ||
      labInvB r.n₀ r.n r.deg (if r.hint then some r.labs.toArray else none)) &&
    instOK r.n r.deg (closure r.deg r.gens) r.pts
      (if r.hint then some r.labs.toArray else none)

/-- **The children** of a step on the parent `f`: `ChildList` with the factor `c` and the
predicate `pred` (nonempty windows included), and `kidsSizeOK` with the step's generator bound
`sC`. -/
def childrenOK (f : SFix) (c : ℕ) (pred : ℕ × Option ℕ → Bool) (sC : ℕ) (cs : List Child) :
    Bool :=
  listB f.w.length c pred (cs.map Child.meas) && kidsSizeOK f sC cs

/-- **A step against brute force**: the fixture is valid, the step's answer (run with
`spySub`) is the brute-force coset, and its `1 ≤ k ≤ kmax` recorded children satisfy
`childrenOK`. -/
def stepOK (f : SFix) (p : Prog (groupSig Ty.unit) (Rec Ty.unit) Ty.denote (Ty.answer Ty.unit))
    (c : ℕ) (pred : ℕ × Option ℕ → Bool) (sC kmax : ℕ) : Bool :=
  f.ok &&
  match runT p with
  | some (a, tr) =>
    ansOK f.N f.sols a && 1 ≤ (records tr).length && (records tr).length ≤ kmax &&
      childrenOK f c pred sC (records tr)
  | none => false

/-- **The base case**: the test decides whether the group fixes the window (`expect`), and when
it does the step's answer is the brute-force coset. -/
def fixedOK (f : SFix) (expect : Bool) : Bool :=
  let fix := f.grp.all fun g => f.w.all fun u => ap g u == u
  f.ok && fix == expect &&
    runV (fixedTestProg (S := groupSig Ty.unit) (rec := Rec Ty.unit) f.hinst) == some fix &&
    (!fix || match runV (fixedStepProg (S := groupSig Ty.unit) (rec := Rec Ty.unit) f.hinst) with
      | some a => ansOK f.N f.sols a
      | none => false)

/-- The orbits of the group on the window, by brute force (each in window order). -/
def SFix.orbits (f : SFix) : List (List ℕ) :=
  (f.w.map fun u => f.w.filter (· ∈ orbitB f.grp u)).dedup

/-- **The chain rule** (an intransitive group: at least two orbits): `ChainChild` children,
`c = 1`, at most one per orbit. -/
def chainOK (f : SFix) : Bool :=
  2 ≤ f.orbits.length &&
    stepOK f (.bind (winOrbitsProg f.hinst) fun os => chainProg spySub f.hinst os) 1
      (chainB f.w.length) (max (f.N * f.N) f.gs.length) f.orbits.length

/-- **M0** (no hint, the group transitive on at least two window points): one `FreeChild` child
for the base `2|w| + 1`. -/
def m0OK (f : SFix) : Bool :=
  f.L.isNone && 2 ≤ f.w.length && f.orbits.length == 1 &&
    stepOK f (m0StepProg spySub f.hinst) 1 (freeB f.w.length (2 * f.w.length + 1))
      (Toolkit.rebaseModel ssOracle f.n f.N (Luks.maxBlocks f.N (gD f.gs) f.w)
        (gD f.gs)).2.1.length 1

/-- The base action (image lists on `[0, N − n)`). -/
def SFix.baseAct (f : SFix) : List (List ℕ) :=
  f.grp.map fun g => (List.range (f.N - f.n)).map fun t => ap g (f.n + t) - f.n

/-- The base action is transitive. -/
def SFix.baseTrans (f : SFix) : Bool :=
  setEq (orbitB f.baseAct 0) (List.range (f.N - f.n))

/-- **M1** (a hint, an intransitive base action): one `FreeChild` child. -/
def m1OK (f : SFix) (L : Array (List ℕ)) : Bool :=
  f.L.isSome && !f.baseTrans &&
    stepOK f (m1StepProg spySub f.hinst L) 1 (freeB f.w.length (f.N - f.n))
      (Toolkit.rebaseModel ssOracle f.n f.N
        (singD (m1O ssOracle f.n f.N (f.N, gD f.gs, ()) (WinData.ofPoints f.N f.w) L))
        (gD f.gs)).2.1.length 1

/-- **M2a** (a hint, a transitive base action, proper maximal blocks, a label not
equidistributed over them, decided by `blkOKD` and `neqD`): one `FreeChild` child. -/
def m2aOK (f : SFix) (L : Array (List ℕ)) : Bool :=
  f.L.isSome && f.baseTrans && blkOKD (f.N - f.n) (mbD f.n f.N (gD f.gs)) &&
    neqD f.n f.N (mbD f.n f.N (gD f.gs)) L f.w &&
    stepOK f (m2aStepProg spySub f.hinst L (mbD f.n f.N (gD f.gs))) 1
      (freeB f.w.length (f.N - f.n))
      (Toolkit.rebaseModel ssOracle f.n f.N (mbD f.n f.N (gD f.gs)) (gD f.gs)).2.1.length 1

/-- The index of the kernel of `J`'s base action in its group, by brute force. -/
def kerIndex (J : SFix) : ℕ :=
  J.grp.length / (J.grp.filter fun g => (List.range (J.N - J.n)).all fun j =>
    ap g (J.n + j) == J.n + j).length

/-- **The kernel reduction** of the instance `J` inside the hinted parent `P` (same degree and
string positions, `K ≤ G`, `w ⊆ W`), by `kerRedProg`, or by `m3Prog` when `J` is `P`:
`StepChild` children for the parent, `c` the index of the kernel (at most `(N − n)!`). -/
def kerOK (P J : SFix) (m3 : Bool) : Bool :=
  P.ok && (m3 || J.L.isNone) && J.n == P.n && J.N == P.N && J.grp.all (· ∈ P.grp) &&
    J.w.all (· ∈ P.w) && kerIndex J ≤ (J.N - J.n).factorial &&
    match runT (if m3 then m3Prog spySub P.hinst else kerRedProg spySub J.n J.n J.inst) with
    | some (a, tr) =>
      ansOK J.N J.sols a && 1 ≤ (records tr).length &&
        childrenOK P (kerIndex J) (stepB P.w.length (P.N - P.n))
          (max (P.N * P.N) (Toolkit.kerModel ssOracle J.n (J.N, gD J.gs, ())).2.1.length)
          (records tr)
    | none => false

/-- **Transfer**: the child `(G', (w', L'))` of a coarsening, solved by milestone 1's solver at
its degree (against brute force there), and the answer transferred back to the parent's group
(`transferProg`), which is the parent's brute-force coset. -/
def transferOK (f : SFix) (r : GroupData Ty.unit.denote × (WinData × Array (List ℕ))) : Bool :=
  let J := childHInst f.x.toArray f.y.toArray (ofList f.σ) f.n f.n r.1 r.2.1 (some r.2.2)
  let B' := solsB (closure r.1.1 (r.1.2.1.map img)) (List.range r.1.1) J.1.1.1.toList
    J.1.1.2.toList r.2.1.1
  f.ok &&
  match runV (.recur J.1) with
  | some (some c') =>
    ansOK r.1.1 B' (some c') &&
      match runV (transferProg f.n (ofList f.σ) (f.N, gD f.gs, ()) c') with
      | some a => ansOK f.N f.sols a
      | none => false
  | some none => B'.isEmpty && f.sols.isEmpty
  | none => false

/-- **Same degree, no hint**: one child, the instance itself without a hint. -/
def sameDegOK (f : SFix) : Bool :=
  f.ok &&
  match runT (sameDegProg spySub f.inst f.n f.n) with
  | some (a, tr) =>
    ansOK f.N f.sols a &&
      (records tr).map (fun r => (r.meas, r.deg)) == [((f.w.length, none), f.N)]
  | none => false

/-! ### Fixtures -/

/-- The base case: `⟨(2 3)⟩` fixes the window `{0, 1}`; `σ = (0 1)` carries `x` to `y`. -/
def fFix : SFix := ⟨4, 4, [[0, 1, 3, 2]], [0, 1], [1, 0, 2, 3], [5, 6, 7, 8], [6, 5, 9, 9], none⟩
/-- The same with `y` not matched by `σ`. -/
def fFixNo : SFix := { fFix with y := [5, 6, 9, 9] }
/-- `⟨(0 1)⟩` moves the window `{0, 1}`. -/
def fMove : SFix := { fFix with gs := [[1, 0, 2, 3]] }

/-- The chain rule: `⟨(0 1), (2 3)⟩`, one isomorphism `(0 1)(2 3)`. -/
def fChain : SFix :=
  ⟨4, 4, [[1, 0, 2, 3], [0, 1, 3, 2]], [0, 1, 2, 3], [0, 1, 2, 3], [1, 2, 1, 2], [2, 1, 2, 1], none⟩
/-- No isomorphism: the first orbit already fails. -/
def fChainNo : SFix := { fChain with y := [2, 2, 1, 1] }

/-- M0: `D₄` on four positions, no hint; the four elements carrying evens to odds. -/
def fM0 : SFix :=
  ⟨4, 4, [[1, 2, 3, 0], [0, 3, 2, 1]], [0, 1, 2, 3], [0, 1, 2, 3], [0, 1, 0, 1], [1, 0, 1, 0], none⟩

/-- M0 on the coset `(0 1) • D₄`, disjoint from `D₄`. -/
def fM0σ : SFix := { fM0 with σ := [1, 0, 2, 3], y := [1, 0, 0, 1] }

/-- M1: `(0 1)` on the strings with `(0 1)` on a base of four points (orbits `{0, 1}, {2}, {3}`),
labels `{0, 2}, {1, 2}` on the window `{0, 1}`. -/
def lM1 : Array (List ℕ) := #[[0, 2], [1, 2], [], []]
def fM1 : SFix := ⟨4, 8, [[1, 0, 2, 3, 5, 4, 6, 7]], [0, 1], List.range 8,
  [3, 4, 0, 0, 0, 0, 0, 0], [4, 3, 0, 0, 0, 0, 0, 0], some lM1⟩

/-- M2a: `C₄` on the strings and the base alike, labels `{i}`. -/
def lM2a : Array (List ℕ) := #[[0], [1], [2], [3]]
def fM2a : SFix := ⟨4, 8, [[1, 2, 3, 0, 5, 6, 7, 4]], [0, 1, 2, 3], List.range 8,
  [0, 1, 0, 1, 0, 0, 0, 0], [1, 0, 1, 0, 0, 0, 0, 0], some lM2a⟩

/-- M3: `C₂ ≀ C₂ = ⟨(0 1), (0 2)(1 3)⟩` on four positions, the second also swapping the two base
points (a primitive base action), labels `{0}, {0}, {1}, {1}`; two isomorphisms. -/
def fM3 : SFix := ⟨4, 6, [[1, 0, 2, 3, 4, 5], [2, 3, 0, 1, 5, 4]], [0, 1, 2, 3], List.range 6,
  [0, 1, 2, 2, 0, 0], [2, 2, 1, 0, 0, 0], some #[[0], [0], [1], [1]]⟩
/-- The kernel reduction of `(0 1) • ⟨(0 2)(1 3)⟩` inside the M3 parent. -/
def fKer : SFix := ⟨4, 6, [[2, 3, 0, 1, 5, 4]], [0, 1, 2, 3], [1, 0, 2, 3, 4, 5],
  [0, 1, 2, 2, 0, 0], [2, 2, 1, 0, 0, 0], none⟩

/-! ### The dynamic chain and the M2b step -/

/-- **The handle** of the dynamic chain: the orbit `O` of the current coset `c` as an instance
without a hint, solved by `spySub` (which records it with the coset's group). -/
def dynHandle (n : ℕ) (xy : StrData × StrData) (c : CosetData Ty.unit) (O : List ℕ) :
    Prog (groupSig Ty.unit) (Rec Ty.unit) Ty.denote (Ty.answer Ty.unit) :=
  spySub ((xy, (WinData.ofPoints c.2.1 O, c)), (n, (n, none)))

/-- The processed orbits are orbits of the groups recorded with them, inside `G`. -/
def orbitsOfCurrent (f : SFix) (cs : List Child) : Bool :=
  cs.all fun r => r.deg == f.N && (closure r.deg r.gens).all (· ∈ f.grp) &&
    setEq (orbitB (closure r.deg r.gens) (r.pts.headD 0)) r.pts

/-- **The dynamic chain** against brute force: the answer, `k` processed orbits, each an orbit
of the current group (`orbitsOfCurrent`), disjoint parts of the window, covering it when the
answer is a coset. -/
def dynOK (f : SFix) (k : ℕ) : Bool :=
  f.ok &&
  match runT (dynSeqProg (dynHandle f.n) (f.x.toArray, f.y.toArray)
      (ofList f.σ, (f.N, gD f.gs, ())) f.w) with
  | some (a, tr) =>
    let cs := records tr
    let ps := cs.flatMap (·.pts)
    ansOK f.N f.sols a && cs.length == k && orbitsOfCurrent f cs &&
      ps.dedup.length == ps.length && ps.all (· ∈ f.w) && (a.isNone || ps.length == f.w.length)
  | none => false

/-- `h` is in the coset `r H`. -/
def inCoset (H : List (List ℕ)) (r h : List ℕ) : Bool := H.any fun e => compose r e == h

/-- The cosets `r R` of the representatives cover `P`. -/
def coverB (P R reps : List (List ℕ)) : Bool := P.all fun g => reps.any fun r => inCoset R r g

/-- **The M2b step** against brute force (a hint, a transitive base action with proper maximal
blocks over which every window label is equidistributed): the block stabilizer `R` of the
first block, `c = |reps| ≤ #blocks` with the representatives covering `G` by cosets of `R`; the
answer; `StepChild` children for `c` (`childrenOK`), each hinted one on `N' − n` base points
with `2 (N' − n) ≤ m`, each unhinted one on at most `|W|/2` points; `kh` hinted and `ku`
unhinted children. -/
def m2bOK (f : SFix) (L : Array (List ℕ)) (kh ku : ℕ) : Bool :=
  let bs := mbD f.n f.N (gD f.gs)
  let m := f.N - f.n
  let st := blockStabModel ssOracle f.N bs (gD f.gs) 0
  let R := closure f.N (st.1.2.1.map img)
  let B₀ := bs.headD []
  f.L.isSome && f.baseTrans && blkOKD m bs && !neqD f.n f.N bs L f.w &&
    sameSet R (f.grp.filter fun g => setEq (B₀.map (ap g)) B₀) &&
    st.2.length ≤ bs.length && coverB f.grp R (st.2.map img) &&
    match runT (m2bStepProg spySub f.hinst bs) with
    | some (a, tr) =>
      let cs := records tr
      ansOK f.N f.sols a && childrenOK f st.2.length (stepB f.w.length m) (f.N * f.N) cs &&
        cs.all (fun r => if r.hint then r.base == B₀.length && 2 * r.base ≤ m
          else 2 * r.win ≤ f.w.length) &&
        (cs.filter (·.hint)).length == kh && (cs.filter (!·.hint)).length == ku
    | none => false

/-- The dynamic chain: `⟨(0 1)(2 3)⟩` with distinct letters (only the identity on `{0, 1}`). -/
def fDyn : SFix :=
  ⟨4, 4, [[1, 0, 3, 2]], [0, 1, 2, 3], [0, 1, 2, 3], [0, 1, 2, 3], [0, 1, 2, 3], none⟩
/-- The same with `y` the image by `(0 1)(2 3)`: one isomorphism. -/
def fDynIso : SFix := { fDyn with y := [1, 0, 3, 2] }

/-- M2b: `C₄` on the strings and the base alike, labels `{i, i + 1}`. -/
def lM2b : Array (List ℕ) := #[[0, 1], [1, 2], [2, 3], [3, 0]]
def fM2b : SFix := ⟨4, 8, [[1, 2, 3, 0, 5, 6, 7, 4]], [0, 1, 2, 3], List.range 8,
  [0, 1, 0, 1, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0], some lM2b⟩
/-- The same with distinct letters: the unhinted branch runs. -/
def fM2b' : SFix := { fM2b with x := [0, 1, 2, 3, 0, 0, 0, 0], y := [0, 1, 2, 3, 0, 0, 0, 0] }

/-! ### Reduce-and-derive -/

/-- **The steps of the top-level dynamic chains** of a run of `rdProg`: the `orbits` calls at
degree `N` on nonempty windows in `[0, n)` (the step's current group `H` and the remaining
points), with the first orbit `O` of the result, outside the sub-solver's runs (between its
markers) and other than the kernel reduction's (the `orbits` call after a `kernel` call). The
other `orbits` calls are at other degrees (the re-based groups) or on base windows (M1). -/
def dynSteps (n N : ℕ) (tr : Trace (groupSig Ty.unit)) :
    List (GroupData Ty.unit.denote × List ℕ) :=
  (tr.foldl (fun (st : List (GroupData Ty.unit.denote × List ℕ) × Bool × Bool) e =>
    match e with
    | .call .generate x _ =>
      let h := (x.2.headD (#[], #[])).1.getD 0 0
      if x.1 == 0 && h == SENT then (st.1, true, false)
      else if x.1 == 0 && h == SENT2 then (st.1, false, false) else (st.1, st.2.1, false)
    | .call .kernel _ _ => (st.1, st.2.1, true)
    | .call .orbits x y =>
      if !st.2.1 && !st.2.2 && x.1.1 == N && !x.2.1.isEmpty && x.2.1.all (· < n) then
        ((x.1, y.headD []) :: st.1, st.2.1, false)
      else (st.1, st.2.1, false)
    | .call _ _ _ => (st.1, st.2.1, false)
    | _ => st) ([], false, false)).1.reverse

/-- The run calls `kernel` (only the kernel reduction of a stuck orbit does). -/
def hasKernel (tr : Trace (groupSig Ty.unit)) : Bool :=
  tr.any fun e => match e with
    | .call .kernel _ _ => true
    | _ => false

/-- **Reduce-and-derive** against brute force, for the hinted parent `f`, the cover `rs` of `G`
by cosets of `K = ⟨ks⟩ ≤ G` (by brute force), the structure `st` and the factor `F ≥ m`: the
answer; the children `StepChild |W| m` with `c = |rs| · F` (`childrenOK`: also `SizeChild` and
valid children, the hinted ones transitive with valid labels); every step of the dynamic
chains an orbit `O ⊆ W` of its current group `H ≤ K`; the tags of the derived hints of the
steps (`deriveModel` for `(H, O)`) are `tags`, and tag `6` occurs exactly when the kernel
reduction runs. -/
def rdOK (f : SFix) (ks rs : List (List ℕ)) (st : ℕ × CJData) (F : ℕ) (tags : List ℕ) : Bool :=
  let K := closure f.N ks
  f.ok && K.all (· ∈ f.grp) && coverB f.grp K rs && f.N - f.n ≤ F && 1 ≤ F &&
  match runT (rdProg spySub f.hinst (gD rs) (f.N, gD ks, ()) st) with
  | some (a, tr) =>
    let steps := dynSteps f.n f.N tr
    let tg := steps.map fun s => (deriveModel ssOracle f.n f.N s.1 s.2 (f.L.getD #[]) st).1
    ansOK f.N f.sols a &&
      childrenOK f (rs.length * F) (stepB f.w.length (f.N - f.n)) (f.N * f.N) (records tr) &&
      steps.all (fun s => (closure f.N (s.1.2.1.map img)).all (· ∈ K) && s.2.all (· ∈ f.w) &&
        setEq (orbitB (closure f.N (s.1.2.1.map img)) (s.2.headD 0)) s.2) &&
      setEq tg tags && tg.contains 6 == hasKernel tr
  | none => false

/-- `K` preserves the colored partition `p` (blocks with colours) of the base: every element maps
each block onto a block of the same colour. -/
def cpartPres (f : SFix) (ks : List (List ℕ)) (p : List (List ℕ × ℕ)) : Bool :=
  (closure f.N ks).all fun g => p.all fun B => p.any fun B' =>
    B'.2 == B.2 && setEq (B.1.map fun j => ap g (f.n + j) - f.n) B'.1

/-- Tags 0 and 1: `D₄` on the strings and the base alike, labels `{i}`, `K = ⟨(0 2)⟩` (orbits
`{0, 2}` (M1 on the base orbit `{0, 2}`), `{1}`, `{3}` (constant labels)), four cosets. -/
def fRD01 : SFix := ⟨4, 8, [[1, 2, 3, 0, 5, 6, 7, 4], [2, 1, 0, 3, 6, 5, 4, 7]], [0, 1, 2, 3],
  List.range 8, [0, 1, 0, 1, 0, 0, 0, 0], [1, 0, 1, 0, 0, 0, 0, 0], some #[[0], [1], [2], [3]]⟩
def kRD01 : List (List ℕ) := [[2, 1, 0, 3, 6, 5, 4, 7]]
def rRD01 : List (List ℕ) :=
  [List.range 8, [1, 2, 3, 0, 5, 6, 7, 4], [2, 3, 0, 1, 6, 7, 4, 5], [3, 0, 1, 2, 7, 4, 5, 6]]

/-- Tag 3: `K = G = C₄` on the strings and the base alike, labels `{i, i + 1}` (the M2b case
inside reduce-and-derive). -/
def fRD3 : SFix := ⟨4, 8, [[1, 2, 3, 0, 5, 6, 7, 4]], [0, 1, 2, 3], List.range 8,
  [0, 1, 2, 3, 0, 0, 0, 0], [0, 1, 2, 3, 0, 0, 0, 0], some #[[0, 1], [1, 2], [2, 3], [3, 0]]⟩

/-- Tag 6: `K = G = C₃` on the strings and the base alike, labels `{i}`, no structure. -/
def fRD6 : SFix := ⟨3, 6, [[1, 2, 0, 4, 5, 3]], [0, 1, 2], List.range 6, [0, 1, 1, 0, 0, 0],
  [1, 1, 0, 0, 0, 0], some #[[0], [1], [2]]⟩

/-- No structure (any tag but `2`). -/
def noSt : ℕ × CJData := (0, (([], [], 0, #[]), #[]))

/-- The Johnson structure `j12` of `GraphIsoChecks.MainHints` (proved `IsJohnson` and `JValid`
there): cells `A = {6, 7}`, `B = {8, 9}`, `C = {10}`, `D = {11}`, `s = 2`, `V₀` the six pairs. -/
def cj12 : CJData :=
  (([0, 1, 2, 3, 4, 5], [[6, 7], [8, 9], [10], [11]], 2,
    #[[0, 1], [0, 2], [0, 3], [1, 2], [1, 3], [2, 3]]), #[])
/-- `K = C₂ ≀ C₂` at degree `4 + 12` (`k12` of `MainHints`). -/
def k12 : List (List ℕ) :=
  [[1, 0, 2, 3, 4, 5, 6, 7, 8, 9, 11, 10, 12, 13, 14, 15],
    [0, 1, 3, 2, 4, 5, 6, 7, 8, 9, 10, 11, 13, 12, 14, 15],
    [2, 3, 0, 1, 4, 7, 8, 5, 6, 9, 12, 13, 10, 11, 14, 15]]
/-- The decoded colour at `u` (`cjcol`, on data). -/
def colB (m : ℕ) (e : CJData) (u : ℕ) : ℕ :=
  if u ∈ Align.jrest m e.1 then get e.2 u + 1 else 0

/-- `K` preserves the coloured Johnson structure `e` of the base (`GraphIsoChecks.MainHints`'s
`cjPres`): the base action of every element carries the embedding (stage 14d's leaf data) and
the colours to themselves. -/
def cjPres (f : SFix) (ks : List (List ℕ)) (e : CJData) : Bool :=
  let m := f.N - f.n
  (closure f.N ks).all fun g =>
    let σ := (List.range m).map fun t => ap g (f.n + t) - f.n
    GraphIsoChecks.Align.outMaps m (ofList σ) (GraphIsoChecks.Align.johnOut e.1)
      (GraphIsoChecks.Align.johnOut e.1) &&
      (List.range m).all fun u => colB m e (ap σ u) == colB m e u

/-- Tag 4 (`fxU`): labels `{AC}`, `{BC}`. -/
def fRD4 : SFix := ⟨4, 16, k12, [0, 1, 2, 3], List.range 16, (List.range 4).map (· % 2) ++
  List.replicate 12 0, [1, 0, 1, 0] ++ List.replicate 12 0, some #[[1], [1], [3], [3]]⟩
/-- Tag 5 (`fxF`): labels `{AC, BD}`, `{AD, BC}`. -/
def fRD5 : SFix := { fRD4 with L := some #[[1, 4], [1, 4], [2, 3], [2, 3]] }

/-! ### Kernel-checked examples -/

example : (fixedOK fFix true && fixedOK fFixNo true && fixedOK fMove false) = true := by
  decide +kernel
example : (chainOK fChain && chainOK fChainNo) = true := by decide +kernel
example : (m0OK fM0 && m0OK fM0σ) = true := by decide +kernel
example : m1OK fM1 lM1 = true := by decide +kernel
example : m2aOK fM2a lM2a = true := by decide +kernel
example : kerOK fM3 fM3 true = true := by decide +kernel
example : kerOK fM3 fKer false = true := by decide +kernel
example : (match runV (m0Prog (D := Ty.unit) 4 4 (gD fM0.gs) (WinData.ofPoints 4 fM0.w)) with
    | some r => transferOK fM0 r && transferOK fM0σ r
    | none => false) = true := by decide +kernel
example : (match runV (m1Prog (D := Ty.unit) 4 8 (8, gD fM1.gs, ()) (WinData.ofPoints 8 fM1.w)
      lM1) with
    | some r => transferOK fM1 r
    | none => false) = true := by decide +kernel
example : (sameDegOK fM0 && sameDegOK fChain) = true := by decide +kernel
example : (dynOK fDyn 3 && dynOK fDynIso 3) = true := by decide +kernel
example : m2bOK fM2b lM2b 3 0 = true := by decide +kernel
example : m2bOK fM2b' lM2b 2 2 = true := by decide +kernel
/-- Reduce-and-derive, tags 0 and 1: `K = ⟨(0 2)⟩` preserves the colored partition `{0, 2}`,
`{1}`, `{3}` of the base (`t = 2`, `4t ≤ 3m`); four cosets, `F = m`. -/
example : (cpartPres fRD01 kRD01 [([0, 2], 0), ([1], 1), ([3], 2)] &&
    rdOK fRD01 kRD01 rRD01 noSt 4 [0, 1]) = true := by decide +kernel
/-- Tag 3 (`m2bLoopProg` inside): `C₄` preserves `{0, 2}, {1, 3}`; `F = m`. -/
example : (cpartPres fRD3 fRD3.gs [([0, 2], 0), ([1, 3], 0)] &&
    rdOK fRD3 fRD3.gs [List.range 8] noSt 4 [3]) = true := by decide +kernel
/-- Tag 6 (stuck, no structure, primitive base action of `C₃`): the kernel reduction, with
`F = m! = 6` (`rd_sem6`). -/
example : rdOK fRD6 fRD6.gs [List.range 6] noSt 6 [6] = true := by decide +kernel
/-- Tags 4 and 5 on the coloured Johnson structure `j12`, preserved by `K = C₂ ≀ C₂`. -/
example : (cjPres fRD4 k12 cj12 && rdOK fRD4 k12 [List.range 16] (2, cj12) 12 [4]) = true := by
  decide +kernel
example : (cjPres fRD5 k12 cj12 && rdOK fRD5 k12 [List.range 16] (2, cj12) 12 [5]) = true := by
  decide +kernel

/-! ### The label invariant (stage 14j-6a) -/

/-- **The label lengths of item 3 of `PLAN-14.md` §14.10 on data**: M0's labels are singletons
(`labLen_labM0D`); the Johnson union of `fRD5`'s labels on the window through the cells of
`cj12` (`labJUD`, as the derived hint computes it) has length `4 = labLen L · s`
(`labLen_labJUD_le`), with `C(4, 2) = 6 ≤ 12`, `2 ≤ s` and `2s ≤ 4` (`dv_cj_choose_le`,
`DOutcome.johnUnion`). -/
example : (labLen (labM0D 4 #[0, 1, 0, 1]) == 1 &&
    labLen (labJUD cj12.1.2.1.length (markArr 12 cj12.1.1) cj12.1.2.2.2
      #[[1, 4], [1, 4], [2, 3], [2, 3]] [0, 1, 2, 3]) == 4 &&
    labLen #[[1, 4], [1, 4], [2, 3], [2, 3]] * cj12.1.2.2.1 == 4 &&
    decide (cj12.1.2.1.length.choose cj12.1.2.2.1 ≤ 12) && decide (2 ≤ cj12.1.2.2.1) &&
    decide (2 * cj12.1.2.2.1 ≤ cj12.1.2.1.length)) = true := by decide +kernel

/-- **A negative control**: labels of length `3` on a base of `2500` points, above
`ell0 3000 = 2048`, fail the invariant (`3 · 12² > 2 · 12²`); length `2` meets it. -/
theorem not_labInvAt : ¬ LabInvAt 3000 2500 3 := by
  rw [← labInvAtB_iff]
  decide +kernel

example : LabInvAt 3000 2500 2 := labInvAtB_iff.1 (by decide +kernel)

/-- An instance with such labels does not satisfy `LabInv`. -/
example : ¬ LabInv ((((#[], #[]), (WinData.ofPoints 2501 [0], (PermData.one 2501,
    (2501, [], ())))), (3000, (1, some #[[0, 1, 2]]))) : HInstData Ty.unit) :=
  fun h => not_labInvAt (h.hint _ rfl)

end GraphIsoChecks.MainSteps
