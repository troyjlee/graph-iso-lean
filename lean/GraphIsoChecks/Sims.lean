module

public import GraphIsoChecks.Coverage
meta import GraphIsoChecks.Coverage
public import GraphIsoChecks.Sweep
meta import GraphIsoChecks.Sweep
public import GraphIso.Solver.SimsCompose
meta import GraphIso.Solver.SimsCompose
import all Init.Data.Array.Basic
import all Init.Data.List.Sort.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Mathlib.Data.List.Sort

/-!
# Milestone 2 checks: the Schreier–Sims backend

**Kernel-evaluated runs** of `simsSolver`, the solver with the Schreier–Sims backend, on small
instances. Each is tied to `solve_sims` through `runSims_spec`, whose hypotheses are decided,
and its answer is compared with brute force over `Perm (Fin 3)`. Kernel-evaluated table
constructions check group orders.

**Interpreter runs** (each `#eval` throws on a failure):

* complete tables of groups far beyond enumeration, with their known orders: `S₁₀`, `A₁₀`,
  the Mathieu groups `M₁₁` and `M₁₂`, `S₄ ≀ S₃`, `PSL(3, 2)` on 7 points;
* the `generate`, `stabilizer` and `orbits` implementations on some of them, as programs of
  the cost language: their results equal the oracle's and their costs are within the
  schedule `ssB`;
* the solver and both reductions against brute force on the families of
  `GraphIsoChecks/Sweep.lean` (degrees 1–4), with their costs within the proved bounds;
* solver runs at degrees 6, 7 and 8 against brute force over all `n!` permutations, including
  `PSL(3, 2)` on the Fano plane.
-/

@[expose] public section

namespace GraphIsoChecks.Sims

open Equiv GraphIso GraphIso.Cost GraphIso.Programs GraphIso.Solver GraphIso.Sims
  GraphIso.Enum GraphIsoChecks.Reference Pointwise

instance : DecidableEq (CosetData Ty.unit) := inferInstance
instance : DecidableEq (AnswerData Ty.unit) :=
  inferInstanceAs (DecidableEq (Option (CosetData Ty.unit)))
instance : DecidableEq (AnswerData Ty.unit × ℕ) := inferInstance

/-- Run the solver with the Schreier–Sims backend: the answer and the charged cost. -/
def runSims (inp : Solver.Ty.input.denote) : Option (AnswerData Ty.unit × ℕ) :=
  (eval Ctx.empty.O (simsSolver.proc Ty.denote) 100000
    ((solveEntry Ty.unit Ty.denote inp).subst ssImpl)).map fun r => (r.1, Trace.localCost r.2)

/-- A run evaluated by the kernel is the run of `solve_sims`: its answer is correct and its
cost is within `simsCost`. -/
theorem runSims_spec {n : ℕ} {xy : StrData × StrData} {w : WinData} {σd : PermData}
    {gs : GensData} {ans : AnswerData Ty.unit} {c : ℕ} (hw : WinData.validB n w = true)
    (hσ : PermData.validB n σd = true) (hgs : GensData.allValidB n gs = true)
    (hinv : GensData.invariantB gs w = true) (h : runSims (xy, w, σd, n, gs) = some (ans, c)) :
    Answer.IsCorrect (AnswerData.denote n ans) (w.denote n) (σd.denote n) (gs.denote n)
        (xy.1.denote n) (xy.2.denote n) ∧
      c ≤ simsCost n gs.length w.1.length (Nat.card (GensData.denote n gs)) := by
  have hw' := WinData.validB_iff.1 hw
  have hgs' := GensData.allValidB_iff.1 hgs
  obtain ⟨ans', tr, hr, hc, hok⟩ := solve_sims hw' (PermData.validB_iff.1 hσ) hgs'
    ((GensData.invariantB_iff hgs' hw').1 hinv)
  unfold runSims at h
  rcases he : eval Ctx.empty.O (simsSolver.proc Ty.denote) 100000
    ((solveEntry Ty.unit Ty.denote (xy, w, σd, n, gs)).subst ssImpl) with _ | ⟨a, tr'⟩
  · rw [he] at h
    cases h
  · rw [he] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    obtain ⟨rfl, rfl⟩ := Runs.unique ⟨_, he⟩ hr
    exact ⟨hok.isCorrect, hc⟩

/-- Membership in the coset an answer denotes, by enumerating its group. -/
theorem mem_denote_some {n : ℕ} {τ : PermData} {H : GroupData (Ty.denote Ty.unit)}
    (hH : GensData.allValidB n H.gens = true) (g : Perm (Fin n)) :
    g ∈ Answer.denote (AnswerData.denote n (some (τ, H))) ↔
      ∃ e ∈ enumerate n H.gens, PermData.denote n τ * PermData.denote n e = g := by
  rw [AnswerData.denote, Option.map_some, Answer.denote_some, mem_leftCoset_iff',
    ((enumerate_spec (GensData.allValidB_iff.1 hH)).1.2.2 _)]
  exact exists_congr fun e => and_congr_right fun _ => by rw [eq_inv_mul_iff_mul_eq]

/-- An answer of degree 3 with no backend data. -/
def ansU (τ : PermData) (gs : GensData) : AnswerData Ty.unit := some (τ, (3, gs, ()))

/-! ### Kernel-evaluated runs -/

/-- `C₃` on `012 ↦ 120`: the unique solution `(0 2 1)`. -/
theorem runC3 : runSims ((#[0, 1, 2], #[1, 2, 0]), univ3, idD, 3, c3gens) =
    some (ansU (#[2, 0, 1], #[1, 2, 0]) [idD, idD, idD], 10651) := by
  decide +kernel

example := runSims_spec (by decide) (by decide) (by decide) (by decide) runC3

example : ∀ g, g ∈ Answer.denote (AnswerData.denote 3
      (ansU (#[2, 0, 1], #[1, 2, 0]) [idD, idD, idD])) ↔
    BruteIso univ3 idD c3gens #[0, 1, 2] #[1, 2, 0] g := by
  intro g
  rw [ansU, mem_denote_some (by decide)]
  revert g
  decide

/-- `S₃` on `001 ↦ 100`: the solutions `{c, (0 2)}`, as `c ⟨(0 1)⟩`. -/
theorem runS3 : runSims ((#[0, 0, 1], #[1, 0, 0]), univ3, idD, 3, s3gens) =
    some (ansU c3D [t01D, idD, idD, idD], 29001) := by
  decide +kernel

example := runSims_spec (by decide) (by decide) (by decide) (by decide) runS3

example : ∀ g, g ∈ Answer.denote (AnswerData.denote 3 (ansU c3D [t01D, idD, idD, idD])) ↔
    BruteIso univ3 idD s3gens #[0, 0, 1] #[1, 0, 0] g := by
  intro g
  rw [ansU, mem_denote_some (by decide)]
  revert g
  decide

/-- The trivial group with an impossible match. -/
theorem runNone : runSims ((#[0, 1, 2], #[0, 2, 1]), univ3, idD, 3, []) = some (none, 256) := by
  decide +kernel

example := runSims_spec (by decide) (by decide) (by decide) (by decide) runNone

/-- The empty window with the outer representative `(0 1)`: the whole coset `(0 1) C₃`. -/
theorem runEmpty : runSims ((#[0, 1, 2], #[1, 0, 2]), empty3, t01D, 3, c3gens) =
    some (ansU t01D [(#[2, 0, 1], #[1, 2, 0]), c3D, idD, idD, idD], 3972) := by
  decide +kernel

example := runSims_spec (by decide) (by decide) (by decide) (by decide) runEmpty

example : ∀ g, g ∈ Answer.denote (AnswerData.denote 3
      (ansU t01D [(#[2, 0, 1], #[1, 2, 0]), c3D, idD, idD, idD])) ↔
    BruteIso empty3 t01D c3gens #[0, 1, 2] #[1, 0, 2] g := by
  intro g
  rw [ansU, mem_denote_some (by decide)]
  revert g
  decide

/-- Group orders from complete tables, by kernel evaluation of the construction. -/
example : order 3 (build 3 #[0, 1, 2] s3gens).1 = 6 := by decide +kernel
example : order 4 (build 4 #[0, 1, 2, 3] GraphIsoChecks.Restriction.d4).1 = 8 := by
  decide +kernel

/-! ### Groups beyond enumeration -/

/-- Permutation data from 0-based cycles. -/
def ofCycles (n : ℕ) (cs : List (List ℕ)) : PermData :=
  let f := cs.foldl (fun (f : Array ℕ) c => (List.range c.length).foldl
    (fun f i => f.setIfInBounds (c.getD i 0) (c.getD ((i + 1) % c.length) 0)) f) (Array.range n)
  (f, (List.range n).foldl (fun (g : Array ℕ) i => g.setIfInBounds (get f i) i) (Array.range n))

def cycleOf (n : ℕ) : PermData := ofCycles n [List.range n]

/-- `S_n = ⟨(0 1), (0 1 … n−1)⟩`. -/
def symGens (n : ℕ) : GensData := [ofCycles n [[0, 1]], cycleOf n]

/-- `A_n = ⟨(0 1 2), (0 1 … n−1)⟩` for odd `n`, `⟨(0 1 2), (1 2 … n−1)⟩` for even `n`. -/
def altGens (n : ℕ) : GensData :=
  [ofCycles n [[0, 1, 2]], if n % 2 = 1 then cycleOf n else ofCycles n [(List.range n).drop 1]]

def m11Gens : GensData := [cycleOf 11, ofCycles 11 [[2, 6, 10, 7], [3, 9, 4, 5]]]

def m12Gens : GensData := [ofCycles 12 [List.range 11], ofCycles 12 [[2, 6, 10, 7], [3, 9, 4, 5]],
  ofCycles 12 [[0, 11], [1, 10], [2, 5], [3, 7], [4, 8], [6, 9]]]

/-- `S₄ ≀ S₃` on 12 points, with blocks `{0..3}, {4..7}, {8..11}`. -/
def wreathGens : GensData := [ofCycles 12 [[0, 1]], ofCycles 12 [[0, 1, 2, 3]],
  ofCycles 12 [[0, 4, 8], [1, 5, 9], [2, 6, 10], [3, 7, 11]],
  ofCycles 12 [[0, 4], [1, 5], [2, 6], [3, 7]]]

/-- `PSL(3, 2)` acting on the 7 points of the Fano plane with lines `{i, i + 1, i + 3}`: the
cycle and the collineation `(2 6)(4 5)`, an involution, so they generate more than the
Frobenius group of order 21. -/
def psl32Gens : GensData := [cycleOf 7, ofCycles 7 [[2, 6], [4, 5]]]

/-- Check a complete table's order for the base `0, …, n − 1`. -/
def checkOrder (name : String) (n : ℕ) (gs : GensData) (expected : ℕ) : IO Unit := do
  let o := order n (build n (Array.range n) gs).1
  unless o == expected do throw <| IO.userError s!"{name}: order {o}, expected {expected}"
  IO.println s!"{name}: order {o}"

#eval checkOrder "S10" 10 (symGens 10) 3628800
#eval checkOrder "A10" 10 (altGens 10) 1814400
#eval checkOrder "M11" 11 m11Gens 7920
#eval checkOrder "M12" 12 m12Gens 95040
#eval checkOrder "S4 wr S3" 12 wreathGens 82944
#eval checkOrder "PSL(3,2)" 7 psl32Gens 168

/-- Run one operation's implementation as a program of the cost language: the result and the
charged cost. -/
def runOp (op : GroupOp) (x : ((groupSig Ty.unit).arg op).denote) :
    Option (((groupSig Ty.unit).res op).denote × ℕ) :=
  (eval (b := Ty.unit) Ctx.empty.O (fun _ => .ret ()) 100000000
    (ssImpl op (Ty.unit, Ty.unit) Ty.denote x)).map fun r => (r.1, Trace.localCost r.2)

/-- The `generate` program on `(n, gs)`. -/
def runGenerate (n : ℕ) (gs : GensData) : Option ((ℕ × GensData × Unit) × ℕ) :=
  runOp .generate (n, gs)

/-- The `stabilizer` program on `((n, gs, ()), u)`. -/
def runStab (n : ℕ) (gs : GensData) (u : ℕ) : Option ((ℕ × GensData × Unit) × ℕ) :=
  runOp .stabilizer ((n, gs, ()), u)

/-- The `orbits` program on `((n, gs, ()), w)`. -/
def runOrbits (n : ℕ) (gs : GensData) (w : WinData) : Option (List (List ℕ) × ℕ) :=
  runOp .orbits ((n, gs, ()), w)

/-- The `generate` program agrees with the oracle within its charge. -/
def checkGenerate (name : String) (n : ℕ) (gs : GensData) : IO Unit := do
  match runGenerate n gs with
  | none => throw <| IO.userError s!"{name}: out of fuel"
  | some (G, c) =>
    let bound := genCost n gs.length + 2
    unless G == (n, generateModel n gs, ()) && decide (c ≤ bound) do
      throw <| IO.userError s!"{name}: disagreement (cost {c}, bound {bound})"
    IO.println s!"{name}: generate costs {c}, bound {bound}, {G.2.1.length} generators"

#eval checkGenerate "S8" 8 (symGens 8)
#eval checkGenerate "M11" 11 m11Gens
#eval checkGenerate "PSL(3,2)" 7 psl32Gens

/-- The `stabilizer` and `orbits` programs agree with the oracle within their charges. -/
def checkStabOrbits (name : String) (n : ℕ) (gs : GensData) (u : ℕ) : IO Unit := do
  let w := WinData.ofPoints n (List.range n)
  match runStab n gs u, runOrbits n gs w with
  | some (K, c₁), some (os, c₂) =>
    let b₁ := stabCost n gs.length + 5
    let b₂ := orbitsCost n gs.length n + 5
    unless K == (n, stabModel n gs u, ()) && decide (c₁ ≤ b₁) && os == orbitsModel n gs w &&
        decide (c₂ ≤ b₂) do
      throw <| IO.userError s!"{name}: disagreement"
    IO.println s!"{name}: stabilizer of order {order n (build n (Array.range n) K.2.1).1}, \
      cost {c₁} (bound {b₁}); {os.length} orbits, cost {c₂} (bound {b₂})"
  | _, _ => throw <| IO.userError s!"{name}: out of fuel"

#eval checkStabOrbits "M11, point 0" 11 m11Gens 0
#eval checkStabOrbits "PSL(3,2), point 3" 7 psl32Gens 3

/-! ### Comparisons with brute force -/

open GraphIsoChecks.Sweep in
/-- The answer is valid, and it denotes the solutions `B`: its representative times each element
of its group (closed by brute force), and nothing else. -/
def answerOK (n : ℕ) (B : List (List ℕ)) : AnswerData Ty.unit → Bool
  | none => B.isEmpty
  | some (τ, (m, hs, _)) =>
    let A := (closure n (hs.map img)).map (compose (img τ))
    m == n && PermData.validB n τ && GensData.allValidB n hs && A.all (· ∈ B) && B.all (· ∈ A)

/-- Run a reduction program with the Schreier–Sims backend. -/
def runWith (p : Prog (groupSig Ty.unit) (Rec Ty.unit) Ty.denote (Ty.answer Ty.unit)) :
    Option (AnswerData Ty.unit × ℕ) :=
  (eval Ctx.empty.O (simsSolver.proc Ty.denote) 10000000 (p.subst ssImpl)).map
    fun r => (r.1, Trace.localCost r.2)

namespace Case

open GraphIsoChecks.Sweep

variable (c : Sweep.Case)

/-- The solver agrees with brute force, within `simsCost`. -/
def solverOK : Bool :=
  match runSims ((c.x.toArray, c.y.toArray), WinData.ofPoints c.n c.pts, ofList c.σ, c.n,
      c.gens.map ofList) with
  | some (a, cost) => answerOK c.n c.solutions a &&
      decide (cost ≤ simsCost c.n c.gens.length c.pts.length c.group.length)
  | none => false

/-- The restriction reduction agrees with brute force, within `restrictSimsCost`. -/
def restrictOK : Bool :=
  match runWith (restrictProg (fun J => .recur J) ((c.x.toArray, c.y.toArray),
      WinData.ofPoints c.n c.pts, ofList c.σ, c.n, c.gens.map ofList, ())) with
  | some (a, cost) => answerOK c.n c.solutions a &&
      decide (cost ≤ restrictSimsCost c.n c.pts.length c.gens.length c.group.length)
  | none => false

/-- The block reduction agrees with brute force on the block system `bs`, within
`blockSimsCost`. -/
def blocksOK (bs : List (List ℕ)) : Bool :=
  match runWith (blockReduceProg (fun J => .recur J) (c.x.toArray, c.y.toArray)
      (WinData.ofPoints c.n c.pts) (ofList c.σ) (c.n, c.gens.map ofList, ()) bs) with
  | some (a, cost) => answerOK c.n c.solutions a &&
      decide (cost ≤ blockSimsCost c.n c.pts.length bs.length c.gens.length c.group.length
        (c.group.length / kernelOrder c.group bs))
  | none => false

end Case

open GraphIsoChecks.Sweep

#eval checkAll "Sims solver, degrees 1-3, binary strings"
  ([1, 2, 3].flatMap fun n => cases n (List.range n).permutations (binaryPairs n)) Case.solverOK
#eval checkAll "Sims solver, degree 4" (cases 4 [id4, cyc4] pairs4) Case.solverOK
#eval checkAll "Sims restriction, degrees 1-3"
  (([1, 2, 3].flatMap fun n => cases n [List.range n] (binaryPairs n)).filter (·.pts ≠ []))
  Case.restrictOK
#eval checkAll "Sims blocks, degrees 1-3"
  (withBlocks (cases 2 [[0, 1], [1, 0]] (binaryPairs 2) ++ cases 3 [[0, 1, 2]] (binaryPairs 3)))
  fun (c, bs) => c.blocksOK bs

/-- Larger instances: a group, a window of all points, and string pairs. -/
def bigCases (n : ℕ) (gens : List (List ℕ)) (strs : List (List ℕ × List ℕ)) : List Sweep.Case :=
  strs.map fun (x, y) => ⟨n, gens, List.range n, List.range n, x, y⟩

/- `⟨(0 1)(2 3)(4 5), (0 2 4)(1 3 5)⟩` and `S₃ × S₃` on 6 points; the dihedral group of order 16
and `⟨(0 1), (0 2 4 6)(1 3 5 7)⟩` on 8 points. -/
#eval checkAll "Sims solver, degrees 6 and 8"
  (bigCases 6 [[1, 0, 3, 2, 5, 4], [2, 3, 4, 5, 0, 1]]
      [([0, 0, 1, 1, 2, 2], [1, 1, 2, 2, 0, 0]), ([0, 1, 0, 1, 0, 1], [1, 0, 1, 0, 1, 0]),
        ([0, 0, 1, 1, 2, 2], [0, 1, 1, 2, 2, 0])] ++
    bigCases 6 [[1, 0, 2, 3, 4, 5], [1, 2, 0, 3, 4, 5], [0, 1, 2, 4, 3, 5], [0, 1, 2, 4, 5, 3]]
      [([0, 0, 1, 2, 2, 3], [1, 0, 0, 3, 2, 2]), ([0, 1, 2, 0, 1, 2], [2, 1, 0, 0, 2, 1])] ++
    bigCases 8 [[1, 2, 3, 4, 5, 6, 7, 0], [7, 6, 5, 4, 3, 2, 1, 0]]
      [([0, 0, 1, 1, 0, 0, 1, 1], [1, 1, 0, 0, 1, 1, 0, 0]),
        ([0, 1, 2, 3, 4, 5, 6, 7], [3, 2, 1, 0, 7, 6, 5, 4])] ++
    bigCases 8 [[1, 0, 2, 3, 4, 5, 6, 7], [2, 3, 4, 5, 6, 7, 0, 1]]
      [([0, 1, 0, 1, 0, 1, 0, 1], [1, 0, 1, 0, 1, 0, 1, 0]),
        ([0, 0, 1, 1, 2, 2, 3, 3], [1, 1, 2, 2, 3, 3, 0, 0])])
  Case.solverOK

/- `PSL(3, 2)` on the Fano plane: distinct symbols (the unique solution is a 7-cycle); a line
against a non-line (no solution); and two lines. -/
#eval checkAll "Sims solver, PSL(3,2)"
  (bigCases 7 [[1, 2, 3, 4, 5, 6, 0], [0, 1, 6, 3, 5, 4, 2]]
    [([0, 1, 2, 3, 4, 5, 6], [1, 2, 3, 4, 5, 6, 0]), ([0, 0, 0, 1, 1, 1, 1], [0, 0, 1, 0, 1, 1, 1]),
      ([0, 0, 1, 0, 1, 1, 1], [1, 0, 0, 1, 0, 1, 1])])
  Case.solverOK

end GraphIsoChecks.Sims
