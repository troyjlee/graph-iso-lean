module

public import GraphIsoChecks.Sims
meta import GraphIsoChecks.Sims
public import GraphIso.Solver.Luks
meta import GraphIso.Solver.Luks
import all Init.Data.Array.Basic
import all Init.Data.List.Sort.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Mathlib.Data.List.Sort

/-!
# Milestone 3 checks: Luks's strategy

**Kernel-evaluated runs** of `luksSolver`, the solver with Luks's strategy and the
Schreier–Sims backend, tied to `solve_luks_any` through `runLuks_spec`, with brute-force
comparisons.

**Interpreter runs** (each `#eval` throws on a failure):

* maximal block systems (`maxBlocks`) of transitive groups, against the expected blocks;
* the solver against brute force on the families of `GraphIsoChecks/Sweep.lean` (degrees 1–4;
  all groups, windows and string pairs, with fewer outer representatives than the default
  strategy's sweep) and on selected groups of degrees 6–8, including `PSL(3, 2)`, within
  `luksSimsCost` for `c = n` (valid for every group);
* iterated wreath products of `C₂`, which are `2`-groups: on 8 points (order 128) against brute
  force, and on 16 points (order 32768) against the solutions found by enumerating the group
  from a complete Sims table; their costs are within the nilpotent bound
  `6640 (n + 1)⁸ + 60 L (n + 1)²` of `solve_luks_nilpotent`, and are compared with the default
  strategy where that one runs.
-/

@[expose] public section

namespace GraphIsoChecks.Luks

open Equiv GraphIso GraphIso.Cost GraphIso.Programs GraphIso.Solver GraphIso.Sims GraphIso.Luks
  GraphIso.Enum GraphIsoChecks.Reference GraphIsoChecks.Sims Pointwise

/-- Run the solver with Luks's strategy and the Schreier–Sims backend: the answer and the
charged cost. -/
def runLuks (inp : Solver.Ty.input.denote) : Option (AnswerData Ty.unit × ℕ) :=
  (eval Ctx.empty.O (luksSolver.proc Ty.denote) 100000
    ((solveEntry Ty.unit Ty.denote inp).subst ssImpl)).map fun r => (r.1, Trace.localCost r.2)

/-- A run evaluated by the kernel is the run of `solve_luks_any`: its answer is correct and its
cost is within `luksSimsCost` for `c = n`. -/
theorem runLuks_spec {n : ℕ} {xy : StrData × StrData} {w : WinData} {σd : PermData}
    {gs : GensData} {ans : AnswerData Ty.unit} {c : ℕ} (hw : WinData.validB n w = true)
    (hσ : PermData.validB n σd = true) (hgs : GensData.allValidB n gs = true)
    (hinv : GensData.invariantB gs w = true) (h : runLuks (xy, w, σd, n, gs) = some (ans, c)) :
    Answer.IsCorrect (AnswerData.denote n ans) (w.denote n) (σd.denote n) (gs.denote n)
        (xy.1.denote n) (xy.2.denote n) ∧
      c ≤ luksSimsCost n gs.length w.1.length n := by
  have hw' := WinData.validB_iff.1 hw
  have hgs' := GensData.allValidB_iff.1 hgs
  obtain ⟨ans', tr, hr, hc, hok⟩ := solve_luks_any hw' (PermData.validB_iff.1 hσ) hgs'
    ((GensData.invariantB_iff hgs' hw').1 hinv)
  unfold runLuks at h
  rcases he : eval Ctx.empty.O (luksSolver.proc Ty.denote) 100000
    ((solveEntry Ty.unit Ty.denote (xy, w, σd, n, gs)).subst ssImpl) with _ | ⟨a, tr'⟩
  · rw [he] at h
    cases h
  · rw [he] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    obtain ⟨rfl, rfl⟩ := Runs.unique ⟨_, he⟩ hr
    exact ⟨hok.isCorrect, hc⟩

/-! ### Kernel-evaluated runs -/

/-- The transposition of two points. -/
def swapD : PermData := (#[1, 0], #[1, 0])

/-- The answer of `runC2`: `(0 1)` times the trivial group, given by two identities. -/
def ansC2 : AnswerData Ty.unit := some (swapD, 2, [(#[0, 1], #[0, 1]), (#[0, 1], #[0, 1])], ())

/-- `⟨(0 1)⟩` on `01 ↦ 10`: the unique solution `(0 1)`. The block system is the two singletons;
the block kernel is trivial, with two cosets. -/
theorem runC2 : runLuks ((#[0, 1], #[1, 0]), WinData.ofPoints 2 [0, 1], PermData.one 2, 2,
    [swapD]) = some (ansC2, 12976) := by
  decide +kernel

example := runLuks_spec (by decide) (by decide) (by decide) (by decide) runC2

example : ∀ g, g ∈ Answer.denote (AnswerData.denote 2 ansC2) ↔
    GraphIsoChecks.Restriction.BruteIso 2 (WinData.ofPoints 2 [0, 1]) (PermData.one 2) [swapD]
      #[0, 1] #[1, 0] g := by
  intro g
  rw [ansC2, GraphIsoChecks.Sims.mem_denote_some (by decide)]
  revert g
  decide

/-! ### Maximal block systems -/

/-- Check `maxBlocks` against the expected block list. -/
def checkBlocks (name : String) (n : ℕ) (gs : GensData) (pts : List ℕ)
    (expected : List (List ℕ)) : IO Unit := do
  let bs := maxBlocks n gs pts
  unless bs == expected do throw <| IO.userError s!"{name}: blocks {bs}, expected {expected}"
  IO.println s!"{name}: maximal blocks {bs}"

/-- Generators of the iterated wreath product of `C₂` on `2 ^ k` points: at level `j`, swap the
two halves of the first block of size `2 ^ (j + 1)`. -/
def wrGens (k : ℕ) : GensData :=
  (List.range k).map fun j => ofCycles (2 ^ k) ((List.range (2 ^ j)).map fun i => [i, i + 2 ^ j])

#eval checkBlocks "C2 wr C2 wr C2" 8 (wrGens 3) (List.range 8) [[0, 1, 2, 3], [4, 5, 6, 7]]
#eval checkBlocks "S4" 4 (symGens 4) (List.range 4) [[0], [1], [2], [3]]
#eval checkBlocks "D4" 4 [ofCycles 4 [[0, 1, 2, 3]], ofCycles 4 [[1, 3]]] (List.range 4)
  [[0, 2], [1, 3]]
#eval checkBlocks "C6" 6 [cycleOf 6] (List.range 6) [[0, 2, 4], [1, 3, 5]]
#eval checkBlocks "S3 wr S2" 6 [ofCycles 6 [[0, 1]], ofCycles 6 [[0, 1, 2]],
  ofCycles 6 [[0, 3], [1, 4], [2, 5]]] (List.range 6) [[0, 1, 2], [3, 4, 5]]
#eval checkBlocks "C4 on 4..7" 8 [ofCycles 8 [[4, 5, 6, 7]]] [5, 4, 6, 7] [[5, 7], [4, 6]]
#eval checkBlocks "PSL(3,2)" 7 psl32Gens (List.range 7) [[0], [1], [2], [3], [4], [5], [6]]
#eval checkBlocks "S4 wr S3" 12 wreathGens (List.range 12)
  [[0, 1, 2, 3], [4, 5, 6, 7], [8, 9, 10, 11]]

/-! ### Comparisons with brute force -/

namespace Case

open GraphIsoChecks.Sweep

variable (c : Sweep.Case)

/-- Luks's strategy agrees with brute force, within `luksSimsCost` for `c = n`. -/
def luksOK : Bool :=
  match runLuks ((c.x.toArray, c.y.toArray), WinData.ofPoints c.n c.pts, ofList c.σ, c.n,
      c.gens.map ofList) with
  | some (a, cost) => answerOK c.n c.solutions a &&
      decide (cost ≤ luksSimsCost c.n c.gens.length c.pts.length c.n)
  | none => false

end Case

open GraphIsoChecks.Sweep

/-- The identity and the cycle `(0 1 … n−1)` as outer representatives. -/
def twoReps (n : ℕ) : List (List ℕ) :=
  if n ≤ 1 then [List.range n] else [List.range n, (List.range n).map fun i => (i + 1) % n]

#eval checkAll "Luks, degrees 1-3, binary strings"
  ([1, 2, 3].flatMap fun n => cases n (twoReps n) (binaryPairs n)) Case.luksOK
#eval checkAll "Luks, degree 3, distinct symbols" (cases 3 [[0, 1, 2]] distinctPairs) Case.luksOK
#eval checkAll "Luks, degree 4" (cases 4 [id4] pairs4) Case.luksOK

/- The groups of the degree 6–8 checks of `GraphIsoChecks/Sims.lean`, and `PSL(3, 2)`. -/
#eval checkAll "Luks, degrees 6 and 8"
  (bigCases 6 [[1, 0, 3, 2, 5, 4], [2, 3, 4, 5, 0, 1]]
      [([0, 0, 1, 1, 2, 2], [1, 1, 2, 2, 0, 0]), ([0, 1, 0, 1, 0, 1], [1, 0, 1, 0, 1, 0]),
        ([0, 0, 1, 1, 2, 2], [0, 1, 1, 2, 2, 0])] ++
    bigCases 6 [[1, 0, 2, 3, 4, 5], [1, 2, 0, 3, 4, 5], [0, 1, 2, 4, 3, 5], [0, 1, 2, 4, 5, 3]]
      [([0, 0, 1, 2, 2, 3], [1, 0, 0, 3, 2, 2]), ([0, 1, 2, 0, 1, 2], [2, 1, 0, 0, 2, 1])] ++
    bigCases 8 [[1, 2, 3, 4, 5, 6, 7, 0], [7, 6, 5, 4, 3, 2, 1, 0]]
      [([0, 0, 1, 1, 0, 0, 1, 1], [1, 1, 0, 0, 1, 1, 0, 0]),
        ([0, 1, 2, 3, 4, 5, 6, 7], [3, 2, 1, 0, 7, 6, 5, 4])])
  Case.luksOK
/- `PSL(3, 2)` is primitive: the blocks are points, and the block reduction branches over all
168 cosets of the trivial kernel. Distinct symbols: the unique solution is a 7-cycle. -/
#eval checkAll "Luks, PSL(3,2)"
  (bigCases 7 [[1, 2, 3, 4, 5, 6, 0], [0, 1, 6, 3, 5, 4, 2]]
    [([0, 1, 2, 3, 4, 5, 6], [1, 2, 3, 4, 5, 6, 0])])
  Case.luksOK

/-! ### `2`-groups -/

/-- The cost bound of `solve_luks_nilpotent`. -/
def nilBound (n L : ℕ) : ℕ := 6640 * (n + 1) ^ 8 + 60 * L * (n + 1) ^ 2

/-- An instance on the whole window, with the identity representative. -/
def wholeInst (n : ℕ) (gs : GensData) (x y : List ℕ) : Solver.Ty.input.denote :=
  ((x.toArray, y.toArray), WinData.ofPoints n (List.range n), PermData.one n, n, gs)

/-- Luks's strategy and the default strategy on a `2`-group, both against brute force; the Luks
cost within the nilpotent bound. -/
def checkTwoGroup (name : String) (n : ℕ) (gs : GensData) (x y : List ℕ) : IO Unit := do
  let c : Sweep.Case := ⟨n, gs.map img, List.range n, List.range n, x, y⟩
  match runLuks (wholeInst n gs x y), runSims (wholeInst n gs x y) with
  | some (a, cl), some (b, cd) =>
    unless answerOK n c.solutions a && answerOK n c.solutions b &&
        decide (cl ≤ nilBound n gs.length) do
      throw <| IO.userError s!"{name}: disagreement"
    IO.println s!"{name}: {c.solutions.length} solutions; Luks cost {cl} \
      (bound {nilBound n gs.length}), default cost {cd}"
  | _, _ => throw <| IO.userError s!"{name}: out of fuel"

#eval checkTwoGroup "C2 wr C2 wr C2, 8 points" 8 (wrGens 3) [0, 0, 1, 1, 0, 1, 0, 1]
  [1, 1, 0, 0, 1, 0, 1, 0]
#eval checkTwoGroup "C2 wr C2 wr C2, distinct symbols" 8 (wrGens 3) (List.range 8)
  [4, 5, 6, 7, 1, 0, 3, 2]

/-- The elements of the group of a complete table: one entry from each row, multiplied. -/
def tableElements (n : ℕ) (T : Table) : List (List ℕ) :=
  (List.range n).foldr (fun k acc => ((T.getD k #[]).toList.filterMap id).flatMap fun σ =>
    acc.map (Sweep.compose (img σ))) [List.range n]

/-- Luks's strategy on a large `2`-group, against the solutions found by enumerating the group
from a complete table: the representative is a solution, the answer's generators lie in the
group and fix `x`, and the answer's group has as many elements as there are solutions. So the
answer denotes exactly the solutions. -/
def checkLarge (name : String) (n : ℕ) (gs : GensData) (x y : List ℕ) : IO Unit := do
  let G := tableElements n (build n (Array.range n) gs).1
  let matchesL (g : List ℕ) (y : List ℕ) : Bool :=
    (List.range n).all fun u => x.getD u 0 == y.getD (g.getD u 0) 0
  let sols := G.filter fun g => matchesL g y
  match runLuks (wholeInst n gs x y) with
  | none => throw <| IO.userError s!"{name}: out of fuel"
  | some (a, cost) =>
    let ok := match a with
      | none => sols.isEmpty
      | some (τ, (m, hs, _)) =>
        m == n && PermData.validB n τ && GensData.allValidB n hs && sols.contains (img τ) &&
          hs.all (fun h => G.contains (img h) && matchesL (img h) x) &&
          order n (build n (Array.range n) hs).1 == sols.length
    unless ok && decide (cost ≤ nilBound n gs.length) do
      throw <| IO.userError s!"{name}: disagreement"
    IO.println s!"{name}: group of order {G.length}, {sols.length} solutions; Luks cost {cost} \
      (bound {nilBound n gs.length})"

#eval checkLarge "C2 wr C2 wr C2 wr C2, 16 points" 16 (wrGens 4) (List.range 16)
  ((List.range 16).map fun i => (i + 8) % 16)

end GraphIsoChecks.Luks
