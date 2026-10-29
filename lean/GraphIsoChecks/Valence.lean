module

public import GraphIsoChecks.GraphBrute
meta import GraphIsoChecks.GraphBrute
public import GraphIso.Solver.ValenceAll
meta import GraphIso.Solver.ValenceAll
import all Init.Data.Array.Basic
import all Init.Data.List.Sort.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Mathlib.Data.List.Sort

/-!
# Milestone 7 checks: graphs of maximum degree five

Runs of `gi5Checked` (connected graphs) and `gi5AllChecked` (all graphs), the checked entries
for maximum degree at most five, with the Schreier–Sims backend substituted, run inside
`luksSolver`. `runGI5_spec` and `runAll5_spec` tie every run to `gi5_checked` and
`gi5_all_checked`: the answer is correct and the cost within the closed-form bound.

* **Kernel-evaluated runs** on no points and one point (connected entry), and on no points
  (all-graphs entry).
* **Interpreter runs** (each `#eval` throws on a failure), compared with brute force over all
  `n!` permutations; a returned isomorphism is checked to be a bijection preserving adjacency.
  - connected entry: `P₃` against a relabelling; the star `K₁,₃` against a relabelling (a twin
    class of two points at level one); `K₃` against `P₃` (not isomorphic);
  - all-graphs entry: three isolated points; `K₂ ⊔ K₁` against a relabelling; `2K₂` against
    `P₄` (component sizes differ);
  - inputs rejected by the input checks: a vertex of degree six, a disconnected graph (connected
    entry only), a wrong number of lists, an asymmetric list, a loop.
* **A layer step with a twin class of three points.** A whole run on a graph with a vertex of
  degree four does not fit the interpreter: for the star `K₁,₄` the second layer is an
  instance on 73 points, and the interpreter keeps the full trace. The first layer step
  (`Valence.stepProg 5`) of `K₁,₄ ⊔ K₁,₄`, rooted at a centre and a leaf of each copy, is run
  on its own: its generators are checked to lie in `A₁`, and the order of the group they
  generate (from a Sims table) is compared with a brute-force count of `A₁` over the
  permutations of the levels. The order is `72 = 2³ · 3²`: the two root symmetries that map
  centres to centres, and `S₃ × S₃` on the two twin classes of three leaves.
-/

@[expose] public section

namespace GraphIsoChecks.Valence

open Equiv GraphIso GraphIso.Cost GraphIso.Sims GraphIso.Graph GraphIsoChecks.Graph

/-- Run the checked entry for connected graphs: the result and the charged cost. -/
def runGI5 (n : ℕ) (X Y : GraphData) : Option (Option (Option (Array ℕ)) × ℕ) :=
  (eval Ctx.empty.O (luksSolver.proc Ty.denote) 10000000000
    ((gi5Checked Ty.unit Ty.denote (n, X, Y)).subst ssImpl)).map
      fun r => (r.1, Trace.localCost r.2)

/-- A completed run is the run of `gi5_checked`: its result is correct and its cost is within
the closed-form bound. -/
theorem runGI5_spec {n : ℕ} {X Y : GraphData} {r : Option (Option (Array ℕ))} {c : ℕ}
    (h : runGI5 n X Y = some (r, c)) :
    c ≤ 28600 * (2 * n + 2) ^ 222 ∧ (r = none ↔ ¬ GIValid5 n X Y) ∧
      ∀ res, r = some res → GIAnswer n X Y res := by
  obtain ⟨r', tr, hr, hc, hnone, hsome⟩ := gi5_checked n X Y
  unfold runGI5 at h
  rcases he : eval Ctx.empty.O (luksSolver.proc Ty.denote) 10000000000
    ((gi5Checked Ty.unit Ty.denote (n, X, Y)).subst ssImpl) with _ | ⟨a, tr'⟩
  · rw [he] at h
    cases h
  · rw [he] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    obtain ⟨rfl, rfl⟩ := Runs.unique ⟨_, he⟩ hr
    exact ⟨hc, hnone, hsome⟩

/-- Run the checked entry for all graphs: the result and the charged cost. -/
def runAll5 (n : ℕ) (X Y : GraphData) : Option (Option (Option (Array ℕ)) × ℕ) :=
  (eval Ctx.empty.O (luksSolver.proc Ty.denote) 10000000000
    ((gi5AllChecked Ty.unit Ty.denote (n, X, Y)).subst ssImpl)).map
      fun r => (r.1, Trace.localCost r.2)

/-- A completed run is the run of `gi5_all_checked`: its result is correct and its cost is
within the closed-form bound. -/
theorem runAll5_spec {n : ℕ} {X Y : GraphData} {r : Option (Option (Array ℕ))} {c : ℕ}
    (h : runAll5 n X Y = some (r, c)) :
    c ≤ 7200 * (2 * n + 2) ^ 224 ∧ (r = none ↔ ¬ GIValidAll5 n X Y) ∧
      ∀ res, r = some res → GIAnswer n X Y res := by
  obtain ⟨r', tr, hr, hc, hnone, hsome⟩ := gi5_all_checked n X Y
  unfold runAll5 at h
  rcases he : eval Ctx.empty.O (luksSolver.proc Ty.denote) 10000000000
    ((gi5AllChecked Ty.unit Ty.denote (n, X, Y)).subst ssImpl) with _ | ⟨a, tr'⟩
  · rw [he] at h
    cases h
  · rw [he] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    obtain ⟨rfl, rfl⟩ := Runs.unique ⟨_, he⟩ hr
    exact ⟨hc, hnone, hsome⟩

/-! ### Kernel-evaluated runs -/

/-- No points: the empty map. -/
theorem runGI5_0 : runGI5 0 #[] #[] = some (some (some #[]), 80) := by
  decide +kernel

example : GIValid5 0 #[] #[] := by simpa using (runGI5_spec runGI5_0).2.1

/-- One point: the identity. -/
theorem runGI5_1 : runGI5 1 #[[]] #[[]] = some (some (some #[0]), 174) := by
  decide +kernel

example := runGI5_spec runGI5_1

/-- No points, all-graphs entry: the empty map. -/
theorem runAll5_0 : runAll5 0 #[] #[] = some (some (some #[]), 39) := by
  decide +kernel

example := runAll5_spec runAll5_0

/-! ### Brute force -/

/-- Compare a valid run's answer with brute force. -/
def checkAnswer (name : String) (n : ℕ) (X Y : GraphData) (res : Option (Array ℕ)) (c : ℕ) :
    IO Unit := do
  let iso := bruteIso n X Y
  match res with
  | none =>
    if iso then throw <| IO.userError s!"{name}: missed an isomorphism"
    IO.println s!"{name}: not isomorphic, as brute force; cost {c}"
  | some arr =>
    unless iso && isBijB n arr && isIsoB n X Y arr.toList do
      throw <| IO.userError s!"{name}: wrong isomorphism {arr}"
    IO.println s!"{name}: isomorphism {arr}, checked; cost {c}"

/-- Run the connected entry on valid connected data and compare with brute force. -/
def checkGI5 (name : String) (n : ℕ) (X Y : GraphData) : IO Unit := do
  let some (r, c) := runGI5 n X Y | throw <| IO.userError s!"{name}: out of fuel"
  let some res := r | throw <| IO.userError s!"{name}: valid input rejected"
  unless c ≤ 28600 * (2 * n + 2) ^ 222 do throw <| IO.userError s!"{name}: cost {c}"
  checkAnswer name n X Y res c

/-- Run the all-graphs entry on valid data and compare with brute force. -/
def checkAll5 (name : String) (n : ℕ) (X Y : GraphData) : IO Unit := do
  let some (r, c) := runAll5 n X Y | throw <| IO.userError s!"{name}: out of fuel"
  let some res := r | throw <| IO.userError s!"{name}: valid input rejected"
  unless c ≤ 7200 * (2 * n + 2) ^ 224 do throw <| IO.userError s!"{name}: cost {c}"
  checkAnswer name n X Y res c

/-- Run the connected entry on invalid data: it must be rejected. -/
def checkGI5Invalid (name : String) (n : ℕ) (X Y : GraphData) : IO Unit := do
  let some (r, c) := runGI5 n X Y | throw <| IO.userError s!"{name}: out of fuel"
  unless r = none do throw <| IO.userError s!"{name}: invalid input accepted"
  IO.println s!"{name}: rejected; cost {c}"

/-- Run the all-graphs entry on invalid data: it must be rejected. -/
def checkAll5Invalid (name : String) (n : ℕ) (X Y : GraphData) : IO Unit := do
  let some (r, c) := runAll5 n X Y | throw <| IO.userError s!"{name}: out of fuel"
  unless r = none do throw <| IO.userError s!"{name}: invalid input accepted"
  IO.println s!"{name}: rejected; cost {c}"

/-! ### Interpreter runs -/

#eval checkGI5 "P3 against a relabelling" 3 #[[1], [0, 2], [1]] #[[2], [2], [0, 1]]
#eval checkGI5 "K13 against a relabelling" 4 #[[1, 2, 3], [0], [0], [0]]
  #[[3], [3], [3], [0, 1, 2]]
#eval checkGI5 "K3 against P3" 3 #[[1, 2], [0, 2], [0, 1]] #[[1], [0, 2], [1]]

#eval checkAll5 "three isolated points" 3 #[[], [], []] #[[], [], []]
#eval checkAll5 "K2 + K1 against a relabelling" 3 #[[1], [0], []] #[[], [2], [1]]
#eval checkAll5 "2K2 against P4" 4 #[[1], [0], [3], [2]] #[[1], [0, 2], [1, 3], [2]]

#eval checkGI5Invalid "a vertex of degree six" 7
  #[[1, 2, 3, 4, 5, 6], [0], [0], [0], [0], [0], [0]]
  #[[1, 2, 3, 4, 5, 6], [0], [0], [0], [0], [0], [0]]
#eval checkGI5Invalid "a disconnected graph" 3 #[[1], [0], []] #[[1], [0], []]
#eval checkGI5Invalid "a wrong number of lists" 2 #[[1], [0]] #[[1], [0], []]
#eval checkGI5Invalid "an asymmetric list" 3 #[[1], [], [1]] #[[1], [0, 2], [1]]
#eval checkGI5Invalid "a loop" 3 #[[0, 1], [0], []] #[[1], [0], []]
#eval checkAll5Invalid "a vertex of degree six" 7
  #[[1, 2, 3, 4, 5, 6], [0], [0], [0], [0], [0], [0]]
  #[[1, 2, 3, 4, 5, 6], [0], [0], [0], [0], [0], [0]]

/-! ### A layer step with a twin class of three points -/

/-- The star `K₁,₄`, centred at `0`. -/
def star4 : GraphData := #[[1, 2, 3, 4], [0], [0], [0], [0]]

/-- The union of two stars, on ten points. -/
def star4Union : GraphData := GraphData.union 5 star4 star4

/-- The levels from the roots `0, 1` and `5, 6`: a centre and a leaf of each star. -/
def star4Lev : Array ℕ := levels 10 star4Union [0, 1, 5, 6]

/-- The first layer step. -/
def star4Step : Option (GensData × ℕ) :=
  (eval Ctx.empty.O (luksSolver.proc Ty.denote) 10000000000
    ((Valence.stepProg (var := Ty.denote) 5 (D := Ty.unit) 10 star4Union star4Lev 0
      (gens0Data 10 0 1 5 6)).subst ssImpl)).map fun r => (r.1, Trace.localCost r.2)

/-- An edge of the layered graph `Z_r`, as a test. -/
def edgeRB (G : GraphData) (lev : Array ℕ) (r u v : ℕ) : Bool :=
  adjB G u v && decide (get lev u ≤ r) && decide (get lev v ≤ r) &&
    (decide (get lev u < r) || decide (get lev v < r) || (get lev u == 0 && get lev v == 0))

/-- The map `f` of `0, …, N − 1` lies in `A_r`. -/
def autRB (N : ℕ) (G : GraphData) (lev : Array ℕ) (r : ℕ) (f : ℕ → ℕ) : Bool :=
  (List.range N).all (fun v =>
    (decide (get lev v ≤ r) || f v == v) && get lev (f v) == get lev v) &&
    (List.range N).all fun u => (List.range N).all fun v =>
      edgeRB G lev r (f u) (f v) == edgeRB G lev r u v

/-- The map placing `l₁` on `p₁` and `l₂` on `p₂`, the identity elsewhere. -/
def placeF (p₁ l₁ p₂ l₂ : List ℕ) (v : ℕ) : ℕ :=
  if v ∈ p₁ then l₁.getD (p₁.idxOf v) v else if v ∈ p₂ then l₂.getD (p₂.idxOf v) v else v

/-- `|A₁|` by brute force: permutations of level `0` and of level `1`, the rest fixed. -/
def star4BruteOrder : ℕ :=
  let l₀ := levList star4Lev 10 0
  let l₁ := levList star4Lev 10 1
  (l₀.permutations.flatMap fun q₀ => l₁.permutations.map fun q₁ => placeF l₀ q₀ l₁ q₁).countP
    fun f => autRB 10 star4Union star4Lev 1 f

#eval show IO Unit from do
  let some (gs, c) := star4Step | throw <| IO.userError "layer step: out of fuel"
  unless gs.all (fun g => g.validB 10 && autRB 10 star4Union star4Lev 1 (get g.1)) do
    throw <| IO.userError "layer step: a generator outside A₁"
  let ord := order 10 (build 10 (Array.range 10) gs).1
  unless ord == star4BruteOrder do
    throw <| IO.userError s!"layer step: order {ord}, brute force {star4BruteOrder}"
  unless ord.primeFactors = {2, 3} do throw <| IO.userError s!"layer step: order {ord}"
  IO.println s!"K14 layer step: {gs.length} generators of A₁, order {ord} = brute force; cost {c}"

end GraphIsoChecks.Valence
