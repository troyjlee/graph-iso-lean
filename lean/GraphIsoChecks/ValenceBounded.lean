module

public import GraphIsoChecks.Valence
meta import GraphIsoChecks.Valence
public import GraphIso.Solver.ValenceBounded
meta import GraphIso.Solver.ValenceBounded
import all Init.Data.Array.Basic
import all Init.Data.List.Sort.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Mathlib.Data.List.Sort

/-!
# Milestone 9 checks: graphs of every bounded valence

Runs of `giBoundedChecked 6` (connected graphs) and `giBoundedAllChecked 6` (all graphs), the
checked entries for maximum degree at most six, with the Schreier–Sims backend substituted, run
inside `luksSolver`. `runGIB_spec` and `runAllB_spec` tie every run to `gi_bounded_checked` and
`gi_bounded_all_checked` (for `Δ = 6` and `k = 5! = 120`): the answer is correct and the cost
within the closed-form bound.

* **Kernel-evaluated runs** on no points and one point (connected entry), and on no points
  (all-graphs entry).
* **Interpreter runs** (each `#eval` throws on a failure), compared with brute force over all
  `n!` permutations; a returned isomorphism is checked to be a bijection preserving adjacency.
  The closed-form bound has an exponent of about `9.4 · 10⁷`, too large to evaluate; the runs
  check the cost against `8100 Δ (2n + 2)^{44 Δ + 2}` (resp. `2300 Δ (2n + 2)^{44 Δ + 4}`),
  which is smaller since `9k³ + 9k² + 36k + 8 ≥ 44`.
  - connected entry: `P₃` against a relabelling;
  - all-graphs entry: three isolated points; `2K₂` against `P₄` (component sizes differ);
  - inputs rejected by the input checks: a vertex of degree seven (both entries).
* **A layer step whose group is not a `{2, 3}`-group.** For maximum degree six a twin class can
  have five points. The first layer step (`Valence.stepProg 6`) of two stars `K₁,₆`, rooted at
  a centre and a leaf of each, is run on its own: its generators are checked to lie in `A₁`,
  and the group they generate has order `28800 = 2 · (5!)²` (from a Sims table): the root
  symmetry exchanging the stars, and `S₅ × S₅` on the two twin classes of five leaves. So `5`
  divides `|A₁|`, and milestone 7's solvable `{2, 3}` bound does not apply; milestone 8's does
  (`Valence.boundedSections_autR` with `k = 120`). A whole run on `K₁,₆` does not fit the
  interpreter (its second layer has `848` subsets).
-/

@[expose] public section

namespace GraphIsoChecks.ValenceBounded

open Equiv GraphIso GraphIso.Cost GraphIso.Sims GraphIso.Graph GraphIsoChecks.Graph
  GraphIsoChecks.Valence

/-- Run the checked entry for connected graphs of maximum degree `Δ`: the result and the charged
cost. -/
def runGIB (Δ n : ℕ) (X Y : GraphData) : Option (Option (Option (Array ℕ)) × ℕ) :=
  (eval Ctx.empty.O (luksSolver.proc Ty.denote) 10000000000
    ((giBoundedChecked Δ Ty.unit Ty.denote (n, X, Y)).subst ssImpl)).map
      fun r => (r.1, Trace.localCost r.2)

/-- A completed run is the run of `gi_bounded_checked`: its result is correct and its cost is
within the closed-form bound, for every `k ≥ 2` with `(Δ − 1)! ≤ k`. -/
theorem runGIB_spec {Δ k n : ℕ} (hΔ : 2 ≤ Δ) (hk2 : 2 ≤ k) (hk : (Δ - 1).factorial ≤ k)
    {X Y : GraphData} {r : Option (Option (Array ℕ))} {c : ℕ} (h : runGIB Δ n X Y = some (r, c)) :
    c ≤ 8100 * Δ * (2 * n + 2) ^ (Δ * (9 * k ^ 3 + 9 * k ^ 2 + 36 * k + 8) + 2) ∧
      (r = none ↔ ¬ GIValidB Δ n X Y) ∧ ∀ res, r = some res → GIAnswer n X Y res := by
  obtain ⟨r', tr, hr, hc, hnone, hsome⟩ := gi_bounded_checked hΔ hk2 hk n X Y
  unfold runGIB at h
  rcases he : eval Ctx.empty.O (luksSolver.proc Ty.denote) 10000000000
    ((giBoundedChecked Δ Ty.unit Ty.denote (n, X, Y)).subst ssImpl) with _ | ⟨a, tr'⟩
  · rw [he] at h
    cases h
  · rw [he] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    obtain ⟨rfl, rfl⟩ := Runs.unique ⟨_, he⟩ hr
    exact ⟨hc, hnone, hsome⟩

/-- Run the checked entry for all graphs of maximum degree `Δ`: the result and the charged
cost. -/
def runAllB (Δ n : ℕ) (X Y : GraphData) : Option (Option (Option (Array ℕ)) × ℕ) :=
  (eval Ctx.empty.O (luksSolver.proc Ty.denote) 10000000000
    ((giBoundedAllChecked Δ Ty.unit Ty.denote (n, X, Y)).subst ssImpl)).map
      fun r => (r.1, Trace.localCost r.2)

/-- A completed run is the run of `gi_bounded_all_checked`: its result is correct and its cost
is within the closed-form bound, for every `k ≥ 2` with `(Δ − 1)! ≤ k`. -/
theorem runAllB_spec {Δ k n : ℕ} (hΔ : 2 ≤ Δ) (hk2 : 2 ≤ k) (hk : (Δ - 1).factorial ≤ k)
    {X Y : GraphData} {r : Option (Option (Array ℕ))} {c : ℕ}
    (h : runAllB Δ n X Y = some (r, c)) :
    c ≤ 2300 * Δ * (2 * n + 2) ^ (Δ * (9 * k ^ 3 + 9 * k ^ 2 + 36 * k + 8) + 4) ∧
      (r = none ↔ ¬ GIValidAllB Δ n X Y) ∧ ∀ res, r = some res → GIAnswer n X Y res := by
  obtain ⟨r', tr, hr, hc, hnone, hsome⟩ := gi_bounded_all_checked hΔ hk2 hk n X Y
  unfold runAllB at h
  rcases he : eval Ctx.empty.O (luksSolver.proc Ty.denote) 10000000000
    ((giBoundedAllChecked Δ Ty.unit Ty.denote (n, X, Y)).subst ssImpl) with _ | ⟨a, tr'⟩
  · rw [he] at h
    cases h
  · rw [he] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    obtain ⟨rfl, rfl⟩ := Runs.unique ⟨_, he⟩ hr
    exact ⟨hc, hnone, hsome⟩

/-- `(6 − 1)! = 120`. -/
theorem factorial_five : (6 - 1).factorial ≤ 120 := by decide

/-! ### Kernel-evaluated runs -/

/-- No points: the empty map. -/
theorem runGIB_0 : runGIB 6 0 #[] #[] = some (some (some #[]), 80) := by
  decide +kernel

example : GIValidB 6 0 #[] #[] := by
  simpa using (runGIB_spec (by norm_num) (by norm_num) factorial_five runGIB_0).2.1

/-- One point: the identity. -/
theorem runGIB_1 : runGIB 6 1 #[[]] #[[]] = some (some (some #[0]), 174) := by
  decide +kernel

example := runGIB_spec (by norm_num) (by norm_num) factorial_five runGIB_1

/-- No points, all-graphs entry. -/
theorem runAllB_0 : runAllB 6 0 #[] #[] = some (some (some #[]), 39) := by
  decide +kernel

example := runAllB_spec (by norm_num) (by norm_num) factorial_five runAllB_0

/-! ### Interpreter runs -/

/-- Run the connected entry for `Δ = 6` on valid connected data and compare with brute force;
the cost is checked against `8100 · 6 · (2n + 2)^{266}`, below the closed-form bound. -/
def checkGIB (name : String) (n : ℕ) (X Y : GraphData) : IO Unit := do
  let some (r, c) := runGIB 6 n X Y | throw <| IO.userError s!"{name}: out of fuel"
  let some res := r | throw <| IO.userError s!"{name}: valid input rejected"
  unless c ≤ 8100 * 6 * (2 * n + 2) ^ (44 * 6 + 2) do
    throw <| IO.userError s!"{name}: cost {c}"
  checkAnswer name n X Y res c

/-- Run the all-graphs entry for `Δ = 6` on valid data and compare with brute force; the cost is
checked against `2300 · 6 · (2n + 2)^{268}`, below the closed-form bound. -/
def checkAllB (name : String) (n : ℕ) (X Y : GraphData) : IO Unit := do
  let some (r, c) := runAllB 6 n X Y | throw <| IO.userError s!"{name}: out of fuel"
  let some res := r | throw <| IO.userError s!"{name}: valid input rejected"
  unless c ≤ 2300 * 6 * (2 * n + 2) ^ (44 * 6 + 4) do
    throw <| IO.userError s!"{name}: cost {c}"
  checkAnswer name n X Y res c

/-- Run both entries for `Δ = 6` on invalid data: both must reject it. -/
def checkInvalidB (name : String) (n : ℕ) (X Y : GraphData) : IO Unit := do
  let some (r, c) := runGIB 6 n X Y | throw <| IO.userError s!"{name}: out of fuel"
  unless r = none do throw <| IO.userError s!"{name}: invalid input accepted"
  let some (r', c') := runAllB 6 n X Y | throw <| IO.userError s!"{name}: out of fuel"
  unless r' = none do throw <| IO.userError s!"{name}: invalid input accepted (all graphs)"
  IO.println s!"{name}: rejected by both entries; costs {c}, {c'}"

#eval checkGIB "P3 against a relabelling" 3 #[[1], [0, 2], [1]] #[[2], [2], [0, 1]]

#eval checkAllB "three isolated points" 3 #[[], [], []] #[[], [], []]
#eval checkAllB "2K2 against P4" 4 #[[1], [0], [3], [2]] #[[1], [0, 2], [1, 3], [2]]

#eval checkInvalidB "a vertex of degree seven" 8
  #[[1, 2, 3, 4, 5, 6, 7], [0], [0], [0], [0], [0], [0], [0]]
  #[[1, 2, 3, 4, 5, 6, 7], [0], [0], [0], [0], [0], [0], [0]]

/-! ### A layer step with a twin class of five points -/

/-- The star `K₁,₆`, centred at `0`. -/
def star6 : GraphData := #[[1, 2, 3, 4, 5, 6], [0], [0], [0], [0], [0], [0]]

/-- The union of two stars, on fourteen points. -/
def star6Union : GraphData := GraphData.union 7 star6 star6

/-- The levels from the roots `0, 1` and `7, 8`: a centre and a leaf of each star. -/
def star6Lev : Array ℕ := levels 14 star6Union [0, 1, 7, 8]

/-- The first layer step. -/
def star6Step : Option (GensData × ℕ) :=
  (eval Ctx.empty.O (luksSolver.proc Ty.denote) 10000000000
    ((Valence.stepProg (var := Ty.denote) 6 (D := Ty.unit) 14 star6Union star6Lev 0
      (gens0Data 14 0 1 7 8)).subst ssImpl)).map fun r => (r.1, Trace.localCost r.2)

#eval show IO Unit from do
  let some (gs, c) := star6Step | throw <| IO.userError "layer step: out of fuel"
  unless gs.all (fun g => g.validB 14 && autRB 14 star6Union star6Lev 1 (get g.1)) do
    throw <| IO.userError "layer step: a generator outside A₁"
  let ord := order 14 (build 14 (Array.range 14) gs).1
  unless ord == 2 * Nat.factorial 5 * Nat.factorial 5 do
    throw <| IO.userError s!"layer step: order {ord}"
  unless ord.primeFactors = {2, 3, 5} do throw <| IO.userError s!"layer step: order {ord}"
  IO.println s!"K16 layer step: {gs.length} generators of A₁, order {ord} = 2 · 5! · 5!; cost {c}"

end GraphIsoChecks.ValenceBounded
