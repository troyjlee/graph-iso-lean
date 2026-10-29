module

public import GraphIso.Solver.Coherent
meta import GraphIso.Solver.Coherent
import all Init.Data.Array.Basic
import all Init.Data.List.Sort.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Mathlib.Data.List.Sort

/-!
# Milestone 10 checks: Weisfeiler–Leman and the Design Lemma

Runs of `wlChecked` (the `k`-ary Weisfeiler–Leman refinement) and `descentChecked` (the
refinement followed by the Design Lemma search), over the empty backend. `runWL_spec` and
`runDescent_spec` tie every completed run to `wl_checked` and `descent_checked`: the result is
the refinement of the input (respectively satisfies the descent guarantees) and the cost is
within the closed-form bound.

* **Kernel-evaluated runs**: the refinement of a constant colouring of the `1`-tuples of two
  points and of the pairs of one point; the descent on one point.
* **Interpreter runs** (each `#eval` throws on a failure):
  - refinements (`k = 2`) of graphs, given as the colouring `(x, y) ↦ [x ~ y]`: `P₃`, the cycle
    `C₅` and `C₆`, and two triangles `2K₃`. Each output is checked to be a coherent
    configuration by brute force over all pairs of tuples (`coherentB`), to refine the input,
    and to be canonical: the refinement of a relabelled input is the relabelled refinement,
    with the same colour list. `C₆` and `2K₃` (both `2`-regular, not separated by colour
    refinement on the vertices) get refinements with different numbers of colours;
  - a refinement with `k = 3`: the ternary structure of `P₃` (`(x, y, z) ↦ [x ~ y]`), checked
    in the same way;
  - descents: outcome (a) on a colouring of four points in two classes of two (`t = 2`), at the
    empty list; outcome (b) on `C₅` (`t = 3`), whose vertices form one class and whose
    2-skeleton is not a clique; `some none` on `K₄` (`t = 2`), whose four points are pairwise
    twins; and inputs rejected by the input checks (`k = 1`, `2t < m`, a wrong array size).
-/

@[expose] public section

namespace GraphIsoChecks.Coherent

open GraphIso GraphIso.Cost GraphIso.Coherent

/-! ### Runs and their specifications -/

/-- Run the checked refinement: the result and the charged cost. -/
def runWL (k m : ℕ) (col : Array ℕ) : Option (Option (Array ℕ × List ℕ) × ℕ) :=
  (eval Ctx.empty.O (wlChecked Ty.denote) 100000000000 (wlChecked Ty.denote (k, m, col))).map
    fun r => (r.1, Trace.localCost r.2)

/-- A completed run is the run of `wl_checked`. -/
theorem runWL_spec {k m : ℕ} {col : Array ℕ} {r : Option (Array ℕ × List ℕ)} {c : ℕ}
    (h : runWL k m col = some (r, c)) :
    c ≤ 720 * (m ^ k + 1) ^ 3 * ((m + 2) * (k + 2)) ^ 2 * (k ^ k + 1) ∧
      (r = none ↔ col.size ≠ m ^ k) ∧
      ∀ res, r = some res → res.1.size = m ^ k ∧ toFun res.1 = (wl k m (toFun col)).1 ∧
        res.2 = (wl k m (toFun col)).2 := by
  obtain ⟨r', tr, hr, hc, hnone, hsome⟩ := wl_checked k m col
  unfold runWL at h
  rcases he : eval Ctx.empty.O (wlChecked Ty.denote) 100000000000
    (wlChecked Ty.denote (k, m, col)) with _ | ⟨a, tr'⟩
  · rw [he] at h
    cases h
  · rw [he] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    obtain ⟨rfl, rfl⟩ := Runs.unique ⟨_, he⟩ hr
    exact ⟨hc, hnone, hsome⟩

/-- Run the checked descent: the result and the charged cost. -/
def runDescent (k m t : ℕ) (col : Array ℕ) :
    Option (Option (Option (List ℕ × Array ℕ)) × ℕ) :=
  (eval Ctx.empty.O (descentChecked Ty.denote) 100000000000
    (descentChecked Ty.denote (k, m, t, col))).map fun r => (r.1, Trace.localCost r.2)

/-- A completed run is the run of `descent_checked`. -/
theorem runDescent_spec {k m t : ℕ} {col : Array ℕ} {r : Option (Option (List ℕ × Array ℕ))}
    {c : ℕ} (h : runDescent k m t col = some (r, c)) :
    c ≤ 1000 * (m ^ k + 1) ^ 3 * ((m + 2) * (k + 2)) ^ 2 * (k ^ k + 1) ∧
      (r = none ↔ ¬ (2 ≤ k ∧ m ≤ 2 * t ∧ col.size = m ^ k)) ∧
      (r = some none → ∃ T : Finset (Fin m), t < T.card ∧
        ∀ u ∈ T, ∀ v ∈ T, IsTwin (toFun (k := k) col) u v) ∧
      ∀ xd col₁, r = some (some (xd, col₁)) → ∃ x : List (Fin m), xd = x.map Fin.val ∧
        x.length < k ∧
        col₁ = ((List.finRange m).map fun u => skel1 (wl k m (toFun col)).1 x u).toArray ∧
        DesignGood (wl k m (toFun col)).1 t x := by
  obtain ⟨r', tr, hr, hc, hnone, htw, hsome⟩ := descent_checked k m t col
  unfold runDescent at h
  rcases he : eval Ctx.empty.O (descentChecked Ty.denote) 100000000000
    (descentChecked Ty.denote (k, m, t, col)) with _ | ⟨a, tr'⟩
  · rw [he] at h
    cases h
  · rw [he] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    obtain ⟨rfl, rfl⟩ := Runs.unique ⟨_, he⟩ hr
    exact ⟨hc, hnone, htw, hsome⟩

/-! ### Kernel-evaluated runs -/

/-- The `1`-tuples of two points, one colour: the refinement keeps one colour. -/
theorem runWL_one_two : runWL 1 2 #[5, 5] = some (some (#[0, 0], [5]), 1195) := by
  decide +kernel

example := runWL_spec runWL_one_two

/-- The pairs of one point. -/
theorem runWL_two_one : runWL 2 1 #[7] = some (some (#[0], [7]), 746) := by
  decide +kernel

example := runWL_spec runWL_two_one

/-- The descent on one point: outcome (a) at the empty list. -/
theorem runDescent_one : runDescent 2 1 1 #[0] = some (some (some ([], #[0])), 894) := by
  decide +kernel

example := runDescent_spec runDescent_one

/-! ### Brute-force checks -/

/-- The code of a digit list, position `0` first. -/
def codeOf (m : ℕ) (d : List ℕ) : ℕ := d.foldr (fun x acc => x + m * acc) 0

/-- The digits of every code, in order. -/
def allTuples (k m : ℕ) : List (List ℕ) := tupList k m

/-- The colour of a digit list. -/
def colAt (m : ℕ) (col : Array ℕ) (d : List ℕ) : ℕ := get col (codeOf m d)

/-- The sorted vectors of the colours with one position replaced, over all points. -/
def vecsOf (k m : ℕ) (col : Array ℕ) (d : List ℕ) : List (List ℕ) :=
  ((List.range m).map fun z => (List.range k).map fun j => colAt m col (d.set j z)).insertionSort
    (· ≤ ·)

/-- The equality pattern of a digit list. -/
def patOf (k : ℕ) (d : List ℕ) : List Bool :=
  (List.range k).flatMap fun i => (List.range k).map fun j => d.getD i 0 == d.getD j 0

/-- The colours of the rearrangements of a digit list. -/
def monoOf (k m : ℕ) (col : Array ℕ) (d : List ℕ) : List ℕ :=
  (tupList k k).map fun τ => colAt m col (τ.map fun i => d.getD i 0)

/-- **Coherence by brute force**: tuples of equal colour have equal patterns, equal colours of
all rearrangements and equal multisets of vectors. -/
def coherentB (k m : ℕ) (col : Array ℕ) : Bool :=
  (allTuples k m).all fun d => (allTuples k m).all fun e =>
    colAt m col d != colAt m col e ||
      (patOf k d == patOf k e && monoOf k m col d == monoOf k m col e &&
        vecsOf k m col d == vecsOf k m col e)

/-- The output refines the input. -/
def refinesB (k m : ℕ) (out col : Array ℕ) : Bool :=
  (allTuples k m).all fun d => (allTuples k m).all fun e =>
    colAt m out d != colAt m out e || colAt m col d == colAt m col e

/-- Relabel an array of colours by the permutation `π` of the points (given as a list). -/
def relabel (k m : ℕ) (π : List ℕ) (col : Array ℕ) : Array ℕ :=
  let ws := (allTuples k m).map fun d => (codeOf m (d.map fun i => π.getD i 0), colAt m col d)
  Prim.applyWrites (a := .nat) (Array.replicate (m ^ k) 0) ws

/-- The colouring `(x, y) ↦ [x ~ y]` of the pairs of a graph on `m` points. -/
def graphCol (m : ℕ) (adj : ℕ → ℕ → Bool) : Array ℕ :=
  ((tupList 2 m).map fun d => if adj (d.getD 0 0) (d.getD 1 0) then 1 else 0).toArray

/-- The sizes of the colour classes, sorted. -/
def classSizes (col : Array ℕ) : List ℕ :=
  ((col.toList.dedup).map fun a => col.toList.count a).insertionSort (· ≤ ·)

/-- Refine, and check coherence, refinement, the cost bound and canonicity under `π`. -/
def checkWL (name : String) (k m : ℕ) (col : Array ℕ) (π : List ℕ) : IO (Array ℕ × List ℕ) := do
  let some (some (out, orig), c) := runWL k m col | throw <| IO.userError s!"{name}: no result"
  unless coherentB k m out do throw <| IO.userError s!"{name}: not coherent"
  unless refinesB k m out col do throw <| IO.userError s!"{name}: does not refine"
  unless c ≤ 720 * (m ^ k + 1) ^ 3 * ((m + 2) * (k + 2)) ^ 2 * (k ^ k + 1) do
    throw <| IO.userError s!"{name}: cost {c}"
  let some (some (out', orig'), _) := runWL k m (relabel k m π col)
    | throw <| IO.userError s!"{name}: no result (relabelled)"
  unless out' == relabel k m π out && orig' == orig do
    throw <| IO.userError s!"{name}: not canonical"
  IO.println s!"{name}: {orig.length} colours, class sizes {classSizes out}, cost {c}"
  return (out, orig)

/-! ### Interpreter runs: the refinement -/

/-- The adjacency of the path `0 – 1 – 2`. -/
def p3 (x y : ℕ) : Bool := (x + 1 == y) || (y + 1 == x)

/-- The adjacency of the cycle on `n` points. -/
def cyc (n x y : ℕ) : Bool := x != y && ((x + 1) % n == y || (y + 1) % n == x)

/-- The adjacency of two triangles `{0, 1, 2}` and `{3, 4, 5}`. -/
def twoK3 (x y : ℕ) : Bool := x != y && x / 3 == y / 3

#eval do let _ ← checkWL "P3" 2 3 (graphCol 3 p3) [2, 0, 1]
#eval do let _ ← checkWL "C5" 2 5 (graphCol 5 (cyc 5)) [3, 1, 4, 0, 2]

#eval show IO Unit from do
  let (c6, _) ← checkWL "C6" 2 6 (graphCol 6 (cyc 6)) [5, 3, 1, 0, 2, 4]
  let (k3, _) ← checkWL "2K3" 2 6 (graphCol 6 twoK3) [4, 0, 5, 1, 3, 2]
  unless classSizes c6 != classSizes k3 do throw <| IO.userError "C6 and 2K3 not separated"
  IO.println "C6 and 2K3 separated"

/-- The ternary structure `(x, y, z) ↦ [x ~ y]` of `P₃`. -/
def p3ternary : Array ℕ :=
  ((tupList 3 3).map fun d => if p3 (d.getD 0 0) (d.getD 1 0) then 1 else 0).toArray

#eval do let _ ← checkWL "P3, k = 3" 3 3 p3ternary [1, 2, 0]

/-! ### Interpreter runs: the descent -/

/-- Run the descent and check the cost bound; return the outcome. -/
def checkDescent (name : String) (k m t : ℕ) (col : Array ℕ) :
    IO (Option (Option (List ℕ × Array ℕ))) := do
  let some (r, c) := runDescent k m t col | throw <| IO.userError s!"{name}: out of fuel"
  unless c ≤ 1000 * (m ^ k + 1) ^ 3 * ((m + 2) * (k + 2)) ^ 2 * (k ^ k + 1) do
    throw <| IO.userError s!"{name}: cost {c}"
  IO.println s!"{name}: {r}, cost {c}"
  return r

/-- Four points in two vertex classes of two. -/
def twoClasses : Array ℕ :=
  ((tupList 2 4).map fun d => if d.getD 0 0 == d.getD 1 0 then d.getD 0 0 / 2 else 7).toArray

#eval show IO Unit from do
  let r ← checkDescent "two classes of two (t = 2)" 2 4 2 twoClasses
  unless r == some (some ([], #[0, 0, 1, 1])) do throw <| IO.userError "expected outcome (a)"

#eval show IO Unit from do
  let r ← checkDescent "C5 (t = 3)" 2 5 3 (graphCol 5 (cyc 5))
  let some (some (xd, col₁)) := r | throw <| IO.userError "expected a list"
  unless xd == [] && (col₁.toList.dedup.length == 1) do
    throw <| IO.userError "expected outcome (b) at the empty list"

/-- The complete graph on four points. -/
def k4 (x y : ℕ) : Bool := x != y

#eval show IO Unit from do
  let r ← checkDescent "K4 (t = 2)" 2 4 2 (graphCol 4 k4)
  unless r == some none do throw <| IO.userError "expected a large twin class"

#eval show IO Unit from do
  let r₁ ← checkDescent "k = 1" 1 4 2 #[0, 0, 0, 0]
  let r₂ ← checkDescent "2t < m" 2 4 1 (graphCol 4 k4)
  let r₃ ← checkDescent "wrong size" 2 4 2 #[0, 0, 0]
  unless r₁ == none && r₂ == none && r₃ == none do
    throw <| IO.userError "invalid input accepted"

end GraphIsoChecks.Coherent
