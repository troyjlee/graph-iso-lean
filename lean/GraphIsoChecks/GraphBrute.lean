module

public import GraphIso.Graph.StepModel

/-!
# Brute-force isomorphism tests for the graph checks

Used by `GraphIsoChecks/Graph.lean` and `GraphIsoChecks/GraphAll.lean`.
-/

@[expose] public section

namespace GraphIsoChecks.Graph

open GraphIso.Graph

/-- `f` preserves adjacency from `X` to `Y` on `n` points. -/
def isIsoB (n : ℕ) (X Y : GraphData) (f : List ℕ) : Bool :=
  (List.range n).all fun u => (List.range n).all fun v =>
    adjB Y (f.getD u 0) (f.getD v 0) == adjB X u v

/-- Some permutation of `0, …, n − 1` is an isomorphism. -/
def bruteIso (n : ℕ) (X Y : GraphData) : Bool := (List.range n).permutations.any (isIsoB n X Y)

/-- `arr` lists a bijection of `0, …, n − 1`. -/
def isBijB (n : ℕ) (arr : Array ℕ) : Bool :=
  arr.size == n && (List.range n).all fun v => arr.toList.contains v

end GraphIsoChecks.Graph
