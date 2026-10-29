module

public import GraphIso.Sims.Table

/-!
# Graphs given by adjacency lists

A graph on `{0, …, N − 1}` is an array of `N` adjacency lists (`GraphData`). It is valid of
maximum degree at most `Δ` (`GraphData.ValidD Δ N`) when the lists contain points below `N`,
without repetition, the relation is symmetric and irreflexive, and every list has at most `Δ`
entries. `GraphData.Valid N` is the case `Δ = 3` of milestones 4 and 5.

`GraphData.union n X Y` is the disjoint union of two graphs on `n` points: `X` on
`0, …, n − 1` and `Y` shifted to `n, …, 2n − 1`.

The levels of a graph from a set of roots are computed by relaxation to a fixpoint
(`levels`): every root starts at `0`, every other point at `N`, and each pass lowers the level
of each point to one more than the least level of its neighbours.
-/

@[expose] public section

namespace GraphIso.Graph

open Equiv

/-- Adjacency lists. -/
abbrev GraphData := Array (List ℕ)

/-- The neighbours of `u`. -/
def nbrs (G : GraphData) (u : ℕ) : List ℕ := G.getD u []

/-- `u` and `v` are adjacent. -/
def Adj (G : GraphData) (u v : ℕ) : Prop := v ∈ nbrs G u

instance (G : GraphData) (u v : ℕ) : Decidable (Adj G u v) :=
  inferInstanceAs (Decidable (v ∈ nbrs G u))

/-- Valid graph data on `N` points, of maximum degree at most `Δ`. -/
structure GraphData.ValidD (Δ N : ℕ) (G : GraphData) : Prop where
  size : G.size = N
  lt : ∀ u v, Adj G u v → v < N
  nodup : ∀ u, (nbrs G u).Nodup
  symm : ∀ u v, Adj G u v → Adj G v u
  irrefl : ∀ u, ¬ Adj G u u
  deg : ∀ u, (nbrs G u).length ≤ Δ

/-- Valid graph data on `N` points, of maximum degree at most three. -/
abbrev GraphData.Valid (N : ℕ) (G : GraphData) : Prop := G.ValidD 3 N

theorem nbrs_of_ge {G : GraphData} {u : ℕ} (h : G.size ≤ u) : nbrs G u = [] := by
  simp [nbrs, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none h]

theorem GraphData.ValidD.lt_left {Δ N : ℕ} {G : GraphData} (hG : G.ValidD Δ N) {u v : ℕ}
    (h : Adj G u v) : u < N :=
  hG.lt v u (hG.symm u v h)

/-- A degree bound can be raised. -/
theorem GraphData.ValidD.mono {Δ Δ' N : ℕ} {G : GraphData} (hG : G.ValidD Δ N) (h : Δ ≤ Δ') :
    G.ValidD Δ' N :=
  ⟨hG.size, hG.lt, hG.nodup, hG.symm, hG.irrefl, fun u => (hG.deg u).trans h⟩

/-! ### Disjoint unions -/

/-- The disjoint union: `X` on `0, …, n − 1` and `Y` shifted by `n`. -/
def GraphData.union (n : ℕ) (X Y : GraphData) : GraphData :=
  X ++ Y.map (·.map (· + n))

theorem nbrs_union_lt {n : ℕ} {X Y : GraphData} (hX : X.size = n) {u : ℕ} (hu : u < n) :
    nbrs (GraphData.union n X Y) u = nbrs X u := by
  simp [nbrs, GraphData.union, Array.getD_eq_getD_getElem?, Array.getElem?_append, hX, hu]

theorem nbrs_union_ge {n : ℕ} {X Y : GraphData} (hX : X.size = n) {u : ℕ} (hu : n ≤ u) :
    nbrs (GraphData.union n X Y) u = (nbrs Y (u - n)).map (· + n) := by
  simp only [nbrs, GraphData.union, Array.getD_eq_getD_getElem?, Array.getElem?_append, hX,
    show ¬ u < n by omega, Array.getElem?_map]
  rcases Y[u - n]? with _ | l <;> simp

theorem size_union (n : ℕ) (X Y : GraphData) :
    (GraphData.union n X Y).size = X.size + Y.size := by
  simp [GraphData.union]

end GraphIso.Graph
