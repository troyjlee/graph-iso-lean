module

public import GraphIso.Graph.Validate
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Graph data as mathlib simple graphs

`GraphData.toSimpleGraph n G` is the simple graph on `Fin n` whose adjacency is `Adj G`
(symmetrized, without loops). For valid data:

* `toSimpleGraph_adj`: its adjacency is `Adj G`;
* `nonempty_iso_iff`: the simple graphs are isomorphic exactly when some `φ` satisfies
  `IsIso n X Y φ`, and every such `φ` is a simple-graph isomorphism (`isIso_iff`);
* `conn_iff_connected`: for `n > 0`, the connectivity `Conn n G` read by the algorithm is
  `SimpleGraph.Connected`.

Conversely, `GraphData.ofSimpleGraph H` lists the neighbours of a simple graph on `Fin n`; its
simple graph is `H` (`toSimpleGraph_ofSimpleGraph`), and it is valid of maximum degree `Δ` when
every degree is at most `Δ` (`valid_ofSimpleGraph`).
-/

@[expose] public section

namespace GraphIso.Graph

open Equiv Sims

/-- The simple graph of graph data on `n` points. -/
def GraphData.toSimpleGraph (n : ℕ) (G : GraphData) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun u v => Adj G u v

variable {Δ n : ℕ} {G X Y : GraphData}

theorem toSimpleGraph_adj (hG : G.ValidD Δ n) (u v : Fin n) :
    (G.toSimpleGraph n).Adj u v ↔ Adj G u v := by
  rw [GraphData.toSimpleGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨-, h | h⟩
    · exact h
    · exact hG.symm _ _ h
  · intro h
    refine ⟨fun e => ?_, Or.inl h⟩
    subst e
    exact hG.irrefl _ h

/-- The isomorphisms of the data are the isomorphisms of the simple graphs. -/
theorem isIso_iff (hX : X.ValidD Δ n) (hY : Y.ValidD Δ n) (φ : Perm (Fin n)) :
    IsIso n X Y φ ↔ ∀ u v : Fin n,
      ((Y.toSimpleGraph n).Adj (φ u) (φ v) ↔ (X.toSimpleGraph n).Adj u v) := by
  simp only [toSimpleGraph_adj hX, toSimpleGraph_adj hY]
  constructor
  · intro h u v
    have := h u v u.2 v.2
    rwa [act_of_lt _ u.2, act_of_lt _ v.2] at this
  · intro h u v hu hv
    have := h ⟨u, hu⟩ ⟨v, hv⟩
    rwa [act_of_lt _ hu, act_of_lt _ hv]

/-- The simple-graph isomorphism of an isomorphism of the data. -/
def isoOfIsIso (hX : X.ValidD Δ n) (hY : Y.ValidD Δ n) {φ : Perm (Fin n)} (h : IsIso n X Y φ) :
    X.toSimpleGraph n ≃g Y.toSimpleGraph n where
  toEquiv := φ
  map_rel_iff' := (isIso_iff hX hY φ).1 h _ _

theorem nonempty_iso_iff (hX : X.ValidD Δ n) (hY : Y.ValidD Δ n) :
    Nonempty (X.toSimpleGraph n ≃g Y.toSimpleGraph n) ↔ ∃ φ, IsIso n X Y φ := by
  constructor
  · rintro ⟨e⟩
    exact ⟨e.toEquiv, (isIso_iff hX hY _).2 fun u v => e.map_rel_iff⟩
  · rintro ⟨φ, h⟩
    exact ⟨isoOfIsIso hX hY h⟩

/-- Levels grow by at most one along each step of a walk. -/
theorem lev_walk_le (hG : G.ValidD Δ n) {roots : List ℕ} {L : Array ℕ}
    (hL : IsLevels n G roots L) {x y : Fin n} (p : (G.toSimpleGraph n).Walk x y) :
    get L y ≤ get L x + p.length := by
  induction p with
  | nil => simp
  | cons h p ih =>
    rename_i a b c
    have hab := (toSimpleGraph_adj hG a b).1 h
    have := hL.adj_le b a (hG.symm _ _ hab)
    rw [SimpleGraph.Walk.length_cons]
    omega

/-- **The connectivity read by the algorithm is connectivity.** -/
theorem conn_iff_connected (hG : G.ValidD Δ n) (hn : 0 < n) :
    Conn n G ↔ (G.toSimpleGraph n).Connected := by
  have hL := levels_spec (roots := [0]) hG
  constructor
  · intro hc
    have key : ∀ k v (hv : v < n), get (levels n G [0]) v = k →
        (G.toSimpleGraph n).Reachable ⟨0, hn⟩ ⟨v, hv⟩ := by
      intro k
      induction k with
      | zero =>
        intro v hv hk
        have := (hL.zero_iff v hv).1 hk
        simp only [List.mem_singleton] at this
        subst this
        rfl
      | succ k ih =>
        intro v hv hk
        obtain ⟨u, hvu, hlu⟩ := hL.wit v hv (by omega) (hc v hv)
        have hu : u < n := hG.lt v u hvu
        refine (ih u hu (by omega)).trans (SimpleGraph.Adj.reachable ?_)
        exact (toSimpleGraph_adj hG _ _).2 (hG.symm _ _ hvu)
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    exact ⟨⟨0, hn⟩, fun w => key _ w.1 w.2 rfl⟩
  · intro hc v hv
    obtain ⟨p, hp⟩ := (hc.preconnected ⟨0, hn⟩ ⟨v, hv⟩).exists_isPath
    have hlen := hp.length_lt
    have := lev_walk_le hG hL p
    have h0 : get (levels n G [0]) 0 = 0 := (hL.zero_iff 0 hn).2 (by simp)
    simp only [Fintype.card_fin] at hlen
    simp only [h0] at this
    omega

/-! ### From simple graphs to data -/

/-- The adjacency lists of a simple graph on `Fin n`. -/
def GraphData.ofSimpleGraph {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] : GraphData :=
  Array.ofFn fun u : Fin n => ((List.finRange n).filter fun v => decide (H.Adj u v)).map (·.val)

section OfSimpleGraph

variable {H : SimpleGraph (Fin n)} [DecidableRel H.Adj]

theorem nbrs_ofSimpleGraph (u : Fin n) :
    nbrs (GraphData.ofSimpleGraph H) u =
      ((List.finRange n).filter fun v => decide (H.Adj u v)).map (·.val) := by
  simp [nbrs, GraphData.ofSimpleGraph, Array.getD_eq_getD_getElem?]

theorem nbrs_ofSimpleGraph_of_ge {u : ℕ} (hu : n ≤ u) : nbrs (GraphData.ofSimpleGraph H) u = [] :=
  nbrs_of_ge (by simpa [GraphData.ofSimpleGraph] using hu)

theorem adj_ofSimpleGraph {u v : ℕ} :
    Adj (GraphData.ofSimpleGraph H) u v ↔ ∃ (hu : u < n) (hv : v < n), H.Adj ⟨u, hu⟩ ⟨v, hv⟩ := by
  by_cases hu : u < n
  · rw [Adj, show u = (⟨u, hu⟩ : Fin n).val from rfl, nbrs_ofSimpleGraph]
    simp only [List.mem_map, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨hu, w.2, hw⟩
    · rintro ⟨_, hv, h⟩
      exact ⟨⟨v, hv⟩, h, rfl⟩
  · rw [Adj, nbrs_ofSimpleGraph_of_ge (by omega)]
    simp [hu]

/-- **The simple graph of the data of `H` is `H`.** -/
theorem toSimpleGraph_ofSimpleGraph : (GraphData.ofSimpleGraph H).toSimpleGraph n = H := by
  ext u v
  rw [GraphData.toSimpleGraph, SimpleGraph.fromRel_adj, adj_ofSimpleGraph, adj_ofSimpleGraph]
  constructor
  · rintro ⟨-, ⟨_, _, h⟩ | ⟨_, _, h⟩⟩
    · exact h
    · exact h.symm
  · intro h
    exact ⟨H.ne_of_adj h, Or.inl ⟨u.2, v.2, h⟩⟩

theorem length_nbrs_ofSimpleGraph (u : Fin n) :
    (nbrs (GraphData.ofSimpleGraph H) u).length = H.degree u := by
  rw [nbrs_ofSimpleGraph, List.length_map, ← SimpleGraph.card_neighborFinset_eq_degree,
    SimpleGraph.neighborFinset_eq_filter, ← List.toFinset_card_of_nodup
      ((List.nodup_finRange n).filter _)]
  congr 1
  ext v
  simp

/-- **The data of a simple graph of maximum degree `Δ` are valid.** -/
theorem valid_ofSimpleGraph (hdeg : ∀ v, H.degree v ≤ Δ) :
    (GraphData.ofSimpleGraph H).ValidD Δ n := by
  refine ⟨by simp [GraphData.ofSimpleGraph], fun u v huv => ?_, fun u => ?_, fun u v huv => ?_,
    fun u huu => ?_, fun u => ?_⟩
  · obtain ⟨-, hv, -⟩ := adj_ofSimpleGraph.1 huv
    exact hv
  · by_cases hu : u < n
    · rw [show u = (⟨u, hu⟩ : Fin n).val from rfl, nbrs_ofSimpleGraph]
      exact ((List.nodup_finRange n).filter _).map Fin.val_injective
    · rw [nbrs_ofSimpleGraph_of_ge (by omega)]
      exact List.nodup_nil
  · obtain ⟨hu, hv, h⟩ := adj_ofSimpleGraph.1 huv
    exact adj_ofSimpleGraph.2 ⟨hv, hu, h.symm⟩
  · obtain ⟨_, _, h⟩ := adj_ofSimpleGraph.1 huu
    exact H.irrefl h
  · by_cases hu : u < n
    · rw [show u = (⟨u, hu⟩ : Fin n).val from rfl, length_nbrs_ofSimpleGraph]
      exact hdeg _
    · rw [nbrs_ofSimpleGraph_of_ge (by omega)]
      simp

end OfSimpleGraph

end GraphIso.Graph
