module

public import GraphIso.Valence.Domain

/-!
# Functional models of one layer step for maximum degree `Δ`

The programs of a layer step compute these functions; the lemmas relate them to the semantic
objects of `GraphIso/Valence/Domain.lean`.

* `edgeL G s`: the list `s` is an edge, two adjacent points (`edgeL_iff`).
* `xSub Δ G lev N r s`: the layer string of the subset `s` as computed: the number of points
  of level `r + 1` whose neighbours of level `r` are the elements of `s`, plus `Δ + 1` for an
  edge. It is `xval` (`xSub_eq`).
* `xArr`: the layer-string array, `0` on the graph points and `xSub` on the subsets.
-/

@[expose] public section

namespace GraphIso.Graph.Valence

open Equiv Sims

/-! ### The edge test -/

/-- The list is an edge: two adjacent points. -/
def edgeL (G : GraphData) : List ℕ → Bool
  | [x, y] => adjB G x y
  | _ => false

theorem edgeL_iff {Δ N : ℕ} {G : GraphData} (hG : G.ValidD Δ N) :
    ∀ {s : List ℕ}, s.Nodup → (edgeL G s = true ↔ IsEdge G s.toFinset)
  | [], _ => by simp [edgeL, IsEdge]
  | [x], _ => by simp [edgeL, IsEdge]
  | [x, y], h => by
    have hxy : x ≠ y := by simpa using h
    have e : [x, y].toFinset = {x, y} := by simp
    rw [e, isEdge_pair hG hxy]
    exact adjB_iff
  | x :: y :: z :: l, h => by
    simp only [edgeL, Bool.false_eq_true, false_iff]
    rintro ⟨hc, -⟩
    rw [List.toFinset_card_of_nodup h] at hc
    simp at hc

/-! ### The layer string -/

section XArr

variable (Δ : ℕ) (G : GraphData) (lev : Array ℕ) (N r : ℕ)

/-- The layer string of the subset `s`, as computed. -/
def xSub (s : List ℕ) : ℕ :=
  ((levList lev N (r + 1)).filter fun w => seteqB (nbL G lev r w) s).length +
    if edgeL G s then Δ + 1 else 0

/-- The layer string array: `0` on the graph points, `xSub` on the subsets of `Lr`. -/
def xArr (Lr : List ℕ) : Array ℕ :=
  (List.replicate N 0 ++ (subsR Δ Lr).map (xSub Δ G lev N r)).toArray

variable {Δ G lev N r}

theorem xSub_eq (hG : G.ValidD Δ N) {s : List ℕ} (hs : s.Nodup) :
    xSub Δ G lev N r s = xval G lev Δ N r s.toFinset := by
  unfold xSub xval cnt cls levList
  have hfilt : (((List.range N).filter fun v => get lev v = r + 1).filter fun w =>
      seteqB (nbL G lev r w) s) =
      (List.range N).filter fun w => get lev w = r + 1 ∧ nb G lev r w = s.toFinset := by
    rw [List.filter_filter]
    refine List.filter_congr fun w _ => ?_
    have : seteqB (nbL G lev r w) s = decide (nb G lev r w = s.toFinset) := by
      rw [Bool.eq_iff_iff, seteqB_iff, toFinset_nbL, decide_eq_true_iff]
    rw [this]
    simp [Bool.and_comm]
  rw [hfilt]
  have e : edgeL G s = decide (IsEdge G s.toFinset) := by
    rw [Bool.eq_iff_iff, edgeL_iff hG hs, decide_eq_true_iff]
  rw [e]
  simp only [decide_eq_true_eq]

theorem get_xArr_lt {Lr : List ℕ} {v : ℕ} (hv : v < N) : get (xArr Δ G lev N r Lr) v = 0 := by
  unfold xArr get
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    List.getElem?_append_left (by simpa using hv)]
  simp [hv]

theorem get_xArr_sub (hG : G.ValidD Δ N) {Lr : List ℕ} (hLr : Lr.Pairwise (· < ·)) {t : ℕ}
    (ht : t < nsub Δ Lr) :
    get (xArr Δ G lev N r Lr) (N + t) = xval G lev Δ N r (subSet Δ Lr t) := by
  unfold xArr get
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    List.getElem?_append_right (by simp), List.length_replicate, Nat.add_sub_cancel_left,
    List.getElem?_map, List.getElem?_eq_getElem ht]
  simp only [Option.map_some, Option.getD_some]
  rw [← subAt_eq ht, xSub_eq hG (nodup_subAt hLr ht)]
  rfl

end XArr

end GraphIso.Graph.Valence
