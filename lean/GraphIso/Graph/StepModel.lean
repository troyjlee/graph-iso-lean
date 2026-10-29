module

public import GraphIso.Graph.Perms

/-!
# Functional models of one layer step

The programs of a layer step compute these functions; the lemmas relate them to the semantic
objects of `GraphIso/Graph/Domain.lean`.

* `ptrips Lr`: the subsets of `Lr` as triples of points, in the order of the domain.
* `seteqB`: two lists with the same elements.
-/

@[expose] public section

namespace GraphIso.Graph

open Equiv Sims

/-! ### The subsets as triples of points -/

/-- The subsets of `Lr`, as triples of points, in the order of `subsL`. -/
def ptrips (Lr : List ℕ) : List (ℕ × ℕ × ℕ) := (subsL Lr.length).map (tmap (Lr.getD · 0))

theorem length_ptrips (Lr : List ℕ) : (ptrips Lr).length = nsub Lr := by
  simp [ptrips]

theorem getElem_ptrips {Lr : List ℕ} {t : ℕ} (ht : t < nsub Lr) :
    (ptrips Lr)[t]'(by rw [length_ptrips]; exact ht) = tmap (Lr.getD · 0) (subAt Lr t) := by
  simp only [ptrips, List.getElem_map, subAt_eq ht]

theorem tset_getElem_ptrips {Lr : List ℕ} {t : ℕ} (ht : t < nsub Lr) :
    tset ((ptrips Lr)[t]'(by rw [length_ptrips]; exact ht)) = tripSet Lr t := by
  rw [getElem_ptrips ht, tset_tmap]
  rfl

/-! ### The layer string on triples -/

/-- Two lists with the same elements. -/
def seteqB (l₁ l₂ : List ℕ) : Bool :=
  l₁.all (fun x => l₂.any fun y => y == x) && l₂.all fun x => l₁.any fun y => y == x

theorem any_beq_iff {l : List ℕ} {x : ℕ} : (l.any fun y => y == x) = true ↔ x ∈ l := by
  simp

theorem seteqB_iff {l₁ l₂ : List ℕ} : seteqB l₁ l₂ = true ↔ l₁.toFinset = l₂.toFinset := by
  simp only [seteqB, Bool.and_eq_true, List.all_eq_true, any_beq_iff, Finset.ext_iff,
    List.mem_toFinset]
  constructor
  · rintro ⟨h₁, h₂⟩ x
    exact ⟨h₁ x, h₂ x⟩
  · intro h
    exact ⟨fun x hx => (h x).1 hx, fun x hx => (h x).2 hx⟩

/-- Adjacency, as a test. -/
def adjB (G : GraphData) (u v : ℕ) : Bool := (nbrs G u).any fun y => y == v

theorem adjB_iff {G : GraphData} {u v : ℕ} : adjB G u v = true ↔ Adj G u v := by
  rw [adjB, any_beq_iff]
  rfl

/-- The set `{x, y, z}` is an edge: two adjacent points. -/
def edge3B (G : GraphData) (x y z : ℕ) : Bool :=
  if x = y then !(x == z) && adjB G x z else (z == x || z == y) && adjB G x y

theorem edge3B_iff {N : ℕ} {G : GraphData} (hG : G.Valid N) (x y z : ℕ) :
    edge3B G x y z = true ↔ IsEdge G {x, y, z} := by
  unfold edge3B
  by_cases hxy : x = y
  · subst hxy
    simp only [↓reduceIte, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
      beq_eq_false_iff_ne, adjB_iff, Finset.insert_eq_of_mem (Finset.mem_insert_self x {z})]
    by_cases hxz : x = z
    · subst hxz
      simp only [ne_eq, not_true_eq_false, false_and, false_iff]
      rintro ⟨h, -⟩
      simp at h
    · rw [isEdge_pair hG hxz]
      simp [hxz]
  · simp only [hxy, ↓reduceIte, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, adjB_iff]
    by_cases hz : z = x ∨ z = y
    · have e : ({x, y, z} : Finset ℕ) = {x, y} := by
        rcases hz with rfl | rfl <;> simp [Finset.pair_comm]
      rw [e, isEdge_pair hG hxy]
      tauto
    · push Not at hz
      have hc : ({x, y, z} : Finset ℕ).card = 3 := by
        rw [Finset.card_insert_of_notMem, Finset.card_pair (Ne.symm hz.2)]
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hxy, Ne.symm hz.1⟩
      constructor
      · rintro ⟨h, -⟩
        exact absurd h (by tauto)
      · rintro ⟨h, -⟩
        omega

section XArr

variable {N : ℕ} {G : GraphData} {lev : Array ℕ}

/-- The neighbours of level `r`, as a list. -/
def nbL (G : GraphData) (lev : Array ℕ) (r w : ℕ) : List ℕ :=
  (nbrs G w).filter fun u => get lev u == r

theorem toFinset_nbL {r w : ℕ} : (nbL G lev r w).toFinset = nb G lev r w := by
  ext u
  simp [nbL, nb]

/-- The layer string of the set `{x, y, z}`, as computed. -/
def xTrip (G : GraphData) (lev : Array ℕ) (N r x y z : ℕ) : ℕ :=
  ((levList lev N (r + 1)).filter fun w => seteqB (nbL G lev r w) [x, y, z]).length +
    if edge3B G x y z then 4 else 0

theorem xTrip_eq (hG : G.Valid N) {r : ℕ} (x y z : ℕ) :
    xTrip G lev N r x y z = xval G lev 3 N r {x, y, z} := by
  unfold xTrip xval cnt cls levList
  have hfilt : (((List.range N).filter fun v => get lev v = r + 1).filter fun w =>
      seteqB (nbL G lev r w) [x, y, z]) =
      (List.range N).filter fun w => get lev w = r + 1 ∧ nb G lev r w = {x, y, z} := by
    rw [List.filter_filter]
    refine List.filter_congr fun w _ => ?_
    have : seteqB (nbL G lev r w) [x, y, z] = decide (nb G lev r w = {x, y, z}) := by
      rw [Bool.eq_iff_iff, seteqB_iff, toFinset_nbL, decide_eq_true_iff]
      simp
    rw [this]
    simp [Bool.and_comm]
  rw [hfilt]
  have e : edge3B G x y z = decide (IsEdge G {x, y, z}) := by
    rw [Bool.eq_iff_iff, edge3B_iff hG, decide_eq_true_iff]
  rw [e]
  simp only [decide_eq_true_eq]

/-- The layer string array: `0` on the graph points, `xTrip` on the triples of points. -/
def xArr (G : GraphData) (lev : Array ℕ) (N r : ℕ) (Lr : List ℕ) : Array ℕ :=
  (List.replicate N 0 ++ (ptrips Lr).map fun (p : ℕ × ℕ × ℕ) =>
    xTrip G lev N r p.1 p.2.1 p.2.2).toArray

theorem get_xArr_lt {r : ℕ} {Lr : List ℕ} {v : ℕ} (hv : v < N) :
    get (xArr G lev N r Lr) v = 0 := by
  unfold xArr get
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    List.getElem?_append_left (by simpa using hv)]
  simp [hv]

theorem get_xArr_trip (hG : G.Valid N) {r : ℕ} {Lr : List ℕ} {t : ℕ} (ht : t < nsub Lr) :
    get (xArr G lev N r Lr) (N + t) = xval G lev 3 N r (tripSet Lr t) := by
  have hlen : t < (ptrips Lr).length := by rw [length_ptrips]; exact ht
  unfold xArr get
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    List.getElem?_append_right (by simp), List.length_replicate, Nat.add_sub_cancel_left,
    List.getElem?_map, List.getElem?_eq_getElem hlen]
  simp only [Option.map_some, Option.getD_some]
  rw [xTrip_eq hG, ← tset_getElem_ptrips ht]
  rfl

end XArr

end GraphIso.Graph
