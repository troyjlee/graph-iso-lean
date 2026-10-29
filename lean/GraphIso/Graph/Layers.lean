module

public import GraphIso.Graph.Levels

/-!
# Layer groups

Fix valid graph data `G` on `N` points of maximum degree at most `Δ ≥ 2`, roots, and levels
`lev` (`IsLevels`) reaching every point (`L v < N`), where every root has a neighbouring root
(`LayeredD Δ`; `Layered` is the case `Δ = 3`). Write `L v` for the level of `v`.

* `EdgeR r u v`: the edges of the layered graph `Z_r`: both ends of level `≤ r`, and one end of
  level `< r` or both ends roots.
* `AutR r`: the permutations supported on level `≤ r` that preserve levels and the edges of
  `Z_r`.
* For a new point `w` (level `r + 1`), `nb r w` is its set of neighbours of level `r`;
  `cls r T` lists, in increasing order, the new points with `nb r w = T`, and `cnt r T` counts
  them. Every class has at most `Δ − 1` points (`cnt_le`): a point of level `r` has a
  neighbour of level `r − 1` (or a root neighbour), hence at most `Δ − 1` of level `r + 1`.
* `xval Δ r T` is the layer string: `cnt r T`, plus `Δ + 1` when `T` is an edge of two points.
  It is read on the subsets of level `r` with one to `Δ` points (`SubL Δ`).
-/

@[expose] public section

namespace GraphIso.Graph

open Equiv Sims

/-- The data of a layered graph: valid graph data of maximum degree `Δ ≥ 2`, levels reaching
every point, and a neighbouring root for every root. -/
structure LayeredD (Δ N : ℕ) (G : GraphData) (roots : List ℕ) (lev : Array ℕ) : Prop where
  valid : G.ValidD Δ N
  levels : IsLevels N G roots lev
  reach : ∀ v < N, get lev v < N
  rootNb : ∀ v < N, get lev v = 0 → ∃ u, Adj G v u ∧ get lev u = 0
  two_le : 2 ≤ Δ

/-- The layered graphs of maximum degree three. -/
abbrev Layered (N : ℕ) (G : GraphData) (roots : List ℕ) (lev : Array ℕ) : Prop :=
  LayeredD 3 N G roots lev

variable {Δ N : ℕ} {G : GraphData} {roots : List ℕ} {lev : Array ℕ}

section Defs

variable (G lev)

/-- The edges of the layered graph `Z_r`. -/
def EdgeR (r u v : ℕ) : Prop :=
  Adj G u v ∧ get lev u ≤ r ∧ get lev v ≤ r ∧
    (get lev u < r ∨ get lev v < r ∨ (get lev u = 0 ∧ get lev v = 0))

/-- The neighbours of level `r`. -/
def nb (r w : ℕ) : Finset ℕ := ((nbrs G w).filter fun u => get lev u = r).toFinset

/-- The points of level `r + 1` with neighbourhood `T` in level `r`, in increasing order. -/
def cls (N r : ℕ) (T : Finset ℕ) : List ℕ :=
  (List.range N).filter fun w => get lev w = r + 1 ∧ nb G lev r w = T

/-- The number of points of level `r + 1` with neighbourhood `T`. -/
def cnt (N r : ℕ) (T : Finset ℕ) : ℕ := (cls G lev N r T).length

/-- `T` is an edge: two adjacent points. -/
def IsEdge (T : Finset ℕ) : Prop := T.card = 2 ∧ ∃ u ∈ T, ∃ v ∈ T, Adj G u v

instance (T : Finset ℕ) : Decidable (IsEdge G T) := by unfold IsEdge; infer_instance

/-- The layer string for maximum degree `Δ`. -/
def xval (Δ N r : ℕ) (T : Finset ℕ) : ℕ := cnt G lev N r T + if IsEdge G T then Δ + 1 else 0

/-- The subsets of level `r` that the layer string is read on: one to `Δ` points. -/
def SubL (Δ N r : ℕ) (T : Finset ℕ) : Prop :=
  T.Nonempty ∧ T.card ≤ Δ ∧ ∀ u ∈ T, u < N ∧ get lev u = r

end Defs

theorem mem_nb {r w u : ℕ} : u ∈ nb G lev r w ↔ Adj G w u ∧ get lev u = r := by
  simp [nb, Adj]

theorem mem_cls {r w : ℕ} {T : Finset ℕ} :
    w ∈ cls G lev N r T ↔ w < N ∧ get lev w = r + 1 ∧ nb G lev r w = T := by
  simp [cls]

theorem nodup_cls (r : ℕ) (T : Finset ℕ) : (cls G lev N r T).Nodup :=
  (List.nodup_range).filter _

theorem sorted_cls (r : ℕ) (T : Finset ℕ) : (cls G lev N r T).Pairwise (· < ·) :=
  (List.pairwise_lt_range).filter _

/-! ### Classes have at most `Δ − 1` points -/

/-- A point of level `r` has a neighbour not of level `r + 1`. -/
theorem exists_nb_not_up (hZ : LayeredD Δ N G roots lev) {u : ℕ} (hu : u < N) :
    ∃ u₀, Adj G u u₀ ∧ get lev u₀ ≠ get lev u + 1 := by
  rcases Nat.eq_zero_or_pos (get lev u) with h | h
  · obtain ⟨u₀, hadj, h₀⟩ := hZ.rootNb u hu h
    exact ⟨u₀, hadj, by omega⟩
  · obtain ⟨u₀, hadj, h₀⟩ := hZ.levels.wit u hu h (hZ.reach u hu)
    exact ⟨u₀, hadj, by omega⟩

/-- **Twin classes have at most `Δ − 1` points.** -/
theorem cnt_le (hZ : LayeredD Δ N G roots lev) {r : ℕ} {T : Finset ℕ} (hT : T.Nonempty) :
    cnt G lev N r T ≤ Δ - 1 := by
  rcases hc : cls G lev N r T with _ | ⟨w₀, rest⟩
  · simp [cnt, hc]
  obtain ⟨u, hu⟩ := hT
  have hw₀ : w₀ ∈ cls G lev N r T := by rw [hc]; exact List.mem_cons_self
  obtain ⟨-, -, hnb₀⟩ := mem_cls.1 hw₀
  have hadj₀ := (mem_nb.1 (hnb₀ ▸ hu : u ∈ nb G lev r w₀))
  have hun : u < N := hZ.valid.lt _ _ hadj₀.1
  -- every member of the class is a neighbour of `u` of level `r + 1`
  have hsub : cls G lev N r T ⊆ (nbrs G u).filter fun w => get lev w = r + 1 := by
    intro w hw
    obtain ⟨-, hlw, hnb⟩ := mem_cls.1 hw
    have := (mem_nb.1 (hnb ▸ hu : u ∈ nb G lev r w)).1
    exact List.mem_filter.2 ⟨hZ.valid.symm _ _ this, by simp [hlw]⟩
  have hlen := (List.subperm_of_subset (nodup_cls r T) hsub).length_le
  obtain ⟨u₀, hadj, hne⟩ := exists_nb_not_up hZ hun
  have hlt : ((nbrs G u).filter fun w => get lev w = r + 1).length < (nbrs G u).length := by
    rw [List.length_filter_lt_length_iff_exists]
    exact ⟨u₀, hadj, by simp [hadj₀.2] at hne ⊢; exact hne⟩
  have := hZ.valid.deg u
  rw [hc] at hlen
  simp only [cnt, hc]
  omega

/-- Twin classes of graphs of maximum degree three have at most two points. -/
theorem cnt_le_two (hZ : Layered N G roots lev) {r : ℕ} {T : Finset ℕ} (hT : T.Nonempty) :
    cnt G lev N r T ≤ 2 :=
  cnt_le hZ hT

/-! ### The layer groups -/

variable (N G lev) in
/-- **The layer group `A_r`**: permutations supported on level `≤ r` preserving levels and the
edges of `Z_r`. -/
def AutR (r : ℕ) : Subgroup (Perm (Fin N)) where
  carrier := {g | (∀ v < N, r < get lev v → act g v = v) ∧
    (∀ v < N, get lev (act g v) = get lev v) ∧
    ∀ u v, u < N → v < N → (EdgeR G lev r (act g u) (act g v) ↔ EdgeR G lev r u v)}
  one_mem' := ⟨fun v _ _ => act_one v, fun v _ => by rw [act_one],
    fun u v _ _ => by rw [act_one, act_one]⟩
  mul_mem' := by
    rintro g h ⟨hg₁, hg₂, hg₃⟩ ⟨hh₁, hh₂, hh₃⟩
    refine ⟨fun v hv hr => ?_, fun v hv => ?_, fun u v hu hv => ?_⟩
    · rw [act_mul, hh₁ v hv hr, hg₁ v hv hr]
    · rw [act_mul, hg₂ _ (act_lt h hv), hh₂ v hv]
    · rw [act_mul, act_mul, hg₃ _ _ (act_lt h hu) (act_lt h hv), hh₃ u v hu hv]
  inv_mem' := by
    rintro g ⟨hg₁, hg₂, hg₃⟩
    refine ⟨fun v hv hr => ?_, fun v hv => ?_, fun u v hu hv => ?_⟩
    · have := hg₁ v hv hr
      rw [act_inv_eq_iff, this]
    · have := hg₂ _ (act_lt g⁻¹ hv)
      rw [act_act_inv] at this
      exact this.symm
    · have := hg₃ _ _ (act_lt g⁻¹ hu) (act_lt g⁻¹ hv)
      rw [act_act_inv, act_act_inv] at this
      exact this.symm

theorem mem_AutR {r : ℕ} {g : Perm (Fin N)} : g ∈ AutR N G lev r ↔
    (∀ v < N, r < get lev v → act g v = v) ∧ (∀ v < N, get lev (act g v) = get lev v) ∧
      ∀ u v, u < N → v < N → (EdgeR G lev r (act g u) (act g v) ↔ EdgeR G lev r u v) :=
  Iff.rfl

end GraphIso.Graph
