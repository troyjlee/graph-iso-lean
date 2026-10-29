module

public import GraphIso.Graph.Basic
public import GraphIso.Sims.Basic

/-!
# Levels from a set of roots

`levels N G roots` starts from `0` at the roots and `N` elsewhere, and repeats a relaxation
pass, which lowers each point's level to one more than the least level of its neighbours,
until nothing changes. The sum of the levels drops at every pass that changes something, so
`N * N + 1` passes suffice.

The result is characterized by `IsLevels` (`levels_spec`):

* the points of level `0` are exactly the roots;
* adjacent points have levels differing by at most one;
* every point of positive level `< N` has a neighbour one level down;
* every level is at most `N` (the level of points not reached).

`lev_act`: a permutation preserving the roots and the adjacency preserves the levels.
-/

@[expose] public section

namespace GraphIso.Graph

open Equiv Sims

variable {Δ N : ℕ} {G : GraphData} {roots : List ℕ}

/-! ### The relaxation -/

/-- One relaxation at `v`: the least of its level and one more than each neighbour's. -/
def relaxAt (G : GraphData) (lev : Array ℕ) (v : ℕ) : ℕ :=
  (nbrs G v).foldl (fun m u => min m (get lev u + 1)) (get lev v)

/-- One relaxation pass over all points. -/
def relaxPass (N : ℕ) (G : GraphData) (lev : Array ℕ) : Array ℕ :=
  ((List.range N).map (relaxAt G lev)).toArray

/-- A pass, or `none` at a fixpoint. -/
def levStep (N : ℕ) (G : GraphData) (lev : Array ℕ) : Option (Array ℕ) :=
  if relaxPass N G lev = lev then none else some (relaxPass N G lev)

/-- The initial levels: `0` at the roots, `N` elsewhere. -/
def initLev (N : ℕ) (roots : List ℕ) : Array ℕ :=
  ((List.range N).map fun v => if v ∈ roots then 0 else N).toArray

/-- The levels from the roots. -/
def levels (N : ℕ) (G : GraphData) (roots : List ℕ) : Array ℕ :=
  iter (levStep N G) (N * N + 1) (initLev N roots)

/-! ### Folding a minimum -/

theorem foldl_min_le_init (f : ℕ → ℕ) : ∀ (l : List ℕ) (m : ℕ),
    l.foldl (fun m u => min m (f u)) m ≤ m
  | [], _ => le_rfl
  | _ :: l, _ => (foldl_min_le_init f l _).trans (min_le_left _ _)

theorem foldl_min_le (f : ℕ → ℕ) : ∀ (l : List ℕ) (m : ℕ) (u : ℕ), u ∈ l →
    l.foldl (fun m u => min m (f u)) m ≤ f u
  | [], _, _, h => absurd h (List.not_mem_nil)
  | x :: l, m, u, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact (foldl_min_le_init f l _).trans (min_le_right _ _)
    · exact foldl_min_le f l _ u h

theorem foldl_min_cases (f : ℕ → ℕ) : ∀ (l : List ℕ) (m : ℕ),
    l.foldl (fun m u => min m (f u)) m = m ∨
      ∃ u ∈ l, l.foldl (fun m u => min m (f u)) m = f u
  | [], _ => Or.inl rfl
  | x :: l, m => by
    rcases foldl_min_cases f l (min m (f x)) with h | ⟨u, hu, h⟩
    · simp only [List.foldl_cons, h]
      rcases min_choice m (f x) with e | e
      · exact Or.inl e
      · exact Or.inr ⟨x, List.mem_cons_self, e⟩
    · exact Or.inr ⟨u, List.mem_cons_of_mem _ hu, h⟩

/-! ### The invariant of the relaxation -/

theorem get_relaxPass {lev : Array ℕ} {v : ℕ} (hv : v < N) :
    get (relaxPass N G lev) v = relaxAt G lev v := by
  simp [relaxPass, get, hv]

theorem size_relaxPass (lev : Array ℕ) : (relaxPass N G lev).size = N := by
  simp [relaxPass]

theorem get_initLev {v : ℕ} (hv : v < N) :
    get (initLev N roots) v = if v ∈ roots then 0 else N := by
  simp [initLev, get, hv]

/-- The invariant of the relaxation. -/
structure LInv (N : ℕ) (G : GraphData) (roots : List ℕ) (lev : Array ℕ) : Prop where
  size : lev.size = N
  root : ∀ v < N, v ∈ roots → get lev v = 0
  pos : ∀ v < N, v ∉ roots → 1 ≤ get lev v
  wit : ∀ v < N, v ∉ roots → get lev v < N → ∃ u, Adj G v u ∧ get lev u + 1 ≤ get lev v
  le : ∀ v < N, get lev v ≤ N

theorem relaxAt_le (lev : Array ℕ) (v : ℕ) : relaxAt G lev v ≤ get lev v :=
  foldl_min_le_init _ _ _

theorem LInv.pass (hN : ∀ u v, Adj G u v → v < N) {lev : Array ℕ}
    (hI : LInv N G roots lev) :
    LInv N G roots (relaxPass N G lev) ∧ ∀ v < N, get (relaxPass N G lev) v ≤ get lev v := by
  have hle : ∀ v < N, get (relaxPass N G lev) v ≤ get lev v := fun v hv => by
    rw [get_relaxPass hv]
    exact relaxAt_le lev v
  refine ⟨⟨size_relaxPass lev, fun v hv hr => ?_, fun v hv hr => ?_, fun v hv hr hlt => ?_,
    fun v hv => (hle v hv).trans (hI.le v hv)⟩, hle⟩
  · have := hle v hv
    rw [hI.root v hv hr] at this
    omega
  · rw [get_relaxPass hv]
    unfold relaxAt
    rcases foldl_min_cases (fun u => get lev u + 1) (nbrs G v) (get lev v) with h | ⟨u, -, h⟩
    · rw [h]
      exact hI.pos v hv hr
    · rw [h]
      omega
  · have hnew := get_relaxPass (G := G) (lev := lev) hv
    unfold relaxAt at hnew
    rcases foldl_min_cases (fun u => get lev u + 1) (nbrs G v) (get lev v) with h | ⟨u, hu, h⟩
    · rw [h] at hnew
      rw [hnew] at hlt
      obtain ⟨u, hadj, hu⟩ := hI.wit v hv hr hlt
      have := hle u (hN v u hadj)
      exact ⟨u, hadj, by omega⟩
    · rw [h] at hnew
      have := hle u (hN v u hu)
      exact ⟨u, hu, by omega⟩

/-! ### Termination -/

/-- The potential: the sum of the levels. -/
def levPot (N : ℕ) (lev : Array ℕ) : ℕ := ∑ v ∈ Finset.range N, get lev v

theorem array_eq_of_get {N : ℕ} {a b : Array ℕ} (ha : a.size = N) (hb : b.size = N)
    (h : ∀ v < N, get a v = get b v) : a = b := by
  apply Array.ext (ha.trans hb.symm)
  intro i hi hi'
  have := h i (ha ▸ hi)
  simpa [get, hi, hi'] using this

theorem levPot_lt {a b : Array ℕ} (ha : a.size = N) (hb : b.size = N)
    (hle : ∀ v < N, get a v ≤ get b v) (hne : a ≠ b) : levPot N a < levPot N b := by
  obtain ⟨v, hv, hlt⟩ : ∃ v < N, get a v < get b v := by
    by_contra hcon
    push Not at hcon
    exact hne (array_eq_of_get ha hb fun v hv => le_antisymm (hle v hv) (hcon v hv))
  exact Finset.sum_lt_sum (fun v hv => hle v (Finset.mem_range.1 hv))
    ⟨v, Finset.mem_range.2 hv, hlt⟩

theorem levPot_le {lev : Array ℕ} (hle : ∀ v < N, get lev v ≤ N) : levPot N lev ≤ N * N := by
  have := Finset.sum_le_sum (s := Finset.range N) fun v hv => hle v (Finset.mem_range.1 hv)
  simpa [levPot] using this

theorem iter_levStep (hN : ∀ u v, Adj G u v → v < N) :
    ∀ (m : ℕ) (lev : Array ℕ), LInv N G roots lev → levPot N lev < m →
      LInv N G roots (iter (levStep N G) m lev) ∧ levStep N G (iter (levStep N G) m lev) = none
  | 0, _, _, hm => absurd hm (Nat.not_lt_zero _)
  | m + 1, lev, hI, hm => by
    by_cases he : relaxPass N G lev = lev
    · have hs : levStep N G lev = none := by simp [levStep, he]
      rw [show iter (levStep N G) (m + 1) lev = lev by simp [iter, hs]]
      exact ⟨hI, hs⟩
    · have hs : levStep N G lev = some (relaxPass N G lev) := by simp [levStep, he]
      obtain ⟨hI', hle⟩ := hI.pass hN
      have hpot := levPot_lt (size_relaxPass lev) hI.size hle he
      simp only [iter, hs]
      exact iter_levStep hN m _ hI' (by omega)

theorem linv_init : LInv N G roots (initLev N roots) := by
  refine ⟨by simp [initLev], fun v hv h => ?_, fun v hv h => ?_, fun v hv h hlt => ?_,
    fun v hv => ?_⟩
  · simp [get_initLev hv, h]
  · simp only [get_initLev hv, h, ↓reduceIte]
    omega
  · simp [get_initLev hv, h] at hlt
  · rw [get_initLev hv]
    split <;> omega

/-! ### The characterization -/

/-- **Levels from the roots.** -/
structure IsLevels (N : ℕ) (G : GraphData) (roots : List ℕ) (lev : Array ℕ) : Prop where
  size : lev.size = N
  zero_iff : ∀ v < N, get lev v = 0 ↔ v ∈ roots
  adj_le : ∀ u v, Adj G u v → get lev u ≤ get lev v + 1
  wit : ∀ v < N, 0 < get lev v → get lev v < N → ∃ u, Adj G v u ∧ get lev u + 1 = get lev v
  le : ∀ v < N, get lev v ≤ N

theorem levels_spec (hG : G.ValidD Δ N) :
    IsLevels N G roots (levels N G roots) := by
  have hN : ∀ u v, Adj G u v → v < N := hG.lt
  have hpot : levPot N (initLev N roots) < N * N + 1 :=
    Nat.lt_succ_of_le (levPot_le (linv_init (G := G)).le)
  obtain ⟨hI, hfix⟩ : LInv N G roots (levels N G roots) ∧
      levStep N G (levels N G roots) = none := iter_levStep hN (N * N + 1) _ linv_init hpot
  set lev := levels N G roots with hlev
  have hfix' : relaxPass N G lev = lev := by
    by_contra h
    simp [levStep, h] at hfix
  -- the fixpoint inequality
  have hadj : ∀ u v, Adj G u v → get lev u ≤ get lev v + 1 := by
    intro u v huv
    have hu := hG.lt_left huv
    have := get_relaxPass (G := G) (lev := lev) hu
    rw [hfix'] at this
    rw [this]
    exact foldl_min_le _ _ _ v huv
  refine ⟨hI.size, fun v hv => ⟨fun h => ?_, hI.root v hv⟩, hadj, fun v hv hpos hlt => ?_, hI.le⟩
  · by_contra hr'
    have := hI.pos v hv hr'
    omega
  · have hr' : v ∉ roots := fun h => by rw [hI.root v hv h] at hpos; omega
    obtain ⟨u, huv, hle⟩ := hI.wit v hv hr' hlt
    exact ⟨u, huv, le_antisymm hle (hadj v u huv)⟩

/-! ### Automorphisms preserve levels -/

theorem lev_act_le (hG : G.ValidD Δ N) {lev : Array ℕ} (hL : IsLevels N G roots lev)
    {g : Perm (Fin N)} (hroot : ∀ v < N, v ∈ roots → act g v ∈ roots)
    (hadj : ∀ u v, u < N → v < N → Adj G u v → Adj G (act g u) (act g v)) :
    ∀ v < N, get lev (act g v) ≤ get lev v := by
  intro v hv
  induction h : get lev v using Nat.strong_induction_on generalizing v with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · have := hroot v hv ((hL.zero_iff v hv).1 h)
      rw [(hL.zero_iff _ (act_lt g hv)).2 this]
    · rcases Nat.lt_or_ge k N with hkN | hkN
      · obtain ⟨u, huv, hu⟩ := hL.wit v hv (h ▸ hk) (h ▸ hkN)
        have hun : u < N := hG.lt v u huv
        have h₁ := ih (get lev u) (by omega) u hun rfl
        have h₂ := hL.adj_le _ _ (hadj v u hv hun huv)
        omega
      · rw [← h] at hkN
        exact (hL.le _ (act_lt g hv)).trans (by omega)

/-- **A permutation preserving the roots and the adjacency preserves the levels.** -/
theorem lev_act (hG : G.ValidD Δ N) {lev : Array ℕ} (hL : IsLevels N G roots lev)
    {g : Perm (Fin N)} (hroot : ∀ v < N, act g v ∈ roots ↔ v ∈ roots)
    (hadj : ∀ u v, u < N → v < N → (Adj G (act g u) (act g v) ↔ Adj G u v)) :
    ∀ v < N, get lev (act g v) = get lev v := by
  intro v hv
  refine le_antisymm (lev_act_le hG hL (fun v hv h => (hroot v hv).2 h)
    (fun u v hu hv h => (hadj u v hu hv).2 h) v hv) ?_
  have hinv := lev_act_le hG hL (g := g⁻¹)
    (fun v hv h => by
      have := (hroot _ (act_lt g⁻¹ hv)).1
      rw [act_act_inv] at this
      exact this h)
    (fun u v hu hv h => by
      have := (hadj _ _ (act_lt g⁻¹ hu) (act_lt g⁻¹ hv)).1
      rw [act_act_inv, act_act_inv] at this
      exact this h) (act g v) (act_lt g hv)
  rwa [act_inv_act] at hinv

end GraphIso.Graph
