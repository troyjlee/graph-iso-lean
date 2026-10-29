module

public import GraphIso.Graph.SimpleGraph

/-!
# Components of graph data

For valid data `G` on `n` points, of any maximum degree `Δ` (`GraphData.ValidD Δ`):

* `Reach G u v`: `u` reaches `v` by steps along adjacency. It is read off the levels:
  `get (levels n G [u]) v < n` exactly when `u` reaches `v` (`lev_lt_iff_reach`).
* `compOf n G u`: the points reached from `u`, in increasing order. A point is a
  representative (`isRep`) when it reaches no smaller point, and the components
  (`comps n G`) are the components of the representatives. They are nonempty, closed under
  adjacency, pairwise disjoint, and every point lies in one (`exists_mem_comps`,
  `eq_of_mem_comps`).
* `subG G cs`: the data of `cs` relabelled by position, `cs[i]` becoming `i`. For a component
  they are valid and connected (`valid_subG`, `conn_subG`).
-/

@[expose] public section

namespace GraphIso.Graph

open Equiv Sims

variable {Δ n : ℕ} {G : GraphData}

/-! ### Reachability -/

/-- `u` reaches `v` by steps along adjacency. -/
def Reach (G : GraphData) (u v : ℕ) : Prop := Relation.ReflTransGen (Adj G) u v

theorem Reach.refl' (u : ℕ) : Reach G u u := Relation.ReflTransGen.refl

theorem Reach.trans {u v w : ℕ} (h₁ : Reach G u v) (h₂ : Reach G v w) : Reach G u w :=
  Relation.ReflTransGen.trans h₁ h₂

theorem Reach.symm (hG : G.ValidD Δ n) {u v : ℕ} (h : Reach G u v) : Reach G v u := by
  induction h with
  | refl => exact .refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (hG.symm _ _ hbc) ih

theorem Reach.lt (hG : G.ValidD Δ n) {u v : ℕ} (h : Reach G u v) (hu : u < n) : v < n := by
  induction h with
  | refl => exact hu
  | tail _ hbc _ => exact hG.lt _ _ hbc

theorem reachable_of_reach (hG : G.ValidD Δ n) {u v : ℕ} (hu : u < n) (h : Reach G u v) :
    (G.toSimpleGraph n).Reachable ⟨u, hu⟩ ⟨v, h.lt hG hu⟩ := by
  induction h with
  | refl => rfl
  | tail hab hbc ih =>
    exact ih.trans (SimpleGraph.Adj.reachable ((toSimpleGraph_adj hG _ _).2 hbc))

/-- **Reachability is read off the levels.** -/
theorem lev_lt_iff_reach (hG : G.ValidD Δ n) {u v : ℕ} (hu : u < n) (hv : v < n) :
    get (levels n G [u]) v < n ↔ Reach G u v := by
  have hL := levels_spec (roots := [u]) hG
  constructor
  · have key : ∀ k w (hw : w < n), get (levels n G [u]) w = k → k < n → Reach G u w := by
      intro k
      induction k with
      | zero =>
        intro w hw hk _
        have := (hL.zero_iff w hw).1 hk
        simp only [List.mem_singleton] at this
        subst this
        exact .refl
      | succ k ih =>
        intro w hw hk hkn
        obtain ⟨x, hwx, hlx⟩ := hL.wit w hw (by omega) (by omega)
        exact (ih x (hG.lt w x hwx) (by omega) (by omega)).tail (hG.symm _ _ hwx)
    exact fun h => key _ v hv rfl h
  · intro h
    obtain ⟨p, hp⟩ := (reachable_of_reach hG hu h).exists_isPath
    have hlen := hp.length_lt
    have := lev_walk_le hG hL p
    have h0 : get (levels n G [u]) u = 0 := (hL.zero_iff u hu).2 (by simp)
    simp only [Fintype.card_fin] at hlen
    simp only [h0] at this
    omega

/-! ### Components -/

/-- The points reached from `u`, in increasing order. -/
def compOf (n : ℕ) (G : GraphData) (u : ℕ) : List ℕ :=
  (List.range n).filter fun v => decide (get (levels n G [u]) v < n)

/-- `u` reaches no smaller point. -/
def isRep (n : ℕ) (G : GraphData) (u : ℕ) : Bool :=
  !(List.range u).any fun v => decide (get (levels n G [u]) v < n)

/-- The representatives: the points least in their component. -/
def reps (n : ℕ) (G : GraphData) : List ℕ := (List.range n).filter (isRep n G)

/-- The components, by increasing representative. -/
def comps (n : ℕ) (G : GraphData) : List (List ℕ) := (reps n G).map (compOf n G)

theorem nodup_compOf {u : ℕ} : (compOf n G u).Nodup := List.nodup_range.filter _

theorem mem_compOf (hG : G.ValidD Δ n) {u v : ℕ} (hu : u < n) :
    v ∈ compOf n G u ↔ v < n ∧ Reach G u v := by
  simp only [compOf, List.mem_filter, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨hv, h⟩
    exact ⟨hv, (lev_lt_iff_reach hG hu hv).1 h⟩
  · rintro ⟨hv, h⟩
    exact ⟨hv, (lev_lt_iff_reach hG hu hv).2 h⟩

theorem self_mem_compOf (hG : G.ValidD Δ n) {u : ℕ} (hu : u < n) : u ∈ compOf n G u :=
  (mem_compOf hG hu).2 ⟨hu, .refl⟩

theorem compOf_eq (hG : G.ValidD Δ n) {u v : ℕ} (hu : u < n) (h : Reach G u v) :
    compOf n G v = compOf n G u := by
  have hv := h.lt hG hu
  unfold compOf
  refine List.filter_congr fun w hw => ?_
  rw [List.mem_range] at hw
  rw [decide_eq_decide, lev_lt_iff_reach hG hv hw, lev_lt_iff_reach hG hu hw]
  exact ⟨fun h' => h.trans h', fun h' => (h.symm hG).trans h'⟩

theorem isRep_iff (hG : G.ValidD Δ n) {u : ℕ} (hu : u < n) :
    isRep n G u = true ↔ ∀ v < u, ¬ Reach G u v := by
  simp only [isRep, Bool.not_eq_eq_eq_not, Bool.not_true, List.any_eq_false, List.mem_range,
    decide_eq_true_eq]
  exact forall₂_congr fun v hv => not_congr (lev_lt_iff_reach hG hu (by omega))

theorem mem_reps (hG : G.ValidD Δ n) {r : ℕ} :
    r ∈ reps n G ↔ r < n ∧ ∀ v < r, ¬ Reach G r v := by
  simp only [reps, List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨hr, h⟩
    exact ⟨hr, (isRep_iff hG hr).1 h⟩
  · rintro ⟨hr, h⟩
    exact ⟨hr, (isRep_iff hG hr).2 h⟩

/-- Every point is reached from a representative. -/
theorem exists_rep (hG : G.ValidD Δ n) {v : ℕ} (hv : v < n) : ∃ r ∈ reps n G, Reach G r v := by
  classical
  have hex : ∃ r, Reach G v r := ⟨v, .refl⟩
  have hmin := Nat.find_min' hex (Reach.refl' v)
  refine ⟨Nat.find hex, (mem_reps hG).2 ⟨by omega, fun w hw h => ?_⟩, (Nat.find_spec hex).symm hG⟩
  exact Nat.find_min hex hw ((Nat.find_spec hex).trans h)

/-- Representatives reaching each other are equal. -/
theorem rep_unique (hG : G.ValidD Δ n) {r r' : ℕ} (hr : r ∈ reps n G) (hr' : r' ∈ reps n G)
    (h : Reach G r r') : r = r' := by
  rw [mem_reps hG] at hr hr'
  rcases lt_trichotomy r r' with hlt | heq | hgt
  · exact absurd (h.symm hG) (hr'.2 r hlt)
  · exact heq
  · exact absurd h (hr.2 r' hgt)

theorem mem_comps {cs : List ℕ} :
    cs ∈ comps n G ↔ ∃ r ∈ reps n G, compOf n G r = cs := by
  simp only [comps, List.mem_map]

theorem lt_of_mem_reps (hG : G.ValidD Δ n) {r : ℕ} (hr : r ∈ reps n G) : r < n :=
  ((mem_reps hG).1 hr).1

/-- The component of a point is a component. -/
theorem compOf_mem_comps (hG : G.ValidD Δ n) {v : ℕ} (hv : v < n) : compOf n G v ∈ comps n G := by
  obtain ⟨r, hr, hrv⟩ := exists_rep hG hv
  exact mem_comps.2 ⟨r, hr, (compOf_eq hG (lt_of_mem_reps hG hr) hrv).symm⟩

theorem nodup_comps (hG : G.ValidD Δ n) : (comps n G).Nodup := by
  refine List.Nodup.map_on (fun r hr r' hr' h => rep_unique hG hr hr' ?_)
    (List.nodup_range.filter _)
  have := self_mem_compOf hG (lt_of_mem_reps hG hr')
  rw [← h, mem_compOf hG (lt_of_mem_reps hG hr)] at this
  exact this.2

section MemComps

variable (hG : G.ValidD Δ n) {cs : List ℕ} (hcs : cs ∈ comps n G)
include hG hcs

/-- A component is the component of each of its points. -/
theorem eq_compOf_of_mem {u : ℕ} (hu : u ∈ cs) : cs = compOf n G u := by
  obtain ⟨r, hr, rfl⟩ := mem_comps.1 hcs
  have hrn := lt_of_mem_reps hG hr
  exact (compOf_eq hG hrn ((mem_compOf hG hrn).1 hu).2).symm

theorem lt_of_mem_comps {u : ℕ} (hu : u ∈ cs) : u < n := by
  obtain ⟨r, hr, rfl⟩ := mem_comps.1 hcs
  exact ((mem_compOf hG (lt_of_mem_reps hG hr)).1 hu).1

theorem reach_of_mem_comps {u v : ℕ} (hu : u ∈ cs) (hv : v ∈ cs) : Reach G u v := by
  obtain ⟨r, hr, rfl⟩ := mem_comps.1 hcs
  have hrn := lt_of_mem_reps hG hr
  exact (((mem_compOf hG hrn).1 hu).2.symm hG).trans ((mem_compOf hG hrn).1 hv).2

theorem mem_comps_of_reach {u v : ℕ} (hu : u ∈ cs) (h : Reach G u v) : v ∈ cs := by
  have hun := lt_of_mem_comps hG hcs hu
  rw [eq_compOf_of_mem hG hcs hu, mem_compOf hG hun]
  exact ⟨h.lt hG hun, h⟩

theorem ne_nil_of_mem_comps : cs ≠ [] := by
  obtain ⟨r, hr, rfl⟩ := mem_comps.1 hcs
  exact List.ne_nil_of_mem (self_mem_compOf hG (lt_of_mem_reps hG hr))

omit hG in
theorem nodup_of_mem_comps : cs.Nodup := by
  obtain ⟨r, hr, rfl⟩ := mem_comps.1 hcs
  exact nodup_compOf

end MemComps

/-- Every point lies in a component. -/
theorem exists_mem_comps (hG : G.ValidD Δ n) {v : ℕ} (hv : v < n) : ∃ cs ∈ comps n G, v ∈ cs :=
  ⟨_, compOf_mem_comps hG hv, self_mem_compOf hG hv⟩

/-- Components sharing a point are equal. -/
theorem eq_of_mem_comps (hG : G.ValidD Δ n) {cs cs' : List ℕ} (hcs : cs ∈ comps n G)
    (hcs' : cs' ∈ comps n G) {v : ℕ} (hv : v ∈ cs) (hv' : v ∈ cs') : cs = cs' :=
  (eq_compOf_of_mem hG hcs hv).trans (eq_compOf_of_mem hG hcs' hv').symm

/-! ### Component data -/

/-- The data of `cs` relabelled by position: `cs[i]` becomes `i`. -/
def subG (G : GraphData) (cs : List ℕ) : GraphData :=
  (cs.map fun u => (nbrs G u).map cs.idxOf).toArray

/-- `cs` is closed under adjacency. -/
def Closed (G : GraphData) (cs : List ℕ) : Prop := ∀ u ∈ cs, ∀ w, Adj G u w → w ∈ cs

theorem closed_of_mem_comps (hG : G.ValidD Δ n) {cs : List ℕ} (hcs : cs ∈ comps n G) :
    Closed G cs :=
  fun _ hu _ h => mem_comps_of_reach hG hcs hu (Relation.ReflTransGen.single h)

theorem size_subG (cs : List ℕ) : (subG G cs).size = cs.length := by simp [subG]

theorem nbrs_subG {cs : List ℕ} {i : ℕ} (hi : i < cs.length) :
    nbrs (subG G cs) i = (nbrs G (cs.getD i 0)).map cs.idxOf := by
  simp [nbrs, subG, Array.getD_eq_getD_getElem?, hi, List.getD_eq_getElem?_getD]

theorem nbrs_subG_of_ge {cs : List ℕ} {i : ℕ} (hi : cs.length ≤ i) : nbrs (subG G cs) i = [] :=
  nbrs_of_ge (by rwa [size_subG])

section Closed

variable {cs : List ℕ} (hcl : Closed G cs) (hnd : cs.Nodup)

include hnd in
theorem idxOf_getD {i : ℕ} (hi : i < cs.length) : cs.idxOf (cs.getD i 0) = i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some,
    hnd.idxOf_getElem i hi]

include hcl hnd in
theorem adj_subG {i j : ℕ} :
    Adj (subG G cs) i j ↔ i < cs.length ∧ j < cs.length ∧ Adj G (cs.getD i 0) (cs.getD j 0) := by
  by_cases hi : i < cs.length
  · rw [Adj, nbrs_subG hi, List.mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hwc := hcl _ (getD_mem hi) w hw
      exact ⟨hi, List.idxOf_lt_length_of_mem hwc, by rwa [getD_idxOf hwc]⟩
    · rintro ⟨-, hj, h⟩
      exact ⟨_, h, idxOf_getD hnd hj⟩
  · rw [Adj, nbrs_subG_of_ge (by omega)]
    simp [hi]

include hcl hnd in
/-- Steps inside a closed list are steps of the component data. -/
theorem reach_subG {a b : ℕ} (ha : a ∈ cs) (h : Reach G a b) :
    b ∈ cs ∧ Reach (subG G cs) (cs.idxOf a) (cs.idxOf b) := by
  induction h with
  | refl => exact ⟨ha, .refl⟩
  | tail _ hbc ih =>
    obtain ⟨hb, hr⟩ := ih
    have hc := hcl _ hb _ hbc
    refine ⟨hc, hr.tail ((adj_subG hcl hnd).2 ⟨List.idxOf_lt_length_of_mem hb,
      List.idxOf_lt_length_of_mem hc, ?_⟩)⟩
    rwa [getD_idxOf hb, getD_idxOf hc]

include hcl hnd in
theorem valid_subG (hG : G.ValidD Δ n) : (subG G cs).ValidD Δ cs.length := by
  refine ⟨size_subG cs, fun u v huv => ((adj_subG hcl hnd).1 huv).2.1, fun u => ?_,
    fun u v huv => ?_, fun u huu => ?_, fun u => ?_⟩
  · by_cases hu : u < cs.length
    · rw [nbrs_subG hu]
      refine (hG.nodup _).map_on fun x hx y hy hxy => ?_
      exact (List.idxOf_inj (hcl _ (getD_mem hu) x hx)).1 hxy
    · rw [nbrs_subG_of_ge (by omega)]
      exact List.nodup_nil
  · obtain ⟨hu, hv, h⟩ := (adj_subG hcl hnd).1 huv
    exact (adj_subG hcl hnd).2 ⟨hv, hu, hG.symm _ _ h⟩
  · obtain ⟨-, -, h⟩ := (adj_subG hcl hnd).1 huu
    exact hG.irrefl _ h
  · by_cases hu : u < cs.length
    · rw [nbrs_subG hu, List.length_map]
      exact hG.deg _
    · rw [nbrs_subG_of_ge (by omega)]
      simp

end Closed

/-- **The data of a component are connected.** -/
theorem conn_subG (hG : G.ValidD Δ n) {cs : List ℕ} (hcs : cs ∈ comps n G) :
    Conn cs.length (subG G cs) := by
  have hcl := closed_of_mem_comps hG hcs
  have hnd := nodup_of_mem_comps hcs
  have hpos : 0 < cs.length := List.length_pos_iff.2 (ne_nil_of_mem_comps hG hcs)
  intro v hv
  rw [lev_lt_iff_reach (valid_subG hcl hnd hG) hpos hv]
  have h := (reach_subG hcl hnd (getD_mem hpos)
    (reach_of_mem_comps hG hcs (getD_mem hpos) (getD_mem hv))).2
  rwa [idxOf_getD hnd hpos, idxOf_getD hnd hv] at h

/-! ### Isomorphisms -/

section Iso

variable {k : ℕ} {A B C : GraphData}

theorem isIso_one (k : ℕ) (A : GraphData) : IsIso k A A 1 := fun _ _ _ _ => by simp

theorem IsIso.inv {φ : Perm (Fin k)} (h : IsIso k A B φ) : IsIso k B A φ⁻¹ := by
  intro u v hu hv
  have := h (act φ⁻¹ u) (act φ⁻¹ v) (act_lt _ hu) (act_lt _ hv)
  rw [act_act_inv, act_act_inv] at this
  exact this.symm

theorem IsIso.comp {φ ψ : Perm (Fin k)} (h₁ : IsIso k A B φ) (h₂ : IsIso k B C ψ) :
    IsIso k A C (ψ * φ) := by
  intro u v hu hv
  rw [act_mul, act_mul]
  exact (h₂ _ _ (act_lt _ hu) (act_lt _ hv)).trans (h₁ u v hu hv)

/-- Isomorphic data of the same size. -/
def GIso (A B : GraphData) : Prop :=
  ∃ k, A.size = k ∧ B.size = k ∧ ∃ φ : Perm (Fin k), IsIso k A B φ

theorem GIso.refl (A : GraphData) : GIso A A := ⟨_, rfl, rfl, 1, isIso_one _ _⟩

theorem GIso.symm (h : GIso A B) : GIso B A :=
  let ⟨k, ha, hb, φ, hφ⟩ := h
  ⟨k, hb, ha, φ⁻¹, hφ.inv⟩

theorem GIso.trans (h₁ : GIso A B) (h₂ : GIso B C) : GIso A C := by
  obtain ⟨k, ha, hb, φ, hφ⟩ := h₁
  obtain ⟨k', hb', hc, ψ, hψ⟩ := h₂
  obtain rfl : k = k' := hb.symm.trans hb'
  exact ⟨k, ha, hc, ψ * φ, hφ.comp hψ⟩

end Iso

section Invariance

variable {X Y : GraphData} {φ : Perm (Fin n)} (hX : X.ValidD Δ n) (hY : Y.ValidD Δ n)
  (hφ : IsIso n X Y φ)

include hX hφ in
theorem reach_act {u v : ℕ} (hu : u < n) (h : Reach X u v) : Reach Y (act φ u) (act φ v) := by
  induction h with
  | refl => exact .refl
  | tail hab hbc ih =>
    have hb := Reach.lt hX hab hu
    exact ih.tail ((hφ _ _ hb (hX.lt _ _ hbc)).2 hbc)

/-- The component of `Y` onto which `φ` maps `cs`. -/
def imgComp (n : ℕ) (Y : GraphData) (φ : Perm (Fin n)) (cs : List ℕ) : List ℕ :=
  compOf n Y (act φ (cs.headD 0))

theorem headD_mem {cs : List ℕ} (h : cs ≠ []) : cs.headD 0 ∈ cs := by
  cases cs with
  | nil => exact absurd rfl h
  | cons a l => exact List.mem_cons_self

variable {cs : List ℕ} (hcs : cs ∈ comps n X)

include hX hY hφ hcs in
theorem mem_imgComp {v : ℕ} : v ∈ imgComp n Y φ cs ↔ ∃ u ∈ cs, act φ u = v := by
  have hr := headD_mem (ne_nil_of_mem_comps hX hcs)
  have hrn := lt_of_mem_comps hX hcs hr
  rw [imgComp, mem_compOf hY (act_lt _ hrn)]
  constructor
  · rintro ⟨hv, h⟩
    have h' := reach_act hY hφ.inv (act_lt _ hrn) h
    rw [act_inv_act] at h'
    exact ⟨_, mem_comps_of_reach hX hcs hr h', act_act_inv _ _⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨act_lt _ (lt_of_mem_comps hX hcs hu),
      reach_act hX hφ hrn (reach_of_mem_comps hX hcs hr hu)⟩

include hX hY hcs in
theorem imgComp_mem : imgComp n Y φ cs ∈ comps n Y :=
  compOf_mem_comps hY (act_lt _ (lt_of_mem_comps hX hcs
    (headD_mem (ne_nil_of_mem_comps hX hcs))))

include hX hY hφ hcs in
theorem length_imgComp : (imgComp n Y φ cs).length = cs.length := by
  have hds := imgComp_mem (φ := φ) hX hY hcs
  rw [← List.toFinset_card_of_nodup (nodup_of_mem_comps hds),
    ← List.toFinset_card_of_nodup (nodup_of_mem_comps hcs),
    show (imgComp n Y φ cs).toFinset = cs.toFinset.image (act φ) by
      ext v
      simp only [List.mem_toFinset, Finset.mem_image, mem_imgComp hX hY hφ hcs],
    Finset.card_image_of_injective _ (act_injective φ)]

include hX hY hφ hcs in
/-- **The data of a component and of its image are isomorphic.** -/
theorem giso_imgComp : GIso (subG X cs) (subG Y (imgComp n Y φ cs)) := by
  set ds := imgComp n Y φ cs with hds_def
  have hds := imgComp_mem (φ := φ) hX hY hcs
  have hlen : ds.length = cs.length := length_imgComp hX hY hφ hcs
  have hcl := closed_of_mem_comps hX hcs
  have hnd := nodup_of_mem_comps hcs
  have hcl' := closed_of_mem_comps hY hds
  have hnd' := nodup_of_mem_comps hds
  have hmem : ∀ i < cs.length, act φ (cs.getD i 0) ∈ ds := fun i hi =>
    (mem_imgComp hX hY hφ hcs).2 ⟨_, getD_mem hi, rfl⟩
  let σ : Fin cs.length → Fin cs.length := fun i =>
    ⟨ds.idxOf (act φ (cs.getD i 0)), lt_of_lt_of_eq (List.idxOf_lt_length_of_mem (hmem i i.2))
      hlen⟩
  have hinj : Function.Injective σ := by
    intro i j hij
    have h := (List.idxOf_inj (hmem i i.2)).1 (congrArg Fin.val hij)
    have h' := act_injective φ h
    have := congrArg cs.idxOf h'
    rw [idxOf_getD hnd i.2, idxOf_getD hnd j.2] at this
    exact Fin.ext this
  let τ := Equiv.ofBijective σ (Finite.injective_iff_bijective.1 hinj)
  have hτ : ∀ i (hi : i < cs.length), act τ i = ds.idxOf (act φ (cs.getD i 0)) := fun i hi => by
    rw [act_of_lt _ hi]
    rfl
  refine ⟨cs.length, size_subG cs, by rw [size_subG, hlen], τ, fun i j hi hj => ?_⟩
  rw [adj_subG hcl' hnd', adj_subG hcl hnd, hτ i hi, hτ j hj, getD_idxOf (hmem i hi),
    getD_idxOf (hmem j hj), hφ _ _ (lt_of_mem_comps hX hcs (getD_mem hi))
      (lt_of_mem_comps hX hcs (getD_mem hj))]
  exact ⟨fun h => ⟨hi, hj, h.2.2⟩, fun h => ⟨List.idxOf_lt_length_of_mem (hmem i hi),
    List.idxOf_lt_length_of_mem (hmem j hj), h.2.2⟩⟩

end Invariance

/-! ### Counting components by isomorphism class -/

/-- Equally many members of each isomorphism class of component data: every Boolean invariant
of isomorphism counts the same on both lists. -/
def Balanced (X Y : GraphData) (cx cy : List (List ℕ)) : Prop :=
  ∀ p : GraphData → Bool, (∀ A B, GIso A B → p A = p B) →
    cx.countP (fun cs => p (subG X cs)) = cy.countP (fun ds => p (subG Y ds))

section Balanced

variable {X Y : GraphData}

/-- **Isomorphic graphs have balanced components.** -/
theorem balanced_comps (hX : X.ValidD Δ n) (hY : Y.ValidD Δ n) {φ : Perm (Fin n)}
    (hφ : IsIso n X Y φ) : Balanced X Y (comps n X) (comps n Y) := by
  have hperm : List.Perm ((comps n X).map (imgComp n Y φ)) (comps n Y) := by
    refine (List.perm_ext_iff_of_nodup ((nodup_comps hX).map_on fun cs hcs cs' hcs' h => ?_)
      (nodup_comps hY)).2 fun ds => ?_
    · have hr := headD_mem (ne_nil_of_mem_comps hX hcs)
      have h₁ : act φ (cs.headD 0) ∈ imgComp n Y φ cs' := by
        rw [← h, mem_imgComp hX hY hφ hcs]
        exact ⟨_, hr, rfl⟩
      obtain ⟨u, hu, hu'⟩ := (mem_imgComp hX hY hφ hcs').1 h₁
      rw [act_injective φ hu'] at hu
      exact eq_of_mem_comps hX hcs hcs' hr hu
    · rw [List.mem_map]
      constructor
      · rintro ⟨cs, hcs, rfl⟩
        exact imgComp_mem hX hY hcs
      · intro hds
        have hw := headD_mem (ne_nil_of_mem_comps hY hds)
        have hwn := lt_of_mem_comps hY hds hw
        have hcs := compOf_mem_comps hX (act_lt φ⁻¹ hwn)
        refine ⟨_, hcs, eq_of_mem_comps hY (imgComp_mem hX hY hcs) hds ?_ hw⟩
        rw [mem_imgComp hX hY hφ hcs]
        exact ⟨_, self_mem_compOf hX (act_lt φ⁻¹ hwn), act_act_inv _ _⟩
  intro p hp
  rw [← hperm.countP_eq, List.countP_map]
  refine List.countP_congr fun cs hcs => ?_
  simp only [Function.comp_apply, hp _ _ (giso_imgComp hX hY hφ hcs)]

theorem Balanced.perm {cx cy cy' : List (List ℕ)} (h : Balanced X Y cx cy)
    (hp : List.Perm cy cy') :
    Balanced X Y cx cy' := fun p hinv => (h p hinv).trans (hp.countP_eq _)

theorem class_invariant (C : GraphData) [∀ A, Decidable (GIso A C)] :
    ∀ A B, GIso A B → decide (GIso A C) = decide (GIso B C) := fun _ _ h =>
  decide_eq_decide.2 ⟨fun h' => h.symm.trans h', fun h' => h.trans h'⟩

/-- A component in the first list has a partner of the same class in the second. -/
theorem Balanced.exists {cs : List ℕ} {cx cy : List (List ℕ)} (h : Balanced X Y (cs :: cx) cy) :
    ∃ ds ∈ cy, GIso (subG X cs) (subG Y ds) := by
  classical
  have heq := h _ (class_invariant (subG X cs))
  have hpos : 0 < (cs :: cx).countP fun cs' => decide (GIso (subG X cs') (subG X cs)) :=
    List.countP_pos_iff.2 ⟨cs, List.mem_cons_self, decide_eq_true (GIso.refl _)⟩
  rw [heq] at hpos
  obtain ⟨ds, hds, hd⟩ := List.countP_pos_iff.1 hpos
  exact ⟨ds, hds, (of_decide_eq_true hd).symm⟩

/-- Removing a matched pair keeps the lists balanced. -/
theorem Balanced.step {cs ds : List ℕ} {cx cy cy' : List (List ℕ)}
    (h : Balanced X Y (cs :: cx) cy) (hp : List.Perm (ds :: cy') cy)
    (hg : GIso (subG X cs) (subG Y ds)) :
    Balanced X Y cx cy' := by
  intro p hinv
  have := h p hinv
  rw [← hp.countP_eq, List.countP_cons, List.countP_cons, hinv _ _ hg] at this
  omega

/-- Nothing is balanced against the empty list but the empty list. -/
theorem Balanced.eq_nil {cy : List (List ℕ)} (h : Balanced X Y [] cy) : cy = [] := by
  classical
  rcases cy with _ | ⟨ds, cy⟩
  · rfl
  · have := h _ (class_invariant (subG Y ds))
    have hd : decide (GIso (subG Y ds) (subG Y ds)) = true := decide_eq_true (GIso.refl _)
    rw [List.countP_nil, List.countP_cons] at this
    simp only [hd, ↓reduceIte] at this
    omega

end Balanced

/-! ### Gluing -/

/-- The writes of a matched pair `(cs, ds, arr)`: `cs[i] ↦ ds[arr[i]]`. -/
def glueWrites (t : List ℕ × List ℕ × Array ℕ) : List (ℕ × ℕ) :=
  (List.range t.1.length).map fun i => (t.1.getD i 0, t.2.1.getD (get t.2.2 i) 0)

/-- The array of `n` zeros after the writes `ws`. -/
def glue (n : ℕ) (ws : List (ℕ × ℕ)) : Array ℕ :=
  Cost.Prim.applyWrites (a := .nat) (Array.replicate n 0) ws

/-- A matched pair of components, with the values of an isomorphism of their data. -/
def MatchOk (X Y : GraphData) (t : List ℕ × List ℕ × Array ℕ) : Prop :=
  t.2.1.length = t.1.length ∧ ∃ σ : Perm (Fin t.1.length),
    IsIso t.1.length (subG X t.1) (subG Y t.2.1) σ ∧ ∀ i < t.1.length, get t.2.2 i = act σ i

theorem map_getD_range (l : List ℕ) : (List.range l.length).map (l.getD · 0) = l := by
  refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
  simp only [List.getElem_map, List.getElem_range]
  exact getD_of_lt h₂

theorem nodup_flatten_comps (hG : G.ValidD Δ n) : (comps n G).flatten.Nodup := by
  refine List.nodup_flatten.2 ⟨fun _ h => nodup_of_mem_comps h,
    (nodup_comps hG).pairwise_of_forall_ne fun a ha b hb hab => ?_⟩
  exact List.disjoint_left.2 fun _ hva hvb => hab (eq_of_mem_comps hG ha hb hva hvb)

section Glue

variable {X Y : GraphData} (hX : X.ValidD Δ n) (hY : Y.ValidD Δ n)
  {M : List (List ℕ × List ℕ × Array ℕ)} (hx : List.Perm (M.map (·.1)) (comps n X))
  (hy : List.Perm (M.map (·.2.1)) (comps n Y)) (hM : ∀ t ∈ M, MatchOk X Y t)
  {ws : List (ℕ × ℕ)} (hws : List.Perm ws (M.flatMap glueWrites))
include hX hY hx hy hM hws

/-- **Gluing.** Matched components with isomorphisms of their data give an isomorphism: the
writes of the pairs, in any order. -/
theorem glue_spec :
    (glue n ws).size = n ∧
      ∃ φ : Perm (Fin n), IsIso n X Y φ ∧ ∀ v < n, get (glue n ws) v = act φ v := by
  have hsize : (glue n ws).size = n := by
    rw [glue, size_applyWrites, Array.size_replicate]
  have hcx : ∀ t ∈ M, t.1 ∈ comps n X := fun t ht => hx.mem_iff.1 (List.mem_map_of_mem ht)
  have hcy : ∀ t ∈ M, t.2.1 ∈ comps n Y := fun t ht => hy.mem_iff.1 (List.mem_map_of_mem ht)
  have hinjx := List.inj_on_of_nodup_map (hx.nodup_iff.2 (nodup_comps hX))
  have hinjy := List.inj_on_of_nodup_map (hy.nodup_iff.2 (nodup_comps hY))
  -- the written keys are the points, each once
  have hkeys : (ws.map Prod.fst).Nodup := by
    refine ((hws.map Prod.fst).nodup_iff).2 ?_
    rw [List.map_flatMap]
    have : M.flatMap (fun t => (glueWrites t).map Prod.fst) = (M.map (·.1)).flatten := by
      rw [← List.flatMap_def]
      refine List.flatMap_congr fun t _ => ?_
      rw [glueWrites, List.map_map]
      exact map_getD_range t.1
    rw [this]
    exact (hx.flatten).nodup_iff.2 (nodup_flatten_comps hX)
  -- the values on the points
  have hlt : ∀ t ∈ M, ∀ i < t.1.length, get t.2.2 i < t.2.1.length := by
    intro t ht i hi
    obtain ⟨hl, σ, -, hσ⟩ := hM t ht
    rw [hσ i hi, hl]
    exact act_lt σ hi
  have hval : ∀ t ∈ M, ∀ i < t.1.length,
      get (glue n ws) (t.1.getD i 0) = t.2.1.getD (get t.2.2 i) 0 := by
    intro t ht i hi
    have hmem : (t.1.getD i 0, t.2.1.getD (get t.2.2 i) 0) ∈ ws :=
      hws.mem_iff.2 (List.mem_flatMap.2 ⟨t, ht, List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩⟩)
    have hk : t.1.getD i 0 < (Array.replicate n 0).size := by
      rw [Array.size_replicate]
      exact lt_of_mem_comps hX (hcx t ht) (getD_mem hi)
    have := getElem?_applyWrites_of_mem (a := .nat) (Array.replicate n 0) hkeys hmem hk
    rw [get, Array.getD_eq_getD_getElem?, glue, this, Option.getD_some]
  have hpos : ∀ v < n, ∃ t ∈ M, ∃ i < t.1.length, t.1.getD i 0 = v := by
    intro v hv
    obtain ⟨cs, hcs, hvc⟩ := exists_mem_comps hX hv
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 (hx.mem_iff.2 hcs)
    exact ⟨t, ht, _, List.idxOf_lt_length_of_mem hvc, getD_idxOf hvc⟩
  have himg : ∀ t ∈ M, ∀ i < t.1.length, get (glue n ws) (t.1.getD i 0) ∈ t.2.1 :=
    fun t ht i hi => by
      rw [hval t ht i hi]
      exact getD_mem (hlt t ht i hi)
  have hrange : ∀ v < n, get (glue n ws) v < n := by
    intro v hv
    obtain ⟨t, ht, i, hi, rfl⟩ := hpos v hv
    exact lt_of_mem_comps hY (hcy t ht) (himg t ht i hi)
  -- injective on the points
  let F : Fin n → Fin n := fun v => ⟨get (glue n ws) v, hrange v v.2⟩
  have hinj : Function.Injective F := by
    intro u v huv
    have huv' : get (glue n ws) u = get (glue n ws) v := congrArg Fin.val huv
    obtain ⟨t, ht, i, hi, hu⟩ := hpos u u.2
    obtain ⟨t', ht', j, hj, hv⟩ := hpos v v.2
    have h₁ := himg t ht i hi
    have h₂ := himg t' ht' j hj
    rw [hu, huv', ← hv] at h₁
    obtain rfl := hinjy ht ht' (eq_of_mem_comps hY (hcy t ht) (hcy t' ht') h₁ h₂)
    rw [← hu, ← hv, hval t ht i hi, hval t ht j hj] at huv'
    have hnd := nodup_of_mem_comps (hcy t ht)
    have := congrArg t.2.1.idxOf huv'
    rw [idxOf_getD hnd (hlt t ht i hi), idxOf_getD hnd (hlt t ht j hj)] at this
    obtain ⟨-, σ, -, hσ⟩ := hM t ht
    rw [hσ i hi, hσ j hj] at this
    have := act_injective σ this
    exact Fin.ext (by rw [← hu, ← hv, this])
  let φ := Equiv.ofBijective F (Finite.injective_iff_bijective.1 hinj)
  have hφ : ∀ v < n, act φ v = get (glue n ws) v := fun v hv => by
    rw [act_of_lt _ hv]
    rfl
  refine ⟨hsize, φ, fun u v hu hv => ?_, fun v hv => (hφ v hv).symm⟩
  rw [hφ u hu, hφ v hv]
  obtain ⟨t, ht, i, hi, rfl⟩ := hpos u hu
  obtain ⟨t', ht', j, hj, rfl⟩ := hpos v hv
  by_cases htt : t = t'
  · subst htt
    obtain ⟨hl, σ, hσi, hσ⟩ := hM t ht
    have hcl := closed_of_mem_comps hX (hcx t ht)
    have hnd := nodup_of_mem_comps (hcx t ht)
    have hcl' := closed_of_mem_comps hY (hcy t ht)
    have hnd' := nodup_of_mem_comps (hcy t ht)
    have := hσi i j hi hj
    rw [adj_subG hcl' hnd', adj_subG hcl hnd, ← hσ i hi, ← hσ j hj] at this
    rw [hval t ht i hi, hval t ht j hj]
    exact ⟨fun h => (this.1 ⟨hlt t ht i hi, hlt t ht j hj, h⟩).2.2,
      fun h => (this.2 ⟨hi, hj, h⟩).2.2⟩
  · refine iff_of_false (fun h => htt ?_) (fun h => htt ?_)
    · have h₁ := himg t ht i hi
      have h₂ := closed_of_mem_comps hY (hcy t ht) _ h₁ _ h
      exact hinjy ht ht' (eq_of_mem_comps hY (hcy t ht) (hcy t' ht') h₂ (himg t' ht' j hj))
    · have h₂ := closed_of_mem_comps hX (hcx t ht) _ (getD_mem hi) _ h
      exact hinjx ht ht' (eq_of_mem_comps hX (hcx t ht) (hcx t' ht') h₂ (getD_mem hj))

end Glue

end GraphIso.Graph
