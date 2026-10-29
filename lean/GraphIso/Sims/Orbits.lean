module

public import GraphIso.Sims.Ops

/-!
# Orbit searches on generators

`orbitBFS n gs u` searches from `u`, applying the generators to the popped points, with a
visited mask. It returns pairs `(v, r_v)`, one per orbit point, with `r_v ∈ ⟨gs⟩` and
`r_v u = v` (`r_{g v} = g r_v`). The points reached are closed under the generators, hence
under `⟨gs⟩` (`isInvariant_closure_iff`): they are exactly the orbit (`orbitBFS_spec`).
Each iteration pops one queued point, and each point is queued once, so `n` iterations
suffice (the potential `|queue| + (n − |found|)` drops at each).

`orbitsModel n gs w` searches from each window point not yet seen and records the orbit
(`orbitsModel_spec`: an exact orbit partition of an invariant window).
-/

@[expose] public section

namespace GraphIso.Sims

open Equiv

/-- A search state: visited mask, queue, found pairs. -/
abbrev OState := Array Bool × List (ℕ × PermData) × List (ℕ × PermData)

/-- Visit the image of the popped point `v`, reached by `r`, under the generator `g`. -/
def visitStep (v : ℕ) (r : PermData) (acc : OState) (g : PermData) : OState :=
  if getB acc.1 (get g.1 v) then acc
  else (acc.1.setIfInBounds (get g.1 v) true, (get g.1 v, g.mul r) :: acc.2.1,
    (get g.1 v, g.mul r) :: acc.2.2)

/-- One iteration: pop a point and visit its images; `none` when the queue is empty. -/
def orbitStep (gs : GensData) (st : OState) : Option OState :=
  match st.2.1 with
  | [] => none
  | p :: rest => some (gs.foldl (visitStep p.1 p.2) (st.1, rest, st.2.2))

/-- The initial state: `u` found and queued, reached by the identity. -/
def orbitInit (n u : ℕ) : OState :=
  ((Array.replicate n false).setIfInBounds u true, [(u, PermData.one n)], [(u, PermData.one n)])

/-- The orbit of `u` with transversal elements. -/
def orbitBFS (n : ℕ) (gs : GensData) (u : ℕ) : List (ℕ × PermData) :=
  (iter (orbitStep gs) (n + 1) (orbitInit n u)).2.2

/-! ### The invariant -/

/-- The invariant of the search from `u` in `G`, without the closure condition. -/
structure BInv (n : ℕ) (G : Subgroup (Perm (Fin n))) (u : ℕ) (st : OState) : Prop where
  size : st.1.size = n
  mask_iff : ∀ i < n, getB st.1 i = true ↔ i ∈ st.2.2.map Prod.fst
  nodup : (st.2.2.map Prod.fst).Nodup
  pair : ∀ p ∈ st.2.2, p.1 < n ∧ p.2.Valid n ∧ p.2.denote n ∈ G ∧ get p.2.1 u = p.1
  queue_sub : ∀ p ∈ st.2.1, p ∈ st.2.2
  queue_nodup : (st.2.1.map Prod.fst).Nodup

/-- The invariant of the search: found points not queued have all their images found. -/
structure OInv (n : ℕ) (gs : GensData) (u : ℕ) (st : OState) : Prop
    extends BInv n (GensData.denote n gs) u st where
  closed : ∀ p ∈ st.2.2, p.1 ∉ st.2.1.map Prod.fst → ∀ g ∈ gs, get g.1 p.1 ∈ st.2.2.map Prod.fst
  start : u ∈ st.2.2.map Prod.fst

/-- The potential: queued points, plus points still to be found. -/
def opot (n : ℕ) (st : OState) : ℕ := st.2.1.length + (n - st.2.2.length)

section Search

variable {n : ℕ} {gs : GensData} {u : ℕ}

theorem BInv.length_le {G : Subgroup (Perm (Fin n))} {st : OState} (h : BInv n G u st) :
    st.2.2.length ≤ n := by
  have hsub : (st.2.2.map Prod.fst).toFinset ⊆ Finset.range n := by
    intro i hi
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hi)
    exact Finset.mem_range.2 (h.pair p hp).1
  have := Finset.card_le_card hsub
  rwa [List.toFinset_card_of_nodup h.nodup, List.length_map, Finset.card_range] at this

/-- One visit keeps the invariant; the image is found afterwards; what is new is queued and
found at once. -/
theorem visitStep_spec {G : Subgroup (Perm (Fin n))} {v : ℕ} {r g : PermData} (hu : u < n)
    (hv : v < n) (hr : r.Valid n) (hrG : r.denote n ∈ G) (hru : get r.1 u = v)
    (hg : g.Valid n) (hgG : g.denote n ∈ G) {acc : OState} (hacc : BInv n G u acc) :
    BInv n G u (visitStep v r acc g) ∧ get g.1 v ∈ (visitStep v r acc g).2.2.map Prod.fst ∧
      ∃ new : List (ℕ × PermData), (visitStep v r acc g).2.1 = new ++ acc.2.1 ∧
        (visitStep v r acc g).2.2 = new ++ acc.2.2 := by
  unfold visitStep
  have hx : get g.1 v < n := hg.fwd_lt v hv
  by_cases hm : getB acc.1 (get g.1 v) = true
  · simp only [hm, ↓reduceIte]
    exact ⟨hacc, (hacc.mask_iff _ hx).1 hm, [], rfl, rfl⟩
  · simp only [hm, Bool.false_eq_true, ↓reduceIte]
    have hnot : get g.1 v ∉ acc.2.2.map Prod.fst := fun h => hm ((hacc.mask_iff _ hx).2 h)
    refine ⟨⟨by simp [hacc.size], fun i hi => ?_, ?_, fun p hp => ?_, fun p hp => ?_, ?_⟩,
      List.mem_cons_self, [(get g.1 v, g.mul r)], rfl, rfl⟩
    · simp only [getB, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, hacc.size, hx,
        ↓reduceIte, List.map_cons, List.mem_cons]
      by_cases hi' : get g.1 v = i
      · simp [hi']
      · simp only [hi', ↓reduceIte, Ne.symm hi', false_or]
        simpa [getB] using hacc.mask_iff i hi
    · exact List.nodup_cons.2 ⟨hnot, hacc.nodup⟩
    · rcases List.mem_cons.1 hp with rfl | hp
      · refine ⟨hx, hg.mul hr, ?_, ?_⟩
        · rw [PermData.denote_mul hg hr]
          exact mul_mem hgG hrG
        · show get (amap (get g.1) r.1) u = get g.1 v
          rw [get_amap (by rw [hr.size_fwd]; exact hu), hru]
      · exact hacc.pair p hp
    · rcases List.mem_cons.1 hp with rfl | hp
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hacc.queue_sub p hp)
    · refine List.nodup_cons.2 ⟨fun h => hnot ?_, hacc.queue_nodup⟩
      obtain ⟨p, hp, hpx⟩ := List.mem_map.1 h
      exact List.mem_map.2 ⟨p, hacc.queue_sub p hp, hpx⟩

theorem visit_fold {G : Subgroup (Perm (Fin n))} {v : ℕ} {r : PermData} (hu : u < n)
    (hv : v < n) (hr : r.Valid n) (hrG : r.denote n ∈ G) (hru : get r.1 u = v) :
    ∀ (l : List PermData), (∀ g ∈ l, g.Valid n ∧ g.denote n ∈ G) → ∀ acc, BInv n G u acc →
      BInv n G u (l.foldl (visitStep v r) acc) ∧
        (∀ g ∈ l, get g.1 v ∈ (l.foldl (visitStep v r) acc).2.2.map Prod.fst) ∧
        ∃ new : List (ℕ × PermData), (l.foldl (visitStep v r) acc).2.1 = new ++ acc.2.1 ∧
          (l.foldl (visitStep v r) acc).2.2 = new ++ acc.2.2
  | [], _, acc, hacc => ⟨hacc, fun _ h => absurd h List.not_mem_nil, [], rfl, rfl⟩
  | g :: l, hl, acc, hacc => by
    obtain ⟨hg, hgG⟩ := hl g List.mem_cons_self
    obtain ⟨h₁, himg, new₁, hq₁, hf₁⟩ := visitStep_spec hu hv hr hrG hru hg hgG hacc
    obtain ⟨h₂, himgs, new₂, hq₂, hf₂⟩ :=
      visit_fold hu hv hr hrG hru l (fun g' hg' => hl g' (List.mem_cons_of_mem _ hg')) _ h₁
    rw [List.foldl_cons]
    refine ⟨h₂, fun g' hg' => ?_, new₂ ++ new₁, by rw [hq₂, hq₁, List.append_assoc],
      by rw [hf₂, hf₁, List.append_assoc]⟩
    rcases List.mem_cons.1 hg' with rfl | hg'
    · rw [hf₂, List.map_append]
      exact List.mem_append_right _ himg
    · exact himgs g' hg'

/-- **One iteration** keeps the invariant and decreases the potential. -/
theorem orbitStep_spec (hu : u < n) (hgs : GensData.AllValid n gs) {st : OState}
    (hI : OInv n gs u st) {p : ℕ × PermData} {rest : List (ℕ × PermData)}
    (hq : st.2.1 = p :: rest) :
    ∃ st', orbitStep gs st = some st' ∧ OInv n gs u st' ∧ opot n st' + 1 ≤ opot n st := by
  obtain ⟨mask, queue, found⟩ := st
  simp only at hq
  subst hq
  have hp := hI.queue_sub p List.mem_cons_self
  obtain ⟨hpn, hpv, hpG, hpu⟩ := hI.pair p hp
  have h₀ : BInv n (GensData.denote n gs) u (mask, rest, found) :=
    ⟨hI.size, hI.mask_iff, hI.nodup, hI.pair,
      fun q hq => hI.queue_sub q (List.mem_cons_of_mem _ hq),
      (List.nodup_cons.1 hI.queue_nodup).2⟩
  obtain ⟨h₁, himg, new, hq', hf'⟩ := visit_fold hu hpn hpv hpG hpu gs
    (fun g hg => ⟨hgs g hg, GensData.mem_denote_of_mem hg⟩) _ h₀
  refine ⟨_, rfl, ⟨h₁, fun q hq hqn g hg => ?_, ?_⟩, ?_⟩
  · simp only [hf'] at hq ⊢
    simp only [hq'] at hqn
    rcases List.mem_append.1 hq with hq | hq
    · exact absurd (List.mem_map.2 ⟨q, hq, rfl⟩) fun h => hqn (by
        rw [List.map_append]; exact List.mem_append_left _ h)
    · by_cases hqp : q.1 = p.1
      · rw [hqp, ← hf']
        exact himg g hg
      · have hnot : q.1 ∉ (p :: rest).map Prod.fst := by
          rw [List.map_cons, List.mem_cons, not_or]
          refine ⟨hqp, fun h => hqn ?_⟩
          rw [List.map_append]
          exact List.mem_append_right _ h
        rw [List.map_append]
        exact List.mem_append_right _ (hI.closed q hq hnot g hg)
  · simp only [hf', List.map_append]
    exact List.mem_append_right _ hI.start
  · have hlen := h₁.length_le
    simp only [opot, hq', hf', List.length_append, List.length_cons] at hlen ⊢
    omega

theorem iter_orbitStep (hu : u < n) (hgs : GensData.AllValid n gs) :
    ∀ (m : ℕ) (st : OState), OInv n gs u st → opot n st < m →
      OInv n gs u (iter (orbitStep gs) m st) ∧ (iter (orbitStep gs) m st).2.1 = []
  | 0, _, _, hm => absurd hm (Nat.not_lt_zero _)
  | m + 1, st, hI, hm => by
    rcases hq : st.2.1 with _ | ⟨p, rest⟩
    · have hstep : orbitStep gs st = none := by simp [orbitStep, hq]
      simp only [iter, hstep]
      exact ⟨hI, hq⟩
    · obtain ⟨st', hstep, hI', hpot⟩ := orbitStep_spec hu hgs hI hq
      simp only [iter, hstep]
      exact iter_orbitStep hu hgs m st' hI' (by omega)

theorem orbitInit_inv (hu : u < n) : OInv n gs u (orbitInit n u) := by
  refine ⟨⟨by simp [orbitInit], fun i hi => ?_, by simp [orbitInit], fun p hp => ?_,
    fun p hp => by simpa [orbitInit] using hp, by simp [orbitInit]⟩, fun p hp hpq => ?_,
    by simp [orbitInit]⟩
  · simp only [orbitInit, getB, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds,
      Array.size_replicate, hu, ↓reduceIte, Array.getElem?_replicate, hi, List.map_cons,
      List.map_nil, List.mem_singleton]
    by_cases h : u = i
    · simp [h]
    · simp [h, Ne.symm h]
  · simp only [orbitInit, List.mem_singleton] at hp
    subst hp
    refine ⟨hu, PermData.valid_one n, by rw [PermData.denote_one]; exact one_mem _, ?_⟩
    exact get_range hu
  · simp only [orbitInit, List.mem_singleton] at hp
    subst hp
    simp [orbitInit] at hpq

/-- **The search finds the orbit**, with an element of `⟨gs⟩` reaching each point. -/
theorem orbitBFS_spec (hu : u < n) (hgs : GensData.AllValid n gs) :
    ((orbitBFS n gs u).map Prod.fst).Nodup ∧
      (∀ j, j ∈ (orbitBFS n gs u).map Prod.fst ↔ SameOrbit (GensData.denote n gs) u j) ∧
      ∀ p ∈ orbitBFS n gs u, p.2.Valid n ∧ p.2.denote n ∈ GensData.denote n gs ∧
        get p.2.1 u = p.1 := by
  have hpot : opot n (orbitInit n u) < n + 1 := by
    simp only [opot, orbitInit, List.length_singleton]
    omega
  obtain ⟨hI, hq⟩ := iter_orbitStep hu hgs (n + 1) (orbitInit n u) (orbitInit_inv hu) hpot
  set st := iter (orbitStep gs) (n + 1) (orbitInit n u)
  refine ⟨hI.nodup, fun j => ⟨fun hj => ?_, fun hj => ?_⟩,
    fun p hp => (hI.pair p hp).2⟩
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hj
    obtain ⟨hpn, hpv, hpG, hpu⟩ := hI.pair p hp
    exact ⟨hu, hpn, p.2.denote n, hpG, Fin.ext (by rw [PermData.val_denote_apply hpv, hpu])⟩
  · -- the found points are invariant under the generators, hence under `⟨gs⟩`
    let W : Set (Fin n) := {i | i.val ∈ st.2.2.map Prod.fst}
    have hinv : IsInvariant (GensData.denote n gs) W := by
      rw [GensData.denote, isInvariant_closure_iff (Set.toFinite W)]
      rintro _ ⟨g, hg, rfl⟩ i hi
      obtain ⟨p, hp, hpi⟩ := List.mem_map.1 (show i.val ∈ st.2.2.map Prod.fst from hi)
      have := hI.closed p hp (by rw [hq]; exact List.not_mem_nil) g hg
      show (PermData.denote n g i).val ∈ st.2.2.map Prod.fst
      rw [PermData.val_denote_apply (hgs g hg), ← hpi]
      exact this
    obtain ⟨_, hj', g, hg, hgu⟩ := hj
    have := hinv g hg ⟨u, hu⟩ hI.start
    rw [hgu] at this
    exact this

end Search

/-! ### The orbits of a window -/

/-- Record the orbit of `p` unless `p` was seen. -/
def orbitsStep (n : ℕ) (gs : GensData) (acc : Array Bool × List (List ℕ)) (p : ℕ) :
    Array Bool × List (List ℕ) :=
  if getB acc.1 p then acc
  else (Cost.Prim.applyWrites (a := .bool) acc.1
      (((orbitBFS n gs p).map Prod.fst).map fun i => (i, true)),
    ((orbitBFS n gs p).map Prod.fst) :: acc.2)

/-- The orbits of the window points. -/
def orbitsModel (n : ℕ) (gs : GensData) (w : WinData) : List (List ℕ) :=
  (w.1.foldl (orbitsStep n gs) (Array.replicate n false, [])).2

theorem getB_applyWrites_true {n : ℕ} :
    ∀ (l : List ℕ) (a : Array Bool), a.size = n →
      (Cost.Prim.applyWrites (a := .bool) a (l.map fun i => (i, true))).size = n ∧
      ∀ i < n, (getB (Cost.Prim.applyWrites (a := .bool) a (l.map fun i => (i, true))) i = true ↔
        getB a i = true ∨ i ∈ l)
  | [], a, ha => ⟨ha, fun i _ => by simp [Cost.Prim.applyWrites]⟩
  | j :: l, a, ha => by
    have hs : (a.setIfInBounds j true).size = n := by simp [ha]
    obtain ⟨h₁, h₂⟩ := getB_applyWrites_true l (a.setIfInBounds j true) hs
    refine ⟨h₁, fun i hi => ?_⟩
    have e : Cost.Prim.applyWrites (a := .bool) a ((j :: l).map fun i => (i, true)) =
        Cost.Prim.applyWrites (a := .bool) (a.setIfInBounds j true) (l.map fun i => (i, true)) :=
      rfl
    rw [e, h₂ i hi, List.mem_cons]
    simp only [getB, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, ha]
    by_cases hji : j = i
    · subst hji
      simp [hi]
    · simp only [hji, ↓reduceIte, Ne.symm hji, false_or]

/-- The invariant of the orbit fold. -/
structure OsInv (n : ℕ) (G : Subgroup (Perm (Fin n))) (w : WinData)
    (acc : Array Bool × List (List ℕ)) : Prop where
  size : acc.1.size = n
  seen_iff : ∀ i < n, getB acc.1 i = true ↔ i ∈ acc.2.flatten
  nodup : acc.2.flatten.Nodup
  orbit : ∀ o ∈ acc.2, o ≠ [] ∧ ∀ i ∈ o, ∀ j, j ∈ o ↔ SameOrbit G i j
  sub : ∀ i ∈ acc.2.flatten, i ∈ w.1

section Window

variable {n : ℕ} {gs : GensData} {w : WinData}

theorem orbits_fold (hgs : GensData.AllValid n gs) (hw : w.Valid n)
    (hinv : IsInvariant (GensData.denote n gs) (w.denote n)) :
    ∀ (l : List ℕ) (acc : Array Bool × List (List ℕ)), (∀ p ∈ l, p ∈ w.1) →
      OsInv n (GensData.denote n gs) w acc →
      OsInv n (GensData.denote n gs) w (l.foldl (orbitsStep n gs) acc) ∧
        ∀ p ∈ l, p ∈ (l.foldl (orbitsStep n gs) acc).2.flatten
  | [], acc, _, hacc => ⟨hacc, fun _ h => absurd h List.not_mem_nil⟩
  | p :: l, acc, hl, hacc => by
    have hpw := hl p List.mem_cons_self
    have hpn := hw.lt p hpw
    -- after processing `p`, it has been recorded
    have hstep : OsInv n (GensData.denote n gs) w (orbitsStep n gs acc p) ∧
        p ∈ (orbitsStep n gs acc p).2.flatten ∧
        ∀ i ∈ acc.2.flatten, i ∈ (orbitsStep n gs acc p).2.flatten := by
      unfold orbitsStep
      by_cases hseen : getB acc.1 p = true
      · simp only [hseen, ↓reduceIte]
        exact ⟨hacc, (hacc.seen_iff p hpn).1 hseen, fun i hi => hi⟩
      · simp only [hseen, Bool.false_eq_true, ↓reduceIte]
        obtain ⟨hnd, hiff, -⟩ := orbitBFS_spec hpn hgs
        set o := (orbitBFS n gs p).map Prod.fst
        have hpo : p ∈ o := (hiff p).2 (sameOrbit_refl hpn)
        have hdisj : ∀ j ∈ o, j ∉ acc.2.flatten := by
          intro j hj hjf
          obtain ⟨o', ho', hjo'⟩ := List.mem_flatten.1 hjf
          have hpo' : p ∈ o' := ((hacc.orbit o' ho').2 j hjo' p).2 ((hiff j).1 hj).symm
          exact hseen ((hacc.seen_iff p hpn).2 (List.mem_flatten.2 ⟨o', ho', hpo'⟩))
        obtain ⟨hsz, hseen'⟩ := getB_applyWrites_true o acc.1 hacc.size
        refine ⟨⟨hsz, fun i hi => ?_, ?_, fun o' ho' => ?_, fun i hi => ?_⟩, ?_, fun i hi => ?_⟩
        · rw [hseen' i hi, hacc.seen_iff i hi, List.flatten_cons, List.mem_append]
          exact Or.comm
        · rw [List.flatten_cons]
          exact List.nodup_append.2 ⟨hnd, hacc.nodup, fun a ha b hb hab => hdisj a ha (hab ▸ hb)⟩
        · rcases List.mem_cons.1 ho' with rfl | ho'
          · refine ⟨List.ne_nil_of_mem hpo, fun i hi j => ?_⟩
            have hpi := (hiff i).1 hi
            rw [hiff j]
            exact ⟨fun h => hpi.symm.trans h, fun h => hpi.trans h⟩
          · exact hacc.orbit o' ho'
        · rw [List.flatten_cons, List.mem_append] at hi
          rcases hi with hi | hi
          · exact SameOrbit.mem_of_invariant hinv ((hiff i).1 hi) hpw
          · exact hacc.sub i hi
        · rw [List.flatten_cons]
          exact List.mem_append_left _ hpo
        · rw [List.flatten_cons]
          exact List.mem_append_right _ hi
    obtain ⟨h₁, h₂, h₃⟩ := hstep
    obtain ⟨h₄, h₅⟩ := orbits_fold hgs hw hinv l _ (fun q hq => hl q (List.mem_cons_of_mem _ hq)) h₁
    rw [List.foldl_cons]
    refine ⟨h₄, fun q hq => ?_⟩
    rcases List.mem_cons.1 hq with rfl | hq
    · -- recorded orbits are kept
      suffices ∀ (l : List ℕ) (acc' : Array Bool × List (List ℕ)) (i : ℕ),
          i ∈ acc'.2.flatten → i ∈ (l.foldl (orbitsStep n gs) acc').2.flatten from this l _ _ h₂
      intro l
      induction l with
      | nil => exact fun _ _ h => h
      | cons x l ih =>
        intro acc' i hi
        rw [List.foldl_cons]
        refine ih _ i ?_
        unfold orbitsStep
        split
        · exact hi
        · rw [List.flatten_cons]
          exact List.mem_append_right _ hi
    · exact h₅ q hq

/-- **The orbits of an invariant window.** -/
theorem orbitsModel_spec (hgs : GensData.AllValid n gs) (hw : w.Valid n)
    (hinv : IsInvariant (GensData.denote n gs) (w.denote n)) :
    IsOrbitPartition (GensData.denote n gs) w (orbitsModel n gs w) := by
  have h₀ : OsInv n (GensData.denote n gs) w (Array.replicate n false, []) :=
    ⟨by simp, fun i hi => by simp [getB, hi], List.nodup_nil,
      fun o ho => absurd ho List.not_mem_nil,
      fun i hi => absurd hi (by simp)⟩
  obtain ⟨hI, hall⟩ := orbits_fold hgs hw hinv w.1 _ (fun p hp => hp) h₀
  refine ⟨(List.perm_ext_iff_of_nodup hI.nodup hw.nodup).2 fun i => ⟨hI.sub i, hall i⟩,
    hI.orbit⟩

end Window

end GraphIso.Sims
