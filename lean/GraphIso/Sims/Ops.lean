module

public import GraphIso.Sims.Construct
public import GraphIso.GroupOps.Interface

/-!
# Operations read off a complete table

A window `w` gives the base order `frontBase n w`: the window's points in list order, then the
other points in increasing order. With the complete table `tableFor n w gs` of `G = ⟨gs⟩` for
that base, `Γ_k` is the pointwise stabilizer of the first `k` base points, so:

* `generate` (`k = 0`, the empty window): the entries generate `G`;
* `stabilizer u` (the window `[u]`, `k = 1`): the entries in rows `≥ 1` generate `G_u`;
* `kernel w` (`k = |w|`): the entries in rows `≥ |w|` generate the pointwise stabilizer of `w`;
* `mem π`: `π ∈ G` exactly when it sifts (`memModel_iff`);
* `lift w π'`: in row `i < |w|`, the entry for the required image `cur⁻¹ (w[π' i])` exists
  whenever some element of `G` restricts to `π'`, and the product of these entries restricts
  to `π'` (`liftModel_spec`).

Each output group has at most `n²` generators (`length_entriesFrom_le`).
-/

@[expose] public section

namespace GraphIso.Sims

open Equiv

/-! ### Base orders listing a window first -/

/-- The base order: the window's points in list order, then the remaining points. -/
def frontBase (n : ℕ) (w : WinData) : Array ℕ :=
  (w.1 ++ (List.range n).filter fun i => !getB w.2 i).toArray

section Base

variable {n : ℕ} {w : WinData}

theorem BaseOrder.of_perm {b : Array ℕ} (h : b.toList.Perm (List.range n)) : BaseOrder n b := by
  have hlen : b.size = n := by
    rw [← Array.length_toList, h.length_eq, List.length_range]
  refine ⟨hlen, h.nodup_iff.2 List.nodup_range, fun k hk => ?_⟩
  have hk' : k < b.toList.length := by rw [Array.length_toList, hlen]; exact hk
  have hmem : b.toList[k] ∈ List.range n := h.subset (List.getElem_mem hk')
  rw [List.mem_range] at hmem
  rwa [get_eq_getElem (by rw [hlen]; exact hk), ← Array.getElem_toList]

theorem frontBase_perm (hw : w.Valid n) : (frontBase n w).toList.Perm (List.range n) := by
  have hfilter : ((List.range n).filter fun i => !getB w.2 i) =
      (List.range n).filter fun i => !decide (i ∈ w.1) := by
    refine List.filter_congr fun i hi => ?_
    rw [List.mem_range] at hi
    have := hw.mask_iff i hi
    cases hb : getB w.2 i <;> simp_all
  have hin : ((List.range n).filter fun i => decide (i ∈ w.1)).Perm w.1 := by
    refine (List.perm_ext_iff_of_nodup (List.nodup_range.filter _) hw.nodup).2 fun i => ?_
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨hw.lt i h, h⟩⟩
  rw [frontBase, List.toList_toArray, hfilter]
  exact (hin.symm.append_right _).trans (List.filter_append_perm _ _)

theorem frontBase_base (hw : w.Valid n) : BaseOrder n (frontBase n w) :=
  BaseOrder.of_perm (frontBase_perm hw)

theorem get_frontBase {i : ℕ} (hi : i < w.1.length) : get (frontBase n w) i = w.1.getD i 0 := by
  rw [frontBase, get_toArray, List.getD_eq_getElem?_getD, List.getElem?_append_left hi,
    List.getD_eq_getElem?_getD]

/-- The empty window. -/
def emptyWin (n : ℕ) : WinData := ([], Array.replicate n false)

theorem emptyWin_valid (n : ℕ) : (emptyWin n).Valid n :=
  ⟨by simp [emptyWin], List.nodup_nil, by simp [emptyWin],
    fun i hi => by simp [emptyWin, getB, hi]⟩

/-- The one-point window `[u]`. -/
def pointWin (n u : ℕ) : WinData := ([u], (Array.replicate n false).setIfInBounds u true)

theorem pointWin_valid {u : ℕ} (hu : u < n) : (pointWin n u).Valid n := by
  refine ⟨by simp [pointWin], List.nodup_singleton u, by simpa [pointWin] using hu,
    fun i hi => ?_⟩
  simp only [pointWin, getB, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds,
    Array.size_replicate, Array.getElem?_replicate, List.mem_singleton]
  by_cases h : u = i
  · subst h
    simp [hu]
  · simp [h, hi, Ne.symm h]

end Base

/-! ### Tables for a window-first base -/

/-- The construction for `⟨gs⟩` with the base order listing `w` first. -/
def tableFor (n : ℕ) (w : WinData) (gs : GensData) : State := build n (frontBase n w) gs

/-- The entries in rows `≥ k`, as generators. -/
def entriesFrom (k : ℕ) (ent : List Item) : GensData :=
  (ent.filter fun e => !decide (e.1 < k)).map Prod.snd

section Tables

variable {n : ℕ} {w : WinData} {gs : GensData}

theorem tableFor_inv (hw : w.Valid n) (hgs : GensData.AllValid n gs) :
    Inv n (frontBase n w) gs (tableFor n w gs) :=
  (build_spec (frontBase_base hw) hgs).1

theorem complete_tableFor (hw : w.Valid n) (hgs : GensData.AllValid n gs) :
    Complete n (frontBase n w) (GensData.denote n gs) (tableFor n w gs).1 :=
  complete_build (frontBase_base hw) hgs

theorem entriesFrom_valid (hw : w.Valid n) (hgs : GensData.AllValid n gs) (k : ℕ) :
    GensData.AllValid n (entriesFrom k (tableFor n w gs).2.1) := by
  intro g hg
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hg
  exact ((tableFor_inv hw hgs).entry_facts (List.mem_filter.1 he).1).2.1

theorem length_entriesFrom_le (hw : w.Valid n) (hgs : GensData.AllValid n gs) (k : ℕ) :
    (entriesFrom k (tableFor n w gs).2.1).length ≤ n * n := by
  rw [entriesFrom, List.length_map]
  exact (List.length_filter_le _ _).trans (tableFor_inv hw hgs).length_le

/-- **The entries in rows `≥ k` generate the pointwise stabilizer of the first `k` base
points.** -/
theorem mem_denote_entriesFrom (hw : w.Valid n) (hgs : GensData.AllValid n gs) (k : ℕ)
    (x : Perm (Fin n)) :
    x ∈ GensData.denote n (entriesFrom k (tableFor n w gs).2.1) ↔
      x ∈ GensData.denote n gs ∧
        ∀ i < k, act x (get (frontBase n w) i) = get (frontBase n w) i := by
  have hI := tableFor_inv hw hgs
  have hC := complete_tableFor hw hgs
  have hset : GensData.denoteSet n (entriesFrom k (tableFor n w gs).2.1) =
      entries n (tableFor n w gs).1 k := by
    rw [← hI.denoteSet_filter k, entriesFrom]
    congr 2
    exact List.filter_congr fun e _ => by
      by_cases h : e.1 < k
      · simp [h, Nat.not_le.2 h]
      · simp [h, Nat.le_of_not_lt h]
  rw [GensData.denote, hset, mem_closure_entries_iff hC.wf hC.closed, hC.gamma_iff]

end Tables

/-! ### Generation, stabilizers, kernels and membership -/

/-- `generate`: the entries of the table for the base `0, …, n − 1`. -/
def generateModel (n : ℕ) (gs : GensData) : GensData :=
  entriesFrom 0 (tableFor n (emptyWin n) gs).2.1

/-- `stabilizer u`: the entries in rows `≥ 1` for a base starting with `u`. -/
def stabModel (n : ℕ) (gs : GensData) (u : ℕ) : GensData :=
  entriesFrom 1 (tableFor n (pointWin n u) gs).2.1

/-- `kernel w`: the entries in rows `≥ |w|` for a base listing `w` first. -/
def kernelModel (n : ℕ) (gs : GensData) (w : WinData) : GensData :=
  entriesFrom w.1.length (tableFor n w gs).2.1

/-- `mem π`: does `π` sift? -/
def memModel (n : ℕ) (gs : GensData) (π : PermData) : Bool :=
  (sift n (frontBase n (emptyWin n)) (tableFor n (emptyWin n) gs).1 0 π).1 == n

section Specs

variable {n : ℕ} {gs : GensData}

theorem generateModel_spec (hgs : GensData.AllValid n gs) :
    GensData.AllValid n (generateModel n gs) ∧
      GensData.denote n (generateModel n gs) = GensData.denote n gs ∧
      (generateModel n gs).length ≤ n * n := by
  refine ⟨entriesFrom_valid (emptyWin_valid n) hgs 0, ?_,
    length_entriesFrom_le (emptyWin_valid n) hgs 0⟩
  ext x
  rw [generateModel, mem_denote_entriesFrom (emptyWin_valid n) hgs]
  simp

theorem stabModel_spec (hgs : GensData.AllValid n gs) {u : ℕ} (hu : u < n) :
    GensData.AllValid n (stabModel n gs u) ∧
      GensData.denote n (stabModel n gs u) = pointStab (GensData.denote n gs) ⟨u, hu⟩ ∧
      (stabModel n gs u).length ≤ n * n := by
  have hw := pointWin_valid hu
  refine ⟨entriesFrom_valid hw hgs 1, ?_, length_entriesFrom_le hw hgs 1⟩
  ext x
  have hb0 : get (frontBase n (pointWin n u)) 0 = u := by
    rw [get_frontBase (by simp [pointWin])]
    rfl
  rw [stabModel, mem_denote_entriesFrom hw hgs, mem_pointStab]
  simp only [Nat.lt_one_iff, forall_eq, hb0]
  rw [act_of_lt _ hu]
  exact and_congr_right fun _ => ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩

theorem kernelModel_spec (hgs : GensData.AllValid n gs) {w : WinData} (hw : w.Valid n) :
    GensData.AllValid n (kernelModel n gs w) ∧
      GensData.denote n (kernelModel n gs w) =
        pointwiseStab (GensData.denote n gs) (w.denote n) ∧
      (kernelModel n gs w).length ≤ n * n := by
  refine ⟨entriesFrom_valid hw hgs _, ?_, length_entriesFrom_le hw hgs _⟩
  ext x
  rw [kernelModel, mem_denote_entriesFrom hw hgs, mem_pointwiseStab]
  refine and_congr_right fun _ => ⟨fun h u hu => ?_, fun h i hi => ?_⟩
  · obtain ⟨i, hi, hiu⟩ := List.getElem_of_mem (show u.val ∈ w.1 from hu)
    have := h i hi
    rw [get_frontBase hi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
      Option.getD_some, hiu, act_of_lt _ u.2] at this
    exact Fin.ext this
  · rw [get_frontBase hi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
      Option.getD_some]
    have hlt := hw.lt _ (List.getElem_mem hi)
    rw [act_of_lt _ hlt, h ⟨_, hlt⟩ (List.getElem_mem hi)]

theorem memModel_iff (hgs : GensData.AllValid n gs) {π : PermData} (hπ : π.Valid n) :
    memModel n gs π = true ↔ π.denote n ∈ GensData.denote n gs := by
  have hC := complete_tableFor (emptyWin_valid n) hgs
  rw [memModel, beq_iff_eq, sift_eq_iff hC.wf hπ (Nat.zero_le n) (fun i hi => absurd hi (by omega)),
    hC.gamma_iff]
  simp

end Specs

/-! ### Lifting a permutation of window indices -/

/-- One row of the lift: multiply by the entry for the required image of the row's point. -/
def liftStep (T : Table) (wa : Array ℕ) (π' : PermData) (cur : PermData) (i : ℕ) : PermData :=
  match slot T i (get cur.2 (get wa (get π'.1 i))) with
  | none => cur
  | some σ => cur.mul σ

/-- `lift w π'`: a product of entries of the table for the base listing `w` first. -/
def liftModel (n : ℕ) (gs : GensData) (w : WinData) (π' : PermData) : PermData :=
  (List.range w.1.length).foldl (liftStep (tableFor n w gs).1 w.1.toArray π') (PermData.one n)

section Lift

variable {n : ℕ} {gs : GensData} {w : WinData} {π' : PermData}

/-- **The lift restricts to `π'`**, whenever some element of `G` does. -/
theorem liftModel_spec (hgs : GensData.AllValid n gs) (hw : w.Valid n) {r : PermData}
    (hr : r.Valid n) (hrG : r.denote n ∈ GensData.denote n gs) (hmap : MapsWindowBy w r π') :
    (liftModel n gs w π').Valid n ∧ (liftModel n gs w π').denote n ∈ GensData.denote n gs ∧
      MapsWindowBy w (liftModel n gs w π') π' := by
  set G := GensData.denote n gs
  set b := frontBase n w
  set T := (tableFor n w gs).1
  have hC : Complete n b G T := complete_tableFor hw hgs
  -- the required images
  set t : ℕ → ℕ := fun j => w.1.getD (get π'.1 j) 0 with ht
  have hbj : ∀ j < w.1.length, get b j = w.1.getD j 0 := fun j hj => get_frontBase hj
  have hbn : ∀ j < w.1.length, get b j < n := fun j hj => by
    rw [hbj j hj, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
    exact hw.lt _ (List.getElem_mem hj)
  have hr₀ : ∀ j < w.1.length, act (r.denote n) (get b j) = t j := fun j hj => by
    rw [act_denote hr (hbn j hj), hbj j hj]
    exact hmap j hj
  have htn : ∀ j < w.1.length, t j < n := fun j hj => by
    rw [← hr₀ j hj]
    exact act_lt _ (hbn j hj)
  -- the invariant after `i` rows
  let P : ℕ → PermData → Prop := fun i cur =>
    cur.Valid n ∧ cur.denote n ∈ G ∧ (∀ j < i, act (cur.denote n) (get b j) = t j) ∧
      ∀ j < i, act ((cur.denote n)⁻¹ * r.denote n) (get b j) = get b j
  have hstep : ∀ i < w.1.length, ∀ cur, P i cur → P (i + 1) (liftStep T w.1.toArray π' cur i) := by
    intro i hi cur ⟨hv, hG, himg, hfix⟩
    set y := (cur.denote n)⁻¹ * r.denote n
    have hyG : y ∈ G := mul_mem (inv_mem hG) hrG
    have hjn : get cur.2 (get w.1.toArray (get π'.1 i)) = act (cur.denote n)⁻¹ (t i) := by
      rw [get_toArray w.1, act_of_lt _ (htn i hi), PermData.val_denote_inv_apply hv]
    have hyi : act y (get b i) = act (cur.denote n)⁻¹ (t i) := by
      rw [act_mul, hr₀ i hi]
    obtain ⟨σ, hσ⟩ := Option.isSome_iff_exists.1
      ((hC.slot_isSome_iff (lt_of_lt_of_le hi (WinData.length_le hw)) _).2
        ⟨y, hyG, hfix, hyi⟩)
    have hσv := hC.wf.valid hσ
    have hσfix := hC.wf.fixes hσ
    have hσimg := hC.wf.image hσ
    have hliftStep : liftStep T w.1.toArray π' cur i = cur.mul σ := by
      simp only [liftStep, hjn, hσ]
    rw [hliftStep]
    have hden : (cur.mul σ).denote n = cur.denote n * σ.denote n := PermData.denote_mul hv hσv
    refine ⟨hv.mul hσv, hden ▸ mul_mem hG (hC.wf.mem hσ), fun j hj => ?_, fun j hj => ?_⟩
    · rw [hden, act_mul]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · rw [hσfix j hj, himg j hj]
      · rw [hσimg, act_act_inv]
    · rw [hden, mul_inv_rev, mul_assoc, act_mul]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · rw [hfix j hj, act_inv_eq_iff, hσfix j hj]
      · rw [hyi, act_inv_eq_iff, hσimg]
  have hfold : ∀ m ≤ w.1.length,
      P m ((List.range m).foldl (liftStep T w.1.toArray π') (PermData.one n)) := by
    intro m
    induction m with
    | zero =>
      intro _
      simp only [List.range_zero, List.foldl_nil]
      refine ⟨PermData.valid_one n, by rw [PermData.denote_one]; exact one_mem G,
        fun j hj => absurd hj (by omega), fun j hj => absurd hj (by omega)⟩
    | succ m ih =>
      intro hm
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      exact hstep m (by omega) _ (ih (by omega))
  obtain ⟨hv, hG, himg, -⟩ := hfold w.1.length le_rfl
  refine ⟨hv, hG, fun j hj => ?_⟩
  have := himg j hj
  rwa [act_denote hv (hbn j hj), hbj j hj] at this

end Lift

end GraphIso.Sims
