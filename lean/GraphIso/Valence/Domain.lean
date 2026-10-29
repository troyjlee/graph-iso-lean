module

public import GraphIso.Valence.Subsets
public import GraphIso.Graph.Ind

/-!
# The domain of one layer step for maximum degree `Δ`

For level `r`, let `Lr` list the points of level `r` in increasing order. The
string-isomorphism instance of the step lives on `D = N + m` points: the `N` points of the
graph, then the `m` subsets of `Lr` with at most `Δ` points, as the sublists `subsR Δ Lr`
(`Subsets.lean`), at `N + t` for the `t`-th one.

* `subImg g t`: the index of the member whose elements are the images under `g` of the
  elements of member `t`, found by a linear search (`findSub`). For `g` mapping `Lr` into
  itself, the set of the image is the image of the set (`subSet_subImg`), and it is an action
  (`subImg_mul`, `subImg_one`).
* `indFun g`: `g` on the first `N` points, `subImg g` on the subsets; `indPerm` is the induced
  permutation of the domain.
* An element of `A_r` preserves the layer string on all subsets exactly when it lies in
  `HR Δ r` (`xstr_iff`).
-/

@[expose] public section

namespace GraphIso.Graph.Valence

open Equiv Sims

section Ind

variable (Δ N : ℕ) (Lr : List ℕ)

/-- The number of subsets: the points of the domain after the first `N`. -/
abbrev nsub : ℕ := (subsR Δ Lr).length

/-- The size of the domain. -/
abbrev domSize : ℕ := N + nsub Δ Lr

/-- The subset of index `t`. -/
def subAt (t : ℕ) : List ℕ := (subsR Δ Lr).getD t []

/-- The index of the first subset with the elements of `s`. -/
def findSub (s : List ℕ) : ℕ := (subsR Δ Lr).findIdx fun u => seteqB u s

/-- The index of the image of the subset `t` under `g`. -/
def subImg (g : Perm (Fin N)) (t : ℕ) : ℕ := findSub Δ Lr ((subAt Δ Lr t).map (act g))

/-- The induced action on the `N + m` points. -/
def indFun (g : Perm (Fin N)) (v : ℕ) : ℕ :=
  if v < N then act g v else if v < N + nsub Δ Lr then N + subImg Δ N Lr g (v - N) else v

/-- The set of points of the subset of index `t`. -/
def subSet (t : ℕ) : Finset ℕ := (subAt Δ Lr t).toFinset

variable {Δ N Lr}

theorem subAt_eq {t : ℕ} (ht : t < nsub Δ Lr) : subAt Δ Lr t = (subsR Δ Lr)[t] :=
  List.getD_eq_getElem _ _ ht

theorem subAt_mem {t : ℕ} (ht : t < nsub Δ Lr) : subAt Δ Lr t ∈ subsR Δ Lr := by
  rw [subAt_eq ht]
  exact List.getElem_mem ht

theorem mem_of_mem_subAt {t : ℕ} (ht : t < nsub Δ Lr) {x : ℕ} (hx : x ∈ subAt Δ Lr t) :
    x ∈ Lr :=
  (mem_subsR.1 (subAt_mem ht)).1.subset hx

theorem length_subAt_le {t : ℕ} (ht : t < nsub Δ Lr) : (subAt Δ Lr t).length ≤ Δ :=
  (mem_subsR.1 (subAt_mem ht)).2

variable (hLr : Lr.Pairwise (· < ·))
include hLr

theorem nodup_subAt {t : ℕ} (ht : t < nsub Δ Lr) : (subAt Δ Lr t).Nodup :=
  (hLr.sublist (mem_subsR.1 (subAt_mem ht)).1).sortedLT.nodup

/-- **Subsets are determined by their sets.** -/
theorem subAt_inj {t t' : ℕ} (ht : t < nsub Δ Lr) (ht' : t' < nsub Δ Lr)
    (h : subSet Δ Lr t = subSet Δ Lr t') : t = t' := by
  have e := eq_of_toFinset_eq hLr (mem_subsR.1 (subAt_mem ht)).1 (mem_subsR.1 (subAt_mem ht')).1 h
  rw [subAt_eq ht, subAt_eq ht'] at e
  exact ((nodup_subsR Δ hLr.nodup).getElem_inj_iff).1 e

/-- The search finds the subset with the same set. -/
theorem findSub_eq {t : ℕ} (ht : t < nsub Δ Lr) {s : List ℕ}
    (h : subSet Δ Lr t = s.toFinset) : findSub Δ Lr s = t := by
  unfold findSub
  rw [List.findIdx_eq ht]
  refine ⟨seteqB_iff.2 (by rw [← subAt_eq ht]; exact h), fun j hj => ?_⟩
  rw [Bool.eq_false_iff]
  intro hs
  have hj' : j < nsub Δ Lr := Nat.lt_trans hj ht
  have e : subSet Δ Lr j = subSet Δ Lr t := by
    rw [h]
    unfold subSet
    rw [subAt_eq hj']
    exact seteqB_iff.1 hs
  exact absurd (subAt_inj hLr hj' ht e) (Nat.ne_of_lt hj)

/-- **Every set of at most `Δ` points of `Lr` is the set of a subset.** -/
theorem exists_subSet {T : Finset ℕ} (hT : ∀ x ∈ T, x ∈ Lr) (hc : T.card ≤ Δ) :
    ∃ t < nsub Δ Lr, subSet Δ Lr t = T := by
  obtain ⟨s, hs, rfl⟩ := exists_subsR hLr.nodup hT hc
  obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.1 hs
  exact ⟨t, ht, by unfold subSet; rw [subAt_eq ht]⟩

theorem subImg_spec {g : Perm (Fin N)} (hg : MapsL Lr g) {t : ℕ} (ht : t < nsub Δ Lr) :
    subImg Δ N Lr g t < nsub Δ Lr ∧
      subSet Δ Lr (subImg Δ N Lr g t) = (subSet Δ Lr t).image (act g) := by
  have hc : ((subSet Δ Lr t).image (act g)).card ≤ Δ := by
    refine Finset.card_image_le.trans ?_
    unfold subSet
    exact (List.toFinset_card_le _).trans (length_subAt_le ht)
  have hT : ∀ x ∈ (subSet Δ Lr t).image (act g), x ∈ Lr := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
    exact hg y (mem_of_mem_subAt ht (List.mem_toFinset.1 hy))
  obtain ⟨t', ht', he⟩ := exists_subSet hLr hT hc
  have hf : subImg Δ N Lr g t = t' := by
    unfold subImg
    refine findSub_eq hLr ht' ?_
    rw [he]
    ext x
    simp [subSet]
  rw [hf]
  exact ⟨ht', he⟩

theorem subImg_lt {g : Perm (Fin N)} (hg : MapsL Lr g) {t : ℕ} (ht : t < nsub Δ Lr) :
    subImg Δ N Lr g t < nsub Δ Lr :=
  (subImg_spec hLr hg ht).1

theorem subSet_subImg {g : Perm (Fin N)} (hg : MapsL Lr g) {t : ℕ} (ht : t < nsub Δ Lr) :
    subSet Δ Lr (subImg Δ N Lr g t) = (subSet Δ Lr t).image (act g) :=
  (subImg_spec hLr hg ht).2

theorem subImg_mul {g h : Perm (Fin N)} (hg : MapsL Lr g) (hh : MapsL Lr h) {t : ℕ}
    (ht : t < nsub Δ Lr) :
    subImg Δ N Lr g (subImg Δ N Lr h t) = subImg Δ N Lr (g * h) t := by
  have hgh : MapsL Lr (g * h) := fun x hx => by rw [act_mul]; exact hg _ (hh x hx)
  refine subAt_inj hLr (subImg_lt hLr hg (subImg_lt hLr hh ht)) (subImg_lt hLr hgh ht) ?_
  rw [subSet_subImg hLr hg (subImg_lt hLr hh ht), subSet_subImg hLr hh ht,
    subSet_subImg hLr hgh ht, Finset.image_image]
  exact Finset.image_congr fun v _ => (act_mul g h v).symm

theorem subImg_one {t : ℕ} (ht : t < nsub Δ Lr) : subImg Δ N Lr (1 : Perm (Fin N)) t = t := by
  have h1 : MapsL Lr (1 : Perm (Fin N)) := fun x hx => by rw [act_one]; exact hx
  refine subAt_inj hLr (subImg_lt hLr h1 ht) ht ?_
  rw [subSet_subImg hLr h1 ht, image_act_one]

end Ind

/-! ### The induced permutation -/

section IndPerm

variable {Δ N : ℕ} {Lr : List ℕ} (hLr : Lr.Pairwise (· < ·))
include hLr

theorem indFun_lt {g : Perm (Fin N)} (hg : MapsL Lr g) {v : ℕ} (hv : v < domSize Δ N Lr) :
    indFun Δ N Lr g v < domSize Δ N Lr := by
  simp only [domSize] at hv ⊢
  unfold indFun
  by_cases h₁ : v < N
  · simp only [h₁, ↓reduceIte]
    have := act_lt g h₁
    omega
  · simp only [h₁, hv, ↓reduceIte]
    have := subImg_lt hLr hg (show v - N < nsub Δ Lr by omega)
    omega

theorem indFun_mul {g h : Perm (Fin N)} (hg : MapsL Lr g) (hh : MapsL Lr h) {v : ℕ}
    (hv : v < domSize Δ N Lr) :
    indFun Δ N Lr g (indFun Δ N Lr h v) = indFun Δ N Lr (g * h) v := by
  simp only [domSize] at hv
  unfold indFun
  by_cases h₁ : v < N
  · simp only [h₁, ↓reduceIte, act_lt h h₁, act_mul]
  · have hv' : v - N < nsub Δ Lr := by omega
    have ht := subImg_lt hLr hh hv'
    simp only [h₁, hv, ↓reduceIte, show ¬ N + subImg Δ N Lr h (v - N) < N by omega,
      show N + subImg Δ N Lr h (v - N) < N + nsub Δ Lr by omega, Nat.add_sub_cancel_left]
    rw [subImg_mul hLr hg hh hv']

theorem indFun_one {v : ℕ} (hv : v < domSize Δ N Lr) :
    indFun Δ N Lr (1 : Perm (Fin N)) v = v := by
  simp only [domSize] at hv
  unfold indFun
  by_cases h₁ : v < N
  · simp [h₁]
  · simp only [h₁, hv, ↓reduceIte]
    rw [subImg_one hLr (by omega)]
    omega

variable (Δ) in
/-- The induced permutation of the domain. -/
def indPerm {g : Perm (Fin N)} (hg : MapsL Lr g) : Perm (Fin (domSize Δ N Lr)) where
  toFun v := ⟨indFun Δ N Lr g v, indFun_lt hLr hg v.2⟩
  invFun v := ⟨indFun Δ N Lr g⁻¹ v, indFun_lt hLr (mapsL_inv hg) v.2⟩
  left_inv v := Fin.ext (by
    simp only
    rw [indFun_mul hLr (mapsL_inv hg) hg v.2, inv_mul_cancel, indFun_one hLr v.2])
  right_inv v := Fin.ext (by
    simp only
    rw [indFun_mul hLr hg (mapsL_inv hg) v.2, mul_inv_cancel, indFun_one hLr v.2])

theorem act_indPerm {g : Perm (Fin N)} (hg : MapsL Lr g) {v : ℕ} (hv : v < domSize Δ N Lr) :
    act (indPerm Δ hLr hg) v = indFun Δ N Lr g v := by
  rw [act_of_lt _ hv]
  rfl

end IndPerm

/-! ### The layer string on the subsets -/

section XStr

variable {Δ N : ℕ} {G : GraphData} {lev : Array ℕ} {r : ℕ}

theorem pairwise_levList (lev : Array ℕ) (N r : ℕ) : (levList lev N r).Pairwise (· < ·) :=
  List.pairwise_lt_range.filter _

theorem subL_subSet {t : ℕ} (ht : t < nsub Δ (levList lev N r))
    (hne : (subSet Δ (levList lev N r) t).Nonempty) :
    SubL lev Δ N r (subSet Δ (levList lev N r) t) := by
  refine ⟨hne, (List.toFinset_card_le _).trans (length_subAt_le ht), fun u hu => ?_⟩
  exact mem_levList.1 (mem_of_mem_subAt ht (List.mem_toFinset.1 hu))

/-- **The layer string on the subsets characterizes `HR Δ r`.** -/
theorem xstr_iff {g : Perm (Fin N)} (hg : g ∈ AutR N G lev r) :
    (∀ t < nsub Δ (levList lev N r),
      xval G lev Δ N r (subSet Δ (levList lev N r) t) =
        xval G lev Δ N r (subSet Δ (levList lev N r) (subImg Δ N (levList lev N r) g t))) ↔
      g ∈ HR N G lev Δ r := by
  have hLr := pairwise_levList lev N r
  have hmaps : MapsL (levList lev N r) g := mapsL_of_autR hg
  constructor
  · intro h
    refine ⟨hg, fun T hT => ?_⟩
    obtain ⟨t, ht, rfl⟩ := exists_subSet hLr (fun x hx => mem_levList.2 (hT.2.2 x hx)) hT.2.1
    rw [h t ht, subSet_subImg hLr hmaps ht]
  · intro h t ht
    rw [subSet_subImg hLr hmaps ht]
    rcases (subSet Δ (levList lev N r) t).eq_empty_or_nonempty with he | hne
    · rw [he, Finset.image_empty]
    · exact (h.2 _ (subL_subSet ht hne)).symm

end XStr

end GraphIso.Graph.Valence
