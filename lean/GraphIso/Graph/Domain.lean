module

public import GraphIso.Graph.Subsets
public import Mathlib.Tactic.Linarith

/-!
# The domain of one layer step

For level `r`, let `Lr` list the points of level `r` in increasing order, with `ℓ` points. The
string-isomorphism instance of the step lives on `D = N + m` points: the `N` points of the
graph, then the `m` nonempty subsets of `Lr` with at most three points, as the canonical
triples of positions `subsL ℓ` (`Subsets.lean`), at `N + t` for the `t`-th one.

* `tripImg g t`: the index of the canonical triple of the positions of the images under `g`.
  For `g` preserving levels it is an action (`tripImg_mul`, `tripImg_one`), and the subset of
  the image triple is the image of the subset (`tripSet_tripImg`).
* `indFun g`: `g` on the first `N` points, `tripImg g` on the subsets. It is multiplicative
  (`indFun_mul`), and its restriction to the first `N` points is `g`.
* An element of `A_r` preserves the layer string on all subsets exactly when it lies in `HR r`
  (`xstr_iff`).
* `enc ℓ i j k = (i ℓ + j) ℓ + k` numbers the ordered triples; the programs use it to look up
  the index of a canonical triple.
-/

@[expose] public section

namespace GraphIso.Graph

open Equiv Sims

variable {N : ℕ} {G : GraphData} {lev : Array ℕ}

section Triples

variable (ℓ : ℕ)

/-- The index of the triple `(i, j, k)`. -/
def enc (i j k : ℕ) : ℕ := (i * ℓ + j) * ℓ + k

/-- The coordinates of a triple index. -/
def dec (t : ℕ) : ℕ × ℕ × ℕ := (t / ℓ / ℓ, t / ℓ % ℓ, t % ℓ)

variable {ℓ}

theorem enc_lt {i j k : ℕ} (hi : i < ℓ) (hj : j < ℓ) (hk : k < ℓ) : enc ℓ i j k < ℓ * ℓ * ℓ := by
  unfold enc
  have h₁ : i * ℓ + j < ℓ * ℓ := by nlinarith
  nlinarith

theorem dec_enc {i j k : ℕ} (hj : j < ℓ) (hk : k < ℓ) : dec ℓ (enc ℓ i j k) = (i, j, k) := by
  have hℓ : 0 < ℓ := by omega
  unfold dec enc
  have h₁ : ((i * ℓ + j) * ℓ + k) / ℓ = i * ℓ + j := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hℓ, Nat.div_eq_of_lt hk, Nat.zero_add]
  have h₂ : ((i * ℓ + j) * ℓ + k) % ℓ = k := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk]
  rw [h₁, h₂]
  have h₃ : (i * ℓ + j) / ℓ = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hℓ, Nat.div_eq_of_lt hj, Nat.zero_add]
  have h₄ : (i * ℓ + j) % ℓ = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  rw [h₃, h₄]

theorem enc_dec {t : ℕ} : enc ℓ (dec ℓ t).1 (dec ℓ t).2.1 (dec ℓ t).2.2 = t := by
  unfold enc dec
  simp only
  rw [Nat.mul_comm (t / ℓ / ℓ), Nat.div_add_mod, Nat.mul_comm, Nat.div_add_mod]

theorem dec_lt {t : ℕ} (ht : t < ℓ * ℓ * ℓ) :
    (dec ℓ t).1 < ℓ ∧ (dec ℓ t).2.1 < ℓ ∧ (dec ℓ t).2.2 < ℓ := by
  have hℓ : 0 < ℓ := by
    rcases Nat.eq_zero_or_pos ℓ with h | h
    · subst h; simp at ht
    · exact h
  unfold dec
  refine ⟨?_, Nat.mod_lt _ hℓ, Nat.mod_lt _ hℓ⟩
  rw [Nat.div_div_eq_div_mul]
  exact (Nat.div_lt_iff_lt_mul (by positivity)).2 (by nlinarith)

end Triples

/-! ### The induced action -/

/-- The points of level `r`, in increasing order. -/
def levList (lev : Array ℕ) (N r : ℕ) : List ℕ := (List.range N).filter fun v => get lev v = r

theorem mem_levList {r v : ℕ} : v ∈ levList lev N r ↔ v < N ∧ get lev v = r := by
  simp [levList]

theorem nodup_levList (r : ℕ) : (levList lev N r).Nodup := List.nodup_range.filter _

section Ind

variable (N : ℕ) (Lr : List ℕ)

/-- The number of subsets: the points of the domain after the first `N`. -/
abbrev nsub (Lr : List ℕ) : ℕ := (subsL Lr.length).length

/-- The canonical triple of index `t`. -/
def subAt (Lr : List ℕ) (t : ℕ) : ℕ × ℕ × ℕ := (subsL Lr.length).getD t (0, 0, 0)

/-- The position of the image of the `i`-th point. -/
def posImg (g : Perm (Fin N)) (i : ℕ) : ℕ := Lr.idxOf (act g (Lr.getD i 0))

/-- The image of the subset `t` under `g`: the canonical triple of the image positions. -/
def tripImg (g : Perm (Fin N)) (t : ℕ) : ℕ :=
  (subsL Lr.length).idxOf (canon (tmap (posImg N Lr g) (subAt Lr t)))

/-- The induced action on the `N + m` points. -/
def indFun (g : Perm (Fin N)) (v : ℕ) : ℕ :=
  if v < N then act g v else if v < N + nsub Lr then N + tripImg N Lr g (v - N) else v

variable {N Lr}

/-- `g` maps the points of `Lr` into `Lr`. -/
def MapsL (Lr : List ℕ) (g : Perm (Fin N)) : Prop := ∀ x ∈ Lr, act g x ∈ Lr

theorem getD_mem {i : ℕ} (hi : i < Lr.length) : Lr.getD i 0 ∈ Lr := by
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

theorem getD_idxOf {x : ℕ} (hx : x ∈ Lr) : Lr.getD (Lr.idxOf x) 0 = x := by
  rw [List.getD_eq_getElem _ _ (List.idxOf_lt_length_of_mem hx)]
  exact List.getElem_idxOf _

theorem getD_idxOf_trip {l : List (ℕ × ℕ × ℕ)} {x : ℕ × ℕ × ℕ} (hx : x ∈ l) :
    l.getD (l.idxOf x) (0, 0, 0) = x := by
  rw [List.getD_eq_getElem _ _ (List.idxOf_lt_length_of_mem hx)]
  exact List.getElem_idxOf _

theorem subAt_eq {t : ℕ} (ht : t < nsub Lr) : subAt Lr t = (subsL Lr.length)[t] :=
  List.getD_eq_getElem _ _ ht

theorem subAt_mem {t : ℕ} (ht : t < nsub Lr) : subAt Lr t ∈ subsL Lr.length := by
  rw [subAt_eq ht]
  exact List.getElem_mem ht

theorem lt_of_mem_tset_subAt {t : ℕ} (ht : t < nsub Lr) {i : ℕ} (hi : i ∈ tset (subAt Lr t)) :
    i < Lr.length := by
  have h := (mem_subsL.1 (subAt_mem ht)).1
  rw [mem_tset] at hi
  omega

theorem posImg_lt {g : Perm (Fin N)} (hg : MapsL Lr g) {i : ℕ} (hi : i < Lr.length) :
    posImg N Lr g i < Lr.length :=
  List.idxOf_lt_length_of_mem (hg _ (getD_mem hi))

theorem posImg_posImg {g h : Perm (Fin N)} (hh : MapsL Lr h) {i : ℕ} (hi : i < Lr.length) :
    posImg N Lr g (posImg N Lr h i) = posImg N Lr (g * h) i := by
  unfold posImg
  rw [getD_idxOf (hh _ (getD_mem hi)), act_mul]

theorem posImg_one (hnd : Lr.Nodup) {i : ℕ} (hi : i < Lr.length) :
    posImg N Lr (1 : Perm (Fin N)) i = i := by
  unfold posImg
  rw [act_one, List.getD_eq_getElem _ _ hi, hnd.idxOf_getElem]

theorem canon_posImg_mem {g : Perm (Fin N)} (hg : MapsL Lr g) {t : ℕ} (ht : t < nsub Lr) :
    canon (tmap (posImg N Lr g) (subAt Lr t)) ∈ subsL Lr.length := by
  have h := (mem_subsL.1 (subAt_mem ht)).1
  exact canon_mem_subsL ⟨posImg_lt hg h.1, posImg_lt hg h.2.1, posImg_lt hg h.2.2⟩

theorem tripImg_lt {g : Perm (Fin N)} (hg : MapsL Lr g) {t : ℕ} (ht : t < nsub Lr) :
    tripImg N Lr g t < nsub Lr :=
  List.idxOf_lt_length_of_mem (canon_posImg_mem hg ht)

theorem subAt_tripImg {g : Perm (Fin N)} (hg : MapsL Lr g) {t : ℕ} (ht : t < nsub Lr) :
    subAt Lr (tripImg N Lr g t) = canon (tmap (posImg N Lr g) (subAt Lr t)) :=
  getD_idxOf_trip (canon_posImg_mem hg ht)

theorem tset_tripImg {g : Perm (Fin N)} (hg : MapsL Lr g) {t : ℕ} (ht : t < nsub Lr) :
    tset (subAt Lr (tripImg N Lr g t)) = (tset (subAt Lr t)).image (posImg N Lr g) := by
  rw [subAt_tripImg hg ht, (canon_spec _).2, tset_tmap]

theorem tripImg_mul {g h : Perm (Fin N)} (hh : MapsL Lr h) {t : ℕ} (ht : t < nsub Lr) :
    tripImg N Lr g (tripImg N Lr h t) = tripImg N Lr (g * h) t := by
  have e : canon (tmap (posImg N Lr g) (subAt Lr (tripImg N Lr h t))) =
      canon (tmap (posImg N Lr (g * h)) (subAt Lr t)) := by
    apply canon_eq_of_tset
    rw [tset_tmap, tset_tripImg hh ht, tset_tmap, Finset.image_image]
    exact Finset.image_congr fun i hi => posImg_posImg hh (lt_of_mem_tset_subAt ht hi)
  show (subsL Lr.length).idxOf _ = (subsL Lr.length).idxOf _
  rw [e]

theorem tripImg_one (hnd : Lr.Nodup) {t : ℕ} (ht : t < nsub Lr) :
    tripImg N Lr 1 t = t := by
  have hmem := subAt_mem ht
  have h := (mem_subsL.1 hmem).1
  have e : tmap (posImg N Lr 1) (subAt Lr t) = subAt Lr t := by
    unfold tmap
    rw [posImg_one hnd h.1, posImg_one hnd h.2.1, posImg_one hnd h.2.2]
  unfold tripImg
  rw [e, canon_of_canonical (mem_subsL.1 hmem).2, subAt_eq ht]
  exact (nodup_subsL _).idxOf_getElem _ ht

end Ind

section IndPerm

variable {N : ℕ} {Lr : List ℕ}

/-- The size of the domain. -/
abbrev domSize (N : ℕ) (Lr : List ℕ) : ℕ := N + nsub Lr

theorem indFun_lt {g : Perm (Fin N)} (hg : MapsL Lr g) {v : ℕ} (hv : v < domSize N Lr) :
    indFun N Lr g v < domSize N Lr := by
  simp only [domSize] at hv ⊢
  unfold indFun
  by_cases h₁ : v < N
  · simp only [h₁, ↓reduceIte]
    have := act_lt g h₁
    omega
  · simp only [h₁, hv, ↓reduceIte]
    have := tripImg_lt hg (show v - N < nsub Lr by omega)
    omega

theorem indFun_mul {g h : Perm (Fin N)} (hh : MapsL Lr h) {v : ℕ}
    (hv : v < domSize N Lr) : indFun N Lr g (indFun N Lr h v) = indFun N Lr (g * h) v := by
  simp only [domSize] at hv
  unfold indFun
  by_cases h₁ : v < N
  · simp only [h₁, ↓reduceIte, act_lt h h₁, act_mul]
  · have hv' : v - N < nsub Lr := by omega
    have ht := tripImg_lt hh hv'
    simp only [h₁, hv, ↓reduceIte, show ¬ N + tripImg N Lr h (v - N) < N by omega,
      show N + tripImg N Lr h (v - N) < N + nsub Lr by omega,
      Nat.add_sub_cancel_left]
    rw [tripImg_mul hh hv']

theorem indFun_one (hnd : Lr.Nodup) {v : ℕ} (hv : v < domSize N Lr) :
    indFun N Lr (1 : Perm (Fin N)) v = v := by
  simp only [domSize] at hv
  unfold indFun
  by_cases h₁ : v < N
  · simp [h₁]
  · simp only [h₁, hv, ↓reduceIte]
    rw [tripImg_one hnd (by omega)]
    omega

theorem mapsL_inv {g : Perm (Fin N)} (hg : MapsL Lr g) :
    MapsL Lr g⁻¹ := by
  -- `g` maps the finite set `Lr` into itself injectively, hence onto it
  intro x hx
  have hsub : (Lr.toFinset).image (act g) ⊆ Lr.toFinset := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hy
    exact List.mem_toFinset.2 (hg z (List.mem_toFinset.1 hz))
  have heq := Finset.eq_of_subset_of_card_le hsub
    (Finset.card_image_of_injective _ (act_injective g)).ge
  have : x ∈ (Lr.toFinset).image (act g) := by
    rw [heq]
    exact List.mem_toFinset.2 hx
  obtain ⟨z, hz, hzx⟩ := Finset.mem_image.1 this
  rw [← hzx, act_inv_act]
  exact List.mem_toFinset.1 hz

/-- The induced permutation of the domain. -/
def indPerm (hnd : Lr.Nodup) {g : Perm (Fin N)} (hg : MapsL Lr g) :
    Perm (Fin (domSize N Lr)) where
  toFun v := ⟨indFun N Lr g v, indFun_lt hg v.2⟩
  invFun v := ⟨indFun N Lr g⁻¹ v, indFun_lt (mapsL_inv hg) v.2⟩
  left_inv v := Fin.ext (by
    simp only
    rw [indFun_mul hg v.2, inv_mul_cancel, indFun_one hnd v.2])
  right_inv v := Fin.ext (by
    simp only
    rw [indFun_mul (mapsL_inv hg) v.2, mul_inv_cancel, indFun_one hnd v.2])

theorem act_indPerm (hnd : Lr.Nodup) {g : Perm (Fin N)} (hg : MapsL Lr g) {v : ℕ}
    (hv : v < domSize N Lr) : act (indPerm hnd hg) v = indFun N Lr g v := by
  rw [act_of_lt _ hv]
  rfl

end IndPerm

/-! ### The layer string on triples -/

section XStr

variable {Lr : List ℕ}

/-- The subset of index `t`. -/
def tripSet (Lr : List ℕ) (t : ℕ) : Finset ℕ := (tset (subAt Lr t)).image (Lr.getD · 0)

theorem tripSet_tripImg {g : Perm (Fin N)} (hg : MapsL Lr g) {t : ℕ} (ht : t < nsub Lr) :
    tripSet Lr (tripImg N Lr g t) = (tripSet Lr t).image (act g) := by
  unfold tripSet
  rw [tset_tripImg hg ht, Finset.image_image, Finset.image_image]
  exact Finset.image_congr fun i hi => getD_idxOf (hg _ (getD_mem (lt_of_mem_tset_subAt ht hi)))

theorem subL_tripSet {r : ℕ} {t : ℕ} (ht : t < nsub (levList lev N r)) :
    SubL lev 3 N r (tripSet (levList lev N r) t) := by
  refine ⟨Finset.Nonempty.image ⟨_, mem_tset.2 (Or.inl rfl)⟩ _, ?_, fun u hu => ?_⟩
  · refine Finset.card_image_le.trans ?_
    exact Finset.card_le_three
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hu
    exact mem_levList.1 (getD_mem (lt_of_mem_tset_subAt ht hi))

/-- Every subset read by the layer string is the set of some canonical triple. -/
theorem exists_tripSet {r : ℕ} {T : Finset ℕ} (hT : SubL lev 3 N r T) :
    ∃ t < nsub (levList lev N r), tripSet (levList lev N r) t = T := by
  set Lr := levList lev N r with hLr
  have hmem : ∀ x ∈ T, x ∈ Lr := fun x hx => mem_levList.2 (hT.2.2 x hx)
  -- a subset listing `x`, `y`, `z`
  have key : ∀ x y z, x ∈ Lr → y ∈ Lr → z ∈ Lr →
      ∃ t < nsub Lr, tripSet Lr t = {x, y, z} := by
    intro x y z hx hy hz
    set u : ℕ × ℕ × ℕ := (Lr.idxOf x, Lr.idxOf y, Lr.idxOf z) with hu
    have hc := canon_mem_subsL (ℓ := Lr.length) (t := u)
      ⟨List.idxOf_lt_length_of_mem hx, List.idxOf_lt_length_of_mem hy,
        List.idxOf_lt_length_of_mem hz⟩
    refine ⟨(subsL Lr.length).idxOf (canon u), List.idxOf_lt_length_of_mem hc, ?_⟩
    unfold tripSet subAt
    rw [getD_idxOf_trip hc, (canon_spec u).2, hu]
    simp only [tset, Finset.image_insert, Finset.image_singleton]
    rw [getD_idxOf hx, getD_idxOf hy, getD_idxOf hz]
  have hc := hT.2.1
  have hpos : 0 < T.card := Finset.card_pos.2 hT.1
  rcases (show T.card = 1 ∨ T.card = 2 ∨ T.card = 3 by omega) with h | h | h
  · obtain ⟨x, rfl⟩ := Finset.card_eq_one.1 h
    obtain ⟨t, ht, he⟩ := key x x x (hmem x (by simp)) (hmem x (by simp)) (hmem x (by simp))
    exact ⟨t, ht, by rw [he]; simp⟩
  · obtain ⟨x, y, -, rfl⟩ := Finset.card_eq_two.1 h
    obtain ⟨t, ht, he⟩ := key x y y (hmem x (by simp)) (hmem y (by simp)) (hmem y (by simp))
    exact ⟨t, ht, by rw [he]; simp⟩
  · obtain ⟨x, y, z, -, -, -, rfl⟩ := Finset.card_eq_three.1 h
    exact key x y z (hmem x (by simp)) (hmem y (by simp)) (hmem z (by simp))

/-- **The layer string on the subsets characterizes `HR r`.** -/
theorem xstr_iff {r : ℕ} {g : Perm (Fin N)} (hg : g ∈ AutR N G lev r) :
    (∀ t < nsub (levList lev N r),
      xval G lev 3 N r (tripSet (levList lev N r) t) =
        xval G lev 3 N r (tripSet (levList lev N r) (tripImg N (levList lev N r) g t))) ↔
      g ∈ HR N G lev 3 r := by
  have hmaps : MapsL (levList lev N r) g := fun x hx => by
    obtain ⟨hxN, hlx⟩ := mem_levList.1 hx
    exact mem_levList.2 ⟨act_lt g hxN, by rw [hg.2.1 x hxN, hlx]⟩
  constructor
  · intro h
    refine ⟨hg, fun T hT => ?_⟩
    obtain ⟨t, ht, rfl⟩ := exists_tripSet hT
    rw [h t ht, tripSet_tripImg hmaps ht]
  · intro h t ht
    rw [tripSet_tripImg hmaps ht]
    exact (h.2 _ (subL_tripSet ht)).symm

end XStr

end GraphIso.Graph
