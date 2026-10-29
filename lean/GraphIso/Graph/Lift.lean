module

public import GraphIso.Graph.Layers
public import Mathlib.Data.List.GetD

/-!
# Extending a layer group by one level

For a layered graph (`Layered`) and a level `r`:

* `HR Δ r`: the elements of `A_r` preserving the layer string `xval Δ r` on the subsets of
  level `r` with one to `Δ` points.
* `nb_act`: an element of `A_{r+1}` maps the neighbourhood of a new point to the
  neighbourhood of its image.
* `liftPerm h` for `h ∈ HR r`: `h` on level `≤ r`, and on level `r + 1` the point of the same
  rank in the class of the image neighbourhood (`liftFun`). It lies in `A_{r+1}`
  (`liftPerm_mem`), and lifting is multiplicative (`liftFun_comp`).
* `resPerm g` for `g ∈ A_{r+1}`: `g` on level `≤ r`, the identity elsewhere. It lies in
  `HR r` (`resPerm_mem`).
-/

@[expose] public section

namespace GraphIso.Graph

open Equiv Sims

variable {Δ N : ℕ} {G : GraphData} {roots : List ℕ} {lev : Array ℕ}

/-! ### Edges of consecutive layered graphs -/

theorem edgeR_iff_adj {r u v : ℕ} (hu : get lev u ≤ r) (hv : get lev v ≤ r + 1) :
    EdgeR G lev (r + 1) u v ↔ Adj G u v := by
  unfold EdgeR
  constructor
  · exact fun h => h.1
  · exact fun h => ⟨h, by omega, hv, Or.inl (by omega)⟩

theorem edgeR_iff_adj' {r u v : ℕ} (hu : get lev u ≤ r + 1) (hv : get lev v ≤ r) :
    EdgeR G lev (r + 1) u v ↔ Adj G u v := by
  unfold EdgeR
  constructor
  · exact fun h => h.1
  · exact fun h => ⟨h, hu, by omega, Or.inr (Or.inl (by omega))⟩

theorem not_edgeR_of_gt {r u v : ℕ} (h : r < get lev u ∨ r < get lev v) : ¬ EdgeR G lev r u v :=
  fun he => by unfold EdgeR at he; omega

theorem not_edgeR_new {r u v : ℕ} (hu : get lev u = r + 1) (hv : get lev v = r + 1) :
    ¬ EdgeR G lev (r + 1) u v := fun he => by unfold EdgeR at he; omega

/-! ### Neighbourhoods under the layer group -/

variable (hZ : LayeredD Δ N G roots lev)
include hZ

theorem lt_of_adj {u v : ℕ} (h : Adj G u v) : v < N := hZ.valid.lt u v h

/-- An element of `A_{r+1}` maps neighbourhoods of new points to neighbourhoods. -/
theorem nb_act {r : ℕ} {g : Perm (Fin N)} (hg : g ∈ AutR N G lev (r + 1)) {w : ℕ} (hw : w < N)
    (hlw : get lev w = r + 1) : nb G lev r (act g w) = (nb G lev r w).image (act g) := by
  obtain ⟨-, hg₂, hg₃⟩ := hg
  ext u'
  rw [mem_nb, Finset.mem_image]
  constructor
  · rintro ⟨hadj, hlu'⟩
    have hu'N := lt_of_adj hZ hadj
    refine ⟨act g⁻¹ u', ?_, act_act_inv g u'⟩
    have hlu : get lev (act g⁻¹ u') = r := by
      have := hg₂ _ (act_lt g⁻¹ hu'N)
      rw [act_act_inv] at this
      omega
    rw [mem_nb]
    refine ⟨?_, hlu⟩
    have h₁ : EdgeR G lev (r + 1) (act g w) (act g (act g⁻¹ u')) := by
      rw [act_act_inv]
      exact (edgeR_iff_adj' (by rw [hg₂ w hw]; omega) (by omega)).2 hadj
    have h₂ := (hg₃ w _ hw (act_lt g⁻¹ hu'N)).1 h₁
    exact (edgeR_iff_adj' (by omega) (by omega)).1 h₂
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨hadj, hlu⟩ := mem_nb.1 hu
    have huN := lt_of_adj hZ hadj
    refine ⟨?_, by rw [hg₂ u huN, hlu]⟩
    have h₁ : EdgeR G lev (r + 1) w u := (edgeR_iff_adj' (by omega) (by omega)).2 hadj
    have h₂ := (hg₃ w u hw huN).2 h₁
    exact (edgeR_iff_adj' (by rw [hg₂ w hw]; omega) (by rw [hg₂ u huN]; omega)).1 h₂

omit hZ in
/-- A new point lies in the class of its neighbourhood. -/
theorem mem_cls_self {r w : ℕ} (hw : w < N) (hlw : get lev w = r + 1) :
    w ∈ cls G lev N r (nb G lev r w) :=
  mem_cls.2 ⟨hw, hlw, rfl⟩

/-- The neighbourhood of a new point is a subset of level `r` read by the layer string. -/
theorem subL_nb {r w : ℕ} (hw : w < N) (hlw : get lev w = r + 1) :
    SubL lev Δ N r (nb G lev r w) := by
  refine ⟨?_, ?_, fun u hu => ?_⟩
  · obtain ⟨u, hadj, hu⟩ := hZ.levels.wit w hw (by omega) (hZ.reach w hw)
    exact ⟨u, mem_nb.2 ⟨hadj, by omega⟩⟩
  · calc (nb G lev r w).card ≤ ((nbrs G w).filter fun u => get lev u = r).length :=
          List.toFinset_card_le _
      _ ≤ (nbrs G w).length := List.length_filter_le _ _
      _ ≤ Δ := hZ.valid.deg w
  · obtain ⟨hadj, hlu⟩ := mem_nb.1 hu
    exact ⟨lt_of_adj hZ hadj, hlu⟩

omit hZ

/-! ### The extendable subgroup -/

theorem subL_image {r : ℕ} {h : Perm (Fin N)} (hh : h ∈ AutR N G lev r) {T : Finset ℕ}
    (hT : SubL lev Δ N r T) : SubL lev Δ N r (T.image (act h)) := by
  obtain ⟨hne, hcard, hmem⟩ := hT
  refine ⟨hne.image _, (Finset.card_image_le).trans hcard, fun u hu => ?_⟩
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hu
  obtain ⟨hvN, hlv⟩ := hmem v hv
  exact ⟨act_lt h hvN, by rw [hh.2.1 v hvN, hlv]⟩

theorem image_act_mul (g h : Perm (Fin N)) (T : Finset ℕ) :
    (T.image (act h)).image (act g) = T.image (act (g * h)) := by
  rw [Finset.image_image]
  congr 1
  funext v
  exact (act_mul g h v).symm

theorem image_act_one (T : Finset ℕ) : T.image (act (1 : Perm (Fin N))) = T := by
  have : act (1 : Perm (Fin N)) = id := funext act_one
  rw [this, Finset.image_id]

variable (N G lev) in
/-- **The extendable subgroup**: the elements of `A_r` preserving the layer string. -/
def HR (Δ r : ℕ) : Subgroup (Perm (Fin N)) where
  carrier := {h | h ∈ AutR N G lev r ∧
    ∀ T, SubL lev Δ N r T → xval G lev Δ N r (T.image (act h)) = xval G lev Δ N r T}
  one_mem' := ⟨one_mem _, fun T _ => by rw [image_act_one]⟩
  mul_mem' := by
    rintro g h ⟨hg, hgx⟩ ⟨hh, hhx⟩
    refine ⟨mul_mem hg hh, fun T hT => ?_⟩
    rw [← image_act_mul, hgx _ (subL_image hh hT), hhx T hT]
  inv_mem' := by
    rintro h ⟨hh, hhx⟩
    refine ⟨inv_mem hh, fun T hT => ?_⟩
    have := hhx _ (subL_image (inv_mem hh) hT)
    rw [image_act_mul, mul_inv_cancel, image_act_one] at this
    exact this.symm

theorem mem_HR {r : ℕ} {h : Perm (Fin N)} : h ∈ HR N G lev Δ r ↔ h ∈ AutR N G lev r ∧
    ∀ T, SubL lev Δ N r T → xval G lev Δ N r (T.image (act h)) = xval G lev Δ N r T := Iff.rfl

include hZ in
/-- The layer string determines the class sizes. -/
theorem cnt_image {r : ℕ} {h : Perm (Fin N)} (hh : h ∈ HR N G lev Δ r) {T : Finset ℕ}
    (hT : SubL lev Δ N r T) : cnt G lev N r (T.image (act h)) = cnt G lev N r T := by
  have hx := hh.2 T hT
  have h₁ := cnt_le hZ (r := r) hT.1
  have h₂ := cnt_le hZ (r := r) (hT.1.image (act h))
  unfold xval at hx
  split at hx <;> split at hx <;> omega

/-! ### The canonical lift -/

variable (N G lev) in
/-- The rank of a new point in its class. -/
def rankIn (r w : ℕ) : ℕ := (cls G lev N r (nb G lev r w)).idxOf w

variable (N G lev) in
/-- The canonical lift of `h`: `h` below level `r + 1`, rank matching on level `r + 1`. -/
def liftFun (r : ℕ) (h : Perm (Fin N)) (w : ℕ) : ℕ :=
  if w < N ∧ get lev w = r + 1 then
    (cls G lev N r ((nb G lev r w).image (act h))).getD (rankIn N G lev r w) w
  else act h w

include hZ in
/-- The lift of a new point lies in the class of the image neighbourhood, at the same rank. -/
theorem liftFun_new {r : ℕ} {h : Perm (Fin N)} (hh : h ∈ HR N G lev Δ r) {w : ℕ} (hw : w < N)
    (hlw : get lev w = r + 1) :
    liftFun N G lev r h w ∈ cls G lev N r ((nb G lev r w).image (act h)) ∧
      rankIn N G lev r (liftFun N G lev r h w) = rankIn N G lev r w := by
  have hmem := mem_cls_self (G := G) hw hlw
  have hk : rankIn N G lev r w < (cls G lev N r ((nb G lev r w).image (act h))).length := by
    have := cnt_image hZ hh (subL_nb hZ hw hlw)
    unfold cnt at this
    rw [this]
    exact List.idxOf_lt_length_of_mem hmem
  have he : liftFun N G lev r h w =
      (cls G lev N r ((nb G lev r w).image (act h)))[rankIn N G lev r w] := by
    simp only [liftFun, hw, hlw, and_self, ↓reduceIte]
    exact List.getD_eq_getElem _ _ hk
  have hin : liftFun N G lev r h w ∈ cls G lev N r ((nb G lev r w).image (act h)) := by
    rw [he]
    exact List.getElem_mem hk
  refine ⟨hin, ?_⟩
  obtain ⟨-, -, hnb⟩ := mem_cls.1 hin
  unfold rankIn
  rw [hnb, he]
  exact (nodup_cls r _).idxOf_getElem _ hk

theorem liftFun_old {r : ℕ} {h : Perm (Fin N)} {w : ℕ} (hw : ¬ (w < N ∧ get lev w = r + 1)) :
    liftFun N G lev r h w = act h w := by
  simp [liftFun, hw]

include hZ in
theorem liftFun_lt {r : ℕ} {h : Perm (Fin N)} (hh : h ∈ HR N G lev Δ r) {w : ℕ} (hw : w < N) :
    liftFun N G lev r h w < N := by
  by_cases hn : get lev w = r + 1
  · exact (mem_cls.1 (liftFun_new hZ hh hw hn).1).1
  · rw [liftFun_old (by tauto)]
    exact act_lt h hw

include hZ in
theorem lev_liftFun {r : ℕ} {h : Perm (Fin N)} (hh : h ∈ HR N G lev Δ r) {w : ℕ} (hw : w < N) :
    get lev (liftFun N G lev r h w) = get lev w := by
  by_cases hn : get lev w = r + 1
  · rw [(mem_cls.1 (liftFun_new hZ hh hw hn).1).2.1, hn]
  · rw [liftFun_old (by tauto)]
    exact hh.1.2.1 w hw

include hZ in
theorem nb_liftFun {r : ℕ} {h : Perm (Fin N)} (hh : h ∈ HR N G lev Δ r) {w : ℕ} (hw : w < N)
    (hlw : get lev w = r + 1) :
    nb G lev r (liftFun N G lev r h w) = (nb G lev r w).image (act h) :=
  (mem_cls.1 (liftFun_new hZ hh hw hlw).1).2.2

theorem liftFun_one {r w : ℕ} : liftFun N G lev r 1 w = w := by
  unfold liftFun
  split
  · rename_i hw
    rw [image_act_one]
    unfold rankIn
    have hmem := mem_cls_self (G := G) hw.1 hw.2
    rw [List.getD_eq_getElem _ _ (List.idxOf_lt_length_of_mem hmem)]
    exact List.getElem_idxOf (List.idxOf_lt_length_of_mem hmem)
  · exact act_one w

theorem liftFun_of_new {r : ℕ} {h : Perm (Fin N)} {w : ℕ} (hw : w < N)
    (hlw : get lev w = r + 1) :
    liftFun N G lev r h w =
      (cls G lev N r ((nb G lev r w).image (act h))).getD (rankIn N G lev r w) w := by
  simp only [liftFun, hw, hlw, and_self, ↓reduceIte]

include hZ in
/-- **Lifting is multiplicative.** -/
theorem liftFun_comp {r : ℕ} {g h : Perm (Fin N)} (hg : g ∈ HR N G lev Δ r)
    (hh : h ∈ HR N G lev Δ r) {w : ℕ} (hw : w < N) :
    liftFun N G lev r g (liftFun N G lev r h w) = liftFun N G lev r (g * h) w := by
  by_cases hn : get lev w = r + 1
  · obtain ⟨hin, hrank⟩ := liftFun_new hZ hh hw hn
    obtain ⟨hw', hlw', hnb'⟩ := mem_cls.1 hin
    have hk : rankIn N G lev r w <
        (cls G lev N r ((nb G lev r w).image (act (g * h)))).length := by
      have := cnt_image hZ (mul_mem hg hh) (subL_nb hZ hw hn)
      unfold cnt at this
      rw [this]
      exact List.idxOf_lt_length_of_mem (mem_cls_self (G := G) hw hn)
    rw [liftFun_of_new hw' hlw', hnb', image_act_mul, hrank, liftFun_of_new (h := g * h) hw hn,
      List.getD_eq_getElem _ _ hk, List.getD_eq_getElem _ _ hk]
  · have hlh : ¬ (act h w < N ∧ get lev (act h w) = r + 1) := by
      rw [hh.1.2.1 w hw]
      tauto
    rw [liftFun_old (h := h) (w := w) (by tauto), liftFun_old hlh,
      liftFun_old (h := g * h) (w := w) (by tauto), act_mul]

/-! ### The lift as a permutation -/

theorem act_injective (g : Perm (Fin N)) : Function.Injective (act g) := by
  intro u v h
  have := congrArg (act g⁻¹) h
  rwa [act_inv_act, act_inv_act] at this

include hZ in
/-- The canonical lift of `h ∈ HR r`, as a permutation. -/
def liftPerm {r : ℕ} {h : Perm (Fin N)} (hh : h ∈ HR N G lev Δ r) : Perm (Fin N) where
  toFun w := ⟨liftFun N G lev r h w, liftFun_lt hZ hh w.2⟩
  invFun w := ⟨liftFun N G lev r h⁻¹ w, liftFun_lt hZ (inv_mem hh) w.2⟩
  left_inv w := Fin.ext (by
    simp only
    rw [liftFun_comp hZ (inv_mem hh) hh w.2, inv_mul_cancel, liftFun_one])
  right_inv w := Fin.ext (by
    simp only
    rw [liftFun_comp hZ hh (inv_mem hh) w.2, mul_inv_cancel, liftFun_one])

include hZ in
theorem act_liftPerm {r : ℕ} {h : Perm (Fin N)} (hh : h ∈ HR N G lev Δ r) (w : ℕ) :
    act (liftPerm hZ hh) w = liftFun N G lev r h w := by
  by_cases hw : w < N
  · rw [act_of_lt _ hw]
    rfl
  · rw [act_of_ge _ (by omega), liftFun_old (by tauto), act_of_ge _ (by omega)]

include hZ in
theorem liftPerm_mul {r : ℕ} {g h : Perm (Fin N)} (hg : g ∈ HR N G lev Δ r)
    (hh : h ∈ HR N G lev Δ r) :
    liftPerm hZ (mul_mem hg hh) = liftPerm hZ hg * liftPerm hZ hh := by
  ext w
  show liftFun N G lev r (g * h) w = liftFun N G lev r g (liftFun N G lev r h w)
  rw [liftFun_comp hZ hg hh w.2]

/-! ### The lift lies in the next layer group -/

theorem edgeR_symm {r u v : ℕ} (hG : G.ValidD Δ N) (h : EdgeR G lev r u v) :
    EdgeR G lev r v u := by
  obtain ⟨hadj, h₁, h₂, h₃⟩ := h
  exact ⟨hG.symm _ _ hadj, h₂, h₁, by omega⟩

theorem isEdge_pair (hG : G.ValidD Δ N) {u v : ℕ} (huv : u ≠ v) :
    IsEdge G {u, v} ↔ Adj G u v := by
  unfold IsEdge
  rw [Finset.card_pair huv]
  constructor
  · rintro ⟨-, x, hx, y, hy, hxy⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact absurd hxy (hG.irrefl _)
    · exact hxy
    · exact hG.symm _ _ hxy
    · exact absurd hxy (hG.irrefl _)
  · intro h
    exact ⟨rfl, u, by simp, v, by simp, h⟩

include hZ in
/-- Adjacency between two points of level `r` is preserved by `HR r`. -/
theorem adj_iff_of_HR {r : ℕ} {h : Perm (Fin N)} (hh : h ∈ HR N G lev Δ r) {u v : ℕ}
    (hu : u < N) (hv : v < N) (hlu : get lev u = r) (hlv : get lev v = r) :
    Adj G (act h u) (act h v) ↔ Adj G u v := by
  by_cases huv : u = v
  · subst huv
    exact ⟨fun h' => absurd h' (hZ.valid.irrefl _), fun h' => absurd h' (hZ.valid.irrefl _)⟩
  have hT : SubL lev Δ N r {u, v} := ⟨⟨u, by simp⟩, by rw [Finset.card_pair huv]; exact hZ.two_le,
    fun x hx => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact ⟨hu, hlu⟩
      · exact ⟨hv, hlv⟩⟩
  have hx := hh.2 _ hT
  have hc := cnt_image hZ hh hT
  have himg : ({u, v} : Finset ℕ).image (act h) = {act h u, act h v} := by simp
  have hne : act h u ≠ act h v := fun e => huv (act_injective h e)
  rw [himg] at hx hc
  unfold xval at hx
  rw [hc] at hx
  rw [← isEdge_pair hZ.valid huv, ← isEdge_pair hZ.valid hne]
  constructor
  · intro he
    by_contra hn
    simp [he, hn] at hx
  · intro he
    by_contra hn
    simp [he, hn] at hx

include hZ in
/-- Adjacency below level `r + 1` is preserved by `HR r`. -/
theorem adj_iff_low {r : ℕ} {h : Perm (Fin N)} (hh : h ∈ HR N G lev Δ r) {u v : ℕ}
    (hu : u < N) (hv : v < N) (hlu : get lev u ≤ r) (hlv : get lev v ≤ r) :
    Adj G (act h u) (act h v) ↔ Adj G u v := by
  have hlu' := hh.1.2.1 u hu
  have hlv' := hh.1.2.1 v hv
  by_cases hc : get lev u < r ∨ get lev v < r ∨ (get lev u = 0 ∧ get lev v = 0)
  · have e₁ : EdgeR G lev r u v ↔ Adj G u v :=
      ⟨fun h' => h'.1, fun h' => ⟨h', hlu, hlv, hc⟩⟩
    have e₂ : EdgeR G lev r (act h u) (act h v) ↔ Adj G (act h u) (act h v) :=
      ⟨fun h' => h'.1, fun h' => ⟨h', by omega, by omega, by rw [hlu', hlv']; exact hc⟩⟩
    rw [← e₁, ← e₂]
    exact hh.1.2.2 u v hu hv
  · exact adj_iff_of_HR hZ hh hu hv (by omega) (by omega)

include hZ in
/-- Adjacency between a new point and a point below is preserved by the lift. -/
theorem adj_iff_new {r : ℕ} {h : Perm (Fin N)} (hh : h ∈ HR N G lev Δ r) {u v : ℕ}
    (hu : u < N) (hv : v < N) (hlu : get lev u = r + 1) (hlv : get lev v ≤ r) :
    Adj G (liftFun N G lev r h u) (act h v) ↔ Adj G u v := by
  have hlv' := hh.1.2.1 v hv
  have hnb := nb_liftFun hZ hh hu hlu
  have hlL := lev_liftFun hZ hh hu
  constructor
  · intro hadj
    have hle := hZ.levels.adj_le _ _ hadj
    rw [hlL, hlu, hlv'] at hle
    have hvr : get lev v = r := by omega
    have hmem : act h v ∈ nb G lev r (liftFun N G lev r h u) := mem_nb.2 ⟨hadj, by omega⟩
    rw [hnb, Finset.mem_image] at hmem
    obtain ⟨v', hv', he⟩ := hmem
    rw [act_injective h he] at hv'
    exact (mem_nb.1 hv').1
  · intro hadj
    have hle := hZ.levels.adj_le _ _ hadj
    have hvr : get lev v = r := by omega
    have hmem : v ∈ nb G lev r u := mem_nb.2 ⟨hadj, hvr⟩
    have : act h v ∈ nb G lev r (liftFun N G lev r h u) := by
      rw [hnb]
      exact Finset.mem_image_of_mem _ hmem
    exact (mem_nb.1 this).1

include hZ in
/-- The lift preserves the edges of `Z_{r+1}`. -/
theorem edgeR_liftFun {r : ℕ} {h : Perm (Fin N)} (hh : h ∈ HR N G lev Δ r) {u v : ℕ}
    (hu : u < N) (hv : v < N) :
    EdgeR G lev (r + 1) (liftFun N G lev r h u) (liftFun N G lev r h v) ↔
      EdgeR G lev (r + 1) u v := by
  have hlu := lev_liftFun hZ hh hu
  have hlv := lev_liftFun hZ hh hv
  rcases Nat.lt_or_ge (r + 1) (get lev u) with hu' | hu'
  · exact ⟨fun h' => absurd h' (not_edgeR_of_gt (Or.inl (by omega))),
      fun h' => absurd h' (not_edgeR_of_gt (Or.inl hu'))⟩
  rcases Nat.lt_or_ge (r + 1) (get lev v) with hv' | hv'
  · exact ⟨fun h' => absurd h' (not_edgeR_of_gt (Or.inr (by omega))),
      fun h' => absurd h' (not_edgeR_of_gt (Or.inr hv'))⟩
  rcases Nat.lt_or_ge (get lev u) (r + 1) with hu₁ | hu₁ <;>
    rcases Nat.lt_or_ge (get lev v) (r + 1) with hv₁ | hv₁
  · -- both below
    rw [liftFun_old (by omega), liftFun_old (by omega),
      edgeR_iff_adj (by rw [hh.1.2.1 u hu]; omega) (by rw [hh.1.2.1 v hv]; omega),
      edgeR_iff_adj (by omega) (by omega)]
    exact adj_iff_low hZ hh hu hv (by omega) (by omega)
  · -- `v` new
    rw [liftFun_old (h := h) (w := u) (by omega),
      edgeR_iff_adj (by rw [hh.1.2.1 u hu]; omega) (by omega), edgeR_iff_adj (by omega) hv']
    constructor
    · intro hadj
      exact hZ.valid.symm _ _ ((adj_iff_new hZ hh hv hu (by omega) (by omega)).1
        (hZ.valid.symm _ _ hadj))
    · intro hadj
      exact hZ.valid.symm _ _ ((adj_iff_new hZ hh hv hu (by omega) (by omega)).2
        (hZ.valid.symm _ _ hadj))
  · -- `u` new
    rw [liftFun_old (h := h) (w := v) (by omega),
      edgeR_iff_adj' (by omega) (by rw [hh.1.2.1 v hv]; omega), edgeR_iff_adj' hu' (by omega)]
    exact adj_iff_new hZ hh hu hv (by omega) (by omega)
  · -- both new
    exact ⟨fun h' => absurd h' (not_edgeR_new (by omega) (by omega)),
      fun h' => absurd h' (not_edgeR_new (by omega) (by omega))⟩

include hZ in
/-- **The lift lies in `A_{r+1}`.** -/
theorem liftPerm_mem {r : ℕ} {h : Perm (Fin N)} (hh : h ∈ HR N G lev Δ r) :
    liftPerm hZ hh ∈ AutR N G lev (r + 1) := by
  refine ⟨fun v hv hr => ?_, fun v hv => ?_, fun u v hu hv => ?_⟩
  · rw [act_liftPerm hZ, liftFun_old (by omega)]
    exact hh.1.1 v hv (by omega)
  · rw [act_liftPerm hZ]
    exact lev_liftFun hZ hh hv
  · rw [act_liftPerm hZ, act_liftPerm hZ]
    exact edgeR_liftFun hZ hh hu hv

end GraphIso.Graph
