module

public import GraphIso.Graph.Lift
public import Mathlib.GroupTheory.Perm.Support

/-!
# The next layer group from the extendable subgroup

For a layered graph and a level `r`:

* `resPerm g` (`g ∈ A_{r+1}`) is `g` on level `≤ r` and the identity elsewhere; it lies in
  `HR r` (`resPerm_mem`). Its lift agrees with `g` on level `≤ r`.
* `twinSwaps r`: the transpositions of two new points with the same neighbourhood. A
  permutation of `A_{r+1}` fixing level `≤ r` pointwise is a product of them
  (`mem_closure_twinSwaps`). For maximum degree three, twin classes have at most two points,
  so such a permutation is an involution (`kernel_apply_apply`).
* **`autR_succ_eq`**: if `gens` generates `HR r`, then the lifts of `gens` and the twin swaps
  generate `A_{r+1}`.
* **`mem_HR_iff_extends`** (the extension criterion): an element of `A_r` extends to an element
  of `A_{r+1}` agreeing with it on level `≤ r` exactly when it lies in `HR r`.
-/

@[expose] public section

namespace GraphIso.Graph

open Equiv Sims

variable {Δ N : ℕ} {G : GraphData} {roots : List ℕ} {lev : Array ℕ}
  (hZ : LayeredD Δ N G roots lev)

/-! ### Restriction -/

variable (lev) in
/-- `g` on level `≤ r`, the identity elsewhere. -/
def resFun (r : ℕ) (g : Perm (Fin N)) (v : ℕ) : ℕ := if get lev v ≤ r then act g v else v

theorem resFun_resFun {r : ℕ} {g : Perm (Fin N)} (hg : ∀ v < N, get lev (act g v) = get lev v)
    {v : ℕ} (hv : v < N) : resFun lev r g⁻¹ (resFun lev r g v) = v := by
  unfold resFun
  by_cases h : get lev v ≤ r
  · have h' : get lev (act g v) ≤ r := by rw [hg v hv]; exact h
    simp only [h, h', ↓reduceIte, act_inv_act]
  · simp only [h, ↓reduceIte]

theorem lev_inv {g : Perm (Fin N)} (hg : ∀ v < N, get lev (act g v) = get lev v) :
    ∀ v < N, get lev (act g⁻¹ v) = get lev v := fun v hv => by
  have := hg _ (act_lt g⁻¹ hv)
  rw [act_act_inv] at this
  exact this.symm

theorem resFun_lt {r : ℕ} (g : Perm (Fin N)) {v : ℕ} (hv : v < N) : resFun lev r g v < N := by
  unfold resFun
  split
  · exact act_lt g hv
  · exact hv

/-- The restriction of `g ∈ A_{r+1}` to level `≤ r`, as a permutation. -/
def resPerm {r : ℕ} {g : Perm (Fin N)} (hg : g ∈ AutR N G lev (r + 1)) : Perm (Fin N) where
  toFun v := ⟨resFun lev r g v, resFun_lt g v.2⟩
  invFun v := ⟨resFun lev r g⁻¹ v, resFun_lt g⁻¹ v.2⟩
  left_inv v := Fin.ext (resFun_resFun hg.2.1 v.2)
  right_inv v := Fin.ext (by
    have := resFun_resFun (r := r) (g := g⁻¹) (lev_inv hg.2.1) v.2
    rwa [inv_inv] at this)

theorem act_resPerm {r : ℕ} {g : Perm (Fin N)} (hg : g ∈ AutR N G lev (r + 1)) (v : ℕ) :
    act (resPerm hg) v = resFun lev r g v := by
  by_cases hv : v < N
  · rw [act_of_lt _ hv]
    rfl
  · rw [act_of_ge _ (by omega)]
    unfold resFun
    split
    · rw [act_of_ge _ (by omega)]
    · rfl


/-! ### `A_{r+1}` preserves the layer string -/

theorem subL_image_of_lev {r : ℕ} {g : Perm (Fin N)}
    (hg : ∀ v < N, get lev (act g v) = get lev v) {T : Finset ℕ} (hT : SubL lev Δ N r T) :
    SubL lev Δ N r (T.image (act g)) := by
  obtain ⟨hne, hcard, hmem⟩ := hT
  refine ⟨hne.image _, (Finset.card_image_le).trans hcard, fun u hu => ?_⟩
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hu
  obtain ⟨hvN, hlv⟩ := hmem v hv
  exact ⟨act_lt g hvN, by rw [hg v hvN, hlv]⟩

include hZ in
theorem cnt_le_image {r : ℕ} {g : Perm (Fin N)} (hg : g ∈ AutR N G lev (r + 1))
    {T : Finset ℕ} : cnt G lev N r T ≤ cnt G lev N r (T.image (act g)) := by
  have hsub : (cls G lev N r T).map (act g) ⊆ cls G lev N r (T.image (act g)) := by
    intro x hx
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hx
    obtain ⟨hwN, hlw, hnb⟩ := mem_cls.1 hw
    refine mem_cls.2 ⟨act_lt g hwN, by rw [hg.2.1 w hwN, hlw], ?_⟩
    rw [nb_act hZ hg hwN hlw, hnb]
  have hnd : ((cls G lev N r T).map (act g)).Nodup :=
    (nodup_cls r T).map (act_injective g)
  have := (List.subperm_of_subset hnd hsub).length_le
  simpa [cnt] using this

include hZ in
theorem cnt_image_eq {r : ℕ} {g : Perm (Fin N)} (hg : g ∈ AutR N G lev (r + 1))
    (T : Finset ℕ) : cnt G lev N r (T.image (act g)) = cnt G lev N r T := by
  refine le_antisymm ?_ (cnt_le_image hZ hg)
  have := cnt_le_image hZ (inv_mem hg) (T := T.image (act g))
  rwa [image_act_mul, inv_mul_cancel, image_act_one] at this

theorem isEdge_image_iff {r : ℕ} {g : Perm (Fin N)} (hg : g ∈ AutR N G lev (r + 1))
    {T : Finset ℕ} (hT : SubL lev Δ N r T) : IsEdge G (T.image (act g)) ↔ IsEdge G T := by
  have hadj : ∀ u ∈ T, ∀ v ∈ T, (Adj G (act g u) (act g v) ↔ Adj G u v) := by
    intro u hu v hv
    obtain ⟨huN, hlu⟩ := hT.2.2 u hu
    obtain ⟨hvN, hlv⟩ := hT.2.2 v hv
    rw [← edgeR_iff_adj (G := G) (lev := lev) (r := r) (by rw [hg.2.1 u huN]; omega)
      (by rw [hg.2.1 v hvN]; omega), ← edgeR_iff_adj (G := G) (lev := lev) (r := r) (by omega)
      (by omega)]
    exact hg.2.2 u v huN hvN
  unfold IsEdge
  rw [Finset.card_image_of_injective _ (act_injective g)]
  constructor
  · rintro ⟨hc, x, hx, y, hy, hxy⟩
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hy
    exact ⟨hc, u, hu, v, hv, (hadj u hu v hv).1 hxy⟩
  · rintro ⟨hc, u, hu, v, hv, huv⟩
    exact ⟨hc, act g u, Finset.mem_image_of_mem _ hu, act g v, Finset.mem_image_of_mem _ hv,
      (hadj u hu v hv).2 huv⟩

include hZ in
/-- **`A_{r+1}` preserves the layer string of level `r`.** -/
theorem xval_image_eq {r : ℕ} {g : Perm (Fin N)} (hg : g ∈ AutR N G lev (r + 1))
    {T : Finset ℕ} (hT : SubL lev Δ N r T) :
    xval G lev Δ N r (T.image (act g)) = xval G lev Δ N r T := by
  simp only [xval, cnt_image_eq hZ hg, isEdge_image_iff hg hT]

include hZ in
/-- **The restriction lies in `HR r`.** -/
theorem resPerm_mem {r : ℕ} {g : Perm (Fin N)} (hg : g ∈ AutR N G lev (r + 1)) :
    resPerm hg ∈ HR N G lev Δ r := by
  have hg₁ := hg.1
  have hg₂ := hg.2.1
  have hg₃ := hg.2.2
  have hres : ∀ v, get lev v ≤ r → act (resPerm hg) v = act g v := fun v hv => by
    rw [act_resPerm]
    simp [resFun, hv]
  have hres' : ∀ v, ¬ get lev v ≤ r → act (resPerm hg) v = v := fun v hv => by
    rw [act_resPerm]
    simp [resFun, hv]
  -- adjacency below level `r + 1`
  have hadj : ∀ u v, u < N → v < N → get lev u ≤ r → get lev v ≤ r →
      (Adj G (act g u) (act g v) ↔ Adj G u v) := by
    intro u v hu hv hlu hlv
    rw [← edgeR_iff_adj (r := r) (by rw [hg₂ u hu]; exact hlu) (by rw [hg₂ v hv]; omega),
      ← edgeR_iff_adj (r := r) hlu (by omega)]
    exact hg₃ u v hu hv
  refine ⟨⟨fun v hv hr => hres' v (by omega), fun v hv => ?_, fun u v hu hv => ?_⟩, ?_⟩
  · by_cases h : get lev v ≤ r
    · rw [hres v h, hg₂ v hv]
    · rw [hres' v h]
  · by_cases h : get lev u ≤ r ∧ get lev v ≤ r
    · rw [hres u h.1, hres v h.2]
      unfold EdgeR
      rw [hadj u v hu hv h.1 h.2, hg₂ u hu, hg₂ v hv]
    · have : r < get lev u ∨ r < get lev v := by omega
      constructor
      · intro he
        exact absurd he (not_edgeR_of_gt (by
          rcases this with h' | h'
          · left
            rw [hres' u (by omega)]
            exact h'
          · right
            rw [hres' v (by omega)]
            exact h'))
      · intro he
        exact absurd he (not_edgeR_of_gt this)
  · intro T hT
    have himg : T.image (act (resPerm hg)) = T.image (act g) :=
      Finset.image_congr fun u hu => hres u (by rw [(hT.2.2 u hu).2])
    rw [himg]
    exact xval_image_eq hZ hg hT

/-! ### Twin swaps -/

variable (N G lev) in
/-- The transpositions of two new points with the same neighbourhood. -/
def twinSwaps (r : ℕ) : Set (Perm (Fin N)) :=
  {σ | ∃ w w' : Fin N, get lev w = r + 1 ∧ get lev w' = r + 1 ∧ w ≠ w' ∧
    nb G lev r w = nb G lev r w' ∧ σ = swap w w'}

include hZ in
/-- A permutation that fixes every point not of level `r + 1` and maps each new point to a new
point with the same neighbourhood lies in `A_{r+1}`. -/
theorem mem_AutR_of_twin {r : ℕ} {k : Perm (Fin N)}
    (hfix : ∀ v < N, get lev v ≠ r + 1 → act k v = v)
    (hnb : ∀ w < N, get lev w = r + 1 →
      get lev (act k w) = r + 1 ∧ nb G lev r (act k w) = nb G lev r w) :
    k ∈ AutR N G lev (r + 1) := by
  have hlev : ∀ v < N, get lev (act k v) = get lev v := fun v hv => by
    by_cases h : get lev v = r + 1
    · rw [(hnb v hv h).1, h]
    · rw [hfix v hv h]
  -- adjacency between a new point and a point below
  have hnew : ∀ u v, u < N → v < N → get lev u = r + 1 → get lev v ≤ r →
      (Adj G (act k u) v ↔ Adj G u v) := by
    intro u v hu hv hlu hlv
    obtain ⟨hlk, hnbk⟩ := hnb u hu hlu
    constructor
    · intro hadj
      have hle := hZ.levels.adj_le _ _ hadj
      have hm : v ∈ nb G lev r (act k u) := mem_nb.2 ⟨hadj, by omega⟩
      rw [hnbk] at hm
      exact (mem_nb.1 hm).1
    · intro hadj
      have hle := hZ.levels.adj_le _ _ hadj
      have hm : v ∈ nb G lev r u := mem_nb.2 ⟨hadj, by omega⟩
      rw [← hnbk] at hm
      exact (mem_nb.1 hm).1
  refine ⟨fun v hv hr => hfix v hv (by omega), hlev, fun u v hu hv => ?_⟩
  rcases Nat.lt_or_ge (r + 1) (get lev u) with hu' | hu'
  · exact ⟨fun h' => absurd h' (not_edgeR_of_gt (Or.inl (by rw [hlev u hu]; exact hu'))),
      fun h' => absurd h' (not_edgeR_of_gt (Or.inl hu'))⟩
  rcases Nat.lt_or_ge (r + 1) (get lev v) with hv' | hv'
  · exact ⟨fun h' => absurd h' (not_edgeR_of_gt (Or.inr (by rw [hlev v hv]; exact hv'))),
      fun h' => absurd h' (not_edgeR_of_gt (Or.inr hv'))⟩
  by_cases hu₁ : get lev u = r + 1 <;> by_cases hv₁ : get lev v = r + 1
  · exact ⟨fun h' => absurd h' (not_edgeR_new (by rw [hlev u hu]; exact hu₁)
      (by rw [hlev v hv]; exact hv₁)), fun h' => absurd h' (not_edgeR_new hu₁ hv₁)⟩
  · rw [hfix v hv hv₁, edgeR_iff_adj' (by rw [hlev u hu]; omega) (by omega),
      edgeR_iff_adj' hu' (by omega)]
    exact hnew u v hu hv hu₁ (by omega)
  · rw [hfix u hu hu₁, edgeR_iff_adj (by omega) (by rw [hlev v hv]; omega),
      edgeR_iff_adj (by omega) hv']
    constructor
    · intro hadj
      exact hZ.valid.symm _ _ ((hnew v u hv hu hv₁ (by omega)).1 (hZ.valid.symm _ _ hadj))
    · intro hadj
      exact hZ.valid.symm _ _ ((hnew v u hv hu hv₁ (by omega)).2 (hZ.valid.symm _ _ hadj))
  · rw [hfix u hu hu₁, hfix v hv hv₁]

theorem act_swap_fin {x y : Fin N} {v : ℕ} (hx : v ≠ x.val) (hy : v ≠ y.val) :
    act (swap x y) v = v := by
  by_cases hv : v < N
  · rw [act_of_lt _ hv, swap_apply_of_ne_of_ne (fun e => hx (congrArg Fin.val e))
      (fun e => hy (congrArg Fin.val e))]
  · rw [act_of_ge _ (by omega)]

include hZ in
/-- A twin swap lies in `A_{r+1}`. -/
theorem swap_mem_AutR {r : ℕ} {x y : Fin N} (hx : get lev x = r + 1) (hy : get lev y = r + 1)
    (hnb : nb G lev r x = nb G lev r y) : swap x y ∈ AutR N G lev (r + 1) := by
  refine mem_AutR_of_twin hZ (fun v hv hl => act_swap_fin (by rintro rfl; exact hl hx)
    (by rintro rfl; exact hl hy)) (fun w hw hlw => ?_)
  rw [act_of_lt _ hw]
  by_cases h₁ : (⟨w, hw⟩ : Fin N) = x
  · rw [h₁, swap_apply_left]
    have : w = x.val := congrArg Fin.val h₁
    subst this
    exact ⟨hy, hnb.symm⟩
  by_cases h₂ : (⟨w, hw⟩ : Fin N) = y
  · rw [h₂, swap_apply_right]
    have : w = y.val := congrArg Fin.val h₂
    subst this
    exact ⟨hx, hnb⟩
  · rw [swap_apply_of_ne_of_ne h₁ h₂]
    exact ⟨hlw, rfl⟩

include hZ in
/-- An element of `A_{r+1}` fixing level `≤ r` keeps neighbourhoods of new points. -/
theorem nb_act_of_fix {r : ℕ} {k : Perm (Fin N)} (hk : k ∈ AutR N G lev (r + 1))
    (hlow : ∀ v < N, get lev v ≤ r → act k v = v) {w : ℕ} (hw : w < N)
    (hlw : get lev w = r + 1) : nb G lev r (act k w) = nb G lev r w := by
  rw [nb_act hZ hk hw hlw]
  refine (Finset.image_congr fun u hu => ?_).trans Finset.image_id
  obtain ⟨hadj, hlu⟩ := mem_nb.1 hu
  exact hlow u (lt_of_adj hZ hadj) (by omega)

include hZ in
/-- For maximum degree three, an element of `A_{r+1}` fixing level `≤ r` is an involution. -/
theorem kernel_apply_apply (hΔ : Δ ≤ 3) {r : ℕ} {k : Perm (Fin N)}
    (hk : k ∈ AutR N G lev (r + 1))
    (hlow : ∀ v < N, get lev v ≤ r → act k v = v) (x : Fin N) : k (k x) = x := by
  by_cases hx : k x = x
  · rw [hx, hx]
  have hkx : act k x.val = (k x).val := act_of_lt _ x.2
  have hlx : get lev x = r + 1 := by
    by_contra hne
    rcases Nat.lt_or_ge (r + 1) (get lev x) with h | h
    · exact hx (Fin.ext (by rw [← hkx]; exact hk.1 x x.2 h))
    · exact hx (Fin.ext (by rw [← hkx]; exact hlow x x.2 (by omega)))
  set y := k x with hy
  have hly : get lev y = r + 1 := by rw [hy, ← hkx, hk.2.1 x x.2, hlx]
  have hnby : nb G lev r y = nb G lev r x := by
    rw [hy, ← hkx]
    exact nb_act_of_fix hZ hk hlow x.2 hlx
  have hky : act k y.val = (k y).val := act_of_lt _ y.2
  have hlky : get lev (k y) = r + 1 := by rw [← hky, hk.2.1 y y.2, hly]
  have hnbky : nb G lev r (k y) = nb G lev r x := by
    rw [← hky, nb_act_of_fix hZ hk hlow y.2 hly, hnby]
  have hxy : x ≠ y := fun e => hx e.symm
  by_contra hne
  have hkyy : k y ≠ y := fun e => hxy (k.injective (by rw [e]))
  have hsub : ({x.val, y.val, (k y).val} : Finset ℕ) ⊆
      (cls G lev N r (nb G lev r x)).toFinset := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rw [List.mem_toFinset]
    rcases hz with rfl | rfl | rfl
    · exact mem_cls_self x.2 hlx
    · exact mem_cls.2 ⟨y.2, hly, hnby⟩
    · exact mem_cls.2 ⟨(k y).2, hlky, hnbky⟩
  have hcard := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup (nodup_cls r _)] at hcard
  have h3 : ({x.val, y.val, (k y).val} : Finset ℕ).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair]
    · exact fun e => hkyy (Fin.ext e.symm)
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun e => hxy (Fin.ext e), fun e => hne (Fin.ext e.symm)⟩
  have := cnt_le hZ (r := r) (subL_nb hZ x.2 hlx).1
  unfold cnt at this
  omega

include hZ in
/-- **Elements of `A_{r+1}` fixing level `≤ r` are products of twin swaps.** -/
theorem mem_closure_twinSwaps {r : ℕ} : ∀ (m : ℕ) (k : Perm (Fin N)), k.support.card ≤ m →
    k ∈ AutR N G lev (r + 1) → (∀ v < N, get lev v ≤ r → act k v = v) →
    k ∈ Subgroup.closure (twinSwaps N G lev r)
  | 0, k, hm, _, _ => by
    have : k = 1 := Perm.support_eq_empty_iff.1 (Finset.card_eq_zero.1 (by omega))
    rw [this]
    exact one_mem _
  | m + 1, k, hm, hk, hlow => by
    by_cases hk1 : k = 1
    · rw [hk1]
      exact one_mem _
    obtain ⟨x, hx⟩ : ∃ x, k x ≠ x := by
      by_contra h
      push Not at h
      exact hk1 (Perm.ext h)
    have hkx : act k x.val = (k x).val := act_of_lt _ x.2
    -- `x` is new
    have hlx : get lev x = r + 1 := by
      by_contra hne
      rcases Nat.lt_or_ge (r + 1) (get lev x) with h | h
      · exact hx (Fin.ext (by rw [← hkx]; exact hk.1 x x.2 h))
      · exact hx (Fin.ext (by rw [← hkx]; exact hlow x x.2 (by omega)))
    set y := k x with hy
    have hly : get lev y = r + 1 := by rw [hy, ← hkx, hk.2.1 x x.2, hlx]
    have hnby : nb G lev r y = nb G lev r x := by
      rw [hy, ← hkx]
      exact nb_act_of_fix hZ hk hlow x.2 hlx
    have hxy : x ≠ y := fun e => hx e.symm
    have hky : k y ≠ y := fun e => hxy (k.injective (e.trans hy)).symm
    -- remove the transposition
    have hσ : swap x y ∈ twinSwaps N G lev r :=
      ⟨x, y, hlx, hly, hxy, hnby.symm, rfl⟩
    have hσA := swap_mem_AutR hZ hlx hly hnby.symm
    set k' := swap x y * k with hk'
    have hk'A : k' ∈ AutR N G lev (r + 1) := mul_mem hσA hk
    have hk'low : ∀ v < N, get lev v ≤ r → act k' v = v := by
      intro v hv hl
      rw [hk', act_mul, hlow v hv hl]
      exact act_swap_fin (by intro e; rw [e] at hl; omega) (by intro e; rw [e] at hl; omega)
    have hsupp : k'.support ⊂ k.support := by
      refine Finset.ssubset_iff_of_subset (fun z hz => ?_) |>.2 ⟨x, ?_, ?_⟩
      · rw [Perm.mem_support] at hz ⊢
        intro hkz
        apply hz
        have hzx : z ≠ x := fun e => hx (by rw [hy, ← e]; exact hkz)
        have hzy : z ≠ y := fun e => hky (by rw [← e]; exact hkz)
        rw [hk', Perm.mul_apply, hkz, swap_apply_of_ne_of_ne hzx hzy]
      · exact Perm.mem_support.2 hx
      · rw [Perm.mem_support, not_not, hk', Perm.mul_apply, ← hy, swap_apply_right]
    have hk'c : k'.support.card ≤ m := by
      have := Finset.card_lt_card hsupp
      omega
    have ih := mem_closure_twinSwaps m k' hk'c hk'A hk'low
    have : k = swap x y * k' := by rw [hk', ← mul_assoc, swap_mul_self, one_mul]
    rw [this]
    exact mul_mem (Subgroup.subset_closure hσ) ih

/-! ### The decomposition -/

theorem liftPerm_one {r : ℕ} : liftPerm hZ (one_mem (HR N G lev Δ r)) = 1 := by
  ext w
  exact liftFun_one

theorem liftPerm_inv {r : ℕ} {h : Perm (Fin N)} (hh : h ∈ HR N G lev Δ r) :
    liftPerm hZ (inv_mem hh) = (liftPerm hZ hh)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  ext w
  show liftFun N G lev r h⁻¹ (liftFun N G lev r h w) = w
  rw [liftFun_comp hZ (inv_mem hh) hh w.2, inv_mul_cancel, liftFun_one]

/-- The lifts of a set of elements of `HR r`. -/
def liftSet (r : ℕ) (gens : Set (Perm (Fin N))) : Set (Perm (Fin N)) :=
  {σ | ∃ h ∈ gens, ∃ hh : h ∈ HR N G lev Δ r, σ = liftPerm hZ hh}

/-- The lift of an element generated by `gens` is generated by the lifts of `gens`. -/
theorem liftPerm_mem_closure {r : ℕ} {gens : Set (Perm (Fin N))}
    (hgens : Subgroup.closure gens = HR N G lev Δ r) {h : Perm (Fin N)}
    (hh : h ∈ HR N G lev Δ r) : liftPerm hZ hh ∈ Subgroup.closure (liftSet hZ r gens) := by
  have hcl : h ∈ Subgroup.closure gens := hgens ▸ hh
  have hHR : ∀ x, x ∈ Subgroup.closure gens → x ∈ HR N G lev Δ r := fun x hx => hgens ▸ hx
  induction hcl using Subgroup.closure_induction with
  | mem x hx => exact Subgroup.subset_closure ⟨x, hx, hh, rfl⟩
  | one => rw [liftPerm_one]; exact one_mem _
  | mul x y hx hy ihx ihy =>
    rw [liftPerm_mul hZ (hHR x hx) (hHR y hy)]
    exact mul_mem (ihx (hHR x hx)) (ihy (hHR y hy))
  | inv x hx ih =>
    have := ih (hHR x hx)
    have e : liftPerm hZ hh = (liftPerm hZ (hHR x hx))⁻¹ := liftPerm_inv hZ (hHR x hx)
    rw [e]
    exact inv_mem this

/-- **The next layer group**: if `gens` generates `HR r`, the lifts of `gens` and the twin
swaps generate `A_{r+1}`. -/
theorem autR_succ_eq {r : ℕ} {gens : Set (Perm (Fin N))}
    (hgens : Subgroup.closure gens = HR N G lev Δ r) :
    Subgroup.closure (liftSet hZ r gens ∪ twinSwaps N G lev r) = AutR N G lev (r + 1) := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro σ (⟨h, -, hh, rfl⟩ | ⟨x, y, hx, hy, -, hnb, rfl⟩)
    · exact liftPerm_mem hZ hh
    · exact swap_mem_AutR hZ hx hy hnb
  · intro g hg
    have hres := resPerm_mem hZ hg
    set ℓ := liftPerm hZ hres with hℓ
    have hℓA : ℓ ∈ AutR N G lev (r + 1) := liftPerm_mem hZ hres
    -- `ℓ` agrees with `g` on level `≤ r`
    have hagree : ∀ v, get lev v ≤ r → act ℓ v = act g v := by
      intro v hv
      rw [hℓ, act_liftPerm hZ, liftFun_old (by omega), act_resPerm]
      simp [resFun, hv]
    set k := ℓ⁻¹ * g with hk
    have hkA : k ∈ AutR N G lev (r + 1) := mul_mem (inv_mem hℓA) hg
    have hklow : ∀ v < N, get lev v ≤ r → act k v = v := by
      intro v _ hv
      rw [hk, act_mul, ← hagree v hv, act_inv_act]
    have hkc := mem_closure_twinSwaps hZ k.support.card k le_rfl hkA hklow
    have hℓc := liftPerm_mem_closure hZ hgens hres
    have : g = ℓ * k := by rw [hk, ← mul_assoc, mul_inv_cancel, one_mul]
    rw [this]
    exact mul_mem (Subgroup.closure_mono Set.subset_union_left hℓc)
      (Subgroup.closure_mono Set.subset_union_right hkc)

include hZ in
/-- **The extension criterion**: an element of `A_r` extends to an element of `A_{r+1}`
(agreeing with it on level `≤ r`) exactly when it lies in `HR r`, i.e. preserves the layer
string. -/
theorem mem_HR_iff_extends {r : ℕ} {g : Perm (Fin N)} (hg : g ∈ AutR N G lev r) :
    g ∈ HR N G lev Δ r ↔
      ∃ h ∈ AutR N G lev (r + 1), ∀ v, get lev v ≤ r → act h v = act g v := by
  constructor
  · intro hH
    exact ⟨liftPerm hZ hH, liftPerm_mem hZ hH, fun v hv => by
      rw [act_liftPerm hZ, liftFun_old (by omega)]⟩
  · rintro ⟨h, hh, hagree⟩
    have e : resPerm hh = g := Equiv.ext fun x => Fin.ext (by
      have h1 := act_resPerm hh x.val
      rw [act_of_lt _ x.2] at h1
      rw [h1, ← act_of_lt g x.2]
      unfold resFun
      split
      · rename_i hl
        exact hagree x.val hl
      · rename_i hl
        exact (hg.1 x.val x.2 (by omega)).symm)
    rw [← e]
    exact resPerm_mem hZ hh

end GraphIso.Graph
