module

public import GraphIso.Pyber.Bridge
public import Mathlib.Tactic.Linarith

/-!
# Pyber's Lemma 8: the reduction for imprimitive groups

Stage 15c, in the abstract form: `H ≤ G` is core-free of index `n`, neither `⊤` nor maximal.

* **The core-free image of a subgroup** (`compA_subset_union_core`): for every subgroup `L` of
  a finite group `A`, `compA L ⊆ compA A ∪ compA L'`, where `L'` is the image of `L` in
  `A ⧸ L.normalCore`: the core is normal in `A` and contained in `L`.
* **Lemma 8** (`exists_ncard_compA_le`): suppose that `|compA H'| ≤ F m` for every core-free
  `H'` of index `m < n` (in any finite group in `Type`). Then `|compA H| ≤ F t + F b + λ(b)` for
  some `t, b ≥ 2` with `t b = n`. Take `M ≠ ⊤` covering `H`, `t = [G : M]`, `b = [M : H]`, and
  `K = M.normalCore`:
  - `K = ⊥`: `M` is core-free of index `t`, and `compA H ⊆ compA M ∪ compA H'`, `H'` the image
    of `H` in `M ⧸ core`, core-free of index `b`;
  - `K ≠ ⊥`: `K ⊔ H = M`, so `H` maps onto `M ⧸ K`, which is core-free of index `t` in
    `G ⧸ K`, with kernel `K ∩ H`. In `K`, `compA (K ∩ H) ⊆ compA K ∪ compA L'` with `L'` the
    core-free image of `K ∩ H` in `K ⧸ J` of index `b`; and
    `compA K ⊆ compA (K ⧸ J) ⊆ compA L' ∪ primeFactors b` (stage 15b and Proposition 3).
-/

@[expose] public section

namespace GraphIso.Pyber

open Subgroup

/-- **The core-free image of a subgroup:** `compA L ⊆ compA A ∪ compA L'`, where `L'` is the
image of `L` in `A ⧸ L.normalCore`. -/
theorem compA_subset_union_core {A : Type*} [Group A] [Finite A] (L : Subgroup A) :
    compA L ⊆ compA A ∪ compA (L.map (QuotientGroup.mk' L.normalCore)) := by
  set J := L.normalCore
  have hJL : J ≤ L := normalCore_le L
  have : (J.subgroupOf L).Normal := Normal.subgroupOf inferInstance L
  refine (compA_subset_union (J.subgroupOf L)).trans (Set.union_subset_union ?_ ?_)
  · rw [compA_eq_of_mulEquiv (subgroupOfEquivOfLe hJL)]
    exact compA_subset_of_isSubnormal (Normal.isSubnormal inferInstance)
  · set f : L →* L.map (QuotientGroup.mk' J) :=
      ((QuotientGroup.mk' J).comp L.subtype).codRestrict _ fun l => mem_map_of_mem _ l.2
    have hker : f.ker = J.subgroupOf L := by
      ext l
      rw [MonoidHom.mem_ker, mem_subgroupOf]
      constructor
      · intro h
        have h1 : QuotientGroup.mk' J (l : A) = 1 := congrArg Subtype.val h
        rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      · intro h
        exact Subtype.ext ((QuotientGroup.eq_one_iff (l : A)).mpr h)
    have hsurj : Function.Surjective f := by
      rintro ⟨q, hq⟩
      obtain ⟨l, hl, rfl⟩ := mem_map.mp hq
      exact ⟨⟨l, hl⟩, rfl⟩
    exact compA_quot_subset_of_hom f _ hker (by
      rw [MonoidHom.range_eq_top.mpr hsurj]
      exact IsSubnormal.top)

/-- `compA (K ∩ H)`, as a subgroup of `H` or of `K`, is the same. -/
theorem compA_subgroupOf_comm {G : Type*} [Group G] (H K : Subgroup G) :
    compA (K.subgroupOf H) = compA (H.subgroupOf K) := by
  rw [← inf_subgroupOf_right K H, ← inf_subgroupOf_right H K,
    compA_eq_of_mulEquiv (subgroupOfEquivOfLe (inf_le_right : K ⊓ H ≤ H)),
    compA_eq_of_mulEquiv (subgroupOfEquivOfLe (inf_le_right : H ⊓ K ≤ K)), inf_comm]

/-- **Pyber's Lemma 8, abstract form.** If every core-free subgroup of index `m < n` (in a finite
group in `Type`) has `|compA| ≤ F m`, then a core-free `H` of index `n` that is neither `⊤` nor
maximal has `|compA H| ≤ F t + F b + λ(b)` for some `t, b ≥ 2` with `t b = n`. -/
theorem exists_ncard_compA_le (F : ℕ → ℕ) {n : ℕ}
    (ih : ∀ m < n, ∀ (G : Type) [Group G] [Finite G] (H : Subgroup G), H.normalCore = ⊥ →
      H.index = m → (compA H).ncard ≤ F m)
    {G : Type} [Group G] [Finite G] {H : Subgroup G} (hc : H.normalCore = ⊥) (hn : H.index = n)
    (htop : H ≠ ⊤) (hmax : ¬IsCoatom H) :
    ∃ t b, 2 ≤ t ∧ 2 ≤ b ∧ t * b = n ∧ (compA H).ncard ≤ F t + F b + Nat.log 2 b := by
  obtain ⟨M, hcov, hM⟩ := exists_covBy_ne_top htop hmax
  set t := M.index
  set b := H.relIndex M
  have hbt : b * t = n := by rw [← hn]; exact relIndex_mul_index hcov.le
  have hb2 : 2 ≤ b := by
    have h0 : b ≠ 0 := relIndex_ne_zero_of_finite H M
    have h1 : b ≠ 1 := fun h => hcov.lt.not_ge (relIndex_eq_one.mp h)
    omega
  have ht2 : 2 ≤ t := by
    have h0 : t ≠ 0 := index_ne_zero_of_finite
    have h1 : t ≠ 1 := fun h => hM (index_eq_one.mp h)
    omega
  have htn : t < n := by rw [← hbt]; nlinarith
  have hbn : b < n := by rw [← hbt]; nlinarith
  refine ⟨t, b, ht2, hb2, by rw [mul_comm]; exact hbt, ?_⟩
  set K := M.normalCore
  by_cases hK : K = ⊥
  · -- `M` is core-free
    have hMt := ih t htn G M hK rfl
    set L := H.subgroupOf M
    have hLb := ih b hbn _ (L.map (QuotientGroup.mk' L.normalCore)) (normalCore_map_mk L)
      (by rw [index_map_mk]; rfl)
    have h1 := compA_subset_union_core L
    rw [compA_eq_of_mulEquiv (subgroupOfEquivOfLe hcov.le)] at h1
    have h2 := (Set.ncard_le_ncard h1 ((compA_finite).union compA_finite)).trans
      (Set.ncard_union_le _ _)
    omega
  · -- `K ⊔ H = M`
    have hKH : K ⊔ H = M := sup_eq_of_covBy hcov M.normalCore_le hc hK
    -- `H` maps onto the image of `M` in `G ⧸ K`
    set f : H →* M.map (QuotientGroup.mk' K) :=
      ((QuotientGroup.mk' K).comp H.subtype).codRestrict _ fun h => mem_map_of_mem _ (hcov.le h.2)
    have hsurj : Function.Surjective f := by
      rintro ⟨q, hq⟩
      obtain ⟨m, hm, rfl⟩ := mem_map.mp hq
      rw [← hKH, ← SetLike.mem_coe, normal_mul K H] at hm
      obtain ⟨k, hk, h, hh, rfl⟩ := Set.mem_mul.mp hm
      refine ⟨⟨h, hh⟩, Subtype.ext ?_⟩
      change (h : G ⧸ K) = ((k * h : G) : G ⧸ K)
      rw [QuotientGroup.eq]
      have := (inferInstance : K.Normal).conj_mem k hk h⁻¹
      rwa [inv_inv, mul_assoc] at this
    have hker : f.ker = K.subgroupOf H := by
      ext h
      rw [MonoidHom.mem_ker, mem_subgroupOf]
      constructor
      · intro e
        have h1 : QuotientGroup.mk' K (h : G) = 1 := congrArg Subtype.val e
        rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      · intro e
        exact Subtype.ext ((QuotientGroup.eq_one_iff (h : G)).mpr e)
    have h1 := compA_subset_union_of_hom f (by
      rw [MonoidHom.range_eq_top.mpr hsurj]
      exact IsSubnormal.top)
    rw [compA_eq_of_mulEquiv (MulEquiv.subgroupCongr hker), compA_subgroupOf_comm] at h1
    have hMt := ih t htn (G ⧸ K) (M.map (QuotientGroup.mk' K)) (normalCore_map_mk M)
      (index_map_mk M)
    -- the block: `H ∩ K` in `K`
    set L := H.subgroupOf K
    set L' := L.map (QuotientGroup.mk' L.normalCore)
    have hLidx : L.index = b := relIndex_eq_of_sup_eq hKH
    have hLb := ih b hbn _ L' (normalCore_map_mk L) (by rw [index_map_mk]; exact hLidx)
    have h2 := compA_subset_union_core L
    have h3 := compA_subset_compA_quot (H := H) (K := K) hc
    have h4 := compA_sdiff_subset L'
    rw [index_map_mk, hLidx] at h4
    have hK' : compA K ⊆ compA L' ∪ ↑b.primeFactors := by
      intro p hp
      by_cases hpL : p ∈ compA L'
      · exact Or.inl hpL
      · exact Or.inr (h4 ⟨h3 hp, hpL⟩)
    have hsub : compA H ⊆ (compA L' ∪ ↑b.primeFactors) ∪ compA (M.map (QuotientGroup.mk' K)) :=
      h1.trans (Set.union_subset_union_left _
        (h2.trans (Set.union_subset hK' Set.subset_union_left)))
    have hfin : ((compA L' ∪ ↑b.primeFactors) ∪ compA (M.map (QuotientGroup.mk' K))).Finite :=
      (compA_finite.union (Finset.finite_toSet _)).union compA_finite
    have h5 := (Set.ncard_le_ncard hsub hfin).trans (Set.ncard_union_le _ _)
    have h6 := Set.ncard_union_le (compA L') (↑b.primeFactors : Set ℕ)
    rw [Set.ncard_coe_finset] at h6
    have h7 := card_primeFactors_le_log b
    omega

end GraphIso.Pyber
