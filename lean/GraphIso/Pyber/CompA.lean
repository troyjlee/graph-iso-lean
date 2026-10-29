module

public import Mathlib.GroupTheory.IsSubnormal
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Data.Nat.Factorization.Basic

/-!
# Abelian composition factors

Stage 15a (`PLAN-15.md` §3, items 1–3). Pyber's analysis (arXiv:1605.08266) counts the abelian
composition factors of point stabilizers. We define them without composition series.

* **The definition** (`compA`): the primes `p` for which `G` has subgroups `B ≤ A` with `A`
  subnormal (mathlib's `Subgroup.IsSubnormal`), `B` normal in `A`, and `[A : B] = p`. By Schreier
  refinement and Jordan–Hölder these are exactly the orders of the abelian composition factors
  (Pyber's `Comp_A`). That equivalence is neither proved nor used: every property below is proved
  from this definition.
* **Basic properties:** `compA G` consists of prime divisors of `|G|` (`compA_subset_primeFactors`),
  so it has at most `⌊log₂ |G|⌋` elements (`ncard_compA_le`); it can only shrink along surjective
  homomorphisms (`compA_subset_of_surjective`) and is an isomorphism invariant
  (`compA_eq_of_mulEquiv`); it contains `compA` of every subnormal subgroup
  (`compA_subset_of_isSubnormal`), and that of every injective image that is subnormal
  (`compA_subset_of_injective`); a normal subgroup of prime index `p` puts `p` in it
  (`mem_compA_of_index`), and so does any prime dividing the order of a commutative group
  (`mem_compA_of_comm`); a nonabelian simple group has none (`compA_eq_empty_of_isSimpleGroup`).
* **Extensions** (`compA_subset_union`): for `N` normal, `compA G ⊆ compA N ∪ compA (G ⧸ N)`,
  from `[A : B] = [A ⊓ N : B ⊓ N] · [A ⊔ N : B ⊔ N]` (`relIndex_eq_mul_relIndex`). The form with a
  homomorphism whose range is subnormal is `compA_subset_union_of_hom`.
* **Pyber's Proposition 3** (`compA_sdiff_subset`): for every subgroup `H`,
  `compA G ∖ compA H ⊆ primeFactors [G : H]`. For subnormal `A`, `[A : A ⊓ H]` divides `[G : H]`
  (`relIndex_dvd_index_of_isSubnormal`); then a prime index `p ∤ [G : H]` survives the
  intersection with `H`.
-/

@[expose] public section

namespace GraphIso.Pyber

open Subgroup

/-- **The abelian composition factors** of `G`, as a set of primes: `p ∈ compA G` iff there are
subgroups `B ≤ A` of `G` with `A` subnormal, `B` normal in `A` and `[A : B] = p`. (Equivalently,
by Schreier refinement and Jordan–Hölder, the orders of the abelian composition factors of `G`;
this equivalence is not proved here and nothing uses it.) -/
def compA (G : Type*) [Group G] : Set ℕ :=
  {p | p.Prime ∧ ∃ A B : Subgroup G, A.IsSubnormal ∧ B ≤ A ∧ (B.subgroupOf A).Normal ∧
    B.relIndex A = p}

section Basic

variable {G G' : Type*} [Group G] [Group G']

/-- `m` has at most `⌊log₂ m⌋` distinct prime factors. -/
theorem card_primeFactors_le_log (m : ℕ) : m.primeFactors.card ≤ Nat.log 2 m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  apply Nat.le_log_of_pow_le (by norm_num)
  calc 2 ^ m.primeFactors.card ≤ ∏ p ∈ m.primeFactors, p :=
        Finset.pow_card_le_prod _ _ _ fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
    _ ≤ m := Nat.le_of_dvd hm (Nat.prod_primeFactors_dvd m)

/-- **`compA G` consists of prime divisors of `|G|`.** -/
theorem compA_subset_primeFactors [Finite G] : compA G ⊆ ↑(Nat.card G).primeFactors := by
  rintro p ⟨hp, A, B, -, -, -, rfl⟩
  rw [Finset.mem_coe, Nat.mem_primeFactors]
  exact ⟨hp, (relIndex_dvd_card B A).trans (card_subgroup_dvd_card A), Nat.card_pos.ne'⟩

theorem compA_finite [Finite G] : (compA G).Finite :=
  (Finset.finite_toSet _).subset compA_subset_primeFactors

/-- `|compA G| ≤ ω(|G|)`. -/
theorem ncard_compA_le_card_primeFactors [Finite G] :
    (compA G).ncard ≤ (Nat.card G).primeFactors.card :=
  (Set.ncard_le_ncard compA_subset_primeFactors (Finset.finite_toSet _)).trans
    (Set.ncard_coe_finset _).le

/-- **`|compA G| ≤ ⌊log₂ |G|⌋`.** -/
theorem ncard_compA_le [Finite G] : (compA G).ncard ≤ Nat.log 2 (Nat.card G) :=
  ncard_compA_le_card_primeFactors.trans (card_primeFactors_le_log _)

/-- The trivial group has no abelian composition factors. -/
theorem compA_eq_empty_of_subsingleton [Subsingleton G] : compA G = ∅ := by
  have : Finite G := Finite.of_subsingleton
  apply Set.eq_empty_of_subset_empty
  refine compA_subset_primeFactors.trans ?_
  simp [Nat.card_unique]

/-- Normality of a pair transported along a preimage. -/
theorem normal_comap_pair (f : G →* G') {A B : Subgroup G'} (hBA : B ≤ A)
    (hN : (B.subgroupOf A).Normal) : ((B.comap f).subgroupOf (A.comap f)).Normal := by
  rw [normal_subgroupOf_iff_le_normalizer (comap_mono hBA)]
  rw [normal_subgroupOf_iff_le_normalizer hBA] at hN
  exact (comap_mono hN).trans (le_normalizer_comap f)

/-- Normality of a pair transported along an image. -/
theorem normal_map_pair (f : G →* G') {A B : Subgroup G} (hBA : B ≤ A)
    (hN : (B.subgroupOf A).Normal) : ((B.map f).subgroupOf (A.map f)).Normal := by
  rw [normal_subgroupOf_iff_le_normalizer (map_mono hBA)]
  rw [normal_subgroupOf_iff_le_normalizer hBA] at hN
  exact (map_mono hN).trans (le_normalizer_map f)

/-- **Surjective images have fewer abelian composition factors.** -/
theorem compA_subset_of_surjective (f : G →* G') (hf : Function.Surjective f) :
    compA G' ⊆ compA G := by
  rintro p ⟨hp, A, B, hA, hBA, hN, rfl⟩
  refine ⟨hp, A.comap f, B.comap f, hA.comap f, comap_mono hBA, normal_comap_pair f hBA hN, ?_⟩
  rw [relIndex_comap, map_comap_eq_self_of_surjective hf]

/-- **`compA` is an isomorphism invariant.** -/
theorem compA_eq_of_mulEquiv (e : G ≃* G') : compA G = compA G' :=
  (compA_subset_of_surjective e.symm.toMonoidHom e.symm.surjective).antisymm
    (compA_subset_of_surjective e.toMonoidHom e.surjective)

/-- An image of a subnormal subgroup under a homomorphism whose range is subnormal is subnormal. -/
theorem isSubnormal_map_of_range (f : G →* G') (hr : f.range.IsSubnormal) {A : Subgroup G}
    (hA : A.IsSubnormal) : (A.map f).IsSubnormal := by
  have h := (hA.map f.rangeRestrict_surjective).trans' hr
  rwa [map_map, MonoidHom.subtype_comp_rangeRestrict] at h

/-- **Injective images with subnormal range keep their abelian composition factors.** -/
theorem compA_subset_of_injective (f : G →* G') (hf : Function.Injective f)
    (hr : f.range.IsSubnormal) : compA G ⊆ compA G' := by
  rintro p ⟨hp, A, B, hA, hBA, hN, rfl⟩
  exact ⟨hp, A.map f, B.map f, isSubnormal_map_of_range f hr hA, map_mono hBA,
    normal_map_pair f hBA hN, relIndex_map_map_of_injective _ _ hf⟩

/-- **Subnormal subgroups.** -/
theorem compA_subset_of_isSubnormal {H : Subgroup G} (hH : H.IsSubnormal) :
    compA H ⊆ compA G :=
  compA_subset_of_injective H.subtype H.subtype_injective (by rwa [range_subtype])

/-- `compA` of the range of a homomorphism lies in that of its source. -/
theorem compA_range_subset (f : G →* G') : compA f.range ⊆ compA G :=
  compA_subset_of_surjective f.rangeRestrict f.rangeRestrict_surjective

/-- **A normal subgroup of prime index `p` puts `p` in `compA`.** -/
theorem mem_compA_of_index {N : Subgroup G} [N.Normal] {p : ℕ} (hp : p.Prime)
    (h : N.index = p) : p ∈ compA G :=
  ⟨hp, ⊤, N, IsSubnormal.top, le_top, normal_subgroupOf, by rw [relIndex_top_right, h]⟩

/-- **Commutative groups:** every prime divisor of the order is in `compA`. -/
theorem mem_compA_of_comm [Finite G] (hc : ∀ a b : G, a * b = b * a) {p : ℕ} (hp : p.Prime)
    (hd : p ∣ Nat.card G) : p ∈ compA G := by
  have := Fact.mk hp
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hd
  have hN : (zpowers g).Normal := ⟨fun n hn x => by rwa [hc x n, mul_inv_cancel_right]⟩
  refine ⟨hp, zpowers g, ⊥, hN.isSubnormal, bot_le, normal_subgroupOf, ?_⟩
  rw [relIndex_bot_left, Nat.card_zpowers, hg]

/-- **Nonabelian simple groups have no abelian composition factors.** -/
theorem compA_eq_empty_of_isSimpleGroup [Finite G] [hG : IsSimpleGroup G]
    (hnc : ∃ a b : G, a * b ≠ b * a) : compA G = ∅ := by
  apply Set.eq_empty_of_forall_notMem
  rintro p ⟨hp, A, B, hA, hBA, hN, hidx⟩
  rcases hA.eq_bot_or_top_of_isSimpleGroup hG with rfl | rfl
  · rw [le_bot_iff.mp hBA, relIndex_self] at hidx
    exact hp.ne_one hidx.symm
  · have hBn : B.Normal := by
      rw [normal_subgroupOf_iff_le_normalizer le_top, top_le_iff] at hN
      exact normalizer_eq_top_iff.mp hN
    rcases hBn.eq_bot_or_eq_top with rfl | rfl
    · rw [relIndex_top_right, index_bot] at hidx
      have := Fact.mk hp
      have := isCyclic_of_prime_card hidx
      obtain ⟨a, b, hab⟩ := hnc
      exact hab ((IsMulCommutative.is_comm (M := G)).comm a b)
    · rw [relIndex_self] at hidx
      exact hp.ne_one hidx.symm

end Basic

section Extension

variable {G G' : Type*} [Group G] [Group G']

theorem relIndex_ne_zero_of_finite [Finite G] (H K : Subgroup G) : H.relIndex K ≠ 0 := by
  intro h
  have := relIndex_mul_card H K
  rw [h, zero_mul] at this
  exact Nat.card_pos.ne' this.symm

/-- **The index of a pair splits across a normal subgroup:**
`[A : B] = [A ⊓ N : B ⊓ N] · [A ⊔ N : B ⊔ N]`. -/
theorem relIndex_eq_mul_relIndex [Finite G] {N A B : Subgroup G} [N.Normal] (hBA : B ≤ A) :
    B.relIndex A = (B ⊓ N).relIndex (A ⊓ N) * (B ⊔ N).relIndex (A ⊔ N) := by
  have h1 := relIndex_mul_relIndex (B ⊓ N) B A inf_le_left hBA
  have h2 := relIndex_mul_relIndex (B ⊓ N) (A ⊓ N) A (inf_le_inf_right N hBA) inf_le_left
  have h5 := relIndex_mul_relIndex N (B ⊔ N) (A ⊔ N) le_sup_right (sup_le_sup_right hBA N)
  have h3 : (B ⊓ N).relIndex B = N.relIndex (B ⊔ N) := by
    rw [inf_relIndex_left, relIndex_sup_right]
  have h4 : (A ⊓ N).relIndex A = N.relIndex (A ⊔ N) := by
    rw [inf_relIndex_left, relIndex_sup_right]
  rw [h3] at h1
  rw [h4, ← h5] at h2
  have hne : N.relIndex (B ⊔ N) ≠ 0 := relIndex_ne_zero_of_finite _ _
  apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne)
  rw [h1, ← h2]
  ring

/-- `[A ⊓ N : B ⊓ N]` as an index inside `N`. -/
theorem relIndex_subgroupOf_eq {N A B : Subgroup G} (hBA : B ≤ A) :
    (B.subgroupOf N).relIndex (A.subgroupOf N) = (B ⊓ N).relIndex (A ⊓ N) := by
  rw [show (B.subgroupOf N).relIndex (A.subgroupOf N) = B.relIndex ((A.subgroupOf N).map N.subtype)
    from relIndex_comap B N.subtype (A.subgroupOf N), subgroupOf_map_subtype]
  rw [← inf_relIndex_right B (A ⊓ N), ← inf_relIndex_right (B ⊓ N) (A ⊓ N)]
  congr 1
  ext x
  simp only [mem_inf]
  exact ⟨fun ⟨hb, _, hn⟩ => ⟨⟨hb, hn⟩, hBA hb, hn⟩, fun ⟨⟨hb, _⟩, ha, hn⟩ => ⟨hb, ha, hn⟩⟩

/-- **Extensions:** `compA G ⊆ compA N ∪ compA (G ⧸ N)` for `N` normal. -/
theorem compA_subset_union [Finite G] (N : Subgroup G) [N.Normal] :
    compA G ⊆ compA N ∪ compA (G ⧸ N) := by
  rintro p ⟨hp, A, B, hA, hBA, hN, hidx⟩
  rw [relIndex_eq_mul_relIndex (N := N) hBA] at hidx
  rcases (Nat.prime_mul_iff.mp (hidx ▸ hp)) with ⟨-, h1⟩ | ⟨-, h1⟩
  · -- the factor lies in `N`
    left
    refine ⟨hp, A.subgroupOf N, B.subgroupOf N, hA.subgroupOf, comap_mono hBA,
      normal_comap_pair N.subtype hBA hN, ?_⟩
    rw [relIndex_subgroupOf_eq hBA, ← hidx, h1, mul_one]
  · -- the factor lies in `G ⧸ N`
    right
    refine ⟨hp, A.map (QuotientGroup.mk' N), B.map (QuotientGroup.mk' N),
      hA.map (QuotientGroup.mk'_surjective N), map_mono hBA, normal_map_pair _ hBA hN, ?_⟩
    rw [relIndex_map_map, QuotientGroup.ker_mk', ← hidx, h1, one_mul]

/-- **Extensions, through a homomorphism with subnormal range:**
`compA G ⊆ compA (ker f) ∪ compA G'`. -/
theorem compA_subset_union_of_hom [Finite G] (f : G →* G') (hr : f.range.IsSubnormal) :
    compA G ⊆ compA f.ker ∪ compA G' := by
  refine (compA_subset_union f.ker).trans (Set.union_subset_union_right _ ?_)
  rw [compA_eq_of_mulEquiv (QuotientGroup.quotientKerEquivRange f)]
  exact compA_subset_of_injective f.range.subtype f.range.subtype_injective
    (by rwa [range_subtype])

/-- A quotient by the kernel of a homomorphism with subnormal range. -/
theorem compA_quot_subset_of_hom (f : G →* G') (K : Subgroup G) [K.Normal] (hK : f.ker = K)
    (hr : f.range.IsSubnormal) : compA (G ⧸ K) ⊆ compA G' := by
  subst hK
  rw [compA_eq_of_mulEquiv (QuotientGroup.quotientKerEquivRange f)]
  exact compA_subset_of_injective f.range.subtype f.range.subtype_injective
    (by rwa [range_subtype])

end Extension

section Index

variable {G : Type*} [Group G]

/-- For `A` normal, `[A : A ⊓ H]` divides `[G : H]`. -/
theorem relIndex_dvd_index_of_normal_right [Finite G] (H : Subgroup G) {A : Subgroup G}
    [A.Normal] : H.relIndex A ∣ H.index := by
  have h1 := relIndex_inf_mul_relIndex H A ⊤
  rw [inf_top_eq, relIndex_top_right, relIndex_top_right,
    ← relIndex_mul_index (inf_le_left : H ⊓ A ≤ H), inf_relIndex_left] at h1
  obtain ⟨c, hc⟩ := relIndex_dvd_index_of_le (le_sup_right : A ≤ H ⊔ A)
  rw [relIndex_sup_right] at hc
  rw [hc] at h1
  have hne : A.relIndex H ≠ 0 := relIndex_ne_zero_of_finite _ _
  refine ⟨c, Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne) ?_⟩
  rw [← h1]
  ring

/-- **For `A` subnormal, `[A : A ⊓ H]` divides `[G : H]`.** -/
theorem relIndex_dvd_index_of_isSubnormal [Finite G] (H : Subgroup G) {A : Subgroup G}
    (hA : A.IsSubnormal) : H.relIndex A ∣ H.index := by
  induction hA with
  | top => rw [relIndex_top_right]
  | step A K hAK _ hN ih =>
    have h := relIndex_dvd_index_of_normal_right (H.subgroupOf K) (A := A.subgroupOf K)
    rw [relIndex_subgroupOf hAK] at h
    exact h.trans ih

/-- **Pyber's Proposition 3:** `compA G ∖ compA H ⊆ primeFactors [G : H]`. -/
theorem compA_sdiff_subset [Finite G] (H : Subgroup G) :
    compA G \ compA H ⊆ ↑H.index.primeFactors := by
  rintro p ⟨⟨hp, A, B, hA, hBA, hN, hidx⟩, hnot⟩
  rw [Finset.mem_coe, Nat.mem_primeFactors]
  refine ⟨hp, ?_, index_ne_zero_of_finite⟩
  by_contra hpd
  apply hnot
  refine ⟨hp, A.subgroupOf H, B.subgroupOf H, hA.subgroupOf, comap_mono hBA,
    normal_comap_pair H.subtype hBA hN, ?_⟩
  rw [show (B.subgroupOf H).relIndex (A.subgroupOf H) = B.relIndex ((A.subgroupOf H).map H.subtype)
    from relIndex_comap B H.subtype (A.subgroupOf H), subgroupOf_map_subtype]
  -- `x = [A ⊓ H : B ⊓ A ⊓ H]` divides `p`
  have hx : B.relIndex (A ⊓ H) ∣ p := by
    have := hN
    have h := relIndex_dvd_index_of_normal (H := B.subgroupOf A) ((A ⊓ H).subgroupOf A)
    rwa [relIndex_subgroupOf inf_le_left, ← relIndex, hidx] at h
  -- and `p` divides `x · [A : A ⊓ H]`
  have hpx : p ∣ B.relIndex (A ⊓ H) * H.relIndex A := by
    have h1 := relIndex_inf_mul_relIndex B H A
    have h2 := relIndex_mul_relIndex (B ⊓ H) B A inf_le_left hBA
    rw [← h2, hidx, inf_comm H A] at h1
    rw [h1]
    exact dvd_mul_left p _
  have hcop : ¬ p ∣ H.relIndex A := fun h =>
    hpd (h.trans (relIndex_dvd_index_of_isSubnormal H hA))
  exact Nat.dvd_antisymm hx ((hp.dvd_mul.mp hpx).resolve_right hcop)

end Index

end GraphIso.Pyber
