module

public import GraphIso.Pyber.CompA
public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Order.CompleteLattice.Finset

/-!
# Families of normal subgroups, and characteristically simple groups

Stage 15a (`PLAN-15.md` §3, items 4–5).

* **Trivial intersection** (`compA_subset_iUnion_of_iInf`, Pyber's Lemma 5 and Proposition 6 for
  subdirect products): for a finite family of normal subgroups `N i` with `⨅ i, N i = ⊥`,
  `compA G ⊆ ⋃ i, compA (G ⧸ N i)`. The general form (`compA_subset_biUnion_of_ker`) takes
  homomorphisms `f i : G →* Q i` with subnormal ranges and trivially intersecting kernels; it is
  proved by induction on the family, passing to the kernel of the first homomorphism.
* **Joins** (`compA_subset_iUnion_of_iSup`): for a finite family of normal subgroups with
  `⨆ i, N i = ⊤`, `compA G ⊆ ⋃ i, compA (N i)`, from `(H ⊔ L)/L ≅ H/(H ⊓ L)`.
* **Minimal normal subgroups** (`IsMinNormal`): a nontrivial finite group has one
  (`exists_isMinNormal`), and it is characteristically simple as a group
  (`IsMinNormal.charSimple`), since characteristic subgroups of a normal subgroup are normal.
* **Characteristically simple groups** (`compA_eq_empty_of_charSimple`): a finite nontrivial
  noncommutative group whose characteristic subgroups are `⊥` and `⊤` has `compA = ∅`. By
  induction on the order, with a minimal normal subgroup `M` and the join `L` of its images under
  all automorphisms (`iSup_map_mulAut_eq_top`), which is characteristic and nontrivial, hence `⊤`:
  - if `M` is commutative, `L` is a join of normal commutative subgroups, hence solvable
    (`isSolvable_biSup`); then the commutator subgroup is a proper characteristic subgroup, so it
    is `⊥` and the group is commutative, a contradiction;
  - if `M = ⊤`, the group is simple (`compA_eq_empty_of_isSimpleGroup`);
  - otherwise `compA M = ∅` by induction, and the joins lemma applies to the images of `M`.
-/

@[expose] public section

namespace GraphIso.Pyber

open Subgroup

section Families

variable {G : Type*} [Group G]

/-- A group whose top and bottom subgroups coincide has no abelian composition factors. -/
theorem compA_eq_empty_of_top_eq_bot (h : (⊤ : Subgroup G) = ⊥) : compA G = ∅ := by
  have : Subsingleton G := ⟨fun a b => by
    have ha : a ∈ (⊥ : Subgroup G) := h ▸ mem_top a
    have hb : b ∈ (⊥ : Subgroup G) := h ▸ mem_top b
    rw [mem_bot] at ha hb
    rw [ha, hb]⟩
  exact compA_eq_empty_of_subsingleton

/-- **Trivially intersecting kernels, through homomorphisms:** for `f i : G →* Q i` with
subnormal ranges and `⨅ i ∈ s, ker (f i) = ⊥`, `compA G ⊆ ⋃ i ∈ s, compA (Q i)`. -/
theorem compA_subset_biUnion_of_ker {ι : Type*} {Q : ι → Type*} [∀ i, Group (Q i)]
    (s : Finset ι) {G : Type*} [Group G] [Finite G] (f : ∀ i, G →* Q i)
    (hr : ∀ i ∈ s, (f i).range.IsSubnormal) (hk : ⨅ i ∈ s, (f i).ker = ⊥) :
    compA G ⊆ ⋃ i ∈ s, compA (Q i) := by
  classical
  induction s using Finset.induction_on generalizing G with
  | empty =>
    simp only [Finset.notMem_empty, iInf_false, iInf_top] at hk
    simp [compA_eq_empty_of_top_eq_bot hk]
  | insert j s hjs ih =>
    rw [Finset.iInf_insert] at hk
    rw [Finset.set_biUnion_insert]
    refine (compA_subset_union_of_hom (f j) (hr j (Finset.mem_insert_self j s))).trans ?_
    refine Set.union_subset (Set.subset_union_of_subset_right ?_ _) Set.subset_union_left
    set K := (f j).ker
    refine ih (fun i => (f i).comp K.subtype) (fun i hi => ?_) ?_
    · rw [MonoidHom.range_comp, range_subtype]
      exact isSubnormal_map_of_range (f i) (hr i (Finset.mem_insert_of_mem hi))
        (Normal.isSubnormal inferInstance)
    · have hk' : (⨅ i ∈ s, (f i).ker).subgroupOf K = ⊥ := by
        rw [subgroupOf_eq_bot, disjoint_iff, inf_comm, hk]
      rw [← hk', subgroupOf, comap_iInf]
      congr 1
      ext i
      rw [comap_iInf]
      rfl

/-- **Pyber's Proposition 6 (subdirect products):** if `⨅ i, N i = ⊥` for a finite family of
normal subgroups, then `compA G ⊆ ⋃ i, compA (G ⧸ N i)`. -/
theorem compA_subset_iUnion_of_iInf {G : Type*} [Group G] [Finite G] {ι : Type*} [Finite ι]
    (N : ι → Subgroup G) [∀ i, (N i).Normal] (h : ⨅ i, N i = ⊥) :
    compA G ⊆ ⋃ i, compA (G ⧸ N i) := by
  have := Fintype.ofFinite ι
  have h' := compA_subset_biUnion_of_ker (Q := fun i => G ⧸ N i) Finset.univ
    (fun i => QuotientGroup.mk' (N i))
    (fun i _ => by rw [QuotientGroup.range_mk']; exact IsSubnormal.top)
    (by simpa [QuotientGroup.ker_mk'] using h)
  exact h'.trans (Set.iUnion₂_subset fun i _ => Set.subset_iUnion (fun i => compA (G ⧸ N i)) i)

/-- `compA` of a join of two subgroups, one of them normal. -/
theorem compA_sup_subset [Finite G] (H L : Subgroup G) [L.Normal] :
    compA ↥(H ⊔ L) ⊆ compA L ∪ compA H := by
  refine (compA_subset_union (L.subgroupOf (H ⊔ L))).trans (Set.union_subset_union ?_ ?_)
  · rw [compA_eq_of_mulEquiv (subgroupOfEquivOfLe le_sup_right)]
  · rw [← compA_eq_of_mulEquiv (QuotientGroup.quotientInfEquivProdNormalQuotient H L)]
    exact compA_subset_of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)

/-- **Joins of normal subgroups**, over a finset. -/
theorem compA_biSup_subset [Finite G] {ι : Type*} (s : Finset ι) (N : ι → Subgroup G)
    [∀ i, (N i).Normal] : compA ↥(⨆ i ∈ s, N i) ⊆ ⋃ i ∈ s, compA (N i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have e : (⨆ i ∈ (∅ : Finset ι), N i) = ⊥ := by simp
    rw [e, compA_eq_empty_of_subsingleton]
    exact Set.empty_subset _
  | insert j s _ ih =>
    rw [Finset.set_biUnion_insert]
    have hL : (⨆ i ∈ s, N i).Normal := biSup_normal _ N fun i _ => inferInstance
    have e : (⨆ i ∈ insert j s, N i) = N j ⊔ ⨆ i ∈ s, N i := Finset.iSup_insert j s N
    rw [e]
    refine (compA_sup_subset (N j) _).trans ?_
    exact Set.union_subset (ih.trans Set.subset_union_right) Set.subset_union_left

/-- **Joins of normal subgroups:** if `⨆ i, N i = ⊤` for a finite family of normal subgroups,
then `compA G ⊆ ⋃ i, compA (N i)`. -/
theorem compA_subset_iUnion_of_iSup [Finite G] {ι : Type*} [Finite ι] (N : ι → Subgroup G)
    [∀ i, (N i).Normal] (h : ⨆ i, N i = ⊤) : compA G ⊆ ⋃ i, compA (N i) := by
  have := Fintype.ofFinite ι
  have h' := compA_biSup_subset Finset.univ N
  have e : (⨆ i ∈ Finset.univ, N i) = ⊤ := by simpa using h
  rw [e] at h'
  simp only [Finset.mem_univ, Set.iUnion_true] at h'
  rwa [compA_eq_of_mulEquiv (topEquiv (G := G)).symm]

end Families

section Solvable

variable {G : Type*} [Group G]

/-- Solvability transfers along an isomorphism. -/
theorem isSolvable_of_mulEquiv {G' : Type*} [Group G'] (e : G ≃* G') [Group.IsSolvable G] :
    Group.IsSolvable G' :=
  Group.isSolvable_of_surjective (f := e.toMonoidHom) fun y => ⟨e.symm y, e.apply_symm_apply y⟩

/-- A join of two normal solvable subgroups is solvable. -/
theorem isSolvable_sup (H L : Subgroup G) [L.Normal] (hH : Group.IsSolvable H)
    (hL : Group.IsSolvable L) : Group.IsSolvable ↥(H ⊔ L) := by
  have : Group.IsSolvable ↥(L.subgroupOf (H ⊔ L)) :=
    isSolvable_of_mulEquiv (subgroupOfEquivOfLe le_sup_right).symm
  have : Group.IsSolvable (H ⧸ L.subgroupOf H) := inferInstance
  have : Group.IsSolvable (↥(H ⊔ L) ⧸ L.subgroupOf (H ⊔ L)) :=
    isSolvable_of_mulEquiv (QuotientGroup.quotientInfEquivProdNormalQuotient H L)
  exact Group.isSolvable_of_subgroup_quotient (L.subgroupOf (H ⊔ L))

/-- **A finite join of normal solvable subgroups is solvable.** -/
theorem isSolvable_biSup {ι : Type*} (s : Finset ι) (N : ι → Subgroup G) [∀ i, (N i).Normal]
    (h : ∀ i ∈ s, Group.IsSolvable (N i)) : Group.IsSolvable ↥(⨆ i ∈ s, N i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have e : (⨆ i ∈ (∅ : Finset ι), N i) = ⊥ := by simp
    rw [e]
    infer_instance
  | insert j s _ ih =>
    have hL : (⨆ i ∈ s, N i).Normal := biSup_normal _ N fun i _ => inferInstance
    rw [Finset.iSup_insert j s N]
    exact isSolvable_sup _ _ (h j (Finset.mem_insert_self j s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end Solvable

section CharSimple

variable {G : Type*} [Group G]

/-- **A characteristically simple group:** its only characteristic subgroups are `⊥` and `⊤`. -/
def CharSimple (N : Type*) [Group N] : Prop :=
  ∀ C : Subgroup N, C.Characteristic → C = ⊥ ∨ C = ⊤

/-- **A minimal normal subgroup:** normal, nontrivial, and containing no smaller nontrivial normal
subgroup of `G`. -/
structure IsMinNormal (M : Subgroup G) : Prop where
  normal : M.Normal
  ne_bot : M ≠ ⊥
  min : ∀ K : Subgroup G, K.Normal → K ≠ ⊥ → K ≤ M → K = M

/-- **A nontrivial finite group has a minimal normal subgroup.** -/
theorem exists_isMinNormal [Finite G] [Nontrivial G] : ∃ M : Subgroup G, IsMinNormal M := by
  classical
  have hex : ∃ n, ∃ M : Subgroup G, M.Normal ∧ M ≠ ⊥ ∧ Nat.card M = n :=
    ⟨_, ⊤, inferInstance, top_ne_bot, rfl⟩
  obtain ⟨M, hMn, hMb, hMc⟩ := Nat.find_spec hex
  refine ⟨M, ⟨hMn, hMb, fun K hKn hKb hKM => ?_⟩⟩
  apply le_antisymm hKM
  apply le_of_eq
  symm
  apply eq_of_le_of_card_ge hKM
  rw [hMc]
  exact Nat.find_min' hex ⟨K, hKn, hKb, rfl⟩

/-- **A minimal normal subgroup is characteristically simple.** -/
theorem IsMinNormal.charSimple {M : Subgroup G} (hM : IsMinNormal M) : CharSimple M := by
  intro C hC
  have := hM.normal
  have hCn : (C.map M.subtype).Normal := inferInstance
  by_cases hb : C.map M.subtype = ⊥
  · left
    exact (map_eq_bot_iff_of_injective C M.subtype_injective).mp hb
  · right
    have h := hM.min _ hCn hb (map_subtype_le C)
    apply map_injective M.subtype_injective
    rw [h, ← MonoidHom.range_eq_map, range_subtype]

/-- A subgroup is commutative as a group when its elements commute. -/
theorem comm_of_mem {M : Subgroup G} (h : ∀ a ∈ M, ∀ b ∈ M, a * b = b * a) :
    ∀ a b : M, a * b = b * a :=
  fun a b => Subtype.ext (h a a.2 b b.2)

instance finite_mulAut [Finite G] : Finite (MulAut G) :=
  Finite.of_injective (fun σ : MulAut G => σ.toEquiv) fun _ _ h => MulEquiv.toEquiv_injective h

/-- **The images of a nontrivial subgroup under all automorphisms of a characteristically simple
group generate it.** -/
theorem iSup_map_mulAut_eq_top (hc : CharSimple G) {M : Subgroup G} (hM : M ≠ ⊥) :
    ⨆ σ : MulAut G, M.map σ.toMonoidHom = ⊤ := by
  set L := ⨆ σ : MulAut G, M.map σ.toMonoidHom
  have hchar : L.Characteristic := by
    rw [characteristic_iff_map_eq]
    intro τ
    rw [Subgroup.map_iSup]
    simp_rw [map_map]
    exact (Equiv.mulLeft τ).iSup_comp (g := fun σ : MulAut G => M.map σ.toMonoidHom)
  rcases hc L hchar with h | h
  · exfalso
    apply hM
    rw [eq_bot_iff, ← h]
    have h1 : M.map (1 : MulAut G).toMonoidHom = M := by
      ext x
      simp
    calc M = M.map (1 : MulAut G).toMonoidHom := h1.symm
      _ ≤ L := le_iSup (fun σ : MulAut G => M.map σ.toMonoidHom) 1
  · exact h

/-- A nontrivial solvable group whose commutator subgroup is `⊥` is commutative. -/
theorem comm_of_commutator_eq_bot (h : commutator G = ⊥) : ∀ a b : G, a * b = b * a := by
  have := (_root_.commutator_eq_bot_iff (G := G)).mp h
  exact fun a b => (IsMulCommutative.is_comm (M := G)).comm a b

/-- The core induction for characteristically simple groups. -/
theorem compA_eq_empty_of_charSimple_aux (n : ℕ) :
    ∀ (N : Type*) [Group N] [Finite N], Nat.card N = n → Nontrivial N → CharSimple N →
      (∃ a b : N, a * b ≠ b * a) → compA N = ∅ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro N _ _ hn _ hc hnc
  obtain ⟨M, hM⟩ := exists_isMinNormal (G := N)
  have := hM.normal
  set L := ⨆ σ : MulAut N, M.map σ.toMonoidHom with hL
  have hLt : L = ⊤ := iSup_map_mulAut_eq_top hc hM.ne_bot
  have hnorm : ∀ σ : MulAut N, (M.map σ.toMonoidHom).Normal := fun σ =>
    hM.normal.map _ σ.surjective
  by_cases hab : ∀ a ∈ M, ∀ b ∈ M, a * b = b * a
  · -- `M` commutative: the group is solvable, hence commutative
    exfalso
    have := Fintype.ofFinite (MulAut N)
    have hsol : ∀ σ : MulAut N, Group.IsSolvable (M.map σ.toMonoidHom) := by
      intro σ
      apply Group.isSolvable_of_comm
      apply comm_of_mem
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← _root_.map_mul, ← _root_.map_mul, hab a ha b hb]
    have hS := isSolvable_biSup Finset.univ (fun σ : MulAut N => M.map σ.toMonoidHom)
      fun σ _ => hsol σ
    have e : (⨆ σ ∈ (Finset.univ : Finset (MulAut N)), M.map σ.toMonoidHom) = ⊤ := by
      rw [← hLt]
      exact iSup_congr fun σ => iSup_pos (Finset.mem_univ σ)
    rw [e] at hS
    have : Group.IsSolvable N :=
      Group.isSolvable_of_surjective (f := (topEquiv (G := N)).toMonoidHom) topEquiv.surjective
    have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial N
    rcases hc (commutator N) inferInstance with h | h
    · obtain ⟨a, b, hab'⟩ := hnc
      exact hab' (comm_of_commutator_eq_bot h a b)
    · exact hlt.ne h
  · push Not at hab
    obtain ⟨a, ha, b, hb, hab⟩ := hab
    by_cases hMt : M = ⊤
    · -- `N` is simple
      have : IsSimpleGroup N := ⟨fun K hK => by
        by_cases hKb : K = ⊥
        · exact Or.inl hKb
        · exact Or.inr (hMt ▸ hM.min K hK hKb (hMt ▸ le_top))⟩
      exact compA_eq_empty_of_isSimpleGroup ⟨a, b, hab⟩
    · -- induction on `M`, then the joins lemma
      have hcard : Nat.card M < n := by
        rw [← hn]
        exact (card_lt_of_lt (lt_top_iff_ne_top.mpr hMt)).trans_eq card_top
      have hMnt : Nontrivial M := (nontrivial_iff_ne_bot M).mpr hM.ne_bot
      have hM0 : compA M = ∅ := ih _ hcard M rfl hMnt hM.charSimple
        ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab (congrArg Subtype.val h)⟩
      have h := compA_subset_iUnion_of_iSup (fun σ : MulAut N => M.map σ.toMonoidHom) hLt
      apply Set.eq_empty_of_subset_empty
      refine h.trans (Set.iUnion_subset fun σ => ?_)
      rw [← compA_eq_of_mulEquiv (M.equivMapOfInjective σ.toMonoidHom σ.injective), hM0]

/-- **Characteristically simple groups:** a finite nontrivial noncommutative group whose only
characteristic subgroups are `⊥` and `⊤` has no abelian composition factors. -/
theorem compA_eq_empty_of_charSimple {N : Type*} [Group N] [Finite N] [Nontrivial N]
    (hc : CharSimple N) (hnc : ∃ a b : N, a * b ≠ b * a) : compA N = ∅ :=
  compA_eq_empty_of_charSimple_aux _ N rfl inferInstance hc hnc

end CharSimple

end GraphIso.Pyber
