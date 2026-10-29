module

public import GraphIso.Pyber.CompA

/-!
# Wielandt's residuals for the class `compA ⊆ S`

Stage 15a (`PLAN-15.md` §3, item 6). Wielandt's Lemma 4, as Pyber uses it, rests on the smallest
subnormal subgroup `H*` of `H` such that every composition factor between `H` and `H*` lies in a
given class. We take the class of groups `Q` with `compA Q ⊆ S`, for a set `S` of primes, and work
with subgroups of an ambient group `G`.

* **Chains** (`SChain S A L`): `A = A₀ ≥ A₁ ≥ … ≥ A_r = L`, each `A_{i+1}` normal in `A_i` with
  `compA (A_i ⧸ A_{i+1}) ⊆ S`. Such an `L` is subnormal in `A` (`SChain.isSubnormal`), and chains
  compose (`SChain.trans`).
* **Intersections** (`SChain.inf_left`): a chain from `A` to `L`, intersected with a subgroup `X`
  subnormal in `A`, is a chain from `X` to `X ⊓ L`: each section of the intersection is the
  quotient of a subnormal subgroup of a section of the chain. Hence chains from `A` are closed
  under `⊓` (`SChain.inf`).
* **The residual** (`resid S A`): the infimum of all `L` with `SChain S A L`, defined without
  choice. In a finite group it is reached (`schain_resid`).
* **Equivariance** (`resid_map`): `resid S (A.map e) = (resid S A).map e` for every isomorphism
  `e`; so every element normalizing `A` normalizes `resid S A` (`mem_normalizer_resid`).
* **One step does not change it** (`resid_eq_of_step`): if `B` is normal in `A` with
  `compA (A ⧸ B) ⊆ S`, then `resid S A = resid S B`.
* **Its use** (`compA_subset_of_schain`): `SChain S A L → compA A ⊆ S ∪ compA L`; in particular
  `resid S A = ⊥ → compA A ⊆ S` (`compA_subset_of_resid_eq_bot`).
-/

@[expose] public section

namespace GraphIso.Pyber

open Subgroup

variable {G G' : Type*} [Group G] [Group G']

/-- **Chains with sections in the class `compA ⊆ S`:** `A = A₀ ≥ A₁ ≥ … ≥ A_r = L`, each `A_{i+1}`
normal in `A_i` with `compA (A_i ⧸ A_{i+1}) ⊆ S`. -/
inductive SChain (S : Set ℕ) (A : Subgroup G) : Subgroup G → Prop
  | refl : SChain S A A
  | step {L L' : Subgroup G} [(L'.subgroupOf L).Normal] :
      SChain S A L → L' ≤ L → compA (L ⧸ L'.subgroupOf L) ⊆ S → SChain S A L'

namespace SChain

variable {S : Set ℕ} {A L : Subgroup G}

theorem le (h : SChain S A L) : L ≤ A := by
  induction h with
  | refl => exact le_rfl
  | step _ hle _ ih => exact hle.trans ih

/-- Chains compose. -/
theorem trans {L' : Subgroup G} (h : SChain S A L) (h' : SChain S L L') : SChain S A L' := by
  induction h' with
  | refl => exact h
  | step _ hle hS ih => exact step ih hle hS

/-- The end of a chain is subnormal in its start. -/
theorem isSubnormal (h : SChain S A L) : (L.subgroupOf A).IsSubnormal := by
  induction h with
  | refl => rw [subgroupOf_self]; exact IsSubnormal.top
  | @step L L' hN _ hle _ ih =>
    exact IsSubnormal.step _ _ (comap_mono hle) ih (normal_comap_pair A.subtype hle hN)

end SChain

/-- Intersecting a normal pair with any subgroup gives a normal pair. -/
theorem normal_inf_pair (X : Subgroup G) {L L' : Subgroup G} (hle : L' ≤ L)
    (hN : (L'.subgroupOf L).Normal) : ((X ⊓ L').subgroupOf (X ⊓ L)).Normal := by
  rw [normal_subgroupOf_iff_le_normalizer (inf_le_inf_left X hle), le_normalizer_iff]
  rw [normal_subgroupOf_iff_le_normalizer hle, le_normalizer_iff] at hN
  intro h hh k hk
  obtain ⟨hhX, hhL⟩ := mem_inf.mp hh
  obtain ⟨hkX, hkL⟩ := mem_inf.mp hk
  exact mem_inf.mpr ⟨X.mul_mem (X.mul_mem hhX hkX) (X.inv_mem hhX), hN h hhL k hkL⟩

/-- The section of an intersection maps into the section, with subnormal image. -/
theorem compA_inf_section_subset [Finite G] (X : Subgroup G) {A L L' : Subgroup G} (hLA : L ≤ A)
    (hX : (X.subgroupOf A).IsSubnormal) [hN : (L'.subgroupOf L).Normal]
    [(( X ⊓ L').subgroupOf (X ⊓ L)).Normal] :
    compA ((X ⊓ L : Subgroup G) ⧸ (X ⊓ L').subgroupOf (X ⊓ L)) ⊆
      compA (L ⧸ L'.subgroupOf L) := by
  set f : ↥(X ⊓ L) →* L ⧸ L'.subgroupOf L :=
    (QuotientGroup.mk' (L'.subgroupOf L)).comp (inclusion inf_le_right)
  refine compA_quot_subset_of_hom f _ ?_ ?_
  · ext ⟨y, hyX, hyL⟩
    simp only [f, MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, mem_subgroupOf, coe_inclusion, mem_inf]
    exact ⟨fun h => ⟨hyX, h⟩, fun h => h.2⟩
  · rw [MonoidHom.range_comp, inclusion_range, inf_subgroupOf_right]
    refine IsSubnormal.map (QuotientGroup.mk'_surjective _) ?_
    have h := hX.comap (inclusion hLA)
    rwa [show (X.subgroupOf A).comap (inclusion hLA) = X.subgroupOf L from by
      ext; simp [mem_subgroupOf]] at h

namespace SChain

variable {S : Set ℕ} {A L : Subgroup G}

/-- **Intersecting a chain with a subnormal subgroup:** from `A` to `L`, cut down by `X`, gives a
chain from `X` to `X ⊓ L`. -/
theorem inf_left [Finite G] (h : SChain S A L) {X : Subgroup G} (hXA : X ≤ A)
    (hX : (X.subgroupOf A).IsSubnormal) : SChain S X (X ⊓ L) := by
  induction h with
  | refl => rw [inf_of_le_left hXA]; exact refl
  | @step L L' hN hc hle hS ih =>
    have := normal_inf_pair X hle hN
    exact step ih (inf_le_inf_left X hle)
      ((compA_inf_section_subset X hc.le hX).trans hS)

/-- **Chains from `A` are closed under intersection.** -/
theorem inf [Finite G] {L₁ L₂ : Subgroup G} (h₁ : SChain S A L₁) (h₂ : SChain S A L₂) :
    SChain S A (L₁ ⊓ L₂) :=
  h₁.trans (h₂.inf_left h₁.le h₁.isSubnormal)

end SChain

/-- **Wielandt's residual** for the class `compA ⊆ S`: the infimum of the ends of all chains
from `A`. -/
def resid (S : Set ℕ) (A : Subgroup G) : Subgroup G :=
  sInf {L | SChain S A L}

theorem resid_le_of_schain {S : Set ℕ} {A L : Subgroup G} (h : SChain S A L) : resid S A ≤ L :=
  sInf_le h

/-- **The residual is reached** by a chain. -/
theorem schain_resid [Finite G] (S : Set ℕ) (A : Subgroup G) : SChain S A (resid S A) := by
  classical
  have hex : ∃ n, ∃ L : Subgroup G, SChain S A L ∧ Nat.card L = n := ⟨_, A, .refl, rfl⟩
  obtain ⟨L₀, h₀, hc₀⟩ := Nat.find_spec hex
  have hmin : ∀ L, SChain S A L → L₀ ≤ L := by
    intro L hL
    have hi := h₀.inf hL
    have heq : L₀ ⊓ L = L₀ := eq_of_le_of_card_ge inf_le_left
      (hc₀ ▸ Nat.find_min' hex ⟨_, hi, rfl⟩)
    exact heq ▸ inf_le_right
  have : resid S A = L₀ := le_antisymm (sInf_le h₀) (le_sInf hmin)
  rw [this]
  exact h₀

/-- Chains transport along isomorphisms. -/
theorem SChain.map [Finite G] {S : Set ℕ} {A L : Subgroup G} (e : G ≃* G') (h : SChain S A L) :
    SChain S (A.map e.toMonoidHom) (L.map e.toMonoidHom) := by
  induction h with
  | refl => exact .refl
  | @step L L' hN _ hle hS ih =>
    have := normal_map_pair e.toMonoidHom hle hN
    refine .step ih (map_mono hle) (Set.Subset.trans ?_ hS)
    have hmem : ∀ y : ↥(L.map e.toMonoidHom), e.symm y.1 ∈ L := fun y => mem_map_equiv.mp y.2
    set g : ↥(L.map e.toMonoidHom) →* L :=
      (e.symm.toMonoidHom.comp (L.map e.toMonoidHom).subtype).codRestrict L hmem
    set f : ↥(L.map e.toMonoidHom) →* L ⧸ L'.subgroupOf L :=
      (QuotientGroup.mk' (L'.subgroupOf L)).comp g
    refine compA_quot_subset_of_hom f _ ?_ ?_
    · ext y
      simp only [f, g, MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff, mem_subgroupOf]
      exact mem_map_equiv.symm
    · have hg : Function.Surjective g := fun x =>
        ⟨⟨e x, mem_map_of_mem e.toMonoidHom x.2⟩, Subtype.ext (e.symm_apply_apply x)⟩
      have hs : Function.Surjective f := (QuotientGroup.mk'_surjective _).comp hg
      rw [MonoidHom.range_eq_top.mpr hs]
      exact IsSubnormal.top

/-- **The residual is equivariant under isomorphisms.** -/
theorem resid_map [Finite G] [Finite G'] (S : Set ℕ) (A : Subgroup G) (e : G ≃* G') :
    resid S (A.map e.toMonoidHom) = (resid S A).map e.toMonoidHom := by
  apply le_antisymm (resid_le_of_schain ((schain_resid S A).map e))
  have h := (schain_resid S (A.map e.toMonoidHom)).map e.symm
  have hA : (A.map e.toMonoidHom).map e.symm.toMonoidHom = A := by
    rw [map_map]
    convert map_id A
    ext x
    simp
  rw [hA] at h
  have h2 := map_mono (f := e.toMonoidHom) (resid_le_of_schain h)
  rwa [map_map, show e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id G' from by
    ext x; simp, map_id] at h2

/-- **Anything normalizing `A` normalizes its residual.** -/
theorem mem_normalizer_resid [Finite G] (S : Set ℕ) {A : Subgroup G} {g : G}
    (hg : g ∈ normalizer (A : Set G)) : g ∈ normalizer (resid S A : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq] at hg ⊢
  have h := resid_map S A (MulAut.conj g)
  rw [show (MulAut.conj g).toMonoidHom = (MulAut.conj g : G →* G) from rfl, hg] at h
  exact h.symm

/-- **One step does not change the residual:** if `B` is normal in `A` and
`compA (A ⧸ B) ⊆ S`, then `resid S A = resid S B`. -/
theorem resid_eq_of_step [Finite G] {S : Set ℕ} {A B : Subgroup G} (hBA : B ≤ A)
    [hN : (B.subgroupOf A).Normal] (hS : compA (A ⧸ B.subgroupOf A) ⊆ S) :
    resid S A = resid S B := by
  apply le_antisymm
  · exact resid_le_of_schain ((SChain.step .refl hBA hS).trans (schain_resid S B))
  · have h := (schain_resid S A).inf_left hBA (Normal.isSubnormal hN)
    exact (resid_le_of_schain h).trans inf_le_right

/-- **The use of a chain:** `compA A ⊆ S ∪ compA L`. -/
theorem compA_subset_of_schain [Finite G] {S : Set ℕ} {A L : Subgroup G} (h : SChain S A L) :
    compA A ⊆ S ∪ compA L := by
  induction h with
  | refl => exact Set.subset_union_right
  | @step L L' hN _ hle hS ih =>
    refine ih.trans (Set.union_subset Set.subset_union_left ?_)
    refine (compA_subset_union (L'.subgroupOf L)).trans (Set.union_subset ?_ ?_)
    · rw [compA_eq_of_mulEquiv (subgroupOfEquivOfLe hle)]
      exact Set.subset_union_right
    · exact hS.trans Set.subset_union_left

/-- **A trivial residual:** `resid S A = ⊥ → compA A ⊆ S`. -/
theorem compA_subset_of_resid_eq_bot [Finite G] {S : Set ℕ} {A : Subgroup G}
    (h : resid S A = ⊥) : compA A ⊆ S := by
  have h' := compA_subset_of_schain (schain_resid S A)
  rw [h] at h'
  rwa [compA_eq_empty_of_subsingleton (G := ↥(⊥ : Subgroup G)), Set.union_empty] at h'

end GraphIso.Pyber
