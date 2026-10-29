module

public import GraphIso.Pyber.Families
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.GroupAction.Primitive

/-!
# Core-free subgroups and faithful transitive actions

Stage 15b (`PLAN-15.md` §4, items 1–2). A point stabilizer of a transitive group of degree `n`
is, abstractly, a subgroup `H ≤ G` of index `n` with `H.normalCore = ⊥` (a *core-free*
subgroup). This file proves the bridges between the two forms, and the reductions through an
intermediate subgroup that the inductions of stages 15b and 15c use.

* **Faithful actions** (`Faithful G Ω`): only `1` fixes every point.
* **Concrete to abstract** (`normalCore_stabilizer_eq_bot`): a point stabilizer of a faithful
  transitive action is core-free; its index is `|Ω|` (mathlib's
  `MulAction.index_stabilizer_of_transitive`). A subgroup of `Perm Ω` acts faithfully
  (`faithful_perm`), and the image of a transitive action in `Perm Ω` acts transitively
  (`isPretransitive_range`).
* **Abstract to concrete** (`faithful_quotient`, `nontrivial_quotient`,
  `isPreprimitive_quotient`): for `H` core-free, `G` acts faithfully and transitively on
  `G ⧸ H`, where the stabilizer of the base coset is `H` (mathlib's
  `MulAction.stabilizer_quotient`). `G ⧸ H` has two points when `H ≠ ⊤`, and the action is
  primitive when `H` is maximal.
* **The quotient by the core** (`normalCore_map_mk`, `index_map_mk`): for every subgroup `L`,
  the image of `L` in `G ⧸ L.normalCore` is core-free of index `[G : L]`.
* **Normal subgroups below a core-free subgroup's overgroup.** Let `H` be core-free and `K`
  normal, and `J` the core of `H ∩ K` in `K`:
  - every prime dividing `|K|` divides `|K ⧸ J|` (`primeFactors_card_subset`), and
    `compA K ⊆ compA (K ⧸ J)` (`compA_subset_compA_quot`), because the conjugates of `J`
    intersect trivially;
  - if `M` covers `H`, `K ≤ M` and `K ≠ ⊥`, then `K ⊔ H = M` (`sup_eq_of_covBy`), and then
    `[K : H ∩ K] = [M : H]` (`relIndex_eq_of_sup_eq`).
* **A covering subgroup** (`exists_covBy_ne_top`): if `H` is neither `⊤` nor maximal, some `M`
  covers `H` and is not `⊤`.
-/

@[expose] public section

namespace GraphIso.Pyber

open Subgroup MulAction

/-- Membership in the normal core: every conjugate lies in `H`. -/
theorem mem_normalCore_iff {G : Type*} [Group G] {H : Subgroup G} {g : G} :
    g ∈ H.normalCore ↔ ∀ b : G, b * g * b⁻¹ ∈ H :=
  Iff.rfl

section Faithful

variable {G Ω : Type*} [Group G] [MulAction G Ω]

/-- **A faithful action:** only `1` fixes every point. -/
def Faithful (G Ω : Type*) [Group G] [MulAction G Ω] : Prop :=
  ∀ g : G, (∀ a : Ω, g • a = a) → g = 1

/-- **Concrete to abstract:** a point stabilizer of a faithful transitive action is core-free. -/
theorem normalCore_stabilizer_eq_bot [IsPretransitive G Ω] (hf : Faithful G Ω) (x : Ω) :
    (stabilizer G x).normalCore = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [mem_bot]
  apply hf
  intro a
  obtain ⟨h, rfl⟩ := exists_smul_eq G x a
  have h1 := mem_normalCore_iff.mp hg h⁻¹
  rw [mem_stabilizer_iff, mul_smul, mul_smul, inv_inv, inv_smul_eq_iff] at h1
  exact h1

/-- A subgroup of `Perm Ω` acts faithfully on `Ω`. -/
theorem faithful_perm (P : Subgroup (Equiv.Perm Ω)) : Faithful P Ω :=
  fun _ h => Subtype.ext (Equiv.ext h)

/-- The image of a transitive action in `Perm Ω` acts transitively. -/
theorem isPretransitive_range [IsPretransitive G Ω] :
    IsPretransitive (toPermHom G Ω).range Ω :=
  ⟨fun a b => by
    obtain ⟨g, hg⟩ := exists_smul_eq G a b
    exact ⟨⟨toPermHom G Ω g, MonoidHom.mem_range.mpr ⟨g, rfl⟩⟩, hg⟩⟩

end Faithful

section Quotient

variable {G : Type*} [Group G]

/-- **Abstract to concrete:** `G` acts faithfully on `G ⧸ H` when `H` is core-free. -/
theorem faithful_quotient {H : Subgroup G} (hc : H.normalCore = ⊥) : Faithful G (G ⧸ H) := by
  intro g hg
  have hk : g ∈ (MulAction.toPermHom G (G ⧸ H)).ker := by
    rw [MonoidHom.mem_ker]
    exact Equiv.Perm.ext hg
  rw [← normalCore_eq_ker, hc, mem_bot] at hk
  exact hk

/-- A nontrivial quotient: `G ⧸ H` has two points when `H ≠ ⊤`. -/
theorem nontrivial_quotient {H : Subgroup G} (hH : H ≠ ⊤) :
    Nontrivial (G ⧸ H) := by
  obtain ⟨g, hg⟩ : ∃ g, g ∉ H := by
    by_contra hall
    push Not at hall
    exact hH (eq_top_iff.mpr fun x _ => hall x)
  exact ⟨⟨(g : G ⧸ H), ((1 : G) : G ⧸ H), by rwa [Ne, QuotientGroup.eq, mul_one, inv_mem_iff]⟩⟩

/-- **Primitivity from maximality:** the action on `G ⧸ H` is primitive when `H` is maximal. -/
theorem isPreprimitive_quotient {H : Subgroup G} (hH : IsCoatom H) :
    IsPreprimitive G (G ⧸ H) := by
  have := nontrivial_quotient hH.1
  rw [← isCoatom_stabilizer_iff_preprimitive G ((1 : G) : G ⧸ H), stabilizer_quotient]
  exact hH

end Quotient

section Core

variable {G : Type*} [Group G]

/-- **The quotient by the core:** the image of `L` in `G ⧸ L.normalCore` is core-free. -/
theorem normalCore_map_mk (L : Subgroup G) :
    (L.map (QuotientGroup.mk' L.normalCore)).normalCore = ⊥ := by
  rw [eq_bot_iff]
  intro c hc
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective L.normalCore c
  rw [mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_normalCore_iff]
  intro h
  obtain ⟨l, hl, he⟩ := mem_map.mp (mem_normalCore_iff.mp hc (QuotientGroup.mk' L.normalCore h))
  rw [← map_inv, ← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq] at he
  have h1 := mul_mem hl (L.normalCore_le he)
  rwa [← mul_assoc, mul_inv_cancel, one_mul] at h1

/-- The image of `L` in `G ⧸ L.normalCore` has the index of `L`. -/
theorem index_map_mk (L : Subgroup G) :
    (L.map (QuotientGroup.mk' L.normalCore)).index = L.index :=
  index_map_eq _ (QuotientGroup.mk'_surjective _) (by
    rw [QuotientGroup.ker_mk']
    exact L.normalCore_le)

/-- **The primes of a normal subgroup.** For `H` core-free and `K` normal, every prime dividing
`|K|` divides `|K ⧸ J|`, where `J` is the core of `H ∩ K` in `K`: an element of prime order in
`K` has a conjugate outside `H`. -/
theorem primeFactors_card_subset [Finite G] {H K : Subgroup G} [K.Normal]
    (hc : H.normalCore = ⊥) :
    (Nat.card K).primeFactors ⊆ (Nat.card (K ⧸ (H.subgroupOf K).normalCore)).primeFactors := by
  intro p hp
  rw [Nat.mem_primeFactors] at hp ⊢
  obtain ⟨hpp, hd, -⟩ := hp
  have := Fact.mk hpp
  obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' p hd
  have hk1 : (k : G) ∉ H.normalCore := by
    rw [hc, mem_bot]
    intro h
    rw [show k = 1 from Subtype.ext h, orderOf_one] at hk
    exact hpp.one_lt.ne hk
  obtain ⟨g, hg⟩ : ∃ g : G, g * k * g⁻¹ ∉ H := by
    by_contra hall
    push Not at hall
    exact hk1 (mem_normalCore_iff.mpr hall)
  set k' := MulAut.conjNormal g k
  have hk' : orderOf k' = p := by
    rw [← hk]
    exact orderOf_injective (MulAut.conjNormal g).toMonoidHom (MulAut.conjNormal g).injective k
  set q := QuotientGroup.mk' (H.subgroupOf K).normalCore
  have hq : orderOf (q k') = p := by
    rcases hpp.eq_one_or_self_of_dvd _ (hk' ▸ orderOf_map_dvd q k') with h1 | h1
    · rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact absurd (mem_subgroupOf.mp ((H.subgroupOf K).normalCore_le h1)) hg
    · exact h1
  exact ⟨hpp, hq ▸ orderOf_dvd_natCard (q k'), Nat.card_pos.ne'⟩

/-- **`compA` of a normal subgroup.** For `H` core-free and `K` normal,
`compA K ⊆ compA (K ⧸ J)`, where `J` is the core of `H ∩ K` in `K`: the conjugates of `J` under
`G` intersect trivially, and each quotient is isomorphic to `K ⧸ J` (15a, item 4). -/
theorem compA_subset_compA_quot [Finite G] {H K : Subgroup G} [K.Normal]
    (hc : H.normalCore = ⊥) : compA K ⊆ compA (K ⧸ (H.subgroupOf K).normalCore) := by
  set J := (H.subgroupOf K).normalCore
  set N : G → Subgroup K := fun g => J.map (MulAut.conjNormal g).toMonoidHom
  have hN : ∀ g, (N g).Normal := fun g =>
    Normal.map inferInstance _ (MulAut.conjNormal g).surjective
  have hi : ⨅ g, N g = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [mem_bot]
    have hx' : (x : G) ∈ H.normalCore := by
      rw [mem_normalCore_iff]
      intro g
      have h1 := mem_iInf.mp hx g⁻¹
      rw [mem_map_equiv] at h1
      have h2 := mem_subgroupOf.mp ((H.subgroupOf K).normalCore_le h1)
      rwa [MulAut.conjNormal_symm_apply, inv_inv] at h2
    rw [hc, mem_bot] at hx'
    exact Subtype.ext hx'
  refine (compA_subset_iUnion_of_iInf N hi).trans (Set.iUnion_subset fun g => ?_)
  rw [compA_eq_of_mulEquiv (QuotientGroup.congr J (N g) (MulAut.conjNormal g) rfl).symm]

/-- **The join with the core.** If `M` covers `H`, `H` is core-free, and `K ≤ M` is normal and
nontrivial, then `K ⊔ H = M`. -/
theorem sup_eq_of_covBy {H M K : Subgroup G} [K.Normal] (hcov : H ⋖ M) (hKM : K ≤ M)
    (hc : H.normalCore = ⊥) (hK : K ≠ ⊥) : K ⊔ H = M := by
  rcases hcov.eq_or_eq le_sup_right (sup_le hKM hcov.le) with h | h
  · refine absurd ?_ hK
    rw [eq_bot_iff, ← hc, normal_le_normalCore]
    exact h ▸ le_sup_left
  · exact h

/-- `[K : H ∩ K] = [K ⊔ H : H]` for `K` normal; so `[K : H ∩ K] = [M : H]` when `K ⊔ H = M`. -/
theorem relIndex_eq_of_sup_eq [Finite G] {H M K : Subgroup G} [K.Normal] (h : K ⊔ H = M) :
    H.relIndex K = H.relIndex M := by
  rw [← h, relIndex_eq_mul_relIndex (N := K) le_sup_right,
    inf_of_le_right (le_sup_left : K ≤ K ⊔ H), sup_comm K H, sup_assoc, sup_idem, relIndex_self,
    mul_one, inf_relIndex_right]

/-- **A covering subgroup:** if `H` is neither `⊤` nor maximal, some `M ≠ ⊤` covers `H`. -/
theorem exists_covBy_ne_top [Finite G] {H : Subgroup G} (htop : H ≠ ⊤) (hmax : ¬IsCoatom H) :
    ∃ M : Subgroup G, H ⋖ M ∧ M ≠ ⊤ := by
  classical
  have hex : ∃ n, ∃ M : Subgroup G, H < M ∧ M ≠ ⊤ ∧ Nat.card M = n := by
    obtain ⟨M, hHM, hM⟩ : ∃ M, H < M ∧ M ≠ ⊤ := by
      by_contra hall
      push Not at hall
      exact hmax ⟨htop, hall⟩
    exact ⟨_, M, hHM, hM, rfl⟩
  obtain ⟨M, hHM, hM, hcard⟩ := Nat.find_spec hex
  refine ⟨M, ⟨hHM, fun c hHc hcM => ?_⟩, hM⟩
  have hlt := card_lt_of_lt hcM
  rw [hcard] at hlt
  exact Nat.find_min hex hlt ⟨c, hHc, ne_top_of_lt hcM, rfl⟩

end Core

end GraphIso.Pyber
