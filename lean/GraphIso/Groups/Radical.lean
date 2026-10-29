module

public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Data.SetLike.Fintype
public import GraphIso.Groups.MinimalNormal
public import Mathlib.Data.Set.Finite.Lemmas

/-!
# The solvable radical

For a finite group `G`:

* `isSolvable_sup`: the join of a solvable subgroup and a solvable normal subgroup is solvable.
* `exists_radical`: the solvable radical, a solvable normal subgroup containing every solvable
  normal subgroup.
* `eq_bot_of_abelian_normal_quotient`: the quotient by the radical has no nontrivial abelian
  normal subgroup (its preimage would be solvable and normal).
* `eq_bot_of_normal_isPGroup_of_normal`: if `G` has no nontrivial normal `p`-subgroup, neither
  has any normal subgroup `R`: a largest `p`-subgroup of `R` normalized by `R` is normalized by
  `G`.
-/

@[expose] public section

namespace GraphIso.Groups

variable {G : Type*} [Group G]

/-- **The join of solvable subgroups, one of them normal, is solvable.** -/
theorem isSolvable_sup (S T : Subgroup G) [hT : T.Normal] [Group.IsSolvable S]
    [Group.IsSolvable T] : Group.IsSolvable (S ⊔ T : Subgroup G) := by
  let U : Subgroup G := S ⊔ T
  let TU : Subgroup U := T.subgroupOf U
  have : TU.Normal := Subgroup.normal_subgroupOf
  let f : T →* U := Subgroup.inclusion le_sup_right
  let g : U →* U ⧸ TU := QuotientGroup.mk' TU
  have hg : g.ker ≤ f.range := by
    intro x hx
    rw [QuotientGroup.ker_mk'] at hx
    exact ⟨⟨x, hx⟩, rfl⟩
  have : Group.IsSolvable (U ⧸ TU) := by
    let h : S →* U ⧸ TU := g.comp (Subgroup.inclusion le_sup_left)
    refine Group.isSolvable_of_surjective (f := h) fun z => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective TU z
    obtain ⟨y, hy, t, ht, hyt⟩ := Subgroup.mem_sup_of_normal_right.1 x.2
    refine ⟨⟨y, hy⟩, ?_⟩
    change g (Subgroup.inclusion le_sup_left ⟨y, hy⟩) = g x
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    change ((Subgroup.inclusion le_sup_left ⟨y, hy⟩ : U)⁻¹ * x : G) ∈ T
    simp only [Subgroup.coe_inv, Subgroup.coe_inclusion]
    rw [← hyt, inv_mul_cancel_left]
    exact ht
  exact Group.isSolvable_of_ker_le_range f g hg

/-- **The solvable radical.** -/
theorem exists_radical (G : Type*) [Group G] [Finite G] :
    ∃ R : Subgroup G, R.Normal ∧ Group.IsSolvable R ∧
      ∀ S : Subgroup G, S.Normal → Group.IsSolvable S → S ≤ R := by
  classical
  have := Fintype.ofFinite G
  let 𝒮 : Set (Subgroup G) := {S | S.Normal ∧ Group.IsSolvable S}
  have hne : 𝒮.Nonempty := ⟨⊥, inferInstance, inferInstance⟩
  obtain ⟨R, ⟨hR, hRs⟩, hmax⟩ := 𝒮.exists_max_image (fun S => Nat.card S) 𝒮.toFinite hne
  refine ⟨R, hR, hRs, fun S hS hSs => ?_⟩
  have : Group.IsSolvable (S ⊔ R : Subgroup G) := isSolvable_sup S R
  have hle := hmax (S ⊔ R) ⟨inferInstance, this⟩
  have heq : R = S ⊔ R := Subgroup.eq_of_le_of_card_ge le_sup_right hle
  exact heq ▸ le_sup_left

/-- **The quotient by the radical has no nontrivial abelian normal subgroup.** -/
theorem eq_bot_of_abelian_normal_quotient [Finite G] {R : Subgroup G} [R.Normal]
    [Group.IsSolvable R] (hR : ∀ S : Subgroup G, S.Normal → Group.IsSolvable S → S ≤ R)
    (A : Subgroup (G ⧸ R)) (hA : A.Normal) (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) :
    A = ⊥ := by
  let A' : Subgroup G := A.comap (QuotientGroup.mk' R)
  have hA'n : A'.Normal := hA.comap _
  have : Group.IsSolvable A := Group.isSolvable_of_comm fun a b => Subtype.ext (hAc a a.2 b b.2)
  have hRA : R ≤ A' := fun x hx => by
    change (QuotientGroup.mk' R x) ∈ A
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).2 hx]
    exact A.one_mem
  have : Group.IsSolvable A' := by
    let f : R →* A' := Subgroup.inclusion hRA
    let g : A' →* A := (QuotientGroup.mk' R).subgroupComap A
    refine Group.isSolvable_of_ker_le_range f g fun x hx => ?_
    have h1 : QuotientGroup.mk' R (x : G) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
    exact ⟨⟨x, (QuotientGroup.eq_one_iff _).1 h1⟩, rfl⟩
  have hle := hR A' hA'n this
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  exact (QuotientGroup.eq_one_iff g).2 (hle hx)

/-- **Normal subgroups inherit the absence of normal `p`-subgroups.** -/
theorem eq_bot_of_normal_isPGroup_of_normal [Finite G] {p : ℕ} [Fact p.Prime]
    (hp : ∀ Q : Subgroup G, Q.Normal → IsPGroup p Q → Q = ⊥) (R : Subgroup G) [hR : R.Normal]
    (Q : Subgroup R) (hQ : Q.Normal) (hQp : IsPGroup p Q) : Q = ⊥ := by
  classical
  have := Fintype.ofFinite G
  let 𝒮 : Set (Subgroup G) := {P | NNormal R P ∧ IsPGroup p P}
  have hne : 𝒮.Nonempty := ⟨⊥, ⟨bot_le, fun _ _ t ht => by
    rw [Subgroup.mem_bot] at ht ⊢
    simp [ht]⟩, IsPGroup.of_bot⟩
  obtain ⟨O, ⟨hO, hOp⟩, hmax⟩ := 𝒮.exists_max_image (fun S => Nat.card S) 𝒮.toFinite hne
  -- `O` contains every member of `𝒮`
  have hall : ∀ P ∈ 𝒮, P ≤ O := by
    rintro P ⟨hP, hPp⟩
    have hPO : P ≤ Subgroup.normalizer (O : Set G) := fun x hx => by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      refine ⟨fun hy => hO.2 x (hP.1 hx) y hy, fun hy => ?_⟩
      have := hO.2 x⁻¹ (R.inv_mem (hP.1 hx)) _ hy
      simpa [mul_assoc] using this
    have hsup : P ⊔ O ∈ 𝒮 := by
      refine ⟨⟨sup_le hP.1 hO.1, fun r hr t ht => ?_⟩, hPp.to_sup_of_normal_right' hOp hPO⟩
      have h1 : P ⊔ O ≤ cj r⁻¹ (P ⊔ O) := sup_le
        (fun y hy => mem_cj.2 (by simpa using Subgroup.mem_sup_left (hP.2 r hr y hy)))
        (fun y hy => mem_cj.2 (by simpa using Subgroup.mem_sup_right (hO.2 r hr y hy)))
      simpa using mem_cj.1 (h1 ht)
    have heq : O = P ⊔ O := Subgroup.eq_of_le_of_card_ge le_sup_right (hmax _ hsup)
    exact heq ▸ le_sup_left
  -- so `O` is normal in `G`, hence trivial
  have hRn : NNormal ⊤ R := nnormal_top_iff.2 hR
  have hOn : O.Normal := by
    refine ⟨fun x hx g => ?_⟩
    have hmem : cj g O ∈ 𝒮 := ⟨hRn.cj hO (Subgroup.mem_top g), hOp.map _⟩
    exact hall _ hmem (mem_cj.2 (by simpa [mul_assoc] using hx))
  have hOb := hp O hOn hOp
  -- and `Q` lies in it
  have hQ𝒮 : Q.map R.subtype ∈ 𝒮 := by
    refine ⟨⟨Subgroup.map_subtype_le Q, fun r hr t ht => ?_⟩, hQp.map _⟩
    obtain ⟨q, hq, rfl⟩ := ht
    exact ⟨⟨r, hr⟩ * q * ⟨r, hr⟩⁻¹, hQ.conj_mem q hq ⟨r, hr⟩, rfl⟩
  have hle := hall _ hQ𝒮
  rw [hOb, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ R.subtype_injective] at hle
  exact hle

end GraphIso.Groups
