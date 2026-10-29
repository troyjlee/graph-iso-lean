module

public import GraphIso.Luks.Strategy
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.Index
public import Mathlib.Data.Nat.Factorial.Basic

/-!
# Bounded primitive sections

* `card_eq_of_isPreprimitive_of_isNilpotent`: a primitive nilpotent permutation group of degree
  `k ≥ 2` has order `k`. Its point stabilizer is a maximal subgroup
  (`isCoatom_stabilizer_iff_preprimitive`), hence normal (`NormalizerCondition.normal_of_coatom`),
  hence contained in every point stabilizer of the transitive action, hence trivial; so the
  order is the index of the stabilizer, the degree.
* `primBounded_of_isNilpotent`: nilpotent groups (in particular `p`-groups) have
  `PrimBounded G₀ 1`, since subgroups and homomorphic images of nilpotent groups are
  nilpotent.
* `primBounded_degree`: every subgroup of `Sym(n)` has `PrimBounded G₀ n`, since a section of
  degree `k` has order at most `min (k!, n!) ≤ k ^ n`. This gives a cost bound, exponential in
  the degree, for every group.
-/

@[expose] public section

namespace GraphIso.Luks

open Equiv MulAction

/-- **A primitive nilpotent permutation group has order equal to its degree.** -/
theorem card_eq_of_isPreprimitive_of_isNilpotent {k : ℕ} (P : Subgroup (Perm (Fin k)))
    [Group.IsNilpotent P] (hk : 2 ≤ k) [hP : IsPreprimitive P (Fin k)] : Nat.card P = k := by
  have : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.2 hk
  set a : Fin k := ⟨0, by omega⟩
  have hcoatom : IsCoatom (stabilizer P a) := (isCoatom_stabilizer_iff_preprimitive P a).2 hP
  have hnormal : (stabilizer P a).Normal :=
    Subgroup.NormalizerCondition.normal_of_coatom _
      (Group.normalizerCondition_of_isNilpotent (G := P)) hcoatom
  -- the stabilizer is trivial: it fixes every point
  have hbot : stabilizer P a = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    have hfix : ∀ b : Fin k, g • b = b := by
      intro b
      obtain ⟨h, rfl⟩ := exists_smul_eq P a b
      have hc : h⁻¹ * g * h ∈ stabilizer P a := by
        have := hnormal.conj_mem g hg h⁻¹
        simpa using this
      rw [mem_stabilizer_iff] at hc
      calc g • h • a = h • (h⁻¹ * g * h) • a := by
            rw [← mul_smul, ← mul_smul]; group
        _ = h • a := by rw [hc]
    apply Subtype.ext
    ext b
    exact congrArg Fin.val (hfix b)
  have := index_stabilizer_of_transitive P a
  rw [hbot, Subgroup.index_bot, Nat.card_eq_fintype_card (α := Fin k), Fintype.card_fin] at this
  exact this

/-- A subgroup of a nilpotent subgroup is nilpotent. -/
theorem isNilpotent_of_le {n : ℕ} {G₀ H : Subgroup (Perm (Fin n))} (hG : Group.IsNilpotent G₀)
    (hH : H ≤ G₀) : Group.IsNilpotent H :=
  Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hH)

/-- **Nilpotent groups have primitive sections of order at most their degree.** -/
theorem primBounded_of_isNilpotent {n : ℕ} {G₀ : Subgroup (Perm (Fin n))}
    (hG : Group.IsNilpotent G₀) : PrimBounded G₀ 1 := by
  intro H hH k φ hk hprim
  have : Group.IsNilpotent H := isNilpotent_of_le hG hH
  have : Group.IsNilpotent φ.range :=
    Group.nilpotent_of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  rw [pow_one, card_eq_of_isPreprimitive_of_isNilpotent φ.range hk]

/-- **Every group has primitive sections of order at most `k ^ n`.** -/
theorem primBounded_degree {n : ℕ} (G₀ : Subgroup (Perm (Fin n))) : PrimBounded G₀ n := by
  intro H _ k φ hk _
  have hk1 : 1 ≤ k := by omega
  rcases le_total k n with hkn | hnk
  · -- at most `k! ≤ k ^ k ≤ k ^ n`
    have h₁ : Nat.card φ.range ≤ Nat.card (Perm (Fin k)) :=
      Nat.card_le_card_of_injective (Subtype.val) Subtype.val_injective
    rw [Nat.card_eq_fintype_card (α := Perm (Fin k)), Fintype.card_perm, Fintype.card_fin] at h₁
    exact h₁.trans ((Nat.factorial_le_pow k).trans (Nat.pow_le_pow_right hk1 hkn))
  · -- at most `n! ≤ n ^ n ≤ k ^ n`
    have h₁ : Nat.card φ.range ≤ Nat.card H :=
      Nat.card_le_card_of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
    have h₂ : Nat.card H ≤ Nat.card (Perm (Fin n)) :=
      Nat.card_le_card_of_injective (Subtype.val) Subtype.val_injective
    rw [Nat.card_eq_fintype_card (α := Perm (Fin n)), Fintype.card_perm, Fintype.card_fin] at h₂
    exact h₁.trans (h₂.trans ((Nat.factorial_le_pow n).trans (Nat.pow_le_pow_left hnk n)))

end GraphIso.Luks
