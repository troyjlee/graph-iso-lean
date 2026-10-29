module

public import GraphIso.Luks.Strategy
public import GraphIso.Groups.PrimitiveSolvable

/-!
# Bounded primitive sections of solvable groups

* `primBounded_of_isSolvable`: a solvable group whose order has at most `s + 1` prime divisors
  has `PrimBounded G₀ (12 s + 1)`. Subgroups and homomorphic images are solvable, with prime
  divisors among those of `|G₀|`, and a primitive solvable group of degree `k` has order at
  most `k^{12 s + 1}` when its order has at most `s + 1` prime divisors
  (`Groups.card_le_of_isPreprimitive_of_isSolvable`). For `s = 0`, the `p`-groups, this is
  the exponent of `primBounded_of_isNilpotent`.
-/

@[expose] public section

namespace GraphIso.Luks

open Equiv

/-- **Solvable groups with at most `s + 1` prime divisors have primitive sections of order at
most `k ^ (12 s + 1)`.** -/
theorem primBounded_of_isSolvable {n s : ℕ} {G₀ : Subgroup (Perm (Fin n))}
    (hG : Group.IsSolvable G₀) (hs : (Nat.card G₀).primeFactors.card ≤ s + 1) :
    PrimBounded G₀ (12 * s + 1) := by
  intro H hH k φ hk hprim
  have : Group.IsSolvable H :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hH)
      (Subgroup.inclusion_injective hH)
  have : Group.IsSolvable φ.range :=
    Group.isSolvable_of_surjective (f := φ.rangeRestrict) φ.rangeRestrict_surjective
  have hdvd : Nat.card φ.range ∣ Nat.card G₀ :=
    (Subgroup.card_range_dvd φ).trans (Subgroup.card_dvd_of_le hH)
  have hsub : (Nat.card φ.range).primeFactors ⊆ (Nat.card G₀).primeFactors :=
    Nat.primeFactors_mono hdvd Nat.card_pos.ne'
  have hcard := Groups.card_le_of_isPreprimitive_of_isSolvable φ.range hk
  exact hcard.trans (Nat.pow_le_pow_right (by omega)
    (by have := Finset.card_le_card hsub; omega))

end GraphIso.Luks
