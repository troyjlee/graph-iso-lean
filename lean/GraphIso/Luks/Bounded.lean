module

public import GraphIso.Luks.Strategy
public import GraphIso.Groups.PrimitiveBounded

/-!
# Bounded primitive sections of groups with bounded simple sections

* `primBounded_of_boundedSections`: a group all of whose simple sections have order at most `k`
  has `PrimBounded G₀ (3 k³ + 3 k² + 12 k + 1)`. Subgroups and homomorphic images have the same
  property (`BoundedSections.of_injective`, `BoundedSections.of_surjective`), and a primitive
  group of degree `m ≥ 2` with that property has order at most `m^{3 k³ + 3 k² + 12 k + 1}`
  (`Groups.card_le_of_isPreprimitive_of_boundedSections`).
-/

@[expose] public section

namespace GraphIso.Luks

open Equiv

/-- **Groups with simple sections of order at most `k` have primitive sections of order at most
`m ^ (3 k³ + 3 k² + 12 k + 1)`.** -/
theorem primBounded_of_boundedSections {n k : ℕ} {G₀ : Subgroup (Perm (Fin n))}
    (hG : Groups.BoundedSections k G₀) :
    PrimBounded G₀ (3 * k ^ 3 + 3 * k ^ 2 + 12 * k + 1) := by
  intro H hH m φ hm hprim
  have hH' : Groups.BoundedSections k H :=
    hG.of_injective (Subgroup.inclusion hH) (Subgroup.inclusion_injective hH)
  have hR : Groups.BoundedSections k φ.range :=
    hH'.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  exact Groups.card_le_of_isPreprimitive_of_boundedSections φ.range hR hm

end GraphIso.Luks
