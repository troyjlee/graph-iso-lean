module

public import GraphIso.Valence.Step
public import GraphIso.Luks.Bounded
public import Mathlib.Data.Finite.Perm

/-!
# Layer groups of graphs of every bounded valence

For a layered graph of maximum degree `Δ` rooted at two edges (`LayeredD Δ`, `Roots4`), and
every `k ≥ 2` with `(Δ − 1)! ≤ k`, **every layer group `A_r` has simple sections of order at
most `k`** (`boundedSections_autR`). This is proved from the construction:

* `A₀` is a `2`-group (`autR0_pow_four`), and a simple section of a `p`-group has order `p`
  (`Groups.boundedSections_of_isPGroup`);
* the kernel of the restriction `A_{r+1} → A_r` embeds in the product over the points of the
  permutation groups of their twins (`twinHom`), each of at most `Δ − 1` points
  (`card_tw_le_pred`), so of order at most `(Δ − 1)!` (`boundedSections_ker`);
* bounded sections pass to subgroups, finite products and extensions (`Groups/Sections.lean`).

So milestone 8's `primBounded_of_boundedSections` gives `LayerPrim Δ (3 k³ + 3 k² + 12 k + 1)`
(`layerPrim_bounded`): every string-isomorphism call of a layer step is polynomial, for every
`Δ`. For `Δ ≥ 6` the layer groups need not be solvable: a twin class of five points gives a
factor `S₅`.
-/

@[expose] public section

namespace GraphIso.Graph.Valence

open Equiv Groups Luks

section Layers

variable {Δ N : ℕ} {G : GraphData} {roots : List ℕ} {lev : Array ℕ} {a b c d k : ℕ}
  (hZ : LayeredD Δ N G roots lev)

include hZ in
/-- **The kernel of the restriction has simple sections of order at most `(Δ − 1)!`.** -/
theorem boundedSections_ker (hk : (Δ - 1).factorial ≤ k) (r : ℕ) :
    BoundedSections k (resHom hZ r).ker := by
  classical
  refine BoundedSections.of_injective ?_ (twinHom G lev hZ r) (twinHom_injective hZ r)
  refine BoundedSections.pi fun x => (boundedSections_card (G := Perm _)).mono ?_
  rw [Nat.card_perm, Nat.card_eq_fintype_card]
  exact (Nat.factorial_le (card_tw_le_pred hZ x)).trans hk

variable (hR : Roots4 N G lev a b c d)
include hZ hR

/-- **Every layer group has simple sections of order at most `k`**, for every `k ≥ 2` with
`(Δ − 1)! ≤ k`. -/
theorem boundedSections_autR (hk2 : 2 ≤ k) (hk : (Δ - 1).factorial ≤ k) :
    ∀ r, BoundedSections k (AutR N G lev r)
  | 0 => by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h2 : IsPGroup 2 (AutR N G lev 0) := fun x =>
      ⟨2, Subtype.ext (by rw [Subgroup.coe_pow]; exact autR0_pow_four hR hZ.valid x.2)⟩
    exact (boundedSections_of_isPGroup h2).mono hk2
  | r + 1 => BoundedSections.of_ker (resHom hZ r) (boundedSections_ker hZ hk r)
      (boundedSections_autR hk2 hk r)

end Layers

/-- **Every bounded valence**: for every `k ≥ 2` with `(Δ − 1)! ≤ k`, the homomorphic images of
the layer groups have `PrimBounded _ (3 k³ + 3 k² + 12 k + 1)`. -/
theorem layerPrim_bounded {Δ k : ℕ} (hk2 : 2 ≤ k) (hk : (Δ - 1).factorial ≤ k) :
    LayerPrim Δ (3 * k ^ 3 + 3 * k ^ 2 + 12 * k + 1) := by
  intro N G roots lev a b c d hZ hR r D f
  exact primBounded_of_boundedSections ((boundedSections_autR hZ hR hk2 hk r).of_surjective
    f.rangeRestrict f.rangeRestrict_surjective)

end GraphIso.Graph.Valence
