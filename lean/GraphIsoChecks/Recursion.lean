module

public import GraphIso.Recursion.Coarsen
public import GraphIso.Recursion.Pullback
public import GraphIso.Recursion.Potential
import all Init.Data.Array.Basic
import all Init.Data.List.Sort.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Mathlib.Data.List.Sort

/-!
# Milestone 14, stage 14a checks: the recursion's mathematics

Stage 14a is mathematics; its programs come in stages 14b–14f. The checks:
* a concrete hint: `Sym(4)` on the `2`-subsets of `Fin 4`, labelled by themselves (the
  Johnson labels of graph isomorphism);
* the block label on a concrete block system, computed by the kernel;
* kernel-checked instances of `κ`'s drop, the binomial count of the pullback, and the
  potential's step inequality.
-/

@[expose] public section

namespace GraphIsoChecks.Recursion

open Equiv Pointwise GraphIso.Recursion

/-- `Sym(4)` on the `2`-subsets of `Fin 4`, labelled by themselves, is a hint. -/
example : IsHint (MonoidHom.id (Perm (Fin 4))) ((Finset.univ : Finset (Fin 4)).powersetCard 2)
    id :=
  ⟨fun _ _ _ => rfl, {0, 1}, by decide, {0, 2}, by decide, by decide⟩

/-- The block label of `{0, 2, 3}` for the blocks `{0, 1}`, `{2, 3}`: it meets both blocks,
so the label is the block of least intersection. -/
example : blockLabel ({{0, 1}, {2, 3}} : Finset (Finset (Fin 4))) {0, 2, 3} = {{0, 1}} := by
  decide

/-- `κ` drops by two when the base shrinks to three quarters, on a range. -/
example : ∀ m ∈ Finset.range 40, ∀ m' ∈ Finset.range 40, 2 ≤ m → 4 * m' ≤ 3 * m →
    kap m' + 2 ≤ kap m := by
  decide +kernel

/-- The binomial count of the pullback, on a range. -/
example : ∀ m ∈ Finset.range 16, ∀ t ∈ Finset.range 9, ∀ j ∈ Finset.range 9,
    ∀ a ∈ Finset.range 9, 2 * a ≤ m → j ≤ t → 1 ≤ t → 2 * t ≤ m → 2 * a.choose j ≤ m.choose t := by
  decide +kernel

/-- The step inequality on a concrete macro-step: a window of 8 points with a base of 8
points, branching factor 4, two children keeping the hint on 6 points and one dropping it on
4 points. -/
example : ([(8, some 6), (8, some 6), (4, none)].map fun x => potO 10 2 x.1 x.2).sum + 10 ≤
    pot 10 2 8 8 :=
  pot_step (c := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) _
    (by decide) (by
      intro x hx
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> simp)

end GraphIsoChecks.Recursion
