module

public import GraphIso.SplitJohnson.BipartiteValid
public import GraphIso.SplitJohnson.BipartiteCount
public import GraphIso.SplitJohnson.BipartiteRelabel

/-!
# Bipartite Split-or-Johnson

**Bipartite Split-or-Johnson** (Helfgott, Prop. 5.7): for a bipartite graph `(V₁, V₂; A)` with
`V₂` a set of nonempty, pairwise disjoint cells and a threshold `t` with `|V₂| ≤ t`,
`|V₁| + 2 ≤ 2t`, `t < |V₁|`, and no twin class of `V₁` above `t` points, the choice tree
`bsoj t V₁ V₂ A` is live, has at most `2^{128 (⌈log₂ t⌉ + 2)²}` paths, and every reachable leaf
is a colored `t`-partition of `V₁` or a Johnson scheme embedded in `V₁` on more than `t` points.
It is canonical (`bipartite_split_or_johnson_relabel`).
-/

@[expose] public section

namespace GraphIso.SplitJohnson

open Finset Pointwise GraphIso.Coherent

variable {α : Type*} [DecidableEq α]

/-- **Bipartite Split-or-Johnson** (Helfgott, Prop. 5.7). -/
theorem bipartite_split_or_johnson {t : ℕ} {V₁ : Finset α} {V₂ : Finset (Finset α)}
    {A : α → Finset α → Bool} (hcells : ∀ s ∈ V₂, s.Nonempty)
    (hdisj : ∀ s ∈ V₂, ∀ s' ∈ V₂, s ≠ s' → Disjoint s s') (hv : V₂.card ≤ t)
    (h₁ : V₁.card + 2 ≤ 2 * t) (h₂ : t < V₁.card)
    (htw : ∀ x ∈ V₁, (twinCls V₁ V₂ A x).card ≤ t) :
    (bsoj t V₁ V₂ A).Live ∧ (bsoj t V₁ V₂ A).count ≤ 2 ^ (128 * (Nat.clog 2 t + 2) ^ 2) ∧
      (bsoj t V₁ V₂ A).AllLeaves (ValidOut V₁ t) := by
  have h : BInv t V₁ V₂ A := ⟨hcells, hdisj, hv, h₁, h₂, htw⟩
  exact ⟨(bsoj_valid h).1, bsoj_count_le hv (by omega), (bsoj_valid h).2⟩

end GraphIso.SplitJohnson
