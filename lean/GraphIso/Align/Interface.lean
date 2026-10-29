module

public import GraphIso.SoJTree.LeafData
public import GraphIso.Representation.Group

/-!
# Structures on the base: the interface

Stage 14f (`PLAN-14.md` §10). Align works with canonical structures on the base `Fin m`, given
on data. For each kind of structure (a set, a colored partition, a trimmed Johnson embedding)
the stage provides a `StructOps`: the decoding, a list of generators of the stabilizer in
`Sym(Fin m)`, and an isomorphism search. `StructOps.Spec` states what Align needs of them:

* the generators are valid and generate exactly the stabilizer of the decoded structure;
* the search returns a valid permutation carrying one structure to the other, or `none`
  exactly when no permutation does.

`Valid` is the representation invariant of the kind (for example `IsColPart` on the decoded
partition, or `IsJohnson` with cells disjoint from `V₀` for a trimmed Johnson embedding).
-/

@[expose] public section

namespace GraphIso.Align

open Equiv GraphIso

/-- The operations Align needs on one kind of structure on `Fin m`, on data. -/
structure StructOps (m : ℕ) (τ O : Type) [MulAction (Perm (Fin m)) O] where
  /-- The decoding. -/
  dec : τ → O
  /-- Generators of the stabilizer in `Sym(Fin m)`. -/
  gens : τ → List PermData
  /-- A permutation carrying the first structure to the second, if there is one. -/
  iso : τ → τ → Option PermData

/-- **What Align needs of a kind of structure.** -/
structure StructOps.Spec {m : ℕ} {τ O : Type} [MulAction (Perm (Fin m)) O]
    (S : StructOps m τ O) (Valid : τ → Prop) : Prop where
  gens_valid : ∀ x, Valid x → ∀ g ∈ S.gens x, g.Valid m
  gens_closure : ∀ x, Valid x →
    Subgroup.closure {σ | ∃ g ∈ S.gens x, PermData.denote m g = σ} =
      MulAction.stabilizer (Perm (Fin m)) (S.dec x)
  iso_some : ∀ x y, Valid x → Valid y → ∀ σ, S.iso x y = some σ →
    σ.Valid m ∧ PermData.denote m σ • S.dec x = S.dec y
  iso_none : ∀ x y, Valid x → Valid y → S.iso x y = none →
    ∀ σ : Perm (Fin m), σ • S.dec x ≠ S.dec y

end GraphIso.Align
