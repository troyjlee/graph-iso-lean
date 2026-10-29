module

public import GraphIso.SplitJohnson.BipartiteDef

/-!
# Split-or-Johnson: the procedure

Helfgott, Thm. 5.3. The input is a uniprimitive classical coherent configuration
`c : Γ → Γ → ℕ` on a finite type and a threshold `t` (`|Γ| + 2 ≤ 2t`, `t < |Γ|`).
`soj c t` chooses a point `x ∈ Γ` and colours `Γ` by `c x ·`.
* If no colour class has more than `t` points, this colouring is the output.
* Otherwise let `V₁` (colour `aqua`) be the class of more than `t` points, and take the least
  pair (`beige`, `cyan`) of colours with `beige, cyan ≠ aqua` such that some `z ∈ V₁` and `y`
  of colour `beige` have `c z y = cyan` (Exercise B.7 gives one). Bipartite Split-or-Johnson
  runs on `(V₁, {{y} | c x y = beige}; cyan)` with the same threshold, and its colored
  partitions of `V₁` are extended to `Γ` by the colours `c x ·` (`extendPart`).
-/

@[expose] public section

namespace GraphIso.SplitJohnson

open Finset Pointwise GraphIso.Coherent

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ]

/-- Extend a colored partition of `V₁` to `Γ` by the colouring `col` outside `V₁`, each of its
classes as one block. -/
def extendPart (V₁ : Finset Γ) (col : Γ → ℕ) (p : CPart Γ) : CPart Γ :=
  ⟨fun y => if y ∈ V₁ then 2 * p.col y else 2 * col y + 1, fun y =>
    if y ∈ V₁ then p.blk y else univ.filter fun z => z ∉ V₁ ∧ col z = col y⟩

/-- `extendPart` on a leaf. -/
def extendOut (V₁ : Finset Γ) (col : Γ → ℕ) : Option (Out Γ) → Option (Out Γ)
  | some (Sum.inl p) => some (Sum.inl (extendPart V₁ col p))
  | o => o

/-- Split-or-Johnson after individualizing `x`. -/
def sojAt (c : Γ → Γ → ℕ) (t : ℕ) (x : Γ) : STree Γ :=
  let big := univ.filter fun y => t < (univ.filter fun z => c x z = c x y).card
  if big = ∅ then .leaf (some (.inl (colPart univ (c x))))
  else
    let aqua := big.image (c x)
    let pairs := ((big ×ˢ univ).filter fun p => c x p.2 ∉ aqua ∧ c p.1 p.2 ∉ aqua).image
      fun p => Nat.pair (c x p.2) (c p.1 p.2)
    if hp : pairs.Nonempty then
      let k := Nat.unpair (pairs.min' hp)
      (bsoj t big ((univ.filter fun y => c x y = k.1).image singleton)
          fun z s => decide (∃ y ∈ s, c z y = k.2)).bind
        fun o => .leaf (extendOut big (c x) o)
    else .leaf none

/-- **Split-or-Johnson** (Helfgott, Thm. 5.3): choose `x ∈ Γ`, then `sojAt`. -/
def soj (c : Γ → Γ → ℕ) (t : ℕ) : STree Γ :=
  .node (univ.image fun x => ([.inl x] : List (Γ ⊕ Finset Γ))) fun ch =>
    match (show List (Γ ⊕ Finset Γ) from ch) with
    | [.inl x] => sojAt c t x
    | _ => .leaf none

end GraphIso.SplitJohnson
