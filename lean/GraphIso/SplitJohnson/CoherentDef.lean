module

public import GraphIso.SplitJohnson.CTree
public import GraphIso.SplitJohnson.Output
public import GraphIso.Coherent.Classical
public import GraphIso.Coherent.BipGraph

/-!
# Coherent Split-or-Johnson: the procedure

Helfgott, Prop. 5.8. The input is a classical coherent configuration `c` on `C₁ ∪ C₂` whose
vertex colour classes are `C₁` and `C₂`, with `|C₁| > |C₂|`, `c` not constant on `C₁ × C₂`
and `X[C₂]` not a clique. `cohSoj C₁ C₂ c` makes at most one choice, a point `y ∈ C₂`, and
returns one of the following (`CohOut`):
* `part p`: a colored partition of `C₁` whose blocks have at most `|C₁|/2` points;
* `bip W₁ W₂ A'`: a bipartite graph with `W₁ ⊆ C₁`, `|W₁| ≥ |C₁|/2`, `W₂` a set of nonempty,
  pairwise disjoint subsets of `C₂` ("ideal points") with `|W₂| ≤ |C₂|/2`, and no twin class of
  `W₁` with more than `|W₁|/2` points.

The steps follow Helfgott's proof (the "reddest" colour is the least one):
1. If `X[C₁]` is imprimitive, the components of its least disconnected colour partition `C₁`.
2. If `X[C₂]` is imprimitive, with blocks `B` the components of its least disconnected colour:
   * if no colour `k` on `C₁ × C₂` has more than `|C₁|/2` points `x` with `c x w = k` for some
     `w`, choose `w ∈ C₂` and colour `C₁` by `c x w`;
   * otherwise, with `violet` the least such colour: if some block `B` has no twin class in
     `C₁` (for the `violet` edges into `B`) of more than `|C₁|/2` points, choose `y` in such a
     block and return `(C₁, {{z} | z ∈ B_y}; violet)`;
   * otherwise return the contraction `(C₁, {B}; green)`, `green` the least other colour.
3. If `X[C₂]` is primitive, choose `y ∈ C₂`. If some colour `violet` has more than `|C₁|/2`
   points `x` with `c x y = violet`, return `(L_violet(y), {{z} | z ∈ L_blue(y)}; violet)` with
   `blue` the least colour of `X[C₂]` of positive degree below `|C₂|/2` (Babai's corrected
   argument, Helfgott footnote 17); otherwise colour `C₁` by `c x y`.
-/

@[expose] public section

namespace GraphIso.SplitJohnson

open Finset Pointwise GraphIso.Coherent

variable {R : Type*} [DecidableEq R]

/-- The outputs of Coherent Split-or-Johnson. -/
inductive CohOut (R : Type*)
  | part : CPart R → CohOut R
  | bip : Finset R → Finset (Finset R) → (R → Finset R → Bool) → CohOut R

/-- The colouring `f` of `S` with each colour class as one block. -/
def colPart (S : Finset R) (f : R → ℕ) : CPart R :=
  ⟨f, fun x => S.filter fun y => f y = f x⟩

/-- Edges of colour `g` from a point to a set of points. -/
def bipEdge (c : R → R → ℕ) (g : ℕ) (x : R) (B : Finset R) : Bool :=
  decide (∃ y ∈ B, c x y = g)

/-- The colours of `X[S]` whose graphs are disconnected. -/
def disconn (S : Finset R) (c : R → R → ℕ) : Finset ℕ :=
  (offCols S c).filter fun r => ∃ x ∈ S, comp S c r x ≠ S

/-- **Coherent Split-or-Johnson** (Helfgott, Prop. 5.8). -/
def cohSoj (C₁ C₂ : Finset R) (c : R → R → ℕ) : CTree R (Option (CohOut R)) :=
  if h₁ : (disconn C₁ c).Nonempty then
    -- `X[C₁]` is imprimitive: the components of its reddest disconnected colour
    .leaf (some (.part ⟨fun _ => 0, comp C₁ c ((disconn C₁ c).min' h₁)⟩))
  else
    let cols := (C₁ ×ˢ C₂).image fun p => c p.1 p.2
    if h₂ : (disconn C₂ c).Nonempty then
      -- `X[C₂]` is imprimitive, with blocks the components of `red`
      let red := (disconn C₂ c).min' h₂
      let big := cols.filter fun k =>
        ∃ w ∈ C₂, C₁.card < 2 * (C₁.filter fun x => c x w = k).card
      if hv : big.Nonempty then
        let violet := big.min' hv
        let good := (C₂.image (comp C₂ c red)).filter fun B =>
          ∀ x ∈ C₁, 2 * (twinCls C₁ B (fun x y => decide (c x y = violet)) x).card ≤ C₁.card
        if good.Nonempty then
          .node (C₂.filter fun y => comp C₂ c red y ∈ good) fun y =>
            .leaf (some (.bip C₁ ((comp C₂ c red y).image singleton) (bipEdge c violet)))
        else if hg : (cols.erase violet).Nonempty then
          .leaf (some (.bip C₁ (C₂.image (comp C₂ c red))
            (bipEdge c ((cols.erase violet).min' hg))))
        else .leaf none
      else
        .node C₂ fun w => .leaf (some (.part (colPart C₁ fun x => c x w)))
    else
      -- `X[C₂]` is primitive
      .node C₂ fun y =>
        let big := cols.filter fun k => C₁.card < 2 * (C₁.filter fun x => c x y = k).card
        if hv : big.Nonempty then
          let violet := big.min' hv
          let blues := (offCols C₂ c).filter fun b =>
            0 < (C₂.filter fun z => c y z = b).card ∧
              2 * (C₂.filter fun z => c y z = b).card < C₂.card
          if hb : blues.Nonempty then
            .leaf (some (.bip (C₁.filter fun x => c x y = violet)
              ((C₂.filter fun z => c y z = blues.min' hb).image singleton) (bipEdge c violet)))
          else .leaf none
        else .leaf (some (.part (colPart C₁ fun x => c x y)))

/-- A valid output of Coherent Split-or-Johnson. -/
def CohValid (C₁ C₂ : Finset R) : Option (CohOut R) → Prop
  | some (.part p) => IsColPart C₁ (C₁.card / 2) p
  | some (.bip W₁ W₂ A) =>
      W₁ ⊆ C₁ ∧ C₁.card ≤ 2 * W₁.card ∧ (∀ B ∈ W₂, B.Nonempty ∧ B ⊆ C₂) ∧
        (∀ B ∈ W₂, ∀ B' ∈ W₂, B ≠ B' → Disjoint B B') ∧ 2 * W₂.card ≤ C₂.card ∧
        ∀ x ∈ W₁, 2 * (twinCls W₁ W₂ A x).card ≤ W₁.card
  | none => False

/-! ### Actions -/

/-- Relabel a colouring of pairs. -/
def relab2 {G : Type*} [Group G] [MulAction G R] (g : G) (c : R → R → ℕ) : R → R → ℕ :=
  fun x y => c (g⁻¹ • x) (g⁻¹ • y)

instance : MulAction (Equiv.Perm R) (CohOut R) where
  smul σ
    | .part p => .part (σ • p)
    | .bip W₁ W₂ A => .bip (σ • W₁) (σ • W₂) fun x B => A (σ⁻¹ • x) (σ⁻¹ • B)
  one_smul o := by
    cases o with
    | part p => show CohOut.part _ = _; rw [one_smul]
    | bip W₁ W₂ A => show CohOut.bip _ _ _ = _; simp only [one_smul, inv_one]
  mul_smul σ τ o := by
    cases o with
    | part p => show CohOut.part _ = CohOut.part _; rw [mul_smul]
    | bip W₁ W₂ A =>
      show CohOut.bip _ _ _ = CohOut.bip _ _ _
      simp only [mul_smul, mul_inv_rev]

end GraphIso.SplitJohnson
