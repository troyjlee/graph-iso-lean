# Lean development plan, milestone 11: Split-or-Johnson

Prepared 21 October 2026. This continues `PLAN-10.md` (Weisfeiler–Leman and the Design Lemma,
commit 7ce6b60), whose roadmap lists this milestone. The conventions, cost model, contracts and
standards of `PLAN.md` and `lean/docs/` remain in force, and so does the CFSG decision recorded
in `PLAN-10.md`: the completion target is CFSG-free.

## Scope

Helfgott's Theorem 5.3 (Babai §7, with the correction in Babai's note *Fixing the UPCC case of
Split-or-Johnson*, 14 January 2017, https://people.cs.uchicago.edu/~laci/upcc-fix.pdf).

**Theorem 5.3.** Let `X` be a uniprimitive classical coherent configuration on `Γ`. At a
multiplicative cost of `|Γ|^{O(log |Γ|)}`, one can find one of the following, canonically:
- a colored `α`-partition of `Γ`; or
- a Johnson scheme embedded in a set `Γ₀ ⊆ Γ` with `|Γ₀| ≥ α|Γ|`.

The proof needs its two propositions, Bipartite Split-or-Johnson (Prop. 5.7) and Coherent
Split-or-Johnson (Prop. 5.8), and the lemmas they use: Exercises 2.15–2.18, 5.4–5.6 and B.7,
and the Ray-Chaudhuri–Wilson inequality (Prop. 2.20).

**Arbitrary uniprimitive inputs.** The CFSG-free replacement of Cameron's theorem (`PLAN-10.md`)
feeds Split-or-Johnson the orbital configurations of uniprimitive groups. Theorem 5.3 is
therefore stated for every uniprimitive classical coherent configuration, not only for those
that the Design Lemma produces.

**Model level.** The procedures are ordinary computable Lean functions, the models, with
correctness, canonicity and multiplicative-cost theorems. As in milestone 10 they run in the
checks. Their costed PHOAS programs are deferred to milestone 14, where the running times of
all the subroutines of the main recursion are assembled. This milestone claims no running time.

## Canonicity relative to choices

Babai's notion (Def. 4.0.4, "reduction at multiplicative cost `s`") is formalized by **choice
trees**:

```
inductive CTree (C O : Type) | leaf : O → CTree C O | node : Finset C → (C → CTree C O) → CTree C O
```

A node is an arbitrary choice, for example individualizing a point, from a canonically
determined finite set. The tree records these quantities:
- its **reachable leaves**, following only choices in the node sets;
- its **count**, the number of root-to-leaf paths, which is Babai's multiplicative cost;
- its **liveness**: every reachable node set is nonempty.

A permutation `σ` acts on trees through its action on choices and outputs. A procedure `F` is
**canonical** if `F (σ • X) = σ • F X` for every `σ` and every input, an equality of trees.

For isomorphism testing this gives `leaves (F Y) = σ • leaves (F X)` whenever `σ` maps `X` to
`Y`. To test `X` against `Y`, one therefore fixes one leaf of `F X` and compares it with every
leaf of `F Y`, at most `count (F Y)` comparisons.

## Objects

Points are a type `α` with decidable equality, and permutations `σ : Equiv.Perm α` act
throughout.
- **Cells.** The second side of a bipartite graph consists of *cells* `Finset α`: Babai's
  "ideal points". The contraction in Prop. 5.8 replaces a block of cells by its union.
- **Choices** are lists over `α ⊕ Finset α`: a point, a cell, or a tuple of cells.
- **Colored partitions** (Babai Def. 5.1.1). A colored partition of a finite set `V` is a
  colouring `col : α → ℕ` together with a block map `blk : α → Finset α`. The block map gives
  each point the block that contains it, so blocks are named by their elements, which is
  canonical. It is required to be:
  - **an equipartition:** the blocks partition `V`, and each colour class is a union of blocks
    of one size;
  - **admissible:** every block of a colour class with at least two points has at least two
    points;
  - **a `t`-partition:** every block has at most `t` points.
- **Johnson embeddings** (`J(r, s)`, `2 ≤ s`, `2s ≤ r`, as in Helfgott §5.3.3). A Johnson
  embedding is a set `V₀`, a set `Λ` of nonempty, pairwise disjoint cells, a size `s`, and a
  map `f` that is a bijection from `V₀` onto the `s`-subsets of `Λ`. Its scheme is
  `c(v, w) = |f v \ f w|`.
- **Thresholds** are natural numbers, as in milestone 10. In place of Helfgott's `α ≥ 2/3` the
  theorems take a `t` with `|V| + 2 ≤ 2t` and `t < |V|`: any `α > 1/2 + 1/|V|`, as Helfgott
  remarks.

## Completion criteria

1. **Classical coherent configurations on a set** (`GraphIso/Coherent/`, mathlib imports only).
   - **Definitions:** homogeneity; primitivity (every off-diagonal colour graph connected,
     taking undirected reachability); uniprimitivity (primitive and not a clique); and the
     restriction to a union of vertex colour classes, which is again coherent.
   - **Exercise 2.15:** a configuration that is not a clique has no clique on more than half of
     its points.
   - **Exercise 2.16:** walk counts depend only on the end colour; the connected components of
     a colour graph all have the same size.
   - **Exercise 2.17:** colour graphs between two colour classes, and between two neighbourhood
     sets `L_i(y)` and `L_j(y)`, are semiregular bipartite graphs.
   - **Exercise 2.18:** contracting the components of a colour graph gives a semiregular
     bipartite graph.
   - **Exercise 5.4:** a nontrivial semiregular bipartite graph has no twin class larger than
     half of its first side.
   - **Exercise 5.5:** splitting the second side of a graph without twins in its first side
     leaves one half with no twin class of `|V₁|/2 + 1` or more points.
   - **Exercise 5.6:** in a coherent configuration, the colour of a pair determines whether its
     points are twins with respect to a colour graph into another class.
   - **Exercise B.7:** in a uniprimitive configuration, any two points joined by a colour `r`
     have a common neighbour in the complement of `r`.
2. **The Ray-Chaudhuri–Wilson inequality** (Prop. 2.20).
   - **Statement:** let `(V, A)` be a family of `u`-subsets of `V`, repeated blocks allowed, in
     which every `t`-subset of `V` lies in exactly `λ ≥ 1` blocks. If `2s ≤ t ≤ u` and
     `s + u ≤ |V|`, then the number of blocks is at least `C(|V|, s)`.
   - **Proof:** Helfgott's Exercise B.14. The incidence vectors of the blocks' `s`-subsets
     span the `ℚ`-vector space on the `s`-subsets, by a triangular system with positive
     diagonal.
3. **Weisfeiler–Leman on any finite type.** `wlOn k c` is milestone 10's `wl`, transported
   along an enumeration `V ≃ Fin |V|`. It is independent of the enumeration by `wl_relabel`,
   and is defined computably through `Fintype.truncEquivFin` and `Trunc.lift`. Its properties
   follow from milestone 10:
   - it is a coherent configuration refining `c`;
   - it has the same twins as `c`;
   - it is natural under every equivalence `V ≃ V'`.
4. **Choice trees**: the definitions above, with their facts:
   - relabelling commutes with leaves, count and liveness;
   - bind, with `count (t >>= f) ≤ count t · max count f`;
   - the isomorphism transfer for canonical procedures.
5. **Coherent Split-or-Johnson** (Prop. 5.8). The input is a classical coherent configuration
   on `C₁ ∪ C₂` whose vertex colour classes are `C₁` and `C₂`, with these hypotheses:
   - `|C₁| > |C₂|`;
   - the colouring is not constant on `C₁ × C₂`;
   - its restriction to `C₂` is not a clique.

   The procedure is canonical under all permutations of the point type, makes at most one
   choice (`count ≤ |C₂|`), is live, and every reachable leaf is one of:
   - (a) a colored partition of `C₁` with blocks of at most `|C₁|/2` points; or
   - (b) a bipartite graph `(W₁, W₂; A')` meeting all of these:
     - `W₁ ⊆ C₁` with `|C₁| ≤ 2|W₁|`;
     - `W₂` consists of nonempty, pairwise disjoint subsets of `C₂`, and `2|W₂| ≤ |C₂|`;
     - no twin class of `W₁` has more than `|W₁|/2` points.

   The proof is Helfgott's, including Babai's corrected argument for a primitive `X[C₂]`
   (footnote 17).
6. **Bipartite Split-or-Johnson** (Prop. 5.7).
   - **Input:** a bipartite graph `(V₁, V₂; A)` with `V₁` points and `V₂` nonempty, pairwise
     disjoint cells, and a threshold `t`, with these hypotheses:
     - `|V₂| ≤ t`;
     - `|V₁| + 2 ≤ 2t` and `t < |V₁|`;
     - no twin class of `V₁` has more than `t` points.
   - **Guarantees:** the procedure is canonical and live, and every reachable leaf is a colored
     `t`-partition of `V₁` or a Johnson embedding with `V₀ ⊆ V₁` and `|V₀| > t`.
   - **Count:** at most an explicit `2^{K (⌈log₂ t⌉ + 1)²}`, with the numeral `K` fixed in the
     proof.
7. **Split-or-Johnson** (Thm. 5.3), for a uniprimitive classical coherent configuration
   `c : Γ → Γ → ℕ` on a finite type and a threshold `t` with `|Γ| + 2 ≤ 2t` and `t < |Γ|`.
   - **Guarantees:** the procedure is canonical under `Sym(Γ)` and live, and every reachable
     leaf is a colored `t`-partition of `Γ` or a Johnson embedding with `|V₀| > t`.
   - **Count:** at most `2^{K (⌈log₂ |Γ|⌉ + 1)²}`, which is `|Γ|^{O(log |Γ|)}`.
8. **Checks** (`GraphIsoChecks/SplitJohnson.lean`): interpreter runs of the procedures on small
   inputs, with these checked:
   - the reachable leaves are valid outputs (checked directly);
   - relabelling the input relabels the leaves.

   Runs of Theorem 5.3 on uniprimitive Johnson-scheme and strongly-regular inputs, with the
   leaves of both outcome types, and runs of Prop. 5.7 and Prop. 5.8 on hand-made inputs that
   reach their main branches.
9. **Audit and docs**: axiom listing of the new principal theorems; `theorem-map.md`,
   `status.md`.

## Design notes

- **Thresholds for the whole recursion.** Prop. 5.7 recurses on smaller bipartite graphs but
  keeps the threshold `t` of the original `V₁` ("for the original value of `|V₁|`"). The points
  dropped at a step are given new colours, one per dropped piece:
  - the points that have twins or a minority degree;
  - the points outside the dominant colour class `C₁`;
  - the points of `C₁` outside `W₁`.

  Each piece has at most `t` points, because `|V₁| ≤ 2t` and `|W₁| ≥ |C₁|/2`. So a colored
  `t`-partition found deeper in the recursion extends to one of the original `V₁`. With this
  invariant, Helfgott's base case `|V₁| ≤ c` is not needed.
- **The `d`-ary structure on `V₂`.** Let `n₁ = |V₁'|` and `v = |V₂|`. Let `j` be the least
  integer with `n₁ ≤ v^j`, and put `d = min(d₁, 6j)` (Helfgott's `6⌈l⌉`).
  - **Base case.** If `v² ≤ 27 L³`, with `L = ⌈log₂ 2t⌉`, every enumeration of `V₂` is a
    choice. A colouring by neighbourhoods then separates the points of `V₁` without twins.
  - **Otherwise** `v² > 27 j³`. When `d < d₁`, a constant `d`-ary structure would make the
    hypergraph a `d`-design. Ray-Chaudhuri–Wilson would then give `n₁ ≥ C(v, 3j) > v^j ≥ n₁`,
    using `s^s C(v, s) ≥ v^s`.
  - **The Design Lemma's choice** costs at most `v^d < (v n₁)^6`, a polynomial.
- **Count.** Every level that makes choices shrinks `|V₂|` to at most `2|V₂|/3`; the twin-class
  split and the constant-colour case make no choices. With at most `2 ⌈log₂ t⌉ + 2` such
  levels, each costing at most `(2t)^{13}`, and a base case of at most `v!`, the count is
  `2^{O((log t)²)}`.
- **Weisfeiler–Leman** is applied in two places. The `d`-ary structure on `V₂` uses the type
  `↥V₂`. The classical structure on `V₁' ∪ V₂` uses the type `α ⊕ Finset α`, restricted to a
  `Finset`. Canonicity of these steps comes from the naturality of `wlOn` under the
  equivalence `↥V₂ ≃ ↥(σ • V₂)` induced by `σ`.
- **Termination.** Every recursive call of Prop. 5.7 has fewer cells. A continuation whose
  chosen value is not in its node set is guarded and returns a junk leaf, which is unreachable.
- **Prop. 5.8** is stated for an arbitrary point type `R`, canonical under all of `Sym(R)`.
  Prop. 5.7 applies it with `R = α ⊕ Finset α` and `σ` acting on both summands.

## References

- László Babai, *Graph isomorphism in quasipolynomial time*, arXiv:1512.03547, §§4, 5.1 and 7,
  with the correction to Split-or-Johnson in *Fixing the UPCC case of Split-or-Johnson* (note,
  14 January 2017, https://people.cs.uchicago.edu/~laci/upcc-fix.pdf).
- Harald A. Helfgott, *Graph isomorphisms in quasi-polynomial time* (Séminaire Bourbaki 1125,
  English translation by J. Bajpai and D. Dona, arXiv:1710.04574), §§2.4–2.7 and 5.2, and
  Exercises B.7 and B.14.
- D. K. Ray-Chaudhuri, R. M. Wilson, *On t-designs*, Osaka J. Math. 12 (1975), 737–744.
