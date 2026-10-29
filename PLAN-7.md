# Lean development plan, milestone 7: graphs of valence at most five

Prepared 20 October 2026. This continues `PLAN-6.md` (primitive solvable groups, commit
b06c86b). The conventions, cost model, contracts and standards of `PLAN.md` and `lean/docs/`
remain in force.

## Objective and completion criteria

Milestones 4 and 5 decide isomorphism of graphs of maximum degree three in polynomial time by
Luks's layered reduction: the layer groups are `2`-groups, so milestone 3's nilpotent bound
applies. This milestone extends the reduction to **maximum degree at most five**. The layer
groups are then solvable `{2, 3}`-groups, and milestone 6's `primBounded_of_isSolvable` with
`s = 1` bounds every string-isomorphism call.

**The reduction for valence `d`.** As in milestone 4, `Z = X ⊔ Y` is rooted at an edge of each
graph, `A_r` is the group of permutations supported on level `≤ r` that preserve levels and
the edges of `Z_r`, and one layer is a string-isomorphism instance on the graph's points and
the subsets of level `r` with at most `d` points:

- a point of level `r + 1` has at most `d` neighbours in level `r`, so its neighbourhood is
  one of the subsets;
- a point of level `r` has a neighbour one level down (or a root partner), so it has at most
  `d − 1` neighbours one level up: **twin classes have at most `d − 1` points**;
- the layer string records, for each subset, the number of new points with that
  neighbourhood, plus `d + 1` when the subset is an edge.

The extension criterion, the canonical lifts, the twin transpositions and the swap criterion
of milestone 4 hold for every `d`. Only two facts depend on `d ≤ 5`:

- the kernel of `A_{r+1} → A_r` permutes each twin class (at most four points), so it embeds
  in a product of symmetric groups of degree at most four: it is **solvable**
  (`Equiv.Perm.isSolvable`), and **every element `k` satisfies `k¹² = 1`**;
- hence, by induction on `r`, every `A_r` is solvable and every element has order
  `2^a 3^b`. By Cauchy's theorem the order of `A_r` has at most the two prime divisors `2`
  and `3`. Solvability comes from the construction: Burnside's `pᵃqᵇ` theorem is not used.

**Subsets.** A subset of level `r` is a sublist of the increasing list of the level's points,
of length at most `d` (`subsR d`), so each subset has exactly one representative and the
count is at most `(ℓ + 1)^d`. The image of a subset under a permutation is found by a linear
search for the representative with the same elements (no index array).

The milestone is complete when:

1. **Generic theory.** The degree-free parts of milestones 4–5 (validity, levels, layer
   groups, extension criterion, lifts, twins, roots, swap criterion, components, simple
   graphs) are stated for maximum degree `d` (`GraphData.ValidD d`), with
   `GraphData.Valid = ValidD 3`; the protected statements of milestones 4–5 are unchanged.
2. **Solvable layer groups.** For `d ≤ 5`: every `A_r` is solvable and the number of prime
   divisors of its order is at most two.
3. **Programs.** The subsets, the layer string, the induced generators, the lifts and twin
   swaps, the levels and validation for degree `d`, with exact values, explicit polynomial
   costs and well-formedness proofs.
4. **The algorithm.** Each layer step calls `solveEntry` (Luks's strategy); the edge test,
   the main loop and the checked entries for connected graphs and, through milestone 5's
   components, for all graphs.
5. **Concrete theorems** with the Schreier–Sims backend, no assumed oracle:
   - `gi5_checked`, `gi5_simpleGraph'`: connected graphs of maximum degree at most five;
   - `gi5_all_checked`, `gi5_all_simpleGraph'`: all graphs of maximum degree at most five;
   each with an explicit closed-form polynomial cost bound in `n`, `none` exactly on invalid
   input, and otherwise a correct answer (`GIAnswer`).
6. **Checks.** Interpreter runs against brute force on small graphs with a vertex of degree
   four (a twin class of three points), as far as the interpreter allows.
7. **Audit and docs.** Axiom listing of the new principal theorems; `theorem-map.md`,
   `status.md` updated.

## Design notes

- **Costs.** One layer instance has `D ≤ N + (N + 1)^5` points for `N = 2n`; the solvable
  bound gives `6640 (D + 1)^44 + 60 L (D + 1)²` per call. The exponent is large; the bound is
  polynomial.
- **Reuse.** Milestone 4's program definitions that do not depend on the degree (levels,
  union, lifts, twin swaps, swap test, components, gluing) are reused; their cost lemmas are
  restated for degree `d`. The triple-based subset programs stay as they are for `d = 3`.

## References

- Eugene M. Luks, *Isomorphism of graphs of bounded valence can be tested in polynomial
  time*, J. Comput. System Sci. 25 (1982).
- László Babai, *Graph isomorphism in quasipolynomial time*, 2016, Section 2.
