# Lean development plan, milestone 9: graphs of every bounded valence

Prepared 21 October 2026. This continues `PLAN-8.md` (the Babai–Cameron–Pálfy theorem for
bounded simple sections, commit 61c8d0b). The conventions, cost model, contracts and standards
of `PLAN.md` and `lean/docs/` remain in force.

## Objective and completion criteria

Milestone 7 decides isomorphism of graphs of maximum degree at most five in polynomial time by
Luks's layered reduction: the layer groups are solvable `{2, 3}`-groups, so milestone 6's
bound applies. For larger degree the layer groups need not be solvable. This milestone
decides isomorphism of graphs of **maximum degree at most `Δ`, for every fixed `Δ ≥ 2`**, in
time polynomial in `n` (the exponent depends on `Δ`), with milestone 8's bound in place of
milestone 6's. This is Luks's theorem (1982).

**The layer groups have bounded sections.** For a layered graph of maximum degree `Δ` rooted at
two edges (`LayeredD Δ`, `Roots4`), and every `k ≥ 2` with `(Δ − 1)! ≤ k`, every layer group
`A_r` has simple sections of order at most `k`:

- `A₀` is a `2`-group, and a simple section of a `p`-group has order `p`;
- the kernel of the restriction `A_{r+1} → A_r` embeds in the product over the points of the
  permutation groups of their twin classes (milestone 7's `twinHom`), each of at most `Δ − 1`
  points, so of order at most `(Δ − 1)!`;
- bounded sections are closed under subgroups, finite products and extensions (milestone 8),
  so by induction on `r` every `A_r` has `BoundedSections k`.

With `c = 3k³ + 3k² + 12k + 1`, `primBounded_of_boundedSections` gives `PrimBounded _ c` for
every homomorphic image of every layer group, which is what each string-isomorphism call
needs: one layer step costs at most `6640 (D + 1)^{3c + 5} + …` on `D ≤ N + (N + 1)^Δ` points.

The milestone is complete when:

1. **Group theory.** `BoundedSections.mono`; `p`-groups have `BoundedSections p`.
2. **Bounded layer groups** (`Valence/Bounded.lean`): twin classes of at most `Δ − 1` points
   for every `Δ` (milestone 7's bound of four for `Δ ≤ 5` is the special case), and
   `boundedSections_autR`: every layer group has `BoundedSections k` for `2 ≤ k`,
   `(Δ − 1)! ≤ k`.
3. **The step constant as a parameter.** Milestone 7's layer step, edge test, main loop and
   matching of components take the constant `c` of the string-isomorphism calls as a
   parameter, with the hypothesis `LayerPrim Δ c` (every homomorphic image of every layer
   group has `PrimBounded _ c`) in place of `Δ ≤ 5`. Milestone 7 instantiates it with
   `c = 13` (`Δ ≤ 5`, solvable), milestone 9 with the bounded-sections constant. The
   protected statements of milestone 7 are unchanged.
4. **Checked entries** for every `Δ ≥ 2`, with the Schreier–Sims backend, no assumed oracle:
   - `gi_bounded_checked`, `gi_bounded_simpleGraph'`: connected graphs of maximum degree at
     most `Δ`;
   - `gi_bounded_all_checked`, `gi_bounded_all_simpleGraph'`: all graphs of maximum degree at
     most `Δ`;
   each `none` exactly on invalid input and otherwise a correct answer (`GIAnswer`), at cost at
   most `C (Δ + 1)³ (2n + 2)^{Δ (9k³ + 9k² + 36k + 8) + e}` for every `k ≥ 2` with
   `(Δ − 1)! ≤ k` (`e = 2` connected, `4` all graphs; `C` an explicit numeral).
5. **Checks** (`GraphIsoChecks/ValenceBounded.lean`): kernel-evaluated and interpreter runs of
   the new entries for `Δ = 6` against brute force, invalid inputs (a vertex of degree seven),
   and a layer step whose group is not a `{2, 3}`-group: the first layer step of two stars
   `K₁,₆` has a twin class of five points, so `S₅ × S₅` lies in `A₁` and `5` divides `|A₁|`.
6. **Audit and docs**: axiom listing of the new principal theorems; `theorem-map.md`,
   `status.md`.

## Design notes

- **Costs.** For `K = N + 2` and `T = K^Δ`: `D + 1 ≤ T`, at most `T²` generators, and every
  lower-order term of a layer step is at most a numeral times `(Δ + 1)² T⁶`. As `3c + 5 ≥ 8`,
  the solver term `6640 T^{3c + 5}` dominates, and the edge test and the loop over edges add
  two factors of `2n + 2` and one of `Δ`. For `Δ = 5` the general constant is far worse than
  milestone 7's (which uses `c = 13`); milestone 7 keeps its own closed forms.
- **Matching components.** The bound on the connected test on at most `n` points becomes a
  parameter of milestone 7's matching (`∀ k ≤ n, mainCost Δ c k ≤ M`), so one proof serves
  both milestones.
- **The exponent** is enormous (`k ≥ 120` for `Δ = 6`); it is polynomial in `n` for each
  fixed `Δ`, which is Luks's theorem. Babai's quasipolynomial methods are a later milestone.

## References

- Eugene M. Luks, *Isomorphism of graphs of bounded valence can be tested in polynomial
  time*, J. Comput. System Sci. 25 (1982).
- László Babai, Peter J. Cameron, Péter P. Pálfy, *On the orders of primitive groups with
  restricted nonabelian composition factors*, J. Algebra 79 (1982), 161–168.
- Harald A. Helfgott, *Isomorphismes de graphes en temps quasi-polynomial*, Séminaire
  Bourbaki 1125 (2017), Theorem 2.3.
