# Lean development plan, milestone 5: all graphs of maximum degree three

Prepared 20 October 2026. This continues `PLAN-4.md` (connected graphs of maximum degree three,
commit 7a39584). The conventions, cost model, contracts and standards of `PLAN.md` and
`lean/docs/` remain in force.

## Objective and completion criteria

Milestone 4 decides isomorphism of **connected** graphs of maximum degree at most three in
polynomial time (`gi3_checked`, `gi3_simpleGraph'`). Its connectivity is `Conn`, which holds
vacuously on no points. This milestone removes the connectivity hypothesis by the standard
reduction to components, so that the final statement covers every mathlib simple graph on
`Fin n` of maximum degree at most three.

**The semantic object.** For valid data `G` on `n` points:

- `u` reaches `v` when they are joined by a walk of `G.toSimpleGraph n`. A point `u` reaches
  `v` exactly when `v` has level below `n` from the root `u`
  (`get (levels n G [u]) v < n`), which the program computes.
- The *component* of `u` is the sorted list of the points it reaches (`compOf n G u`). The
  *components* of `G` (`comps n G`) are the components of the points that are least in their
  own component. They partition `0, …, n − 1`, and none is empty.
- The *component data* `subG G cs` relabel a component `cs` by position: the point `cs[i]`
  becomes `i`. They are valid and connected (`Conn`) on `cs.length` points.

Then:

- **Components are invariant.** An isomorphism `φ` of `X` onto `Y` maps each component `cs`
  of `X` onto a component of `Y` whose data are isomorphic to `subG X cs`. This map is a
  bijection of the components. Hence, for every graph `C`, `X` and `Y` have equally many
  components whose data are isomorphic to `C`.
- **Gluing.** If the components of `X` are matched bijectively with those of `Y`, with an
  isomorphism of the component data for each pair, the glued map is an isomorphism of `X`
  onto `Y`. Distinct components are never adjacent.
- **Greedy matching is complete.** Take the components of `X` in order. For each, remove the
  first remaining component of `Y` of the same size whose data the connected test finds
  isomorphic, and fail if none remains. At the end, fail if a component of `Y` remains.
  - If `X ≅ Y`, the counts above stay equal for the remaining components, and the matching
    never fails. Isomorphism of component data is an equivalence relation.
  - If it succeeds, gluing gives an isomorphism.

The milestone is complete when:

1. **Components.** The following are proved for valid data of maximum degree `≤ 3`:
   - reachability is read off the levels (`lev_lt_iff_reachable`);
   - the components partition the points, are nonempty and closed under adjacency;
   - the component data are valid and connected;
   - the invariance of components under isomorphisms, with the counting statement;
   - gluing;
   - the step of the greedy invariant.
2. **Programs.** The following run in the cost language within explicit polynomial costs,
   each with a well-formedness proof:
   - the components (one level computation per point);
   - the component data;
   - the matching, which calls `mainProg` on each candidate pair of equal size;
   - the gluing, by `arrayUpdate`.
3. **The algorithm.** `allProg` runs inside `luksBody`. For valid data, its result is `none`
   exactly when `X` and `Y` are not isomorphic, and otherwise lists the values of an
   isomorphism (`RunsWithin.allProg`). The cost is at most `allCost n`, polynomial in `n`.
   The matching tests at most `n²` pairs, each costing at most `mainCost n`.
4. **Concrete theorems** with the Schreier–Sims backend, with no assumed oracle:
   - **`gi3_all_checked`**: the checked entry `gi3AllChecked`, on every input `(n, X, Y)`,
     returns `none` exactly when `X` or `Y` is not valid data of maximum degree three. There
     is no connectivity condition, so no exception on no points. Otherwise it returns a
     correct answer (`GIAnswer`) at cost at most an explicit `C (2n + 1)^e`; expect `e = 28`;
   - **`gi3_all_simpleGraph`**: for **any** simple graphs `G`, `H` on `Fin n` with every
     degree at most three, given by their adjacency lists, the result is `some none` exactly
     when there is no `G ≃g H`, and `some (some arr)` gives an isomorphism with values `arr`.
5. **Checks.** Brute force over all `n!` permutations, within the interpreter's budget
   (about 2M cost units a second; one connected test on `K₂` already costs 32M):
   - three isolated points (a non-trivial matching, cheap);
   - `K₂ ⊔ K₁` against a relabelling;
   - `2K₂` against itself relabelled;
   - `2K₂` against `P₄` (component sizes differ, no connected test);
   - `K₃ ⊔ K₁` against `P₃ ⊔ K₁` (equal sizes, not isomorphic);
   - invalid inputs;
   - kernel runs on zero and two points.
6. **Audit and docs.** The principal theorems are added to the axiom audit. `status.md`,
   `theorem-map.md` and the contracts are updated, and the milestone-4 deviation on no
   points is resolved for the new entry.

## Design notes

- **No new group theory.** Each component pair is decided by milestone 4's `mainProg`,
  whose specification (`RunsWithin.mainProg`) needs exactly valid connected data, which the
  component data provide.
- **Components without a visited array.** The component of `u` is
  `(List.range n).filter (get (levels n G [u]) · < n)`. A point is a representative when it
  heads its own component. This costs `n` level computations, `O(n⁴)` in all. It is simpler
  to specify than a search with a visited set, and the cost is negligible next to the
  connected tests.
- **Relabelling by position.** `subG G cs` lists, for each `cs[i]`, the positions in `cs` of
  its neighbours, using `idxOf` (or a position array).
- **Results are existential.** `mainProg`'s answer is given by its specification, not by a
  Lean function. The matching is proved by fold invariants (`RunsWithin.foldList_exists`),
  as the edge loop was in milestone 4, and the combinatorial lemmas are stated independently
  of the programs. The remaining components of `Y` together with the matched ones are a
  permutation of `comps n Y`. Counts are `List.countP` of the isomorphism class of a fixed
  graph.
- **No choice in data.** The permutations built from bijections in the proofs
  (`Equiv.ofBijective`) appear only inside `∃` statements, never in programs.
- **Isomorphism of data across sizes.** `GIso A B` says `A.size = B.size` and some
  `IsIso A.size A B φ` holds. It is reflexive, symmetric and transitive on valid data.

## Phases

| Phase | Work | Gate |
|---|---|---|
| 0 | Plan; executable model of components, component data, greedy matching and gluing, with a brute-force connected test | On all valid graphs with up to five points, the decisions and the glued maps agree with brute force |
| 1 | Reachability, components, component data, invariance and counting | `lev_lt_iff_reachable`; partition; `subG` valid and connected; the counting statement |
| 2 | Gluing and the greedy invariant | Gluing gives `IsIso`; the step and final lemmas of the counting invariant |
| 3 | Programs and costs | `RunsWithin` and well-formedness for components, component data, matching, gluing |
| 4 | The algorithm, the checked entry, the closed form, the `SimpleGraph` statement | `RunsWithin.allProg`, `gi3_all_checked`, `gi3_all_simpleGraph` |
| 5 | Checks, audit, documentation | Small graphs, axiom listing, docs |

## Layout

New modules under `lean/GraphIso/Graph/`:

- `Components.lean` (phases 1 and 2);
- `CompProg.lean` (phase 3);
- `All.lean` (the algorithm, phase 4).

The checked entry and the concrete theorems go in `lean/GraphIso/Solver/GraphAll.lean`, and
checks in `lean/GraphIsoChecks/GraphAll.lean`.

## References

- Eugene M. Luks, *Isomorphism of graphs of bounded valence can be tested in polynomial
  time*, J. Comput. System Sci. 25 (1982): the trivalent test (Section 2) is stated for
  connected graphs, with the standard reduction from arbitrary graphs to their components.
