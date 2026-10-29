# Representations, cost model and backend contracts

## Finite representations (`GraphIso/Representation/`)

| Object | Data | Validity | Denotation |
|---|---|---|---|
| Permutation | `PermData = Array ℕ × Array ℕ` (forward, inverse) | `PermData.Valid n`: lengths `n`, entries `< n`, mutually inverse; checked by `validB` | `PermData.denote n : Perm (Fin n)` (identity on invalid data) |
| Generators | `GensData = List PermData` | `GensData.AllValid n` | `GensData.denote n = Subgroup.closure {denote g}` |
| Window | `WinData = List ℕ × Array Bool` (points, mask) | `WinData.Valid n`: nodup, `< n`, mask agrees, mask length `n` | `WinData.denote n : Set (Fin n)` |
| String | `StrData = Array ℕ` | `StrData.Valid n q`: length `n`, symbols `< q` | `StrData.denote n : Fin n → ℕ` |
| Group | `GroupData D = ℕ × GensData × D` (degree, generators, backend data) | `GroupValid DV n gs d` | the generated subgroup; backend data never changes it |
| Instance | `InstanceData D` | `InstanceData.Valid q`, checked by `validB`, includes window invariance under the generators | `W`, `σ`, `G`, `xs`, `ys`, `solutions` |

Executable checks with exact characterizations:

- `GensData.invariantB_iff`: generator-only check ↔ `IsInvariant` of the generated group
  (finite windows; uses `isInvariant_closure_iff`).
- `GensData.fixesB_iff`: ↔ `FixesPointwise`.
- `matchesB_iff`: ↔ `Matches` on the window, without inverting the permutation.
- `StrData.denote_comp`: `y.comp σ` denotes `y ∘ σ` (coset normalization).
- `PermData.denote_mul`, `denote_inv`, `denote_one`, `beq_iff`, `denote_injOn`.

Arrays are read with `get a i = a.getD i 0`, which is exactly the semantics of the cost
language's `arrayGet`. Functional models use `amap` (list-based, equal to `Array.map`) so that
concrete checks reduce in the kernel.

Decoding is total: `StrData.denote n x` reads position `i < n` as `get x i`, so entries past the
array read as `0` and entries past `n` are ignored. Symbols are unbounded naturals.

## The input contract and the two entry points (`GraphIso/Solver/`)

`InputValid q (xy, w, σ, n, gs)` is the full input contract:
- both strings satisfy `StrData.Valid n q`;
- `w`, `σ` and `gs` are valid data of degree `n`;
- `w` is invariant under `⟨gs⟩`.

Its check `inputValidB` equals `InstanceData.validB q` at degree `|x|`
(`inputValidB_eq_validB`).

| Entry | Input checked | Theorems |
|---|---|---|
| `solveEntry` | nothing; strings decoded totally | `solveEntry_spec`, `solve_backend_refinement`, `solve_reference`: correct for the decoded strings under hypotheses on `w`, `σ`, `gs` |
| `solveChecked` (input `(q, …)`) | `InputValid q`, by the program `inputValidProg`, charged at most `validCost n m s` | `solveChecked_spec`, `solve_reference_checked`: on every input, `none` exactly when the contract fails, otherwise a correct answer; no hypotheses |

`validCost n m s = (m + 1)(3m + 9) + n (3m + 10) + s (14n + 4m + 16) + 24n + 4m + 54`, for window
size `m` and `s` generators. Repetitions in the window are found by comparing each point with
the later ones, and the mask by scanning the point list. The bound depends on `n` and the list
lengths only, so it also holds for invalid data. The alphabet bound `q` is checked; the
unit-cost word model does not use it. Bit-level costs come from the Turing-machine compilation
of milestones 17–18 (*On Turing machines* and *On a single tape* below), for well-formed
procedures over the empty signature; it bounds the bit lengths of intermediate values inside its
proof, so no separate bounded-word model is needed.

## Cost model (`GraphIso/Cost/`)

Programs are PHOAS terms `Prog S rec var t`; every constructor below is charged by the
evaluator, and none embeds a Lean function on runtime values. The type of closed programs
alone does not make them parametric (classical case analysis can inspect `var`); see
*Well-formedness* below for the witness that accepted programs carry.

| Construct | Charge |
|---|---|
| word and pointer primitives (`natLit`, `add`, `sub`, `natEq`, `natLt`, Boolean ops, `pair`, `fst`, `snd`, `none`, `some`, `nil`, `cons`) | 1 |
| `arraySize`, `arrayGet` (one indexed cell) | 1 |
| `append` (first list), `reverse`, `length` | length + 1 |
| `range k`, `arrayMk k v` | `k + 1` |
| `arrayOfList`, `arrayToList` | length + 1 |
| `arrayUpdate arr ws` (copy, then writes) | `|arr| + |ws| + 1` |
| `ite`, `caseOption`, `caseList` | 1 per branch taken |
| `foldList` | 1 per element, plus the body |
| `loop` | 1 per iteration, plus the body |
| `recur` | 1 per call, plus the callee |
| `call op x` | an `Event.call op x y` with the actual argument and result; charged `B.call op x y` by the schedule `B` |

Naturals are unit-cost words in this abstract semantics: the library's programs only
manipulate positions, symbols below the alphabet bound `q`, and counters bounded by data
lengths. Persistent array updates are not assumed constant-time; `arrayUpdate` copies.

**On Turing machines** (milestone 17, `GraphIso/TM/`). The compiler `comp` stores values in
cells of a heap, numbers in binary. `comp_sat` (`GraphIso/TM/Compile.lean`, whose docstring
lists its hypotheses: the primitives' specification `PrimSpec`, proved by `primCode_spec`; a
heap and a frame representing the context, within the bit bound `B` and the field bound `F`;
size constants `K`, `D` large enough for the program) relates a program at levels (`Lv`) to a
run of a program at `Ty.denote` related to it by `Prog.Wf true Γ`: the compiled code pushes a
pointer representing the run's value within `(psize + K · cost) · Q N` steps, `N` the final
heap's length. `main_exec` and `main_tm` (`GraphIso/TM/Main.lean`): for a well-formed procedure
`Pr` and entry `E` over the empty signature (`Prog.Wf true [⟨a', x₁, x₂⟩] (E Ty.denote x₁)
(E Lv x₂)` for all `x₁`, `x₂`) and every run of `E` on `x` to `v` with trace `tr`, the machine
`toFinTM2 (mainProg Pr E) .inp .out` outputs `ser c v` on input `ser a' x` within
`(κ (C + L + L' + 1))^120 + 1` steps (`TM2OutputsInTime`), where `C` is the local cost of
`tr`, `L` and `L'` the lengths of `ser a' x` and `ser c v`, and
`κ = 4096 (wt a' + wt c + K + D + |E| + 1)` depends only on the program. The output's length is
needed: values share cells, so a cost of about `m` can build an output of `m²` symbols, and no
bound of a degree independent of the program omits it (`PLAN-17.md` §10.3). The bit lengths of
intermediate values are bounded inside the proof by the local cost and the input's length (the
field and bit bounds `fB`, `bB`), so no separate bounded-word model is needed.

**On a single tape** (milestone 18, `GraphIso/TM/SingleTape/`). `compile_outputs`
(`Compile.lean`): for a `FinTM2` `tm` whose stack alphabets are finite, if
`TM2OutputsInTime tm x (some y) T`, the finite single-tape machine `compile tm hΓ` (mathlib's
`TM0`) outputs the framed tape `encodeOut y` on the framed tape `encodeIn x` within
`compileConst tm (|x| + T + 1)²` transitions, `compileConst tm = 4 (2 s² + 3 s + 6)` with `s` the
most stack actions of a statement; the input's preparation and the output's cleanup are counted.
With `gi_tm` and `gi_coset_tm` this gives `gi_tm0`, `gi_coset_tm0` (within
`2^{c (λ(L₀) + 1)⁸}` transitions, `L₀` the input tape's length) and `gi_tm0_vertices`,
`gi_coset_tm0_vertices` (within `2^{c (λ(n) + 1)⁸}`, `n` the number of vertices),
`GraphIso/TM/SingleTape/GI.lean`.

Evaluation (`eval`) is fuel-bounded: termination of the solver gives the existence of enough
fuel, not a public runner with a proved fuel bound. Case analysis in `eval` matches on the
scrutinee before evaluating a branch, so compiled runs perform only the work their trace
records; `GraphIsoChecks/Execution.lean` checks this by timing compiled runs at small and large
fuel. An earlier version passed both branches of `caseList` as arguments, and compiled code
then evaluated the untaken branch: the results and traces were unchanged, but on some
instances the running time grew with the fuel. The trace sums (`Trace.localCost`, `callCost`,
`cost`) are left folds, so compiled code sums long traces in constant stack space; as
`List.sum`s of the mapped trace they exhausted the interpreter's stack on a run with 1.8
million events, which `GraphIsoChecks/Execution.lean` now sums.

## Well-formedness (`GraphIso/Cost/WellFormed.lean`)

`Prog.Wf r Γ p₁ p₂` (Chlipala's PHOAS well-formedness) relates one program at two variable
instantiations: same constructors, primitives and operations; every variable occurrence is a
pair related by the context; binders extend the context with arbitrary fresh pairs. The flag
`r` allows `recur`.

- `Proc.Wf P`: related at every pair of instantiations, recursion allowed. Bundled as
  `WfProc`.
- `Impl.Wf impl`: for every client recursion type, related with recursion **forbidden**, so an
  implementation cannot call back into the client. Bundled as `WfImpl`.
- Preserved by substitution: `Prog.Wf.subst`, `Proc.Wf.subst`, `WfProc.subst`; plus weakening
  and `Prog.Wf.of_false`.
- The `prog_wf` tactic proves it for concrete programs; all library programs have
  well-formedness lemmas (`wf_mapList`, …, `wf_permBeq`).

What the witness rules out: because the relation holds for every pair of instantiations and
every choice of bound values, a choice made by inspecting runtime values can only select
between alternatives with the same constructors, primitives and operations, and between
variables holding equal values; so it cannot change results or charged costs (an informal
consequence of the formal invariant). `GraphIsoChecks/WellFormed.lean` checks that the review's
counterexamples are rejected: a procedure that applies an arbitrary `f` at zero cost by
classical case analysis on `var .nat = ℕ` (`hidden_not_wf`), and an executable implementation
that matches on the client's recursion type and calls `recur` (`sneaky_not_wf`). The compiler
of milestone 17 gives a first-order counterpart for the programs it compiles: `comp` translates
a program at levels (`Lv`) into stack-machine code, and `comp_sat` relates that code, through
`Prog.Wf true Γ`, to the program at `Ty.denote` that `eval` runs, with the result and a step
bound in its local cost (`main_exec`, `main_tm`: on Turing machines, see the cost model above).
A general correspondence between well-formed PHOAS terms and a first-order syntax is not
formalized.

`Trace.cost B tr = Trace.localCost tr + Σ_{e ∈ calls tr} B e` (`cost_eq_localCost_add_sum_calls`),
additive (`cost_append`) and monotone in `B` (`cost_mono`).

Validated permutation costs (`GraphIso/Programs/Perm.lean`), degree `n`:
apply `2`, inverse `3`, composition `12n + 13`, identity `2n + 3`, equality `6n + 10`.

## Backend signature and contracts (`GraphIso/GroupOps/Interface.lean`)

`groupSig D` lists the operations; `GroupPre DV` and `GroupPost DV` are the contract;
`MeetsContract DV O` says an oracle satisfies it. All postconditions are exact.

Size parameters (`callParams`): degree `n`, input generator count `s`, encoded size of the
backend data, window size `m`, `outCount` (number of output items: generators of an output
group, orbits, transversal pairs or coset representatives; `1` for `mem` and `lift`) and
`outSize` (encoded cells of the whole result, `Ty.size`). The two output measures differ: a
valid permutation of degree `n` occupies `2n + 2` cells (`Ty.size_perm_of_valid`), a generator
list `1 + s (2n + 2)` (`Ty.size_gens`), a group `2 + s (2n + 2) + |data|` (`Ty.size_group`), and
an orbit transversal with `k` pairs `1 + k (2n + 3)` (`Ty.size_transversal`).

| Operation | Precondition | Postcondition | Size parameters (`callParams`) |
|---|---|---|---|
| `generate (n, gs)` | generators valid | degree `n`, valid, same generated subgroup | `n`, `s`, output count and size |
| `mem (G, π)` | valid | `true ↔ π ∈ G` | `n`, `s`, data size |
| `orbits (G, w)` | valid, `w` `G`-invariant | `IsOrbitPartition`: exactly the orbits, covering `w` once | `n`, `s`, data, `m`, output |
| `stabilizer (G, u)` | valid, `u < n` | generates `{g ∈ G | g u = u}` | `n`, `s`, data, output |
| `orbitTransversal (G, u)` | valid, `u < n` | one `(v, r_v)` per orbit point, `r_v ∈ G`, `r_v u = v` | `n`, `s`, data, `outCount` = orbit length `k`, `outSize` = `1 + k (2n + 3)` |
| `cosetReps (G, K)` | valid, `K ≤ G` | `IsLeftTransversal G K` (output length `[G : K]`) | `n`, `s_G + s_K`, data, output |
| `kernel (G, w)` | valid, `w` invariant | generates the pointwise stabilizer of `w` | `n`, `s`, data, `m`, output |
| `lift (G, w, π')` | valid, invariant, `π'` in the restricted image | `r ∈ G` mapping `w[j] ↦ w[π' j]` | `n`, `s`, data, `m`, output |

Not provided, by design: string stabilizers, arbitrary setwise stabilizers, coset intersection.

## What the solver assumes of a backend (`GraphIso/Solver/Cost.lean`)

The solver calls four operations (`solverOps`): `generate`, `orbits`, `stabilizer` and
`orbitTransversal`. The generic theorems take:

- `MeetsContractOn DV solverOps O`: the exact contracts, on these four operations only;
- preconditions: every contract input of these operations is an allowed call in the context;
- `BackendBounds X DV n s G₀`: for groups of degree `n` with at most `s` generators that
  are subgroups of an ambient `G₀`, the charges of `orbits`, `stabilizer` and
  `orbitTransversal` are at most `Borb`, `Bstab` and `Btr`. The charge of `generate` on
  at most `n (s + 1)` valid generators is at most `Bgen`. Stabilizers and generated groups
  have at most `s` generators (`stabOut`, `genOut`).

The ambient group matters because a fixed per-call bound cannot hold for all subgroups of
`Perm (Fin n)` at once, while every group the solver meets is a subgroup of the input group.
The input `n (s + 1)` to `generate` is the branching reduction's reconstruction list: at most
`n` branches with `s` generators each, plus `n - 1` representative differences.

## The reference backend (`GraphIso/GroupOps/Enumeration*.lean`, `GraphIso/Solver/Reference.lean`)

Backend data `Ty.gens`: the list of all elements of the group (`refDV n gs el`: valid, without
repetition, exactly the elements of `⟨gs⟩`). Output groups are given by all their elements, both
as generators and as data, so `s = N₀`.

| Operation | Program | Charge in `refB` (group of order `N`, degree `n`) |
|---|---|---|
| `generate (n, gs)` | closure search from the identity under left multiplication by `gs` and their inverses, scanning for duplicates; `n!` iterations of fuel, at most `N + 1` used | `closureCost n N |gs| + 6` |
| `stabilizer (G, u)` | filter the elements fixing `u` | `7N + 10` |
| `orbitTransversal (G, u)` | one element per new image of `u` | `N (4n + 7) + 5` |
| `orbits (G, w)` | images of each unprocessed window point under all elements | `m (N (3n + 6) + 4n + 10) + 9` |
| `kernel (G, w)` | filter the elements fixing every window point | `N (5m + 5) + 11` |
| `lift (G, w, π')` | the first element restricting to `π'` (scan with `MapsWindowBy`) | `N (8m + 8) + 2m + 2n + 16` |
| `cosetReps (G, K)` | greedy: keep each element not in the left `K`-coset of a kept one (membership in `K` by scanning its element list) | `N (N (|K| (6n + 12) + 12n + 19) + 4) + 7` |

`mem` is not implemented (it returns a default; no reduction calls it, and the context forbids
it). `refImpl_implements` proves that the programs compute
`refOracle` within `refB` on every allowed call, and `refImpl_wf` that they are well-formed
without recursion. `refBounds` instantiates `BackendBounds` with these charges at `N = N₀`.

## The Schreier–Sims backend (`GraphIso/Sims/`, `GraphIso/Solver/Sims.lean`)

Backend data `Ty.unit`, with the trivially true invariant `ssDV`: every operation that needs a
stabilizer chain builds the complete Sims table it needs from the group's generators.

**Sims tables.** A base order lists all `n` points. The table has `n` rows of `n` slots, and
slot `(k, j)` holds an element fixing the first `k` base points and mapping `b_k` to `j`. The
construction `build` is a worklist with Knuth's closure criterion:

- each failed sift inserts its residue into an empty slot and queues the products that the
  criterion needs;
- termination counts filled slots, so no group order is used: at most `L + 2n⁴` steps.

Output groups are generated by table entries, at most `n²` of them, so `s = n²`.

| Operation | Algorithm | Charge in `ssB` (`L` generators, degree `n`, window `m`) |
|---|---|---|
| `generate (n, gs)` | table for the base `0, …, n − 1`; all entries | `genCost n L + 2 ≤ 100 (n+1)⁶ + 60 L (n+1)² + 2` |
| `stabilizer (G, u)` | table for a base starting with `u`; entries of rows `≥ 1` | `stabCost n L + 5` |
| `kernel (G, w)` | table for a base listing `w` first; entries of rows `≥ m` | `kerCost n L m + 5` |
| `lift (G, w, π')` | same table; one entry per window row, by the required image | `liftCost n L m + 7` |
| `mem (G, π)` | sift `π` in the table for the base `0, …, n − 1` | `memCost n L + 5` |
| `orbitTransversal (G, u)` | search from `u` on the generators, with a visited mask | `transCost n L + 5` |
| `orbits (G, w)` | one search per unseen window point | `orbitsCost n L m + 5` |
| `cosetReps (G, K)` | search over left cosets of `K` from the identity; a product is new unless sifting `r'⁻¹ g r` in `K`'s table succeeds | `repsCost n L L' R + 7`, `R = [G : K]` representatives |

Here `buildCost n L = O(n⁶ + L n²)` bounds the construction, and every charge above is an
explicit polynomial (`GraphIso/Sims/*Prog.lean`). `ssOracle_meets` proves the contracts of all
eight operations, `ssImpl_implements` that the programs compute the oracle within `ssB` on
every contract input, and `ssImpl_wf` that they are well-formed without recursion. `ssBounds`
instantiates `BackendBounds` with `s = n²` for every ambient group, with no dependence on its
order.

## What Luks's strategy assumes of a backend (`GraphIso/Luks/Strategy.lean`)

`luksBody` calls four operations (`luksOps`): `orbits`, `generate`, `kernel` and `cosetReps`.
It computes the maximal block system itself (`maxBlocksProg`, no backend calls) and the block
kernel by the induced action at degree `n + k` (`blockKernelProg`). The bounds it needs are
`LuksBounds X DV n s R G₀`, for groups inside an ambient group `G₀` given by at most `s`
generators:

- `Borb`: an `orbits` charge;
- `Bge`, `Bke`, `Bgt`: generating the extended group at degree `n + k`, its kernel on the
  block points, and generating the block kernel from the truncated kernel generators, for
  every block list the group permutes; `sKe` bounds the kernel's generator count, and the
  block kernel has at most `s` generators;
- `Bcr`: a `cosetReps` charge for a block kernel with at most `R` cosets;
- `Bgen`: a `generate` charge for at most `R (s + 1)` generators, and `genOut`: generated
  groups have at most `s` generators.

The cost theorem `luks_spec` adds `PrimBounded G₀ c` and `n ^ c ≤ R`. Then every block kernel
met has at most `k ^ c ≤ R` cosets, since their number is the order of a primitive image of
the group. `PrimBounded` is a property of the group alone, not of the backend: it is proved
for nilpotent groups (`c = 1`), for solvable groups whose order has at most `s + 1` prime
divisors (`c = 12 s + 1`, milestone 6) and for every group (`c = n`).

**The Schreier–Sims instance** `ssLuksBounds n R G₀` has `s = n²`, for every ambient group:

| Bound | Value |
|---|---|
| `Borb` | `orbitsCost n n² n + 5` |
| `Bge` | `genCost (2n) n² + 2` |
| `Bke` | `kerCost (2n) (4n²) n + 5` |
| `Bgt` | `genCost n (4n²) + 2` |
| `sKe` | `4n²` |
| `Bcr` | `repsCost n n² n² R + 7` |
| `Bgen` | `genCost n (R (n² + 1)) + 2` |

The per-invocation unit `luksSimsQ n R` is at most `3200 (n+1)⁶ + 50 R (n+1)⁴ + 13 R² (n+1)⁴`
(`luksSimsQ_le`), with `R = n ^ c`.

## Proved versus assumed

- `runs_subst` / `Proc.runs_subst` / `WfProc.runs_subst`: if an implementation
  `impl : Impl (groupSig D) S'` meets `Implements O B Pre impl O' B'`, substituting it
  preserves results and gives `cost ≤ localCost + Σ B(e)`. Each call is charged through its
  implementation or its bound, never both. Accepted implementations are additionally
  `Impl.Wf`, which forbids calls into the client; the substitution theorem itself does not rely
  on that, since `Implements` quantifies over every client body.
- The generic solver theorems (`solve_correct`, …, `solve_cost_le`, `solveEntry_spec`,
  `solve_backend_refinement`) are stated for an arbitrary oracle with
  `MeetsContractOn DV solverOps O`, an arbitrary schedule and `BackendBounds`: these are the
  explicit hypotheses for future efficient backends.
- The concrete theorem `solve_reference` discharges all of them for the reference backend
  (`refOracle_meets`, `refImpl_implements`, `refBounds`). It states correctness and the cost
  of the closed substituted program over the empty signature; no contract is assumed there.
  `solve_reference_checked` does the same for the validating entry, with no hypotheses on the
  input.
- Output generator counts are not bounded by the contracts; `BackendBounds` requires them
  (`stabOut`, `genOut`), and the reference backend supplies them through the group order.
- `kernel`, `lift` and `cosetReps` are used by the phase-5 reductions. The block kernel is not
  a backend operation: `blockKernelProg` obtains it from `generate` and `kernel` through the
  induced action on the blocks, at degree `n + k`. `mem` is unused.
- The reductions are stated, like the solver, for an arbitrary contract-meeting oracle with
  their charges as hypotheses (`RunsWithin.restrictProg`, `RunsWithin.blockReduceProg`). They
  are also composed with the solver as their sub-solver (`restrict_solve_spec`,
  `blockReduce_solve_spec`). The restriction's sub-call runs at the window's degree `m`, so it
  takes `BackendBounds` at degree `m` for the restricted group.
- `restrict_reference` and `blockReduce_reference` discharge every one of these hypotheses
  for the reference backend, as `solve_reference` does for the solver. Their programs are
  closed and run inside `referenceSolver`.
- `solve_sims`, `solve_sims_checked`, `restrict_sims` and `blockReduce_sims` discharge the
  same hypotheses for the Schreier–Sims backend, with charges polynomial in the degree.
  `simsCost_le` puts the solver's bound in closed form. The group order enters only through
  the default strategy's `solveBound`, which stays linear in `N`.
- The graph-isomorphism algorithm (`GraphIso/Graph/`, milestone 4) uses the backend only
  through `solveEntry` inside `luksBody`, once per layer step. It is proved against the
  Schreier–Sims context directly (`RunsWithin.stepProg` uses `luksEntry_spec` with
  `ssLuksBounds`), and `gi3_checked` substitutes the implementations as `solve_luks` does. Each
  layer's group is the image of a `2`-group, so the nilpotent bound applies
  (`luksSimsCost_one_le`).
- The algorithm for all graphs of maximum degree three (`Graph/All.lean`, milestone 5) uses the
  backend only through milestone 4's `mainProg`, at most once per candidate pair of components
  of equal size: the search for a partner stops at the first one found
  (`RunsWithin.partnerStepProg`). `gi3_all_checked` substitutes the implementations in the same
  way.
- `efficient-backends.md` lists what remains beyond a polynomial backend.
