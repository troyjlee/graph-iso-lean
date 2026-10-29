# Theorem map

Status of the milestone targets in `PLAN.md` (milestone 1, phases 0–7) and in `PLAN-2.md` to
`PLAN-19.md` (milestones 2–18 done; milestone 19 in progress). The sections run in order up to
milestone 14's stage 14j-5b; from stage 14j-5c on, the newest stage comes first (milestone 19's
stage 19d down to 14j-5c). The endpoints: graph isomorphism in quasipolynomial time with no
hypothesis (`giSolve_final`, `gi_simpleGraph_final`, milestone 16); on Turing machines with
stacks (`gi_tm`, `gi_coset_tm`, milestone 17, in the input's length; `gi_tm_vertices`,
`gi_coset_tm_vertices`, stage 18a, in the number of vertices); and on single-tape machines
(`gi_tm0_vertices`, `gi_coset_tm0_vertices`, in the number of vertices, and `gi_tm0`,
`gi_coset_tm0`, in the input tape's length, stage 18f). The single-tape theorems in the number of
vertices are also stated with definitions that use Mathlib only, for the Palomar registry
(`GraphIsoPalomar.gi_singleTape_proof`, stage 19c; `gi_coset_singleTape_proof` and
`cosetWord_injective_proof`, stage 19d).
All listed theorems are in namespace `GraphIso` (cost-language results in `GraphIso.Cost`,
programs in `GraphIso.Programs`, the solver in `GraphIso.Solver`, the reference backend in
`GraphIso.Enum` and `GraphIso.Reference`, the Schreier–Sims backend in `GraphIso.Sims`, Luks's
strategy in `GraphIso.Luks`, graph isomorphism of bounded valence in `GraphIso.Graph`, group
theory in `GraphIso.Groups`; Babai's algorithm in `GraphIso.Coherent`, `GraphIso.SplitJohnson`,
`GraphIso.AltQuot`, `GraphIso.Certificates`, `GraphIso.Recursion`, `GraphIso.Main` and the
namespaces of milestone 14's stages, Pyber's bound in `GraphIso.Pyber`, the transitivity bound
and the unconditional theorems in `GraphIso.Wielandt`, Turing machines in `GraphIso.TM`), except
the Palomar statement's (`GraphIsoPalomar`) and the checks' (`GraphIsoChecks`). All build with
`--wfail` and pass the axiom audit.

## Phase 0 — project and conventions (done)

| Item | Location |
|---|---|
| Pinned toolchain and mathlib, clean `--wfail` build | `lean-toolchain`, `lakefile.toml`, `lake-manifest.json` |
| `g * h` versus `h * g`, relabel convention (kernel `decide` and `#guard`) | `GraphIsoChecks/Conventions.lean` |
| Mathlib signature checks (cosets, closure, orbits, blocks, Schreier, TM time) | `GraphIsoChecks/MathlibAPI.lean` |
| Axiom and import-closure audit | `GraphIsoChecks/AxiomAudit.lean` |

## Phase 1 — semantics (done)

| Statement | Name | File |
|---|---|---|
| `Matches univ g x y ↔ relabel g x = y` (and `↔ g • x = y` for `arrowAction`) | `matches_univ_iff`, `matches_univ_iff_smul` | `Semantics/Action.lean` |
| Finite window: invariance under `closure S` iff under generators | `isInvariant_closure_iff` | `Semantics/Window.lean` |
| Pointwise fixing checked on generators | `fixesPointwise_closure_iff` | `Semantics/Window.lean` |
| `Aut_W(G,x)` is a subgroup (uses invariance) | `aut`, `mem_aut`, `aut_le` | `Semantics/StringIso.lean` |
| **Solution-coset theorem** `τ ∈ iso → iso = τ • aut` | `iso_eq_smul_aut` | `Semantics/StringIso.lean` |
| Empty or a single coset | `iso_eq_empty_or_eq_smul_aut` | `Semantics/StringIso.lean` |
| A solution coset determines its subgroup | `eq_aut_of_iso_eq_smul` | `Semantics/StringIso.lean` |
| **Normalization** `iso W σ G x y = σ • iso W 1 G x (y ∘ σ)` | `iso_eq_smul_iso_one`, `iso_mul_left` | `Semantics/StringIso.lean` |
| Empty window, empty domain | `iso_empty_window`, `iso_of_isEmpty` | `Semantics/StringIso.lean` |
| **Sequential windows** | `iso_union_of_eq_smul`, `iso_union_of_eq_empty`, `iso_union_eq_iso_aut` | `Semantics/StringIso.lean` |
| Pointwise-fixing group: whole coset or empty | `iso_of_fixesPointwise_of_matches`, `iso_of_fixesPointwise_of_not_matches` | `Semantics/StringIso.lean` |
| **Branching** along a left cover of `G` by cosets of `K ≤ G` | `iso_eq_iUnion_of_isLeftCover` | `Semantics/StringIso.lean` |
| **Reconstruction** `aut = ⟨⋃ Hᵢ ∪ {τ₀⁻¹τᵢ}⟩` | `aut_eq_closure_of_iso_eq_iUnion`, `iso_eq_smul_closure_of_iso_eq_iUnion` | `Semantics/StringIso.lean` |
| Group-theoretic reconstruction lemma | `eq_closure_of_leftCoset_eq_iUnion` | `Semantics/Coset.lean` |
| Semantic answers | `Answer.denote`, `Answer.IsCorrect`, `.eq_none_iff`, `.of_some` | `Semantics/StringIso.lean` |

## Phase 2 — representations and contracts (done)

| Statement | Name | File |
|---|---|---|
| Validity checks decide validity | `PermData.validB_iff`, `WinData.validB_iff`, `StrData.validB_iff`, `GensData.allValidB_iff`, `InstanceData.validB_iff` | `Representation/*` |
| Permutation operations agree with interpretation | `PermData.denote_mul`, `denote_inv`, `denote_one`, `beq_iff`, `denote_ofPerm`, `denote_injOn` | `Representation/Permutation.lean` |
| Generator-only checks decide invariance and pointwise fixing | `GensData.invariantB_iff`, `GensData.fixesB_iff` | `Representation/Group.lean` |
| Window matching and normalized target | `matchesB_iff`, `StrData.denote_comp` | `Representation/Encoding.lean` |
| Decoded instance satisfies the input invariant | `InstanceData.Valid.isInvariant` | `Representation/Encoding.lean` |
| Backend signature, exact contracts, size parameters | `groupSig`, `GroupPre`, `GroupPost`, `MeetsContract`, `callParams`, `CostSchedule.ofParams` | `GroupOps/Interface.lean` |

## Phase 3 — cost semantics and backend substitution (done)

| Statement | Name | File |
|---|---|---|
| Closed PHOAS program language with charged primitives | `Ty`, `Prim`, `Prim.cost`, `Prog`, `Proc` | `Cost/Program.lean` |
| Evaluation returns result and trace of charged events; case analysis evaluates only the branch taken (checked in `GraphIsoChecks/Execution.lean`) | `eval`, `Runs`, `runs_*` | `Cost/Evaluation.lean` |
| Fuel monotonicity, determinism | `eval_mono`, `Runs.unique` | `Cost/Evaluation.lean` |
| `cost_B = localCost + Σ B(e)`; additivity; monotonicity in `B`; the left-fold sums as sums | `Trace.cost_eq_localCost_add_sum_calls`, `Trace.cost_append`, `Trace.cost_mono`, `Trace.localCost_eq_sum`, `Trace.cost_eq_sum` | `Cost/Evaluation.lean` |
| **Backend substitution** | `runs_subst`, `Runs.subst`, `Proc.runs_subst`, `WfProc.runs_subst` | `Cost/BackendRefinement.lean`, `Cost/WellFormed.lean` |
| Relational well-formedness; recursion forbidden in implementations | `Prog.Wf`, `Proc.Wf`, `Impl.Wf`, `WfProc`, `WfImpl`, `Prog.Wf.not_recur` | `Cost/WellFormed.lean` |
| Weakening, preservation under substitution | `Prog.Wf.weaken`, `Prog.Wf.of_false`, `Prog.Wf.subst`, `Proc.Wf.subst`, `WfProc.subst` | `Cost/WellFormed.lean` |
| Library programs well-formed | `wf_mapList`, `wf_mapArray`, `wf_allList`, `wf_permApply`, `wf_permInv`, `wf_permMul`, `wf_permOne`, `wf_arrayNatBeq`, `wf_permBeq` | `Programs/*` |
| Encoded sizes of results | `Ty.size_perm_of_valid`, `Ty.size_gens`, `Ty.size_group`, `Ty.size_transversal` | `GroupOps/Interface.lean` |
| Compositional cost specifications | `RunsWithin` and its lemmas | `Cost/Spec.lean` |
| Map/all combinators with costs | `RunsWithin.mapList`, `mapArray`, `allList` | `Programs/List.lean` |
| Permutation program costs validated | `RunsWithin.permApply`, `permInv`, `permMul`, `permOne`, `permBeq` | `Programs/Perm.lean` |

Regression checks (`GraphIsoChecks/Cost.lean`): validity of concrete data, concrete program
runs with their actual costs, and a toy backend charged by contract (20) versus by
implementation (4) through `Proc.runs_subst`. `GraphIsoChecks/WellFormed.lean`: the review's
counterexamples are rejected (`hidden_not_wf`, `sneaky_not_wf`) although the first runs at
zero cost as a raw `Proc` (`hidden_runs_uncharged`); example procedures, implementations and
a recursive procedure are well-formed; transversal cell counts.

## Phase 4 — sequential windows and branching (done)

Semantic layer:

| Statement | Name | File |
|---|---|---|
| Answer-level sequential composition | `Answer.IsCorrect.union_none`, `.union_some`, `.isInvariant_of_some` | `Reductions/Sequential.lean` |
| Branch answers combine to a correct answer (nonnormal `K` allowed) | `Answer.IsCorrect.combineBranches` | `Reductions/Subgroup.lean` |
| Represented reconstruction generators, `s_out = Σ sᵢ + k - 1` | `branchGens`, `length_branchGens`, `denote_branchGens` | `Reductions/Subgroup.lean` |

Programs (the sub-solver is a parameter; the solver will pass its own `recur`):

| Statement | Name | File |
|---|---|---|
| Represented instances and answers; correctness of represented answers | `InstData`, `AnswerData`, `AnsOK`, `AnsOK.union_some`, `SubSolves` | `Reductions/Data.lean` |
| Window materialization, cost `2n + 5m + 7` | `mkWindow`, `RunsWithin.mkWindow`, `WinData.valid_ofPoints` | `Programs/Window.lean` |
| **Sequential reduction**: correct for the union, cost `1 + Σ (C o + 2n + 5|o| + 13)` | `seqProg`, `RunsWithin.seqProg`, `wf_seqProg` | `Reductions/SequentialProg.lean` |
| Exact orbit partitions supply the sequential hypotheses | `seqInputs_of_isOrbitPartition` | `Reductions/SequentialProg.lean` |
| Branch combination: exact value, cost `combineCost`, `generate` charged on its actual argument | `combineProg`, `RunsWithin.combineProg`, `combineModel`, `combineCost_le`, `length_combineGens` | `Reductions/SubgroupProg.lean` |
| Represented branch combination is correct | `AnsOK.combineModel` | `Reductions/SubgroupProg.lean` |
| **Branching reduction**: correct for `σ • G`, cost `|R| (24n + C + s + 45) + B_gen + 19`, output generators bounded by the backend's `generate` bound | `branchProg`, `RunsWithin.branchProg`, `wf_branchProg` | `Reductions/SubgroupProg.lean` |
| `orbitTransversal` output is a left transversal by cosets of the point stabilizer | `isLeftTransversal_of_orbitTransversal` | `Reductions/SubgroupProg.lean` |

Regression checks (`GraphIsoChecks/Reductions.lean`): the `S₃` branch answers combined by the
program (representative `c`, generator `(0 1)`, cost 85 against the bound 91); sequential
bookkeeping at exactly its bound (60); procedures using both reductions with `recur` as the
sub-solver are well-formed.

## Phase 5 — restriction, lifting and block systems (done)

Restriction to an invariant window, in `GraphIso.Reductions` and `GraphIso.Programs`:

| Statement | Name | File |
|---|---|---|
| Action on an invariant window, transported along a reindexing `e : α ≃ W` | `restrictHom`, `restrictHom_apply`, `restrictHom_eq_iff` | `Reductions/Restriction.lean` |
| **Kernel of the restriction** is the pointwise stabilizer | `restrictHom_eq_one_iff`, `map_ker_restrictHom` | `Reductions/Restriction.lean` |
| Matching on `W` is matching of the restriction on the whole reindexed domain | `matches_restrict`, `mem_iso_one_iff_restrict` | `Reductions/Restriction.lean` |
| **Lifting**: restricted answer `τ' • H'`, lift `τ`, lifts `L` of generators ⇒ `iso W σ G x y = (σ τ) • (⟨L⟩ ⊔ K)` | `iso_one_eq_of_restrict`, `iso_eq_of_restrict`, `iso_eq_empty_of_restrict` | `Reductions/Restriction.lean` |
| The kernel lies in every automorphism subgroup, so it cannot be dropped | `pointwiseStab_le_aut` | `Reductions/Restriction.lean` |
| Represented reindexing (list order), positions, restricted permutations, strings and generators | `WinData.reindex`, `WinData.pos`, `get_pos`, `PermData.restrictTo`, `denote_restrictTo`, `GensData.denote_restrictTo`, `StrData.restrictTo` | `Reductions/RestrictionData.lean` |
| The `lift` postcondition says exactly that `r` restricts to `π'` | `mapsWindowBy_iff`, `exists_lift` | `Reductions/RestrictionData.lean`, `Reductions/RestrictionProg.lean` |
| Represented answer lifting | `AnsOK.lift_restrict`, `AnsOK.restrict_none` | `Reductions/RestrictionProg.lean` |
| **Restriction reduction**: one sub-call at degree `m`; lifts, kernel and `generate` at degree `n`; cost `restrictCost` | `restrictProg`, `restrictInst`, `RunsWithin.restrictProg`, `restrictCost`, `liftCost`, `wf_restrictProg` | `Reductions/RestrictionProg.lean` |

Block systems:

| Statement | Name | File |
|---|---|---|
| Block lists, permuting blocks, the block kernel (a subgroup) | `IsBlockList`, `PermutesBlocks`, `blockKernel`, `blockKernel_le` | `Reductions/Blocks.lean` |
| Blocks are invariant under the block kernel and cover the window | `seqInputs_of_blocks` | `Reductions/Blocks.lean` |
| **Block reduction**: branch over `G / K` (`cosetReps`), process the blocks in each branch; `|R| · |K| = |G|` | `blockProg`, `RunsWithin.blockProg`, `blockBranchCost`, `isLeftCover_map`, `wf_blockProg` | `Reductions/BlocksProg.lean` |
| **Induced action on blocks** at degree `n + k`, injective; its kernel on the block points is the extension of the block kernel; truncation recovers it | `blockMap`, `blockHom`, `extendPerm`, `extendHom`, `extendHom_injective`, `extendTo_eq`, `mem_pointwiseStab_extend`, `truncTo_extendHom`, `denote_truncTo` | `Reductions/BlockAction.lean` |
| **Block kernel by the induced action**, using `generate` and `kernel` only | `blockKernelProg`, `RunsWithin.blockKernelProg`, `blockKernelCost`, `wf_blockKernelProg` | `Reductions/BlockKernelProg.lean` |
| **Block-system reduction with its kernel**, number of branches `[G : K]` | `blockReduceProg`, `RunsWithin.blockReduceProg`, `wf_blockReduceProg` | `Reductions/BlockKernelProg.lean` |

Reference implementations (`GraphIso.Enum`, `GraphIso.Reference`): `kernel` by filtering
(`kerElems_spec`, `kerProg`), `lift` by search (`liftModel_spec`, `liftProg`), and `cosetReps`
by a greedy search (`repsModel_spec`, `repsProg`). `refOracle_meets_refOps` covers every
operation but `mem`, and `refImpl_implements` covers every one of them.

Regression checks (`GraphIsoChecks/Restriction.lean`), each run evaluated by the kernel:
- **Restriction** of `⟨(0 1), (2 3)⟩` to `{0, 1}`, a non-faithful action: the answer contains the
  kernel element `(2 3)` and lists both solutions, by brute force over `Perm (Fin 4)`.
- **Block kernel** of the dihedral group of order 8 for blocks `{0, 1}, {2, 3}`, computed at
  degree 6: it is `{1, (0 1), (2 3), (0 1)(2 3)}`, checked against brute force.
- **Block reduction** on two branches: its answer coset equals the brute-force solution set.


## Phase 6 — the recursive solver and the reference backend (done)

The solver against an abstract backend (`GraphIso.Solver`):

| Statement | Name | File |
|---|---|---|
| Local checks: pointwise fixing on generators (cost `s (5m + 3) + 1`), matching on a window (`7m + 3`) | `fixesProg`, `matchesProg`, `RunsWithin.fixesProg`, `RunsWithin.matchesProg` | `Programs/Checks.lean` |
| **The recursive solver**: empty window, pointwise-fixed window, several orbits (`seqProg`), transitive window (`branchProg` over the point stabilizer); well-formed | `solveBody`, `solveBody_wf` | `Solver/Basic.lean` |
| Orbit–stabilizer count from a left transversal; orbit-partition facts used for termination | `IsLeftTransversal.card_eq`, `IsOrbitPartition.length_lt`, `.length_sum`, `.transitive_of_singleton`, `length_orbitTransversal` | `Solver/Facts.lean` |
| Backend charge and output-size hypotheses, relative to an ambient group `G₀` | `solverOps`, `BackendBounds` | `Solver/Cost.lean` |
| Cost bound `solveBound Q m N = 2mNQ - Q` (`Q` if `m = 0`) with `Q = nodeCost + 2 edgeCost`, and the arithmetic of both recursive steps | `nodeCost`, `edgeCost`, `solveQ`, `solveBound`, `branch_arith`, `seq_arith` | `Solver/Cost.lean` |
| **Termination, correctness and cost together**, by strong induction on `|W|` and then on `|G|` | `SolveSpec`, `solve_spec` | `Solver/Correctness.lean` |
| **`solve_correct`**: the answer denotes `iso W σ G x y` | `solve_correct` | `Solver/Main.lean` |
| **`solve_none_iff`** | `solve_none_iff` | `Solver/Main.lean` |
| **`solve_some_group`**: representative is a solution, generators generate `aut` | `solve_some_group` | `Solver/Main.lean` |
| **`solve_cost_le`**: `cost_B ≤ solveBound …`, every call charged on its actual argument and result | `solve_cost_le` | `Solver/Main.lean` |
| Run exists; calls satisfy preconditions; valid output data | `solve_exists`, `solve_calls_ok`, `solve_answer_valid` | `Solver/Main.lean` |
| Public entry: `generate`, then solve; cost `11 + B(generate) + solveBound …` | `solveEntry`, `solveEntry_wf`, `solveEntry_spec` | `Solver/Entry.lean` |
| **`solve_backend_refinement`**: substituting well-formed implementations that compute a contract-meeting backend within its schedule preserves correctness and the generic bound | `solve_backend_refinement` | `Solver/Entry.lean` |
| Validation programs computing the representation checks, costs in `n`, `m`, `s` | `strValidProg`, `permValidProg`, `gensValidProg`, `winValidProg`, `invariantProg`, `RunsWithin.*` | `Programs/Validate.lean` |
| The input contract, its check (`= InstanceData.validB`) and program, cost `validCost` | `InputValid`, `inputValidB`, `inputValidB_iff`, `inputValidB_eq_validB`, `inputValidProg`, `validCost` | `Solver/Checked.lean` |
| **Validating entry**: `none` exactly on inputs violating the contract, otherwise a correct answer; no input hypotheses | `solveChecked`, `solveChecked_wf`, `solveChecked_spec` | `Solver/Checked.lean` |

The reference backend (`GraphIso.Enum`, `GraphIso.Reference`): groups are given by all
their elements.

| Statement | Name | File |
|---|---|---|
| Closure search with scan-based duplicate detection is exact and lists `|⟨gs⟩|` elements | `enumerate`, `enumerate_spec`, `refDV` | `GroupOps/Enumeration.lean` |
| Functional models of stabilizer, orbit transversal and orbits, exact | `stabElems_spec`, `transModel_spec`, `orbitsModel_spec` | `GroupOps/Enumeration.lean` |
| The reference oracle meets the exact contracts of the solver's operations | `refOracle`, `refOracle_meets` | `GroupOps/Enumeration.lean` |
| Programs computing the models, with costs in `n`, `N`, `L`, `m` | `closureProg`, `stabProg`, `transProg`, `orbitsProg`, `RunsWithin.closureProg`, `.stabProg`, `.transProg`, `.orbitsProg`, `closureCost` | `GroupOps/EnumerationProg.lean` |
| Implementations over the empty signature: well-formed, and computing `refOracle` within `refB` | `refImpl`, `refImpl_wf`, `refImpl_implements` | `Solver/Reference.lean` |
| Backend bounds for subgroups of a group of order `≤ N₀`, with `s = N₀` | `refBounds` | `Solver/Reference.lean` |
| **`solve_reference_correct_and_cost`**: the closed substituted solver returns a correct answer at local cost `≤ referenceCost n N |gs| |W|`, with no oracle assumed | `referenceSolver`, `referenceCost`, `solve_reference` | `Solver/Reference.lean` |
| The same for the validating entry, on every input, at cost `≤ validCost + 4 + referenceCost` | `solve_reference_checked` | `Solver/Reference.lean` |

Regression checks (`GraphIsoChecks/Reference.lean`): six runs of `referenceSolver`, each
evaluated by the kernel, cover `S₃` with two solutions, with no solution and with a unique
solution; the coset `(0 1) • C₃`; the window `{0, 1}` with the unmatched point `2`; and the
empty window. Each run has its exact answer and charged cost, for example 8689 for `S₃` with
two solutions. Each is tied to `solve_reference` with its hypotheses decided, and each answer
coset, enumerated, equals the brute-force solution set over `Perm (Fin 3)`. The proved bound
is loose: `referenceCost 3 6 2 3 = 2506915`.

The validating entry rejects strings shorter or longer than the degree (which the unchecked
entry decodes totally), a symbol at the alphabet bound and a non-invariant window. On the
valid window instance it returns the unchecked answer at the unchecked cost plus 274. Each
run is tied to `solve_reference_checked` (`runChecked_spec`).

`GraphIsoChecks/Execution.lean` times compiled runs at small and large fuel. Two synthetic
procedures would take time exponential in the fuel if `eval` evaluated the untaken
`caseList` or `caseOption` branch. The third run is the reference solver on an instance where
the eager `caseList` re-solved the unchanged problem. A last run sums the 1.8 million trace
events of the block reduction for `S₄` on the empty window, which exhausted the interpreter's
stack when the trace sums were `List.sum`s rather than left folds.

## Phase 7 — integration and final audit (done)

The phase-5 reductions composed with the solver (`GraphIso.Solver`), against any backend
meeting the contracts of the operations involved:

| Statement | Name | File |
|---|---|---|
| **The solver as a sub-solver**: a recursive call solves every valid instance of degree `n` in `G₀` with at most `s` generators within `1 + solveBound Q m N` | `SubSolves.solve` | `Solver/Compose.lean` |
| The restricted group is a quotient of `G`, so its order is at most `|G|` | `card_restrictTo_le` | `Solver/Compose.lean` |
| **Restriction with the solver as sub-solver**: the sub-call runs at degree `m`, against `BackendBounds` at degree `m` for the restricted group; cost `restrictCost` with `C = 1 + solveBound Q m |G|` | `restrictSolveOps`, `restrict_solve_spec` | `Solver/Compose.lean` |
| **Block reduction with the solver as sub-solver**: one call per block in each of the `R` cosets, `R · |K| = |G|` | `blockSolveOps`, `blockReduce_solve_spec` | `Solver/Compose.lean` |

With the reference backend (`GraphIso.Reference`), as closed programs over the empty
signature inside `referenceSolver`, with no assumed oracle. The instance carries the group's
element list `enumerate n gs` as backend data, which the reduction programs take as input. The
bounds start from that data. Computing it is not included; the reference `generate` charges at
most `closureCost n N |gs| + 6` for it (`refB_generate_le`).

| Statement | Name | File |
|---|---|---|
| **Restriction**: correct answer, local cost `≤ restrictReferenceCost n m N |gs|` | `restrict_reference`, `restrictReferenceCost`, `refQ` | `Solver/ReferenceCompose.lean` |
| **Block reduction** with `k` blocks: correct answer, local cost `≤ blockReferenceCost n m k N |gs| (N / |K|)` | `blockReduce_reference`, `blockReferenceCost`, `blockBranchCost_le` | `Solver/ReferenceCompose.lean` |

Concrete instantiations, evaluated by the kernel:

- **The phase-5 runs.** `runRestrict_spec` and `runBlocks_spec` (`GraphIsoChecks/Restriction.lean`)
  tie them to these theorems with their hypotheses decided, as `runRef_spec` does for the
  solver. That `G` permutes the blocks is checked on the elements of `G`.
  - The restriction run costs 3283 against the bound 245677.
  - The block run costs 26133 against the bound 30233029. The block kernel's order 4 is
    counted over `Perm (Fin 4)`.
- **The remaining cases of the verification list** (`GraphIsoChecks/Coverage.lean`), as runs
  of the reference solver, each tied to `solve_reference` and compared with brute force:
  - the trivial group, with a match and an impossible match;
  - a singleton domain;
  - constant strings, where all of `S₃` solves;
  - linked orbits under `⟨(0 1)(2 3)⟩`, with and without a solution;
  - the dihedral group of order 8 solved directly, whose coset equals the block reduction's.

Comparisons over families (`GraphIsoChecks/Sweep.lean`), run in the interpreter. The reference
solver, the restriction reduction and the block reduction are each compared with brute force on
image lists, which uses none of the library's group code. Each run checks:

- valid answer data, whose group data lists exactly its group;
- the denoted set equals the solution set;
- the cost is within the proved bound.

| Program | Instances | Runs |
|---|---|---|
| Solver | the subgroups of `S₁`, `S₂`, `S₃` up to conjugacy, plus `⟨(0 2)⟩`; all invariant windows, all representatives, all binary string pairs | 7880 |
| Solver | degree 3, strings with three distinct symbols | 4320 |
| Solver | ten groups of degree 4 (including `D₄`, `A₄`, `S₄`), all invariant windows, two representatives, 16 string pairs | 1472 |
| Restriction | as the first row, nonempty windows | 5892 |
| Restriction | degree 4, identity representative | 576 |
| Block reduction | every block system of every window, degrees ≤ 3 | 4744 |
| Block reduction | degree 4, two string pairs | 242 |

The harness was checked to report a disagreement, on swapped strings and on an impossible
cost bound.

### PLAN's final targets

| Target in `PLAN.md` | Lean |
|---|---|
| `solve_correct` | `GraphIso.Solver.solve_correct` |
| `solve_none_iff` | `GraphIso.Solver.solve_none_iff` |
| `solve_some_group` | `GraphIso.Solver.solve_some_group` |
| `solve_cost_le` | `GraphIso.Solver.solve_cost_le` |
| `solve_backend_refinement` | `GraphIso.Solver.solve_backend_refinement` |
| `solve_reference_correct_and_cost` | `GraphIso.Reference.solve_reference`, and `solve_reference_checked` for the validating entry |

### Hypotheses of the principal theorems

Unlisted hypotheses are notation: degrees, generators, data, the run itself.

| Theorem | Backend hypotheses | Input hypotheses |
|---|---|---|
| `solve_correct`, `solve_none_iff`, `solve_some_group`, `solve_cost_le` | `MeetsContractOn DV solverOps X.O`; those calls allowed by `X.Pre`; `BackendBounds X DV n s G₀` | valid instance (window, representative, group data `GroupValid DV`, invariant window); at most `s` generators; `⟨gs⟩ ≤ G₀` |
| `solveEntry_spec` | as above, with `G₀ = ⟨gs⟩` | valid window, representative and generators; invariant window |
| `solve_backend_refinement` | as above, plus well-formed implementations with `Implements` for the context | as above |
| `solveChecked_spec` | as above | none: invalid input gives `none` |
| `solve_reference` | none | valid window, representative and generators; invariant window |
| `solve_reference_checked` | none | none |
| `RunsWithin.restrictProg` | contracts of `generate`, `lift`, `kernel`; their charges; a sub-solver for the restricted instance | valid instance |
| `restrict_solve_spec` | contracts of the solver's operations and of `lift`, `kernel`; `BackendBounds` at degree `m` for the restricted group; charges of the reduction's own calls | valid instance |
| `restrict_reference` | none | valid window, representative and generators; invariant window; group data `enumerate n gs`, not charged |
| `RunsWithin.blockReduceProg` | contracts of `generate`, `kernel`, `cosetReps`; their charges; a sub-solver for the blocks | as below |
| `blockReduce_solve_spec` | contracts of the solver's operations and of `kernel`, `cosetReps`; `BackendBounds` at degree `n` for `G`; at most `s` block-kernel generators; charges | valid window, representative, group data; invariant window; `IsBlockList w bs`; `PermutesBlocks G bs` |
| `blockReduce_reference` | none | as above, with the group given by generators and group data `enumerate n gs`, not charged |

In every theorem, strings are read by total decoding (`StrData.denote`): an entry with a
missing position reads `0`. Only the validating entry checks string lengths and the alphabet.

### Final audit

`GraphIsoChecks/AxiomAudit.lean` checks every project declaration and the import closure. It
also lists the axioms of the principal theorems by name in the build output. Each of these
depends only on `propext`, `Classical.choice` and `Quot.sound`:

- `iso_eq_smul_aut`;
- the six final targets;
- `solveEntry_spec` and `solveChecked_spec`;
- `refImpl_implements`;
- `iso_eq_of_restrict`;
- the two reductions and their compositions and reference instantiations.

The executable path is checked by running it. The concrete theorems are about closed
programs over the empty signature (`referenceSolver`, the reductions with `refImpl`
substituted). These programs are evaluated by the kernel in the checks and by the interpreter
in the sweep, so their output is computed, not chosen classically. The remaining
efficient-backend work is listed in `efficient-backends.md`.

## Milestone 2 — the Schreier–Sims backend (`PLAN-2.md`, done)

A backend with no stored data (`D = Ty.unit`) that meets every contract, with charges
polynomial in the degree `n`, the generator counts and, for `cosetReps`, the number of
representatives. Every module is under `GraphIso/Sims/`, except the wiring in
`GraphIso/Solver/Sims.lean` and `SimsCompose.lean`.

### Phase 1 — Sims tables (`Sims/Basic.lean`, `Sims/Table.lean`)

| Statement | Name |
|---|---|
| Base orders list all `n` points; a permutation fixing every base point is `1` | `BaseOrder`, `BaseOrder.eq_one` |
| The slot conditions relative to `G` | `TableWF` |
| `Γ_k = T_k ⋯ T_{n−1}`, by one entry per row | `InGamma` |
| The row-`k` factor of `x ∈ Γ_k` is the entry in slot `(k, x b_k)` | `inGamma_iff` |
| **Sifting decides `Γ_k`**, with no group structure assumed | `sift_eq_iff`, `siftResult` |
| **The closure criterion**: `τ σ ∈ Γ_k` for the entries `σ` of row `k` and `τ` of rows `≥ k` makes every `Γ_k` closed under multiplication | `Closed`, `InGamma.mul` |
| Then `Γ_k` is the subgroup generated by the entries of rows `≥ k` | `mem_closure_entries_iff` |
| **Completeness**: with the generators of `G` in `Γ₀`, `Γ_k` is the pointwise stabilizer of `b₀, …, b_{k−1}` | `complete_of_closed`, `Complete` |
| Slot `(k, p)` is filled exactly when `p` is in the orbit of `b_k` under that stabilizer | `Complete.slot_isSome_iff` |

### Phase 2 — the construction (`Sims/Construct.lean`)

| Statement | Name |
|---|---|
| The worklist invariant: slot conditions, entries listing the filled slots once each, valid pending items, every requirement met or pending | `Inv`, `Met`, `ItemOK` |
| At most `n²` entries | `Inv.length_le` |
| **One step** keeps the invariant, decreases the potential `|pending| + 2n²(n² − |entries|)` and only fills empty slots | `step_spec` |
| The worklist empties within `fuel n L = L + 2n⁴ + 1` steps | `iter_step_spec`, `build_spec` |
| **The constructed table is complete for `⟨gs⟩`** | `complete_build` |
| The entries of rows `≥ k`, as a list, denote the entries of the table | `Inv.denoteSet_filter` |

### Phase 3 — sifting and the construction as programs (`Sims/SiftProg.lean`, `Sims/ConstructProg.lean`)

| Statement | Name |
|---|---|
| A loop paid by a potential returns the iterate of its step within the potential | `RunsWithin.loop_pot`, `iter_eq_of_fix` |
| Sifting costs at most `siftCost n = n (12 n + 40) + 21` | `RunsWithin.siftProg` |
| **The construction costs at most `buildCost n L`**, amortized: `siftCost n + 14` per pending item, `2n² (siftCost n + 14) + insCost n` per fillable slot | `RunsWithin.buildProg`, `buildPot`, `RunsWithin.stepBody` |

### Phase 4 — the operations (`Sims/Ops.lean`, `Orbits.lean`, `Cosets.lean`, `Oracle.lean`, `*Prog.lean`, `Wf.lean`)

| Operation | Model and contract | Program and cost |
|---|---|---|
| base orders listing a window first | `frontBase`, `frontBase_base` | `RunsWithin.frontBaseProg` |
| `generate`: the entries for the empty window | `generateModel_spec` | `RunsWithin.generateProg`, `genCost` |
| `stabilizer u`: entries of rows `≥ 1` for the window `[u]` | `stabModel_spec` | `RunsWithin.stabProg`, `stabCost` |
| `kernel w`: entries of rows `≥ |w|` | `kernelModel_spec` | `RunsWithin.kernelProg`, `kerCost` |
| `mem π`: does `π` sift? | `memModel_iff` | `RunsWithin.memProg`, `memCost` |
| `lift w π'`: one entry per window row, chosen by the required image | `liftModel_spec` | `RunsWithin.liftProg`, `liftCost` |
| `orbitTransversal u`: search from `u` on the generators, `r_{g v} = g r_v` | `orbitBFS_spec` | `RunsWithin.orbitBFSProg`, `transCost` |
| `orbits w`: one search per unseen window point | `orbitsModel_spec` | `RunsWithin.orbitsProg`, `orbitsCost` |
| `cosetReps G K`: search over left cosets, tested by sifting in `K`'s table | `cosetRepsModel_spec`, `length_le_index`, `mul_mem_of_closed` | `RunsWithin.cosetRepsProg`, `repsCost` |
| **all eight** | `ssOracle_meets : MeetsContract ssDV ssOracle` | well-formedness: `wf_*` lemmas |

### Phase 5 — the backend and its instantiations (`Solver/Sims.lean`, `Solver/SimsCompose.lean`)

| Statement | Name |
|---|---|
| The implementations are well-formed and never call back into the client | `ssImpl_wf` |
| **They compute the oracle within the schedule `ssB`**, on every contract input | `ssImpl_implements` |
| The number of coset representatives is the index | `length_cosetRepsModel` |
| **Backend bounds with `s = n²` for every ambient group**, independent of its order | `ssBounds` |
| `simsQ n ≤ 400 (n + 1)⁶`; `genCost n L ≤ 100 (n + 1)⁶ + 60 L (n + 1)²` | `simsQ_le`, `genCost_le` |
| **The solver with this backend**: correct, at cost at most `simsCost n L m N` | `solve_sims`, `simsSolver` |
| In closed form: `simsCost n L m N ≤ 13 + 100 (n+1)⁶ + 60 L (n+1)² + 800 (m+1) N (n+1)⁶` | `simsCost_le` |
| The validating entry, on every input | `solve_sims_checked` |
| **The restriction reduction**, cost `restrictSimsCost n m L N` | `restrict_sims` |
| **The block reduction**, cost `blockSimsCost n m k L N R` with `R = N / |K|` | `blockReduce_sims` |

The group order `N` enters `simsCost` only through the default strategy's `solveBound`; every
backend charge is polynomial (`efficient-backends.md`).

### Phase 6 — checks (`GraphIsoChecks/Sims.lean`)

- **Kernel-evaluated solver runs**, each tied to `solve_sims` by `runSims_spec` and compared
  with brute force: `C₃` with a unique solution, `S₃` with two, the trivial group with none,
  and the empty window with an outer representative.
- **Kernel-evaluated tables**: the orders of `S₃` and the dihedral group of order 8.
- **Interpreter runs**:
  - tables of `S₁₀`, `A₁₀`, `M₁₁`, `M₁₂`, `S₄ ≀ S₃` and `PSL(3, 2)` with their known orders;
  - the `generate`, `stabilizer` and `orbits` programs on `S₈`, `M₁₁` and `PSL(3, 2)`,
    agreeing with the oracle within their charges (for example `generate` on `M₁₁` costs
    2,065,437 against 60,875,390);
  - the solver and both reductions against brute force on the families of the sweep:
    7880 + 1472 solver runs, 1028 restriction runs, 2496 block runs, and 12 solver runs at
    degrees 6, 7 and 8 (among them `PSL(3, 2)` on the Fano plane) checked against all `n!`
    permutations.

These checks are narrower than `PLAN-2.md`'s verification list; `status.md` records the
difference.

### Audit

The build lists the axioms of 16 more principal theorems: `complete_of_closed`,
`complete_build`, `RunsWithin.buildProg`, `orbitBFS_spec`, `orbitsModel_spec`,
`cosetRepsModel_spec`, `liftModel_spec`, `ssOracle_meets`, `ssImpl_implements`, `ssImpl_wf`,
`solve_sims`, `solve_sims_checked`, `restrict_sims`, `blockReduce_sims`, `simsQ_le` and
`simsCost_le`. Each depends only on `propext`, `Classical.choice` and `Quot.sound`
(`ssImpl_wf` only on `propext`).

## Milestone 3 — Luks's strategy (`PLAN-3.md`)

A second solver procedure, `luksBody`, that handles a transitive window by a maximal block
system and the block reduction instead of point stabilizers. Its cost is governed by the
orders of primitive sections of the group, not by the group order. Every module is under
`GraphIso/Luks/`, except the Schreier–Sims instance in `GraphIso/Solver/Luks.lean`.

### Phase 1 — the closure of a partition and a pair (`Luks/Basic.lean`, `Luks/Closure.lean`)

| Statement | Name |
|---|---|
| Partitions of a window as label arrays; valid labels, invariance under the generators, coarsening | `LabelsOK`, `Stable`, `Coarser` |
| A merge relabels one class and removes exactly one leader | `labelsOK_merge`, `eq_or_of_merge`, `leaders_merge` |
| One step keeps the worklist invariant and lowers `|pending| + (s + 1) · leaders` | `closeStep_drop`, `closeStep_merge`, `CInv` |
| **The closure is the finest invariant partition coarser than `cl` that joins `u` and `v`** | `closure_spec` |

### Phase 2 — maximal block systems (`Luks/MaxBlocks.lean`, `Luks/Primitive.lean`)

| Statement | Name |
|---|---|
| Closures are monotone in the input partition | `oneClass_closure_mono` |
| **The pass**: every window point is in the class of `u` or has a closure with `u` that is a single class | `maxLabels_spec`, `MInv` |
| The classes form a block list that the generated group permutes, with at least two blocks | `isBlockList_blocksOf`, `permutesBlocks_blocksOf`, `two_le_length_blocksOf` |
| Labels invariant under the generators are invariant under the group | `stable_denote` |
| The block action of a transitive group is transitive, with blocks of equal size | `exists_blockHom_eq`, `length_block_mul` |
| **`|image of the block action| · |block kernel| = |G|`** | `blockHom_eq_one_iff`, `card_range_mul_card_blockKernel` |
| **The block action of the maximal pass is primitive** (`MulAction.IsPreprimitive`) | `isPreprimitive_blocksOf` |
| **The maximal block system**, packaged | `maxBlocks_spec` |

### Phase 3 — programs (`Luks/MaxBlocksProg.lean`)

| Statement | Name |
|---|---|
| Filtering a list by a Boolean program | `filterList`, `RunsWithin.filterList` |
| **The closure costs at most `closureCost n m s = m (n + 8m + 21s + 18) + 22`**, by a loop paid by the potential `closePot` | `RunsWithin.closureProg`, `closePot` |
| **The maximal block system costs at most `maxBlocksCost n m s`**: `O(m² (n + m + s))` | `RunsWithin.maxBlocksProg`, `RunsWithin.mbBody`, `RunsWithin.blocksOfProg` |
| The programs are well-formed | `wf_closureProg`, `wf_mbBody`, `wf_maxBlocksProg` |

### Phase 4 — the strategy and its theorem (`Luks/Strategy.lean`, `Luks/Cost.lean`, `Luks/Correctness.lean`, `Luks/Entry.lean`)

| Statement | Name |
|---|---|
| The procedure: empty window, pointwise-fixed window, orbits, maximal blocks with the block reduction | `luksBody`, `luksTransitive`, `luksBody_wf` |
| **Bounded primitive sections**: every primitive image of degree `k ≥ 2` of a subgroup of `G₀` has order at most `k ^ c` | `PrimBounded` |
| The backend bounds the strategy needs, with at most `R` coset representatives | `LuksBounds`, `luksQ` |
| `luksBound Q c m = 2 Q m ^ (c + 1) − Q` for `m ≥ 1`, and `Q` for `m = 0`; the orbit and block recurrences | `luksBound`, `luks_seq_arith`, `luks_block_arith`, `sum_pow_le` |
| The transitive case: `R' = |image| ≤ k ^ c ≤ n ^ c ≤ R`, then the block reduction | `luks_transitive_case` |
| The orbit case | `luks_orbits_case` |
| **Correctness and cost**: for `PrimBounded G₀ c` and `n ^ c ≤ R`, every valid instance is solved at cost at most `luksBound Q c m`, with at most `s` output generators | `luks_spec`, `LuksSpec` |
| The public and validating entries, and backend substitution | `luksEntry_spec`, `luksChecked_spec`, `luks_backend_refinement` |

### Phase 5 — bounded sections and the Schreier–Sims instance (`Luks/Nilpotent.lean`, `Solver/Luks.lean`)

| Statement | Name |
|---|---|
| **A primitive nilpotent permutation group of degree `k ≥ 2` has order `k`** | `card_eq_of_isPreprimitive_of_isNilpotent` |
| Nilpotent groups (so `p`-groups) have `PrimBounded G₀ 1` | `primBounded_of_isNilpotent` |
| Every subgroup of `Sym(n)` has `PrimBounded G₀ n` | `primBounded_degree` |
| Monotonicity of the Sims charges in the degree | `genCost_mono₂`, `kerCost_mono₂`, `repsCost_mono₃` |
| **The Schreier–Sims bounds for Luks's strategy**, `s = n²`, every ambient group | `ssLuksBounds` |
| `luksSimsQ n R ≤ 3200 (n+1)⁶ + 50 R (n+1)⁴ + 13 R² (n+1)⁴` | `luksSimsQ_le` |
| The solver's bound in closed form | `luksSimsCost_le` |
| **The solver with Luks's strategy and this backend**: correct, at cost at most `luksSimsCost n L m c` | `solve_luks`, `luksSolver` |
| The validating entry, on every input | `solve_luks_checked` |
| Every group, with the exponential bound for `c = n` | `solve_luks_any` |
| **Nilpotent groups: cost at most `6640 (n+1)⁸ + 60 L (n+1)²`** | `solve_luks_nilpotent` |

### Phase 6 — checks (`GraphIsoChecks/Luks.lean`)

- **A kernel-evaluated solver run**, tied to `solve_luks_any` by `runLuks_spec` and compared
  with brute force: `⟨(0 1)⟩` on two points with the unique solution `(0 1)`, cost 12,976.
- **Interpreter runs**:
  - `maxBlocks` on eight transitive groups, with their expected maximal blocks: the wreath
    products `C₂ ≀ C₂ ≀ C₂` and `S₄ ≀ S₃`, `S₃ ≀ S₂`, `D₄`, `C₄`, `C₆`, and the primitive
    groups `S₄` and `PSL(3, 2)`;
  - the solver against brute force, within `luksSimsCost` for `c = n`: 2760 + 720 + 736 runs
    on the sweep families of degrees 1–4, 7 runs at degrees 6 and 8, and `PSL(3, 2)` with
    distinct symbols;
  - `C₂ ≀ C₂ ≀ C₂` on 8 points (order 128), two runs against brute force with the default
    strategy alongside (Luks costs 6,624,446 and 5,339,641; the default strategy 2,262,152
    and 1,572,920);
  - `C₂ ≀ C₂ ≀ C₂ ≀ C₂` on 16 points (order 32768) with distinct symbols, against the
    solutions found by enumerating the group from a complete table: cost 171,554,221, within
    the nilpotent bound 46,319,029,477,600.

`status.md` records how these checks are narrower than `PLAN-3.md`'s verification list.

### Audit

The build lists the axioms of 21 more principal theorems:
- the block-system results: `closure_spec`, `maxLabels_spec`, `isPreprimitive_blocksOf`,
  `maxBlocks_spec`, `card_range_mul_card_blockKernel`;
- the program costs and well-formedness: `RunsWithin.closureProg`,
  `RunsWithin.maxBlocksProg`, `luksBody_wf`;
- the strategy's theorems: `luks_spec`, `luksEntry_spec`, `luks_backend_refinement`,
  `luksChecked_spec`;
- the bounds on primitive sections: `card_eq_of_isPreprimitive_of_isNilpotent`,
  `primBounded_of_isNilpotent`, `primBounded_degree`;
- the Schreier–Sims instance: `luksSimsQ_le`, `luksSimsCost_le`, `solve_luks`,
  `solve_luks_checked`, `solve_luks_any`, `solve_luks_nilpotent`.

Each depends only on `propext`, `Classical.choice` and `Quot.sound`; `luksBody_wf` depends
only on `propext`, and `luksSimsQ_le` only on `propext` and `Quot.sound`.

## Milestone 4 — graphs of maximum degree three (`PLAN-4.md`)

Luks's polynomial-time isomorphism test for connected graphs of maximum degree at most three,
by a layered `2`-group reduction to string isomorphism solved with `solve_luks`'s machinery.
Graph data are arrays of adjacency lists on `0, …, n − 1`; the union `Z = X ⊔ Y` has `N = 2n`
points. Modules are under `GraphIso/Graph/`, the concrete theorems in
`GraphIso/Solver/Graph.lean`.

### Phase 1 — graph data and levels (`Graph/Basic.lean`, `Graph/Levels.lean`)

| Statement | Name |
|---|---|
| Valid data of maximum degree three: sizes, bounds, no repeats, symmetric, loopless, degree `≤ 3` | `GraphData.Valid` |
| The disjoint union and its adjacency (`adj_union_iff` in `Swap.lean`) | `GraphData.union`, `nbrs_union_lt`, `nbrs_union_ge`, `adj_union_iff` |
| **Levels by relaxation to a fixpoint**: `0` exactly at the roots, adjacent levels differ by at most one, each positive level below `N` has a witness one level down | `levels`, `IsLevels`, `levels_spec` |
| Root- and adjacency-preserving permutations preserve levels | `lev_act` |

### Phase 2 — layer groups (`Graph/Layers.lean` to `Graph/Swap.lean`)

| Statement | Name |
|---|---|
| `A_r`: permutations supported on level `≤ r`, preserving levels and the edges of `Z_r` | `AutR`, `EdgeR` |
| Twin classes (new points with the same neighbourhood in level `r`) have at most two points | `cnt_le_two` |
| The extendable subgroup: elements of `A_r` preserving the layer string `xval` on the subsets of level `r` with at most three points | `HR`, `xval`, `SubL` |
| **The canonical lift** by rank matching is a homomorphism into `A_{r+1}` | `liftPerm`, `liftPerm_mul`, `liftPerm_mem` |
| Restriction lands in `HR r`; the kernel is generated by twin transpositions | `resPerm_mem`, `mem_closure_twinSwaps` |
| **`A_{r+1}` is generated by the lifts of generators of `HR r` and the twin swaps** | `autR_succ_eq` |
| **The extension criterion**: an element of `A_r` extends to `A_{r+1}` exactly when it lies in `HR r` | `mem_HR_iff_extends` |
| **Every `A_r` is a `2`-group**; `A_0` is generated by three involutions | `isPGroup_autR`, `closure_gens0` |
| The union rooted at two edges is layered once every point is reached | `layered_union`, `roots4_union` |
| **The swap criterion**: an isomorphism sending `{a, b}` to `{a', b'}` exists exactly when some generator of `A_{2n}` moves `a` to the other side; it is read off as `v ↦ g v − n` | `iso_iff_exists_gen`, `exists_iso_of_swap` |

### Phase 3 — the layer step and its programs (`Graph/Subsets.lean` to `Graph/LevelsProg.lean`)

| Statement | Name |
|---|---|
| Canonical triples: a set of at most three numbers is determined by its sorted, padded triple | `canon`, `canon_spec`, `canonical_unique`, `subsL` |
| The domain `N + m` (`m` the nonempty subsets of level `r` with at most three points) and the induced action; an action for level-preserving `g` | `tripImg`, `indFun`, `tripImg_mul`, `tripImg_one`, `indPerm` |
| **The layer string on the subsets characterizes `HR r`** | `xstr_iff` |
| The induced action as an injective homomorphism; its image of a `2`-group is nilpotent; the window of the subsets is invariant | `indHom`, `indHom_injective`, `isNilpotent_indHom`, `isInvariant_tripWin` |
| The induced generators generate the image | `denote_map_indData`, `denote_map_indData'` |
| **Readback**: truncating generators of the string-isomorphism answer gives valid generators of `HR r` | `readback` |
| **The next generators**: lifts and twin transpositions are valid and generate `A_{r+1}` | `nextGens_spec` |
| Programs with exact values and costs: neighbour lists, set equality, the layer string, canonical triples, the position, offset and index arrays, induced generators, lifts, twin swaps, levels (a loop paid by the sum of levels), the union, the generators of `A₀` and the swap test | `RunsWithin.nbLProg`, `.xTripProg`, `.xArrProg`, `.subsProg`, `.ptsProg`, `.posProg`, `.multsProg`, `.cidxProg`, `.canonProg`, `.indProg`, `.liftProg`, `.twinsProg`, `.levelsProg`, `.unionProg`, `.gens0Prog`, `.testProg`, `.findProg`, `.isoArrProg` |
| The computed models are the semantic objects | `get_xArr_trip`, `get_posArr`, `get_cidxArr`, `indDataB_eq`, `liftB_eq`, `liftDataB_eq` |

### Phase 4 — the algorithm (`Graph/Step.lean`, `EdgeProg.lean`, `Algorithm.lean`, `Entry.lean`)

| Statement | Name |
|---|---|
| **One layer step**, running `solveEntry` inside `luksBody` with the Schreier–Sims context: from valid generators of `A_r`, at most `genBound N` valid generators of `A_{r+1}`, at cost at most `stepCost N L` | `RunsWithin.stepProg` |
| The edge test for `{a, b}` and `{a', b'}`: `none` exactly when no isomorphism sends one edge to the other, otherwise an isomorphism, at cost at most `edgeCost n` | `RunsWithin.edgeProg` |
| Connectivity as read by the algorithm (vacuous for `n = 0`); every point of the union is then reached | `Conn`, `reach_union` |
| **The algorithm**: for valid connected data, `none` exactly when `X` and `Y` are not isomorphic, otherwise an isomorphism, at cost at most `mainCost n` | `RunsWithin.mainProg` |
| The programs are well-formed | `wf_stepInputProg`, `wf_stepProg`, `wf_edgeProg`, `wf_mainProg` |

### Phase 5 — validation, closed form, concrete theorems (`Graph/Validate.lean` to `Solver/Graph.lean`)

| Statement | Name |
|---|---|
| The validity check decides `GraphData.Valid`, at cost at most `151 n + 8` on every input | `validGB_iff`, `RunsWithin.validGraphProg` |
| The connectivity check decides `Conn` on valid data | `connB_iff`, `RunsWithin.connProg` |
| The checked entry against the Schreier–Sims context, on every input; the empty input `(0, #[], #[])` is valid, as `Conn 0` holds vacuously | `gi3Checked`, `gi3Checked_wf`, `RunsWithin.gi3Checked` |
| **Closed form**: one layer step `≤ 8100 (N + 1)²⁴`; the algorithm `≤ 16900 (2n + 1)²⁶`; the checked entry `≤ 17500 (2n + 1)²⁶` | `layerCost_le`, `edgeCost_le`, `mainCost_le`, `checkedCost_le` |
| **Graph isomorphism of maximum degree three in polynomial time**: the checked entry with the Schreier–Sims implementations substituted, run inside `luksSolver`, on every input | `gi3_checked` |
| Simple graphs of the data; their isomorphisms are those of the data; `Conn` is `SimpleGraph.Connected` for `n > 0` | `GraphData.toSimpleGraph`, `isIso_iff`, `nonempty_iso_iff`, `conn_iff_connected` |
| The data of a simple graph on `Fin n`: its simple graph is the graph, and it is valid when every degree is at most three | `GraphData.ofSimpleGraph`, `toSimpleGraph_ofSimpleGraph`, `valid_ofSimpleGraph` |
| **The statement for mathlib's simple graphs**: connected, every degree at most three | `gi3_simpleGraph`, `gi3_simpleGraph'` |

### Phase 6 — checks (`GraphIsoChecks/Graph.lean`)

- **Kernel-evaluated runs**, tied to `gi3_checked` by `runGI_spec`: on one point, the identity,
  cost 174; on no points, the empty map, cost 80. The empty input is valid for the checked
  entry, although mathlib's graphs on `Fin 0` are not connected.
- **Interpreter runs** against brute force over all `n!` permutations, every returned
  isomorphism checked, within `17500 (2n + 1)²⁶`: `K₂` (32,205,778 units); `P₃` against a
  relabelling (39,358,911); `P₄` against a relabelling (100,759,374); `P₄` against the star
  `K₁,₃`, not isomorphic (298,416,314); `K₄` against itself with permuted lists (142,320,009).
- Five invalid inputs rejected by the validity and connectivity checks: a vertex of degree
  four, a disconnected graph, a wrong number of lists, an asymmetric list, a loop.

`status.md` records how these checks are narrower than `PLAN-4.md`'s list.

### Audit

The build lists the axioms of 34 more principal theorems: the layer-group results
(`levels_spec`, `cnt_le_two`, `liftPerm_mem`, `autR_succ_eq`, `mem_HR_iff_extends`,
`isPGroup_autR`, `closure_gens0`, `iso_iff_exists_gen`, `exists_iso_of_swap`, `xstr_iff`); the
layer step (`indHom_injective`, `denote_map_indData`, `readback`, `indDataB_eq`,
`liftDataB_eq`, `nextGens_spec`, `RunsWithin.stepProg`); the algorithm
(`RunsWithin.levelsProg`, `RunsWithin.edgeProg`, `reach_union`, `RunsWithin.mainProg`); the
checked entry and the concrete theorems (`validGB_iff`, `RunsWithin.validGraphProg`,
`gi3Checked_wf`, `RunsWithin.gi3Checked`, `checkedCost_le`, `gi3_checked`); the simple graphs
(`conn_iff_connected`, `nonempty_iso_iff`, `toSimpleGraph_ofSimpleGraph`,
`valid_ofSimpleGraph`, `gi3_simpleGraph`, `gi3_simpleGraph'`); and `luksSimsCost_one_le`.

Each depends only on `propext`, `Classical.choice` and `Quot.sound`; `gi3Checked_wf` depends
only on `propext`, and `nonempty_iso_iff` only on `propext` and `Quot.sound`.

## Milestone 5 — all graphs of maximum degree three (`PLAN-5.md`)

Milestone 4 without the connectivity hypothesis, by the reduction to components. Candidate
pairs of components of equal size are tested by milestone 4's `mainProg` until a partner is
found. Modules
`Graph/Components.lean`, `Graph/CompProg.lean`, `Graph/All.lean`; the concrete theorems in
`GraphIso/Solver/GraphAll.lean`.

### Phases 1 and 2 — components, invariance, gluing (`Graph/Components.lean`)

| Statement | Name |
|---|---|
| Reachability is read off the levels from one root | `Reach`, `lev_lt_iff_reach` |
| The components: nonempty, closed, disjoint, covering | `compOf`, `isRep`, `reps`, `comps`, `ne_nil_of_mem_comps`, `closed_of_mem_comps`, `eq_of_mem_comps`, `exists_mem_comps`, `nodup_comps` |
| **The component data are valid and connected** | `subG`, `adj_subG`, `valid_subG`, `conn_subG` |
| Isomorphism of data of the same size, an equivalence | `GIso`, `GIso.refl`, `GIso.symm`, `GIso.trans` |
| **An isomorphism maps components onto components with isomorphic data** | `imgComp`, `mem_imgComp`, `giso_imgComp` |
| **Isomorphic graphs have balanced components** | `Balanced`, `balanced_comps` |
| The greedy step: a partner exists, removing a pair keeps the balance, the end | `Balanced.exists`, `Balanced.step`, `Balanced.eq_nil` |
| **Gluing**: matched components with isomorphisms give an isomorphism, writes in any order | `glueWrites`, `MatchOk`, `glue`, `glue_spec` |

### Phase 3 — programs (`Graph/CompProg.lean`, `Graph/All.lean`)

| Statement | Name |
|---|---|
| The components, at cost at most `compsCost n` | `compsProg`, `comps_eq_fold`, `RunsWithin.compsProg` |
| The component data, at cost at most `subGCost k` | `subGProg`, `RunsWithin.subGProg` |
| The gluing writes, a permutation of `M.flatMap glueWrites` | `glueProg`, `perm_foldl_glueStep`, `RunsWithin.glueProg` |
| One candidate partner, calling `mainProg` when the sizes agree | `partnerStepProg`, `PartnerInv`, `RunsWithin.partnerStepProg` |
| Matching one component | `matchStepProg`, `MatchInv`, `RunsWithin.matchStepProg` |
| A fold with an invariant of the remaining elements | `RunsWithin.foldList_rest` |
| The programs are well-formed | `wf_compsProg`, `wf_subGProg`, `wf_glueProg`, `wf_partnerStepProg`, `wf_matchStepProg`, `wf_allProg` |

### Phase 4 — the algorithm and the concrete theorems (`Graph/All.lean`, `Solver/GraphAll.lean`)

| Statement | Name |
|---|---|
| **The algorithm**: for valid data, `none` exactly when `X` and `Y` are not isomorphic, otherwise an isomorphism, at cost at most `allCost n` | `allProg`, `RunsWithin.allProg` |
| The checked entry against the Schreier–Sims context, on every input | `GIValidAll`, `gi3AllChecked`, `gi3AllChecked_wf`, `RunsWithin.gi3AllChecked` |
| **Closed form**: the algorithm `≤ 4750 (2n + 1)²⁸`, the checked entry `≤ 5100 (2n + 1)²⁸` | `allCost_eq`, `allCost_le`, `allCheckedCost_le` |
| **Isomorphism of all graphs of maximum degree three in polynomial time**, on every input | `gi3_all_checked` |
| **The statement for mathlib's simple graphs**: every degree at most three, connected or not | `gi3_all_simpleGraph`, `gi3_all_simpleGraph'` |

### Phase 5 — checks (`GraphIsoChecks/GraphAll.lean`)

- **Kernel-evaluated runs**, tied to `gi3_all_checked` by `runAll_spec`: on no points, the
  empty map, cost 39; on two isolated points, the identity, cost 691.
- **Interpreter runs** against brute force over all `n!` permutations, every returned
  isomorphism checked, within `5100 (2n + 1)²⁸`: three isolated points (1,209 units);
  `K₂ ⊔ K₁` against a relabelling (32,206,938); `2K₂` against a relabelling with components
  `{0, 2}` and `{1, 3}` (64,413,521); `2K₂` against `P₄`, not isomorphic (3,194);
  `K₃ ⊔ K₁` against `P₃ ⊔ K₁`, not isomorphic (132,880,243); `P₃ ⊔ K₃` against `K₃ ⊔ P₃`
  (285,280,795).
- Four invalid inputs rejected by the validity check: a vertex of degree four, a wrong number
  of lists, an asymmetric list, a loop.

### Audit

The build lists the axioms of 24 more principal theorems: `lev_lt_iff_reach`, `conn_subG`,
`valid_subG`, `giso_imgComp`, `balanced_comps`, `Balanced.exists`, `Balanced.step`,
`Balanced.eq_nil`, `glue_spec`, `RunsWithin.compsProg`, `RunsWithin.subGProg`,
`RunsWithin.glueProg`, `RunsWithin.partnerStepProg`, `RunsWithin.matchStepProg`,
`RunsWithin.allProg`, `wf_allProg`, `gi3AllChecked_wf`, `RunsWithin.gi3AllChecked`,
`allCheckedCost_le`, `gi3_all_checked`, `gi3_all_simpleGraph`, `gi3_all_simpleGraph'`.

Each depends only on `propext`, `Classical.choice` and `Quot.sound`; `wf_allProg` and
`gi3AllChecked_wf` depend only on `propext`, and `Balanced.step` only on `propext` and
`Quot.sound`.

## Milestone 6 — primitive solvable groups (`PLAN-6.md`)

The solvable case of the Babai–Cameron–Pálfy theorem in the form of Helfgott's Theorem 2.3,
for a bounded number of prime divisors, and polynomial string isomorphism for such groups. The group theory is in `GraphIso/Groups/`
(namespace `GraphIso.Groups`, mathlib imports only); `primBounded_of_isSolvable` in
`Luks/Solvable.lean`; the concrete theorem in `Solver/LuksSolvable.lean`.

### Phase 1 — linear `r`-groups (`Groups/LinearPGroup.lean`)

| Statement | Name |
|---|---|
| `r`-subgroups of `Sym(t)` have order at most `2^{t−1}` (Legendre) | `le_two_pow_pred`, `card_le_two_pow_of_isPGroup_perm` |
| A maximal abelian normal subgroup of an `r`-group is self-centralizing | `exists_mem_center_of_normal`, `centralizer_le_of_maximal` |
| The algebra generated by a group of order invertible in `F`, with commuting image, is reduced (Maschke) | `isReduced_adjoin_range` |
| An element acting trivially by conjugation on a normal subgroup centralizes it | `mem_centralizer_of_conjNormal_eq_one` |
| Idempotents of the maximal ideals; `\|V\| = ∏ \|V_𝔪\|` | `zeroSpace`, `exists_idempotents`, `card_eq_prod_zeroSpace` |
| `R` permutes the maximal ideals by conjugation | `gensOf`, `algOf`, `conjB`, `maxAct`, `maxAction`, `apply_mem_zeroSpace_maxAct` |
| The kernel restricted to the subspaces | `fixSub`, `resGL` |
| The induction step: two or more maximal ideals, one maximal ideal | `card_le_of_two_le_card`, `card_le_of_card_eq_one` |
| **Linear `r`-groups in characteristic `p ≠ r`: `2 \|R\| ≤ \|V\|³`** | `card_le_of_isPGroup`, `card_le_of_isPGroup'` |

### Phase 2 — coprime action and the `p′`-core (`Groups/Coprime.lean`, `Groups/PCore.lean`)

| Statement | Name |
|---|---|
| A homomorphism from a `p`-group to a `p′`-group is trivial | `map_one_of_isPGroup` |
| `MulAut E` acts linearly on an elementary abelian `E` | `exists_mulAut_toGL` |
| **Coprime automorphism groups of solvable groups: `\|P\| ≤ \|N\|³`** | `card_le_of_coprime` |
| The `p′`-core exists | `not_dvd_card_sup`, `exists_pcore` |
| A nontrivial normal subgroup contains a nontrivial normal `p`-subgroup (no normal `p′`-subgroup) | `exists_derivedSeries_last`, `exists_normal_isPGroup_le`, `eq_bot_of_pcore_quotient` |
| **The centralizer of the `p′`-core lies in it** (solvable, no normal `p`-subgroup) | `centralizer_le_of_pcore` |

### Phase 3 — solvable linear and primitive solvable groups (`Groups/SolvableLinear.lean`, `Groups/PrimitiveSolvable.lean`, `Luks/Solvable.lean`)

| Statement | Name |
|---|---|
| The order from bounds on the Sylow subgroups | `card_le_prod_of_sylow` |
| **Solvable linear groups with no normal `p`-subgroup: `\|H\| ≤ \|V\|^{12 s′}`** | `card_le_of_isSolvable_linear` |
| A nontrivial elementary abelian normal subgroup, inside any given nontrivial abelian normal subgroup | `exists_abelian_normal`, `exists_elementary_of_abelian`, `exists_elementary_abelian_normal` |
| Nontrivial normal subgroups of quasiprimitive groups are transitive | `nontrivial_of_isPretransitive`, `isPretransitive_of_ne_bot` |
| The affine reduction (factored out in milestone 8): a bound for the linear point stabilizers bounds the group | `card_le_of_isQuasiPreprimitive_of_abelian` |
| **Quasiprimitive and primitive solvable groups: `\|G\| ≤ k^{12 s + 1}` for `s + 1` prime divisors** | `card_le_of_isQuasiPreprimitive_of_isSolvable`, `card_le_of_isPreprimitive_of_isSolvable` |
| **Solvable groups with at most `s + 1` prime divisors have bounded primitive sections**: `PrimBounded G₀ (12 s + 1)` | `primBounded_of_isSolvable` |

### Phase 4 — the concrete theorem (`Solver/Luks.lean`, `Solver/LuksSolvable.lean`)

| Statement | Name |
|---|---|
| The solver's bound for `c ≥ 1`: at most `6640 (n + 1)^{3c + 5} + 60 L (n + 1)²` (in `Solver/Luks.lean`; `luksSimsCost_one_le` is the case `c = 1`) | `luksSimsCost_le_pow` |
| **String isomorphism for solvable groups with `s + 1` prime divisors**, at most `6640 (n + 1)^{36 s + 8} + 60 L (n + 1)²` | `solve_luks_solvable` |

### Phase 5 — checks (`GraphIsoChecks/LuksSolvable.lean`)

Interpreter runs of Luks's strategy against brute force and the default strategy, the number
of prime divisors computed from a Sims table, the cost within the bound of
`solve_luks_solvable`: `S₄` (two string pairs), `AGL(1, 5)` (two), `S₃ wr S₂` with `s = 1`;
`AGL(1, 7)` with `s = 2`.

### Audit

The build lists the axioms of 16 more principal theorems: `card_le_two_pow_of_isPGroup_perm`,
`centralizer_le_of_maximal`, `isReduced_adjoin_range`, `exists_idempotents`,
`card_eq_prod_zeroSpace`, `card_le_of_isPGroup`, `card_le_of_isPGroup'`, `card_le_of_coprime`,
`exists_pcore`, `centralizer_le_of_pcore`, `card_le_of_isSolvable_linear`,
`card_le_of_isQuasiPreprimitive_of_isSolvable`, `card_le_of_isPreprimitive_of_isSolvable`,
`primBounded_of_isSolvable`, `luksSimsCost_le_pow`, `solve_luks_solvable`. Each depends only on `propext`, `Classical.choice` and `Quot.sound`.

## Milestone 7 — graphs of maximum degree five (`PLAN-7.md`)

Luks's layered reduction of milestones 4 and 5 for maximum degree `Δ`, polynomial for
`Δ ≤ 5`: the layer groups are solvable `{2, 3}`-groups, so milestone 6's
`primBounded_of_isSolvable` with `s = 1` bounds every string-isomorphism call. The
degree-free theory of milestones 4 and 5 is stated for maximum degree `Δ` in place
(`GraphData.ValidD`, `LayeredD`, `SubL Δ`, `xval Δ`, `HR … Δ`), with `GraphData.Valid =
ValidD 3` and `Layered = LayeredD 3`, so milestones 4 and 5 are unchanged. The new modules are
under `GraphIso/Valence/` (namespace `GraphIso.Graph.Valence`); the concrete theorems are in
`GraphIso/Solver/Valence.lean` and `GraphIso/Solver/ValenceAll.lean`.

### Phase 1 — the degree-free theory for maximum degree `Δ` (`Graph/Basic.lean` to `Graph/SimpleGraph.lean`)

| Statement | Name |
|---|---|
| Valid data of maximum degree `Δ`; `Valid` is the case `Δ = 3` | `GraphData.ValidD`, `GraphData.Valid`, `GraphData.ValidD.mono` |
| Layered graphs of maximum degree `Δ ≥ 2`; `Layered` is the case `Δ = 3` | `LayeredD`, `Layered` |
| **Twin classes have at most `Δ − 1` points** | `cnt_le` (`cnt_le_two` for `Δ = 3`) |
| The layer string adds `Δ + 1` for an edge; the subsets read have at most `Δ` points | `xval`, `SubL`, `HR` |
| The lifts, the extension criterion, the twin decomposition (no bound on class sizes), the roots and the swap criterion, for every `Δ` | `liftPerm_mem`, `mem_HR_iff_extends`, `mem_closure_twinSwaps`, `autR_succ_eq`, `closure_gens0`, `layered_union`, `iso_iff_exists_gen` |
| For `Δ ≤ 3` an element of the kernel is an involution; the `2`-group property of milestone 4 | `kernel_apply_apply`, `isPGroup_autR` |
| Components, balance, gluing and simple graphs for every `Δ` | `valid_subG`, `balanced_comps`, `glue_spec`, `nonempty_iso_iff`, `conn_iff_connected`, `valid_ofSimpleGraph` |

### Phase 2 — subsets and the layer step domain (`Valence/Subsets.lean` to `Valence/Ind.lean`)

| Statement | Name |
|---|---|
| The sublists of `l` with at most `Δ` elements: exactly the sublists of length `≤ Δ`, no repeats, empty first | `subsR`, `mem_subsR`, `nodup_subsR`, `subsR_head` |
| A sublist of an increasing list is determined by its elements; every set of at most `Δ` points of `l` is represented | `eq_of_toFinset_eq`, `exists_subsR` |
| **At most `(ℓ + 1)^Δ` subsets** | `length_subsR_le` |
| The domain `N + m`; the image of a subset by linear search; an action for maps of `Lr` into itself | `domSize`, `subAt`, `findSub`, `subImg`, `subSet`, `subAt_inj`, `findSub_eq`, `subSet_subImg`, `subImg_mul`, `subImg_one`, `indFun`, `indPerm` |
| **The layer string on the subsets characterizes `HR Δ r`** | `xstr_iff` |
| The edge test and the layer string as computed | `edgeL`, `edgeL_iff`, `xSub`, `xSub_eq`, `xArr`, `get_xArr_sub` |
| The induced action as an injective homomorphism; the induced generators generate the image; the window is invariant | `indHom`, `indHom_injective`, `denote_map_indData`, `isInvariant_subWin` |
| **Readback**: truncations of the answer's generators generate `HR Δ r` | `readback` |

### Phase 3 — solvable layer groups (`Valence/Solvable.lean`)

| Statement | Name |
|---|---|
| A finite product of solvable groups is solvable | `isSolvable_pi` |
| A permutation of at most four points satisfies `σ¹² = 1` | `pow_twelve_eq_one` |
| Restriction `A_{r+1} →* A_r`; its kernel fixes every point not of level `r + 1` | `resHom`, `fix_of_mem_ker`, `fix_of_mem_ker'` |
| **The kernel embeds in a product of permutation groups of twin classes**, each of at most `Δ − 1` points, so at most four for `Δ ≤ 5` | `Tw`, `tw_iff`, `twinHom`, `twinHom_injective`, `card_tw_le_pred`, `card_tw_le` |
| The kernel is solvable, and its elements satisfy `k¹² = 1` | `isSolvable_ker`, `ker_pow_twelve` |
| **For `Δ ≤ 5`, every `A_r` is solvable**, every element has order dividing `2^i 3^j`, and **`\|A_r\|` has at most two prime divisors** (Cauchy) | `isSolvable_autR`, `exists_pow_eq_one`, `card_primeFactors_autR_le` |

### Phase 4 — programs (`Valence/LevelsProg.lean` to `Valence/Step.lean`)

| Statement | Name |
|---|---|
| Levels and the union for maximum degree `Δ` (milestone 4's programs) | `RunsWithin.relaxAtProg`, `.levStepProg`, `.levelsProg`, `.unionProg` |
| The sublists, by one fold from the right, at cost at most `subsCost Δ ℓ` | `subsProg`, `foldl_subsStep`, `RunsWithin.subsFold`, `RunsWithin.subsProg` |
| The search, the induced arrays and generators; **the computed data are `indData`** | `findSubProg`, `indProg`, `RunsWithin.findSubProg`, `RunsWithin.indProg`, `indArr_eq`, `indDataB_eq` |
| The layer string and its array | `xSubProg`, `xArrProg`, `RunsWithin.xSubProg`, `RunsWithin.xArrProg` |
| The lifts and twin swaps (milestone 4's programs) for maximum degree `Δ` | `RunsWithin.classProg`, `.liftBProg`, `.liftProg`, `.twinInnerProg`, `.twinsProg` |
| **The constant of the string-isomorphism calls as a parameter**: `LayerPrim Δ c`, every homomorphic image of every layer group has `PrimBounded _ c`; for `Δ ≤ 5` it holds with `c = 13` (solvable, at most two prime divisors) | `LayerPrim`, `layerPrim_solvable` |
| **One layer step** for `LayerPrim Δ c`, `c ≥ 1`: from valid generators of `A_r`, at most `genBound Δ N` valid generators of `A_{r+1}`, at cost at most `stepCost Δ c N L` (the solver's term `6640 (D + 1)^{3c + 5}`) | `stepProg`, `RunsWithin.stepProg` |
| The programs are well-formed | `wf_subsProg`, `wf_indProg`, `wf_xArrProg`, `wf_stepInputProg`, `wf_stepProg` |

### Phase 5 — the algorithms and the concrete theorems (`Valence/EdgeProg.lean` to `Solver/ValenceAll.lean`)

| Statement | Name |
|---|---|
| The edge test and the algorithm for connected graphs, `Δ ≥ 2` and `LayerPrim Δ c`, at cost at most `edgeCost Δ c n`, `mainCost Δ c n` | `RunsWithin.edgeProg`, `RunsWithin.edgesProg`, `RunsWithin.mainProg`, `wf_edgeProg`, `wf_mainProg` |
| The validity check of maximum degree `Δ`, on every input; connectivity | `validGB`, `validGB_iff`, `shortProg`, `RunsWithin.validGraphProg`, `RunsWithin.connProg` |
| The checked entry for connected graphs of maximum degree `Δ`, for `LayerPrim Δ c`; the entry for `Δ = 5`, the case `c = 13` | `GIValidB`, `giBoundedChecked`, `giBoundedChecked_wf`, `RunsWithin.giBoundedChecked`, `GIValid5`, `gi5Checked`, `gi5Checked_wf`, `RunsWithin.gi5Checked` |
| **Closed form**: a layer domain has at most `(N + 2)⁵` points; one layer step `≤ 9000 (N + 2)²²⁰`; the algorithm `≤ 28000 (2n + 2)²²²`; the checked entry `≤ 28600 (2n + 2)²²²` | `domBound_five_succ_le`, `layerCost_five_le`, `edgeCost_five_le`, `mainCost_five_le`, `checkedCost5_le` |
| **Isomorphism of connected graphs of maximum degree five in polynomial time**, on every input | `gi5_checked` |
| **The statement for mathlib's simple graphs**: connected, every degree at most five | `gi5_simpleGraph`, `gi5_simpleGraph'` |
| Components for maximum degree `Δ` (milestone 5's programs); the matching with `mainProg Δ`, for a bound `B` on the connected test on at most `n` points (`mainBound n = 28000 (2n + 2)²²²` for `Δ = 5`) | `RunsWithin.compsProg`, `RunsWithin.subGProg`, `partnerStepProg`, `matchStepProg`, `allProg`, `RunsWithin.partnerStepProg`, `RunsWithin.matchStepProg`, `RunsWithin.allProg`, `wf_allProg`, `mainCost_le_mainBound` |
| The checked entry for all graphs of maximum degree `Δ`; the entry for `Δ = 5` | `GIValidAllB`, `giBoundedAllChecked`, `giBoundedAllChecked_wf`, `RunsWithin.giBoundedAllChecked`, `GIValidAll5`, `gi5AllChecked`, `gi5AllChecked_wf`, `RunsWithin.gi5AllChecked` |
| **Closed form**: the algorithm `≤ 7100 (2n + 2)²²⁴`, the checked entry `≤ 7200 (2n + 2)²²⁴` | `allCost_five_le`, `allCheckedCost5_le` |
| **Isomorphism of all graphs of maximum degree five in polynomial time**, on every input | `gi5_all_checked` |
| **The statement for mathlib's simple graphs**: every degree at most five, connected or not | `gi5_all_simpleGraph`, `gi5_all_simpleGraph'` |

### Phase 6 — checks (`GraphIsoChecks/Valence.lean`)

- **Kernel-evaluated runs**, tied to `gi5_checked` and `gi5_all_checked` by `runGI5_spec` and
  `runAll5_spec`: no points (cost 80) and one point (174) for the connected entry, no points
  (39) for the all-graphs entry.
- **Interpreter runs** against brute force over all `n!` permutations, every returned
  isomorphism checked, within the closed-form bounds: `P₃` against a relabelling
  (50,699,515 units); `K₁,₃` against a relabelling (125,661,344); `K₃` against `P₃`, not
  isomorphic (171,114,633); three isolated points (1,209), `K₂ ⊔ K₁` against a relabelling
  (42,437,378) and `2K₂` against `P₄` (3,194) with the all-graphs entry.
- Six invalid inputs rejected: a vertex of degree six (both entries), a disconnected graph, a
  wrong number of lists, an asymmetric list, a loop.
- **A layer step with a twin class of three points**: the first layer step of
  `K₁,₄ ⊔ K₁,₄` (78,629,977 units) returns generators of `A₁` whose group has order
  `72 = 2³ · 3²`, equal to a brute-force count of `A₁`. A whole run with a vertex of degree
  four does not fit the interpreter (`status.md`).

### Audit

The build lists the axioms of 47 more principal theorems: the layer theory (`cnt_le`,
`mem_closure_twinSwaps`), the subsets and the domain (`mem_subsR`, `length_subsR_le`,
`subAt_inj`, `subSet_subImg`, `xstr_iff`, `xSub_eq`, `indHom_injective`,
`denote_map_indData`, `readback`), the solvable layer groups (`isSolvable_pi`,
`pow_twelve_eq_one`, `twinHom_injective`, `isSolvable_ker`, `ker_pow_twelve`,
`isSolvable_autR`, `exists_pow_eq_one`, `card_primeFactors_autR_le`), the programs and the
step (`RunsWithin.levelsProg`, `indDataB_eq`, `RunsWithin.subsProg`, `RunsWithin.indProg`,
`RunsWithin.xArrProg`, `RunsWithin.liftProg`, `RunsWithin.twinsProg`, `layerPrim_solvable`
(`induced_isSolvable` before milestone 9), `RunsWithin.stepProg`), the algorithms (`RunsWithin.edgeProg`, `RunsWithin.mainProg`,
`wf_mainProg`, `validGB_iff`, `RunsWithin.validGraphProg`, `RunsWithin.allProg`,
`wf_allProg`) and the concrete theorems (`gi5Checked_wf`, `RunsWithin.gi5Checked`,
`checkedCost5_le`, `gi5_checked`, `gi5_simpleGraph`, `gi5_simpleGraph'`, `gi5AllChecked_wf`,
`RunsWithin.gi5AllChecked`, `allCheckedCost5_le`, `gi5_all_checked`, `gi5_all_simpleGraph`,
`gi5_all_simpleGraph'`).

Each depends only on `propext`, `Classical.choice` and `Quot.sound`; `mem_subsR` and
`length_subsR_le` only on `propext` and `Quot.sound`, and `wf_mainProg`, `wf_allProg`,
`gi5Checked_wf` and `gi5AllChecked_wf` only on `propext`.

## Milestone 8 — the Babai–Cameron–Pálfy theorem (`PLAN-8.md`)

The Babai–Cameron–Pálfy theorem in the form of Helfgott's Theorem 2.3: a primitive group of
degree `n ≥ 2` all of whose simple sections have order at most `k` has order at most
`n^{3 k³ + 3 k² + 12 k + 1}`, solvable or not; and polynomial string isomorphism for such
groups. The group theory is in `GraphIso/Groups/` (namespace `GraphIso.Groups`, mathlib and
milestone 6 imports only); `primBounded_of_boundedSections` in `Luks/Bounded.lean`; the
concrete theorem in `Solver/LuksBounded.lean`. Milestone 6's affine reduction is factored out
of `card_le_of_isQuasiPreprimitive_of_isSolvable` (statement unchanged) as
`card_le_of_isQuasiPreprimitive_of_abelian`.

### Phase 1 — sections (`Groups/Sections.lean`)

| Statement | Name |
|---|---|
| **Bounded simple sections**: every simple quotient `H/M` of a subgroup `H ≤ G` has order at most `k` | `BoundedSections` |
| Images of subgroups onto simple groups | `BoundedSections.card_le` |
| Closure under injective maps, subgroups, surjective maps, extensions, finite products | `BoundedSections.of_injective`, `.subgroup`, `.of_surjective`, `.of_ker`, `.pi`, `boundedSections_of_subsingleton` |
| A finite group has sections of order at most its own | `boundedSections_card` |
| The primes dividing `\|G\|` are at most `k`; at most `k` of them | `BoundedSections.le_of_prime_dvd_card`, `BoundedSections.card_primeFactors_le` |
| `k! ≤ 2^{k²}` | `factorial_le_two_pow_sq` |

### Phase 2 — minimal normal subgroups and their factors (`Groups/MinimalNormal.lean`, `Groups/FactorAction.lean`, `Groups/Subdirect.lean`)

All relative to a subgroup `Y` of a finite group `X` (`Y = ⊤` for the usual notions).

| Statement | Name |
|---|---|
| Conjugates of subgroups | `cj`, `mem_cj`, `cj_mul`, `cj_one`, `card_cj` |
| Subgroups of `N` normalized by `N`; minimal normal subgroups of `Y`, which exist | `NNormal`, `nnormal_top_iff`, `IsMinNormal`, `exists_isMinNormal` |
| **A nonabelian minimal normal subgroup is the product of the `Y`-conjugates of a simple factor**: normalized by `N`, nonabelian simple, pairwise commuting, independent, with supremum `N`, permuted transitively by `Y` | `exists_simple_factors` |
| **The action on the factors**: `\|Y\| ≤ \|C_Y(N)\| (k! 2^k)^{\|F\|}` | `card_le_of_factors` |
| **Subgroups of a product of nonabelian simple groups of equal order `m` containing no factor**: `2^{\|ι\|} \|H\|² ≤ m^{2 \|ι\|}` | `killAt`, `suppOn`, `HasFactor`, `card_le_card_map_killAt_mul`, `exists_lift`, `not_hasFactor_two`, `two_pow_mul_card_sq_le` |

### Phase 3 — linear groups (`Groups/Radical.lean`, `Groups/NoAbelian.lean`, `Groups/BoundedLinear.lean`)

| Statement | Name |
|---|---|
| The join of a solvable subgroup and a solvable normal subgroup is solvable; the solvable radical | `isSolvable_sup`, `exists_radical` |
| The quotient by the radical has no nontrivial abelian normal subgroup | `eq_bot_of_abelian_normal_quotient` |
| Normal subgroups inherit the absence of normal `p`-subgroups | `eq_bot_of_normal_isPGroup_of_normal` |
| No nontrivial abelian normal subgroup; passes to centralizers of normal subgroups | `NoAbelianNormal`, `nnormal_centralizer`, `comm_cj`, `NoAbelianNormal.centralizer` |
| A nonabelian simple group is not a `p`-group: the `p′`-part of its order is at least `2` | `two_le_ordCompl_of_simple` |
| **No abelian normal subgroup: `\|Y\| ≤ (k! 2^k)^t` with `2^t` at most the `p′`-part of `\|Y\|`** | `exists_card_le_of_noAbelianNormal` |
| The `p′`-part of a linear group's order is at most `\|V\|^{3 s}` | `ordCompl_card_le_linear` |
| **Linear groups with bounded sections and no normal `p`-subgroup: `\|H\| ≤ \|V\|^{3 k³ + 3 k² + 12 k}`** | `card_le_of_boundedSections_linear` |

### Phase 4 — primitive groups (`Groups/PrimitiveBounded.lean`, `Luks/Bounded.lean`)

| Statement | Name |
|---|---|
| The affine case (in `Groups/PrimitiveSolvable.lean`) | `card_le_of_isQuasiPreprimitive_of_abelian` |
| The nonabelian case: `\|G\| ≤ n^{2 k² + 2 k + 1}` | `card_le_of_isQuasiPreprimitive_of_nonabelian` |
| **The Babai–Cameron–Pálfy theorem: quasiprimitive and primitive groups with simple sections of order at most `k` have order at most `n^{3 k³ + 3 k² + 12 k + 1}`** | `card_le_of_isQuasiPreprimitive_of_boundedSections`, `card_le_of_isPreprimitive_of_boundedSections` |
| **Groups with bounded sections have bounded primitive sections**: `PrimBounded G₀ (3 k³ + 3 k² + 12 k + 1)` | `primBounded_of_boundedSections` |

### Phase 5 — the concrete theorem (`Solver/LuksBounded.lean`)

| Statement | Name |
|---|---|
| **String isomorphism for groups with simple sections of order at most `k`**, at most `6640 (n + 1)^{9 k³ + 9 k² + 36 k + 8} + 60 L (n + 1)²` | `solve_luks_bounded` |

### Phase 6 — checks (`GraphIsoChecks/LuksBounded.lean`)

Interpreter runs of Luks's strategy against brute force and the default strategy, the order
computed from a Sims table, the cost within the bound of `solve_luks_bounded` for `k` the order
(`boundedSections_card`): `A₅` and `S₅` on five points, `A₅ ≅ PSL(2, 5)` on six points, with
and without solutions.

### Audit

The build lists the axioms of 19 more principal theorems: `BoundedSections.of_ker`,
`BoundedSections.pi`, `BoundedSections.card_primeFactors_le`, `exists_simple_factors`,
`card_le_of_factors`, `two_pow_mul_card_sq_le`, `isSolvable_sup`, `exists_radical`,
`eq_bot_of_abelian_normal_quotient`, `eq_bot_of_normal_isPGroup_of_normal`,
`NoAbelianNormal.centralizer`, `exists_card_le_of_noAbelianNormal`,
`card_le_of_boundedSections_linear`, `card_le_of_isQuasiPreprimitive_of_abelian`,
`card_le_of_isQuasiPreprimitive_of_nonabelian`,
`card_le_of_isQuasiPreprimitive_of_boundedSections`,
`card_le_of_isPreprimitive_of_boundedSections`, `primBounded_of_boundedSections`,
`solve_luks_bounded`. Each depends only on `propext`, `Classical.choice` and `Quot.sound`.

## Milestone 9 — graphs of every bounded valence (`PLAN-9.md`)

Luks's theorem: for every `Δ ≥ 2`, isomorphism of graphs of maximum degree at most `Δ` in time
polynomial in `n`. For every `k ≥ 2` with `(Δ − 1)! ≤ k` the layer groups of milestone 7's
reduction have simple sections of order at most `k`, so milestone 8's
`primBounded_of_boundedSections` bounds every string-isomorphism call. Milestone 7's layer
step, edge test, algorithm and matching take the constant `c` of the string-isomorphism calls
as a parameter (`LayerPrim Δ c`, see milestone 7's phases 4 and 5); milestone 7 is the case
`Δ = 5`, `c = 13`, with its protected statements unchanged.

### Phase 1 — sections of `p`-groups (`Groups/Sections.lean`)

| Statement | Name |
|---|---|
| A bound on sections may be raised | `BoundedSections.mono` |
| **A finite `p`-group has simple sections of order `p`** | `boundedSections_of_isPGroup` |

### Phase 2 — bounded layer groups (`Valence/Solvable.lean`, `Valence/Bounded.lean`)

| Statement | Name |
|---|---|
| **A point has at most `Δ − 1` twins**, for every `Δ` | `card_tw_le_pred` |
| The kernel of the restriction `A_{r+1} → A_r` has simple sections of order at most `(Δ − 1)!` | `boundedSections_ker` |
| **Every layer group has simple sections of order at most `k`**, for every `k ≥ 2` with `(Δ − 1)! ≤ k` (`A₀` is a `2`-group; extensions) | `boundedSections_autR` |
| **`LayerPrim Δ (3 k³ + 3 k² + 12 k + 1)`** for every `Δ` | `layerPrim_bounded` |

### Phase 3 — closed forms and the concrete theorems (`Solver/ValenceBounded.lean`)

| Statement | Name |
|---|---|
| A layer domain has fewer than `T = (N + 2)^Δ` points for `Δ ≥ 2`; `Δ, N ≤ T`; at most `T²` generators | `pow_add_succ_le`, `le_pow_facts`, `sq_le_pow`, `genBound_le_sq` |
| The other terms of a layer step and of the entries, as polynomials in `T` | `inputCost_le_pow`, `outCost_le_pow`, `levelsCost_le_pow`, `validCost_le_pow`, `subGCost_le_pow`, `glueCost_le_pow`, `compsCost_le_pow` |
| **Closed forms for every `Δ ≥ 2` and `c ≥ 1`**: one layer step `≤ 7300 (N + 2)^{Δ (3c + 5)}`; the edge test `≤ 7600 (2n + 2)^{Δ (3c + 5) + 1}`; the algorithm `≤ 7700 Δ (2n + 2)^{Δ (3c + 5) + 2}`; the checked entries `≤ 8100 Δ (2n + 2)^{Δ (3c + 5) + 2}` (connected) and `≤ 2300 Δ (2n + 2)^{Δ (3c + 5) + 4}` (all graphs) | `layerCost_le_pow`, `edgeCost_le_pow`, `mainCost_le_pow`, `checkedCostB_le_pow`, `allCheckedCostB_le_pow` |
| **Isomorphism of connected graphs of maximum degree `Δ` in polynomial time, for every `Δ ≥ 2`**, on every input: `none` exactly on invalid input (`GIValidB Δ`), otherwise `GIAnswer`, at cost at most `8100 Δ (2n + 2)^{Δ (9k³ + 9k² + 36k + 8) + 2}` for every `k ≥ 2` with `(Δ − 1)! ≤ k` | `gi_bounded_checked` |
| **The statement for mathlib's simple graphs**: connected, every degree at most `Δ` | `gi_bounded_simpleGraph`, `gi_bounded_simpleGraph'` |
| **Isomorphism of all graphs of maximum degree `Δ` in polynomial time, for every `Δ ≥ 2`** (`GIValidAllB Δ`), at cost at most `2300 Δ (2n + 2)^{Δ (9k³ + 9k² + 36k + 8) + 4}` | `gi_bounded_all_checked` |
| **The statement for mathlib's simple graphs**: every degree at most `Δ`, connected or not | `gi_bounded_all_simpleGraph`, `gi_bounded_all_simpleGraph'` |

### Phase 4 — checks (`GraphIsoChecks/ValenceBounded.lean`)

- **Kernel-evaluated runs** of the entries for `Δ = 6`, tied to `gi_bounded_checked` and
  `gi_bounded_all_checked` (with `k = 120`) by `runGIB_spec` and `runAllB_spec`: no points
  (cost 80) and one point (174) for the connected entry, no points (39) for the all-graphs
  entry.
- **Interpreter runs** against brute force, every returned isomorphism checked: `P₃` against a
  relabelling (50,699,515 units); three isolated points (1,209) and `2K₂` against `P₄`
  (3,194) with the all-graphs entry; a vertex of degree seven rejected by both entries. The
  costs are checked against `8100 Δ (2n + 2)^{44Δ + 2}` and `2300 Δ (2n + 2)^{44Δ + 4}`,
  below the closed forms, whose exponents (about `9.4 · 10⁷` for `k = 120`) are too large to
  evaluate.
- **A layer group that is not a `{2, 3}`-group**: the first layer step of `K₁,₆ ⊔ K₁,₆`
  (115,800,876 units) returns 71 generators of `A₁`, whose group has order
  `28800 = 2 · (5!)²` (from a Sims table): the root symmetry exchanging the stars, and
  `S₅ × S₅` on the two twin classes of five leaves.

### Audit

The build lists the axioms of 20 more principal theorems: `BoundedSections.mono`,
`boundedSections_of_isPGroup`, `card_tw_le_pred`, `boundedSections_ker`,
`boundedSections_autR`, `layerPrim_bounded`, `giBoundedChecked_wf`,
`RunsWithin.giBoundedChecked`, `giBoundedAllChecked_wf`, `RunsWithin.giBoundedAllChecked`,
`layerCost_le_pow`, `mainCost_le_pow`, `checkedCostB_le_pow`, `allCheckedCostB_le_pow`,
`gi_bounded_checked`, `gi_bounded_simpleGraph`, `gi_bounded_simpleGraph'`,
`gi_bounded_all_checked`, `gi_bounded_all_simpleGraph`, `gi_bounded_all_simpleGraph'`; and
milestone 7's `layerPrim_solvable` replaces `induced_isSolvable`. Each depends only on
`propext`, `Classical.choice` and `Quot.sound`; `giBoundedChecked_wf` and
`giBoundedAllChecked_wf` only on `propext`.

## Milestone 10 — Weisfeiler–Leman and the Design Lemma (`PLAN-10.md`)

The first stage of Babai's recursion (Helfgott §§2.3–2.6, 5.1; Babai §6.1): coherent
configurations, the `k`-ary Weisfeiler–Leman refinement as a costed canonical program, Fisher's
inequality, the large clique lemma, Babai's Design Lemma, and the Design Lemma as an algorithm
on a `k`-ary relational structure. Elementary throughout; no classification of finite simple
groups. Namespace `GraphIso.Coherent`.

### Phase 1 — configurations (`Coherent/Basic.lean`, `Coherent/Skeleton.lean`)

| Statement | Name |
|---|---|
| A `k`-ary configuration (Def. 2.5): the colour of a tuple determines its equality pattern and the colour of `x ∘ τ` for every `τ : Fin k → Fin k` | `IsConfig` |
| A `k`-ary coherent configuration (Def. 2.8): the number of points `z` with `c (update x j z) = r j` for all `j` depends only on `c x` | `IsCoherent` |
| A classical coherent configuration, with the intersection numbers `#{z \| c x z = r ∧ c z y = s}`; twins; cliques | `IsCoherent2`, `IsTwin`, `IsTwin2`, `IsClique` |
| Individualizing a list `x`: `skel1 c x u = c (x, u, …, u)`, `skel2 c x u v = c (x, u, v, …, v)`, the class `cls1 c x u` | `pad1`, `pad2`, `skel1`, `skel2`, `cls1` |
| Counting with any predicate on the colour vector (resp. the two colours) depends only on the colour | `IsCoherent.card_filter_pred`, `IsCoherent2.card_filter_pred` |
| **The individualized 2-skeleton of a `k`-ary coherent configuration is a classical coherent configuration** (Exercises 2.11, 2.13) | `isCoherent2_skel2` |
| **Its restriction to a vertex colour class is one** (Exercise 2.12) | `isCoherent2_restrict` |
| Individualizing is canonical | `skel1_relabel`, `skel2_relabel` |

### Phase 2 — Fisher, the large clique lemma, the Design Lemma

Files `Coherent/Fisher.lean`, `Coherent/LargeClique.lean`, `Coherent/Design.lean`.

| Statement | Name |
|---|---|
| **Fisher's inequality** (Prop. 2.19), repeated blocks allowed: every point in `r` blocks, every pair of distinct points in `l` blocks, `l < r` ⟹ at least as many blocks as points (an injective `ℚ`-linear map) | `fisher_inequality` |
| **The large clique lemma** (Lemma 5.2): a vertex colour class `C` with `2 \|C\| > \|V\|` on which all pairs of distinct points have one colour consists of pairwise twins | `isTwin2_of_large_clique` |
| **The Design Lemma** (Prop. 5.1, Babai Thm. 6.1.1), `k ≥ 2`, a natural threshold `t` with `\|V\| ≤ 2t + 1` in place of `α\|Γ\|` (a class has more than `α\|V\|` points iff more than `⌊α\|V\|⌋`, and `\|V\| ≤ 2⌊α\|V\|⌋ + 1` for every `α ≥ 1/2`, so this is Helfgott's whole range): if no set of more than `t` points consists of pairwise twins, some list `x` of fewer than `k` points has (a) an individualized vertex colouring with no class of more than `t` points, or (b) `x.length + 2 ≤ k`, a class of more than `t` points, and an individualized 2-skeleton that is not a clique on it | `design_lemma_of_le_succ` |
| The case `\|V\| ≤ 2t` (the form used by the checked entry) | `design_lemma` |

### Phase 3 — Weisfeiler–Leman, the model (`Coherent/WL.lean`)

| Statement | Name |
|---|---|
| Round 0 (input colour and equality pattern); the signature of a round (colour, colours of `x ∘ τ` for all `τ`, sorted vectors `vec c x z`); colours are ranks in the sorted distinct signatures; the decoding list | `sig0`, `sig`, `sigList`, `rank`, `wlInit`, `wlStep`, `wlIter`, `wl` |
| The number of colours grows at each round that does not stop, and is at most `m^k`; the refinement is stable after `m^k + 1` rounds | `wlStep_inv`, `numColours_le`, `wlStep_wlIter` |
| **The refinement is a coherent configuration** | `wl_isCoherent` |
| **The colour list decodes the input; the refinement refines it** | `wl_decode`, `wl_refines` |
| **Canonicity**: relabelling the input by `π` relabels the refinement by `π`, colour names included, and keeps the colour list | `wl_relabel` |
| **Isomorphism transfer**: `π` maps `c` to `d` iff it maps `wl c` to `wl d` and the colour lists agree; the refinement has the twins of the input | `wl_iso_iff`, `isTwin_wl_iff` |

### Phase 4 — programs

Files `Coherent/ListProg.lean`, `Coherent/Tuples.lean`, `Coherent/TuplesProg.lean`,
`Coherent/WLArray.lean`, `Coherent/WLProg.lean`.

| Statement | Name |
|---|---|
| Lexicographic three-way comparison encodes mathlib's order on lists; insertion is `List.orderedInsert`, insertion sort is `List.insertionSort`, sorting without repetition is `Finset.sort`, the position is `List.idxOf` | `lexCmp_eq`, `insertM_eq`, `sortM_eq`, `dedupSortM_eq`, `idxM_eq` |
| The programs for them, with costs and well-formedness | `RunsWithin.lexCmpProg`, `RunsWithin.insertProg`, `RunsWithin.sortProg`, `RunsWithin.dedupSortProg`, `RunsWithin.idxOfProg`, `RunsWithin.filterProg`, `wf_*` |
| Tuples are stored by their codes `enc x = ∑ⱼ xⱼ mʲ` (`finFunctionFinEquiv`); the digit lists in code order; the codes of `update x j z` and of `x ∘ τ` from a table of products | `tupList_eq`, `nbrRowM_eq`, `monoRowM_eq`, `patRowM_eq`, `infoAt_enc` |
| **A round on arrays is the round of the model**, and so is round 0; the iteration on arrays computes `wl` | `stepA_repSt`, `initA_eq`, `wlA_eq` |
| **The refinement as a program**: `wlProg k m col` returns `wlA k m col` at cost at most `wlCost k m`; the loop is paid by the potential `(m^k + 1 − #colours) (roundCost + 2)` | `RunsWithin.wlProg`, `wf_wlProg` |

### Phase 5 — the Design Lemma as an algorithm

Files `Coherent/DesignArray.lean`, `Coherent/DesignProg.lean`.

| Statement | Name |
|---|---|
| The codes of `(x, u, …, u)` and `(x, u, v, …, v)`; the individualized vertex colouring | `codePad1_eq`, `codePad2_eq`, `col1A_eq` |
| Two classes of more than `t ≥ m/2` points are equal | `cls1_eq_of_large` |
| **The test at a candidate is the Design Lemma's conclusion** (`DesignGood`), for `m ≤ 2t` | `goodA_iff`, `cliqueA_iff` |
| The candidates are the lists of fewer than `k` points; the search returns the first one where the test holds | `mem_cands`, `searchA_eq_some`, `searchA_eq_none` |
| The search as a program, at cost at most `searchCost k m` | `RunsWithin.searchProg`, `wf_searchProg` |

### Phase 6 — checked entries and closed forms (`Solver/Coherent.lean`)

| Statement | Name |
|---|---|
| With `A = m^k + 1`, `M = (m + 2)(k + 2)`, `K = k^k`: a signature `≤ 50 M² (K + 1)`, a comparison `≤ 38 M (K + 1)`, a round `≤ 210 A² M² (K + 1)`, the loop `≤ 489 A³ M² (K + 1)`, the tables `≤ 114 A M² (K + 1)`, the search `≤ 141 A M²` | `sigCost_le`, `ceSig_le`, `roundCost_le`, `wlRunCost_le`, `infoCost_le`, `searchCost_le` |
| **Closed forms** of the checked entries: `≤ 720 (m^k + 1)³ ((m + 2)(k + 2))² (k^k + 1)` and `≤ 1000 (m^k + 1)³ ((m + 2)(k + 2))² (k^k + 1)` | `wlCheckedCost_le`, `descentCheckedCost_le` |
| **The `k`-ary Weisfeiler–Leman refinement as a costed program**, on every input `(k, m, col)`: `none` exactly when `col` is not an array of `m^k` colours; otherwise the array of `wl k m (toFun col)` (of size `m^k`) and its colour list, at cost at most `720 (m^k + 1)³ ((m + 2)(k + 2))² (k^k + 1)` | `wl_checked` |
| **Descent from a relational structure**, on every input `(k, m, t, col)`: `none` exactly when `k < 2`, `2t < m` or `col` is not of size `m^k` (so the entry takes the thresholds `t ≥ m/2`: `t = ⌊αm⌋` with `α ≥ 1/2` qualifies unless `m` is odd and `⌊αm⌋ = (m − 1)/2`, that is `α < (m + 1)/(2m)`); `some none` only if `toFun col` has more than `t` pairwise twins; otherwise a list `x` of fewer than `k` points with `DesignGood (wl k m (toFun col)).1 t x` and its individualized vertex colouring; cost at most `1000 (m^k + 1)³ ((m + 2)(k + 2))² (k^k + 1)` | `descent_checked` |
| The restricted individualized 2-skeleton of the refinement is a classical coherent configuration; the outcome at `x` is canonical relative to `x` | `isCoherent2_wl_skel2`, `skel1_wl_relabel` |

### Phase 7 — checks (`GraphIsoChecks/Coherent.lean`)

- **Kernel-evaluated runs**, tied to `wl_checked` and `descent_checked` by `runWL_spec` and
  `runDescent_spec`: a constant colouring of the `1`-tuples of two points (cost 1195), the
  pairs of one point (746), the descent on one point, outcome (a) at the empty list (894).
- **Interpreter runs of the refinement** (`k = 2`) on the pair colourings of graphs `P₃`, `C₅`,
  `C₆`, `2K₃`, and (`k = 3`) on a ternary structure on `P₃`: each output is checked to be a
  coherent configuration by brute force over all pairs of tuples, to refine the input, and to
  be canonical (the refinement of a relabelled input is the relabelled refinement, with the
  same colour list). `C₆` and `2K₃` get different colour class sizes (`[6, 6, 12, 12]` and
  `[6, 12, 18]`).
- **Interpreter runs of the descent**: outcome (a) at the empty list on four points in two
  classes of two (`t = 2`); outcome (b) at the empty list on `C₅` (`t = 3`); `some none` on
  `K₄` (`t = 2`, four pairwise twins); `none` for `k = 1`, `2t < m` and a wrong array size.

### Audit

The build lists the axioms of 44 more principal theorems: `IsCoherent.card_filter_pred`,
`IsCoherent2.card_filter_pred`, `fisher_inequality`, `isTwin2_of_large_clique`, `isCoherent2_skel2`,
`isCoherent2_restrict`, `skel1_relabel`, `skel2_relabel`, `design_lemma_of_le_succ`, `design_lemma`,
`wlStep_wlIter`, `wl_isCoherent`, `wl_decode`, `wl_refines`, `wl_relabel`, `wl_iso_iff`,
`isTwin_wl_iff`, `lexCmp_eq`, `sortM_eq`, `dedupSortM_eq`, `idxM_eq`, `tupList_eq`, `infoAt_enc`,
`stepA_repSt`, `initA_eq`, `wlA_eq`, `RunsWithin.wlProg`, `wf_wlProg`, `goodA_iff`, `mem_cands`,
`searchA_eq_some`, `searchA_eq_none`, `RunsWithin.searchProg`, `wf_searchProg`, `wlChecked_wf`,
`descentChecked_wf`, `RunsWithin.wlChecked`, `RunsWithin.descentChecked`, `wlCheckedCost_le`,
`descentCheckedCost_le`, `wl_checked`, `descent_checked`, `isCoherent2_wl_skel2`,
`skel1_wl_relabel`. Each depends only on `propext`, `Classical.choice` and `Quot.sound`;
`skel1_relabel`, `skel2_relabel`, `sortM_eq` and `tupList_eq` only on `propext` and `Quot.sound`,
and the well-formedness lemmas `wf_wlProg`, `wf_searchProg`, `wlChecked_wf`, `descentChecked_wf`
only on `propext`.

## Milestone 11 — Split-or-Johnson (`PLAN-11.md`)

The second stage of Babai's recursion (Helfgott Thm. 5.3 with Props. 5.7 and 5.8; Babai §7
with the correction in Babai's note *Fixing the UPCC case of Split-or-Johnson*, January 2017),
**at the model level**: the procedures are computable Lean functions, with correctness,
canonicity and multiplicative-cost theorems; no running time is claimed (costed programs are
deferred to milestone 14). Canonicity relative to arbitrary choices (Babai, Def. 4.0.4) is
formalized by choice trees. Elementary throughout.
Namespaces `GraphIso.Coherent` (phases 1–3) and `GraphIso.SplitJohnson` (phases 4–8).

### Phase 1 — classical coherent configurations on a set (`Coherent/Classical.lean`, `Coherent/BipGraph.lean`)

| Statement | Name |
|---|---|
| A classical coherent configuration on `S : Finset R` (`IsCoherent2` on the subtype `↥S`); homogeneous; the off-diagonal colours; undirected `r`-adjacency within `S` and the `r`-component of `x` (computed by `\|S\|` rounds of closure); primitive (Def. 2.14: homogeneous, every off-diagonal colour graph connected); uniprimitive (primitive and not a clique) | `IsCoh2On`, `IsHomog`, `offCols`, `Adj`, `comp`, `mem_comp`, `IsPrimitive`, `IsUniprimitive` |
| Restriction to a union of vertex colour classes is coherent (Exercise 2.12) | `IsCoh2On.subset` |
| Counting with any predicate on the two colours depends only on the colour of the pair; out- and in-degrees in a colour depend only on the vertex colour (Exercise 2.17) | `IsCoh2On.card_filter_pred`, `IsCoh2On.outdeg`, `IsCoh2On.indeg`, `IsCoh2On.card_in_eq_out` |
| A colour of more than half of an out-neighbourhood is symmetric | `IsCoh2On.symm_of_large` |
| **No large clique** (Exercise 2.15), for a **homogeneous** configuration that is not a clique; homogeneity is needed (the orbital configuration of `Sym({0,1,2})` on `{0,1,2,3}` is a counterexample without it) | `IsCoh2On.not_isClique_of_large` |
| **Walk counts** (Exercise 2.16 (a)): the number of walks `x = x₀, …, x_k = y` in `S` with prescribed colours `c xᵢ₋₁ xᵢ = rᵢ` depends only on the colour of `(x, y)` | `walkCount`, `IsCoh2On.walkCount_eq` |
| Reachability in a colour graph depends only on the colour of the pair; the components of a colour graph all have the same size (Exercise 2.16 (b)), at least two points for an off-diagonal colour, at most half of `S` when the graph is disconnected | `IsCoh2On.reach_iff`, `IsCoh2On.card_comp_eq`, `IsCoh2On.two_le_card_comp`, `IsCoh2On.two_mul_card_comp_le` |
| **The contraction of a colour graph is semiregular** (Exercise 2.18) | `IsCoh2On.contract_deg_blocks`, `IsCoh2On.contract_deg_points` |
| The colour of a pair determines whether its points are twins with respect to a vertex colour class (Exercise 5.6) | `IsCoh2On.twin_iff`, `IsCoh2On.twinAll_iff` |
| **A common neighbour in the complement** (Exercise B.7): in a uniprimitive configuration, distinct `x, z` have `y` with `c x y ≠ c x z` and `c y z ≠ c x z` | `IsUniprimitive.exists_common` |
| Twin classes of bipartite graphs; **Exercise 5.4**: a nontrivial semiregular bipartite graph has no twin class of more than half of its first side; **Exercise 5.5**: splitting the second side of a graph without twins leaves one half with no twin class of `\|V₁\|/2 + 1` or more points | `twinCls`, `two_mul_card_twinCls_le`, `twin_split` |

### Phase 2 — Ray-Chaudhuri–Wilson (`Coherent/RCW.lean`)

| Statement | Name |
|---|---|
| Blocks containing `T`, and containing `I` while missing `J`, depend only on the sizes when `\|I\| + \|J\| ≤ t` (double counting) | `rcwCnt_eq_of_card`, `rcwLam_eq_of_card` |
| **The Ray-Chaudhuri–Wilson inequality** (Prop. 2.20): a family `A : B → Finset P` of `u`-subsets of `V`, repeated blocks allowed, with every `t`-subset in exactly `l ≥ 1` blocks, `2s ≤ t ≤ u`, `s + u ≤ \|V\|`, has at least `C(\|V\|, s)` blocks. Proof: the quadratic form `Σ_b (Σ_{S ⊆ A b} x_S)²` is a nonnegative combination of `Σ_{\|I\| = i} (Σ_{S ⊇ I} x_S)²`, `i ≤ s`, with a positive coefficient at `i = s`, so the incidence map on functions on `s`-subsets is injective | `ray_chaudhuri_wilson` |

### Phase 3 — Weisfeiler–Leman on any finite type (`Coherent/WLOn.lean`)

| Statement | Name |
|---|---|
| `wl` along an enumeration does not depend on the enumeration (`wl_relabel`); `wlOn k c` is `wl` along `Fintype.truncEquivFin` via `Trunc.lift` (computable), and evaluates at any enumeration | `wl_along_indep`, `wlOn`, `wlOn_eq`, `wlOn_eq'` |
| Coherence and twins pull back along equivalences | `IsCoherent.comp_equiv`, `isTwin_comp_equiv_iff` |
| **`wlOn` is a coherent configuration refining its input, with the same twins** | `wlOn_isCoherent`, `wlOn_refines`, `isTwin_wlOn_iff` |
| **Canonicity: `wlOn` is natural under every equivalence `V ≃ W`**, colour names included | `wlOn_natural` |

### Phase 4 — choice trees and outputs (`SplitJohnson/CTree.lean`, `SplitJohnson/Output.lean`)

| Statement | Name |
|---|---|
| Choice trees: leaves and nodes choosing from a finite set; reachable leaves, all reachable leaves satisfy `P`, liveness (every reachable node set nonempty), the number of root-to-leaf paths (Babai's multiplicative cost), bind, change of choice and output types | `CTree`, `Reach`, `AllLeaves`, `Live`, `count`, `leaves`, `bind`, `trans` |
| `AllLeaves` is "every reachable leaf"; a live tree has a reachable leaf; `count` bounds the number of leaves; bind and change of types preserve validity and liveness, `count (t.bind f) ≤ count t · B` when every `f o` has at most `B` paths | `allLeaves_iff_reach`, `Live.exists_reach`, `card_leaves_le`, `allLeaves_bind`, `live_bind`, `count_bind_le`, `allLeaves_trans`, `live_trans`, `count_trans` |
| The action of a group on trees (choices and outputs moved); it preserves reachability, validity, liveness and count; it commutes with canonical binds and with changes of types | `CTree.act`, `reach_act`, `allLeaves_act`, `live_act`, `count_act`, `act_bind`, `act_trans` |
| Colored partitions (colour and block map); **a colored `t`-partition of `V`** (Babai Def. 5.1.1: an admissible colored equipartition with blocks of at most `t` points); **a Johnson embedding** (a bijection `f` from `V₀ ⊆ V`, `\|V₀\| > t`, onto the `s`-subsets of a set `Λ` of nonempty pairwise disjoint cells, `2 ≤ s`, `2s ≤ \|Λ\|`); valid leaves; actions of `Sym(α)` | `CPart`, `IsColPart`, `JEmb`, `IsJohnson`, `ValidOut`, `Choice` |

### Phase 5 — Coherent Split-or-Johnson (`SplitJohnson/CoherentDef.lean`, `CoherentSpec.lean`, `Relabel.lean`)

| Statement | Name |
|---|---|
| The procedure (Helfgott's proof of Prop. 5.8, with Babai's corrected argument for a primitive `X[C₂]`, footnote 17): `X[C₁]` imprimitive ⟹ components of its least disconnected colour; `X[C₂]` imprimitive ⟹ a `w`-colouring, a block with small twin classes (choose `y` in it), or the contraction; `X[C₂]` primitive ⟹ choose `y`, then `(L_violet(y), L_blue(y); violet)` or the `y`-colouring | `cohSoj`, `CohOut`, `colPart`, `bipEdge`, `disconn` |
| **Coherent Split-or-Johnson** (Prop. 5.8): for a classical coherent configuration on `C₁ ∪ C₂` with vertex colour classes `C₁`, `C₂`, `\|C₂\| < \|C₁\|`, not constant on `C₁ × C₂`, `X[C₂]` not a clique: live, at most `\|C₂\|` paths, every leaf a colored `\|C₁\|/2`-partition of `C₁` or a bipartite graph `(W₁, W₂; A')` with `W₁ ⊆ C₁`, `\|C₁\| ≤ 2\|W₁\|`, `W₂` nonempty pairwise disjoint subsets of `C₂` (ideal points: Helfgott writes `V₂ ⊆ C₂`, but his contraction produces blocks), `2\|W₂\| ≤ \|C₂\|`, and no twin class of `W₁` above `\|W₁\|/2` | `coherent_split_or_johnson`, `CohValid` |
| **It is canonical** under every permutation of the point type | `coherent_split_or_johnson_relabel` |

### Phase 6 — Bipartite Split-or-Johnson (`SplitJohnson/Bipartite*.lean`, `DLAux.lean`, `BipRelabelAux.lean`)

| Statement | Name |
|---|---|
| The procedure: one level `bstep` with the recursive calls supplied, `bsoj` by well-founded recursion on the number of cells; twins and degrees, the Johnson test, then the base case (enumerate `V₂` when `v² ≤ 27 ⌈log₂ 2t⌉³`; Helfgott takes it first, but the two earlier steps make no choice), the `d`-ary structure (`d = min(s, 6 ⌈log_v n₁⌉)`), the Design Lemma's choice, `dlCont` (thirds, the classical refinement on `V₁' ⊔ V₂`, Coherent Split-or-Johnson and the union cells), dropped pieces | `bsoj`, `bstep`, `dlCont`, `cohCont`, `shrink`, `enums`, `nbrCode`, `twinPart`, `tfDeg`, `bigDegs`, `sOf`, `fOf`, `arity`, `daryCol`, `bigTwins`, `pickSide`, `selThird`, `DLGood`, `cohOn`, `code`, `cellOf`, `addPiece`, `withPiece` |
| The invariant (cells nonempty and pairwise disjoint, `\|V₂\| ≤ t`, `\|V₁\| + 2 ≤ 2t`, `t < \|V₁\|`, twin classes of at most `t`); dropped pieces and colourings preserve validity | `BInv`, `colPart_valid`, `isColPart_addPiece`, `isJohnson_mono`, `withPiece_valid`, `count_withPiece` |
| **The Johnson case**: the neighbourhoods of the points without twins of a large degree are distinct `s`-subsets, `2 ≤ s ≤ v/2`, and onto when there are `C(v, s)` of them | `johnson_valid` |
| **The `d`-ary structure is not symmetric** (for `d = 6j < s` by Ray-Chaudhuri–Wilson: `n₁ ≥ C(v, 3j) > v^j ≥ n₁`, using `v^k ≤ C(v, k) k^k` and `v² > 27 j³`); the Design Lemma's choice exists | `bigTwins_card_lt`, `invariant_of_forall_isTwin`, `pow_le_choose_mul_pow`, `choose_gt_of_cube`, `two_le_arity`, `exists_dlGood` |
| **After the choice**: `selThird` takes more than a third and at most two thirds; the classical refinement is coherent and refines the initial colours; every branch of `dlCont` is valid given valid recursive calls | `selThird_spec`, `isCoherent2_pair`, `isCoh2On_cohOn`, `cohOn_refines`, `cellOf_disjoint`, `isColPart_toLeft`, `third_valid`, `contB_valid`, `cohCont_valid`, `dlCont_valid` |
| Validity of one level and of the recursion | `bstep_valid`, `base_valid`, `twinPart_valid`, `bsoj_valid` |
| **The multiplicative cost**: with `\|V₂\| ≤ t`, `\|V₁\| ≤ 2t`, at most `(64 (t + 1)^13)^{lvl v} · B₀^{B₀}` paths (`B₀ = ⌊√(27 ⌈log₂ 2t⌉³)⌋`), hence at most `2^{128 (⌈log₂ t⌉ + 2)²}`; Coherent Split-or-Johnson has at most `max 1 \|C₂\|` paths unconditionally | `bsoj_count_le`, `BCount.count_bsoj_le_cntF`, `BCount.count_cohSoj_le`, `BCount.cntF_le` |
| **Bipartite Split-or-Johnson** (Prop. 5.7): for `V₂` nonempty pairwise disjoint cells, `\|V₂\| ≤ t`, `\|V₁\| + 2 ≤ 2t`, `t < \|V₁\|`, twin classes of `V₁` of at most `t` points: live, at most `2^{128 (⌈log₂ t⌉ + 2)²}` paths, every leaf a colored `t`-partition of `V₁` or a Johnson embedding in `V₁` on more than `t` points | `bipartite_split_or_johnson` |
| **It is canonical** under `Sym(α)` acting on points and cells together | `bipartite_split_or_johnson_relabel`, `BipRelabel.bstep_relabel`, `BipRelabel.dlCont_relabel` |

### Phase 7 — Split-or-Johnson (`SplitJohnson/MainDef.lean`, `SplitJohnson/Main.lean`)

| Statement | Name |
|---|---|
| The procedure: choose `x`; the colouring by `c x ·`; if a class `C_aqua` has more than `t` points, the least pair (`beige`, `cyan`) of colours other than `aqua` with `c z y = cyan` for some `z ∈ C_aqua`, `y ∈ C_beige`; Bipartite Split-or-Johnson on `(C_aqua, {{y}}; cyan)`; colored partitions extended by the classes of `c x ·` | `soj`, `sojAt`, `extendPart` |
| The bipartite input satisfies the invariant (semiregular by coherence, nonempty, not complete by the degree bound, Exercise 5.4) | `MainValid.main_case`, `MainValid.sojAt_spec` |
| **Split-or-Johnson** (Thm. 5.3): for a uniprimitive classical coherent configuration `c` on a finite type `Γ` and `t` with `\|Γ\| + 2 ≤ 2t`, `t < \|Γ\|` (Helfgott's `α` is `t = ⌊α\|Γ\|⌋`, covered when `\|Γ\| + 2 ≤ 2⌊α\|Γ\|⌋`; for `α = 2/3` when `\|Γ\| = 6` or `\|Γ\| ≥ 8`): live, at most `2^{129 (⌈log₂ \|Γ\|⌉ + 2)²}` paths (`\|Γ\|^{O(log \|Γ\|)}`), every leaf a colored `t`-partition of `Γ` or a Johnson embedding in `Γ` on more than `t` points | `split_or_johnson` |
| **It is canonical** under `Sym(Γ)`, an equality of trees; a relabelling carries reachable leaves to reachable leaves | `split_or_johnson_relabel`, `MainRelabel.sojAt_relabel`, `split_or_johnson_reach` |

### Phase 8 — checks (`GraphIsoChecks/SplitJohnson.lean`)

- **Theorem 5.3** end to end on the Petersen graph (`t = 6`: 10 leaves, each the colouring by
  `c x ·`) and the Clebsch graph (`t = 9`: the non-neighbours of `x` are the large class, and
  Bipartite Split-or-Johnson recognizes `J(5, 2)`: 16 leaves, all Johnson embeddings). Inputs are
  checked to be uniprimitive (`uniprimB_spec`) coherent configurations; every leaf is checked
  valid; the count is the number of leaves; canonicity is checked at every `x` for a
  relabelling.
- **Proposition 5.8** on the orbital configurations of `Sym(5)` on ordered pairs and 2-subsets
  (`X[C₁]` imprimitive) and of `Sym(7)` on 3-subsets and 2-subsets (both sides primitive: one
  choice `y`, 21 leaves): hypotheses checked, every leaf valid, count at most `\|C₂\|`.
- **Proposition 5.7** on incidence graphs, hypotheses checked: the 3-subsets of a 7-set give one
  Johnson leaf `J(7, 3)`; the 2-subsets of a 6-set less one give the base case (720 leaves).
- Not run: the deeper branches of Prop. 5.7. At sizes that can be run the base case applies
  (`v² ≤ 27 ⌈log₂ 2t⌉³`) whenever the Johnson test fails, and the `d`-ary Weisfeiler–Leman step
  is a polynomial of degree about `6d`; these branches are covered by the proofs only.

### Audit

The build lists the axioms of 40 more principal theorems: `ray_chaudhuri_wilson`, `wlOn_eq`,
`wlOn_isCoherent`, `wlOn_refines`, `isTwin_wlOn_iff`, `wlOn_natural`, `mem_comp`,
`IsCoh2On.subset`, `IsCoh2On.symm_of_large`, `IsCoh2On.not_isClique_of_large`,
`IsCoh2On.reach_iff`, `IsCoh2On.walkCount_eq`, `IsCoh2On.card_comp_eq`,
`IsCoh2On.two_le_card_comp`, `IsCoh2On.two_mul_card_comp_le`, `IsCoh2On.twin_iff`, `IsCoh2On.twinAll_iff`,
`IsCoh2On.contract_deg_blocks`, `IsCoh2On.contract_deg_points`, `IsUniprimitive.exists_common`,
`two_mul_card_twinCls_le`, `twin_split`, `CTree.reach_act`, `CTree.count_act`,
`CTree.count_bind_le`, `CTree.act_bind`, `CTree.act_trans`, `coherent_split_or_johnson`,
`coherent_split_or_johnson_relabel`, `johnson_valid`, `bigTwins_card_lt`, `exists_dlGood`,
`dlCont_valid`, `bsoj_valid`, `bsoj_count_le`, `bipartite_split_or_johnson`,
`bipartite_split_or_johnson_relabel`, `split_or_johnson`, `split_or_johnson_relabel`,
`split_or_johnson_reach`. Each depends only on `propext`, `Classical.choice` and `Quot.sound`.

## Milestone 12 — alternating quotients and the CFSG-free interfaces (`PLAN-12.md`)

The group theory of alternating quotients (Babai §§8.1, 8.3; Helfgott §4.1) and the effect of a
colouring on `t`-subsets (Babai §5.2). The two CFSG-dependent results of Babai's analysis
enter as explicit hypotheses in their weak CFSG-free form (`PLAN-12.md` §1 lists every use of
CFSG and its replacement; §2 gives the argument replacing Cameron's theorem). Milestones 15–16
discharge them (`altQuotientIso_pyber`; `transitivityBound_quad`, a quadratic rather than linear
transitivity bound, used through `QPHypJ`). Namespace `GraphIso.AltQuot`; mathlib imports only.

### Phase 1 — interfaces (`AltQuot/Interfaces.lean`)

| Statement | Name |
|---|---|
| **Helfgott's Lemma 4.1 with threshold function `K`** (Babai Lemma 8.2.4; CFSG-free: Pyber's Lemma 12 with `K n = max C ((⌊log₂ n⌋ + 1)⁵)`): every epimorphism from a primitive permutation group of degree `n` onto `Alt(k)`, `k ≥ K n`, is injective | `AltQuotientIso` |
| **Wielandt's bound with threshold function `T`** (`t < 3 ln k`): a `t`-transitive permutation group of degree `k ≥ t` not containing `Alt(k)` has `t ≤ T k` | `TransitivityBound` |
| **Both interfaces are satisfiable** (useless thresholds): `K n = n + 1` (`\|G\| ≤ n! < (n + 1)!/2`), `T k = k` | `altQuotientIso_succ`, `transitivityBound_id` |

### Phase 2 — alternating groups and subdirect products (`AltQuot/Alternating.lean`, `AltQuot/Subdirect.lean`)

| Statement | Name |
|---|---|
| `Alt(Λ)` is perfect for `\|Λ\| ≥ 5` | `alternatingGroup_commutator` |
| Every proper subgroup of `Alt(Λ)` has index at least `\|Λ\|`; every subgroup of `Sym(Λ)` not containing `Alt(Λ)` has index at least `\|Λ\|` (`\|Λ\| ≥ 5`) | `card_le_index_of_ne_top`, `card_le_index_of_not_le` |
| **Simple quotient of a subdirect product** (Babai Lemma 8.1.1): normal subgroups `M i` with trivial intersection and an epimorphism onto a nonabelian simple group — some `M i` lies in the kernel | `exists_le_ker_of_simple` |

### Phase 3 — affected points (`AltQuot/Affected.lean`, `AltQuot/Unaffected.lean`)

Throughout `G : Subgroup (Perm Ω)`, `k = \|Λ\|`, and the interface `AltQuotientIso K` is a hypothesis with `K` monotone.

| Statement | Name |
|---|---|
| Giant representations (`Alt(Λ) ≤ φ(G)`); affected points (`Alt(Λ) ≰ φ(G_x)`, Babai Def. 8.3.4) | `IsGiant`, `IsAffected` |
| **Transitive groups** (Babai Lemma 8.3.1, Helfgott Lemma 4.3 (a)): `G` transitive, `φ` onto `Alt(Λ)`, `5 ≤ k`, `K \|Ω\| ≤ k`, `\|Ω\| < k!/2` ⟹ `φ(G_x) ≠ Alt(Λ)` for every `x` | `stabilizer_map_ne_top` |
| **Some point is affected** (Lemma 8.3.3, Lemma 4.3 (b)): orbits of at most `N` points, `K N ≤ k`, `N < k!/2` | `exists_affected` |
| **The Unaffected Stabilizer Theorem** (Thm. 8.3.5, Prop. 4.4 (a)): for a giant representation, under the hypotheses of the previous row, `Alt(Λ) ≤ φ(G_(D))` with `D` the unaffected points | `unaffected_stabilizer` |
| **Orbits of the kernel** (Prop. 8.3.6): `φ` onto `H`, `y ∈ x^G` ⟹ `\|y^{ker φ}\| · [H : φ(G_x)] = \|x^G\|` | `card_orbit_ker_mul_index` |
| **The Affected Orbit Lemma** (Cor. 8.3.7, Prop. 4.4 (b)): giant `φ`, `k ≥ 5`, `x` affected ⟹ `k · \|x^{ker φ}\| ≤ \|x^G\|` | `affected_orbit` |

### Phase 4 — colourings of `t`-subsets (`AltQuot/Subsets.lean`)

| Statement | Name |
|---|---|
| **The binomial inequality** (Babai Prop. 5.2.3): `t₁, t₂ ≥ 1`, `2(t₁ + t₂) ≤ m₁ + m₂` ⟹ `3 C(m₁, t₁) C(m₂, t₂) ≤ 2 C(m₁ + m₂, t₁ + t₂)` | `choose_mul_choose_le` |
| Mixed `t`-subsets (Lemma 5.2.1 (a)): if `2t ≤ m` and `T` meets two colour classes, at most `(2/3) C(m, t)` subsets have the intersection numbers of `T` | `SameCounts`, `card_sameCounts_le` |
| Monochromatic `t`-subsets (Lemma 5.2.1 (b)): `C(d, t) m^t ≤ d^t C(m, t)` for `d ≤ m` | `choose_mul_pow_le` |
| Colourings without large classes (Cor. 5.2.2): classes of at most `a` points, `1 ≤ t`, `2t ≤ m` ⟹ every class of `t`-subsets has `3·size ≤ 2 C(m, t)` or `m·size ≤ a C(m, t)` | `card_sameCounts_le_of_le` |

### Phase 5 — checks (`GraphIsoChecks/AltQuot.lean`)

The interfaces are inhabited; the binomial inequality (all `m₁, m₂ < 9`, `1 ≤ t₁, t₂ < 5`) and
Lemma 5.2.1 (b) (`d ≤ m < 9`, `t < 6`) are kernel-checked on small ranges, with the tight case
`m₁ = m₂ = 2`, `t₁ = t₂ = 1`; the Unaffected Stabilizer Theorem is instantiated at the witness
interface `K n = n + 1`, where it is vacuous — the reason the quasipolynomial threshold of
Pyber's Lemma 12 (milestone 15) is needed.

### Audit

The build lists the axioms of 15 more principal theorems: `altQuotientIso_succ`,
`transitivityBound_id`, `alternatingGroup_commutator`, `card_le_index_of_ne_top`,
`card_le_index_of_not_le`, `exists_le_ker_of_simple`, `stabilizer_map_ne_top`, `exists_affected`,
`unaffected_stabilizer`, `card_orbit_ker_mul_index`, `affected_orbit`, `choose_mul_choose_le`,
`card_sameCounts_le`, `choose_mul_pow_le`, `card_sameCounts_le_of_le`. Each depends only on
`propext`, `Classical.choice` and `Quot.sound`. The interfaces `AltQuotientIso` and
`TransitivityBound` are definitions (`Prop`s), never axioms: every theorem that uses one takes it
as an explicit hypothesis.

## Milestone 13 — local certificates and their aggregation (`PLAN-13.md`)

Babai's method of local certificates (Babai §10.1, Thm. 10.1.3; Helfgott §6.1) and their
aggregation (Helfgott §6.2), as mathematics: the certificates are defined from the group, the
giant representation and the string; the recursive computation of the certificates and its
cost belong to milestone 14. Namespace `GraphIso.Certificates`. Throughout,
`G : Subgroup (Perm Ω)`, `φ : G →* Perm Γ`, `x : Ω → L`, and `σ ∈ G` acts on strings by
`smulStr σ x = x ∘ σ⁻¹`.

### Phase 1 — setting and the beard (`Certificates/Basic.lean`, `Certificates/Beard.lean`)

| Statement | Name |
|---|---|
| The setwise stabilizer `G_A = φ⁻¹(Sym(Γ)_A)` and its restriction `ψ_A : G_A →* Sym(A)` | `stabA`, `psiA` |
| `Aut^W_H(x)`: the `h ∈ H` with `h • W = W` preserving `x` on `W` (Babai's `Aut_H(x^W)`); `Aut_G(x) = Aut^Ω_G(x)` | `autW`, `autG` |
| Affected points `Aff(H) = {i \| Alt(A) ≰ ψ_A(H_i)}` (Babai Def. 10.1.4); giant (`Alt(A) ≤ ψ_A(H)`); full (`Alt(A) ≤ ψ_A(Aut_{G_A}(x))`, Def. 10.1.2) | `aff`, `IsGiantOn`, `IsFull` |
| **The beard** (procedure LocalCertificates, lines 01–05): `W₀ = ∅`, `H₀ = G_A`; while `ψ_A(H_i)` is a giant, `W_{i+1} = W_i ∪ Aff(H_i)`, `H_{i+1} = Aut^{W_{i+1}}_{H_i}(x)`; `W(A)`, `H(A)` the values at step `\|Ω\|` | `beardStep`, `beard`, `beardW`, `beardH` |
| The iteration is constant from step `\|Ω\|` on | `beard_stable` |
| `W_i` is `H_i`-invariant and `H_i` preserves `x` on it | `beardH_le_autW` |
| `Aut_{G_A}(x) ≤ H_i` for every `i` | `autW_univ_le_beard` |
| **The window group**: `H(A) = Aut^{W(A)}_{G_A}(x)` | `beardH_eq_autW` |
| If `H(A)` is a giant on `A`, `Aff(H(A)) ⊆ W(A)` | `aff_subset_beardW` |

### Phase 2 — local certificates (`Certificates/Local.lean`)

`Thresholds K n k` collects milestone 12's hypotheses for `n = |Ω|` and `k = |A|`:
`AltQuotientIso K`, `K` monotone, `5 ≤ k`, `K n ≤ k`, `n < k!/2`.

| Statement | Name |
|---|---|
| **Certificate of fullness** (Claim 10.1.6): if `ψ_A(H(A))` is a giant, `K(A) = H(A)_(Ω \ W(A))` satisfies `K(A) ≤ Aut_G(x)` and `Alt(A) ≤ ψ_A(K(A))` | `certK`, `cert_full` |
| **Certificate of non-fullness** (Claim 10.1.7): otherwise `M(A) = ψ_A(H(A))` satisfies `Alt(A) ≰ M(A)` and `ψ_A(Aut_{G_A}(x)) ≤ M(A)` | `certM`, `cert_not_full` |
| **The certificates decide fullness** (Thm. 10.1.3): `A` full ⟺ `ψ_A(H(A))` a giant | `isFull_iff` |
| **The kernel on the new window** (Cor. 8.3.7 applied to `H_i`): `ψ_A(H_i)` a giant, `\|A\| ≥ 5`, `u ∈ Aff(H_i)` ⟹ `\|A\| · \|u^{H_i ∩ ker ψ_A}\| ≤ \|u^{H_i}\|` | `kernel_orbit` |

### Phase 3 — canonicity (`Certificates/Relabel.lean`)

| Statement | Name |
|---|---|
| **The beard is canonical** (Prop. 10.1.8 (v)): for `(σ • x, φ(σ) • A)`, every `W_i` is moved by `σ` and every `H_i` (in `G`) is conjugated by `σ` | `beard_relabel` |
| Giant-ness of `H(A)`, fullness and `K(A)` are canonical | `isGiantOn_relabel`, `isFull_relabel`, `certK_relabel` |
| `M(A)` is conjugated by the bijection `A → φ(σ) • A` | `certM_relabel` |

### Phase 4 — aggregation (`Certificates/Cases.lean`, `Certificates/Aggregate.lean`)

For test sets of size `k`, `F(x)` is the subgroup of `G` generated by the `K(A)` with `|A| = k`
and `ψ_A(H(A))` a giant, and `S` the support of `φ(F)` on `Γ`. Cases 1 and 2 are stated for an
arbitrary permutation group `P` (in the application, `P = φ(F)` or the group it induces on an
orbit).

| Statement | Name |
|---|---|
| `F(x) ≤ Aut_G(x)` (under `Thresholds`) | `fullGroup`, `fullGroup_le_autG` |
| `F` and `S` are canonical: `F(σ • x) = σ F(x) σ⁻¹`, `supp(σ F σ⁻¹) = φ(σ) • supp F` | `fullGroup_relabel`, `supp`, `supp_conj` |
| **Case 1**: if the moved points are at least half of `Γ` and every orbit has at most half of the points, the orbit colouring (orbits as blocks, the fixed points as one block; such a colouring exists) is a colored `⌊m/2⌋`-partition (milestone 11's `IsColPart`) | `IsOrbitPart`, `exists_orbitPart`, `orbitPart_valid` |
| **Case 2**: an orbit of more than half of the points is unique | `large_orbit_unique` |
| **Case 2b, the degree of transitivity**: a transitive `P` not containing `Alt(Φ)` is `d`-transitive and not `(d+1)`-transitive for some `d` with `1 ≤ d`, `d + 2 ≤ \|Φ\|` and `d ≤ T \|Φ\|` (under `TransitivityBound T`) | `exists_degree` |
| **Case 2b**: `P` `d`-transitive, not `(d+1)`-transitive, `1 ≤ d`, `d + 1 ≤ \|Φ\|`; the pointwise stabilizer of any `d − 1` distinct points is transitive and not doubly transitive on the rest | `fixing_transitive_not_two` |
| The orbital configuration of a transitive, not doubly transitive group is a homogeneous classical coherent configuration (milestone 11's `IsCoh2On`) that is not a clique | `orbital_config` |
| **Case 3**: colour the `k`-tuples of `Γ \ S` by the equivalence of certificates (Helfgott (12): some `g ∈ G` maps `T` to `T'` pointwise through `φ` and `x^{W(T)}` to `x^{W(T')}`; tuples with repetitions form one colour). No `k` points of `Γ \ S` are pairwise twins | `CertIso`, `SameColour`, `no_large_twins` |

### Phase 5 — checks (`GraphIsoChecks/Certificates.lean`)

The beard starts from `(∅, G_A)` and is constant after `|Ω|` steps; `Thresholds (· + 1) n k`
holds for `5 ≤ k`, `n + 1 ≤ k` (`thresholds_succ`); `cert_full`, `isFull_iff`,
`fullGroup_le_autG` and `no_large_twins` are instantiated at that witness interface, where they
are vacuous for giant representations (the witness forces `k > |Ω|`); `exists_degree` is
instantiated at the witness `T k = k`.

### Audit

The build lists the axioms of 24 more principal theorems: `beard_stable`, `beardH_le_autW`,
`autW_univ_le_beard`, `beardH_eq_autW`, `aff_subset_beardW`, `cert_full`, `cert_not_full`,
`isFull_iff`, `kernel_orbit`, `beard_relabel`, `isGiantOn_relabel`, `isFull_relabel`,
`certK_relabel`, `certM_relabel`, `exists_orbitPart`, `orbitPart_valid`, `large_orbit_unique`,
`exists_degree`, `fixing_transitive_not_two`, `orbital_config`, `fullGroup_le_autG`, `fullGroup_relabel`,
`supp_conj`, `no_large_twins`. Each depends only on `propext`, `Classical.choice` and
`Quot.sound`.

## Milestone 14, stage 14a — the recursion's mathematics (`PLAN-14.md` §5)

`PLAN-14.md` fixes the CFSG-free main recursion. An instance may carry a **labelled hint**: a
base `Γ`, a representation `ψ : G → Sym(Γ)`, and labels `lab : W → 2^Γ` that are equivariant
and not constant on the window `W`. Each **macro-step** (M0–M5) reduces the group and coarsens
the hint, and every step is paid for by the **potential**
`pot Q b n m = n² (m + 1) Q^{b (κ(m) + 4 (λ(n) + 6)²)}`, with `κ(m) = ⌊log₂ m⁵⌋` and
`λ(n) = ⌊log₂ n⌋`. Stage 14a proves the mathematics the macro-steps rely on. It adds no
programs: stages 14b–14j do (`PLAN-14.md` §4). Namespace `GraphIso.Recursion`, directory `GraphIso/Recursion/`.

### Phase 1 — hints (`Recursion/Hint.lean`)

| Statement | Name |
|---|---|
| Equivariant, non-constant labels; invariant and transitive windows; fibres | `Equivar`, `NonConst`, `IsHint`, `Invariant`, `Transitive`, `fiber` |
| Fibres are blocks; under transitivity each fibre has at most `\|W\|/2` points | `card_fiber_smul`, `card_fiber_le` |
| A subset of the window with constant labels has at most `\|W\|/2` points | `card_le_of_const` |
| An element fixing every label keeps points in their fibres; hints restrict to subgroups and subwindows | `lab_smul_of_fix`, `IsHint.restrict` |
| **Children of a macro-step**: hinted instances are transitive on their windows; after a reduction `H ≤ G`, every `H`-orbit keeps the hint or has at most `\|W\|/2` points | `orbit_child` |

### Phase 2 — coarsenings (`Recursion/Coarsen.lean`)

| Statement | Name |
|---|---|
| Restriction of a representation to an invariant finite set; the induced action on subsets; labels inside a set | `restrictHom`, `setAct`, `subLab` |
| **M1**: labels `lab ∩ Γ'` for an invariant `Γ'` form a hint where not constant; of finitely many sets covering `Γ`, one gives non-constant labels | `hint_inter`, `exists_nonConst_inter` |
| **M2a**: for a block system `Ψ` of a transitive `ψ` and labels not equidistributed over `Ψ`, the block labels (blocks met, or blocks of least intersection) form a hint on `Ψ`; labels do not grow; `2\|Ψ\| ≤ \|Γ\|` for blocks of at least two points | `IsBlockSys`, `blockLabel`, `hint_blockLabel`, `card_blockLabel_le`, `card_blockSys_le` |
| **M2b**: for equidistributed labels, on every orbit of the stabilizer of a block `B₀` the labels `lab ∩ B₀` form a hint | `blockStab`, `hint_blockStab` |
| **Johnson union**: for a Johnson structure `V₀ ≅ Λ^{(s)}` preserved by `ψ`, the union of the `s`-subsets of `Λ` labelling `lab u ∩ V₀` forms a hint on `Λ` where not constant; if both it and `lab ∖ V₀` are constant on an orbit, every element fixing the cells of the union fixes every label; `\|jUnion\| ≤ t s`; `\|Λ\|(\|Λ\| − 1) ≤ 2\|V₀\|` | `jUnion`, `hint_jUnion`, `fix_of_jUnion_const`, `card_jUnion_le`, `card_cells` |

### Phase 3 — primitive quotients (`Recursion/Primitive.lean`)

| Statement | Name |
|---|---|
| **The giant test**: `Alt(Γ) ≤ P` iff `P` is `(\|Γ\| − 2)`-transitive | `alt_le_iff` |
| A group containing `Alt(Γ)`, `\|Γ\| ≥ 3`, is transitive on the subsets of each size | `exists_smul_eq_of_alt_le` |
| The stabilizer of a block of a transitive group is transitive on the block | `exists_blockStab_smul_eq` |
| The orbital configuration of a primitive, not doubly transitive group is a classical coherent configuration that is uniprimitive: the hypotheses of `split_or_johnson` | `orbital_uniprimitive` |
| **Canonical colour names** (Case 2b): the 2-ary Weisfeiler–Leman refinement of one orbital (`0` diagonal, `1` the orbital, `2` otherwise) is natural with its colour names; for a transitive, not doubly transitive group it is coherent, homogeneous, not a clique and invariant; for a primitive group it is uniprimitive. In general (Split-or-UPCC on the configuration), either the least disconnected colour gives a colored `⌊\|Φ\|/2⌋`-partition by its components, or the refinement is uniprimitive | `relCol`, `wlRel`, `wlRel_natural`, `wlRel_spec`, `wlRel_uniprimitive`, `wlRel_split_or_uniprimitive` |

### Phase 4 — progress (`Recursion/Progress.lean`)

| Statement | Name |
|---|---|
| For a group preserving a colored `t`-partition of `V`, an orbit `O ⊆ V` with at least two points has at most `t` points, or at most `\|V\|/2`, or is cut by the blocks into an invariant partition with at least two parts of at least two points | `colPart_orbit` |
| For a Johnson structure, an orbit lies in `V₀` or misses it with fewer than `\|V\| − t` points | `johnson_orbit` |

### Phase 5 — coset decompositions (`Recursion/Align.lean`)

| Statement | Name |
|---|---|
| Canonical structures (local to the window, equivariant); isomorphisms carry `X x` to `X y` | `Canonical`, `iso_transporter` |
| **Alignment**: if `σ ∈ G` carries `X x` to `X y`, `iso W 1 G x y = iso W σ G₁ x y` with `G₁ = ψ⁻¹(Stab(X x))` | `stabPre`, `iso_eq_align` |
| **Choice trees**: isomorphisms carry reachable leaves for `x` to reachable leaves for `y` | `iso_reach` |
| For a tree fixed by `ψ(G)`, the stabilizer of a reachable leaf has index at most the count | `index_stab_le_count` |

### Phase 6 — the pullback (`Recursion/Pullback.lean`)

| Statement | Name |
|---|---|
| If `Alt(Φ) ≤ r(F)`, every element is `k f` or `τ k f` (`k ∈ ker r`, `f ∈ F`, `τ` odd on `Φ`) | `cover_of_alt_le`, `cover_of_alt_le_even` |
| `iso W 1 H x y = (iso W 1 K x y ∪ iso W τ K x y) * F`, and the automorphisms are generated by those of `K`, of `τ K`, and `F` | `iso_pullback`, `aut_pullback` |
| `2 C(a, j) ≤ C(m, t)` for `2a ≤ m`, `j ≤ t`, `1 ≤ t`, `2t ≤ m` | `two_mul_choose_le` |
| Under a giant base with labels of size `t ≤ \|Γ\|/2`, every orbit of a subgroup fixing `Φ` (`2\|Φ\| > \|Γ\|`) pointwise has at most half of the window | `card_orbit_le_half` |

### Phase 7 — the potential (`Recursion/Potential.lean`)

| Statement | Name |
|---|---|
| `κ`, `λ`, the potential with and without a hint; `κ` drops by two at three quarters | `kap`, `lam`, `pot`, `potO`, `kap_add_two_le`, `le_pot` |
| **A macro-step with branching factor `c ≤ Q²`** is paid for: its children, counted with multiplicity (`Σ nᵢ ≤ c n`), keep the hint with `4mᵢ ≤ 3m` or drop it on windows of at most `n/2` points | `pot_step` |
| **A step without branching** is paid for: smaller base, smaller window, or hint dropped on half the window | `pot_free` |
| The bound in closed form: `pot0 ≤ (2n + 2) n² Q^{b (5λ(n) + 9 + 4(λ(n) + 6)²)}` | `pot0_le` |
| **The label invariant**: Johnson parameters satisfy `s ≤ ⌊log₂ m⌋`; a Johnson step into a base of more than `ℓ ≥ max(2¹¹, (⌊log₂ n₀⌋ + 1)³)` points keeps `t (⌊log₂ m⌋ + 1)²` from growing | `s_le_lam`, `johnson_step_label` |

### Phase 8 — checks (`GraphIsoChecks/Recursion.lean`)

`Sym(4)` on the `2`-subsets of `Fin 4` with their own labels is a hint; a block label computed
by the kernel; `κ`'s drop and the pullback's binomial count, kernel-checked on ranges; the step
inequality on a concrete macro-step.

### Audit

The build lists the axioms of 43 more principal theorems (the theorems named in the tables
above). Each depends only on `propext`, `Classical.choice` and
`Quot.sound`.

## Milestone 14, stage 14b — the group toolkit (`PLAN-14.md` §6)

Costed programs for the macro-steps, in `GraphIso/Toolkit/`, namespace `GraphIso.Toolkit`.
- Each program has a well-formedness lemma, a model, and an explicit cost.
- Each `RunsWithin` spec is proved for any oracle meeting the contract on the operations it
  calls, with the backend charges as hypotheses.
- A hinted instance has degree `N = n + m`: the strings live on the positions `[0, n)`, the base
  `Γ = Fin (N − n)` on `[n, N)`, and the base action `ψ` is the restriction (`baseHom`).

### Phase 1 — hints as data (`Toolkit/Base.lean`)

| Statement | Name |
|---|---|
| Base positions, the base action and its value on a base point | `baseSet`, `basePos`, `baseHom`, `baseHom_apply` |
| Labels as data (one duplicate-free list of base indices per window position), their denotation, the window as a finite set | `LabelData`, `labOf`, `winFinset`, `basePts` |
| **Valid hint data denotes a stage 14a hint**: equivariance on the generators implies it for the generated group | `HintValid`, `HintValid.isHint` |

### Phase 2 — re-basing (`Toolkit/Extend.lean`)

| Statement | Name |
|---|---|
| `rebaseProg`: extend the generators by the induced action on a list of blocks of the base (block systems, or Johnson cells as blocks of their union), keep the string positions and the new block positions, and generate at degree `n + k` | `rebaseProg`, `RunsWithin.rebaseProg`, `rebaseHom` |
| The new group preserves its new base and its string positions | `rebase_invariant` |
| If the old group acts faithfully on the string positions, so does the new one, and there is an isomorphism `θ` that agrees on the string positions and induces the block action on the new base | `rebase_faithful`, `rebase_iso` |

### Phase 3 — label programs (`Toolkit/Labels.lean`)

| Statement | Name |
|---|---|
| Intersection with an invariant set, renumbered (M1, and M2b with one block), linked to `subLab` | `interLabProg`, `RunsWithin.interLabProg`, `mem_subLab_iff_interLab` |
| Block labels (M2a) and the equidistribution test, linked to `blockLabel` and `Equidist` | `blockLabProg`, `equidistProg`, `RunsWithin.blockLabProg`, `RunsWithin.equidistProg`, `mem_blockLab_iff`, `equidistB_iff` |
| The Johnson union from the cell map, linked to `jUnion`; complements | `jUnionProg`, `complLabProg`, `RunsWithin.jUnionProg`, `RunsWithin.complLabProg`, `mem_jUnionData_iff`, `mem_complLab_iff` |
| A label program applied to every window point | `mapLabelsProg`, `RunsWithin.mapLabelsProg`, `getD_mapLabels` |

### Phase 4 — transitivity and blocks of the base (`Toolkit/Transitivity.lean`, `Toolkit/BaseBlocks.lean`)

| Statement | Name |
|---|---|
| `degreeProg`: `min(cap, d)`, `d` the degree of transitivity of `ψ(G)` on the base, by iterated `orbits` and `stabilizer` | `degreeProg`, `RunsWithin.degreeProg`, `degreeModel_spec` |
| **The giant test**: `giantProg` returns `true` exactly when `Alt(Γ) ≤ ψ(G)` | `giantProg`, `RunsWithin.giantProg`, `giantModel_iff` |
| Maximal blocks of a transitive base action: at least two equal blocks; singletons mean a primitive action; blocks of at least two points form an `IsBlockSys` for `baseHom` | `baseBlocksProg`, `RunsWithin.baseBlocksProg`, `baseBlocks_spec` |

### Phase 5 — reductions (`Toolkit/Reduce.lean`, `Toolkit/BlockStab.lean`)

Charges of calls on varying groups are bounded as in `BackendBounds`: for groups inside an
ambient group with at most `s` generators, with stabilizers keeping at most `s` generators.

| Statement | Name |
|---|---|
| `ker ψ` (backend `kernel` on the base) with a left transversal of `G` by its cosets, of length `\|ψ(G)\|` | `kerProg`, `RunsWithin.kerProg` |
| The pointwise stabilizer of a list of points (iterated `stabilizer`), and for base points a left cover of `G` by its cosets, at most `m^r` representatives | `iterStabProg`, `pointStabsProg`, `RunsWithin.iterStabProg`, `RunsWithin.pointStabsProg` |
| Lifting a permutation of the base lying in `ψ(G)` (backend `lift`) | `liftProg`, `RunsWithin.liftProg` |
| For a giant base action, the setwise stabilizer of a set of base points, given two base points outside it: the pointwise stabilizer and lifts of even permutations (generators only; no representatives are needed) | `giantSetStabProg`, `RunsWithin.giantSetStabProg` |
| **M2b**: the setwise stabilizer of one block of a block system of the base, by the induced action at degree `N + k` (`stabilizer` of the block point, truncated), with a left cover of `G` by its cosets (`orbitTransversal` of the block point), at most `k` representatives (`Toolkit/BlockStab.lean`) | `blockStabProg`, `RunsWithin.blockStabProg` |

### Phase 6 — orbital configurations (`Toolkit/Orbital.lean`)

| Statement | Name |
|---|---|
| The `m × m` array of orbital indices of a transitive base action; colours agree exactly on an orbital, the hypothesis of `orbital_uniprimitive` | `orbitalProg`, `RunsWithin.orbitalProg`, `orbitalModel_spec` |
| The colouring by one orbital, equal to `relCol` of the orbital, whose relation has the shape `wlRel_spec` needs | `relColProg`, `RunsWithin.relColProg`, `relColModel_spec`, `arrRel_orbital` |

### Phase 7 — checks (`GraphIsoChecks/Toolkit.lean`)

The checks are interpreter runs over the Schreier–Sims backend:
- `Sym(5)`, `Alt(5)` and `D₅` on pairs and points have degrees of transitivity `3` (capped), `3`
  and `1` on the base, and the giant test separates them;
- the bases are primitive;
- the orbital configuration of `Sym(5)` on pairs is the Petersen graph's three colours;
- the kernel of `Sym(5)` on the base is trivial with `120` representatives;
- the Johnson labels of the pairs satisfy `HintValid`'s generator condition;
- `C₂ ≀ C₂` re-based onto its blocks acts on two points.

### Audit

The build lists the axioms of 35 more principal theorems (those named in the tables, except
definitions and programs). Each depends only on `propext`, `Classical.choice` and
`Quot.sound`.

## Milestone 14, stage 14c — Split-or-Johnson programs I: the steps (`PLAN-14.md` §7)

Programs for one level of milestone 11's Split-or-Johnson, in `GraphIso/SoJProg/`, namespace
`GraphIso.SoJProg`. Points are `Fin m`, sets are lists of indices, cells are lists, colourings
of pairs are `m × m` arrays, and bipartite relations are Boolean arrays (`Data.lean`).
- No program calls the backend. Each has a data model, an explicit cost and a `RunsWithin` spec.
- Each data model is proved equal, after decoding, to the milestone 11 function it implements.
- The programs never multiply: they read arrays through precomputed row offsets.

### Phase 1 — data (`SoJProg/Data.lean`)

| Statement | Name |
|---|---|
| Sets, families of cells, colourings of pairs, bipartite relations; their decoding | `setOf`, `famOf`, `colOf`, `relOf`, `mem_setOf`, `mem_famOf`, `card_setOf`, `card_famOf`, `relOf_cell` |

### Phase 2 — twins and degrees, the Johnson test, the base case (`SoJProg/Twins*.lean`, `Johnson*.lean`, `BaseCase*.lean`)

| Statement | Name |
|---|---|
| Degrees, twin classes and their sizes, the points without twins of degree `d`, the large degrees and their minimum, the twin partition, equal to milestone 11's `deg`, `twinCls`, `tw`, `tfDeg`, `bigDegs`, `twinPart` | `deg_decode`, `twinCls_decode`, `tw_decode`, `tfDeg_decode`, `bigDegs_decode`, `optMin_bigDegs`, `twinPart_decode`, `RunsWithin.twinPartProg`, `RunsWithin.minBigDegProg` |
| Neighbourhoods, complemented neighbourhoods, binomial coefficients (Pascal's rows), the Johnson test and the Johnson leaf | `nbr_decode`, `fOf_decode`, `pascalRow_getD`, `johnson_decode`, `johnsonTest_decode`, `RunsWithin.chooseProg`, `RunsWithin.johnsonTestProg`, `RunsWithin.johnsonLeafProg` |
| The base case: all orderings of the cells (equal to `enums`, at cost `k!` times a polynomial, inherent to the step), neighbourhood codes, the colored partition by code | `enums_decode`, `nbrCode_decode`, `colPart_decode`, `baseLeaf_decode`, `RunsWithin.enumsProg`, `RunsWithin.nbrCodeProg`, `RunsWithin.colBlkProg`, `RunsWithin.baseLeafProg` |

### Phase 3 — the `d`-ary structure and Weisfeiler–Leman on sets (`SoJProg/Dary.lean`, `SoJProg/WLSets.lean`)

| Statement | Name |
|---|---|
| Milestone 10's `wlA` along a bijection computes `wlOn`; on the cells (`↥V₂`) and on `V₁' ⊔ V₂` (milestone 11's `cohOn` with the initial colours `code`) | `get_wlA_eq_wlOn`, `get_wlA_cells`, `cohOn_eq_wlA`, `cohOn_code_eq`, `RunsWithin.cohProg` |
| `Nat.clog` and the arity; the colouring `daryCol` on codes of tuples and its refinement | `clogD_eq`, `RunsWithin.clogProg`, `RunsWithin.arityProg`, `toFun_daryArr`, `wlOn_daryCol_eq`, `RunsWithin.daryArrProg`, `RunsWithin.daryWLProg` |
| Twins of a `d`-ary colouring (swap invariance), `bigTwins`, `pickSide` | `isTwin_cellSub_iff`, `bigTwins_decode`, `bigTwins_daryCol`, `RunsWithin.bigTwinsProg`, `pickSide_decode`, `RunsWithin.pickSideProg` |

### Phase 4 — the Design Lemma test and `dlCont`'s pieces (`SoJProg/DLTest.lean`)

| Statement | Name |
|---|---|
| Milestone 10's `goodA` decides milestone 11's `DLGood` (for thresholds with `v ≤ 2t`); the good lists of length below `d` equal the filtered `tuplesLt` | `goodA_iff_dlGood`, `dlGood_iff_goodA`, `goodList_decode`, `RunsWithin.goodListProg` |
| The class-size test, the dominant classes, the constancy test on `C₁ × C₂`, `selThird` | `allSmallL_iff`, `bigL_decode`, `constRectL_iff`, `selThirdL_decode`, `RunsWithin.selThirdProg` |

### Phase 5 — one level of Coherent Split-or-Johnson (`SoJProg/Coherent.lean`)

| Statement | Name |
|---|---|
| `cohSoj` on data: disconnected colours and components, the imprimitive and primitive branches; the decoded tree equals milestone 11's `cohSoj C₁ C₂ c` exactly; cost at most `903 (N + 1)⁷` | `cohSojD`, `decode_cohSojD`, `decodeRes_cohSojD`, `RunsWithin.cohSojProg`, `cohSojCost_le` |
| The edges of a bipartite leaf: the costed edge query equals `bipEdge`, and the materialized relation array, read through `relOf`, equals `bipEdge` on every listed cell (the representation `bsoj` consumes) | `bipEdgeD_eq`, `relOf_bipRelD`, `RunsWithin.bipEdgeProg`, `RunsWithin.bipRelProg` |

### Phase 6 — checks (`GraphIsoChecks/SoJProg.lean`)

Checks (41) comparing the programs with the model on small inputs (each `#eval` throws on a
failure):
- twins, degrees and the Johnson test on `J(5, 2)` and `J(6, 3)` (true) and on `J(5, 2)` minus
  one pair (false);
- the base case's orderings;
- `Nat.clog` and the arity;
- `bigTwins` and `pickSide`;
- Weisfeiler–Leman on three cells and on three points plus three cells;
- the Design Lemma test on a 5-cycle;
- `selThird` in both branches;
- one level of Coherent Split-or-Johnson against `cohSoj`: equal trees, leaves compared with
  their relations on all points and cells, and the shape and every leaf's kind asserted. Each
  configuration is certified coherent by a brute-force test of the intersection numbers, except
  one deliberately non-coherent input. Every branch is reached:
  - the `J(5, 2)` incidence configuration with `C₂` a clique (every leaf `none`) and with `C₂`
    the Petersen configuration (ten bipartite leaves; an interpreter run);
  - the pentagon under `D₅ × C_l`: partition leaves in the primitive and the imprimitive branch,
    and `X[C₁]` imprimitive;
  - `J(6, 2) ⊔ ([6] × {0, 1})` in the imprimitive branch, with the contraction as the leaf and
    with twelve bipartite leaves;
  - a constant colouring on `C₁ × C₂` (the leaf `none`), and the non-coherent input;
  - the Clebsch configuration: coherence, the `2`-ary refinement, the Design Lemma test, the
    Johnson test (false), and one level on two copies of it (sixteen bipartite leaves).

  The larger fixtures (the clique, `J(6, 2) ⊔ ([6] × {0, 1})` and the doubled Clebsch) compare
  the data model `cohSojD`, which `RunsWithin.cohSojProg` proves is the program's result; an
  interpreter run on them takes minutes;
- the materialized relation `bipRelProg` against `bipEdge` on every point and five cells of
  the `J(5, 2)` incidence configuration, for four colours.

Two values are also checked by the kernel: `C(6, 3) = 20` and `⌈log₂ 9⌉ = 4`.

### Audit

The build lists the axioms of 63 more principal theorems (those named in the tables). Each
depends only on `propext`, `Classical.choice` and `Quot.sound`.

## Milestone 14, stage 14d — Split-or-Johnson trees and leaf stabilizers (`PLAN-14.md` §8)

Whole trees and leaf stabilizers, in `GraphIso/SoJTree/`, namespace `GraphIso.SoJTree` (the
model-level measures in `GraphIso.SplitJohnson`).
- The tree programs make no backend calls and no `.recur` call; they are `.loop`s over a stack
  of frames.
- The leaf stabilizer calls the backend, with the backend charges as explicit hypotheses.

### Phase 1 — leaf multisets, sizes and heights (`SoJTree/Measure.lean`)

| Statement | Name |
|---|---|
| The multiset of the leaves of all paths: cardinality the count, elements the reachable leaves; behaviour under `bind`, `trans` (injective choices) and `withPiece` | `CTree.leafMs`, `CTree.card_leafMs`, `CTree.mem_leafMs`, `CTree.leafMs_bind`, `CTree.leafMs_trans`, `leafMs_withPiece` |
| Size (vertices and edges) and height; a live tree has size at most `2 (height + 1) · count`; `bsoj` has height at most `2 |V₂| + 1`, `soj` at most `2 |Γ| + 2` | `CTree.size`, `CTree.height`, `CTree.size_le_of_live`, `height_bsoj_le`, `height_soj_le` |
| **The M4 index bound**: if every element of `G` preserves `c`, the orbit of a reachable leaf of `soj c t` has at most `count` elements | `card_orbit_le_count` |

### Phase 2 — leaf data (`SoJTree/LeafData.lean`, `SoJTree/LeafProg.lean`)

| Statement | Name |
|---|---|
| Leaf data decoding to `Option (Out (Fin m))` through `cpartOf` and `jembOf`; `addPieceOut` and `extendOut` on data | `OutD`, `decodeOut`, `decodeOut_addPieceD`, `decodeOut_extendD`, `RunsWithin.addPieceProg`, `RunsWithin.extendOutProg` |
| Equality of decoded leaves (total functions compared at every point) and a permutation acting on leaves, with polynomial costs | `outEqD_iff`, `decodeOut_actOutD`, `RunsWithin.outEqProg`, `RunsWithin.actOutProg`, `outSize_actOutD_le`, `outEqCost_le`, `actOutCost_le` |

### Phase 3 — one frame (`SoJTree/Frame.lean`, `SoJTree/StepProg.lean`)

| Statement | Name |
|---|---|
| `bsoj` reads its relation only on its cells (trees equal on reachable branches, `TEq`); `cohSoj` is natural along injective maps | `FrameAux.bsoj_congr`, `FrameAux.cohSoj_agree` |
| One level on data: the frame tree's leaves are the produced leaves plus the children's; children are valid with fewer cells; work plus children's sizes is at most the frame's size | `stepD`, `stepD_leafMs`, `stepD_children`, `stepD_size` |
| The initial frames of `sojAt`: a leaf, or a frame whose tree agrees with `sojAt` up to `TEq` | `sojAtD_leaf`, `sojAtD_frame` |
| The step program: cost at most `stepK m q t · (1 + work + produced leaves)`, the invariant preserved by the children | `RunsWithin.stepProg`, `stepD_validP` |

### Phase 4 — the worklist and the tree programs (`SoJTree/Worklist.lean`, `SoJTree/Trees.lean`)

| Statement | Name |
|---|---|
| A generic worklist `.loop`: outputs as a multiset, cost at most `(K + 11) · Σ (rank + 2) · size + 7` | `worklistD_ms`, `enumMs_eq`, `RunsWithin.worklistProg` |
| `bsojProg` and `sojProg`: decoded outputs equal the model's `leafMs` (length the count, elements the reachable leaves); cost a polynomial times the size | `bsojProg_leafMs`, `bsojProg_length`, `bsojProg_reach`, `RunsWithin.bsojProg`, `sojProg_leafMs`, `sojProg_length`, `sojProg_reach`, `RunsWithin.sojProg` |
| Closed bounds under milestone 11's hypotheses: a polynomial in `m` times `2^{128 (⌈log₂ t⌉ + 2)²}` (`bsoj`) and `2^{129 (⌈log₂ m⌉ + 2)²}` (`soj`) | `bsojProg_cost_le`, `sojProg_cost_le` |
| `sojAtProg`: the whole tree `sojAt` after individualizing `x`, decoding to its `leafMs`, cost a polynomial times its size (round 1 found only the initializer, F1) | `sojAtProg_leafMs`, `sojAtProg_length`, `sojAtProg_reach`, `RunsWithin.sojAtProg` |
| Every leaf the tree programs output has data size at most `m² + m + q + 1` (`outB`), through every step and the worklist (round 1, F2) | `stepD_outSize`, `bsojProg_outSize`, `sojAtProg_outSize`, `sojProg_outSize` |

### Phase 5 — orbits and stabilizers (`SoJTree/OrbitClosure.lean`, `OrbitStab.lean`, `LeafStab.lean`, `LeafBound.lean`)

| Statement | Name |
|---|---|
| The orbit of a structure under permutation generators, listed without repetition, with each generator's index map; its length is the orbit's size | `orbitD_spec`, `orbitD_length_eq`, `RunsWithin.orbitProg` |
| The index action of a group on a listed G-set; the stabilizer of a point through the backend, with at most `r` representatives forming an `IsLeftCover` | `exists_idxActHom`, `idxAct_fix_iff`, `RunsWithin.orbitStabProg` |
| **The leaf stabilizer** `{g ∈ G | ψ(g) • o = o}` with its cover; at most `count` representatives when `ψ(G)` preserves the colouring and `o` is reachable in `soj` | `RunsWithin.leafStabProg`, `leafOrbit_length_eq`, `leafStab_index_le_count`, `leafStab_reps_le_count` |
| The leaf stabilizer's cost for a leaf of bounded data size: `1000 (N + k + |gs| + r + S + 2)⁸` plus terms in the backend's output lengths and the four charges; for a leaf output by `sojProg` with `ψ(G)` preserving the colouring, this bound with `S = outB k t` and `r ≤ count` (macro-step M4) | `leafStabCost_le_of_outSize`, `RunsWithin.leafStabProg_of_outSize`, `RunsWithin.leafStabProg_sojLeaf` |

### Phase 6 — checks (`GraphIsoChecks/SoJTree.lean`)

Interpreter runs and data-model comparisons (38), each `#eval` throwing on a failure:
- leaf data: `outEqD`/`outEqProg`, `actOutD`/`actOutProg`, `addPieceD`/`addPieceProg`,
  `extendD`/`extendOutProg` against the model on decoded leaves;
- frame steps against the model (multiset equation and size inequality) on the twin partition,
  the Johnson leaf of `J(5, 2)`, the base case, large twin classes, and the Design Lemma node
  with arity 1; the `cohSoj` level on data, with the children's steps against the model;
- whole trees: `worklistD` of `stepD` against `(bsoj …).leafMs` and `(soj …).leafMs` and the
  counts (Petersen with `t = 6`, `K₅`, two random colourings);
- `bsojProg`, `sojAtProg`, `sojProg` and `stepProg` in the interpreter against the data models,
  with `outSize ≤ outB` for every output leaf;
- direct continuation coverage: hand-built inputs take every branch of `dlCont` and `cohCont`
  (`allSmall` included), each compared in the interpreter, on data and with the model;
- `orbitD` against brute-force orbits, and `leafStabProg` with the Schreier–Sims backend:
  stabilizer orders against brute force, the cover, and the M4 index bound.

The `cohSoj` level of whole frames is not compared with the model, because the model's
Weisfeiler–Leman is too slow there. Through whole valid frames, `allSmall` is not reached, and
the checks' docstring argues four other branches unreachable on small inputs. All five are
covered by the direct fixtures.

### Audit

The build lists the axioms of 62 more principal theorems (those named in the tables, except
the definitions). Each depends only on `propext`, `Classical.choice` and `Quot.sound`.

## Milestone 14, stage 14e — local certificates as programs (`PLAN-14.md` §9)

Milestone 13's local certificates and their comparison, as programs in `GraphIso/CertProg/`,
namespace `GraphIso.CertProg` (the paired beard in `GraphIso.Certificates`). The programs call
the backend; every recursive call goes through a sub-solver parameter.

### Phase 1 — the paired beard (`CertProg/PairBeard.lean`)

| Statement | Name |
|---|---|
| The paired coset after `i` steps; for `x' = x`, `A' = A` the beard's group; a left coset of it | `pairCoset`, `beardG`, `pairCoset_self`, `pairCoset_eq_smul` |
| Its elements conjugate the beards of `x` at `A` and `x'` at `A'` (one beard computation suffices) | `beardG_conj`, `beardW_succ_conj` |
| Each step is a string-isomorphism coset on the next window; `CertIso` holds exactly when the final coset maps `T` to `T'` | `pairCoset_succ`, `certIso_iff` |

### Phase 2 — setting, test sets, affected points, the kernel (`CertProg/Setting.lean`, `TestSets.lean`, `Affected.lean`, `Kernel.lean`)

| Statement | Name |
|---|---|
| A representation `φ` of the group restricted to the string positions agreeing with the base action exists (faithfulness) | `exists_phi` |
| `G_A`, an element mapping `T` to `T'` pointwise, the giant test of `ψ_A(H)` on degree `k` | `RunsWithin.stabSetProg`, `toStab_stabSet`, `moveD_spec`, `RunsWithin.moveProg`, `isGiantOn_toStab_iff`, `RunsWithin.giantAProg`, `giantAModel_iff` |
| The affected points equal milestone 13's `aff` | `RunsWithin.affProg` |
| The kernel `H ∩ ker ψ_A` with at most `k!` coset representatives, at cost `kerACost` (polynomial × `k!`); its orbits on the affected points have at most `n / k` points | `pointStabs_reps_le_factorial`, `RunsWithin.kerAProg`, `kernel_orbit_of_giant`, `kerOrbit_length_le` |

### Phase 3 — the step, the loop, the certificate and the comparison (`CertProg/Step.lean`, `Cert.lean`, `CertIso.lean`, `Transporter.lean`)

| Statement | Name |
|---|---|
| One beard step: branch over the kernel's cosets, process its orbits through the sub-solver; the result represents the next paired coset | `denotes_iso_succ`, `RunsWithin.beardStepProg` |
| The loop of at most `n` rounds (stops once the window is stable); the result represents the final paired coset and lists the final window | `pairCoset_stable`, `RunsWithin.pairLoopProg`, `atRound_none_iff` |
| The tuple transporter in a group | `RunsWithin.tupleTransProg` |
| **The certificate**: `W(A)`, `H(A)`, `K(A)` equal milestone 13's `beardW`, `beardH`, `certK`, and the fullness test is `IsGiantOn φ A (certK …)`; `G_A`'s generator count from `BackendBounds` | `RunsWithin.certProg`, `giantGens_allValid`, `stabSet_gens_le` |
| **The comparison**: `certIsoProg` decides `CertIso` | `certIso_iff_transporter`, `RunsWithin.certIsoProg` |
| The returned `H(A)` and `K(A)` are exactly the preimages of milestone 13's groups (round 1, F2) | `denotes_toStab` (conclusions of `RunsWithin.certProg`) |
| Costs: the kernel at polynomial × `k!` (factorial bounds on the intermediate representative lists, round 1, F3); the step, the loop, the certificate and the comparison at polynomial × `k!` plus `n · k! · n` sub-calls of cost `Cb` | `cp_ps_run`, `beardStepCost_eq`, `beardStepCost_le`, `pairLoopCost_le`, `certCost_le`, `certIsoCost_le` |

### Phase 4 — checks (`GraphIsoChecks/CertProg.lean`)

Kernel-checked examples (10, `decide`) on `S₃`/`A₃` acting on `[3]` with a base of three
points: each program against a brute-force value in the same term (`certProg` and `certIsoProg`
with `k = 1`, the beard step and the paired loop with `k = 3`). Supplementary interpreter runs
(14) with the Schreier–Sims backend and milestone 1's solver as the sub-solver, each compared
with brute force over every group element:
- `S₅`/`A₅` on the pairs of `[5]` and on `[5]` (`k = 3`), `S₇` on `[7]` (`k = 5`);
- `stabSetProg`, `moveProg`, `giantAProg`, `affProg`, `kerAProg`, `kerOrbitsProg` (with
  `k · |o| ≤ n` for `k = 5`), `tupleTransProg`;
- `beardStepProg` and `pairLoopProg` (`x' ≠ x`: nonempty and empty final cosets);
- `certProg` (windows, groups, `K(A)`, fullness, with and without full test sets) and
  `certIsoProg` (true and false cases).

Whole certificates use `k = 3`; with `k = 5` they take about 40 s each, so `k = 5` is checked
through the pieces.

### Audit

The build lists the axioms of 37 more principal theorems (those named in the tables, except
the definitions). Each depends only on `propext`, `Classical.choice` and `Quot.sound`.

## Milestone 14, stage 14f — structures on the base and Align (`PLAN-14.md` §10)

Babai's procedure Align, in `GraphIso/Align/`, namespace `GraphIso.Align`.

### Phase 1 — trimmed Johnson embeddings (`Align/Trim.lean`)

| Statement | Name |
|---|---|
| Trimming `f` to `V₀` commutes with the action, keeps `IsJohnson` and validity, and keeps `soj` canonical | `trimJ_smul`, `trimOut_smul`, `isJohnson_trimJ`, `validOut_trimOut`, `trim_canonical` |
| Johnson leaves of `soj` have cells disjoint from `V₀` (unconditionally); those of `bsoj` too, when the input cells are disjoint from `V₁` (the hypothesis is necessary) | `soj_johnson_disjoint`, `bsoj_johnson_disjoint` |

### Phase 2 — structures: stabilizers and isomorphisms (`Align/Interface.lean`, `SetOps.lean`, `PartOps.lean`, `JohnOps.lean`)

| Statement | Name |
|---|---|
| Colored partitions: generators of exactly the stabilizer, isomorphism search, programs with polynomial costs | `partGens_closure`, `partGens_valid`, `partOps_spec`, `RunsWithin.partGensProg`, `RunsWithin.partIsoProg`, `partGensCost_le`, `partIsoCost_le` |
| Sets (as two-block colored partitions) | `setPart_valid`, `setOps_spec`, `RunsWithin.setGensProg`, `RunsWithin.setIsoProg`, `setGensCost_le`, `setIsoCost_le` |
| Trimmed Johnson embeddings: generators of exactly the stabilizer, isomorphism search (some and none), the data invariant `JValid` from `IsJohnson` together with the representation conditions `JShape` (disjoint cells, trimmed data, lists in range), programs | `johnGensD_closure`, `johnIsoD_some`, `johnIsoD_none`, `johnOps_spec`, `jvalid_of_isJohnson`, `RunsWithin.johnGensProg`, `RunsWithin.johnIsoProg` |

### Phase 3 — Align (`Align/AlignProg.lean`)

| Statement | Name |
|---|---|
| `Stab(X) ∩ P` by Schreier generators of index at most 2; isomorphisms inside `P` with parity correction; `P` generated at the base degree | `closure_schreierSet`, `closure_stabInPL`, `isoInPL_spec`, `RunsWithin.stabInPProg`, `RunsWithin.isoInPProg`, `RunsWithin.pGroupProg` |
| The preimage `ψ⁻¹(L)` from lifts and the kernel | `closure_lifts_ker`, `RunsWithin.preProg` |
| The isomorphisms decompose over the structures of `y`; one candidate's isomorphisms are a coset of `G₁` | `iso_eq_isoTo`, `iso_eq_iUnion_isoTo`, `RunsWithin.alignCall` |
| **Align**: the combined answer is correct for `G`, given that every isomorphism carries `X(x)` to a listed structure | `RunsWithin.alignProg` |

### Phase 4 — checks (`GraphIsoChecks/Align.lean`)

Kernel-checked examples (6, `decide`): stabilizers and isomorphisms of sets, colored partitions
and a trimmed Johnson embedding on `[4]` against brute force over `Sym(4)`; parity inside
`Alt(4)`/`Sym(4)`; `alignProg` in `S₃` and `A₃` with the Schreier–Sims backend and milestone 1's
solver as the sub-solver, against the brute-force isomorphism coset. Supplementary interpreter
runs (6) on bases of 5 to 10 points.

### Audit

The build lists the axioms of 39 more principal theorems (those named in the tables). Each
depends only on `propext`, `Classical.choice` and `Quot.sound`.

## Milestone 14, stage 14g — aggregation, Case 1 and Case 2a (`PLAN-14.md` §11)

The first half of the giant macro-step after the certificates, in `GraphIso/Giant/`, namespace
`GraphIso.Giant` (the full group in `GraphIso.Certificates`).

### Phase 1 — the full group and aggregation (`Giant/FullGroup.lean`, `Giant/Aggregate.lean`)

| Statement | Name |
|---|---|
| The full group by the test on `K(A)`: automorphisms unconditionally, canonical, equal to milestone 13's `fullGroup` under the thresholds, generated by the passing `K(A)` | `fullGroupK_le_autG`, `fullGroupK_relabel`, `fullGroupK_eq_fullGroup`, `fullGroupK_eq_closure` |
| The `k`-subsets of the base, each once; their number and the partial lists' bound | `ksubsD_finsetOf`, `length_ksubsD`, `agParts_length_le`, `RunsWithin.ksubsProg` |
| `fullProg`: `F` denotes `fullGroupK`, at most `C(m, k)` certificates | `agPart_ksubsD`, `RunsWithin.fullProg` |
| The certificates' `K(A)` have at most `s` generators; the charge premises of `fullProg` (generate on lists of at most `2s` generators, the set stabilizers of the enumerated `k`-subsets) hold for the Schreier–Sims backend with explicit values (round 1, F1) | `ag_certProg_gens`, `ag_ss_charges` |
| The case decision (orbit of more than `m/2` points, support) | `caseD_spec`, `RunsWithin.caseProg` |

### Phase 2 — Case 1 (`Giant/Case1.lean`)

| Statement | Name |
|---|---|
| Orbit partitions: unique, moved by the action, colored partitions | `isOrbitPart_unique`, `isOrbitPart_smul`, `isColPart_of_isOrbitPart` |
| The data partition from the backend's orbits; canonical | `orbitPartD_spec`, `orbitPart_canonical`, `RunsWithin.orbitPartProg`, `orbitPartCost_le` |
| **Case 1**: Align of the orbit partitions; the answer is correct | `RunsWithin.case1Prog`, `case1Cost_le` |

### Phase 3 — Case 2a (`Giant/Case2a.lean`)

| Statement | Name |
|---|---|
| The cover of `H` by `K ⊔ F` and the generators of `H` (no parity computed) | `c2_cover` |
| The pullback: branches, the answer correct for the coset | `RunsWithin.pbBranch`, `RunsWithin.pullbackProg` |
| **Case 2a**: alignment of `Φ` with the pullback inside | `c2_g1_spec`, `RunsWithin.case2aProg` |
| The orbits of `K` have at most `n/2` points, from the giant hint's labels | `c2_hhalf_of_labels`, `RunsWithin.pullbackProg_of_labels`, `RunsWithin.case2aProg_of_labels` |
| The unique large orbit is canonical, so every isomorphism carries `Φ(x)` to `Φ(y)`; **Case 2a** with the alignment derived from canonical `F` (round 1, F2) | `largeOrbit_canonical`, `c2_orbit_stable`, `RunsWithin.case2aProg_canonical` |

### Phase 4 — checks (`GraphIsoChecks/Giant.lean`)

Kernel-checked examples (`decide`): the `k`-subsets, the case decision and the orbit partition
on `[4]`, a full-group step (control flow), `case1Prog` and `case2aProg` in `S₃`/`A₃` against
brute-force isomorphism cosets. Supplementary interpreter runs: `fullProg` with `k = 3` in `S₆`
against the brute-force full group (order 24), `case2aProg` in `S₅`.

### Audit

The build lists the axioms of 34 more principal theorems (those named in the tables). Each
depends only on `propext`, `Classical.choice` and `Quot.sound`.

## Milestone 14, stage 14h — Case 2b (`PLAN-14.md` §12)

Case 2b of the giant macro-step, in `GraphIso/Case2b/`, namespace `GraphIso.Case2b`.

### Phase 1 — the choice tree (`Case2b/Tree.lean`)

| Statement | Name |
|---|---|
| The tree over tuples of `Φ`, pairs of `Φ ∖ S`, `wlRel` of the orbital, components or `soj`, with trimmed and extended leaves: canonical | `case2bTree_relabel`, `case2bTree_relabel'`, `leafTree_relabel` |
| Valid leaves, liveness, and the count bound; the degree of transitivity gives the hypotheses; the alignment through `iso_reach` | `case2bTree_valid`, `extPart_valid`, `extJohn_valid`, `leafTree_spec`, `case2bTree_live`, `case2bTree_count_le`, `case2bHyp_of_degree`, `case2b_reach` |

### Phase 2 — leaves as structures (`Case2b/OutOps.lean`)

| Statement | Name |
|---|---|
| `outOps` over leaf data, its spec, the generator count of a valid leaf, programs | `outOps_spec`, `length_outGensD_le`, `RunsWithin.outGensProg`, `RunsWithin.outIsoProg`, `outGensCost_le`, `outIsoCost_le` |

### Phase 3 — the data pipeline and the link (`Case2b/Pipeline.lean`, `PipelineProg.lean`, `ChoiceProg.lean`, `Link.lean`)

| Statement | Name |
|---|---|
| Decoding: the WL colouring is `wlRel` of the orbital, the leaves and their trimming and extension, the enumerations | `colOf_wlColD`, `decodeOut_compLeafD`, `disconn_wlCol`, `sojD_leafMs`, `decodeOut_trimD`, `decodeOut_extD`, `mem_tuplesD`, `mem_pairsD`, `leavesOfD_decode_comp`, `leavesOfD_decode_soj` |
| Programs: the restricted stabilizer, the colouring, one choice, all choices, the first leaf | `RunsWithin.resProg`, `RunsWithin.colProg`, `RunsWithin.leavesOfProg`, `RunsWithin.choiceProg`, `RunsWithin.allLeavesProg`, `RunsWithin.firstLeafProg` |
| The data lists are the tree's leaves, the first leaf is reachable and exists, every listed leaf is valid, each `soj` tree has size at most `sojZ` | `allLeavesD_leafMs`, `firstLeafD_reach`, `firstLeafD_ne_none`, `allLeavesD_valid`, `firstLeafD_valid`, `sojSz_le` |

### Phase 4 — the program (`Case2b/Case2bProg.lean`)

| Statement | Name |
|---|---|
| The degree of transitivity on `Φ` | `RunsWithin.degProg`, `degD_spec`, `case2bHyp_degD` |
| **Case 2b**: Align over all of `y`'s structures; correct for `G` from canonical `F` and `Φ`, with the sizes and the first leaf derived | `RunsWithin.case2bProg`, `RunsWithin.case2bProg_canonical`, `RunsWithin.case2bProg_canonical'` |
| The Schreier–Sims charges with bounded lists | `c2b_ss_charges` |

### Phase 5 — checks (`GraphIsoChecks/Case2b.lean`)

Kernel-checked examples (`decide`): enumerations, orbital colourings, the degree, one choice of
`C₄` against brute force, leaves against milestone 11's model (exact, with a failing control),
trimming and extension, canonicity of a choice, `outOps`; `case2bProg` end to end on an empty
window (`S₄` with the Klein group: all 24 permutations), the complete leaf lists under
relabelling, and Johnson dispatch. Supplementary interpreter runs: degrees and all choices for
`D₄`, `C₅`, `D₅`, `AGL(1,5)`, `PSL(2,5)`, `S₅` on pairs; canonicity over all choices;
`case2bProg` with `S₄` on 4-vertex graphs against brute-force isomorphism cosets. The model tree
and the nonempty-window runs are too slow for the kernel; milestone 10's `wlA` does not reduce
there.

### Audit

The build lists the axioms of 46 more principal theorems (those named in the tables). Each
depends only on `propext`, `Classical.choice` and `Quot.sound`.

## Milestone 14, stage 14i — Case 3 (`PLAN-14.md` §13)

Case 3 of the giant macro-step, in `GraphIso/Case3/`, namespace `GraphIso.Case3`.

### Phase 1 — the colouring of `k`-tuples (`Case3/Colouring.lean`)

| Statement | Name |
|---|---|
| `CertIso` is an equivalence across strings, induced by isomorphisms | `certIso_refl`, `certIso_symm`, `certIso_trans`, `certIso_of_relabel`, `certIsoL_iff` |
| The colourings with consistent names: isomorphisms map `x`'s to `y`'s; `x`'s colours are `SameColour` | `tupleCol_iso`, `colX_eq_iff` |
| Programs: the comparisons by `certIsoProg`, the colourings | `RunsWithin.cmpProg`, `RunsWithin.tupleColProg` |

### Phase 2 — the structures (`Case3/Model.lean`)

| Statement | Name |
|---|---|
| Split-or-UPCC and `soj` on the dominant class (natural, live, valid, count) | `splitTree_relabel`, `splitTree_spec`, `domCls_eq`, `outTree_relabel`, `outTree_spec` |
| The tree over the good lists: natural, alignment through `iso_reach`, live and valid without large twins, count | `case3Tree_relabel`, `case3_reach`, `case3_reach_eOf`, `case3Tree_spec`, `case3Tree_live`, `case3Tree_valid`, `case3Tree_count_le` |
| No large twins under the thresholds | `no_twins_of_thresholds` |

### Phase 3 — the pipeline and the link (`Case3/Pipeline.lean`, `PipelineProg.lean`, `Link.lean`)

| Statement | Name |
|---|---|
| Decoding: the WL array, the good lists, the vertex colouring, the outcomes, the twins flag | `toFun_wlCD`, `mem_goodListsD`, `goodListsD_ne_nil`, `twinsD_spec`, `col1D_eq`, `outcomeD_small`, `outcomeD_dom` |
| Programs | `RunsWithin.wlCProg`, `RunsWithin.outcomeProg`, `RunsWithin.allStructsProg`, `RunsWithin.firstStructProg`, `RunsWithin.twinsFlagProg` |
| The data lists are the tree's leaves; the first structure is reachable; validity; sizes; twins | `allStructsD_leafMs`, `firstStructD_reach`, `firstStructD_ne_none`, `allStructsD_valid`, `firstStructD_valid`, `outSzD_le`, `twinsD_eq_false`, `htw_of_thresholds` |

### Phase 4 — the program (`Case3/Case3Prog.lean`)

| Statement | Name |
|---|---|
| **Case 3**: the fallback signal when no good list exists (which implies large twins, not conversely), `some none` on different sizes, otherwise Align's answer, correct for `G` with the alignment, validity, sizes and first structure derived | `RunsWithin.case3Prog_ne`, `RunsWithin.case3Prog`, `RunsWithin.case3Prog_canonical`, `outCostD_le` |
| No fallback under the thresholds; the Schreier–Sims charges | `case3_no_fallback`, `c3_ss_charges` |

### Phase 5 — checks (`GraphIsoChecks/Case3.lean`)

Kernel-checked examples (`decide`): colourings with consistent names, the pipeline programs
against brute force (`C₄`, `2K₂`, a constant colouring, `C₅`), canonicity of the complete
structure lists, and `case3Prog` end to end on `S₃` (an isomorphic pair, a non-isomorphic pair,
the fallback; an empty window with three Align candidates, whose colouring has large twins but
good lists). Supplementary interpreter runs: `tupleColProg` on `S₅` (`k = 2`) and
`case3Prog` on `S₅` with `k = 3` and nontrivial certificates.

### Audit

The build lists the axioms of 48 more principal theorems (those named in the tables). Each
depends only on `propext`, `Classical.choice` and `Quot.sound`.

## Milestone 14, stage 14j-1 — hinted instances and derived hints (`PLAN-14.md` §14.1)

The first loop of the main recursion, in `GraphIso/Main/`, namespace `GraphIso.Main`. Degree
`N = n + m`: string positions `[0, n)`, base `[n, N)`.

### Phase 1 — hinted instances (`Main/HInst.lean`)

| Statement | Name |
|---|---|
| Hinted instances as data, the invariant `HInstValid` (hint data plus transitivity on the window), the bridge to stage 14a, the measure | `HInstValid.isHint`, `HInstValid.transitive`, `hmeasure_some`, `hmeasure_none` |

### Phase 2 — free coarsenings and reductions (`Main/Free.lean`, `Main/Reduce.lean`)

| Statement | Name |
|---|---|
| **M0**: maximal blocks of the window as the base (new base at most `\|w\| ≤ n`), with `HintValid`, transitivity, faithfulness and the same string action | `RunsWithin.m0Prog`, `wf_m0Prog` |
| **M1**: the first base orbit with non-constant labels | `RunsWithin.m1Prog`, `mf_exists_ncD`, `mf_pickD_spec`, `wf_m1Prog` |
| **M2a**: block labels, `2m' ≤ m` | `RunsWithin.m2aProg`, `mf_blockLab_nonconst`, `wf_m2aProg` |
| Pieces: hint data from generator checks, the M0 labels, M1's intersection, constancy test, choice and singletons, M2a's block index, the factorial cover of pointwise stabilizers | `hintValid_of_forall`, `RunsWithin.labM0Prog`, `RunsWithin.interOProg`, `RunsWithin.ncProg`, `RunsWithin.pickProg`, `RunsWithin.labM1Prog`, `RunsWithin.singProg`, `RunsWithin.m2aIdxProg`, `RunsWithin.mr_pointStabsFact` |
| **M2b**: the block stabilizer (a left cover by at most `\|Ψ\|` cosets), re-based onto the block, `2m' ≤ m`, a hint on every nonempty invariant part of the window | `RunsWithin.m2bProg`, `m2b_hintValid`, `m2b_card`, `wf_m2bProg` |
| **The Johnson fallback**, in the group re-based onto the cells: the pointwise stabilizer of the positions of the `u` union cells (each union cell fixed as a set; a left cover by at most `u!` cosets, `u ≤ \|lab u₀\| · s`); orbits of at most half of the window | `RunsWithin.jfallbackProg`, `jfallback_half`, `length_jUnionData_le`, `jfallback_cells_le`, `wf_jfallbackProg` |

### Phase 3 — the derived hint, model (`Main/DeriveModel.lean`)

| Statement | Name |
|---|---|
| The children of a derived hint, each with `pot_step`'s measure | `inter_isHint`, `blocks_label_isHint`, `blocks_stab_isHint`, `johnUnion_isHint`, `johnFallback_fix`, `johnFallback_half` |
| A colored `t`-partition with `4t ≤ 3m`; a Johnson structure with `m ≤ 4t`; a coloured Johnson pair with classes outside `V₀` of at most `m/2` points; extended partitions | `derived_colPart`, `derived_johnson`, `derived_cjohnson`, `dm_cells_bound`, `isColPart_ext_bound`, `derived_extPart` |
| **A preserved set alone gives no progress**: the labels may be non-constant on `O` only inside `Φ` | `derived_set` |

### Phase 4 — coloured Johnson structures (`Main/CJohnOps.lean`)

| Statement | Name |
|---|---|
| `(Q, J)` as a `StructOps`: stabilizer generators (at most `3m²`), the colour-respecting isomorphism search | `cjohnOps_spec`, `cj_smul_eq_iff`, `cjohnGensD_closure`, `length_cjohnGensD_le`, `cjohnIsoD_some`, `cjohnIsoD_none` |
| Programs | `RunsWithin.cjohnGensProg`, `RunsWithin.cjohnIsoProg`, `wf_cjohnGensProg`, `wf_cjohnIsoProg` |

### Phase 5 — the derived hint as a program (`Main/Derive.lean`)

| Statement | Name |
|---|---|
| The setting (`DSetting`): no hint when the labels are constant on `O`, with `2\|O\| ≤ \|w\|`; the hint for `K` otherwise | `DSetting.half`, `DSetting.hintK` |
| The pieces: the block step, M1 with continuation, the free dispatch, the Johnson cells, the fallback, the Johnson step, the coloured Johnson dispatch | `RunsWithin.blocksProg`, `RunsWithin.m1ContProg`, `RunsWithin.deriveFreeProg`, `dv_cells_child`, `dv_jfallback`, `RunsWithin.johnStepProg`, `RunsWithin.deriveCJProg` |
| **`deriveProg`**: the run, an explicit cost with backend charges as hypotheses on specific inputs, and `DOutcome` (tags 0–5 with their measure, every child window equal to `O`; tag 6 `stuck` has no guarantee) | `RunsWithin.deriveProg_free`, `RunsWithin.deriveProg_cj`, `wf_deriveProg` |
| **Progress**: `stuck` is excluded when `K` preserves a colored `t`-partition with `4t ≤ 3m` (`m ≥ 2`), or a coloured Johnson structure with classes outside `V₀` of at most `m/2` points (`m ≥ 5`) | `dv_not_prim`, `derivePart_ne_stuck`, `dv_m1_colour`, `deriveCJ_ne_stuck` |

### Phase 6 — checks (`GraphIsoChecks/MainHints.lean`)

Kernel-checked examples (`decide`), all against brute force on data:
- M0 on `D₄` and `S₄`;
- M1, M2a and M2b on `C₄`, and the Johnson fallback on `S₂ × S₂`;
- `cjohnOps` twice;
- `deriveProg` on eight fixtures, each checked for its setting, for program = model, and for
  the outcome promised by its tag (0–5, every child window `O`). The Johnson fixtures
  (`m = 12`, `s = 2`, four cells, `IsJohnson` and `JValid` proved) check tag 5's cell-level
  stabilizer exactly: two coset representatives;
- a `stuck` negative control (`C₃`, no structure);
- a preserved partition giving progress (`C₆`).

### Audit

The build lists the axioms of 70 more principal theorems (those named in the tables). Each
depends only on `propext`, `Classical.choice` and `Quot.sound`.

## Milestone 14, stage 14j-2 — the macro-step framework and M0–M3 (`PLAN-14.md` §14.2)

In `GraphIso/Main/`, namespace `GraphIso.Main`. Every step takes a hinted sub-solver as a
parameter. Its spec gives the run (the children's costs plus explicit work), the parent's
answer, and a `ChildList` of children's measures with the predicate `pot_step` or `pot_free`
needs.

### Phase 1 — the framework and transfer (`Main/Frame.lean`, `Main/Transfer.lean`)

| Statement | Name |
|---|---|
| The measure through `baseOpt`; each children's predicate decreases it | `hmeasure_eq`, `StepChild.measLt`, `FreeChild.measLt`, `ChainChild.measLt` |
| Transfer: the lifted representative agrees with the child's; the iso set maps to the parent's | `tr_eq_of_agree`, `tr_iso_eq`, `tr_iso_eq_empty`, `tr_lift_exists`, `RunsWithin.transferProg`, `wf_transferProg` |
| The child instance is valid; `ChildOK` gives the relation | `ChildOK.rel`, `ChildOK.labels`, `childHInst_valid`, `noHintHInst_valid`, `RunsWithin.childInstProg` |
| **Solving through a re-based child**: align, pad, call, restrict and lift; a call without a hint | `RunsWithin.viaChildProg`, `RunsWithin.sameDegProg`, `wf_viaChildProg`, `wf_sameDegProg` |

### Phase 2 — steps without re-based children (`Main/StepsBase.lean`)

| Statement | Name |
|---|---|
| Calls without a hint; validity; the sequential reduction's hypothesis from `HSubSolves` | `RunsWithin.plainSub`, `sb_hinstValid_plain`, `sb_seqSub` |
| **Base case**: a window fixed pointwise | `fixedTest_iff`, `RunsWithin.fixedStepProg`, `wf_fixedStepProg` |
| **Chain rule**: `ChainChild` children, `c = 1` | `RunsWithin.chainProg`, `wf_chainProg` |
| **Kernel reduction** and **M3**: at most `m!` cosets, children without a hint inside label fibres (`StepChild`) | `sb_half_of_fix`, `RunsWithin.kerRedProg`, `RunsWithin.m3Prog`, `wf_kerRedProg`, `wf_m3Prog` |

### Phase 3 — the free coarsenings (`Main/StepsHint.lean`)

| Statement | Name |
|---|---|
| The shared tail through `viaChildProg` | `sh_childOf` |
| **M0**, **M1**, **M2a**: one hinted child each, `FreeChild`, `c = 1` | `RunsWithin.m0StepProg`, `RunsWithin.m1StepProg`, `RunsWithin.m2aStepProg`, `wf_m0StepProg`, `wf_m1StepProg`, `wf_m2aStepProg` |

### Phase 4 — the dynamic chain and the block-stabilizer loop (`Main/DynSeq.lean`, `Main/M2bLoop.lean`)

| Statement | Name |
|---|---|
| **The dynamic chain**: orbits of the current group; correct answer; sizes sum to at most `\|W\|` | `RunsWithin.dynSeqProg`, `wf_dynSeqProg` |
| The loop's handle: a hinted child, or one without a hint on at most half of an `R`-orbit | `ml_handle`, `M2bChild.stepChild`, `HSubSolves.mono` |
| **The block-stabilizer loop** and **M2b**: `StepChild` children, `c = \|reps\| ≤ #blocks` | `RunsWithin.m2bLoopProg`, `RunsWithin.m2bStepProg`, `wf_m2bLoopProg`, `wf_m2bStepProg` |

### Phase 5 — reduce-and-derive (`Main/RD.lean`)

| Statement | Name |
|---|---|
| Per-tag semantics, the handle, the branch | `rd_sem0`, `rd_sem124`, `rd_sem3`, `rd_sem5`, `rd_sem6`, `rd_base_inv_of_iso`, `rd_handle`, `rd_branch` |
| Output degrees; the tag-5 factor `≤ (#union cells)!` | `rd_deg_free`, `rd_deg_cj`, `rd_cj_reps5` |
| **`rdProg`**: `StepChild` children with `c = \|rs\| · (N − n)!` | `RunsWithin.rdProg`, `RunsWithin.rdProg_general`, `wf_rdProg` |
| **No stuck orbit**: `c = \|rs\| · m` for a preserved colored partition with `4t ≤ 3m`, `c = \|rs\| · max(m, uB!)` for a coloured Johnson structure | `RunsWithin.rdProg_ns`, `rd_ns_part`, `rd_ns_cj`, `rd_orbit_free`, `rd_orbit_cj`, `RunsWithin.rdProg_part_ns`, `RunsWithin.rdProg_cj_ns` |
| The charges hold for the Schreier–Sims backend (`sIn = N²`) | `rd_ss_bounds` |

### Phase 6 — checks (`GraphIsoChecks/MainSteps.lean`)

Kernel-checked examples (`decide`). An instrumented sub-solver records the actual sub-calls,
and each step's answer is compared with the brute-force coset. The children are checked
against the step's `ChildList`, `MeasLt` and `SizeChild`, and hinted children for transitivity
and valid labels. Covered:
- the base case, the chain rule, M0, M1, M2a, M3 and the kernel reduction;
- transfer, `sameDegProg` and `dynSeqProg`;
- the M2b step;
- `rdProg` with tags 0, 1, 3, 4, 5 and 6.

### Audit

The build lists the axioms of 70 more principal theorems (those named in the tables). Each
depends only on `propext`, `Classical.choice` and `Quot.sound`.

## Milestone 14, stage 14j-3 — M4 (`PLAN-14.md` §14.3)

In `GraphIso/Main/M4*.lean`, namespace `GraphIso.Main`, except `GraphIso.IsLeftCover.trans`.

### Phase 1 — covers, bridges and individualization (`Main/M4Bridge.lean`)

| Statement | Name |
|---|---|
| Composition of left covers; the product list of representatives | `IsLeftCover.trans`, `isLeftCover_prodRepsD`, `length_prodRepsD`, `RunsWithin.prodRepsLProg` |
| The window restriction is `baseHom`; extension of a leaf along the window's numbering, preserved by its stabilizer | `baseHom_winE`, `restrictHom_baseWin_val`, `decodeOut_extD_shE`, `baseHom_extOut`, `leafStab_baseHom_extOut`, `leafStab_le` |
| The coloured Johnson structure with the colouring `{S, rest}`: preserved, colour classes outside `V₀` of at most `m/2` points when `2\|S\| ≤ m` | `cj_ext_stab`, `cj_ext_hq` |
| Individualization: `H = fixFirst G n (d − 1)` is transitive and not 2-transitive on the rest of the base | `pointwiseStab_range'`, `indiv_trans`, `indiv_not_two`, `one_le_degree`, `indiv_of_degree` |

### Phase 2 — the structure (`Main/M4Struct.lean`)

| Statement | Name |
|---|---|
| The orbital configuration of `H` on `Γ ∖ S`: orbital, `H`-invariant, coherent, homogeneous, not a clique; uniprimitive when every colour graph is connected | `msPsi_val`, `ms_orbital`, `ms_relab`, `ms_coherent2`, `ms_config`, `ms_uniprimitive` |
| The leaves: valid, orbit at most the tree count; the components leaf is fixed | `ms_leaves`, `ms_comp_fixed` |
| **The structure program**: `K` is the stabilizer of the first leaf, with a cover of `H` by at most the count | `RunsWithin.m4StructProg`, `m4Struct_spec`, `wf_m4StructProg` |

### Phase 3 — the step (`Main/M4Step.lean`)

| Statement | Name |
|---|---|
| The run and the composition | `indColsD_eq`, `m4_run`, `m4_ps_gens_le`, `m4_core` |
| `K` preserves the extended leaf; the partition and Johnson facts | `m4_K_rel`, `m4_part_facts`, `m4_cj_facts` |
| **M4**: `StepChild` children, `c = \|reps\| · m!`; with no stuck orbit under explicit numeric conditions, `c = \|reps\| · max(m, uB!)` | `RunsWithin.m4StepProg`, `RunsWithin.m4StepProg_ns`, `wf_m4StepProg` |
| The degree under `TransitivityBound`; the numeric conditions from `2(d−1) + 6 ≤ m`; the charges | `m4_deg_le`, `m4_deg_le_T`, `m4_numeric`, `m4Charges_exact` |

### Phase 4 — checks (`GraphIsoChecks/MainM4.lean`)

Kernel-checked examples (`decide`):
- `m4StructProg`: the disconnected case on `D₄`, and soj leaves on `D₅` and `C₅`;
- the composed cover and individualization.

Kernel-checked executions in pieces (`GraphIsoChecks/Exec.lean`; since stage 14j-4):

| Statement | Name |
|---|---|
| The run's tokens read exactly the children, the chain steps and the `kernel` calls of the trace | `tokKids_flatMap`, `tokSteps_flatMap`, `tokKer_flatMap`, `m4RunQ_flatMap`, `runs_of_tok` |
| **The whole M4 step** on `AGL(1,5)` (components branch) and `C₅` (uniprimitive branch): the answer, the children's predicates and the tags, on the actual run of `m4StepProg` | `m4_step_agl`, `m4_step_c5`, `m4_step_agl_tr`, `m4_step_c5_tr` |

Supplementary `#eval` runs: the step on `D₅`, and the Petersen action of `S₅`.

### Audit

The build lists the axioms of 42 more principal theorems (those named in the tables). Each
depends only on `propext`, `Classical.choice` and `Quot.sound`.

## Milestone 14, stage 14j-4 — M5, correctness and the plain cases (`PLAN-14.md` §14.4)

In `GraphIso/Main/M5*.lean`, namespace `GraphIso.Main`.

### Phase 1 — restriction to window and base (`Main/M5Restrict.lean`)

| Statement | Name |
|---|---|
| The iso set through the restriction to `w ∪ base`, with the kernel | `rb_iso_one_eq`, `rb_iso_eq`, `rb_iso_eq_empty`, `AnsOK.rb_none`, `AnsOK.rb_lift`, `RunsWithin.rbLiftProg` |
| **A giant base action makes the restriction faithful on the window** | `rb_alt_two`, `rb_proper_label`, `rb_baseHom_eq_one` |
| The restricted hinted instance: valid, the same measure, window = string positions | `rb_equivar`, `rbHInst_valid`, `rbHInst_measure` |
| **The restriction as a program** | `RunsWithin.restrictBaseProg`, `wf_restrictBaseProg` |

### Phase 2 — certificates and the case decision (`Main/M5Cert.lean`)

| Statement | Name |
|---|---|
| Certificates with the hinted sub-solver; calls counted | `m5_hinstValid_step`, `m5_stepSub`, `RunsWithin.m5CertProg`, `fullCost_le_count`, `wf_m5CertProg` |
| The full-group map: contained, base-invariant, local, natural, matching | `m5Fmap_le`, `m5Fmap_base`, `m5Fmap_loc`, `m5Fmap_relabel`, `m5Fmap_matchesW` |
| **The case decision with the Case 2a/2b separation**; `(k−2)`-transitive groups contain `Alt` | `alt_le_of_tupTrans`, `m5_hFalt`, `m5_tupTrans_iff`, `RunsWithin.m5CaseProg`, `m5Case_spec`, `wf_m5CaseProg` |

### Phase 3 — Align with reduce-and-derive (`Main/M5Align.lean`)

| Statement | Name |
|---|---|
| The uniform branch cost: a maximum over all valid representatives | `exists_allPermsD`, `ar_branch_max`, `ar_K_fix` |
| **Align with reduce-and-derive**: general, and no stuck orbit for partitions and coloured Johnson structures | `RunsWithin.alignRd`, `RunsWithin.alignRd_general`, `RunsWithin.alignRd_part_ns`, `RunsWithin.alignRd_cj_ns`, `wf_alignRdProg` |

### Phase 4 — the cases (`Main/M5Cases.lean`)

| Statement | Name |
|---|---|
| **Case 1** | `RunsWithin.m5Case1Prog`, `RunsWithin.m5Case1Prog_ns`, `wf_m5Case1Prog` |
| **Case 2a**: the pullback's sub-calls restricted, counted | `m5_pbSub`, `c2aCost_count`, `RunsWithin.m5Case2aProg`, `wf_m5Case2aProg` |
| **Case 2b**: general, and partition leaves | `RunsWithin.m5Case2bProg`, `m5_leaf2b_valid`, `RunsWithin.m5Case2bProg_part`, `wf_m5Case2bProg` |
| **Case 3**, with the fallback to M3 | `m5_c3First_unique`, `RunsWithin.m5Case3Prog`, `wf_m5Case3Prog` |
| **Case 3 with a partition leaf and no twins**: no fallback, factor `c3R · m`; the thresholds exclude twins | `m5_fix_iff_supp`, `m5_no_twins`, `RunsWithin.m5Case3Prog_part` |

### Phase 5 — the dispatcher and the step (`Main/M5Core.lean`, `Main/M5Step.lean`)

| Statement | Name |
|---|---|
| The fixed points of `ψ(F)`; the case decision is invariant under isomorphisms | `fixPtsD_spec`, `m5_Fmap_iso`, `m5_isA_iff`, `m5_large_iso`, `m5_tupTrans_iso` |
| **The dispatcher and the core** | `RunsWithin.m5Dispatch`, `RunsWithin.m5CoreProg`, `wf_m5Dispatch`, `wf_m5CoreProg` |
| **No stuck orbit**: the dispatcher and the core with partition leaves and no twins | `RunsWithin.m5Dispatch_ns`, `RunsWithin.m5CoreProg_ns` |
| **M5**: the restriction and the core; the giant survives the restriction | `m5s_giant`, `RunsWithin.m5StepProg`, `wf_m5StepProg` |

### Phase 6 — checks (`GraphIsoChecks/MainM5.lean`, `GraphIsoChecks/MainM5b.lean`)

Single kernel checks (`decide`): the restriction; the case decision.

Kernel-checked executions in pieces. Each is a theorem
`∃ v s, RunsS ssOracle body0 recF P v s ∧ Q v s = true` about the actual program `P`, with `Q`
comparing the answer with brute force and the children with the spec's stated bounds
(`kidsOK`). All fixtures have relaxed parameters (`k ≤ 3`, `m ≤ 5`): the checks stand on their
own, not as instances of the spec.

| Statement | Name |
|---|---|
| The dispatch: Case 1, decisions that differ, Case 2a | `MainM5.disp_case1`, `MainM5.disp_differ`, `MainM5.disp_case2a` |
| The certificates on the restricted instance: their values and `certCount` | `MainM5.cert_xA`, `MainM5.cert_yA`, `MainM5.cert_xB`, `MainM5.cert_yB` |
| **The whole M5 step** on `S₄` (`m = 4`, `k = 3`): an isomorphic and a non-isomorphic pair | `MainM5.step_iso`, `MainM5.step_noniso` |
| **Case 3**: one distinguished point, a non-isomorphic pair, the fallback to M3 | `MainM5b.c3_iso`, `MainM5b.c3_noniso`, `MainM5b.c3_fallback` |
| **Case 2b** on `S₄` with `F` the Klein group | `MainM5b.c2b_klein` |
| **The whole M5 step at base size 5** (`S₅`, `k = 3`), with the certificates' values | `MainM5b.R5_eq`, `MainM5b.cert_x5`, `MainM5b.cert_y5`, `MainM5b.step5` |

Supplementary `#eval` runs: further dispatch fixtures, the whole step's children on `S₄`
acting on pairs and with `k = 2`, `A₄` with `x` constant (its certificates exceed `certCount`
at the relaxed parameters), and `m = 5` on further strings.

### The kernel execution toolkit (`GraphIsoChecks/Exec.lean`, `GraphIsoChecks/ExecSteps.lean`)

| Statement | Name |
|---|---|
| A run with its value and the `flatMap` of a summary of its trace | `RunsS` |
| Composition along the program's constructors | `RunsS.bind`, `RunsS.ite`, `RunsS.caseOption_*`, `RunsS.caseList_*`, `RunsS.foldList_*`, `RunsS.loop_*`, `RunsS.recur`, `RunsS.call`, `RunsS.prim`, `RunsS.ret` |
| A run checked by the kernel: an evaluation with the serialized value and the summary | `checkRunS`, `runsS_of_check`, `serV_injective`, `SerTree.eq_of_beq` |
| The command: split the run into pieces of at most `budget` events and composition steps, each its own declaration under the default budgets | `execRuns`, `execNode`, `execSplit`, `execFold`, `composeNode` |
| The children summary of the instrumented sub-solver is `MainSteps.records` | `ExecSteps.recF`, `ExecSteps.flatMap_recF` |

### Audit

The build lists the axioms of 69 more principal theorems (those named in the tables), and of
20 of the checks' kernel-checked executions and their bridges. Each depends only on `propext`,
`Classical.choice` and `Quot.sound`.

## Milestone 14, stage 14j-4b — coloured Johnson alignment in M5 (`PLAN-14.md` §14.5)

In `GraphIso/Main/M5CJ*.lean`, `M5Case2bCJ.lean`, `M5Case3CJ.lean`, `M5StepCJ.lean`, namespace
`GraphIso.Main`.

### Phase 1 — the Johnson leaves stay inside their domain (`Main/M5CJLeaf.lean`)

| Statement | Name |
|---|---|
| Every reachable Johnson leaf of Case 2b's leaf tree, of Split-or-UPCC and of Case 3's outcome is the extension along the numbering of a Johnson embedding on more than `(m' + 3)/2` points | `leafTree_jleaf`, `splitTree_jleaf`, `outTree_jleaf` |
| **On data**: Case 2b's listed Johnson leaves lie along `Φ ∖ S`, Case 3's along the dominant class (more than `(|V| + 1)/2` points) | `choiceLeavesD_along`, `outcomeD_along`, `c3ClsD_facts` |
| The colour bound from a Johnson datum along a list | `cj_ext_hq'`, `cj_hq_of_along` |

### Phase 2 — the canonical colourings and the coloured pairs (`Main/M5CJData.lean`)

| Statement | Name |
|---|---|
| The colourings: Case 2b's (`2 + i` at the tuple, `1` on `Φ ∖ S`, `0` off `Φ`), Case 3's (`1` on `C`, `2` on `V ∖ C`, `0` on the support), and their transport | `get_q2bD`, `get_q2bD_smul`, `get_q3D`, `outTree_transport` |
| **Canonicity**: an isomorphism carries `x`'s coloured pair to one of `y`'s | `cj2b_reach`, `cj3_reach` |
| **The colour bound `hq` of `rd_ns_cj`**, from the case conditions | `cj2b_hq`, `cj3_hq` |
| Validity of the listed pairs | `cj2b_valid`, `cj3_valid` |

### Phase 3 — the programs and the case variants (`Main/M5CJProg.lean`, `Main/M5Case2bCJ.lean`, `Main/M5Case3CJ.lean`)

| Statement | Name |
|---|---|
| The colourings, the coloured leaves and lists as programs | `RunsWithin.q2bProg`, `RunsWithin.q3Prog`, `RunsWithin.cjOfProg`, `RunsWithin.cjLeaves2bProg`, `RunsWithin.c3ClsProg`, `RunsWithin.cjOutcome3Prog`, `RunsWithin.cjStructs3Prog`, `RunsWithin.c3FirstClsProg` |
| **Case 2b's Johnson route**: the test, the route (correct answer, `StepChild` children with factor `c2bR · max(m, uB!)`, no stuck orbit) | `c2bJD_true`, `c2bJD_false`, `RunsWithin.c2bJTestProg`, `RunsWithin.c2bCJProg` |
| **Case 3's Johnson route** | `RunsWithin.c3CJRouteProg` |
| **The variants**: correct answer in both branches; 14j-4's partition hypotheses only for a leaf or structure that is not a Johnson one | `RunsWithin.m5Case2bCJProg`, `RunsWithin.m5Case3CJProg`, `wf_m5Case2bCJProg`, `wf_m5Case3CJProg` |

### Phase 4 — the dispatcher and the step (`Main/M5StepCJ.lean`, `Main/M5CJWf.lean`)

| Statement | Name |
|---|---|
| **The dispatcher, the core and the step with coloured Johnson alignment** | `RunsWithin.m5DispatchCJ`, `RunsWithin.m5CoreCJProg`, `RunsWithin.m5StepCJProg`, `wf_m5DispatchCJ`, `wf_m5CoreCJProg`, `wf_m5StepCJProg` |
| **No stuck orbit** in every case except the partition leaves of Cases 2b and 3 | `RunsWithin.m5DispatchCJ_ns`, `RunsWithin.m5CoreCJProg_ns` |

### Phase 5 — checks (`GraphIsoChecks/MainM5CJ.lean`)

Single kernel checks (`decide`): the colourings against their definitions and their programs;
the coloured leaves; a coloured Johnson leaf of Case 3's shape (`J(5, 2)` on `32` points); a
transported pair found among `y`'s pairs.

| Statement | Name |
|---|---|
| The coloured leaf `cj32`: `IsJohnson`, `JValid`, and the colour bound `hq` | `MainM5CJ.j32_johnson`, `MainM5CJ.j32_valid`, `MainM5CJ.cj32_hq` |
| **The Johnson routes' Align call** (`cjohnOps`, reduce-and-derive at `st = (2, X₀)`) on `J(4, 2)` under `S₄`, kernel-checked in pieces | `MainM5CJ.al_j42` |
| `y`'s candidates, memoized (each choice's colouring once, the leaves once per distinct colouring), equal `cjLeaves2bD` | `MainM5CJRoute.ys2bM_eq` (with `memoL_spec`, `lookL_eq`) |

Supplementary `#eval` runs: the Align call on further fixtures (`J(4, 2)`, `J(5, 2)`); the
variants `m5Case3CJProg`, `m5Case2bCJProg` and `m5StepCJProg` on 14j-4's fixtures (answers and
children against the stated bounds); the Petersen colouring's first structure is a coloured
partition.

**Staged check of Case 2b's Johnson route** (`GraphIsoChecks/MainM5CJRoute.lean`, `#eval`),
on an instance in Case 2b's setting. `G = Sym(16)` acts alike on the window and the base
(giant). `F(x)` is the
Clebsch graph's group `2⁴ : Sym(5)` and `F(y)` its conjugate by the unique isomorphism `g₀`.
The staged check:

- the degrees are `1` and `c2bJD` holds;
- `x`'s first leaf is `J(5, 2)` on ten non-neighbours, with `9 < |V₀| = 10`; `hq` holds;
- `y`'s 3840 candidates (16 distinct) come from `ys2bM`;
- the Align suffix of `c2bCJProg` runs with the distinct candidates as modified input:
  the answer is `{g₀}` and the children are `StepChild` with factor `16 · m`.

The earlier steps are evaluated through the data functions that `RunsWithin` proves the programs
return. One choice of the program takes 160 s and a 213-million-event trace, and `y` needs 240.
The full list has 3840 entries; the suffix runs on 16. Candidate membership preserves `halign`
and the answer-correctness argument, not the execution, cost or child summary. The observed
22 children belong only to this shortened suffix. Neither named case program has been run
end to end on a Johnson fixture or connected to this check by a composed execution theorem.
The amendment of `PLAN-14.md` §14.5 item 5 on 24 October 2026 accepts this coverage and closes
audit F1 by changing the criterion; it does not add a theorem or revise the archived verdicts.

### Audit

The build lists the axioms of 43 more principal theorems (those named in the tables) and of
seven of the checks' theorems (`j32_johnson`, `j32_valid`, `cj32_hq`, `al_j42`, `memoL_spec`,
`lookL_eq`, `ys2bM_eq`). Each depends only
on `propext`, `Classical.choice` and `Quot.sound`.

## Milestone 14, stage 14j-5a — the contract repair (`PLAN-14.md` §14.6)

The step specs of stages 14j-2 to 14j-4b are strengthened in place. `docs/contract-repair.md`
records each changed definition and statement, with the bound `sC` of its sub-solver predicate
and how the old statement follows.

| Statement | Name |
|---|---|
| Children's generator bound; nonempty windows; at most `c · n` children | `SizeChild` (`gens_le`), `ChildList` (`pos`), `ChildList.length_le` |
| One bound closed under the recursion; a larger bound or factor | `SizeChild.closed`, `SizeChild.mono`, `ChildList.mono_factor` |
| A hinted window has a point; the largest of `f 0, …, f k` | `HInstValid.win_pos`, `supTo`, `le_foldr_max`, `le_supTo` |
| The loop's sub-calls with at most `sC` generators | `MlChild` |
| Reduce-and-derive's generator counts for every tag with a child (scope amendment) | `DOutGens` |
| Case 2a's generator hypothesis is satisfiable for every backend | `m5_exists_genOut_le`, `m5ListsOver`, `m5_mem_listsOver` |

Changed protected statements:
- **(sub-solver bound only)** `RunsWithin.chainProg`, `kerRedProg`, `m3Prog`, `m0StepProg`,
  `m1StepProg`, `m2aStepProg`, `m2bLoopProg`, `m2bStepProg`.
- **(and `RDOrbit` through `DOutGens`)** `rdProg`, `rdProg_part_ns`, `rdProg_cj_ns`,
  `m4StepProg`, `m4StepProg_ns`, `alignRd`, `m5Case1Prog`, `m5Case2bProg`, `m5Case3Prog`,
  `m5Case3Prog_part`, `m5Dispatch`, `m5CoreProg`, `m5CoreProg_ns`, `m5StepProg`,
  `m5Case2bCJProg`, `m5Case3CJProg`, `m5DispatchCJ`, `m5CoreCJProg`, `m5CoreCJProg_ns`,
  `m5StepCJProg`.
- **(and the satisfiable `hgR` with a fresh `sR`)** `m5Case2aProg`.

Every one but `m5Case2aProg` also gains `pos` in its `ChildList` conclusion.

The checks (`GraphIsoChecks/MainSteps.lean` and the M4/M5 check modules) use the new
definitions:
- `listB_iff` matches the new `ChildList`;
- `childrenOK` and `kidsSizeOK` bound the recorded children's generator counts by the step's
  `sC` (`N²` for the steps through reduce-and-derive).

### Audit

The build lists the axioms of the new lemmas: `ChildList.length_le`, `ChildList.mono_factor`,
`SizeChild.closed`, `SizeChild.mono`, `HInstValid.win_pos`, `le_foldr_max`, `le_supTo`,
`m5_mem_listsOver` and `m5_exists_genOut_le`. Each depends only on `propext`,
`Classical.choice` and `Quot.sound`.

## Milestone 14, stage 14j-5b — Schreier–Sims counts and the mini procedure (`PLAN-14.md` §14.7)

| Statement | Name |
|---|---|
| Backend bounds at any generator bound `s ≥ n²` | `Sims.ssBoundsS`, `rd_ss_boundsS` |
| Schreier–Sims meets every contract for `|gs| ≤ max S M²` | `Sims.ssBnd`, `Sims.ssOracle_meets_bnd`, `Sims.ssCtxB`, `Sims.ssBoundsB` |
| An outcome for `ssBnd S` has the generator counts `DOutGens S` | `dOutGens_of_dOutcome`, `DSetting.ssBnd` |
| **The strengthened `DOutGens` for Schreier–Sims**, tags `1`–`5` | `rd_ss_dOutGens_free`, `rd_ss_dOutGens_cj` |
| `RDOrbit` for Schreier–Sims without the `DOutGens` hypothesis | `rd_orbit_free_ss`, `rd_orbit_cj_ss` |
| M4's `hKs`; M2b's `hsR`, `hsR'`; M5's `hsK`, `hsKR`; Case 2a's `hgR`; `Bm` | `ss_m4K_gens_le`; `ss_hsR`, `ss_m2bRb_gens_le`; `ss_hsK`, `ss_kernel_gens_le`; `ss_hgR`; `ssBm` |
| The mini procedure and its entry, well formed | `miniBody`, `miniEntry`, `miniBody_wf`, `miniEntry_wf` |
| Generator counts of M0's child and the kernel | `ss_rebase_gens_le`, `ss_m0_gens_le`, `ss_ker_gens_le` |
| Case facts: a hinted base is nonempty; M0's case; a window has at most `n` points | `HInstValid.base_pos`, `mini_m0_case`, `HInstValid.winSize_le`, `IsOrbitPartition.length_le_win` |
| The domain, the rank, the cost bound | `MiniDom`, `miniRk`, `miniRk_lt`, `miniC`, `miniC_mono`, `le_miniC`, `miniW`, `miniCost` |
| A child stays in the domain with a smaller rank | `mini_child`, `StepChild.getD_le`, `FreeChild.getD_le`, `ChainChild.getD_le`, `mini_rk_pos` |
| The sub-solver hypothesis from the induction hypothesis | `MiniIH`, `mini_hsub` |
| The steps with their work on the domain; one step | `mini_chain`, `mini_m0`, `mini_m3`, `mini_cost_le`, `mini_step` |
| **Correctness and cost by induction on the rank** | `mini_spec` |
| **The entry on every valid instance, with no hypothesis** | `miniSolve_ss` |

The checks (`GraphIsoChecks/MainMini.lean`, `decide +kernel`) run `miniEntry` on six fixtures:
an empty window; a fixed window with and without an isomorphism; the chain rule; `D₄` (M0,
M3) with and without an isomorphism. Each compares the answer with brute force, the trace's
cost with `miniSolve_ss`'s bound, and the recursion's path.

### Audit

Every new declaration is listed in `GraphIsoChecks/AxiomAudit.lean`, and the new modules are
in its import closure.

## Milestone 19, stage 19d — the Palomar coset statement (`PLAN-19.md` §6)

The statement of `PLAN-19.md`'s Appendix B, with its definitions added to
`GraphIso/Palomar/Statement.lean` (Mathlib only), and its proofs from `gi_coset_tm0_vertices`
(`GraphIso/Palomar/Bridge.lean`). No existing statement changes; stage 19c's encoding lemmas are
now instances of the generic ones below.

| Statement | Name |
|---|---|
| **The words** (Mathlib only): a permutation of `Fin n`: the images of `n - 1` down to `0`, then the inverse images; the coset machine's output: `no`, or `yes`, a permutation and the list of the generators, between the marks | `permWord`, `cosetWord` |
| **The encodings, for every map `f` of the symbols that writes numbers and lists as `g` writes the library's symbols** | `Writes`, `Writes.natWord_map`, `Writes.listWord_map`, `Writes.numberList_map`, `Writes.graphWord_map`, `Writes.input_map`, `Writes.permWord_map` (valid data), `Writes.gensWord_map` (valid generators), `writes_symbolEmbedding` |
| **The coset machine's embeddings** into `giCosetTM0`'s tape alphabet: `cosetIn` to the input symbols, `cosetOut` to the output symbols (`yes` and `no` to `tag some` and `tag none`); injective, no blank image | `CosetAlphabet`, `cosetAlphabet_eq`, `cosetInMap`, `cosetOutMap`, `cosetInMap_injective`, `cosetOutMap_injective`, `cosetIn`, `cosetOut`, `cosetIn_ne_default`, `cosetOut_ne_default`, `writes_cosetIn`, `writes_cosetOut`, `cosetIn_input_map` |
| **The output word is the output tape**: for valid data `r`, `cosetWord (cosetData n r)` maps to `encodeOut (ser Ty.giCoset r)` | `cosetData`, `cosetWord_map` |
| **The coset word determines the answer**: numbers, lists of the words of a prefix code, and permutations are prefix codes | `PrefixCode`, `eq_of_append_cons`, `natWord_prefixCode`, `listWord_cons`, `PrefixCode.list`, `permWord_prefixCode`, `cosetWord_injective_proof` |
| **The Palomar coset statement**: there are a `TM0` machine with finitely many symbols and states, injective maps `ιin`, `ιout` of the symbols into its alphabet with no blank image, and `c`, such that for all `n` and simple graphs `G`, `H` on `Fin n` there is an answer `r` with `r = none ↔ IsEmpty (G ≃g H)`; for `r = some (τ, gs)`, a permutation `φ` underlies an isomorphism exactly when `τ⁻¹ φ` is in the subgroup generated by `gs`; and started on `ιin (input G H)`, the machine makes at most `2 ^ (c (⌊log₂ n⌋ + 1) ^ 8)` transitions and halts with the tape `ιout (cosetWord r)` | `gi_coset_singleTape_proof` |

The checks (`GraphIsoChecks/Palomar.lean`, `decide +kernel`): the word of the 3-cycle
`0 ↦ 1 ↦ 2 ↦ 0`; the output words of the 3-cycle with the generators `[swap, 3-cycle]`, and of
`none`, against `encodeOut (ser Ty.giCoset r)`, symbol by symbol; the coset theorem instantiated
on `pp` (`some (τ, gs)` with `τ` underlying an isomorphism) and on `pt` (`none`); negative
controls: the images listed from `0` upwards give another word, and the word of `none` is not
the word of any `some`.

A local Comparator run with the three theorems `gi_singleTape`, `cosetWord_injective` and
`gi_coset_singleTape` (a scratch challenge: the statement file's text, then the theorems with
`by sorry`) accepts the solution, and rejects it when the challenge's `permWord` lists the images
from `0` upwards, or when its coset clause has `φ * τ⁻¹` instead of `τ⁻¹ * φ`.

### Audit

Every new declaration is listed in `GraphIsoChecks/AxiomAudit.lean`.

## Milestone 19, stage 19c — the Palomar statement (`PLAN-19.md` §5)

The statement of `PLAN-19.md`'s Appendix A, with definitions that use Mathlib only
(`GraphIso/Palomar/Statement.lean`), and its proof from `gi_tm0_vertices`
(`GraphIso/Palomar/Bridge.lean`), in namespace `GraphIsoPalomar`. No existing statement changes.

| Statement | Name |
|---|---|
| **The words** (Mathlib only): the symbols; a number: its binary digits, least significant first (`Nat.bits`), then `endNum`; a list: each element after `cons`, then `nil`; a graph on `Fin n`: the neighbour lists, in increasing order, of the vertices `n - 1` down to `0`; the input `n`, `G`, `H` and the output `yes` or `no`, between the marks | `Sym`, `natWord`, `listWord`, `nbrs`, `graphWord`, `input`, `output` |
| **The symbol embedding** into `giDecTM0`'s tape alphabet: injective, no symbol mapped to the blank | `TapeAlphabet`, `tapeAlphabet_eq`, `symbolMap`, `symbolMap_injective`, `symbolEmbedding`, `symbolEmbedding_ne_default` |
| **The encodings agree**: `Nat.bits = toBits`; the words map to `ser .nat`, `ser (.list .nat)` and `ser Ty.graph` of `GraphData.ofSimpleGraph`; the input word to `encodeIn p.enc` at `p = ⟨n, G, H⟩`, the output word to `encodeOut (ser .bool b)` | `bits_eq_toBits`, `natWord_map`, `listWord_map`, `numberList_map`, `graphWord_map`, `input_map`, `output_map` |
| **The Palomar statement**: there are a `TM0` machine with finitely many symbols and states, an injective map `ι` of the symbols into its alphabet with no blank image, and `c`, such that for all `n` and simple graphs `G`, `H` on `Fin n`, started on `ι (input G H)`, the machine makes at most `2 ^ (c (⌊log₂ n⌋ + 1) ^ 8)` transitions and halts with the tape `ι (output b)`, where `b = true ↔ Nonempty (G ≃g H)` | `gi_singleTape_proof` |

The checks (`GraphIsoChecks/Palomar.lean`, `decide +kernel`): `natWord` at `0` and `6`;
`Nat.bits = toBits` on `0, …, 64`; the input words of the empty pairs at `n = 0, 1`, of `pp` and of
`pt` against `encodeIn p.enc`, and the output words against `encodeOut`, symbol by symbol
(`wordEq`); the theorem instantiated on `pp` (`output true`) and `pt` (`output false`); negative
controls: the output words differ under every injective map, a path and the triangle have
different words, `graphWord` lists the vertices in decreasing order.

A local Comparator run (`lake comparator --inadvisably-no-sandbox`) on a scratch `Challenge.lean`
(the statement file's text, then the theorem as `gi_singleTape` with `by sorry`) and
`Solution.lean` (importing the bridge) accepts the solution, and rejects it when the challenge's
`output` swaps `yes` and `no`.

### Audit

Every new declaration is listed in `GraphIsoChecks/AxiomAudit.lean`, and the new modules are
in its import closure.

## Milestone 18, stage 18f — graph isomorphism on a single tape (`PLAN-18.md` §7)

In `GraphIso/TM/SingleTape/GI.lean` (stages 18d–18e and milestone 17). No existing statement changes.

| Statement | Name |
|---|---|
| **The single-tape machines**: the two machines of milestone 17 compiled (finite stack alphabets by 18d's `finite_toFinTM2`) | `giDecTM0`, `giCosetTM0` |
| **The input tapes**: `L₀ = \|p.enc\| + 2` | `length_giDec_tape`, `length_giCoset_tape` |
| **The growth**: `C (L + 2 ^ (c (λ(L) + 1) ^ 8) + 1)² ≤ 2 ^ ((C + 2 c + 4) (λ(L + 2) + 1) ^ 8)` | `compile_growth` |
| `λ(L₀) + 1 ≤ 8 (λ(n) + 1)`; `2 ^ (c (λ(L₀) + 1) ^ 8) ≤ 2 ^ (c 8⁸ (λ(n) + 1) ^ 8)` | `GraphPair.lam_tape_le`, `exp_tape_le_vertices` |
| **Decision on one tape, in the number of vertices**: on every pair, `giDecTM0` outputs `encodeOut (ser .bool (isoDecide p))` on `encodeIn p.enc` within `2 ^ (c (λ(n) + 1) ^ 8)` transitions | `gi_tm0_vertices` |
| **The coset on one tape, in the number of vertices**: `giCosetTM0` outputs `encodeOut (ser Ty.giCoset r)` within `2 ^ (c (λ(n) + 1) ^ 8)`, with the full specification of `gi_coset_tm` | `gi_coset_tm0_vertices` |
| **The same, in the input tape's length `L₀`**: within `2 ^ (c (λ(L₀) + 1) ^ 8)` | `gi_tm0`, `gi_coset_tm0` |

The checks (`GraphIsoChecks/TMGISingleTape.lean`; theorem instantiations, the compiled GI
machines are not run): the machines are finite; the input tapes' lengths (`tape_pp`, `tape_pt`,
`tape_coset`); each of the four theorems instantiated on `pp` (`true`, `some`) and `pt` (`false`,
`none`), and the two vertex theorems also on the empty pairs at `n = 0, 1` (`true`, `some`);
negative controls.

## Milestone 18, stage 18e — the compiler from stack machines to single-tape machines (`PLAN-18.md` §6)

In `GraphIso/TM/SingleTape/IO.lean` and `GraphIso/TM/SingleTape/Compile.lean` (mathlib only). No
existing statement changes.

| Statement | Name |
|---|---|
| **Mirrored tapes**: a tape read from right to left; work tapes as mirrored tapes of `Sym` | `flipDir`, `tapeMirror`, `tapeMirror_move`, `workMap`, `unwork`, `workTape`, `workTape_move`, `workTape_write` |
| **Simulated statements**: moves reversed, `halt` as a jump; the image of the result, runs of the same length, supports | `simStmt`, `simCfg`, `stepAux_simStmt`, `steps_sim`, `supportsStmt_simStmt` |
| **Scanning loops**: one step per symbol, in either direction | `scan_steps` |
| **The compiled machine**: the input adapter, mathlib's simulator, the output adapter | `Lab`, `cell`, `inCell`, `outCell`, `toWork`, `setBottom`, `outOf`, `toOut`, `compM` |
| **The input adapter**: `\|x\| + 3` steps to mathlib's initial simulator configuration, mirrored | `inMark_tape`, `input_steps` |
| **The output adapter**: when `tm` halts the simulator's tape holds exactly the output stack; `\|y\| + 2` steps to `Tape.mk₁ (encodeOut y)` | `halt_tape`, `outOf_outCell`, `toOut_outCell`, `output_steps` |
| **The run**: within `(2 s² + 3 s + 6) (\|x\| + T + 1)²` steps | `compM_run` |
| **Finite control**: statements of size at most `4`, a finite support, a finite alphabet | `stmtSize_simStmt`, `compM_size`, `compM_supports`, `finite_cSym` |
| **The transfer theorem**: `TM2OutputsInTime tm x (some y) T` gives `TM0OutputsInTime (compile tm hΓ) (encodeIn x) (encodeOut y) (compileConst tm (\|x\| + T + 1)²)`, `compileConst tm = 4 (2 s² + 3 s + 6)` | `compile`, `compileConst`, `compile_outputs` |

The checks (`GraphIsoChecks/TMSingleTape.lean`, no GI imports): the compiled reversal machine run
by the kernel (exactly `63` transitions on `[true, false]`, the framed output, the head and the
blanks; `17` on `[]`), `compile_outputs` instantiated and the exact timed output `rev_exact`; the
compiled negation machine of 17a (`compile_outputs` for every input; kernel runs on `[]` and
`[true]`); negative controls.

## Milestone 18, stage 18d — machines with local state on one tape, counted, with finite control (`PLAN-18.md` §5)

In `GraphIso/TM/SingleTape/TM1Sim.lean` and `Sim.lean` (mathlib only, for mathlib's `TM1to0.tr`,
`trCfg`, `TM2to1.tr` and `TrCfg`) and `Programs.lean` (the project's `toFinTM2`). No existing
statement changes.

| Statement | Name |
|---|---|
| **Statement size**: moves and writes on the longest path, plus one for `goto`/`halt` | `stmtSize` |
| **One step, counted**: between `1` and `stmtSize` transitions, `trCfg` preserved; `N` steps within `N s`; halting preserved | `stepsIn_of_step_eq`, `stepAux_steps`, `tr1_simIn`, `tr1_run`, `tr1_halt` |
| **Finite control**: the reachable states, finite under a finite support; the restriction has the same runs and halts | `Reachable`, `Reachable.mem`, `finite_reachable`, `restrict`, `restrict_eq_some`, `restrict_steps`, `restrict_halt` |
| **The finite machine** of a finitely supported `TM1` machine with finite alphabet and local states; its timed output within `N s` | `FinTM0.ofTM1`, `ofTM1_outputs` |
| **The simulator's statements** have size at most `3`; the stack machine's labels support its program | `stmtSize_trNormal`, `stmtSize_tr`, `supportsStmt_univ` |
| **The composed simulation, counted**: `N` stack-machine steps within `3 N (1 + s (2 (B + s N) + 2))` single-tape transitions; a bundled machine's timed output within `3 (2 s² + 2 s + 1) (T + 1) (\|x\| + T + 1)` | `sim_run`, `initList_eq_init`, `sim_outputs` |
| **The finite simulator**: `TM1to0.tr (TM2to1.tr tm.m)` on its reachable states (start label `normal tm.main`), finite by both support translations; its halting run from `trInit tm.k₀ x` to the stacks of `haltList tm y` | `mainInhabited`, `tr_supports_univ`, `finite_Γ'`, `simTM0`, `simTM0_outputs` |
| **The project's compiled stack programs** have finite stack alphabets (symbols and return labels); a run of `main` in `n` steps gives a finite-simulator run within `3 (2 s² + 2 s + 1) (n + 2) (\|l\| + n + 2)` | `finite_toFinTM2`, `exec_simTM0` (`Programs.lean`) |

The checks (`GraphIsoChecks/TM1Sim.lean`, no GI imports): `walkM` run by the kernel (`3` steps;
the translation exactly `9 = 3 · 3`; the restriction the same `9`), a timed output by
`ofTM1_outputs` and by the kernel, negative controls (not halted after `8`; no other output; a
trailing blank).
The checks of the composition (`GraphIsoChecks/TMSim.lean`, no GI imports): the finite simulators
of the reversal machine (exactly `37` transitions, bound `3 · 312`) and of the compiled negation
program of 17a (exactly `161` on `[true, false]`, bound `18360` by `exec_simTM0`; `25` on `[]`),
run by the kernel; negative controls.

## Milestone 18, stage 18c — the simulation of stack machines on one tape, counted (`PLAN-18.md` §4)

In `GraphIso/TM/SingleTape/TM2Sim.lean` (mathlib only), for mathlib's `TM2to1.tr` and `TrCfg`. No
existing statement changes.

| Statement | Name |
|---|---|
| **Stack actions** of a statement (longest path, every branch); a step changes each stack's length by at most that; `N` steps by at most `s N` | `acts`, `stepAux_length_le`, `step_length_le`, `run_length_le` |
| **The shuttles**: `n` cells out to a stack's top and back are exactly `n` steps each | `go_steps`, `ret_steps` |
| **One step, counted**: from stacks of length at most `B`, a step is simulated within `1 + s (2 (B + s) + 2)` steps, `TrCfg` preserved | `trNormal_steps`, `tr2_step` |
| **Runs, counted**: `N` steps within `N (1 + s (2 (B + s N) + 2))` | `tr2_run` |
| **Bundled machines**: `TM2OutputsInTime tm x (some y) T` gives a simulator run between `TrCfg`-related configurations within `(2 s² + 2 s + 1) (T + 1) (\|x\| + T + 1)` steps, `s = tmActs tm`; `\|y\| ≤ \|x\| + s T` | `tmActs`, `tmActs_le`, `initList_length_le`, `run_bound_le`, `tr2_outputs`, `length_out_le` |

The checks (`GraphIsoChecks/TM2Sim.lean`, no GI imports): the reversal machine `revTM` (kernel
run of the machine, `3` steps, and of its simulator, exactly `21` steps against the bound `312`;
`tr2_outputs` instantiated), `mixM` (five stack actions in one step, an empty-stack pop, stacks
of different lengths: exactly `22` simulator steps against `81`), negative controls.

## Milestone 18, stage 18b — finite single-tape machines and timed outputs (`PLAN-18.md` §3)

In `GraphIso/TM/SingleTape/Model.lean` (namespace `GraphIso.TM.SingleTape`; mathlib only). No
existing statement changes.

| Statement | Name |
|---|---|
| **Counted runs**: `(flip bind f)^[n] (some a) = some b`; composition, unfolding, determinism of halting runs, `Reaches`, `EvalsToInTime` | `StepsIn`, `stepsIn_succ`, `StepsIn.trans`, `StepsIn.halt_unique`, `StepsIn.reaches`, `StepsIn.evalsToInTime`, `EvalsToInTime.stepsIn` |
| **Quantitative simulation**: each transition of `f₁` matched by at most `κ` transitions of `f₂`; `N` transitions by at most `N K` | `SimIn`, `SimIn.run` |
| **Finite single-tape machines**: mathlib's `TM0.Machine`, `Finite` alphabet and states, blank and start as the `Inhabited` defaults | `FinTM0`, `FinTM0.step` |
| **Timed outputs**: from `TM0.init l`, at most `m` transitions to a halting configuration with tape `Tape.mk₁ l'` (the halt not counted); in `TM0.eval`, unique up to trailing blanks, exact running time | `TM0OutputsInTime`, `.mono`, `.mem_eval`, `.unique`, `.steps_le` |
| **Framed tapes**: `lmark :: x ++ [rmark]` over `Sym W α β` (blank `work default`), lengths `\|x\| + 2`, injective, injective as tapes | `Sym`, `encodeIn`, `encodeOut`, `length_encodeIn`, `length_encodeOut`, `encodeIn_injective`, `encodeOut_injective`, `mk_append_inj`, `mk_encodeIn_inj`, `mk_encodeOut_inj` |

The checks (`GraphIsoChecks/TMSingleTapeModel.lean`, no GI imports): framed-tape lengths and
distinct outputs by the kernel; the copy machine `copyM` run by kernel reduction on
`[true, false]` (exactly `8` transitions) and `[]` (`2`); negative controls (wrong output, too
few transitions, trailing blanks, no halt at the start).

## Milestone 18, stage 18a — graph isomorphism in the number of vertices (`PLAN-18.md` §2)

In `GraphIso/TM/Vertices.lean`. No existing statement changes.

| Statement | Name |
|---|---|
| A list of naturals below `n` serializes to at most `\|xs\| (n + 1) + 1` symbols | `length_ser_natList_le` |
| Graph data with `ValidD n n` serializes to at most `n (n (n + 1) + 2) + 1` symbols | `length_ser_graph_le` |
| **The encoding of a pair on `n` vertices** has at most `5 (n + 1)³` symbols; `λ(L) + 1 ≤ 8 (λ(n) + 1)` | `GraphPair.enc_length_le`, `GraphPair.lam_enc_le` |
| `2 ^ (c (λ(L) + 1) ^ 8) ≤ 2 ^ (c 8⁸ (λ(n) + 1) ^ 8)`; timed outputs within larger bounds | `exp_enc_le_vertices`, `outputsInTime_mono` |
| **Decision in the number of vertices**: on every pair, `toFinTM2 giDecProg .inp .out` outputs `ser .bool (isoDecide p)` on `p.enc` within `2 ^ (c (λ(n) + 1) ^ 8)` steps | `gi_tm_vertices` |
| **The coset in the number of vertices**: `gi_coset_tm` with the time `2 ^ (c (λ(n) + 1) ^ 8)`, the full specification kept | `gi_coset_tm_vertices` |

The checks (`GraphIsoChecks/TMVertices.lean`): the encoding bounds by the kernel at `n = 0, 1`
(empty graphs) and on the two paths `pp`; `gi_tm_vertices` instantiated on `pp` (`true`), `pt`
(`false`) and the empty pairs at `n = 0, 1` (`true`), `gi_coset_tm_vertices` on `pp` (`some`)
and `pt` (`none`); negative controls (input length versus vertex count, the factors of
`lam_enc_le` and `enc_length_le`).

## Milestone 17, stage 17h — graph isomorphism on Turing machines (`PLAN-17.md` §11)

In `GraphIso/TM/GI.lean` (stage 17g and milestone 16). No existing statement changes.

| Statement | Name |
|---|---|
| **Graph pairs**: `n` and simple graphs `G`, `H` on `Fin n` with decidable adjacency; the encoding `ser Ty.giInput (n, ofSimpleGraph G, ofSimpleGraph H)`, at least `n` long | `GraphPair`, `GraphPair.data`, `GraphPair.enc`, `GraphPair.n_le_enc`, `length_le_serElems`, `size_le_ser_array` |
| **The specification**: brute force over the permutations of `Fin n`; `isoDecide p = true ↔ Nonempty (p.G ≃g p.H)` | `isoDecide`, `isoDecide_iff` |
| **The output's length**: for valid data with at most `4 gN(n)²` generators, `(ser Ty.giCoset r).length ≤ 16 (n + 1) ^ 6` | `length_ser_nat_le`, `length_ser_arrNat_le`, `permValid_mem_lt`, `length_ser_perm_le`, `length_ser_coset_le` |
| **The entries and programs**: milestone 16's entry with Schreier–Sims substituted (`giCosetEntry`), and `true` exactly on `some` (`giDecEntry`); both well formed; `mainProg (qpSolver 192 181) _` | `giCosetEntry`, `giDecEntry`, `giCosetEntry_wf`, `giDecEntry_wf`, `giCosetProg`, `giDecProg`, `runs_giDec` |
| **Milestone 16 at a graph pair**: the run of the coset entry within local cost `2 ^ (c (λ(n) + 1) ^ 8)`, its answer, at most `4 gN(n)²` generators | `gi_runs` |
| **The bound**: with `n ≤ L`, a local cost of at most `2 ^ (c (λ(n) + 1) ^ 8) + 2` and an output of at most `16 (n + 1) ^ 6` symbols, `mainPoly + 1 ≤ 2 ^ ((120 (κ + c + 12) + 1) (λ(L) + 1) ^ 8)` | `exp_arith`, `poly_le_exp`, `gi_bound`, `exp_succ_le` |
| **The run of the decision program**: from the encoding of `p` to `ser .bool (isoDecide p)` within `2 ^ ((A + 1) (λ(L) + 1) ^ 8)` steps | `gi_dec_exec` |
| **Decision on Turing machines**: a `TM2ComputableInTime GraphPair.enc (ser .bool) isoDecide` with machine `toFinTM2 giDecProg .inp .out` and time at most `2 ^ (c (λ(L) + 1) ^ 8)`; that machine outputs `ser .bool (isoDecide p)` on `p.enc` within `2 ^ (c (λ(L) + 1) ^ 8)` steps | `gi_tm` |
| **The coset on Turing machines**: on every pair, `toFinTM2 giCosetProg .inp .out` outputs `ser Ty.giCoset r` within `2 ^ (c (λ(L) + 1) ^ 8)` steps; `r = none ↔ IsEmpty (G ≃g H)`; for `r = some (τ, hs)`, valid data with `τ • ⟨hs⟩` the set of the permutations underlying the isomorphisms | `gi_coset_tm` |

The checks (`GraphIsoChecks/TMGI.lean`), on graphs on `Fin 3`: `pp_iso` (two paths) and
`pt_not_iso` (a path and the triangle, the negative control), by the kernel, with
`isoDecide_iff`; the encoding of the two paths (`40` symbols) and that the two pairs' encodings
differ; `length_ser_coset_le` at `cosetData` (`43` symbols); `gi_tm` instantiated (the decision
machine outputs `true` on `pp` and `false` on `pt`, within `2 ^ (c 6 ^ 8)` steps) and
`gi_coset_tm` (`some` on `pp`, `none` on `pt`); the coset entry in the cost model on the empty
graphs (`some`, local cost `144`), the one-vertex graphs (`some`, `376`) and an edge and the
empty graph (`pe_runs`: `none`, `86100`, `54430` trace events kernel-checked in pieces of at most
`1000` events).

## Milestone 17, stage 17g — the simulation on Turing machines (`PLAN-17.md` §10)

In `GraphIso/TM/Main.lean` (stages 17a–17f). No existing statement changes.

| Statement | Name |
|---|---|
| **Stack growth**: a run of `n` steps adds at most `n` symbols to each stack | `Exec.length_le` |
| Canonical pointers: the number on `ptr` with its high zero bits dropped | `canonPtr`, `canonPtr_sat` |
| **The main program**: the counter, load, bind, the compiled entry, drop, canonical pointer, write, erase `heap` and `cnt` | `mainBody`, `mainProg` |
| The parameters of a run: loaded cells and symbols, the field and bit bounds, the final heap's cells and symbols, a unit of compiled code, the step bound `mainT` | `uB`, `heapB`, `fB`, `bB`, `nCells`, `nSym`, `qB`, `mainT`, `kP`, `dP`, `Sat.of_exec`, `visB_mono`, `heapLen_mono` |
| **The run of `main` within `mainT`** | `main_sat` |
| Powers of a base `Y ≥ 4096`; `mainT ≤ (κ (C + L + L' + 1)) ^ 120` with `κ = 4096 (wt a' + wt c + K + D + sE + 1)`, `sE = psize 1 (E Lv 0)` | `pow_step`, `pow_mono_le`, `one_le_pow'`, `le_pow_mul`, `le_pow_one`, `kappa`, `PL_le`, `lookupBound_le_pow`, `fcE_le_pow`, `allocBound_le_pow`, `mainT_le`, `mainPoly` |
| **The run**: for a well-formed entry and every run of `E` on `x` with value `v` and trace `tr`, `main` runs from `inCfg .inp (ser a' x)` to `inCfg .out (ser c v)` within `mainPoly` steps (of the local cost of `tr` and the lengths of `ser a' x` and `ser c v`) | `main_exec` |
| **On Turing machines**: `TM2OutputsInTime (toFinTM2 (mainProg Pr E) .inp .out) (ser a' x) (some (ser c v)) (mainPoly … + 1)` | `main_tm` |

The output's length is in the bound because values share cells: at a cost of about `m` a
program can build a list of `m` copies of one list of `m` numbers, whose output has at least `m²`
symbols (the check `square`: at `m = 20`, local cost `62`, an output of `2221` symbols); so no
bound of a degree independent of the program omits it (`PLAN-17.md` §10.3).

The checks (`GraphIsoChecks/TMMain.lean`) run `main` from `inCfg .inp` with the output, every
other stack (including `heap` and `cnt`) empty, empty registers and exact step counts:
`copyMain` (`42340` steps), `natMain` (`45410`), `listMain` (`67665`), `shareMain` (an output
four times as long as the input: `102694`); and `canonPtr` (`75`). On `copyRec` and `[1, 2, 3]`:
`copy_bound` (`mainPoly = 7577600 ^ 120`), `copy_exec`, `copyTM` (step count `42341`). Negative
controls: `copyMain_not_42339`, `copyMain_not_rev`.

## Milestone 17, stage 17f — the primitives (`PLAN-17.md` §9)

In `GraphIso/TM/` (`PrimLib`, `Prims`; stages 17a–17e). No existing statement changes. Routines
start with empty registers and leave every stack they do not name unchanged. They end with empty
registers, except `openTop` (the fetched cell's tag in register `1`) and the loop tests
`mkTest`, `rangeTest` (a bit in register `0`), `getTest`, `updTest` (the top of `work` in
register `0`, a bit in register `1`); the code of every primitive ends with empty registers.

| Statement | Name |
|---|---|
| Frames: `c'` agrees with `c` outside the stacks `S` | `Fr`, `Fr.refl`, `Fr.trans`, `Fr.mono`, `Fr.restore`, `fr1`, `fr2`, `fr3`, `fr_push`, `fr_pop`, `fr_set`, `fr_peek`, `HeapAt.fr` |
| **Allocation under the size invariant**; a cell from the `n` pointers on top of `work` | `HeapBnd.snoc`, `allocB_sat`, `encFields_eq_encNums`, `allocArgs`, `sum_move_le`, `allocArgs_sat` |
| Fetching the cell, or the bits of the natural, of the pointer on top of `work` | `openTop`, `openTop_sat`, `natTo`, `natTo_sat` |
| Counts (`k` increments of the empty number: value `k`, at most `k + 1` bits); moving or counting the numbers above a marker | `cntBits`, `ofBits_cntBits`, `length_cntBits_le`, `head_bits_ne_mk`, `moveAll`, `moveAll_sat`, `countAll`, `countAll_sat` |
| Walking a list onto a stack; building a list from pointers on a stack, keeping `HeapBnd` | `walkList`, `walkList_sat`, `buildListB`, `buildListB_sat` |
| The bound per unit of cost, `primB M = (2 M + 10) (fcE M M + allocBound (M² + 3 M + 2) M + 100 M + 100)`; the shape of each primitive's result | `primB`, `primB_ge`, `primB_ge'`, `primB_mono`, `ctrlB_mono`, `PrimOut`, `PrimOut.of_sat`, `PrimOut.seq`, `PrimOut.spec`, `sizes_le`, `le_mul_primB`, `le_succ_mul`, `le_succ_mul0`, `le_succ_mul1`, `le_succ_mul2`, `le_comb`, `fcE_ge`, `allocBound_ge` |
| One cell from the arguments; natural literals; projections; Booleans | `out_allocArgs`, `natLitCode`, `out_natLit`, `fstCode`, `sndCode`, `out_old`, `out_old'`, `out_fst`, `out_snd`, `notCode`, `out_not`, `dropSnd`, `dropSnd_sat`, `boolSel`, `boolSel_sat`, `andCode`, `orCode`, `out_and`, `out_or`, `finish0` |
| Arithmetic and comparisons | `natTo2_sat`, `arithCode`, `out_arith`, `out_add`, `out_sub`, `cmpCode`, `out_cmp`, `out_natEq`, `out_natLt` |
| Lists | `lengthCode`, `out_length`, `reverseCode`, `out_reverse`, `appendCode`, `out_append`, `rangeTest`, `rangeTest_sat`, `RangeInv`, `rangeBody`, `rangeCode`, `range_rev_succ`, `range_step`, `out_range` |
| Arrays: from and to lists, size, `arrayMk` | `RepList.rep_arr`, `Rep.arr_list`, `arrayOfListCode`, `out_arrayOfList`, `arrayToListCode`, `out_arrayToList`, `arraySizeCode`, `out_arraySize`, `mkTest`, `mkTest_sat`, `arrayMkCode`, `out_arrayMk` |
| Array reads (the default value's `tySize` cells past the fields) | `allocDefault`, `one_le_tySize`, `allocDefault_sat`, `getTest`, `getTest_sat`, `getBody`, `getScan`, `getFinish`, `arrayGetCode`, `GetInv`, `get_step`, `out_arrayGet` |
| Array writes (each write applied in order to the fields; out-of-bounds writes ignored) | `updTest`, `updTest_sat`, `updBody`, `UpdInv`, `upd_step`, `setTail`, `setTail_sat`, `setAt`, `setAt_sat`, `RepList.set`, `applyW`, `applyW_sat`, `reMark`, `reMark_sat`, `writesLoop`, `applyWrites_snoc`, `writesLoop_sat`, `upd_bound`, `arrayUpdateCode`, `out_arrayUpdate` |
| **Code for every primitive** | `primCode`, `Args.eq_nil`, `Args.eq_one`, `Args.eq_two`, `ArgsRep.nil_inv`, `ArgsRep.one_inv`, `ArgsRep.two_inv` |
| **The specification**: for every program, `F + 1 ≤ B`, `2 ≤ F` and `primB (B + N) ≤ Q N` for every `N`, `PrimSpec prog primCode B F K Q` | `primCode_spec` |

The checks (`GraphIsoChecks/TMPrims.lean`) run programs compiled with `primCode` (`primProg`:
load, bind, run, write), with the output, the other stacks, the registers and exact step counts:
`natOps` on `(5, 3)`, `(3, 5)`, `(4, 4)` (`44992`, `44786`, `45140` steps), `boolOps`
(`27646`, `27582`), `listOps` (`67077`), `listOps'` (`142792`), `arrOps` (`165549`), `updOps`
(`251701`), `pairDefault` (`16626`), `optOps` (`38422`), and `copyRec` (`41962`).
`primCode_spec` is instantiated; `copy_spec` is `comp_sat` for `copyRec` with `primCode` and no
premise on the primitives (it replaces the check of that name in `TMCompile`, whose premise
`PrimSpec` for `pcDemo` could not hold: finding F1 of the 17e audit), and `copy_nil` is a
concrete instance with every premise discharged. Negative controls: `natOps_not_44991`,
`arrOps_default`, `updOps_oob`.

## Milestone 17, stage 17e — the compiler (`PLAN-17.md` §8)

In `GraphIso/TM/` (`Env`, `Compile`; stages 17a–17d and the cost language). No existing
statement changes. Routines start and end with empty registers and leave every stack they do not
name unchanged.

| Statement | Name |
|---|---|
| Numbers on a stack; frames (level `k` is `ls[k]`, the last on top) | `encNums`, `encNums_nil`, `encNums_cons`, `encNums_append`, `envEnc`, `envEnc_nil`, `envEnc_concat` |
| Moving `j` numbers; copying the number at offset `j` of `env`, or a level, within `fetchB j E` steps | `moveN`, `moveN_sat`, `sum_map_le_mul`, `fetchTo`, `fetchB`, `fetchTo_sat`, `fetchLv`, `fetchLv_sat` |
| Levels, primitive code, weights of primitives, the loop marker | `Lv`, `PrimCode`, `tySize`, `pw`, `goMark`, `length_args_le`, `two_le_pw` |
| **The compiler** and its parts; the program size | `pushEnv`, `popEnv`, `fetchArgs`, `iteCode`, `optCode`, `listCode`, `foldStep`, `foldCode`, `loopStep`, `loopCode`, `comp`, `psize` |
| **The size invariant** (addresses and fields of cell `i` at most `B + i` bits, at most `F` fields); every heap satisfies it for `B`, `F` at least its length; the heap's length under it: `(encHeap h).length ≤ h.length (B + h.length + 4 + F (B + h.length + 1))` | `HeapBnd`, `HeapBnd.field_lt`, `HeapBnd.of_length`, `length_encHeap_le_bnd`, `length_encFields`, `length_encHeap_append`, `length_encHeap_mono`, `length_le_encHeap_append` |
| Frames representing contexts (entries of at most `B + h.length` bits); fetching a cell through a pointer of at most `E` bits | `EnvAt`, `EnvAt.mono`, `EnvAt.push`, `EnvAt.sub`, `EnvAt.var`, `fetchVar_sat`, `ArgsRep`, `fetchArgs_sat`, `fcE`, `fetchCellE_sat`, `fetchVarCell`, `foldHead`, `exec_ite_cond` |
| The control overhead (`ctrlB D (B + N) ≤ Q N` pays for one construct) and the step-bound arithmetic | `ctrlB`, `ctrl_le`, `fetchB_mono`, `fetchB_le_ctrlB`, `lin_le_ctrlB`, `fcE_le_ctrlB`, `fcE_mono`, `bnd_one`, `bnd_bind`, `bnd_mono`, `bnd_branch`, `bnd_recur`, `bnd_iter` |
| **The primitive specification** (code: stage 17f) | `PrimSpec` |
| The simulation, by construct; the loops by inner inductions | `Pushes`, `Sim`, `sim_ret`, `sim_bind`, `sim_prim`, `sim_ite`, `sim_opt`, `sim_list`, `sim_recur`, `foldLoop_sat`, `sim_fold`, `loopLoop_sat`, `sim_loop`, `sim_all` |
| **The simulation theorem**: under `PrimSpec`, `Q` monotone with `ctrlB D (B + N) ≤ Q N`, `K ≤ B` and size conditions on the procedure, for `Prog.Wf true Γ p₁ p₂` with `eval … fuel p₁ = some (v, tr)` and `localCost tr ≤ F`, from `HeapAt h`, `HeapBnd B F h` and a frame representing `Γ`, the compiled code appends at most `K * localCost tr` cells, keeps the invariants, pushes a pointer representing `v`, leaves the other stacks unchanged, within `(psize d p₂ + K * localCost tr) * Q N` steps | `comp_sat` |

The checks (`GraphIsoChecks/TMCompile.lean`) use `pcDemo`, code for the primitives of the test
programs. Kernel runs with the output, the other stacks, the registers and exact step counts: a
fold (`revFold`, `47016` steps), recursion (`copyRec`, `41434`), a loop on a pair (`revLoop`,
`81340`), and case analysis with a branch (`optBr`, `2206`, `2242`, `1078`). `comp_revFold` shows
the compiled fold and its levels; `h₀_bnd`, `HeapBnd.of_length` and the heap-length bound on a
concrete heap; `copyRec_wf` and `O₀` serve the simulation theorem with the primitives' code
(stage 17f; the earlier `copy_spec` under `PrimSpec` for `pcDemo`, whose premise could not hold,
was removed). Negative controls: `revFold_not_47015`, `copyRec_not_rev`, `optBr_not_two`,
`h₀_not_bnd`.

## Milestone 17, stage 17d — input and output (`PLAN-17.md` §7)

In `GraphIso/TM/` (`Ser`, `Load`, `Write`, and `Sat.loop_list` in `Sat`; mathlib and stages
17a–17c). No existing statement changes. Routines start and end with empty registers and leave
every stack they do not name unchanged.

| Statement | Name |
|---|---|
| Canonical bits of a natural, and their value | `toBits`, `ofBits_toBits`, `length_toBits_le` |
| **Serialization** of values of every `Ty` (a prefix code; arrays in reverse order); a weight of types | `ser`, `serElems`, `serElems_cons`, `length_serElems`, `ser_list`, `ser_array`, `wt`, `one_le_wt` |
| **Loops over lists**: an invariant indexed by the items still to process, a budget per item | `Sat.loop_list` |
| The loader and its parts; the bounds on cells and steps | `RepList`, `RepList.mono`, `readElems`, `buildList`, `alloc0`, `load`, `cellsB`, `ldB`, `blB` |
| Lemmas for loading | `HeapAt.frame`, `readElems_sat`, `allocBound_mono`, `cellAt_new`, `alloc0_sat`, `sum_map_const`, `buildList_sat`, `length_encFields_le`, `load_unit`, `load_bool`, `load_nat`, `load_prod`, `load_option`, `load_list`, `load_array` |
| **Loading**: from `HeapAt h`, `ser t v` on `inp` and `h.length + cellsB t v ≤ U`, the input read, cells `h'` appended (`HeapAt (h ++ h')`, at most `cellsB t v`), a pointer `l` with `l.length ≤ U` and `Rep (h ++ h') t v (ofBits l)` on `work`, other stacks unchanged, within `ldB t v U` steps | `LoadSpec`, `load_sat` |
| **Bounds for loading**: `cellsB t v ≤ wt t (L + 1)` and, for `L ≤ U`, `ldB t v U ≤ wt t (L + 1) PL U` (`L` the length of `ser t v`) | `cellsB_le`, `PL`, `PL_ge`, `ldB_le`, with `sum_le_wt`, `length_le_sum_succ`, `le_wtP`, `le_mul_of_parts`, `wtP_add`, `wtP_add1`, `sum_wtP` |
| Canonical bits of a bit list | `strip`, `toBits_eq_nil`, `toBits_bit`, `strip_cons_of_ne`, `strip_cons_of_eq`, `strip_eq_toBits`, `length_strip_le`, `head_dropWhile_false` |
| Moving numbers (keeping bit order; down to a marker) | `moveNum2`, `moveNum2_sat`, `xferNums`, `xferNums_sat` |
| Fetching and closing a cell; writing list elements | `openCell`, `openCell_sat`, `fetchCell`, `fcB`, `fetchCell_sat`, `closeCell`, `closeCell_sat`, `lookupBound_mono`, `writeElems`, `writeElems_sat`, `sum_map_fst_zip` |
| Inversion of representations | `Rep.unit_inv`, `Rep.bool_inv`, `Rep.pair_inv`, `Rep.none_inv`, `Rep.some_inv`, `Rep.nil_inv`, `Rep.cons_inv`, `Rep.arr_inv`, `Rep.list_inv`, `listTag`, `ListCell`, `length_field_le` |
| The writer and its step bound | `write`, `visB`, `fcB_visB`, `wrB`, `write_unit`, `write_bool`, `write_nat`, `write_prod`, `write_option`, `write_list`, `write_array` |
| **Writing**: from a well-formed heap `h`, `scan` empty and a pointer `p` (`\|p\| ≤ N`, `N` the heap's length in symbols) with `Rep h t v (ofBits p)`, `ser t v` pushed onto `out` (naturals canonical), the pointer consumed, other stacks unchanged, within `wrB t v N` steps | `WriteSpec`, `write_sat` |
| **Bound for writing**: `wrB t v N ≤ wt t (L + 1) visB N` | `visB_ge`, `wrB_le` |

The checks (`GraphIsoChecks/TMIO.lean`) are on `v₁ = (5, [some true, none])`. `ser_v₁` and
`ser_arr` compute serializations. Kernel runs, with all final stacks, registers and exact step
counts: `load` of `v₁` (`4660` steps, the heap `h₁` of eight cells), `write` from `h₁` (`17743`
steps), a round trip of an array, and the canonical output of a non-canonical natural through a
non-canonical pointer. `rep_v₁` is the representation of `v₁` in `h₁`; `load_spec` and
`write_spec` apply the specifications to concrete inputs. Negative controls: `load_not_4659`,
`not_rep_some_false` and `write_not_other`.

## Milestone 17, stage 17c — the heap (`PLAN-17.md` §6)

In `GraphIso/TM/` (`Heap`, `Lookup`, `Alloc`, `Rep`; mathlib, stages 17a–17b, and
`GraphIso.Cost.Program` for `Ty`). No existing statement changes. Routines start and end with
empty registers and leave every stack they do not name unchanged.

| Statement | Name |
|---|---|
| The simulator's stacks (finite) | `Stk` |
| Moving a segment `w ++ [s]` (`s ∉ w`) onto two stacks, reversed (`6 \|w\| + 10` steps) | `moveSeg2`, `moveSeg2_sat` |
| Cells `⟨addr, tag, fields⟩` on a stack; heaps (oldest first, newest on top); the scan stack; well-formed heaps (cell `i` has address `i`) | `Cell`, `encFields`, `cellBody`, `encCell`, `encHeap`, `encScan`, `HeapWF` |
| Lemmas on cells and heaps: markers, reversal, taking and dropping cells, lengths | `mk_not_mem_bits`, `mk_not_mem_encFields`, `mk0_not_mem_cellBody`, `encCell_reverse`, `mk1_not_mem_reverse`, `encHeap_append`, `encHeap_cons`, `encHeap_take_succ`, `encScan_drop`, `length_encHeap`, `one_le_length_encCell`, `le_sum_of_mem_nat`, `length_encCell_le`, `length_le_encHeap`, `length_addr_lt`, `length_cellBody` |
| Comparing the top cell's address with the pointer | `addrTest`, `addrTest_sat` |
| **Lookup**: for a well-formed heap `h`, `scan` empty and a pointer `p` with `ofBits p < h.length`, a copy of `encCell h[ofBits p]` onto `work`, the pointer consumed, every other stack as it was, within `lookupBound N \|p\| ≤ 50 (N + \|p\| + 3)²` steps (`N` the heap's length in symbols) | `lookup`, `lookupBound`, `lookupBound_le`, `lookup_sat` |
| Lists of numbers (the fields of a cell); moving them down to the marker `mk 2` | `encFields_nil`, `encFields_cons`, `encFields_append`, `length_encFields_cons`, `length_le_encFields`, `encFields_reverse_map`, `length_encFields_reverse_map`, `moveNums`, `moveNums_sat` |
| **Allocation**: from `HeapAt h` (well formed, on `heap`, `scan` empty, a counter of value `h.length` and length `≤ h.length + 1`) and fields above `mk 2` on `work`, `HeapAt (h ++ [⟨l, t, fs⟩])` with `ofBits l = h.length`, `l.length ≤ h.length + 1` and the address `l` on `work`, within `2 Lf (6 Lf + 14) + 63 n + 300` steps | `HeapAt`, `alloc`, `allocBound`, `alloc_sat` |
| **Representation** of values of every `Ty` by cells; kept by appending cells; points into the heap; inversion for naturals | `CellAt`, `Rep`, `CellAt.mono`, `Rep.mono`, `Rep.lt`, `Rep.nat_inv` |

The checks (`GraphIsoChecks/TMHeap.lean`) are kernel runs on the heap `h₃` (`5`, `none`, the
pair of them) with all final stacks, registers and exact step counts. They cover `lookup` of
each cell (`603`, `462`, `298` steps), a non-canonical pointer, and `alloc` of a `some` cell and
of a pair cell. `lookup_spec` and `alloc_spec` apply the specifications to concrete inputs.
`rep_pair`, `rep_pair_mono` and `rep_some` are representations, including after an allocation.
Negative controls: `not_rep_pair` (a wrong value), `not_rep_bool` (a wrong type) and `not_wf`
(an ill-formed heap).

## Milestone 17, stage 17b — numbers and arithmetic on stacks (`PLAN-17.md` §5)

In `GraphIso/TM/` (`Sat`, `Bits`, `Num`, `Arith`; mathlib and stage 17a only). No existing
statement changes. Routines use `4` registers (`Rg`), start and end with empty registers and
leave every stack they do not name unchanged. `M = max |xs| |ys|`.

| Statement | Name |
|---|---|
| `Sat prog x c t Q`: `x` runs from `c` within `t` steps to a configuration in `Q`; rules per construct, budget forms, loops with an invariant indexed by the remaining iterations | `Sat`, `Sat.exec`, `Sat.mono`, `Sat.act`, `Sat.skip`, `Sat.seq`, `Sat.seq_le`, `Sat.act_le`, `Sat.act_seq`, `Sat.ite_true`, `Sat.ite_false`, `Sat.ite`, `Sat.ite_true_le`, `Sat.ite_false_le`, `Sat.call`, `Sat.loop` |
| The alphabet (finite): bits, end mark, cell tags, markers | `Tag`, `Sym` |
| Bit lists, least significant first, of any length, and their values | `ofBits`, `ofBits_nil`, `ofBits_cons`, `ofBits_append`, `ofBits_lt`, `hd`, `tl`, `hd_nil`, `hd_cons`, `ofBits_hd_tl` |
| The serial processor `zipL f` (missing bits read as `false`); its output has length `M` | `zipL`, `zipL_nil`, `zipL_step`, `length_zipL` |
| Adder, subtractor, comparator: the sum with the final carry; borrow ↔ `<`, else the difference; final carry ↔ values differ | `fullAdd`, `fullSub`, `diffBit`, `zipL_add`, `zipL_add_val`, `zipL_sub`, `zipL_sub_borrow`, `zipL_sub_val`, `zipL_sub_lt`, `zipL_diff`, `zipL_diff_false` |
| The bits of `x + y` (length `M + 1`) and of truncated `x - y` (length `≤ M`) | `addBits`, `ofBits_addBits`, `length_addBits`, `subBits`, `ofBits_subBits`, `length_subBits_le` |
| Numbers on stacks (`bits l ++ nd :: …`), register vectors, conditions | `Rg`, `bits`, `bits_nil`, `bits_cons`, `bits_append`, `length_bits`, `rv`, `rv_zero`, `rv_one`, `rv_two`, `rv_three`, `update_rv_zero`, `update_rv_one`, `update_rv_two`, `update_rv_three`, `empty_eq_rv`, `Cond.or`, `Cond.or_eval`, `isBit`, `isBit_eval_bit`, `isBit_eval_nd`, `isBit_eval_head` |
| Moving a number (reversed) onto one stack (`6 \|l\| + 9` steps) or two (`8 \|l\| + 11`); copying it (`14 \|l\| + 21`); dropping it (`2 \|l\| + 5`); pushing a constant (`2 \|l\| + 1`) | `moveBits`, `moveBits_sat`, `moveBits2`, `moveBits2_sat`, `copyNum`, `copyNum_sat`, `dropNum`, `exists_cons_bits`, `dropNum_sat`, `pushNum`, `pushNum_sat` |
| Moving (`4 \|w\| + 7`) or dropping (`2 \|w\| + 5`) a segment `w ++ [s]` with `s ∉ w`; emptying a stack (`2 \|a\| + 5`) | `moveSeg`, `eq_last_iff`, `moveSeg_sat`, `dropSeg`, `dropSeg_sat`, `erase`, `erase_sat` |
| **The bit processor on stacks** runs `zipL f` on two numbers in `17 M + 21` steps | `readBit`, `readBit_sat`, `bitCase`, `bitCase_sat`, `zipTable`, `zipTable_sat`, `zipBody`, `zipNum`, `zipNum_sat` |
| **Arithmetic**: `x + y` and truncated `x - y` (`23 M + 37` steps), the bits `x < y` (`19 M + 33`) and `x = y` (`19 M + 34`), `x + 1` and `x - 1` (`23 \|xs\| + 64`) | `addNum`, `addNum_sat`, `subNum`, `subNum_sat`, `ltNum`, `ltNum_sat`, `eqNum`, `eqNum_sat`, `incNum`, `incNum_sat`, `decNum`, `decNum_sat` |

The checks (`GraphIsoChecks/TMArith.lean`) are kernel runs on concrete numbers with exact final
stacks, registers and step counts (`11 + 6 = 17` in exactly the `129` steps of `addNum_sat`;
truncated `3 - 5 = 0`; `[1] = [1, 0, 0]`; copying, segments, erasing). `add_spec` and `eq_spec`
apply the specifications to concrete inputs. Negative control: `add_not_128`, the addition does
not finish within `128` steps.

## Milestone 17, stage 17a — stack programs and Turing machines (`PLAN-17.md` §3)

In `GraphIso/TM/` (`Code`, `Machine`; mathlib imports only). No existing statement changes.

| Statement | Name |
|---|---|
| Stack programs: registers, actions, conditions, code (`skip`, `act`, `seq`, `ite`, `loop`, `call`), programs | `Regs`, `Act`, `Cond`, `Code`, `Cfg`, `Program`, `Act.run`, `Cond.eval` |
| Big-step semantics with step counts; a fuel interpreter agreeing with it; determinism | `Exec`, `Exec.one_le`, `run`, `run_of_exec`, `exec_of_run`, `Exec.det` |
| Labels as continuations: `reach`, closure under successors and tails, the finite label set | `Lab`, `reach`, `mem_reach_self`, `Succ`, `reach_succ`, `reach_tail`, `labs`, `nil_mem_labs`, `body_mem_labs`, `labs_succ`, `labs_tail` |
| The compiled `FinTM2`: program stacks and a return stack, registers and a return slot, one statement per label | `Label`, `mainLab`, `MΓ`, `MState`, `MStmt`, `actStmt`, `stmt`, `mach`, `embedStk`, `mcfg`, `toFinTM2` |
| **Simulation**: `n` steps of `Exec` are exactly `n` machine steps between continuation labels; `main` halts one step later | `embedStk_update_some`, `embedStk_update_none`, `stepAux_actStmt`, `iter_succ`, `iter_add`, `sim`, `halts` |
| `initList`, `haltList` are the input and output configurations | `inStk`, `inCfg`, `initList_eq`, `haltList_eq` |
| **`TM2OutputsInTime` in `n + 1` steps** from an `Exec` of `main` in `n` steps; **`TM2ComputableInTime` with time `T + 1`** from such runs within `T` | `outputsInTime`, `stepsOf`, `stepsOf_eq`, `computableInTime` |

The checks (`GraphIsoChecks/TMCode.lean`): a recursive program complementing a list of Booleans
(`negProg`, `negBody_exec`, `main_exec`) gives `negTM : TM2ComputableInTime` for `List.map not` in
time `12 L + 9`. Kernel runs of the interpreter, and of the compiled machine's `step`: it halts
after exactly `33` steps on `[true, false]`. Negative control: running before `33` steps, so no
`TM2OutputsInTime` in `32` (`running_lt_33`, `not_outputs_32`).

## Milestone 16, stage 16b — the unconditional theorems (`PLAN-16.md` §5)

In `GraphIso/Main/QPJ.lean` (namespace `GraphIso.Main`, the growth lemmas in `GraphIso.Growth`)
and `GraphIso/Wielandt/Final.lean`. No existing statement changes. `λ = Nat.log 2`,
`Tq m = 256 (λ(m) + 1)²`, `Kpy n = 192 (λ(n) + 1)⁵`, `ℓT C' = 64 (C' + 1)²`.

| Statement | Name |
|---|---|
| **The generalized hypothesis** `QPHypJ K T C C' j`: `AltQuotientIso K`, `K` monotone, `K n ≤ C (λ(n) + 1)⁵`, `TransitivityBound T`, `TBelow T (ℓT C')`, `supTo T m ≤ j n₀` for `m ≤ 2 n₀`; `QPHyp K T C C'` gives `QPHypJ K T C C' (jMaxQ C')` | `QPHypJ`, `QPHyp.toJ` |
| The corner values with `j` for `jMaxQ C'`; `QQP C C' = QQPJ C C' (jMaxQ C')` | `qpM4J`, `qpM5J`, `qpCasesJ`, `qpWorkJ`, `qpFacJ`, `QQPJ`, `QQP_eq_QQPJ` |
| Milestone 14's thresholds, bounds, potential and headlines under `QPHypJ` | `thresholds_qpJ`, `sharpHyp_qpJ`, `caseWorkS_le_qpCasesJ`, `mainWorkS_le_QQPJ`, `caseFAB_le_QQPJ`, `winSize_add_two_le_QQPJ`, `pot_ind_stepJ`, `main_potJ`, `mainSolve_qpJ`, `mainSolve_qp_closedJ`, `mainSolve_qp_gensJ` |
| For `j ∈ PLB λ 5`: the corner values are in `QPB λ 6`; `QQPJ C C' j n₀ ≤ 2^{c (λ(n₀) + 1)⁶}` | `Growth.Main.qpM4J_qpb`, `Growth.Main.qpM5J_qpb`, `Growth.Main.qpCasesJ_qpb`, `Growth.Main.qpWorkJ_qpb`, `Growth.Main.qpFacJ_qpb`, `Growth.Main.QQPJ_qpb`, `QQPJ_le_exp` |
| **The generalized headlines** (`j ∈ PLB λ 5`): `mainSolve_qp_exp`, `giSolve_qp_exp`, `gi_qp_simpleGraph` with `QPHypJ K T C C' j` in place of `QPHyp K T C C'`, same programs and cost `2^{c (λ + 1)⁸}` | `mainSolve_qp_expJ`, `mainSolve_qp_exp_gensJ`, `giSolve_qp_expJ`, `gi_qp_simpleGraphJ` |
| `Tq` monotone; `supTo Tq m ≤ Tq k` for `m ≤ k`; `1024 (L + 1)² + 6 ≤ 2^L` for `L ≥ 21`; `TBelow Tq (ℓT 181)` | `Tq_mono`, `supTo_Tq_le`, `sq_le_two_pow`, `tBelow_Tq` |
| `jq n₀ = Tq (2 n₀) ∈ PLB λ 5`; **`QPHypJ Kpy Tq 192 181 jq`** | `jq`, `jq_plb`, `qpHypJ_final` |
| **The unconditional headlines**: the statements of `mainSolve_qp_exp`, `giSolve_qp_exp` and `gi_qp_simpleGraph` at `thrQP 192 181` and `qpSolver 192 181`, with no hypothesis | `mainSolve_final`, `giSolve_final`, `gi_simpleGraph_final` |

The checks (`GraphIsoChecks/WielandtFinal.lean`): `ℓT 181 = 2119936 > 2²¹`, `jq 1 = 1024`
(kernel `decide`), `sq_le_two_pow` at `21`; a negative control: for every `C'`,
`Tq m ≤ C' (λ(m) + 1)` fails at `m = 2^{C'}`, so `¬QPHyp K Tq C C'` (`not_tle_Tq`,
`not_qpHyp_Tq`); `qpHypJ_final`; `gi_simpleGraph_final` on the empty graphs on `Fin 3` (a
nonempty answer).

## Milestone 16, stage 16a — the transitivity bound (`PLAN-16.md` §3)

In `GraphIso/Wielandt/` (`Commutator`, `Support`, `Power` with mathlib imports only; `Bound`).
No existing statement changes. `supp x` is the support, `n = |Ω|`, `λ = Nat.log 2`,
`Tq m = 256 (λ(m) + 1)²`.

| Statement | Name |
|---|---|
| `supp ⁅x, y⁆ ⊆ I ∪ x(I) ∪ y(I)` for `I = supp x ∩ supp y`; `\|supp ⁅x, y⁆\| ≤ 3 \|I\|`; commutators are even; `\|I\| = 1` and `⁅x, y⁆ ≠ 1` give a `3`-cycle | `support_commutatorElement_subset`, `card_support_commutatorElement_le`, `sign_commutatorElement`, `isThreeCycle_commutatorElement` |
| `3`-transitivity on triples of distinct points; `\|S ∩ h(S)\| = \|{w ∈ S \| h w ∈ S}\|` | `emb3`, `exists_mem_map3`, `card_inter_map_eq` |
| **Averaging** (`G` `3`-transitive, `a, a' ∈ S` distinct, `b ∉ S`): some `h ∈ G`, `h a = a`, `h a' = b`, has `(n − 2) \|{w ∈ S \| h w ∈ S}\| ≤ (n − 2) + (\|S\| − 1)(\|S\| − 2)` | `exists_mem_card_inter_le` |
| The arithmetic of the reduction: `2 ≤ s`, `6 s ≤ n`, `2 ≤ k`, `(n − 2) k ≤ (n − 2) + (s − 1)(s − 2)` give `3 k < s` | `three_mul_lt` |
| **Small supports** (`G` `3`-transitive, `x ∈ G`, `x ≠ 1`, `6 \|supp x\| ≤ n`): `G` contains a `3`-cycle, and `Alt(Ω) ≤ G` | `exists_isThreeCycle_mem`, `alternatingGroup_le_of_support_le` |
| **Babai–Seress**: `n^n < (ord σ)^s` gives `σ^m ≠ 1` with `\|supp σ^m\| < s`; pairwise coprime divisors; `d ∣ M`, `d ∤ M/p` give `p^{v_p(M)} ∣ d` | `exists_pow_support_lt`, `prod_dvd_of_pairwise_coprime`, `ordProj_dvd_of_not_dvd_div` |
| On `t ≥ x²` points (`x ≥ 1`), some `τ` has `lcm(1, …, x) ∣ ord τ` (cycle type `p^{⌊log_p x⌋}`, sum `≤ x²`, parts `≥ 2`); `π(x) ≤ x` | `lcmCycles`, `card_primesLE_le`, `sum_lcmCycles_le`, `two_le_of_mem_lcmCycles`, `exists_perm_lcmUpto_dvd` |
| **Lifting** (`G` `t`-transitive, `t ≤ \|Λ\|`): for `τ ∈ Sym(t)` some `g ∈ G` has `ord τ ∣ ord g` | `exists_mem_orderOf_dvd` |
| **The transitivity bound**: `TransitivityBound Tq`; `7 a + 15 ≤ 2^(a + 8)` | `Tq`, `transitivityBound_quad`, `seven_mul_add_le` |
| `if` with a decided condition | `ite_eq_of_pos`, `ite_eq_of_neg` |

The checks (`GraphIsoChecks/WielandtBound.lean`): the commutator of `(0 1 2)` and `(2 3 4)`
(one common point) is a `3`-cycle; Babai–Seress on `(0 1)(2 3 4)(5 6 7 8 9)` (order `30`,
`10^10 < 30^7`, `σ^15 = (0 1)`); a negative control (rotations of `Fin 4`:
`¬TransitivityBound (fun _ => 0)`); `Tq 1 = 256`, `Tq 1024 = 30976` (kernel `decide`).

## Milestone 15, stage 15d — Lemma 12 and the discharge (`PLAN-15.md` §6)

In `GraphIso/Pyber/` (`Primes.lean` with mathlib imports only; `Lemma12.lean`, `Discharge.lean`).
No existing statement changes. `λ = Nat.log 2`, `π(N) = #(Nat.primesLE N)`,
`Kpy n = 192 (λ(n) + 1)⁵`.

| Statement | Name |
|---|---|
| `lcm(1, …, N) ≤ N^{π(N)}`; Chebyshev: `2^N ≤ (N + 1) N^{π(N)}` | `lcmUpto_le_pow`, `two_pow_le_mul_pow_card` |
| **Many primes** (`L ≥ 1`): `2 L² + 1 ≤ π(64 L³)` | `card_primesLE_ge` |
| `L ≥ 1`, `R ≤ 2 L²`: a set of `R` primes `≠ 2`, each `≤ 64 L³` | `exists_odd_primes` |
| **The permutation**: a finite set `s` of odd primes with `∑ s ≤ \|Λ\|` gives `σ ∈ alternatingGroup Λ` with `p ∣ orderOf σ` for `p ∈ s` | `exists_mem_alternatingGroup` |
| `Kpy` monotone; `R · 64 (ℓ + 1)³ ≤ 192 (ℓ + 1)⁵` for `R = 2 ℓ² + ℓ + 2` | `Kpy`, `Kpy_mono`, `lemma12_arith` |
| **Pyber's Lemma 12** (`G Ω Λ : Type`, `G` finite, faithful and primitive on finite `Ω`, `φ : G →* alternatingGroup Λ` onto, `Kpy \|Ω\| ≤ \|Λ\|`): `φ` injective | `injective_of_surjective_alt` |
| **The CFSG-free Lemma 4.1**: `AltQuotientIso Kpy` | `altQuotientIso_pyber` |
| `Kpy n ≤ 192 (lam n + 1)⁵`; `TransitivityBound T` and `T m ≤ C' (λ(m) + 1)` give `QPHyp Kpy T 192 C'` | `Kpy_le_lam`, `qpHyp_pyber` |
| **The headlines under Wielandt's bound alone**: `mainSolve_qp_exp`, `giSolve_qp_exp`, `gi_qp_simpleGraph` at `C = 192` with `QPHyp` replaced by `TransitivityBound T` and `T m ≤ C' (λ(m) + 1)` | `mainSolve_qp_exp_pyber`, `giSolve_qp_exp_pyber`, `gi_qp_simpleGraph_pyber` |

The checks (`GraphIsoChecks/PyberLemma12.lean`): `π(64) = 18` and `card_primesLE_ge` at `L = 1`;
the permutation for `{3, 5, 7}` in `Alt(15)`; a negative control for the threshold (`Sym(3)` onto
the trivial `Alt(2)`, `subsingleton_alt2`, surjective and not injective, `2 < Kpy 3`); the numbers
`Kpy 1 = 192`, `Kpy 3 = 6144` and the arithmetic of Lemma 12 for `ℓ < 32` (kernel `decide`).

## Milestone 15, stage 15c — Theorem 7 (`PLAN-15.md` §5)

In `GraphIso/Pyber/` (mathlib imports only). No existing statement changes. Notation as in stage
15b; `G_{xy} = stabilizer G x ⊓ stabilizer G y`, `T(a) = suborbitKer G x y a`, `P` the range of
`toPermHom (stabilizer G x) Δ(x)` and `P_y` the stabilizer of `⟨y, _⟩` in `P`.

| Statement | Name |
|---|---|
| `T(a)` fixes `a` and every `b` with `(a, b) ∈ orbit G (x, y)`; it lies in and is normal in `G_a ⊓ G_b`; `T(g • a) = g T(a) g⁻¹`; `G_{g a} ⊓ G_{g b} = g (G_a ⊓ G_b) g⁻¹` | `suborbitKer`, `mem_suborbitKer`, `suborbitKer_le`, `suborbitKer_normal`, `suborbitKer_normal_self`, `suborbitKer_smul`, `stabilizer_inf_smul` |
| A chain does not change the residual: `SChain S A L → resid S A = resid S L` | `resid_eq_of_schain` |
| **Wielandt's Lemma 4** (finite `G`, faithful, primitive, `x ≠ y`, `(y, x) ∈ orbit G (x, y)`): `compA T(x) ⊆ compA (G_{xy} ⧸ T(x))` | `compA_suborbitKer_subset` |
| **Pyber's `(∗)`** (same hypotheses): `compA G_x ⊆ compA P ∪ compA P_y`; the kernel of `G_x → P` is `T(x)` | `compA_stabilizer_subset`, `ker_toPermHom_suborbit` |
| Faithful, primitive: normal `N ≠ ⊥` is transitive. Faithful, `N` commutative transitive: regular, `\|N\| = \|Ω\|` (finite `G`). `N` transitive generated by `l`: `G_x` acts faithfully on the conjugates of `l` | `isPretransitive_of_normal`, `stabilizer_eq_bot_of_comm`, `card_eq_of_comm`, `conj_injective` |
| **Abelian minimal normal** (finite `G`, `Ω`, faithful, primitive, `N` normal commutative `≠ ⊥`): `\|G\| ≤ \|Ω\|^(λ(\|Ω\|) + 1)` | `card_le_of_comm` |
| **Nonabelian minimal normal** (finite `G`, faithful, primitive, `N` minimal normal noncommutative): `compA G ⊆ compA G_x` | `compA_subset_of_noncomm` |
| **The dichotomy of Lemma 10** (finite nontrivial `G`, finite `Ω`, faithful, primitive): `\|G\| ≤ \|Ω\|^(λ(\|Ω\|) + 1)` or `compA G ⊆ compA G_x` | `card_le_or_compA_subset` |
| `compA L ⊆ compA A ∪ compA L'`, `L'` the image of `L` in `A ⧸ L.normalCore` (finite `A`); `compA (K ⊓ H)` inside `H` and inside `K` agree | `compA_subset_union_core`, `compA_subgroupOf_comm` |
| **Lemma 8** (any `F`; `\|compA\| ≤ F m` for core-free subgroups of index `m < n` of finite groups in `Type`; `H` core-free of index `n`, neither `⊤` nor maximal): `\|compA H\| ≤ F t + F b + λ(b)` for some `t, b ≥ 2`, `t b = n` | `exists_ncard_compA_le` |
| **Theorem 7** (`G : Type` finite, `H` core-free): `\|compA H\| ≤ 2 λ([G : H])² + 1` | `ncard_compA_le_of_coreFree` (`ncard_compA_le_of_coreFree_aux`) |
| Theorem 7 for a faithful transitive action (`G Ω : Type`, `G` finite): `\|compA G_x\| ≤ 2 λ(\|Ω\|)² + 1`; for `Ω` nonempty, `\|compA G\| ≤ 2 λ(\|Ω\|)² + λ(\|Ω\|) + 1` | `ncard_compA_stabilizer_le`, `ncard_compA_le_of_transitive` |
| `\|Δ(x)\| < \|Ω\|` for `x ≠ y`, `Ω` finite | `ncard_suborbit_lt` |
| Arithmetic, `F(L) = 2 L² + 1`: `T(L) = L (L + 1) / 2 ≤ F(L)`; `F` monotone; `F(a) + F(c) + c ≤ F(L)` for `1 ≤ a, c` and `a + c ≤ L`; `F(a) + F(c) + c + s ≤ F(L)` for `1 ≤ a, c` and `a + c ≤ s ≤ L`; `λ(m^k) + 1 ≤ k (λ(m) + 1)` for `k ≥ 1`; `λ(d^(λ(d)+1)) ≤ F(L)` for `λ(d) ≤ L` | `tri_le_F`, `F_mono`, `F_add_le`, `F_add_add_le`, `log_pow_lt`, `log_pow_le_F` |

The checks (`GraphIsoChecks/PyberThm7.lean`): Wielandt's lemma and its corollary on `Sym(3)` at
the self-paired orbital of `(0, 1)`; Theorem 7 on `Sym(4)` (`faithful_perm4`):
`|compA G_0| ≤ 9`, `|compA G| ≤ 11`; a negative control for core-freeness (`⊤` in `Sym(3)`:
`|compA ⊤| = 2 > 1`); the dichotomy on `Alt(3)` (`isPreprimitive_alt3`, `nontrivial_alt3`;
first alternative) and on `Sym(8)` (`8! > 8^4`, so `compA Sym(8) ⊆ compA G_0`); the three
inequalities of the induction for small values (kernel `decide`).

## Milestone 15, stage 15b — permutation groups and the odd-order bound (`PLAN-15.md` §4)

In `GraphIso/Pyber/` (mathlib imports only). No existing statement changes. `H` is core-free when
`H.normalCore = ⊥`; `Faithful G Ω` says that only `1` fixes every point. The orbital of `(x, y)`
is `orbit G (x, y)` (diagonal action on `Ω × Ω`), and `Δ(x) = orbit (stabilizer G x) y`.
`ω(m) = |m.primeFactors|`, `λ = Nat.log 2`, `T(L) = L (L + 1) / 2`.

| Statement | Name |
|---|---|
| A point stabilizer of a faithful transitive action is core-free; subgroups of `Perm Ω` act faithfully; images of transitive actions in `Perm Ω` act transitively; membership in the normal core | `normalCore_stabilizer_eq_bot`, `Faithful`, `faithful_perm`, `isPretransitive_range`, `mem_normalCore_iff` |
| `H` core-free: `G` acts faithfully on `G ⧸ H`; `G ⧸ H` nontrivial for `H ≠ ⊤`; primitive for `H` maximal | `faithful_quotient`, `nontrivial_quotient`, `isPreprimitive_quotient` |
| **The quotient by the core**: the image of any `L` in `G ⧸ L.normalCore` is core-free of index `[G : L]` | `normalCore_map_mk`, `index_map_mk` |
| **Normal subgroups** (finite `G`, `H` core-free, `K` normal, `J = (H.subgroupOf K).normalCore`): `primeFactors \|K\| ⊆ primeFactors \|K ⧸ J\|`; `compA K ⊆ compA (K ⧸ J)` | `primeFactors_card_subset`, `compA_subset_compA_quot` |
| **Covering subgroups**: `H` core-free, `H ⋖ M`, `K ≤ M` normal, `K ≠ ⊥` ⟹ `K ⊔ H = M`; then `[K : H ∩ K] = [M : H]` (finite `G`); finite `G`, `H` neither `⊤` nor maximal ⟹ some `M ≠ ⊤` covers `H` | `sup_eq_of_covBy`, `relIndex_eq_of_sup_eq`, `exists_covBy_ne_top` |
| Orbitals: invariance; `b ∈ Δ(x) ↔ (x, b) ∈ orbit G (x, y)`; no diagonal pairs for `x ≠ y`; `\|Δ(x)\| = [G_x : G_y ⊓ G_x]`; equal-index subgroups have symmetric relative indices | `smul_mem_orbit_pair`, `mem_orbit_stabilizer_iff`, `diag_notMem_orbit`, `ncard_orbit_stabilizer`, `relIndex_comm_of_index_eq` |
| **Paired suborbits** (finite `G`, `Ω`, transitive): `\|{b \| (b, x) ∈ orbit G (x, y)}\| = \|Δ(x)\|` | `ncard_paired_eq` |
| **Odd order** (finite `G`, `\|G\|` odd, `x ≠ y`): `(y, x) ∉ orbit G (x, y)`; for a transitive action on finite `Ω`, `2 \|Δ(x)\| + 1 ≤ \|Ω\|` | `swap_notMem_orbit`, `two_mul_ncard_suborbit_add_one_le` |
| Involutions: `g * g = 1` ⟹ `(g • x, x) ∈ orbit G (x, g • x)` | `swap_mem_orbit_of_mul_self` |
| **Connectivity** (finite `G`, primitive, `x ≠ y`): a set containing `x` and closed along the orbital is everything | `eq_univ_of_closed` |
| **Jordan's Lemma 1** (finite `G`, faithful, primitive, `x ≠ y`): every prime dividing `\|G_x\|` divides `\|range (toPermHom G_x Δ(x))\|` | `prime_dvd_card_range` |
| **The odd-order bound** (Pyber's Lemma 2): `G : Type` finite, `\|G\|` odd, `H` core-free ⟹ `ω(\|G\|) ≤ T(λ([G : H]))`; for a faithful transitive action (`G Ω : Type`), `ω(\|G\|) ≤ T(λ(\|Ω\|))` | `card_primeFactors_le_of_odd` (`card_primeFactors_le_of_odd_aux`), `card_primeFactors_le_of_odd_action` |
| Arithmetic: `T(a) + T(c) ≤ T(a + c)`; `T` monotone; `L + T(a) ≤ T(L)` for `a < L`; `λ(t) + λ(b) ≤ λ(t b)`; `λ(d) + 1 ≤ λ(n)` for `1 ≤ d`, `2 d < n`; `ω(a b) ≤ ω(a) + ω(b)` | `tri_add_le`, `two_mul_tri`, `tri_mono`, `add_tri_le`, `log_add_log_le`, `log_add_one_le`, `card_primeFactors_mul_le` |

The checks (`GraphIsoChecks/PyberPerm.lean`): `Sym(3)` on `Fin 3` has the self-paired orbital of
`(0, 1)` (`selfPaired_perm3`) and `Δ(0) = {1, 2}` (`suborbit_perm3`, `ncard_suborbit_perm3`), so
`2 |Δ(0)| + 1 = 5 > 3` (a negative control for odd order); Jordan's lemma there with
`|G_0| = 2` (`card_stabilizer_perm3`); `Alt(3)` (`odd_alt3`, `isPretransitive_alt3`) has no
self-paired orbital at `(0, 1)`, `2 |Δ(0)| + 1 ≤ 3`, and `ω(3) ≤ 1`; a negative control for
connectivity: the rotations of `Fin 4` (`isPretransitive_rot4`, `rot_add_two`) leave `{0, 2}`
closed along the orbital of `(0, 2)`; the two inequalities of the induction for small values
(kernel `decide`).

## Milestone 15, stage 15a — the group theory of `compA` (`PLAN-15.md` §3)

Group theory only, in `GraphIso/Pyber/` (mathlib imports only), toward Pyber's CFSG-free
Lemma 4.1. No existing statement changes. `compA G` is the set of primes `p` with subgroups
`B ≤ A`, `A` subnormal, `B` normal in `A` and `[A : B] = p`. These are the orders of the abelian
composition factors, by Schreier refinement and Jordan–Hölder, which are not formalized and not
used. "Finite" below means a `Finite` instance on the group, and on the index type for families.

| Statement | Name |
|---|---|
| The definition | `compA` |
| Finite `G`: `compA G ⊆ primeFactors \|G\|`; `\|compA G\| ≤ ω(\|G\|) ≤ ⌊log₂ \|G\|⌋`; `\|primeFactors m\| ≤ ⌊log₂ m⌋` for all `m` | `compA_subset_primeFactors`, `compA_finite`, `ncard_compA_le_card_primeFactors`, `ncard_compA_le`, `card_primeFactors_le_log` |
| Surjective images: `compA G' ⊆ compA G`; isomorphism invariance; ranges | `compA_subset_of_surjective`, `compA_eq_of_mulEquiv`, `compA_range_subset` |
| Injective homomorphisms with subnormal range, and subnormal subgroups: `compA G ⊆ compA G'`, `compA H ⊆ compA G` | `compA_subset_of_injective`, `compA_subset_of_isSubnormal`, `isSubnormal_map_of_range`, `normal_comap_pair`, `normal_map_pair` |
| A normal subgroup of prime index `p` gives `p ∈ compA G`; finite commutative `G`: every prime divisor of `\|G\|`; finite nonabelian simple `G`: `compA G = ∅`; trivial groups: `∅` | `mem_compA_of_index`, `mem_compA_of_comm`, `compA_eq_empty_of_isSimpleGroup`, `compA_eq_empty_of_subsingleton`, `compA_eq_empty_of_top_eq_bot` |
| **Extensions** (finite `G`, `N` normal): `compA G ⊆ compA N ∪ compA (G ⧸ N)`, from `[A : B] = [A ⊓ N : B ⊓ N] · [A ⊔ N : B ⊔ N]`; through a homomorphism with subnormal range: `compA G ⊆ compA (ker f) ∪ compA G'` | `compA_subset_union` (from `relIndex_eq_mul_relIndex`, `relIndex_subgroupOf_eq`), `compA_subset_union_of_hom`, `compA_quot_subset_of_hom` |
| **Pyber's Proposition 3** (finite `G`, any `H`): `compA G ∖ compA H ⊆ primeFactors [G : H]`; for `A` subnormal, `[A : A ⊓ H] ∣ [G : H]` | `compA_sdiff_subset`, `relIndex_dvd_index_of_isSubnormal`, `relIndex_dvd_index_of_normal_right` |
| **Pyber's Proposition 6** (finite `G`, finite family of normal `N i`, `⨅ N i = ⊥`): `compA G ⊆ ⋃ compA (G ⧸ N i)`; homomorphisms with subnormal ranges and `⨅ ker = ⊥` | `compA_subset_iUnion_of_iInf`, `compA_subset_biUnion_of_ker` |
| **Joins** (finite `G`, finite family of normal `N i`, `⨆ N i = ⊤`): `compA G ⊆ ⋃ compA (N i)` | `compA_subset_iUnion_of_iSup`, `compA_biSup_subset`, `compA_sup_subset` |
| **Characteristically simple groups**: finite, nontrivial, noncommutative, `CharSimple N` ⟹ `compA N = ∅`; minimal normal subgroups exist and are characteristically simple; images under all automorphisms generate; finite joins of normal solvable subgroups are solvable | `compA_eq_empty_of_charSimple` (`compA_eq_empty_of_charSimple_aux`), `CharSimple`, `IsMinNormal`, `exists_isMinNormal`, `IsMinNormal.charSimple`, `iSup_map_mulAut_eq_top`, `isSolvable_biSup`, `isSolvable_sup`, `isSolvable_of_mulEquiv`, `comm_of_commutator_eq_bot`, `comm_of_mem`, `finite_mulAut` |
| **Residuals** (finite `G`): chains `SChain S A L` with sections `compA ⊆ S`; subnormal ends, composition, intersection; `resid S A` reached; equivariant under isomorphisms; normalized by the normalizer of `A`; unchanged by one step; **`SChain S A L → compA A ⊆ S ∪ compA L`**, so `resid S A = ⊥ → compA A ⊆ S` | `SChain`, `SChain.le`, `SChain.trans`, `SChain.isSubnormal`, `SChain.inf_left`, `SChain.inf`, `SChain.map`, `normal_inf_pair`, `compA_inf_section_subset`, `resid`, `resid_le_of_schain`, `schain_resid`, `resid_map`, `mem_normalizer_resid`, `resid_eq_of_step`, `compA_subset_of_schain`, `compA_subset_of_resid_eq_bot` |
| Finite groups are generated by at most `⌊log₂ \|G\|⌋` elements | `exists_list_closure_eq_top`, `exists_list_closure_sup_eq_top` |

The checks (`GraphIsoChecks/Pyber.lean`): `compA (Perm (Fin 3)) = {2, 3}` (`compA_perm3`); the
cyclic group of order `12` has `compA = {2, 3}`; a negative control,
`compA (alternatingGroup (Fin 5)) = ∅` with `primeFactors 60 = {2, 3, 5}` (`compA_alt5`, also
through the characteristically simple theorem); Proposition 3 on `Alt(3) ≤ Sym(3)`;
`resid {2, 3} ⊤ = ⊥` and `resid {2} ⊤ ≠ ⊥` in `Sym(3)`; `Sym(3)` generated by `2` elements;
`|primeFactors m| ≤ ⌊log₂ m⌋` for `m < 65` (kernel `decide`).

## Milestone 14, stage 14j-6c-3 — the graph-isomorphism entry (`PLAN-14.md` §14.15)

No protected statement changes, and the procedure is unchanged; three new targets. Two graphs on
`n` vertices become strings on `N = n + n · n` points (the vertices, then the ordered pairs
`(u, v)` at `n + v + n u`) under the lift of `Sym(V)`. The procedure runs on that instance, and
the answer is restricted to the first `n` points. Correctness holds for every threshold program
with `ThrSpec`; the cost bound `2^{c (λ(n) + 1)⁸}` assumes `QPHyp K T C C'`. The constant `c`
depends only on `C` and `C'`, and is not explicit. **Historical:** milestones 15 and 16 were to
discharge `QPHyp`; it is not shown satisfiable (milestone 16's `Tq` is quadratic, and `QPHyp`
fails for it: `not_qpHyp_Tq`). The unconditional versions go through `QPHypJ`
(`giSolve_final`, `gi_simpleGraph_final`).

| Statement | Name |
|---|---|
| **Correctness on every valid input**: for every threshold program with `ThrSpec` and valid graph data `X`, `Y` on `n` points of any degree, the closed entry (Schreier–Sims substituted, no oracle) returns `r` with `GICosetOK n X Y r`, within `giCostSS cT n` | `giSolve_ss` |
| **Graph isomorphism in time `2^{O((log n)⁸)}`**: for all `C`, `C'` there is `c` such that for all `K`, `T` with `QPHyp K T C C'`, on valid graph data on `n` points the closed entry at `thrQP C C'` returns a `GICosetOK` result with local cost at most `2^{c (λ(n) + 1)⁸}` | `giSolve_qp_exp` (from `mainSolve_qp_exp_gens`, `giEntry_runs`, `gi_close`, `gi_cost_le`) |
| **The same for simple graphs** `G`, `H` on `Fin n` given by their adjacency lists: `r = none ↔ IsEmpty (G ≃g H)`, and otherwise valid data `τ`, `hs` with `τ • ⟨hs⟩` equal to the set of the permutations underlying the isomorphisms `G ≃g H` | `gi_qp_simpleGraph` (from `isIso_ofSimpleGraph_iff`) |
| A correct answer of the graph problem: `none` exactly when no isomorphism exists; otherwise valid data of a coset with at most `(2N)²` generators equal to `{φ \| IsIso n X Y φ}` | `GICosetOK` |
| The points and the lift: `ptEquiv`, `liftPerm n : Perm (Fin n) →* Perm (Fin N)` (`φ` on the vertices, `(u, v) ↦ (φ u, φ v)`), injective; its values in numbers | `gN`, `ptEquiv`, `liftPerm`, `liftPerm_apply`, `liftPerm_inl`, `liftPerm_inr`, `liftPerm_injective`, `liftFun`, `val_liftPerm`, `pt_cases`, `div_mod_pair`, `liftFun_pair` |
| Lifted data is the data of the lift | `liftRow`, `liftWrites`, `liftArr`, `liftData`, `get_liftArr`, `liftData_eq`, `valid_liftData`, `denote_liftData`, `offArr`, `get_offArr` |
| The strings: `0` at the vertices, `1` at `(u, v)` exactly when `Adj X u v` | `strWrites`, `gStr`, `mem_strWrites`, `get_gStr`, `gStr_inl`, `gStr_inr` |
| The generators: the lifts of `finRotate n` and of the transposition of `0` and `1` (none for `n ≤ 1`), valid, generating the image of the lift (mathlib's `closure_cycle_adjacent_swap`) | `rotF`, `rotI`, `swF`, `rot_eq`, `sw_eq`, `gensData`, `gensData_valid`, `gensData_denote` |
| **The reduction**: on the whole window, in the image of the lift with the identity as representative, the solutions are the lifts of the isomorphisms | `iso_graph` |
| **Decoding**: restriction to the first `n` points inverts the lift; a correct answer of the encoded instance decodes to a `GICosetOK` result | `restrictArr`, `restrictData`, `restrict_lift`, `decodeAns`, `coset_pullback`, `decode_ok` |
| The programs, with exact results and polynomial costs (on valid data): offsets, lifted arrays and data, strings, generators, restriction, decoding; the entry, well formed | `offProg`, `liftArrProg`, `liftDataProg`, `strProg`, `gensProg`, `restrictProg`, `decodeProg`, `giEntry`, `giEntry_wf`; `RunsWithin.offProg`, `RunsWithin.liftArrProg`, `RunsWithin.liftDataProg`, `RunsWithin.strProg`, `RunsWithin.gensProg`, `RunsWithin.restrictProg`, `RunsWithin.decodeProg`; `offCost`, `liftArrCost`, `liftDataCost`, `strCost`, `vtxCost`, `gensCost`, `encCost`, `decCost` |
| **The entry from a run of the main entry** on the encoded instance (`giInst`) with at most `(2N)²` generators: within `encCost n + c + decCost n (2N · 2N)` | `giEntry_runs`, `giInst_valid` |
| The main entry with the generator count kept (the proofs of `mainSolve_ss`, `mainSolve_qp`, `mainSolve_qp_exp`) | `mainSolve_ss_gens`, `mainSolve_qp_gens`, `mainSolve_qp_exp_gens` (from `entryI`, `entry_hinst`, `entry_ok`, `mainEntry_of_body`) |
| The closed solver | `mainSolver`, `qpSolver`, `gi_close` |
| The closed form: `λ(N) + 1 ≤ 2 (λ(n) + 1)`; the encoding, `generate` and the decoding at most `1000 (n + 1)¹²`; the total at most `2^{(256 c₁ + 23) (λ(n) + 1)⁸}` | `lam_gN_le`, `gi_poly_le`, `gi_cost_le` |

The checks (`GraphIsoChecks/GraphQP.lean`, kernel `decide`):
- the string of the path `P₃` on `12` points; the generators' validity; the lifted `3`-cycle at
  a pair and at a vertex; the window; decoding of the lifted `3`-cycle;
- the entry run with the verified Schreier–Sims oracle and `mainBody (thrQP 1 3)`, against the
  brute-force set of isomorphisms (the decoded coset enumerated): `K₂` with itself and with the
  empty graph, the empty graph with itself; `P₃` with another `P₃`, with the triangle; the
  triangle with itself (`gi_k2k2`, `gi_k2e2`, `gi_e2e2`, `gi_p3p3`, `gi_p3k3`, `gi_k3k3`);
- a negative control: with only the lifted transposition of `0` and `1` as generator, the answer
  for two isomorphic `P₃`s centred at `1` and `2` is `none` (`gi_swap`).

The runs (`3 000` to `87 000` trace events) are proved in pieces of at most `5 000` events by
`execRuns`, each piece and the composition checked by the kernel.

## Milestone 14, stage 14j-6c-2 — the closed bound (`PLAN-14.md` §14.14)

No protected statement changes, and the procedure is unchanged; two new targets. Stage
14j-6c-1's `Q(n₀) = QQP C C' n₀` is at most `2^{c (λ(n₀) + 1)⁶}`, so the headline's cost is
`genCost N |gs| + 2^{c (λ(N) + 1)⁸}`. Both constants depend only on `C` and `C'`, and are not
explicit. `QPHyp` is a hypothesis here and is not shown satisfiable; the unconditional version
goes through `QPHypJ` (`mainSolve_qp_expJ`, `mainSolve_final`).

| Statement | Name |
|---|---|
| **The closed bound**: for all `C`, `C'` there is `c` with `QQP C C' n₀ ≤ 2^{c (λ(n₀) + 1)⁶}` for every `n₀` | `QQP_le_exp` (from `Growth.Main.QQP_qpb`) |
| **The headline in closed form**: for all `C`, `C'` there is `c` such that for all `K`, `T` with `QPHyp K T C C'`, every valid plain instance of degree `N` gets a correct answer (`AnsOK`) within `genCost N \|gs\| + 2^{c (λ(N) + 1)⁸}` | `mainSolve_qp_exp` (from `mainSolve_qp_closed`, `qp_closed_le`, `qp_exponent_le`) |
| The growth classes over an index `ι` with a size `L`: `PLB L e v` (`v ≤ c (L + 1)^e`) and `QPB L d v` (`v ≤ 2^{c (L + 1)^d}`) | `PLB`, `QPB` |
| Their closure: constants, `+`, `·`, `max`, `min`, `-`, `/`, constant powers, `log`/`clog`, raising degrees, `PLB ⊆ QPB 1`, re-indexing | `QPB.const`, `QPB.add`, `QPB.mul`, `QPB.max`, `QPB.min_left`, `QPB.sub`, `QPB.div`, `QPB.pow_const`, `QPB.clog`, `QPB.log`, `QPB.lift`, `QPB.mono`, `QPB.comp`, and the same for `PLB` with `PLB.const_mul`, `PLB.mul_const`, `PLB.clog`, `PLB.log`, `PLB.qpb`, `PLB.qpb'` |
| **The growth steps**, for `x ∈ QPB L 1`, `y ∈ PLB L e`: `x^y`, `y!`, `x.choose y` in `QPB L (e + 1)`; `2^y` in `QPB L e`; `supTo` and sums over `List.range`, with the bound variable in `PLB` | `QPB.pow`, `QPB.factorial`, `QPB.choose`, `QPB.two_pow`, `QPB.supTo`, `QPB.sum_range` (with `sum_range_le`), `PLB.bvar_le`, `PLB.bvar_lt` |
| **A growth lemma for each of the 261 definitions `Q` reads** (generated; the polynomial ones at every degree, the others with each argument's class: `PLB L 5`, `QPB L 1` or `QPB L 6`; M3's with `N − n ∈ PLB L 5`) | `Growth.<namespace>.<name>_qpb` (`GraphIso.Main.GrowthCosts`) |
| The small parameters with explicit constants, `X = λ(n₀) + 1`: `qpL ≤ 2X`, `kQP C ≤ (32C + 7) X⁵`, `ℓQP C C' ≤ (4 (32C + 7) + 2056 + ℓT C') X⁵`, `jMaxQ C' ≤ 2C' X`, `uMaxQ = 2X²`; `n₀ ∈ QPB λ 1` | `qpL_le`, `kQP_le`, `ℓQP_le`, `jMaxQ_le`, `lt_two_pow_lam`, `id_qpb`, `lam_plb`, `qpL_plb`, `kQP_plb`, `ℓQP_plb`, `mLQ_plb`, `uMaxQ_plb`, `jMaxQ_plb`, `m3_sub_plb` |
| `Q`'s parts in `QPB λ 6` | `Growth.Main.qpTest_qpb`, `qpM4_qpb`, `qpM5_qpb`, `qpCases_qpb`, `qpWork_qpb`, `qpFac_qpb`, `QQP_qpb` |

The checks (`GraphIsoChecks/QPBound.lean`):
- by kernel `decide`: the small parameters' constants at `C = 1`, `C' = 3` and
  `n₀ = 0, 30, 1000, 2¹⁶`; `QQP 1 3 4 ≤ 2^{36 (λ(4) + 1)⁶}` and
  `QQP 1 3 16 ≤ 2^{7 (λ(16) + 1)⁶}` (values, not the proof's constant);
- negative controls, as proofs: `2^n`, `(m + 1)^m` (`c2bRU`'s growth) and `n^n` are not in
  `QPB λ 6` (`not_qpb_two_pow`, `not_qpb_pow_self`, `not_qpb_self_pow`).

## Milestone 14, stage 14j-6c-1 — the potential (`PLAN-14.md` §14.13)

No protected statement changes, and the procedure is unchanged; two new targets. Under the
interfaces' growth assumptions (`QPHyp K T C C'`, not shown satisfiable; see `QPHypJ`), the
full procedure at the thresholds `thrQP C C'` costs at most `potO Q 2 |W| bo + Q`, with an
explicit `Q = QQP C C' n₀`.

| Statement | Name |
|---|---|
| **The potential bound** on the domain `MiniDom n₀ n₀ (2n₀)` with `LabInv`: a correct answer with at most `(2n₀)²` generators within `potO (QQP C C' n₀) 2 \|W\| bo + QQP C C' n₀` | `main_pot` (from `pot_ind_step`, `PotIH`, `pot_sub_of_ih`) |
| **The headline**: every valid plain instance of degree `N` within `genCost N \|gs\| + 2 + 15 + potO (QQP C C' N) 2 \|W\| none + QQP C C' N`; in closed form in `Q`, at most `genCost N \|gs\| + 17 + (2N + 2) N² Q^{2 (5 λ(N) + 9 + 4 (λ(N) + 6)²)} + Q` | `mainSolve_qp`; `mainSolve_qp_closed` |
| The interface hypotheses: `AltQuotientIso K`, `Monotone K`, `K n ≤ C (λ(n) + 1)⁵`, `TransitivityBound T`, `T m ≤ C' (λ(m) + 1)` | `QPHyp` |
| The thresholds `k = C L⁵ + L + 5` and `ℓ = 4k + L³ + 2¹¹ + 64 (C' + 1)²`, `L = ⌈log₂ (n₀ + 2)⌉ ≥ λ(n₀) + 1` | `qpL`, `kQP`, `ℓT`, `ℓQP`, `lam_add_one_le_qpL`, `qpL_le`, `kQP_eq`, `five_le_kQP`, `four_mul_kQP_le`, `ℓT_le_ℓQP`, `ell0_le_ℓQP` |
| The threshold program: local, within `cTQP C n₀` | `thrQP`, `cTQP`, `thrQP_spec` |
| **The sharp dispatcher's numeric hypotheses at the thresholds** (`Thresholds`: `K n₀ ≤ k`, `n₀ < k!/2`; `TBelow` above `64 (C' + 1)²`) | `sharpHyp_qp` (from `thresholds_qp`, `two_pow_le_factorial`, `tBelow_qp`, `sq_succ_le_four_pow`, `TBelow.mono`) |
| What the step sees: M4's depth at most `supTo T m`; the depth bounds at most `C' (λ(2n₀) + 1)`; the union cells above `ell0 n₀` at most `2 (λ(n₀) + 1)²` | `ss_m4J_le_T`, `supTo_le_jMaxQ`, `labLen_mul_lam_le` |
| **`Q`**: `n₀ + 2`, the tests' cost and every case's work at the corners, and every case's factor plus counted calls at the corners | `QQP`, `qpWork`, `qpTest`, `qpCases`, `qpM4`, `qpM5`, `qpFac`, `sGQ`, `uMaxQ`, `jMaxQ`, `mLQ` |
| **The bounds by `Q`**: the step's work, the factor plus the counted calls, the window | `mainWorkS_le_QQP` (from `caseWorkS_le_qpCases`), `caseFAB_le_QQP`, `winSize_add_two_le_QQP` |
| Monotonicity of the tests' cost, the other cases' work, M5's restriction, `ssLgM4Ns`, `ssLgM5Ns`, `m5FBns`, `c3Count` (25 lemmas, as in `SharpWork`); `m5WorkUB` | `CostMono.*` (`GraphIso.Main.PotWork`), `m5WorkUB_mono` |
| **The potential with an offset** `R ≤ 2Q` per child: with branching (at most `Q³` children), without branching (nonempty windows), the chain rule | `pot_step_off`, `pot_free_off`, `pot_chain_off` (from `pot_step_mul`, `pow_le_pot`, `pot_free_child`, `two_mul_le_pow`, `sum_map_add_const`) |
| The cost of a step within the potential, by case | `pot_case_le` (from `pot_free_case`, `pot_step_case`, `pot_chain_case`, `ChildList.eq_nil_of_zero`, `sum_one_add`, `sum_counted`, `potO_none_mono`, `caseA_zero_win`, `caseB_zero_win`) |

The checks (`GraphIsoChecks/Pot.lean`, kernel `decide`, at `C = 1`, `C' = 3`):
- `thrQP 1 3` run by the evaluator at `n₀ = 0` and `n₀ = 30`: `(7, 3101)` at cost `66 ≤ 85` and
  `(3135, 15737)` at cost `2588 ≤ 2893`; the thresholds' values at `n₀ = 1000` and `2¹⁶`
  (`k = 1419879`, `ℓ = 5687501`);
- `4k ≤ ℓ`, `ell0 n₀ ≤ ℓ` at `n₀ = 1000` and `2¹⁶`; `TBelow wielandtT (ℓQP 1 3 n₀)` for every
  `n₀`, and its inequality at `m = 1025`;
- the three inequalities with the offset at explicit values; negative controls: a child with the
  parent's measure, `90000` children at `Q = 3`, and `T = id` without the growth bound;
- `2^25809 ≤ QQP 1 3 4 < 2^25810` and `2^95171 ≤ QQP 1 3 16 < 2^95172`.

## Milestone 14, stage 14j-6b-2 — the sharp dispatcher (`PLAN-14.md` §14.12)

No protected statement changes, and the procedure is unchanged; one new target. The full
procedure's step with M4 and M5 charged without stuck orbits, under numeric hypotheses on the
thresholds and the interfaces' functions (`SharpHyp`).

| Statement | Name |
|---|---|
| **One step without stuck orbits**: `main_step_lab`'s conclusion with `mainWorkS`, `caseFS`, and M3 only on bases of at most `ℓ` points | `main_step_sharp` |
| The numeric hypotheses | `TBelow`, `SharpHyp`, `Thresholds.of_le` |
| `TBelow` at Wielandt's bound (not vacuous), and not at the trivial bound | `wielandtT`, `supTo_wielandtT`, `twelve_le_pow`, `tBelow_wielandt`; `not_tBelow_id` |
| No M3 above `ℓ` | `mainCase_m3_le` (from `ss_m4J_sharp`, `bigCase_eq_m4`, `bigCase_eq_m5`, `mainCase_big`) |
| M4 and M5 in the procedure without stuck orbits | `main_m4_sharp`, `main_m5_sharp`, `m5FBns_mono_u` |
| The sharp case functions | `caseWorkS`, `caseFS`, `caseWorkS_of_ne`, `caseFS_of_ne`, `labT`, `mainWorkS`, `mainWorkS_eq`, `mainWorkS_of_ne` |
| **Corner bounds of the sharp work**: `caseWorkS` at M4 at most the maximum over `j' ≤ j` of M4's work at the corner (`m ≥ 1`); at M5 at most the restriction's work plus `m5WorkUB` (`1 ≤ k`, `2k ≤ m`, `jB < m`) | `caseWorkS_m4_le`, `caseWorkS_m5_le` (from `m4WorkNsLSS_le`, `m5WorkNsSS_le`) |
| The work functions at given sizes and their monotonicity | `m4PtNsL`, `m4PtNsL_mono`, `m5CertPt`, `m5CasePt`, `m5DispPt`, `m5WorkRawNs_eq`, `m5WorkUB`, `m5CertPt_mono`, `m5CasePt_mono`, `m5DispPt_mono` |
| Monotonicity of every cost function the two works call (227 lemmas, each by `unfold` and `gcongr`, `@[gcongr only]`) | `CostMono.*`, `psCostFrom_mono` |
| Tools | `envSup_le`, `pow_half_le_factorial` (`(m/2)^(m - m/2) ≤ m!`) |

The checks (`GraphIsoChecks/Sharp.lean`, kernel `decide`):
- `caseWorkS` at M4 and M5 below `m!` at `m = 65536` (`sharp_m4_work_lt`, `sharp_m5_work_lt`),
  with `n = p = 65536`, `N = g = 131072`, `s = (2N)²`, `k = 5`, `j = 51`, `t = 2` and
  `jB = supTo wielandtT 65536 = 51`, through the corner bounds and `pow_half_le_factorial`;
- M4's work at least `msCount (m - j)⁸` at any sizes (`msCount_pow_le_caseWorkS_m4`), hence
  above `3000!` at `m = 3000`: the comparison needs a large base;
- `caseFS` at M4 and M5 below `m!` at `m = 3000` (`k = 5`, `j = 3`, `t = 2`, `jB = 36`) and at
  `m = 65536`, with `caseF` at `m = 3000` as a negative control;
- `TBelow`'s inequality at Wielandt's bound at `m = 129` and `m = 3000`, and its failure at
  `m = 64`.

## Milestone 14, stage 14j-6b-1 — the steps without stuck orbits (`PLAN-14.md` §14.11)

No protected statement changes. The no-stuck forms of M4 and M5 at the Schreier–Sims backend,
with factors, `Lg` and work free of the base size's factorial.

| Statement | Name |
|---|---|
| **M4 without stuck orbits, the union cells bounded by the labels** | `RunsWithin.m4StepProg_nsL_ss` (from `RunsWithin.m4StepProg_ns_ssU`, which also gives `RunsWithin.m4StepProg_ns_ss`) |
| **M5 as a step without stuck orbits** (any backend) | `RunsWithin.m5StepCJProg_ns` |
| **M5 without stuck orbits with Schreier–Sims** | `RunsWithin.m5StepCJProg_ns_ss` (from `RunsWithin.m5StepCJProg_ns_ss₀`) |
| Case 2b's counts for `y` only in Case 2b | `RunsWithin.m5DispatchCJ_ns_jpC`, `RunsWithin.m5CoreCJProg_ns_jpC` (the `_ns_jp` forms their corollaries) |
| The size of the partitions, on the models | `PartLe`, `extPart_partLe`, `leafTree_partLe`, `cb_choice_facts`, `cb_choice_partLe`, `case2bTree_partLe`; `splitTree_uniprim`, `splitTree_partLe`, `outTree_dom`, `outTree_partLe`, `case3Tree_partLe` |
| The size of the partitions, on data | `firstLeafD_partLe` (Case 2b), `firstStructD_partLe` (Case 3) |
| Case 2b's degree under `TransitivityBound` | `degD_le_T`, `ss_m5_degD_le_T`, `ss_m5_depth_le` |
| The union cells bounded by the labels | `ss_union_le_lab`; `ssBdJU`, `ssBdJ_eq`, `rd_orbit_cj_ssUB`, `rd_orbit_cj_ssL`, `ss_m4_hDU`, `ssBdJU_mono_u` |
| The hypotheses without stuck orbits, discharged at `ssCtx` | `ss_m5_hBgen₂ᵦ_ns`, `ss_m5_hLY₂_ns`, `ss_m5_hpart₂ᵦ`, `ss_m5_c3_facts`, `ss_m5_hnt₃`, `ss_m5_hpart₃`, `ss_m5_hu₂_lab`, `ss_m5_hu₃_lab`, `ss_m5_hDJ₂_lab`, `ss_m5_hDJ₃_lab`, `m5Sel_four`, `m5Sel_three` |
| Case 2b's counts at a depth bound and the bounds | `c2bRj`, `c2bRU_eq_c2bRj`, `c2bR_le_j`, `c2bRj_mono`, `ssM5βns` |
| The work | `m4WhUSS`, `m4WhSS_eq`, `m4WorkNsLSS`, `m4WorkNsLSS_mono`; `m5DispNumNs`, `m5WnsCJ_le`, `m5WorkRawNs`, `m5WorkNsSS`, `m5WorkNsSS_mono`, `le_m5WorkNsSS`, `m5CoreWorkNsCJ_le` |
| The factor and the parameters | `m5FBns`, `ss_m5CFnsCJ_le`, `ssLgM5Ns`, `m5ns_params` |

The checks (`GraphIsoChecks/NoStuck.lean`): the partition bound on a fixture extended by
`extPart`, the union bound on 14j-6a's `cj12` fixture, and `m5FBns`, `ssLgM5Ns`, `ssLgM4Ns` below
`3000!` with `m5FB`, `ssLgM5`, `ssLgM4` as a negative control.

## Milestone 14, stage 14j-6a — the label invariant (`PLAN-14.md` §14.10)

A semantic contract amendment (`lean/docs/contract-repair.md`, "The label invariant of stage
14j-6a"): `SizeChild` gains `lab`, and `DOutcome`'s hinted constructors gain label facts.

| Statement | Name |
|---|---|
| **One step with the label invariant**, the form stage 14j-6c's induction uses | `main_step_lab` (with `main_step`, cases of `main_step_gen`) |
| The invariant | `ell0`, `LabInvAt`, `LabInv`, `LabInvAt.mono`, `LabInvAt.of_le_one`, `LabInvAt.johnson`, `le_choose_two`, `LabInv.of_none`, `LabInv.entry`, `LabInv.of_le` |
| The frame's field and its closure | `SizeChild.lab`, `SizeChild.lab_none`, `SizeChild.lab_closed` |
| Label lengths on data | `labLen`, `labLen_le_iff`, `length_le_labLen`, `length_getD_le_labLen`, `labLen_le_of_getD`, `labLen_mapLabels_le`, `labLen_mapLabels_short`, `length_interLab_le`, `length_filter_pos_blockCount_le`, `length_blockLab_le` |
| The children's labels | `labLen_labM0D`, `labLen_labM1D_le`, `m1O_facts`, `labLen_labM2aD_le`, `labLen_m2bLabels_le`, `labLen_labJUD_le`, `labLen_labDiffD_le`, `labLen_rbLabels_le`, `labLen_normLabD_le`, `childHInst_labInv` |
| The derived hints' label facts (`DOutcome.inter`, `blockLab`, `blockStab`, `johnUnion`) | `RunsWithin.deriveProg_free`, `RunsWithin.deriveProg_cj`, `dv_johnson_choose_le`, `dv_jdec_card`, `dv_cj_choose_le` |
| The block-stabilizer loop with its children's labels | `MlChildL`, `RunsWithin.m2bLoopProg_lab` (`RunsWithin.m2bLoopProg` its corollary) |
| The steps of the full procedure with the flag | `LabInvIf`, `MainSubB`, `MainSubL`, `MainSub.toB`, `MainSubL.toB`, `MainSubB.step`, `main_predB`, `LabInvIf.normLab` |

The checks (`GraphIsoChecks/MainSteps.lean`) test the label field on every recorded child
(`kidsSizeOK`, `labInvB`, `labInvAtB_iff`). Kernel checks cover M0's labels, a Johnson union
against `labLen L · s` on `cj12`, and a negative control (`not_labInvAt`).

## Milestone 14, stage 14j-5d — the dispatcher and the recursion (`PLAN-14.md` §14.9)

| Statement | Name |
|---|---|
| **The full procedure on every valid instance** | `mainSolve_ss` (every `thr` with `ThrSpec`), `mainSolve_ss_const` (no hypothesis), `mainSolve_ss_dom` (the work at the domain's parameters) |
| **Correctness and cost on the domain**, by induction on the rank | `main_spec` (from `main_ind_step`, `MainIH`), `main_spec_dom` |
| **One step**, the form stage 14j-6 reuses | `main_step` |
| The programs and their well-formedness | `ThrProg`, `ThrWf`, `thrConst`, `normLabProg`, `noStProg`, `m5OkProg`, `m4OkProg`, `bigProg`, `hintProg`, `mainBody`, `mainEntry`, `mainBody_wf` |
| The threshold contract | `ThrSpec`, `thrConst_spec`, `ThrSpec.calls` |
| Local programs: no backend or recursive call, so no backend event in any run | `Prog.Local`, `Prog.Local.eval_calls`, `Prog.Local.runs_calls`, `foldRun_calls`, `Prog.not_local_call`, `Prog.not_local_recur` |
| The tests' values | `normLabD`, `m5OkD_iff`, `m4OkD_iff`, `noStD_fst`, `orbits_trans_iff`, `base_trans_iff`, `HintValid.normLab`, `HInstValid.normLab` |
| The case taken | `MainCase`, `hintCase`, `bigCase`, `mainCase`, `casePred`, `mainCase_m5`, `mainCase_m4`, `mainCase_none`, `mainCase_some`, `mainCase_kj` |
| The branches at `ssCtx` | `RunsWithin.hintProg_m1`, `hintProg_blocks`, `hintProg_m2a`, `hintProg_m2b`, `hintProg_big`, `bigProg_small`, `bigProg_deg`, `bigProg_m5`, `bigProg_m5_m3`, `bigProg_m4`, `bigProg_m4_m3`; `main_top_hint` |
| The steps from the domain's sub-solver | `MainSub`, `MainSub.step`, `main_pred`, `main_chain`, `main_m0`, `main_m1`, `main_m2a`, `main_m2b`, `main_m3`, `main_m4`, `main_m5`, `ss_mb_facts` |
| M4 and M5 at any `Lg`, `uB` meeting the conditions; at the domain's bounds | `main_m4_at`, `main_m5_at`, `main_m4_dom`, `main_m5_dom` |
| The parameters at the domain's bounds and their conditions | `domLgM4`, `domLgM5`, `m4_dom_params`, `m5_dom_params`, `ssLgM4_le_dom`, `ssLgM5_le_dom`, `m4R_le_dom`, `pow_le_dom`, `msCount_mono`, `c2bRU_mono`, `c3R_le_dom` |
| M5's factor and counted calls | `m5FB`, `m5FBu`, `m5FBu_self`, `ss_m5CFCJ_le`, `ss_m5CFCJ_le_u`, `ss_m5CKCJ_le`, `m5CH_le` |
| The work of a step | `m0WorkSS`, `m3WorkSS`, `rbOverSS`, `caseWork`, `mainTestCost`, `mainWork`, `mainWork_eq`, `caseF`, `caseA`, `caseB` |
| The bounds on the domain | `workEnv`, `le_workEnv`, `mainW`, `mainA`, `mainCost`, `mainWork_le`, `main_count_le`, `caseWork_le_env`, `caseF_le_env`, `caseA_le_env`, `caseB_le_env` |
| The work at the domain's parameters | `caseWorkDom`, `caseWork_le_dom`, `mainWDom`, `mainW_le_dom`, `envSup_mono_box`, `workEnv_mono_box`, `miniC_mono_W` |
| The ranks and the cost of a step | `miniRk_none_lt`, `casePred_rk`, `dom_base_le`, `main_sub_of_ih`, `main_cost_le` |

The checks (`GraphIsoChecks/MainFull.lean`) run the full procedure at constant thresholds. They
compare the answer with brute force, the path (nodes per case), and every node's own work with
`mainWork` (M4: `m4CostSS` at the node's sizes). They are kernel-checked from the entry (the
base case, the chain rule, M0, M3) and on hinted fixtures (M1, M2a, M2b, M3), with a negative
control. M4 on `AGL(1, 5)` and M5's branch on `S₄` (a giant, M3) are checked by `#eval`. A
threshold program that calls the backend is not local and has no `ThrSpec` (`thrCall`).

## Milestone 14, stage 14j-5c — the Schreier–Sims steps (`PLAN-14.md` §14.8)

| Statement | Name |
|---|---|
| **M1, M2a, M2b with Schreier–Sims**, no backend hypothesis | `RunsWithin.m1StepProg_ss`, `RunsWithin.m2aStepProg_ss`, `RunsWithin.m2bStepProg_ss` |
| **M4 with Schreier–Sims**, general factor and no stuck orbit | `RunsWithin.m4StepProg_ss`, `RunsWithin.m4StepProg_ns_ss` |
| **M5 with Schreier–Sims** | `RunsWithin.m5StepCJProg_ss` (from `RunsWithin.m5StepCJProg_ss₀`) |
| The work, monotone | `m1WorkSS`, `m2aWorkSS`, `m2bWorkSS`, `m4WorkSS`, `m4WorkNsSS`, `m5WorkSS` and their `_mono` |
| The monotone envelope | `envSup`, `le_envSup`, `envSup_mono`, `supTo_le`, `supTo_mono` |
| M5's dispatch work by its data | `m5DispNum`, `m5WCJ_le`, `m5WorkRaw`, `m5CoreWorkCJ_le`, `le_m5WorkSS` |
| `RDOrbit` for every orbit, with explicit work | `rd_orbit_free_ssU`, `rd_orbit_cj_ssU`, `ssBdF`, `ssBdJ` |
| M1's orbit and child, the maximal blocks | `ss_m1O_facts`, `ss_m1_child`, `ss_mbD_facts`, `HintValid.base_pos` |
| The charges of M1, the block step, the leaf stabilizer, M5 | `ss_m1Charges`, `ss_blkCharges`, `ss_blockStab_sizes`, `ss_leafStab_sizes`, `ss_m4Charges`, `ss_m4_pre`, `ssM5β`, `ss_m5_rb` |
| Generator lists' lengths | `stabInPL_length_le`, `partGensD_length_le`, `outGensD_length_le`, `johnGensD_length_le_bound`, `cjohnGensD_length_le_bound`, `outGensD_length_le_bound`, `ss_giantGens_le` |
| M5's routes with their premises | `RunsWithin.c2bCJProg_jp`, `RunsWithin.c3CJRouteProg_jp`, `RunsWithin.m5Case2bCJProg_jp`, `RunsWithin.m5Case3CJProg_jp`, `RunsWithin.m5DispatchCJ_jp`, `RunsWithin.m5DispatchCJ_ns_jp`, `RunsWithin.m5CoreCJProg_jp`, `RunsWithin.m5CoreCJProg_ns_jp`, `RunsWithin.m5StepCJProg_jp`, `CJFacts` |
| The charge lemmas of M1, M2a, M2b | `ss_hint_hBo`, `ss_hint_hB`, `ss_hint_hBlift`, `ss_hint_hBgen`, `ss_m2b_sizes`, `ss_m2bCharges`, `ss_m2b_hBlift`, `ss_m2b_hBgen`, `ss_m2b_hBo`, `ss_m2b_hBgen₂` |
| The charge lemmas of M5 (each hypothesis of `RunsWithin.m5StepCJProg_jp`) | `ss_m5_hBgP`, `ss_m5_hBmem`, `ss_m5_hBlA`, `ss_m5_hBg`, `ss_m5_hBgk`, `ss_m5_hBgs`, `ss_m5_hBF`, `ss_m5_hB3`, `ss_m5_hBox`, `ss_m5_hBoy`, `ss_m5_hBg1₁`, `ss_m5_hD₁`, `ss_m5_hBg1₂ₐ`, `ss_m5_hBgen₂ₐ`, `ss_m5_hBpb`, `ss_m5_hBgm`, `ss_m5_hBlift`, `ss_m5_hBker`, `ss_m5_hBgn`, `ss_m5_hBg1₂ᵦ`, `ss_m5_hBgen₂ᵦ`, `ss_m5_hD₂ᵦ`, `ss_m5_hBg1₃`, `ss_m5_hBgen₃`, `ss_m5_hD₃`, `ss_m5_hBg1J₂`, `ss_m5_hLY₂`, `ss_m5_hDJ₂`, `ss_m5_hu₂`, `ss_m5_hBg1J₃`, `ss_m5_hLY₃`, `ss_m5_hDJ₃`, `ss_m5_hu₃`, `ss_m5_hBgmR`, `ss_m5_hBliftR`, `ss_m5_hBkerR`, `ss_m5_hsKR`, `ss_m5_hBgnR` |
| The parameter choices | `ssSIn`, `ssSIn_spec`, `m2b_params`, `ssLgM4`, `ssLgM4Ns`, `m4_params`, `m4ns_params`, `ssLgM5`, `m5_params`, `m5_params_five` |

The checks (`GraphIsoChecks/MainSimsSteps.lean`) compare, on executed runs, the step's own cost
(outside the sub-solver's markers) with the corollary's work, and every own backend call with
the bound of every charge site it matches (a site per charge lemma: an exact input for a lemma
about one call, the statement's degree and size conditions for a quantified one): M1, M2a, M2b
by `decide +kernel`; M4 on `AGL(1, 5)`, and M5's charges on `S₄` and `S₅`, by interpreter runs
that fail the build on a false result. Negative controls show that zeroing an exact site's bound
fails the check.

### Audit

Every new declaration is listed in `GraphIsoChecks/AxiomAudit.lean`, and the new modules are in
its import closure.
