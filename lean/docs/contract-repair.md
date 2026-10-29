# The contract repair of stage 14j-5a

Milestone 14, stage 14j-5a (`PLAN-14.md` §14.6). This repair applies option 1 of
`14J5-DESIGN-ISSUE.md`, decided on 24 October 2026, with the scope amendment recorded in
§14.6 item 2. It lists every changed definition and every changed protected statement, and
says how each old statement follows from the new one.

## Why

The macro-step specs take the recursive call as a hypothesis
`HSubSolves X body DV sub (fun J => SizeChild I J ∧ XChild …) C s`, with one cost `C` per
measure. Before the repair, two facts were missing.

- **No generator bound on the children.** The cost of a run grows with the number of input
  generators, so no single `C` covered every child.
- **No bound on the number of children.** `ChildList` allowed any number of children with an
  empty window. Each sub-call costs at least `1`, but `pot Q b 0 m = 0`.

## Changed definitions (`GraphIso/Main/Frame.lean`, `M2bLoop.lean`, `RD.lean`)

| Definition | Before | After |
|---|---|---|
| `SizeChild` | `SizeChild I J`: fields `n₀`, `n_le`, `degree_le` | `SizeChild sC I J`: the same fields and `gens_le : J.inst.2.2.2.gens.length ≤ sC` |
| `ChildList` | `ChildList n c pred ch`: fields `sum_le`, `pred` | the same and `pos : ∀ x ∈ ch, 1 ≤ x.1` |
| `MlChild` (the block-stabilizer loop's sub-call predicate) | `MlChild n₀ n N' p J`: same `n₀` and `n`, degree `N'`, `M2bChild` | `MlChild sC n₀ n N' p J`: the same and `J`'s generator count `≤ sC` |
| `DOutGens` (field `gens` of `RDOrbit`) | for tags `3`, `5`: `R`'s and the child's generator counts `≤ sIn` | the same, and for tags `1`, `2`, `4`: the child's generator count `≤ sIn` (**scope amendment**) |

The new definition is `supTo f k`, the largest of `f 0, …, f k`.

## New lemmas

The frame (`Frame.lean`):
- `ChildList.length_le`: `ch.length ≤ c · n`, from `pos` and `sum_le`;
- `ChildList.mono_factor`: a larger factor (moved here from `M5Case2bCJ.lean`);
- `SizeChild.closed`: if the parent has at most `nB` string positions and degree at most
  `NB ≥ 2 nB`, and `sC ≤ sG`, then the child has at most `nB` string positions, degree at
  most `NB` and at most `sG` generators;
- `SizeChild.mono`: a larger bound;
- `HInstValid.win_pos`: a hinted window has a point;
- `le_foldr_max` and `le_supTo`.

Case 2a (`M5Cases.lean`): `m5_exists_genOut_le`, with `m5ListsOver` and `m5_mem_listsOver`.

## How each old statement follows

Every changed protected statement keeps its name, its program, its conclusion's run, cost,
`AnsOK` and generator bound, and every hypothesis on the parent. Changes of two kinds give
the old statement back:

- **(i) A weaker sub-solver hypothesis.** The new predicate is the old one with `J`'s generator
  count bounded by `sC`. Given the old `hsub`, `HSubSolves.mono` gives the new one, since
  `SizeChild sC I J → SizeChild_old I J`.
- **(ii) A stronger conclusion.** The new `ChildList` has `pos`; forgetting it gives the old
  `ChildList`.

Where `sC` is an expression in data and parameters the statement already has, no hypothesis
is added. Implicit binders `{sIn}`, `{sR}`, `{sm}` moved before `hsub` where `sC` needs them;
reordering implicit binders does not change the statement's content.

Two statement groups go beyond (i) and (ii):

- **(iii) `RDOrbit`: the strengthened `DOutGens`.** These statements take an `RDOrbit`
  hypothesis (`hD`, `hD₁`, `hD₂ᵦ`, `hD₃`, `hDJ₂`, `hDJ₃`, the per-orbit facts of reduce-and-derive).
  `RDOrbit`'s field `gens : DOutGens sIn …` now also bounds the child of tags `1`, `2`, `4`, so
  the hypothesis is stronger. The old statement follows only when the strengthened `DOutGens`
  holds.
  - **Why it is needed.** Those children are re-based `generate` outputs. Bounding their count
    needs a valid input, and for tag `4` that needs `K` to preserve the Johnson structure,
    which `rdProg` does not assume.
  - **Who decided.** This was the user's decision of 24 October 2026, recorded in
    `PLAN-14.md` §14.6.
  - **Discharge.** Stage 14j-5b proves it for Schreier–Sims at the callers. For tag `4`, Johnson
    preservation (`rd_orbit_cj`'s `hK`) gives valid re-based generators, and then the
    backend's output bound applies. Tags `1` and `2` follow likewise from the M1 and M2a
    models.
- **(iv) Case 2a: one new hypothesis on a fresh parameter.**
  - **The gap.** `RunsWithin.m5Case2aProg` solves each pullback sub-call after restricting it
    to its window, so the child's group is a `generate` output at a degree of at most `|W|/2`.
    Nothing in its hypotheses bounds that output.
  - **The new hypothesis.** It takes a fresh `{sR}` and
    `hgR : ∀ M ≤ |W|/2, ∀ hs, AllValid M hs → hs.length ≤ s → |generate (M, hs)| ≤ sR`.
  - **Why the domain is unchanged.** At each degree there are finitely many valid generator
    lists of at most `s` entries, so `m5_exists_genOut_le` proves that some `sR` satisfies
    `hgR` for every backend. The old statement follows by choosing that `sR`.
  - **Discharge by the callers.** M5's dispatch, core and step discharge `hgR` from their
    existing `Bm : ∀ M, BackendBounds X DV M (sm M) ⊤` (field `genOut`), with
    `sR = max sIn (supTo sm (|W|/2))` and no new hypothesis.

## The changed protected statements

`sC` is the generator bound of the sub-solver predicate. Every statement with a `ChildList`
conclusion gains `pos`; that is all 29 but `m5Case2aProg`, whose sub-calls are counted by
number.

| Statement | `sC` | Where the bound comes from | Kind |
|---|---|---|---|
| `RunsWithin.chainProg` | `max s gs.length` | the sequential reduction's `SeqSub` bound | (i), (ii) |
| `RunsWithin.kerRedProg` | `max s (kerModel X.O n (N, gs, d)).2.1.length` | the block reduction over the kernel's orbits | (i), (ii) |
| `RunsWithin.m3Prog` | the same, for the instance itself | as `kerRedProg` | (i), (ii) |
| `RunsWithin.m0StepProg` | `(rebaseModel X.O n N (maxBlocks N gs w) gs).2.1.length` | the child is that group | (i), (ii) |
| `RunsWithin.m1StepProg` | `(rebaseModel X.O n N (singD (m1O …)) gs).2.1.length` | the child is that group | (i), (ii) |
| `RunsWithin.m2aStepProg` | `(rebaseModel X.O n N (mbD n N gs) gs).2.1.length` | the child is that group | (i), (ii) |
| `RunsWithin.m2bLoopProg` | `sIn` (in `MlChild`) | `DynHandle`'s input bound | (i), (ii) |
| `RunsWithin.m2bStepProg` | `sIn` | the loop's `MlChild sIn` | (i), (ii) |
| `RunsWithin.rdProg`, `rdProg_part_ns`, `rdProg_cj_ns` | `sIn` | `DynHandle`, `RDBounds.kerGens`, `DOutGens` (all tags) | (i)–(iii) |
| `RunsWithin.m4StepProg`, `m4StepProg_ns` | `sIn` | reduce-and-derive | (i)–(iii) |
| `RunsWithin.alignRd` | `sIn` | reduce-and-derive on each aligned coset | (i)–(iii) |
| `RunsWithin.m5Case1Prog`, `m5Case2bProg`, `m5Case3Prog`, `m5Case3Prog_part` | `sIn` | reduce-and-derive; the comparisons' `StepSubP`; Case 3's fallback `m3Prog` with `max s kerGens ≤ sIn` (`RDBounds.kerGens`) | (i)–(iii) |
| `RunsWithin.m5Case2bCJProg`, `m5Case3CJProg` | `sIn` | as above, with `rdBranch` at `(2, X₀)` | (i)–(iii) |
| `RunsWithin.m5Case2aProg` | `sR` | the restricted pullback sub-calls, by `hgR` | (i), (ii), (iv) |
| `RunsWithin.m5Dispatch`, `m5CoreProg`, `m5CoreProg_ns`, `m5DispatchCJ`, `m5CoreCJProg`, `m5CoreCJProg_ns` | `max sIn (supTo sm (|W|/2))` | `sIn` for the certificates and Cases 1, 2b, 3; `Bm`'s `genOut` for Case 2a | (i)–(iii) |
| `RunsWithin.m5StepProg`, `m5StepCJProg` | `max sIn (supTo sm (|W_P|/2))` | the core on the restricted instance (`|W| = |W_P|`) | (i)–(iii) |

`RunsWithin.viaChildProg` and `RunsWithin.m5CertProg` take `HSubSolves` with an abstract
predicate and are unchanged. No other protected statement changed. Statements were compared
with the loop's base commit `f1d8696`, and no protected statement outside the table mentions
`SizeChild`, `ChildList`, `MlChild`, `RDOrbit` or `DOutGens`.

The loop's gate snapshots statements with Lean's default `ppExpr`, which prints deep subterms
as `⋯`. It reports 22 of the 29 as changed. The changes to the other seven sit inside elided
subterms, so the gate's text is identical before and after:
- `alignRd`;
- `m5Case2aProg`, `m5Case2bProg`, `m5Case3Prog`, `m5Case3Prog_part`;
- `m5Case2bCJProg`, `m5Case3CJProg`.

They changed as the table says. The comparison above was made on the source.

## Positive windows

`pos` is proved where the children are created:
- orbits are nonempty (`IsOrbitPartition`): the chain rule, the kernel reduction, tag `5`;
- the dynamic chain's handles receive nonempty orbits (`DynHandle`): tag `0`, the loop;
- a hinted window has two points with different labels (`HintValid.nonconst`,
  `HInstValid.win_pos`): M1, M2a;
- M0 has `2 ≤ |W|`.

The combinators (`RDRes`, `rd_handle`, `rd_branch`, `ml_branch`, `ar_branch_max`,
`m5_alignSub`, `m5_replicate_childList`) carry `pos` through.

M5 has sub-calls counted by number rather than listed in `ChildList`:
- `2 · certCount + m5CK` certificate and comparison calls;
- `m5CH` pullback calls.

These are bounded through the monotone `C · none`, not by `pot`, so they need no positivity.

## For stage 14j-5b

- **One closed bound.** With Schreier–Sims, every step's `sC` is at most `sG = NB²`, given:
  - `NB` bounds every degree in the recursion;
  - `sIn = NB²` for the backend bounds;
  - `sm M = M²`.

  Then `SizeChild.closed` keeps `n ≤ nB`, `degree ≤ NB` and `gens ≤ sG` along the recursion.
- **Obligations.**
  - The strengthened `DOutGens`, for every tag.
  - `hKs`, `hsR`, `hsR'`, `hsK`, `hsKR`, `M5Bounds`.
  - Backend bounds at `s = NB²` for degrees below `NB`; `ssBounds` fixes `s = n²`.
- **The empty root.** It is the base case (`fixedStepProg`, cost `fixedStepCost 0`), with its
  own cost bound.

# The label invariant of stage 14j-6a

Milestone 14, stage 14j-6a (`PLAN-14.md` §14.10). **This is a semantic contract amendment.**
It was decided by the user on 25 October 2026 ("in place, with label facts in `DOutcome`",
the pattern of the `DOutGens` amendment above). Protected statement texts are unchanged, but
the meanings of the statements listed under (vi) below change: they assume more of the
derived hints. Their old forms do not follow by forgetting fields. Unchanged gate hashes do not
establish semantic preservation, and this record lists every affected statement.

## Why

The Johnson fallback of reduce-and-derive branches over at most `u!` cosets, where `u` counts
the union cells at a point (`rd_cj_reps5`). That count is at most `t · s`, for labels of length
`t` and Johnson parameter `s`. The potential of stage 14j-6c needs `t` polylogarithmic at every
instance the recursion reaches. This is the invariant of §5 item 8:
`t (λ(m) + 1)² ≤ 2 (λ(n₀) + 1)²` while the base `m` exceeds `ell0 n₀`.

The step specs see their children only through the sub-solver predicate (`SizeChild`).
Reduce-and-derive sees its derived children only through `RDOrbit`'s `DOutcome`, so both carry
the invariant.

## Changed definitions

| Definition | Before | After |
|---|---|---|
| `SizeChild sC I J` (`Frame.lean`) | fields `n₀`, `n_le`, `degree_le`, `gens_le` | the same and `lab : LabInv I → LabInv J` |
| `DOutcome.inter`, `.blockLab`, `.blockStab` (`Derive.lean`) | the child `L'` as before | the same and `hlab : labLen L' ≤ labLen L` |
| `DOutcome.johnUnion` | `ChildOK`, `w'.1 = O`, `4 (N' − n) ≤ 3 (N − n)` | the same and `hlab : ∃ s, labLen L' ≤ labLen L · s ∧ C(N' − n, s) ≤ N − n ∧ 2 ≤ s ∧ 2s ≤ N' − n` |

The other `DOutcome` constructors are unchanged: `noHint` and `johnFallback` have children
without a hint, and `stuck` has none.

## New definitions

- `labLen L` (`Toolkit/Labels.lean`): the largest length of the lists of `L`.
- `ell0 n₀ = max 2¹¹ ((λ(n₀) + 1)³)`, `LabInvAt n₀ m t` and `LabInv J` (`Frame.lean`).
- `MlChildL sC n₀ n N' p L'` (`M2bLoop.lean`): `MlChild`, and a hinted sub-call has the loop's
  labels `L'`. `MlChild` itself is unchanged.
- `LabInvIf`, `MainSubB`, `MainSubL` (`FullStep.lean`).

## Unprotected helpers with new premises

`RunsWithin.m1ContProg` and `RunsWithin.blocksProg` used to allow labels unrelated to the
parent's `L`. They now take the length comparison explicitly:

| Helper | New premise | Discharged by |
|---|---|---|
| `RunsWithin.m1ContProg` | `hLL : labLen L' ≤ labLen L` | `deriveFreeProg`: `le_rfl` (`L' = L`); `deriveCJProg`: `labLen_labDiffD_le` |
| `RunsWithin.blocksProg` | `hLL : labLen L₁ ≤ labLen L` | `m1ContProg`: M1's labels, `labLen_labM1D_le` with `m1O_facts`, then `hLL` |
| `rd_sem124` | `hLab : LabInvAt n₀ m (labLen L) → LabInvAt n₀ m' (labLen L')` | the dispatch: `LabInvAt.mono` (tags 1, 2), `LabInvAt.johnson` (tag 4) from `DOutcome`'s `hlab` |
| `rd_sem3` | `hlab : labLen L' ≤ labLen L` | `DOutcome.blockStab`'s `hlab` |

`RunsWithin.m2bLoopProg_lab` (new) is `m2bLoopProg` with the predicate `MlChildL`. The
protected `RunsWithin.m2bLoopProg` (with `MlChild`, unchanged) is its corollary.

## The affected protected statements

Of the 263 protected targets, 46 mention `SizeChild`, `MlChild`, `RDOrbit` or `DOutcome`. The
list comes from a script over the source of every target, with the base commit `5cc89f4`.

- **(v) `SizeChild` only, as a sub-solver predicate: stronger.** These 14 statements are
  stronger:
  - `chainProg`, `kerRedProg`, `m3Prog`, `m0StepProg`, `m1StepProg`, `m2aStepProg`,
    `m2bStepProg`;
  - `m5Case2aProg`;
  - the Schreier–Sims corollaries `m1StepProg_ss`, `m2aStepProg_ss`, `m2bStepProg_ss`,
    `m4StepProg_ss`, `m4StepProg_ns_ss`, `m5StepCJProg_ss` (all `RunsWithin.…`).

  `SizeChild` occurs only in `hsub : HSubSolves … (fun J => SizeChild … ∧ …)`. A stronger
  predicate makes `hsub` weaker, so the old statement follows by `HSubSolves.mono`. Every proof
  proves `lab` where it builds a child:
  - children without a hint: `SizeChild.lab_none`;
  - M0: `labLen_labM0D`, `LabInvAt.of_le_one`, `childHInst_labInv`;
  - M1, M2a: `labLen_labM1D_le` and `labLen_labM2aD_le` with `LabInvAt.mono`;
  - M2b and tag `3`: `MlChildL` with `labLen_m2bLabels_le`;
  - tag `6`: the same labels;
  - M5's restriction: `labLen_rbLabels_le`.
- **(vi) `RDOrbit` hypotheses: changed meaning.** These 29 statements (all `RunsWithin.…`) take
  per-orbit `RDOrbit` hypotheses (`hD`, `hD₁`, `hD₂ᵦ`, `hD₃`, `hDJ₂`, `hDJ₃`):
  - `rdProg`, `rdProg_part_ns`, `rdProg_cj_ns`;
  - `m4StepProg`, `m4StepProg_ns`;
  - `alignRd`;
  - `m5Case1Prog`, `m5Case2bProg`, `m5Case3Prog`, `m5Case3Prog_part`;
  - `m5Dispatch`, `m5CoreProg`, `m5CoreProg_ns`, `m5StepProg`;
  - `m5Case2bCJProg`, `m5Case3CJProg`, `m5DispatchCJ`, `m5CoreCJProg`, `m5CoreCJProg_ns`,
    `m5StepCJProg`;
  - `m5Case2bCJProg_jp`, `m5DispatchCJ_jp`, `m5CoreCJProg_jp`, `m5StepCJProg_jp`,
    `m5DispatchCJ_ns_jp`, `m5CoreCJProg_ns_jp`, `c2bCJProg_jp`, `c3CJRouteProg_jp`,
    `m5Case3CJProg_jp`.

  `RDOrbit`'s field `out : DOutcome …` now carries `hlab`, so those hypotheses are stronger.
  Their `hsub` is weaker, as in (v). The old statements follow only for derived hints whose
  labels meet `hlab`.
- **`MlChild`: unchanged.** `RunsWithin.m2bLoopProg` mentions only `MlChild`, which is
  unchanged. It keeps its meaning and is now a corollary of `RunsWithin.m2bLoopProg_lab`.
- **(vii) `DOutcome` as a conclusion: stronger.** `RunsWithin.deriveProg_free` and
  `RunsWithin.deriveProg_cj` prove the new fields:
  - tags `1`–`3`: `labLen_labM1D_le`, `labLen_labM2aD_le`, `labLen_m2bLabels_le`, through the
    premises of `m1ContProg` and `blocksProg`;
  - tag `4`: the witness `s = jd.2.2.1`, the Johnson parameter of the structure's data.
    - `labLen_labJUD_le` with `JValid.f_len` (every point of `V₀` lies in `s` cells);
    - `dv_cj_choose_le`: `C(nc, s) ≤ m` from `IsJohnson.surj`, through `dv_johnson_choose_le`
      and `dv_jdec_card`;
    - `IsJohnson.two_le` and `IsJohnson.le_half`.

## Discharge paths

The strengthened `RDOrbit` hypotheses of (vi) are discharged as before, with no new
hypothesis:
1. `deriveProg_free` and `deriveProg_cj` (vii) give `DOutcome` with the label facts.
2. `rd_orbit_free` and `rd_orbit_cj`, and their Schreier–Sims forms (`rd_orbit_free_ssU`,
   `rd_orbit_cj_ssU`, `ss_m4_hD` and the M5 ones of `SimsM5.lean`), build `RDOrbit` from them.
3. The Schreier–Sims corollaries, `main_step`, `main_spec` and the headlines `mainSolve_ss`,
   `mainSolve_ss_const`, `mainSolve_ss_dom` have no `RDOrbit` hypothesis.
   - Their parent domains, correctness, progress and executed-cost bounds are as before.
   - The corollaries of (v) are strictly stronger.
   - `main_step`, `main_spec` and the headlines keep their meaning: `MainSub` and `MiniDom` are
     unchanged.

The new target `main_step_lab` is `main_step` for a parent with `LabInv`, with the sub-solver
hypothesis only for the domain's instances with `LabInv` (`MainSubL`). Both are cases of
`main_step_gen` (`b = false`, `b = true`).
