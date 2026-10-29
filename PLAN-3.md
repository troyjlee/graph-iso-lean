# Lean development plan, milestone 3: Luks's strategy

Prepared 19 October 2026. **Status: complete with documented deviations**
(`lean/docs/status.md`, theorem map in `lean/docs/theorem-map.md`). There is no separate
`luks_correct` without backend bounds (correctness is part of `luks_spec`, and
`solve_luks_any` gives it for every group with the Schreier–Sims backend), and the checks
are narrower than the verification list below; `lean/docs/status.md` (milestone 3, items 2
and 5) records both. This continues
`PLAN-2.md`, whose milestone (a verified Schreier–Sims backend with polynomial charges) is
complete at commit c6817a4. The
conventions, cost model, contracts and standards of `PLAN.md` and `lean/docs/` remain in force.

## Objective and completion criteria

Milestone 2 left the solver's own recursion exponential: the default strategy branches over
point stabilizers, and its bound `solveBound Q m N` is linear in the group order `N`. This
milestone adds Luks's strategy. On a transitive window it branches over the cosets of the
kernel of the action on a **maximal block system**, where the group acts primitively on the
blocks. The cost is then governed by the orders of primitive groups, not by `N`.

The bound is stated for groups whose primitive sections are small:

- `PrimBounded G₀ c`: every primitive permutation group of degree `k ≥ 2` that is a
  homomorphic image of a subgroup of `G₀` has order at most `k ^ c`.
- For groups with composition factors in `Γ_d`, this is the Babai–Cameron–Pálfy theorem,
  with `c` depending only on `d`. That theorem is **not** formalized here.
- It is proved for **nilpotent** groups, with `c = 1`, which covers `p`-groups. A primitive
  nilpotent group has a normal maximal point stabilizer, so its order is its degree.

The milestone is complete when:

1. **Maximal block systems.** A program `maxBlocksProg` computes, from the generators of a
   group `G` transitive on a window `W` with `|W| ≥ 2`, a block list `bs` with:
   - `IsBlockList w bs` and `PermutesBlocks G bs`;
   - at least two blocks, all of the same size;
   - `G` acting primitively on the blocks: the image of `blockHom` is
     `MulAction.IsPreprimitive` on `Fin bs.length`.

   It uses no backend calls; its cost is an explicit polynomial in `n`, `|W|` and the
   generator count.
2. **The strategy.** `luksBody D` is a well-formed procedure over `groupSig D`, structured
   like `solveBody` with one change: the transitive case calls `maxBlocksProg` and then the
   block reduction `blockReduceProg`, recursing on each block. For every backend meeting the
   contracts of the operations it calls (`orbits`, `generate`, `kernel`, `cosetReps`):
   - `luks_correct`: it returns a correct answer on every valid instance;
   - correctness needs no bound and no hypothesis on the group.
3. **The cost bound.** Assume `PrimBounded G₀ c` and backend bounds `LuksBounds` (charges of
   the calls Luks makes, with at most `Rmax ≥ n ^ c` coset representatives). Then the cost
   is at most `luksBound Q c m = 2 Q m ^ (c + 1) − Q` for window size `m ≥ 1` (and `Q` for
   the empty window), with `Q` the per-invocation unit. The bound is independent of `|G₀|`.
4. **Concrete theorems** with the Schreier–Sims backend, with no assumed oracle:
   - `solve_luks`: for `PrimBounded ⟨gs⟩ c`, cost at most
     `P(n, L) + luksBound (luksQ n c) c m`, with `luksQ` an explicit polynomial in `n`
     (degree depending on `c`);
   - `solve_luks_checked`;
   - `solve_luks_nilpotent`: for a nilpotent group (in particular a `p`-group), a closed
     polynomial bound in `n` and `L` alone.
5. **Checks.**
   - Interpreter comparisons with brute force on the sweep families.
   - Runs on `2`-groups far beyond the default strategy's reach, such as the Sylow
     `2`-subgroup of `S₁₆` (order `2¹⁵`), with costs compared to the default strategy's.
   - Kernel-evaluated runs where feasible.
6. **Audit and docs.** The axiom audit is extended. The theorem map, backend contracts and
   status are updated, together with the list of remaining work.

## Design

### Invariant partitions as label arrays

A partition of the window's points is a **label array** `cl` of size `n`:

- `p` and `q` are in the same class when `cl[p] = cl[q]`;
- every label of a window point is a window point that labels itself: the class's
  **leader**.

A partition is `G`-invariant when the generators map classes into classes. The
corresponding equivalence is then invariant under `⟨gs⟩`: by finiteness, the subgroup
closure is the submonoid closure (`Subgroup.closure_toSubmonoid_of_finite`).

### The closure of a partition and a pair

`closure gs pts cl u v` computes the finest `G`-invariant partition that is coarser than `cl`
and puts `u` and `v` together. The state is the labels and a pending list of pairs, starting
from `[(u, v)]`. Processing a pair `(a, b)`:

1. if `cl[a] = cl[b]`, drop it;
2. otherwise relabel the class of `b` to the label of `a` (one array update), and queue
   `(g a, g b)` for every generator `g`.

**Correctness.**

- *Soundness.* Every class merged lies in any `G`-invariant equivalence that contains `cl`
  and `(u, v)`.
- *Invariance.* Invariant: whenever `a ~ b` and `g` is a generator, `g a` and `g b` are
  related in the equivalence generated by the classes and the pending pairs. At the end
  nothing is pending.

**Cost.** Each merge removes one leader and queues `s` pairs, so the potential
`|pending| + (s + 1) · leaders` drops at every iteration. The cost is
`O(|W| (n + |W| + s))`.

### Maximal block systems in one pass

Start from the discrete partition and the first window point `u`. For each window point `v`
in turn, if `v` is not in the class of `u`, compute `P' = closure P u v`; keep `P'` if it
has at least two classes.

At the end, every `v` is in `u`'s class or has a closure equal to the trivial partition. A
rejected `v` stays rejected: closures are monotone, so a coarser `P` gives a coarser
`closure P u v`.

The result has:

- **at least two classes**, since the start has `|W| ≥ 2` and only such partitions are kept;
- **classes that are blocks** of `G`;
- **primitive action on the blocks.** Let `B` be a block of the action on blocks with two
  elements; translate it to contain `u`'s block. The relation "the blocks of `p` and `q`
  lie in a common translate of `B`" is a `G`-invariant equivalence coarser than `P` that
  joins `u` with some `v` outside its class. So the closure of `u` and `v` is contained in
  it, and that closure is trivial; hence `B` is everything;
- **equal block sizes**, from transitivity.

The output block list lists, for each leader, the window points with its label: `O(|W|²)`.

### The strategy

`luksBody` is `solveBody` with a new transitive case:

| Case | Action | Recursive calls |
|---|---|---|
| empty window | return the input coset | none |
| fixed pointwise | check `σ` | none |
| several orbits | `seqProg` over the orbits | one per orbit, smaller windows |
| transitive | `maxBlocksProg`, then `blockReduceProg` | `R · k`, on blocks of size `m / k` |

Here `R = [G : K]` is the number of cosets of the block kernel `K`, and `k ≥ 2` is the number
of blocks.

- **Correctness** is by strong induction on the window size alone.
- **Cost.** `R` is the order of the image of the block action (first isomorphism theorem),
  which is primitive, so `R ≤ k ^ c` under `PrimBounded`. With blocks of size `b = m / k`:
  - `R · k · b ^ (c + 1) ≤ k ^ (c + 1) b ^ (c + 1) = m ^ (c + 1)`;
  - the orbit case uses `Σ |o| ^ (c + 1) ≤ (Σ |o|) ^ (c + 1)`;
  - the overheads are absorbed as in `branch_arith` and `seq_arith`, with `R · k ≥ 2` and
    at least two orbits.

  The node cost includes `cosetReps` and the final `generate` at `R ≤ Rmax`, the block
  kernel at degree `n + k ≤ 2n`, and `maxBlocksProg`.

### The Schreier–Sims instance

`Rmax = n ^ c` and `s = n²`.

- `cosetReps` costs `O(n⁶ + R² n⁴)`;
- the final `generate` costs `O(n⁶ + R n⁴)`;
- the block kernel costs `O(n⁶)` at degree `2n`.

So `luksQ n c = O(n⁶ + n^(2c+4))`. For nilpotent groups (`c = 1`) the total is `O(n⁸)` plus
the initial `generate`.

## Implementation phases and acceptance gates

| Phase | Work | Acceptance gate |
|---|---|---|
| 0 | Plan; executable models of `closure` and `maxBlocks` | `#eval` on wreath products, `S₄`, `A₄`, a primitive group: the expected maximal blocks |
| 1 | Label partitions and the closure: invariants, soundness, invariance, termination | `closure` is the finest invariant coarsening joining `u` and `v` |
| 2 | Maximal block systems: block list, block property, at least two blocks, equal sizes, primitivity of the block action | `maxBlocks_spec` |
| 3 | Programs and costs for the closure and `maxBlocks`, with well-formedness | `RunsWithin` within explicit polynomials |
| 4 | `luksBody`, `PrimBounded`, `LuksBounds`; correctness and the cost recurrence | `luks_spec` against an abstract backend |
| 5 | Nilpotent groups; the Schreier–Sims instance; entries; closed forms | `primBounded_of_nilpotent`, `solve_luks`, `solve_luks_checked`, `solve_luks_nilpotent` |
| 6 | Checks, audit, documentation | Sweep, `2`-group runs with cost comparisons, axiom listing, docs |

## Proposed layout

New modules under `lean/GraphIso/Luks/`:

- `Partition.lean`, `Closure.lean` — label partitions and the closure (phase 1).
- `MaxBlocks.lean`, `Primitive.lean` — maximal block systems and primitivity (phase 2).
- `ClosureProg.lean`, `MaxBlocksProg.lean` — programs and costs (phase 3).
- `Strategy.lean`, `Correctness.lean` — the procedure and its theorems (phase 4).
- `Nilpotent.lean` — `PrimBounded` for nilpotent groups (phase 5).

The Schreier–Sims instance goes in `lean/GraphIso/Solver/Luks.lean`, and checks in
`lean/GraphIsoChecks/Luks.lean`.

## Verification

- **Interpreter sweep:**
  - the Luks solver against brute force on the sweep families of degrees up to 4;
  - selected groups of degrees 6–8, including non-nilpotent ones (correctness holds for all
    groups);
  - costs checked against the proved bounds where `PrimBounded` is known (nilpotent groups).
- **`2`-groups:** iterated wreath products of `C₂` on 8 and 16 points. Compare the Luks
  solver's cost with the default strategy's, at least where the latter is feasible.
- **Axiom audit** as before, with the new principal theorems listed.

## References

- Eugene M. Luks, *Isomorphism of graphs of bounded valence can be tested in polynomial
  time*, J. Comput. System Sci. 25 (1982).
- László Babai, Peter J. Cameron, Péter P. Pálfy, *On the orders of primitive groups with
  restricted nonabelian composition factors*, J. Algebra 79 (1982).
- Michael D. Atkinson, *An algorithm for finding the blocks of a permutation group*, Math.
  Comp. 29 (1975).
- Ákos Seress, *Permutation Group Algorithms*, Cambridge, 2003, Sections 5.5 and 6.
- László Babai, *Graph isomorphism in quasipolynomial time*, 2016, Section 2 (Luks's
  framework).
