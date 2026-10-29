# Lean development plan, milestone 14: Babai's recursion

Prepared 22 October 2026. This continues `PLAN-13.md` (local certificates and their
aggregation, commit 636babc). The conventions, cost model, contracts and standards of `PLAN.md`
and `lean/docs/` remain in force, and so does the CFSG-free route of `PLAN-12.md`: the
classification enters only through the interfaces `AltQuotientIso K` and `TransitivityBound T`,
as explicit hypotheses of the cost theorems.

Milestone 14 is the main recursion (Helfgott §§3, 5.3, 6.3 and Appendix A; Babai §§3, 11, 12,
13.1), the costed programs of milestones 11–14, and the quasipolynomial cost. It is far larger
than the earlier milestones, so it runs as ten stages (§4); the last is split into six loops. This plan fixes
the algorithm and its analysis for all of them. Section 5 gives the completion criteria of the
first stage, 14a, which formalizes the recursion's mathematics before any program is written.

## 1. Why the recursion needs a design of its own

Neither source gives the recursion in a form that can be formalized as it stands.

- **Babai** keeps the recursion short by two results:
  - the Main Structure Theorem (§8.5, through the Jordan–Liebeck theorem), which provides
    *standard blocks* for every giant representation;
  - Cameron's theorem, whose CFSG-free replacement (§13.1) he only outlines. There, a Johnson
    scheme whose group acts on its point set `Λ` as a non-giant is to be handled by "recurse
    (find orbits and minimal block system for the action on `[m]`, etc.)".
- **Helfgott** carries a tower of block systems with the potential
  `ρ = Σ (2⌊log₂ rᵢ⌋ − 1)`, and leaves the CFSG-free branch to a remark.

On the CFSG-free route the recursion meets, at the level of a block system, groups that are
neither small nor giant. It must keep track of how the blocks of the current window relate to
the set on which such a group acts, through several changes of that set (orbit, quotient by
blocks, Johnson coordinates). The design below does this with one device, **labelled hints**,
which replaces both the standard blocks and the tower. As a result the Main Structure Theorem
and the Jordan–Liebeck theorem are not needed.

## 2. The algorithm

### 2.1 Instances and hints

An instance is a string-isomorphism instance in the existing sense: strings `x, y`, a window
`W` and a left coset `σ • G`. The answer is `iso W σ G x y`. Alignment (`iso_eq_smul_iso_one`)
reduces to `σ = 1`. An instance may carry a **hint**:

- a finite **base** `Γ` with a homomorphism `ψ : G → Sym(Γ)`;
- **labels** `lab : W → 2^Γ`, equivariant (`lab (g u) = ψ(g) · lab u` for `g ∈ G`) and **not
  constant** on `W`.

The label fibres form a system of blocks.

**Invariant: an instance carries a hint only if its group is transitive on its window.** The
recursion attaches hints only to orbits of the current group, and M0 creates them only for
transitive instances. Under this invariant every fibre has at most `|W|/2` points. Any subgroup
that fixes every label keeps each of its orbits inside a fibre, which is the source of all
window progress. Without transitivity the half-window bound fails (audit of round 1, F1: a
six-point orbit with constant labels in a seven-point window).

Write `n = |W|`, `m = |Γ|`, `t = max |lab u|`, and `P = ψ(G)`.

In programs, `G` acts on `Ω ⊔ Γ`, so `ψ(g)` is the restriction of an extended permutation, and
the backend's orbits, stabilizers, kernels and lifts on the `Γ` positions compute `P`'s orbits,
the preimages of `P`'s stabilizers, `ker ψ`, and lifts of elements of `P`. This is how the block
kernel is already computed (`blockKernelProg`, at degree `n + k`).

### 2.2 Macro-steps

Each step of the recursion is a **macro-step**. It reduces `G` to a subgroup `H`, branching over
coset representatives with a multiplicative factor `c`. It then applies the chain rule over the
`H`-orbits of the window and calls the recursion on each orbit:

- with a derived hint, if the labels are not constant on that orbit;
- without a hint otherwise, in which case the orbit lies inside a fibre of the transitive
  parent and has at most `n/2` points (`orbit_child`).

An intransitive `G` occurs only without a hint (by the invariant). It is handled by the chain
rule over its orbits, with children that carry no hint and have smaller windows. For a hinted,
hence transitive, `G` the macro-step depends on
`P` acting on `Γ`; `ℓ = ℓ(n₀)` is a polylogarithmic threshold. Each derived hint below is a
**coarsening**: a new base built from `Γ`, with labels computed from the old ones and kept
equivariant and not constant.

| Case | Reduction (factor `c`) | Progress |
|---|---|---|
| **M0.** No hint | a maximal block system `Φ` of `G` on `W` (singletons if `G` is primitive), labels `u ↦ {block of u}` (`c = 1`) | the hint is created with `m ≤ n` |
| **M1.** `P` intransitive | none | base: a `P`-orbit `Γᵢ` on which `lab ∩ Γᵢ` is not constant (one exists); `m' < m` |
| **M2a.** `P` transitive with blocks `Ψ`; some label does not meet every block in the same number of points | none | base `Ψ`; labels: the blocks met by `lab u`, or, if `lab u` meets every block, the blocks where `|lab u ∩ B|` is least; `m' ≤ m/2`, `t' ≤ t` |
| **M2b.** As M2a, but `|lab u ∩ B| = j` for every block (`0 < j < |B|`) | the stabilizer of one block `B₀` (`c = |Ψ|`) | base `B₀`, labels `lab ∩ B₀`; not constant on every new orbit, since the stabilizer of `B₀` is transitive on `B₀`; `m' ≤ m/2` |
| **M3.** `P` primitive, `m ≤ ℓ` | `ker ψ` (`c = |P| ≤ ℓ!`) | windows inside fibres, `n' ≤ n/2`, no hint |
| **M4.** `P` primitive, not a giant, `m > ℓ` | see below | `m' ≤ 3m/4`, or `n' ≤ n/2` |
| **M5.** `P` giant (`Alt(Γ) ≤ P`), `m > ℓ` | the giant macro-step (§2.3) | `m' ≤ 3m/4`, or `n' ≤ n/2` |

**M4** proceeds as follows.
- Let `d` be the degree of transitivity of `P`. Then `d ≤ T(m)` under `TransitivityBound T`
  (`exists_degree`).
- Individualize `d − 1` points `S`, with factor at most `m^{d−1}`. Then `P_(S)` is transitive
  and not doubly transitive on `Γ ∖ S` (`fixing_transitive_not_two`).
- If `P_(S)` is imprimitive there, its blocks give a colored partition.
- If it is primitive, its orbital configuration is uniprimitive. Split-or-Johnson (milestone 11)
  then gives a choice tree. Since the configuration depends on `G` alone, the tree is
  `G`-invariant.
- Reduce to the stabilizer of its first reachable leaf. Its index is at most the tree's count,
  `2^{129(⌈log₂ m⌉+2)²}`. The stabilizer is computed by orbit–stabilizer on leaf structures,
  not through the individualized path, whose cells would need setwise stabilizers.
- The **progress lemmas** of §5 then turn the leaf into a derived hint:
  - a **colored `t₀`-partition** (`IsColPart`, `t₀ ≈ 3m/4`) gives a base of at most
    `max(t₀, m/2)` points;
  - a **Johnson scheme** `V₀ ≅ Λ^{(s)}` (`IsJohnson`) gives a base of at most
    `max(m − t₀, √(2m) + 1)` points, through the *Johnson union* (§5, item 2).
  - When the Johnson union is constant, the step falls back to the pointwise stabilizer of the
    union `U₀`, with factor at most `|U₀|! ≤ (ts)!`. Every orbit of that group lies inside a
    fibre.

### 2.3 The giant macro-step (M5)

`P ⊇ Alt(Γ)` and `m > ℓ`. The group is first restricted to the window (Babai Obs. 3.1.10). The
labels are then all `t`-subsets of `Γ`, each fibre has `n/C(m, t)` points, and `t ≤ m/2` after
complementing.

1. **Certificates** (milestone 13). For every `A ∈ Γ^{(k)}`, with `k = k(n₀)` chosen so that
   `Thresholds K n k` holds under the interface:
   - the beard `(W(A), H(A))`, each window group computed by Luks reduction to the kernel
     `N = H_i ∩ ker ψ_A`, with factor at most `k!`. The orbits of `N` on the new window have at
     most `n/k` points (`kernel_orbit`), and the recursion is called on them;
   - `K(A)`, and the test `Alt(A) ≤ ψ_A(K(A))`.
2. **Aggregation.** `F` is generated by the `K(A)` that pass the test, and `S` is its support.
   - Deciding fullness by this test, rather than by "`ψ_A(H(A))` is a giant", makes
     `F ≤ Aut(x)` unconditional: `cert_full`'s first half needs no thresholds. Under the
     interface the two tests agree (`cert_full`, `isFull_iff`).
3. **Case 1** (`orbitPart_valid`): the orbit-length colouring is a colored `⌊m/2⌋`-partition.
4. **Case 2a**, the pullback. Let `H` be the preimage of the setwise stabilizer of `Φ` and `K`
   that of its pointwise stabilizer.
   - Because `F ≤ Aut(x)` covers `Alt(Φ)`, `H = K F ∪ K τ F` for any `τ ∈ H` that is odd on `Φ`.
   - So `Aut_H(x)` is generated by `Aut_K(x)`, `F` and `Aut_{τK}(x)`, and `Iso_H(x, y)` is
     `g₀ · Aut_H(x)` for any `g₀ ∈ Iso_K(x, y) ∪ Iso_{τK}(x, y)`.
   - The orbits of `K` have at most `n/2` points (§5, item 6). So four recursive solutions on
     windows of at most `n/2` points finish the case, without a hint.
5. **Case 2b.**
   - The degree of transitivity `d` of `φ(F)|Φ` is at most `T(|Φ|)` (`exists_degree`).
     Individualize `d − 1` points.
   - On the rest of `Φ` the action is transitive and not doubly transitive.
   - **Canonical colour names** (audit of round 1, F2). The group `φ(F)` depends on the
     string, and an isomorphism may permute numbered orbitals; no numbering need be invariant.
     So the step proceeds as follows:
     - choose a pair `(a, b)` of distinct points (a further choice, at most `m²` options);
     - colour the pairs `0` (diagonal), `1` (the orbital of `(a, b)`) or `2`;
     - refine by 2-ary Weisfeiler–Leman (`wlRel`). The result is natural with its colour names
       (`wlRel_natural`), coherent, homogeneous, not a clique and invariant under the group
       (`wlRel_spec`).
   - **Branch on the configuration, not on the action** (audit of round 2, F3: an imprimitive
     action can give a primitive refinement, for instance on `(ℤ/4ℤ)²`).
     `wlRel_split_or_uniprimitive` is the exhaustive alternative, Babai's Split-or-UPCC test:
     - some colour graph of `wlRel R` is disconnected, and the components of the least such
       colour form a colored `⌊|Φ|/2⌋`-partition (`isColPart_comp`);
     - or `wlRel R` is uniprimitive, and Split-or-Johnson applies.

     For a primitive action only the second case occurs (`wlRel_uniprimitive`).
   - M4 uses the orbital configuration of `P` itself. That configuration depends on the group
     alone and is fixed by `P` exactly, so its names need no canonicity.
6. **Case 3.**
   - Align the supports. Colour the `k`-tuples of `Γ ∖ S` by certificate equivalence: the
     comparisons are recursive calls on windows of at most `n/k` points, for the string pairs
     `(x, x)`, `(x, y)` and `(y, y)`.
   - Run `k`-ary Weisfeiler–Leman and the Design Lemma descent (milestone 10, threshold
     `⌈|Γ∖S|/2⌉`).
   - On a dominant class, split by connected components if the 2-skeleton is imprimitive
     (Babai's Split-or-UPCC test). Otherwise apply Split-or-Johnson.
   - There is no set of `k` pairwise twins (`no_large_twins`). The descent's "large twin class"
     outcome therefore cannot occur under the interface. If it does occur, the step falls back
     to M3's kernel reduction, which is correct but expensive.
7. **Align** (Babai §11.1).
   - The structures `X(x)` and `X(y)` on `Γ` are canonical relative to choices. Take the first
     leaf for `x`, and every leaf for `y`, with factor at most the count.
   - Find `σ ∈ P` carrying one structure to the other. Lift it, shift `y`, and reduce to
     `G₁ = ψ⁻¹(Aut(X(x)) ∩ P)`. The progress lemmas then give `m' ≤ 3m/4`.

### 2.4 Correctness and cost

**Correctness is unconditional.** Every macro-step is a coset decomposition of `iso`, or an
inclusion of `iso` in the preimage of a canonical structure's stabilizer. The interfaces are
used only to bound costs, and every place where the theory needs them has a correct fallback.

**Cost.** Let `κ(m) = ⌊log₂ m⁵⌋` and `λ(n) = ⌊log₂ n⌋`, and let `Q` bound both the work of one
macro-step and its factor `c`.

- **Potential:** `B(n, m) = n² (m + 1) Q^{b (κ(m) + 4 (λ(n) + 6)²)}`, with `m := 2n + 1`
  without a hint.
- **Every macro-step satisfies** `c · Σ_children B + work ≤ B(n, m)`, and well-founded induction
  on `(n, m)` gives `cost ≤ B`. The cases are:
  - chain rule (instances without a hint): strict superadditivity of `n²`;
  - `m' ≤ 3m/4`: `κ` drops by 2;
  - free coarsenings: the `m + 1` factor;
  - windows of at most `n/2` points, or of at most `n/k` points from the certificate
    sub-calls: `λ` drops by 1, and the weight 4 dominates `κ(2n + 1)`.
- **Bounds on `Q`** under the interfaces (`K(n) ≤ C (log n)⁵`, `T(m) ≤ C' log m`):
  - `n₀^{O(k)} k!` (certificates and comparisons);
  - `m^{T(m)}` (individualization);
  - the Split-or-Johnson count;
  - `(ts)!` (Johnson fallback; `ts` is polylogarithmic by the label invariant of §5, item 8).
- **Result:** `Q = exp(O((log n₀)⁶))`, and the total cost is `exp(O((log n₀)⁸))`.

The exponent is far from Helfgott's 3, and the plan does not try to improve it.

## 3. Departures from Babai and Helfgott

- **Labelled hints instead of standard blocks.** Babai derives standard blocks for every giant
  representation from the Main Structure Theorem. Here every representation the recursion uses
  arises explicitly, as a block action, an orbit or Johnson coordinates, and the labels carry
  the standard-block information along. Neither the Main Structure Theorem nor Jordan–Liebeck
  is formalized.
- **Progress on the base, not the window, in Align.** Babai bounds the colour classes of the
  window through Lemma 5.2.1. Here Align reduces the group, and the next macro-step coarsens
  the hint to a smaller base. Lemma 5.2.1 (milestone 12) is not needed by the recursion.
- **Leaf stabilizers** are computed by orbit–stabilizer on structures. Individualizing a
  Split-or-Johnson path would need the setwise stabilizers of its cells.
- **Full test sets** are those whose certificate passes `Alt(A) ≤ ψ_A(K(A))`. This keeps
  correctness free of the interfaces.
- **Case 2b and the non-giant primitive case** use Wielandt (`TransitivityBound`), as `PLAN-12.md`
  §2 decided, and Split-or-Johnson's input is always a uniprimitive configuration, as
  milestone 11 requires.

## 4. Stages

Each stage is one loop with its own completion criteria, written into this plan when the stage
starts. A stage may split further if its audit requires.

- **14a — the recursion's mathematics** (this loop, §5): hints, coarsenings, progress lemmas,
  coset decompositions, the pullback, the potential and the label invariant.
- **14b — group toolkit programs** (§6). Hints as data on extended degrees; derived actions
  (block quotient, Johnson cells, restriction to positions); label coarsenings; degree of
  transitivity and the giant test; block systems of the base; kernel and stabilizer
  reductions with coset representatives and lifts; orbital configurations. Each has a
  `RunsWithin` spec over the backend contract.
- **14c — Split-or-Johnson programs I: the steps** (§7). The data representation and the
  programs for one level of `bsoj` (twins and degrees, the Johnson test, the base case, the
  `d`-ary structure with Weisfeiler–Leman and the Design Lemma test, `dlCont`'s pieces) and of
  `cohSoj`, each proved equal to milestone 11's model after decoding.
- **14d — Split-or-Johnson programs II: the trees** (§8). The choice trees `bsoj`, `cohSoj`,
  `sojAt` and `soj` as worklist programs enumerating the reachable leaves, with cost at most
  the count times a polynomial. Leaf stabilizers by orbit–stabilizer on leaf structures (M4).
- **14e — local certificates and their comparison as programs** (§9), refining milestone 13 and
  parameterized by the recursive call.
- **14f — structures on the base and Align** (§10): canonical structures on `Γ` with explicit
  stabilizers, isomorphism of structures inside the giant `P`, preimages under `ψ`, and the
  procedure Align. Split off from the original stage 14f when its design showed that a Johnson
  structure needs its own canonical trimming.
- **14g — aggregation, Case 1 and Case 2a** (§11): the full group `F` (by the `K(A)` test),
  the case decision, Case 1's orbit partition with Align, and Case 2a's alignment of `Φ` with
  the pullback.
- **14h — Case 2b** (§12): individualization in `Φ`, `wlRel`, Split-or-UPCC and `sojProg`,
  with Align on the resulting structures.
- **14i — Case 3** (§13): the colouring of `k`-tuples of `Γ ∖ S` by certificate equivalence,
  milestone 10's Weisfeiler–Leman and Design Lemma programs on it, and Split-or-UPCC on the
  dominant class.
- **14j — the main recursion** (§14), in six loops 14j-1 to 14j-6.
  - The procedure on instances with hints, with correctness by well-founded induction on
    `(n, m)` and cost through the potential.
  - The Schreier–Sims instance, the graph-isomorphism entry, and the final theorem, conditional
    on `AltQuotientIso` and `TransitivityBound`.

Milestones 15 (Pyber) and 16 (Wielandt) then discharge the interfaces.

## 5. Stage 14a: completion criteria

The stage goes in `GraphIso/Recursion/`, namespace `GraphIso.Recursion`. It imports milestones
10–13 and mathlib and adds no programs. `G : Subgroup (Perm Ω)`, windows are `Finset Ω`, and
the base `Γ` is a finite type.

1. **Hints** (`Hint.lean`).
   - `IsHint G W ψ lab`: equivariance on `W` and non-constancy.
   - The fibres are blocks; under transitivity every fibre has at most `|W|/2` points.
   - A subgroup whose image fixes every label keeps its orbits inside fibres.
   - **Orbit dichotomy:** for `H ≤ G`, every `H`-orbit in `W` either has non-constant labels,
     and the hint restricts to it, or lies inside one fibre.
   - `orbit_child`: for a transitive hinted instance and `H ≤ G`, every `H`-orbit keeps the hint
     or has at most `|W|/2` points.
2. **Coarsenings** (`Coarsen.lean`). Each produces a hint (with the stated bounds) on every new
   orbit with non-constant labels.
   - **Invariant subsets (M1):** for a `P`-invariant `Γ' ⊆ Γ`, labels `lab ∩ Γ'`. Some
     `P`-orbit has non-constant intersections. `t' ≤ t`.
   - **Block quotient (M2a):** base `Ψ`, labels "blocks met" or "blocks of least
     intersection". Not constant, `t' ≤ t`, `|Ψ| ≤ m/2`.
   - **Block stabilizer (M2b):** under the preimage of `Stab_P(B₀)`, `lab ∩ B₀` is not constant
     on any orbit. `|B₀| ≤ m/2`.
   - **Johnson union (M4, Align):** for an invariant Johnson structure `V₀ ≅ Λ^{(s)}`, one of
     the following holds on each orbit:
     - `lab ∖ V₀` is not constant;
     - `U(u) = ⋃_{γ ∈ lab u ∩ V₀} e(γ)` is not constant (base `Λ`, `t' ≤ ts`,
       `|Λ| ≤ √(2|V₀|) + 1`);
     - both are constant, and every element of the pointwise stabilizer of `U₀` fixes every
       label.
3. **Primitive quotients** (`Primitive.lean`).
   - `Alt(Γ) ≤ P ↔ P` is `(m − 2)`-transitive.
   - A giant is transitive on `t`-subsets (`0 < t < m`, `m ≥ 3`).
   - The setwise stabilizer of a block is transitive on it.
   - The orbital configuration of a primitive group that is not doubly transitive satisfies
     `IsCoherent2` and `IsUniprimitive`, the hypotheses of `split_or_johnson`.
   - The Weisfeiler–Leman refinement of one orbital (`wlRel`) has these properties:
     - it is natural with colour names (`wlRel_natural`);
     - it is coherent, homogeneous, not a clique and invariant (`wlRel_spec`);
     - it is uniprimitive for primitive groups (`wlRel_uniprimitive`);
     - in general, either a disconnected colour gives a colored partition by its components,
       or the refinement is uniprimitive (`wlRel_split_or_uniprimitive`).
4. **Progress lemmas** (`Progress.lean`). Let `P ≤ Sym(Γ)` preserve the structure and let `O`
   be a `P`-orbit inside `V`.
   - **Colored `t`-partition** (`IsColPart`), `|O| ≥ 2`: either `|O| ≤ t`, or `2|O| ≤ |V|`, or
     the blocks cut `O` into a `P`-invariant partition with at least two parts of at least two
     points each. In the last case M2a or M2b halves the base.
   - **Johnson structure** (`IsJohnson`): either `O ⊆ V₀`, where the Johnson union applies, or
     `O` misses `V₀` and has fewer than `|V| − t` points.

   With the bounds of item 2, the base after the next coarsening has at most
   `max(t, |V|/2, |V| − t, √(2|V₀|) + 1)` points, or the Johnson fallback applies. The
   instances used are:
   - Split-or-Johnson leaves (`ValidOut`);
   - Case 1 (`IsOrbitPart`);
   - Case 2b;
   - the Design Lemma outcomes.

   Assembling these into derived hints is part of stage 14g.
5. **Coset decompositions** (`Align.lean`), for `iso`:
   - canonical structures: `iso` lies in the preimage of the structure's transporter;
   - alignment by a lifted `σ`, giving `iso W 1 G x y = iso W σ G₁ x y` with
     `G₁ = ψ⁻¹(Stab(X(x)))`;
   - choice trees: `iso` is covered by the transporters from the first reachable leaf for `x`
     to the reachable leaves for `y` (via `CTree.reach_act`);
   - a `G`-invariant tree: the index of a reachable leaf's stabilizer is at most the count.
6. **Pullback** (`Pullback.lean`), Case 2a:
   - `H = K F ∪ K τ F`;
   - the formulas for `aut` and `iso` of `H`;
   - under labels of all `t`-subsets, `t ≤ m/2` and `2|Φ| > m`, every `K`-orbit in `W` has at
     most `|W|/2` points. The underlying count is `2 C(a, j) ≤ C(m, t)` for `a ≤ m/2`,
     `j ≤ t ≤ m/2`.
7. **Potential** (`Potential.lean`). The potential is
   `B(n, m) = n² (m + 1) Q^{b (κ(m) + 4 (λ(n) + 6)²)}`. The shift by 6 makes the inequalities
   hold for every `n ≥ 1`.
   - **The macro-step inequalities:**
     - with branching factor `c ≤ Q²`, the children (counted with multiplicity) keep the hint
       with `4m' ≤ 3m`, or drop it on windows of at most `n/2` points (`pot_step`);
     - without branching, the children have a smaller base or a smaller window, or drop the
       hint on windows of at most `n/2` points (`pot_free`). This covers the chain rule, the
       free coarsenings and the creation of a hint.
   - The resulting bound `B(n₀, 2n₀ + 1) ≤ Q^{O(log² n₀)}`, explicit.
8. **Label invariant** (`Potential.lean`). Let `ℓ ≥ max(2¹¹, (⌊log₂ n₀⌋ + 1)³)` (the exact
   constants may be adjusted by the proof). The invariant is
   `m > ℓ → t (⌊log₂ m⌋ + 1)² ≤ 2 (⌊log₂ n₀⌋ + 1)²`, for bases of at most `n₀` points.
   - The coarsenings that do not increase `t` preserve it.
   - So does a Johnson step into a base `Λ` of more than `ℓ` points. The proof uses
     `C(|Λ|, s) ≤ m`, `2 ≤ s` and `2s ≤ |Λ|`, which give `s ≤ ⌊log₂ m⌋` and
     `2⌊log₂ |Λ|⌋ ≤ ⌊log₂ m⌋ + 2`.
   - Hence at every Johnson fallback `|U₀| ≤ max(ts, ℓ)` is polylogarithmic in `n₀`.
9. **Checks** (`GraphIsoChecks/Recursion.lean`): a concrete hint, for example `Sym(5)` on
   pairs with Johnson labels; kernel-checked instances of the potential inequalities and of the
   binomial count on small ranges; the progress lemma applied to a concrete colored partition.
10. **Audit and docs:** axiom listing; `theorem-map.md`, `status.md`.

## 6. Stage 14b: completion criteria

Programs in `GraphIso/Toolkit/`, namespace `GraphIso.Toolkit`. Every program is a PHOAS `Prog`
over `groupSig D` with a well-formedness lemma and a `RunsWithin` spec. A spec is proved for an
arbitrary oracle meeting the contract on the operations it calls, with the backend charges as
hypotheses (the `LuksBounds` pattern) and its local cost explicit.

1. **The base on extended degrees** (`Base.lean`).
   - A hinted instance has degree `N = n + m`, with the string positions `[0, n)` and the base
     positions `[n, n + m)`. Both sets are invariant under the group, and windows lie in
     `[0, n)`.
   - `baseHom : ↥(denote N gs) →* Perm (Fin m)` restricts to the base.
   - Hint data is an array of labels: sorted lists of base indices, one per string position.
     `HintData.Valid` says the labels are equivariant for the generated group and not constant
     on the window.
   - The bridge: valid data denotes stage 14a's `IsHint (baseHom …) W lab`, with `W` the
     window as a `Finset (Fin N)`. Equivariance for the generators implies it for the
     generated group.
2. **Derived actions** (`Extend.lean`).
   - **Extension programs** take each generator to a permutation of `N + k` points, acting on
     `k` new positions:
     - by the induced action on a list of disjoint blocks of positions that the group
       permutes (the existing `extendProg`, generalized from blocks of the window);
     - on a list of disjoint cells whose images are cells (the Johnson cells `Λ`).
   - `dropProg` restricts a group to a list of invariant positions with renumbering: it keeps
     the string positions and drops an old base.
   - **Specs:** the outputs are valid. Extension is a homomorphism whose restriction to the
     old positions is the identity map of the group, so the extended generators generate an
     isomorphic group. The new positions carry the derived action, and the restriction
     programs compute `restrictHom` and `setAct` of stage 14a.
3. **Label programs** (`Labels.lean`).
   - The coarsenings of stage 14a on data: intersection with a position set (M1), the block
     label (M2a), intersection with one block (M2b), the Johnson union (from the cell map),
     and the complement normalization.
   - Each is proved equal to the denotation of `subLab`, `blockLabel` or `jUnion`, on
     duplicate-free label lists (part of `HintValid`; the programs output duplicate-free
     lists).
   - The cost is polynomial: `O(k t + m)` for `k` blocks, labels of `t` entries and base
     size `m`. Persistent array updates copy, so per-entry counting into an array is not
     linear in this cost model. Polynomial per-step work is all the potential needs, since
     `Q` absorbs it. (Revised after the round 1 audit of stage 14b, finding F4: the original
     criterion asked for linear cost.)
4. **Transitivity** (`Transitivity.lean`).
   - `degreeProg` computes `min(cap, d)`, where `d` is the degree of transitivity of the base
     action, by iterating `orbits` and `stabilizer` on the base positions.
   - Spec: the action is `min(cap, d)`-transitive, and not `(d + 1)`-transitive when
     `d < cap`.
   - `giantProg` decides `Alt(base) ≤ ψ(G)` through `alt_le_iff`, using `cap = m − 2`.
   - Cost: at most `cap` rounds of stabilizer and orbit charges.
5. **Block systems of the base** (`BaseBlocks.lean`). `maxBlocksProg` on the base positions
   either finds a block list with at least two blocks of at least two points, which gives
   stage 14a's `IsBlockSys` for `baseHom`, or certifies that the base action is primitive.
6. **Reductions** (`Reduce.lean`). Charges are bounded as in `BackendBounds`: for groups inside
   an ambient group with at most `s` generators, with stabilizers keeping at most `s`
   generators. Generators and coset representatives (an `IsLeftCover`) are produced for:
   - `ker ψ`, through `kernel` on the base window and `cosetReps`;
   - the pointwise stabilizer of a list of base points, through iterated `stabilizer`, with
     representatives that are products of `orbitTransversal`s;
   - the setwise stabilizer of a block, through an extension and `stabilizer`;
   - for a giant base action, the setwise stabilizer of a `k`-subset, generators only. It is
     computed through `lift`s of explicit even permutations together with the pointwise
     stabilizer. The certificates use `G_A` only as a group, and the alignments of Cases 2a
     and 3 use a single lifted `σ`. So no representatives are needed. (Revised after the
     round 1 audit of stage 14b, finding F3.)

   `liftProg` lifts a permutation of the base lying in `ψ(G)`.
7. **Orbital configurations** (`Orbital.lean`).
   - `orbitalProg` returns the `m × m` array of orbital indices of the base action. Its spec
     is the hypothesis `hc` of `orbital_uniprimitive` and `orbital_config`: colours are equal
     exactly on the same orbital.
   - `relColProg` returns the colouring `relCol R` for the orbital `R` of a chosen pair.
8. **Checks** (`GraphIsoChecks/Toolkit.lean`): interpreter runs over the Schreier–Sims backend:
   - `Sym(5)` on pairs, with its Johnson labels;
   - degrees of transitivity of `Sym(5)`, `Alt(5)` and the dihedral group `D₅`;
   - the giant test;
   - an orbital configuration (the Petersen graph's) and a kernel reduction.
9. **Audit and docs.**

## 7. Stage 14c: completion criteria

Programs in `GraphIso/SoJProg/`, namespace `GraphIso.SoJProg`, refining milestone 11's model
(`GraphIso/SplitJohnson/`). The programs make no backend calls; each has a well-formedness
lemma, an explicit polynomial cost and a `RunsWithin` spec.

1. **Data and decoding** (`Data.lean`).
   - The points are `Fin m`. Sets are duplicate-free lists (or Boolean masks).
   - Cells are lists of points; a family of cells is a list of cells.
   - A colouring of pairs is an `m × m` array, and a bipartite relation between points and
     cells is a Boolean array.
   - Decoding maps these to milestone 11's `Finset`s, `Finset (Finset (Fin m))`,
     `Fin m → Fin m → ℕ` and `A : Fin m → Finset (Fin m) → Bool`. The decoding lemmas cover
     membership, cardinality and the operations used below.
2. **Twins and degrees** (step 1 of `bstep`). Programs equal, after decoding, to:
   - `deg`, `tw`/`twinCls`, `tfDeg`, `bigDegs` and its minimum;
   - `twinPart`, as a `CPart`: colours and blocks.
3. **The Johnson test** (step 2): `nbr`, `sOf`, `fOf`, the binomial coefficient, and the leaf
   `⟨V₁', V₂, s, fOf …⟩`.
4. **The base case** (step 0): the enumerations of `V₂` (`enums`), `nbrCode` and `colPart`.
5. **The `d`-ary structure** (step 3):
   - `arity` (through `Nat.clog`);
   - the colouring `daryCol` on codes of `d`-tuples of cells;
   - `bigTwins` (the twin test of a `d`-ary colouring) and `pickSide`.
6. **Weisfeiler–Leman on sets.** `wlOn` (milestone 11), for `d`-ary colourings of the cells
   and for the classical colouring `cohOn` on `V₁' ⊔ V₂`, computed by milestone 10's `wlProg`
   through a renumbering (`wlOn_eq'`).
7. **The Design Lemma test and `dlCont`'s pieces**:
   - `cls1`, `skel1`, `skel2` and the clique test, giving `DLGood` for a given list;
   - the lists `tuplesLt` and their filter;
   - `selThird`, the dominant classes `C₂`, `C₁`, and the constancy test.
8. **One level of `cohSoj`**: `offCols`, the components `comp`, `disconn`, and the choices
   (`big`/`violet`, `good`, `blues`) with the leaves they produce, `bipEdge` and `colPart`.
9. **Checks** (`GraphIsoChecks/SoJProg.lean`): interpreter runs comparing each program with the
   model on small inputs, among them the Petersen and Clebsch configurations and Johnson
   schemes `J(5, 2)` and `J(6, 3)`.
10. **Audit and docs.**

## 8. Stage 14d: completion criteria

Programs in `GraphIso/SoJTree/`, namespace `GraphIso.SoJTree`. They compose the stage 14c steps
into whole trees (milestone 11's `bsoj`, `sojAt` and `soj`) and compute leaf stabilizers. The
tree programs make no backend calls. The leaf stabilizer calls the backend through the group
signature, as `blockStabProg` does. Each program has a well-formedness lemma, an explicit cost
and a `RunsWithin` spec.

1. **Leaf multisets and tree sizes** (model level).
   - `CTree.leafMs`: the multiset of the leaves of all root-to-leaf paths. Its cardinality is
     `count` (`card_leafMs`), and its elements are the reachable leaves (`mem_leafMs`).
   - `CTree.size` counts nodes and leaves, and `CTree.height` is the height.
   - Lemmas for `bind`, `trans` with an injective choice map, `withPiece`, and the `Live`
     bound `size ≤ (height + 1) · count`.
   - Height bounds for `bsoj` (linear in `|V₂|`) and `soj` (linear in `|Γ|`).
2. **Leaf data.**
   - Data for `Option (Out (Fin m))`, decoded through stage 14c's `cpartOf` and `jembOf`.
   - The leaf constructors of `bsoj` and `sojAt` on data: `twinPart`, the Johnson leaf, the
     base-case `colPart`, `addPieceOut` and `extendOut`.
   - The translation of `cohCont`'s leaves from the numbered sum `V₁' ⊔ V₂` of stage 14c.
   - Each is equal to the model after decoding.
3. **One frame.**
   - A frame is a pending call of `bsoj` together with a wrapper: the pieces and the extension
     to apply to its leaves.
   - One step of a frame on data runs `bstep` with `dlCont`, the `cohSoj` level of stage 14c,
     `cohCont`, and the guards of `shrink` and `bsoj`. It returns the leaves it produces and
     the child frames.
   - Decoding: the frame's `leafMs` is the produced leaves plus the children's `leafMs`, after
     the wrapper. The frame's `size` bounds the step's work plus the children's sizes.
4. **The tree programs.**
   - `bsojProg`, `sojAtProg` and `sojProg` are `.loop`s over a stack of frames.
   - They make no `.recur` call, since `.recur` is reserved for the main recursion.
   - Specs:
     - the output list, decoded, equals the model tree's `leafMs` as a multiset;
     - `RunsWithin` with cost at most `P(m) · size` for an explicit polynomial `P`;
     - under the hypotheses of `bipartite_split_or_johnson` and `split_or_johnson`, a closed
       bound: a polynomial in `m` times milestone 11's count bound.
5. **Leaf structures under the group.**
   - The points of a configuration are a duplicate-free list `ps` of base positions,
     invariant under `G`. `ψ_ps(g)` is the induced permutation of `Fin |ps|`.
   - A program applies a permutation to leaf data, decoding to `σ • o`.
   - A program decides equality of decoded leaves, at polynomial cost.
6. **Leaf orbits and stabilizers.**
   - `leafOrbitProg` computes, by a closure loop, the orbit of a leaf under the generators: a
     list without repetitions after decoding, together with each generator's index map on it.
     Its cost is polynomial in `N`, the number of generators, `m` and the orbit size `r`.
   - `leafStabProg` follows `blockStabProg`:
     - extend the generators by the index maps to degree `N + r`;
     - take the backend's stabilizer and transversal of the point `N`;
     - truncate.
   - Spec of `leafStabProg`:
     - generators of `{g ∈ G | ψ_ps(g) • o = o}`;
     - at most `r` coset representatives forming an `IsLeftCover`;
     - backend charges as explicit hypotheses, as in `RunsWithin.blockStabProg`.
   - **Index bound** (M4): if `c` is invariant under `ψ_ps(G)` and `o` is a reachable leaf of
     `soj c t`, then the orbit of `o` consists of reachable leaves, so
     `r ≤ (soj c t).count`.
7. **Checks** (`GraphIsoChecks/SoJTree.lean`).
   - Interpreter runs comparing the leaf lists with the model's `leafMs` on small inputs. They
     reach the Johnson leaf, the base case, the twin partition and `none` leaves.
   - `sojProg` on small uniprimitive configurations.
   - One frame step reaching each branch of `bstep`, `dlCont` and `cohCont`. Whole trees are
     too large for the `d`-ary branch, because the base case covers every
     `|V₂|² ≤ 27 ⌈log₂ 2t⌉³`.
   - Leaf stabilizers compared with brute-force stabilizers, together with the cover and the
     index bound.
8. **Audit and docs.**

## 9. Stage 14e: completion criteria

Programs in `GraphIso/CertProg/`, namespace `GraphIso.CertProg`. They refine milestone 13's
local certificates (`GraphIso/Certificates/`) for the giant macro-step M5.

**Setting.**
- `G` acts on degree `N = n' + m`. The `n'` string positions form the window `Ω`, after the
  restriction of Babai's Obs. 3.1.10, which stage 14b's restriction programs carry out. The
  base positions `[n', N)` form `Γ`.
- `G` is faithful on the string positions. So the base action `ψ` is a representation of `G`
  restricted to `Ω`, which is milestone 13's `φ`.

**Program conventions.**
- The programs call the backend.
- Every recursive call goes through a sub-solver parameter `sub`, as `seqProg` and
  `branchProg` already take one. The specs assume `SubSolves` for the instances a step
  creates.
- Each program has a well-formedness lemma, an explicit cost in the backend charges and the
  sub-solver's costs, and a `RunsWithin` spec.

1. **The paired beard** (model level). Babai compares certificates by running the beard on
   `(x, A)` and `(x', A')` in lockstep.
   - Define `pairBeard`, with windows `W_i`, `W'_i` and the coset
     `C_i = {g ∈ G | ψ(g)A = A', g W_j = W'_j for j ≤ i, x'(g u) = x(u) for u ∈ W_i}`.
   - The window grows by `W_{i+1} = W_i ∪ Aff(H_i)`, where `H_i` is the group of `C_i`.
   Prove:
   - for `x' = x` and `A' = A`, `C_i` is milestone 13's `H_i` and `W_i` its window;
   - for `σ ∈ C_i`, `σ H_i σ⁻¹` is the group `H'_i` of `x'` at `A'`, so `Aff(H'_i) = σ Aff(H_i)`
     and the lockstep needs only one beard computation;
   - `CertIso φ x x' T T'` holds if and only if the final coset contains some `g` with
     `ψ(g) ∘ T = T'`. This uses milestone 13's canonicity (its relabelling lemmas), and the
     fact that the beard reads the string only on its final window;
   - each step is a string-isomorphism coset on the affected points:
     `C_{i+1} = Iso_{C_i}(x^{Aff(H_i)}, x'^{Aff(H'_i)})`;
   - while `ψ_A(H_i)` is a giant and `|A| ≥ 5`, the orbits of `H_i ∩ ker ψ_A` on `Aff(H_i)`
     have at most `|Ω| / |A|` points (from `kernel_orbit`).
2. **Test sets and their stabilizers.**
   - A `k`-subset `A` of the base is a list.
   - `G_A` and the initial coset `{g | ψ(g)A = A'}` come from stage 14b's giant set
     stabilizer and lift.
   - `ψ_A` is the restriction to the positions of `A`.
   - The giant test of `ψ_A(H)` is on degree `k`.
3. **Affected points.** For each window point `j`, the backend's stabilizer `H_j` and the giant
   test of `ψ_A(H_j)`. The result equals milestone 13's `aff`.
4. **One beard step.**
   - Compute the kernel `N = H ∩ ker ψ_A` with at most `k!` coset representatives: the
     pointwise stabilizer of the positions of `A`.
   - Branch over the representatives (`branchProg`). Inside each branch, process `N`'s orbits
     on the affected points sequentially (`seqProg`), calling `sub`.
   - Spec: under `SubSolves` for windows of at most `|Ω| / k` points, the result is `C_{i+1}`.
5. **The certificate.** `certProg sub x A` iterates the step in a `.loop` of at most `|Ω| + 1`
   rounds, until `ψ_A(H_i)` is not a giant. It returns:
   - `W(A)` and `H(A)`;
   - `K(A) = H(A)_(Ω ∖ W(A))`;
   - the fullness test `Alt(A) ≤ ψ_A(K(A))`.

   These equal milestone 13's `beardW`, `beardH` and `certK`, and the test equals
   `IsGiantOn φ A (certK …)`.
6. **The comparison.** `certIsoProg sub x x' T T'` runs the paired beard of `(x, A)` and
   `(x', A')`, then a tuple transporter in the final group. The result is
   `decide (CertIso φ x x' T T')`.
7. **Costs.** Explicit, made of three parts:
   - a polynomial in `n'`, `m`, `k`, the generator counts and the backend charges;
   - times `k!` and the number of rounds;
   - plus the sub-solver's costs over at most `(|Ω| + 1) · k! · |Ω|` calls on windows of at
     most `|Ω| / k` points.
8. **Checks** (`GraphIsoChecks/CertProg.lean`). Interpreter runs with the Schreier–Sims
   backend and milestone 1's solver as `sub` (`.recur` of `solveBody`), compared with brute
   force:
   - beards, certificates, fullness and `CertIso`;
   - on small giant actions, for example `S₇` and `A₇` with `k = 5`;
   - for strings with and without full test sets.
9. **Audit and docs.**

## 10. Stage 14f: completion criteria

Model and programs in `GraphIso/Align/`, namespace `GraphIso.Align`, for Babai's procedure
Align (§2.3 step 7, and the alignment in Cases 2a and 2b). The base `Γ = Fin m`, and
`P = ψ(G)` contains `Alt(Γ)`.

1. **Structures on the base** (model). The canonical structures used for alignment are of
   three kinds:
   - a set `Φ ⊆ Γ`;
   - a colored partition `p` with `IsColPart univ t p`;
   - a *trimmed* Johnson embedding: `trimJ J` keeps `V₀`, `Λ`, `s` and `f` on `V₀`, and is
     empty off `V₀`.

   Requirements:
   - Trimming commutes with the action (`trimJ_smul`) and keeps `IsJohnson`. So a canonical
     structure stays canonical after trimming, and the progress lemma still applies to its
     stabilizer.
   - For every reachable leaf of `soj`, the cells are disjoint from `V₀`
     (`soj_johnson_disjoint`, an invariant of `bsoj`).
2. **Stabilizers in `Sym(Γ)`.** For each kind, an explicit list of generators with
   `closure = stabilizer` (`stabGens_closure`):
   - for a set: `Sym(Φ) × Sym(Γ ∖ Φ)`;
   - for a colored partition: transpositions inside blocks, and swaps of two blocks of one
     colour;
   - for a trimmed Johnson embedding with cells disjoint from `V₀`:
     - transpositions inside a cell;
     - swaps of two cells of equal size, together with the permutation they induce on `V₀`
       through `f`;
     - transpositions of two points outside `V₀ ∪ ⋃Λ`.
3. **Isomorphism of structures.** On data, `structIsoD X Y` returns `σ ∈ Sym(Γ)` with
   `σ • X = Y`, or none exactly when no such `σ` exists.
   - Matching is by colours, block sizes, cell sizes and `f`.
   - Inside `P = Alt(Γ)` the parity is corrected by an odd element of the stabilizer, if there
     is one. Otherwise the answer is none exactly when every isomorphism is odd.
4. **Programs.**
   - The isomorphism search and the stabilizer generators, with polynomial costs.
   - `Stab(X) ∩ P` (the even part when `P = Alt(Γ)`, by Schreier generators of index 2).
   - The preimage `ψ⁻¹(L)`, from lifts of `L`'s generators and `ker ψ` (stage 14b's `liftProg`
     and `kerProg`).
5. **Align.** `alignProg sub X(x) [Y₁, …, Y_r]` takes the structure for `x` and every reachable
   structure for `y`. For each `Y_i` with an isomorphism `σ_i ∈ P`, it lifts `σ_i` and calls
   `sub` in the coset `σ_i • G₁`, where `G₁ = ψ⁻¹(Stab(X(x)) ∩ P)`. It then combines the
   answers.
   - Spec, under `SubSolves` for these cosets: the answer is correct for `G`. This follows
     from `iso_eq_align` and `iso_reach`, given that the `Y_i` are all reachable structures of
     a canonical tree for `y`.
   - Cost: at most `r` sub-calls, plus a polynomial.
6. **Checks** (`GraphIsoChecks/Align.lean`). Kernel-checked examples (`decide`) on small
   bases, with interpreter runs as supplementary checks:
   - structure isomorphisms and stabilizer orders against brute force in `S₄`, `S₅` and `A₅`,
     for each kind;
   - Align on small instances against brute force.
7. **Audit and docs.**

## 11. Stage 14g: completion criteria

Model and programs in `GraphIso/Giant/`, namespace `GraphIso.Giant`: the first half of the giant
macro-step M5 after the certificates. The setting is that of §9 and §10. Recursive calls go
through a sub-solver parameter, and backend charges are explicit, as before.

1. **The full group** (model). `fullGroupK φ k x` is generated by the `K(A)` with `|A| = k`
   that pass the test `Alt(A) ≤ ψ_A(K(A))`, which is the test `certProg` computes. Prove:
   - `fullGroupK φ k x ≤ autG x` unconditionally, since every `K(A)` respects `x`;
   - it is canonical (`fullGroupK_relabel`), and so is its support (`suppK_conj`);
   - under `Thresholds`, it equals milestone 13's `fullGroup` (`isFull_iff`, `cert_full`).
2. **Aggregation.** `fullProg sub x` runs `certProg` on every `k`-subset of the base (in the
   order of a fixed enumeration) and generates `F` from the passing `K(A)`. It also computes
   `F`'s orbits on the base and the case:
   - Case 1: support at least `m/2` and no orbit of more than `m/2` points;
   - Case 2: an orbit `Φ` of more than `m/2` points, which is unique;
   - Case 3: support less than `m/2`.
   Spec: `F` denotes `fullGroupK` (transported), the case is decided correctly, and the cost
   is at most `C(m, k)` certificates plus the backend charges.
3. **Case 1.** The orbit-length colouring is a colored-partition datum satisfying
   `IsOrbitPart`, valid by `orbitPart_valid` and canonical. The reduction is Align with
   `partOps`, the structure of `x` against that of `y`; this needs `F` for both strings.
   Spec: the answer is correct, under `SubSolves` for the cosets of
   `G₁ = ψ⁻¹(Stab(X(x)) ∩ P)`.
4. **Case 2a** (`F` acts on `Φ` as a giant). Align `Φ(x)` with `Φ(y)` (`setOps`). Inside each
   aligned coset, apply the pullback:
   - `H` is the setwise stabilizer of `Φ`;
   - `K` is the pointwise stabilizer of `Φ`'s positions in `H`;
   - `τ ∈ H` is odd on `Φ`, if there is one;
   - the solutions come from `iso_pullback` and `aut_pullback`. The sub-calls process `K`'s
     orbits on the window sequentially; each orbit has at most `n/2` points
     (`card_orbit_le_half`).
   Spec: the answer is correct for the aligned coset, with explicit costs.
5. **Checks** (`GraphIsoChecks/Giant.lean`). Kernel-checked examples (`decide`) on tiny
   fixtures, with interpreter runs as supplementary checks:
   - `F` and the case decision against brute force;
   - Case 1 and Case 2a answers against brute-force isomorphism cosets.
6. **Audit and docs.**

## 12. Stage 14h: completion criteria

Model and programs in `GraphIso/Case2b/`, namespace `GraphIso.Case2b`: Case 2b of M5, where `F`
has an orbit `Φ` of more than `m/2` points on which it is not a giant (§2.3 step 5). Alignment
happens in the original group `G`, whose base action contains `Alt(Γ)`:
- `x`'s structure comes from the first choices and the first leaf;
- `y`'s structures come from every choice;
- every isomorphism maps `x`'s choices to `y`'s, so `iso_reach` supplies Align's alignment
  hypothesis;
- the aligned group preserves the structure, which is all the progress lemmas need. There is
  no rebasing onto `Φ ∖ S`.

1. **The choice tree** (model). `case2bTree F Φ` on the base `Γ`:
   - a node over the `(d − 1)`-tuples `S` of distinct points of `Φ`, where `d` is the degree
     of transitivity of `ψ(F)` on `Φ`;
   - a node over the pairs `(a, b)` of distinct points of `Φ ∖ S`;
   - the colouring `wlRel R` of the orbital `R` of `(a, b)` under `F_(S)` on `Φ ∖ S`;
   - then one of two branches:
     - if some colour graph is disconnected, the components of the least such colour, as a
       colored partition (`wlRel_split_or_uniprimitive`);
     - otherwise `soj` on `Φ ∖ S` with `t = ⌈(|Φ ∖ S| + 2) / 2⌉`.
   - Every leaf is trimmed (`trimOut`) and extended to `Γ`: a colored partition gets the rest
     of `Γ` as one block of a fresh colour; a Johnson embedding is transported.
   Prove:
   - **canonicity**: `case2bTree (F(relabel g x)) (Φ(relabel g x)) = (case2bTree F(x) Φ(x)).act
     (ψ g)`, from `fullGroupK_relabel`, `largeOrbit_canonical`, `wlRel_natural`,
     `split_or_johnson_relabel` (with `Φ ∖ S` numbered as `Fin m'` in list order) and
     `trim_canonical`;
   - **validity**: every reachable leaf is a colored partition of `univ` or a trimmed Johnson
     embedding meeting the hypotheses of `jvalid_of_isJohnson`.
2. **Leaves as structures.** `outOps`, a `StructOps` on leaf data `OutD`: colored partitions
   by `partOps`, trimmed Johnson embeddings by `johnOps`, and no isomorphism across kinds. Its
   `Spec` holds for the valid leaves of item 1.
3. **Programs.**
   - `F_(S)`: the pointwise stabilizer, restricted to the positions of `Φ ∖ S`.
   - Its orbital array (stage 14b's `orbitalProg`), the colouring of the pair (`relColProg`),
     and `wlRel` by milestone 10's Weisfeiler–Leman program (stage 14c's
     `get_wlA_eq_wlOn`).
   - The disconnected colours and components (stage 14c), and `sojProg` (stage 14d).
   - Trimming, and the extension to `Γ`.
   - The structures for `y` over every choice, and the first structure for `x`. The data lists
     equal the tree's leaves as multisets.
   - `case2bProg sub …` = `alignProg` with `outOps`.
   - Spec: the answer is correct for `G`, with the alignment hypothesis discharged by
     canonicity, and an explicit cost: the number of choices (at most `m^{d+1}`) times the
     tree's count, times a polynomial, plus sub-calls.
4. **Checks** (`GraphIsoChecks/Case2b.lean`). Kernel-checked examples (`decide`) on tiny
   fixtures, with interpreter runs as supplementary checks:
   - the tree's leaves against the model;
   - the canonicity of the structure lists under relabelling;
   - `case2bProg`'s answer against brute force.
5. **Audit and docs.**

## 13. Stage 14i: completion criteria

Model and programs in `GraphIso/Case3/`, namespace `GraphIso.Case3`: Case 3 of M5, where the
support `S` of `F` has fewer than `m/2` points (§2.3 step 6). As in stage 14h, the reduction is
Align in the original group:
- `x`'s structure comes from its first choices;
- `y`'s structures come from every choice.

1. **The colouring of `k`-tuples.** Colour the ordered `k`-tuples of `Γ ∖ S`:
   - one colour (gray) for tuples with repetitions;
   - otherwise by certificate equivalence (`SameColour`), with names consistent across `x`
     and `y`. A tuple of `x` is named by the first equivalent tuple of `x` in a fixed order. A
     tuple of `y` is named by the first equivalent tuple of `x` if there is one, and by a
     fresh name otherwise.
   - The comparisons are `certIsoProg` calls (stage 14e) for `(x, x)`, `(x, y)` and `(y, y)`.
   - Spec (`tupleCol_iso`): every isomorphism `g` maps the colouring of `x` to that of `y`,
     `c_y (ψ g ∘ T) = c_x T`. So everything computed from these colourings by natural
     procedures is aligned. The colourings need not be canonical one string at a time.
2. **The structures** (model). On the colouring, the `k`-ary refinement `wl` (milestone 10)
   and, for every good list `z` of the Design Lemma (`DesignGood`, threshold
   `⌈|Γ ∖ S| / 2⌉`), one of three outcomes:
   - if every vertex colour class at `z` has at most `t` points, the vertex colouring as a
     colored partition;
   - otherwise, on a dominant class `C` with non-clique individualized 2-skeleton (a coherent
     configuration by `isCoherent2_wl_skel2`), Split-or-UPCC: the components of the least
     disconnected colour, or `soj` with trimmed leaves;
   - every structure is extended to `Γ`, as in stage 14h.

   Prove:
   - **alignment**: for colourings related by `g` as in item 1, `g` maps every structure of
     `x` (over all good lists and leaves) to one of `y`'s;
   - **validity**: every structure is a valid `outOps` structure;
   - **count**: the number of structures is at most `|Γ|^k` good lists times the
     Split-or-Johnson count.
3. **Twins.** If the descent finds a class of more than `t` pairwise twins, the step reports
   it, and the main recursion falls back to M3's kernel reduction. Under the thresholds this
   cannot happen (`no_large_twins`). State it as a lemma: given `Thresholds`, the outcome is
   not "twins".
4. **Programs.**
   - The colouring (item 1).
   - Milestone 10's `k`-ary Weisfeiler–Leman program, and all good lists (stage 14c's
     `goodList` pattern, for `DesignGood`).
   - For each good list: the vertex colouring, the dominant class, the restricted 2-skeleton,
     then components or `sojProg`, trimming and the extension.
   - The first structure for `x` and all structures for `y`.
   - `case3Prog sub …` = `alignProg` with `outOps`. Spec: the answer is correct for `G`, with
     the alignment derived from item 1. Explicit costs:
     - `O(|Γ|^{2k})` certificate comparisons;
     - the Weisfeiler–Leman cost;
     - `|Γ|^k` good lists, each a polynomial times the `soj` size;
     - Align.
5. **Checks** (`GraphIsoChecks/Case3.lean`). Kernel-checked examples (`decide`) on tiny
   fixtures, including the whole program on an empty window, with interpreter runs as
   supplementary checks.
6. **Audit and docs.**

## 14. Stage 14j: the main recursion

Stage 14j composes the macro-steps into one recursive procedure. It is split into six loops
(restaged after 14j-1; the macro-steps were first planned as one loop):

- **14j-1, derived hints** (§14.1);
- **14j-2, the macro-step framework and M0–M3** (§14.2), each step a one-step reduction
  through a sub-solver;
- **14j-3, M4** (individualization, the orbital configuration, Split-or-Johnson, the leaf
  stabilizer, reduce-and-derive);
- **14j-4, M5** (restriction to the window, certificates, aggregation, Cases 1, 2a, 2b and 3,
  reduce-and-derive), and **14j-4b**, the coloured Johnson pairs of §14.1 item 5 for Cases 2b
  and 3;
- **14j-5, the recursive procedure**, with unconditional correctness;
- **14j-6, the cost and the final theorems.**

**The accounting that fixes the design.** `pot_step` pays for a macro-step with branching
factor `c ≤ Q²` only if every child does one of two things:
- it keeps a hint with base `m' ≤ 3m/4`;
- it drops the hint on a window of at most `n/2` points.

`pot_free` pays for a step without branching whose children shrink the base or the window. So a
macro-step that reduces the group (M2b, M3, M4, M5) must coarsen its children's hints *before*
recursing. This is done by the progress lemmas of stage 14a, applied to the structure the
reduced group preserves. The free coarsenings M1 and M2a are their own macro-steps.

### 14.1 Stage 14j-1: completion criteria (derived hints)

Model and programs in `GraphIso/Main/`, namespace `GraphIso.Main`. The setting is a hinted
instance on degree `N = n + m`:
- the string positions are `[0, n)` and the base is `[n, N)`;
- the labels are `LabelData`;
- the group is faithful on the string positions and transitive on the window
  (`HintValid` of stage 14b, plus transitivity).

1. **Hinted instances as data.**
   - The type of hinted instances: an instance, `n₀`, `n`, and optional labels.
   - The validity predicate `HInstValid`.
   - Its denotation as a stage 14a hint (`HintValid.isHint`).
2. **Free coarsenings, as programs.** Each returns the re-based group (`rebaseProg`) and the
   new labels. Each spec gives `HintValid` for the new data, the same action on the string
   positions (`rebase_iso`), and the new base size:
   - **M0:** a maximal block system of `G` on the window (milestone 3's programs) as the new
     base, with labels `u ↦ {block of u}`, so `m ≤ n`;
   - **M1:** an orbit of `ψ(G)` on which the labels are not constant (`exists_nonConst_inter`,
     `hint_inter`), so `m' < m`;
   - **M2a:** block labels (`hint_blockLabel`), so `m' ≤ m/2`.
3. **Coarsening reductions.** Each has a cover and its factor:
   - **M2b:** the block stabilizer (`blockStabProg`, factor `|Ψ| ≤ m`), with base `B₀` and
     labels `lab ∩ B₀` (`hint_blockStab`), so `m' ≤ m/2`;
   - **the Johnson fallback:** the pointwise stabilizer of the Johnson union `U₀`
     (`fix_of_jUnion_const`, factor at most `|U₀|!`). After it, every orbit lies inside a
     fibre.
4. **The structure-derived hint.** A group `K ≤ G` whose base action preserves a valid
   structure `X` (a colored `t`-partition, a trimmed Johnson embedding, or a set of more than
   `m/2` points), and an orbit `O` of `K` on the window, produce one of four children:
   - no hint, when the labels are constant on `O`; then `|O| ≤ n/2` by `orbit_child`;
   - a hint on a base orbit `O_b` of `ψ(K)` with `|O_b| ≤ 3m/4`, by `colPart_orbit`, case 1
     or 2, or by `johnson_orbit`'s disjoint case;
   - a block coarsening of `O_b`, by `colPart_orbit` case 3, with `m' ≤ m/2`. This uses block
     labels, or a further block-stabilizer reduction with factor at most `m`;
   - the Johnson union (`hint_jUnion`, `johnson_step_label`) with `m' ≤ 3m/4` when `m > ℓ`,
     or the Johnson fallback.

   The spec is the child's validity and the measure that `pot_step` needs: `4m' ≤ 3m`, or no
   hint with `2|O| ≤ n`. Any extra factor appears explicitly.
5. **Coloured Johnson structures** (design correction found while writing item 4).
   - The trimmed Johnson embeddings of stages 14h and 14i leave the points outside
     `V₀ ∪ ⋃Λ` free. A base orbit there can then have about `7m/8` points, so progress fails.
   - The fix: align the pair `(Q, J)` instead of `J`. `Q` is the canonical coarse partition:
     `{S, Φ ∖ S, Γ ∖ Φ}` in Case 2b, and `{S, C, (Γ ∖ S) ∖ C}` in Case 3. Each of its classes
     outside `V₀` has at most `m/2` points.
   - `cjohnOps` is a `StructOps` for coloured trimmed Johnson embeddings (Johnson data plus a
     colouring of the remaining points). Its stabilizer is `Stab(Q) ∩ Stab(J)` with explicit
     generators, and its isomorphism search respects the colours.
   - The pairs are built from the leaves of stages 14h and 14i and the canonical `Q`. Their
     alignment follows from those stages' theorems and the canonicity of `Q`; no approved
     statement changes.
   - `derived_cjohnson` is the derived hint for a group preserving `(Q, J)`.
   - Colored partitions need no change: their rest block has fewer than `m/2 + d` points,
     which is at most `3m/4` when `d ≤ m/4`.
6. **Checks** (`GraphIsoChecks/MainHints.lean`). Kernel-checked examples (`decide`) on tiny
   fixtures, with interpreter runs as supplementary checks.
7. **Audit and docs.**

### 14.2 Stage 14j-2: completion criteria (the macro-step framework, M0–M3)

Programs in `GraphIso/Main/`, namespace `GraphIso.Main`. Every macro-step takes a **hinted
sub-solver** `sub : var (hinstTy D) → Prog S rec var (Ty.answer D)` as a parameter; stage
14j-5 instantiates it with `.recur`.

`HSubSolves X body DV sub P C s` follows `SubSolves`. For every hinted instance `I` with
`HInstValid I` and `P I`, `sub I` runs within `C I` and returns an answer correct for `I`'s
instance (`AnsOK`) with at most `s` generators. Sub-calls without a hint go through the same
`sub`, with the labels `none`.

A macro-step's spec has four parts:
- its run, with an explicit cost: the branching factor times the sum of the children's costs,
  plus the work;
- an answer correct for the parent (`AnsOK`);
- the **children's predicate**, which states the measure each child gets in the form
  `pot_step` or `pot_free` uses;
- the fact that the predicate implies a strictly smaller recursion measure, for the
  well-founded induction of 14j-5.

The measure is lexicographic on `(n, m̂)`: `n` is the number of window points, and `m̂` is
the base size, or `2n + 1` without a hint. Every child shrinks the window, or keeps it and
shrinks `m̂`:
- M0 gives `m ≤ n < 2n + 1`;
- M1 gives `m' < m`;
- M2a, M2b and the derived hints give `m' ≤ 3m/4`;
- otherwise the window has at most `n/2` points.

1. **Answer transfer** (`transferProg`).
   - A parent group `K` (degree `N`) and a child group `G'` (degree `N'`) are both faithful on
     the string positions `[0, n)`. They are isomorphic with the same action there
     (`ChildOK.iso`), and the window lies in `[0, n)`.
   - An answer for the child instance becomes one for the parent: restrict it to `[0, n)` and
     lift it into `K` (`lift`), as in `restrictProg` but with a trivial kernel.
   - Spec: the child's `AnsOK` gives the parent's `AnsOK`, with explicit `lift` charges.
2. **The child instance** (`childProg`).
   - It builds a hinted child from `deriveProg`'s output, or from M0, M1, M2a or M2b.
   - The coset representative is aligned first (`iso_eq_smul_iso_one`): the target string
     becomes `y ∘ σ` on the string positions, computed at the parent's degree, so no
     condition on `σ` is needed.
   - The child gets the strings padded to the child's degree, its window, the identity
     coset, its group, `n₀`, `n` and its labels.
   - Spec: the child is `HInstValid`, and an answer for it gives, through transfer and the
     shift by `σ`, a correct answer for the parent coset.
3. **The dynamic chain rule** (`dynSeqProg`, a design correction made during 14j-2).
   - `seqProg` processes a fixed list of orbits. Each later orbit is solved in the coset
     returned so far, whose group `H` (an automorphism group of the earlier orbits) need not
     be transitive on that orbit. A hinted child must be transitive on its window (§2.1).
   - `dynSeqProg` instead repeats a step until the window is exhausted. Each step takes the
     first orbit of the *current* group `H` on the remaining window, and solves it in the
     current coset.
   - Every processed orbit is therefore an orbit of a subgroup of the starting group. The
     processed orbits partition the window, so their sizes sum to `|W|`.
   - Children without a hint need no transitivity, so `seqProg` stays correct for them (the
     chain rule, M3, the Johnson fallback, the stuck fallback).
4. **Reduce-and-derive** (`rdProg`), the common tail of M4 and M5.
   - Input: a hinted instance `(σ • G, W, L)` with `G` transitive on `W`, a left cover `rs`
     of `G` by cosets of `K ≤ G`, and a structure `st` that `K` preserves (or none).
   - For each `r ∈ rs` (`branchProg`), the coset `σ r • K` is solved by `dynSeqProg` over
     `W`. Each step's orbit `O` is an orbit of some `H ≤ K`, which also preserves `st`. It
     goes through `deriveProg` for `H`, then by tag:
     - **tag 0:** a sub-call without a hint on `O`, with `2|O| ≤ |W|`;
     - **tags 1, 2, 4:** a sub-call on the hinted child (`4m' ≤ 3m`), then transfer;
     - **tag 3:** the block-stabilizer loop (`m2bLoopProg`, shared with M2b): a branch over
       the cover of `P`, the M1 child, by at most `m` cosets of `R`. Then `dynSeqProg` over
       `O`. Each step's orbit `O''`, an orbit of some `H' ≤ R`, is either a hinted child
       with `2m' ≤ m` (when `L' = L₁ ∩ B₀` is not constant on `O''`), or a child without a
       hint. In the second case `2|O''| ≤ |O_R| ≤ n`, by `card_le_of_const` for `R`, which is
       transitive with the hint `L'` on the `R`-orbit `O_R ⊇ O''` (`hint_blockStab`). Then
       transfer;
     - **tag 5:** a branch over the cover of `P` (`K` re-based onto the cells) by at most
       `u!` cosets of `R`. Then `seqProg` over the `R`-orbits of `O`, without a hint, each
       with `2|O'| ≤ |O|`. Then transfer;
     - **tag 6 (stuck): the fallback**, the kernel reduction of M3 on `O`. It uses the cosets
       of the kernel of `K`'s base action, whose orbits lie inside label fibres
       (`2|O'| ≤ |W|`). It is correct, but its cost is not bounded by `pot_step`; under the
       interfaces the progress theorems exclude it.
   - Spec: `AnsOK` for the parent, the children's predicate per tag, and the cost.
5. **The steps.** Each step has its run, cost, `AnsOK` and children's predicate, under its
   case condition stated on data:
   - **base cases:** `|W| ≤ 1`, reusing the existing solvers' base case where one exists;
   - **the chain rule:** no hint and `G` intransitive on `W`. `seqProg` over the orbits; the
     children have no hint and fewer than `|W|` points;
   - **M0:** no hint, `G` transitive, `|W| ≥ 2`. `m0Prog` gives one hinted child with
     `m ≤ n`, then transfer;
   - **M1:** a hint and `P` intransitive. One hinted child with `m' < m`, then transfer;
   - **M2a:** `P` transitive, with a proper block system on which some label is not
     equidistributed. One hinted child with `2m' ≤ m`, then transfer;
   - **M2b:** as M2a, with every label equidistributed. `m2bProg`, then `m2bLoopProg` (item
     4, tag 3) for `G` itself, with at most `m` cosets; the children have `2m' ≤ m`, or no
     hint and at most `n/2` points;
   - **M3:** `P` primitive and `m ≤ ℓ`. The kernel of the base action (`kernel` with the
     base window) and its coset representatives (`cosetReps`, at most `m!`), then `seqProg`
     over the kernel's orbits. The children have no hint and `2|O| ≤ |W|`.
6. **Checks** (`GraphIsoChecks/MainSteps.lean`).
   - Kernel-checked examples (`decide`) on tiny fixtures, with a concrete hinted sub-solver:
     milestone 1's reference solver on the underlying instance, ignoring the hint.
   - Each step's answer is compared with the brute-force coset. The children's predicate is
     checked on the actual sub-calls, by recording them.
7. **Audit and docs.**

### 14.3 Stage 14j-3: completion criteria (M4)

M4 handles a hinted instance `(σ • G, W, L)` whose base action `P` is primitive but not a
giant. Programs live in `GraphIso/Main/`, namespace `GraphIso.Main`. The step reuses:
- the toolkit of stage 14b: `degreeProg`, `pointStabsProg`, `orbitalProg`;
- the trees and leaf stabilizers of stage 14d: `sojProg`, `leafStabProg`,
  `leafStab_index_le_count`;
- the leaf-to-structure conversion of stage 14h: `trimD`, `extD`, `extPart_valid`,
  `extJohn_valid`;
- reduce-and-derive (`rdProg`).

There is no alignment: the tree depends on `G` alone.

1. **Covers.** `IsLeftCover.trans`: a cover of `G` by `r` cosets of `K₁` and of `K₁` by `r'`
   cosets of `K₂` give a cover of `G` by the `r · r'` products. Also its data version, a
   product list of representatives.
2. **Bridges.**
   - The restriction `restrictHom` to the window `[n', N)` agrees with `baseHom` at
     `n' = n + d − 1`, after `WinData.reindex` (templates: `psiA_eq_permCongr`,
     `cp2_restrict_iff`).
   - Structures on `Fin (N − n')`, which is `Γ ∖ S`, extend to `Fin (N − n)`, which is `Γ`,
     with `S` as an extra class, by the extension of stage 14h along the shift.
   - Stabilizers and invariance transfer across these bridges.
3. **Individualization.**
   - The degree of transitivity `d` comes from `degreeProg`; the giant case is excluded by
     the case condition.
   - `S` is the first `d − 1` base positions, and `H = fixFirst G n (d − 1)` comes from
     `pointStabsProg`, with a cover of `G` by at most `m^{d−1}` cosets.
   - `H` is transitive on `[n + d − 1, N)` and not 2-transitive there (`TransAt`,
     `sameOrbit_iff_stabTrans`, `degreeModel_spec`).
4. **The structure.**
   - The orbital configuration of `H` on `Γ ∖ S` comes from `orbitalProg` at `n' = n + d − 1`.
     It is coherent, homogeneous and not a clique (`orbital_config`).
   - **If some colour graph is disconnected:** the components of the least such colour form a
     colored partition (`isColPart_comp`), and `K = H`.
   - **Otherwise** the configuration is uniprimitive:
     - `sojProg` builds the tree, with `t` chosen so that `m' + 2 ≤ 2t` and `4t ≤ 3m'`;
     - its first leaf is reachable and valid (`sojProg_leafMs`, `split_or_johnson`);
     - `leafStabProg` on `H` with the window `[n', N)` gives `K` and a cover of `H` by at most
       the tree's count (`leafStab_index_le_count`, with the configuration `H`-invariant by
       `orbitalModel_spec`).
   - The leaf, trimmed and extended to `Γ`, is the structure `st` for `rdProg`:
     - a colored partition, with `S` as a class;
     - or a coloured Johnson structure, with the colouring `{S, rest}`.
   - `K` preserves `st`, and `st` is valid.
5. **The step** `m4StepProg`.
   - It composes items 3 and 4 and calls `rdProg` with the composed cover. Spec: `AnsOK` and
     `StepChild |W| m` children.
   - The factor is `c = |reps| · F`, with `|reps| ≤ m^{d−1} · count` and the tree count of
     stage 14d.
   - **No-stuck corollary:** under explicit numeric conditions, `st` meets the hypotheses of
     `rd_ns_part` or `rd_ns_cj`. For a partition this is `4t ≤ 3m`, from `|S| = d − 1` and the
     leaf's `t`. For a Johnson structure, each colour class outside `V₀` has at most `m/2`
     points. Then `F = max(m, uB!)`.
   - These conditions are stated as hypotheses on `d` and `m` that stage 14j-6 discharges
     under `TransitivityBound`.
6. **Checks** (`GraphIsoChecks/MainM4.lean`). Kernel-checked examples (`decide`) on tiny
   primitive non-giant actions:
   - an imprimitive `H` on `Γ ∖ S`, giving a components partition;
   - a uniprimitive configuration, giving a `soj` leaf.

   Each answer is compared with the brute-force coset, and the children's predicates and the
   cover factor are checked. The instrumented sub-solver of 14j-2 is reused.
7. **Audit and docs.**

### 14.4 Stage 14j-4: completion criteria (M5, correctness and the plain cases)

**Restaging.** M5 is split into two loops:

- **14j-4 (this section):** M5 correct for every case, with progress for Cases 1 and 2a and
  for the partition leaves of Cases 2b and 3.
- **14j-4b:** the coloured Johnson alignment for the Johnson leaves of Cases 2b and 3
  (§14.1 item 5), which they need for progress.

**Setting.** A hinted instance `(σ • G, W, L)` whose base action `P` is a giant
(`Alt(Γ) ≤ P`), with `m > ℓ`. Programs live in `GraphIso/Main/`, namespace `GraphIso.Main`.

1. **Restriction to the window and base** (Babai Obs. 3.1.10).
   - `restrictBaseProg` keeps the window points and the base. The new string positions are
     `[0, |W|)` (the window, in list order) and the base is `[|W|, |W| + m)`. It aligns the
     coset: the target becomes `y ∘ σ`, and the representative becomes `1`.
   - The answer is lifted back with the kernel of the restriction, as in `restrictProg`.
   - The restricted hinted instance is `HInstValid`, with labels re-indexed.
   - **Faithfulness on the new string positions:**
     - an element fixing `W` pointwise fixes every label;
     - the subgroup of `P` fixing every label is normal in `P`, and it fixes a proper
       nonempty set;
     - since `Alt(Γ) ≤ P` and `m ≥ 5`, that subgroup is trivial.
   - After the restriction the window contains every string position. This is the
     assumption `hwS` of `case3Prog_canonical`, and `hloc` for `fullGroupK`.
   - The restricted instance has the same `(window size, base)` measure. It is part of the
     same macro-step and is not a recursive child.
2. **Certificates, aggregation and the case decision.**
   - `fullProg` gives `F` (`Denotes … fullGroupK`). Its sub-solver is `plainSub`, on windows
     of at most `n/k` points (`StepSubP`): `StepChild` children without a hint.
   - `caseProg` gives the case and `Φ`.
   - **Separating Case 2a from Case 2b:** decide whether `ψ(F)` is `(|Φ| − 2)`-transitive on
     `Φ`, with `degD_spec`. Prove the classical lemma that a `(k − 2)`-transitive group of
     degree `k` contains `Alt(k)`. This gives `hFalt`.
   - Package `Fmap := fun x => fullGroupK …` with `hloc` and `heq`, from the restriction and
     `fullGroupK_relabel`.
3. **Align with a structure-dependent continuation.**
   - Align's sub-solver hypothesis takes one cost `Cb` for every valid representative. So
     its continuation, `rdBranch` with the aligned structure, gets as `Cb` the maximum over
     the finitely many valid representatives of the branch cost, as `ml_exists_max` does.
   - The children are then reported as `|candidates|` copies of the most expensive branch's
     children.
   - `K` is `ψ⁻¹(Stab(X(x)))` (`c2_g1_spec`), which preserves `X(x)`. This discharges `hD`
     through `rd_orbit_free`.
4. **Children counted by number.** The certificate sub-calls and Case 2a's pullback take
   one uniform cost per call (`StepSubP`, `PbSubP`), and they are numerous. So they are
   reported by count rather than as a `ChildList`:
   - the cost is at most `cnt · C ⌊n/k⌋ none` (certificates) or `cnt · C ⌊n/2⌋ none`
     (Case 2a), with explicit bounds on `cnt`;
   - this needs the hypothesis that the cost `C · none` is monotone in the window size;
   - stage 14j-6 adds the matching potential lemma. The halving of the window, or its
     division by `k`, gives slack of a power of `Q`, which absorbs the count.
5. **The cases.** Each has its run, `AnsOK`, children's predicate and factor:
   - **Case 1:** `case1Prog`, with the continuation of item 3 on the orbit partition, a
     colored `⌊m/2⌋`-partition (`orbitPart_valid`). No orbit is stuck (`rd_ns_part`).
   - **Case 2a:** `case2aProg_canonical`, whose sub-solver is `plainSub` on windows of at
     most `|W|/2` points (`PbSubP`): `StepChild` children without a hint. The factor is
     `|gens G₁| + 1` branches.
   - **Case 2b:** `case2bProg_canonical'`, with the continuation of item 3 on the aligned
     leaf. A partition leaf gives progress when its blocks and its rest have at most
     `3m/4` points. A Johnson leaf goes through `rdProg` with no structure, which is correct
     but may hit the stuck fallback; 14j-4b fixes this.
   - **Case 3:** `case3Prog_canonical`, with the comparisons through `plainSub`
     (`StepSubP`) and the continuation as in Case 2b. Its `none` signal falls back to
     `m3Prog`, the kernel reduction.
6. **The step** `m5StepProg`: the restriction, then the certificates, then the dispatch.
   - Spec: `AnsOK` for the parent, unconditionally.
   - The children: `StepChild` (with a hint, `4m' ≤ 3m`; without, `2n' ≤ n`) or certificate
     children (without a hint, `k · n' ≤ n`).
   - The factor bounds:
     - `k!`-type, from the certificates;
     - the Align candidates;
     - the reduce-and-derive factor.
   - A no-stuck corollary for Cases 1 and 2a, and for Cases 2b and 3 with partition leaves.
7. **Checks** (`GraphIsoChecks/MainM5.lean`). Kernel-checked examples on tiny giant actions,
   at least `m = 5` and preferably `S₅`/`A₅`: the restriction, each case reached, and the
   whole step on one fixture. They reuse the instrumented sub-solver.
8. **Audit and docs.**

### 14.5 Stage 14j-4b: completion criteria (coloured Johnson alignment in Cases 2b and 3)

Stage 14j-4 hands the Johnson leaves of Cases 2b and 3 to `rdProg` with no structure. That is
correct, but it can reach the stuck fallback. This stage aligns the coloured pair `(Q, J)` of
§14.1 item 5 instead, so that `rd_ns_cj` applies. The code is in `GraphIso/Main/`. No approved
statement changes: the new programs are variants that reuse the pieces of stages 14h, 14i and
14j-4.

1. **Johnson leaves stay inside their domain.** Every Johnson leaf of Case 2b's leaf tree
   along `e` (the numbering of `Φ ∖ S`), and of Case 3's outcome on the dominant class `C`, has
   `V₀ ∪ ⋃Λ` inside the numbered set, of size `m'`, with `(m' + 3)/2 < |V₀|`. These facts come
   from `split_or_johnson` at `t = (m' + 3)/2` and the extension along the numbering.
2. **The canonical colouring `Q` on data.** It is an `Array ℕ` on the base indices, and the
   coloured pair is a `CJData`: the leaf's Johnson data with that colouring.
   - **Case 2b:** colour `0` off `Φ`, `1` on `Φ ∖ S`, and `2 + i` at the `i`-th point of the
     tuple `S` of the leaf's choice. Each individualized point is its own class.
   - **Case 3:** colour `0` on the support, `1` on the dominant class `C` of the leaf's good
     list, and `2` on the rest of the fixed points.
   - **The lists:** `x`'s first coloured pair (the first leaf of the first choice, with that
     choice's `Q`), and the coloured Johnson leaves of `y` over all choices.
   - **Canonicity:** if `ψ(g)` carries `Φ(x)` to `Φ(y)` (Case 2b), or the support and
     colourings of `x` to those of `y` (Case 3), it carries `x`'s first coloured pair to one of
     `y`'s coloured pairs. This is proved choice by choice, from:
     - Case 2b: `lk_pairs` and `pairNode_relabel`;
     - Case 3: `c3l_outcome`, `outTree_relabel` and `domCls_relabel`.
   - **Validity:** `JValid` and `IsJohnson` for the leaf's embedding (`CJValid` is `JValid`).
   - **The colour bound `hq` of `rd_ns_cj`:** each colour class outside `V₀` has at most `m/2`
     points. It follows from item 1 and the case conditions: `2|Φ| > m` in Case 2, and
     `2|supp| < m` in Case 3. No further numeric hypothesis is needed.
3. **The variants** `m5Case2bCJProg` and `m5Case3CJProg`.
   - They compute `x`'s first leaf as in 14j-4. A partition leaf continues as in 14j-4.
   - A Johnson leaf goes to Align with `cjohnOps` on `x`'s first coloured pair against `y`'s
     coloured pairs, followed by `rdBranch` with `st = (2, X₀)`.
   - **Specs:**
     - `AnsOK` under the hypotheses of 14j-4's `RunsWithin.m5Case2bProg` and
       `RunsWithin.m5Case3Prog`;
     - the children `StepChild |W| m`;
     - for a Johnson leaf, no stuck orbit (`alignRd_cj_ns`) and the factor
       `|candidates| · max(m, uB!)`.
4. **The step.** A dispatcher and step variant use the new programs. Their specs give:
   - `AnsOK`, unconditionally;
   - children as in 14j-4;
   - a no-stuck corollary covering every case except the partition leaves of Cases 2b and 3,
     whose `4t ≤ 3m` hypothesis stays as in 14j-4.
5. **Checks** (`GraphIsoChecks/MainM5CJ.lean`, `GraphIsoChecks/MainM5CJRoute.lean`).
   - Kernel-checked examples (`decide`) of the colourings, the coloured lists, a transported
     pair found among `y`'s pairs, and `hq` on a Johnson leaf.
   - A staged check of Case 2b's Johnson route on the Clebsch fixture: check the case
     conditions, degrees, routing test, first Johnson leaf, its size threshold and `hq`, and
     a transported pair among `y`'s candidates. The earlier stages may use the data functions
     that their `RunsWithin` specifications prove the programs return; the memoized candidate
     computation must be proved equal to the full candidate model (`ys2bM_eq`).
   - Execute the route's Align suffix with `cjohnOps` and `rdBranch` at `st = (2, X₀)`,
     compare its answer with brute force, and check its recorded children against the stated
     bounds. This suffix may use the 16 distinct candidates from the full list of 3840:
     membership preservation retains `halign` and hence correctness of the answer.
   - **Acceptance amendment, 24 October 2026:** this staged check satisfies item 5. It does
     not establish an end-to-end execution of either case program, or an execution, cost or
     child-summary correspondence with the full candidate list. In particular, the observed
     22 children belong only to the suffix on 16 candidates. The full execution is optional
     follow-up coverage. Audit F1 is closed by this criterion change; the two archived audit
     verdicts remain unchanged.
6. **Audit and docs.**

**Contract repair before 14j-5 (decision, 24 October 2026).** Adopt option 1 of
`14J5-DESIGN-ISSUE.md`: strengthen the affected macro-step specifications in place, keeping
their names. A parallel family of `_g` headline theorems is not required. This is a decision
on the design; the strengthened specifications and their proofs are not yet implemented.

- Restrict each recursive sub-solver predicate to children with a proved input-generator
  bound, in addition to its existing size and measure facts. Keep this representation bound
  explicit rather than hiding it in `HInstValid`. For induction, choose a bound closed under
  every recursive step, including answer groups and changes of degree; a fresh, possibly
  growing bound at each step is insufficient for a single measure-indexed cost `C`.
- Strengthen `ChildList` with `∀ x ∈ ch, 1 ≤ x.1`, prove it at child-creation sites, and
  propagate it through the combinators. Derive `ch.length ≤ c * n` from positivity and
  `sum_le`, so per-call overhead is accounted for. Handle an empty root separately with an
  explicit base-case cost: `pot Q b 0 m = 0` cannot bound a positive execution cost.
- Re-prove the affected specs and record each old/new statement and any changed definitions.
  Check the direction of implication: the bounded sub-solver is a weaker hypothesis, while
  nonempty children are an additional conclusion. Preserve the existing parent-input
  domain, `AnsOK`, progress and executed-cost guarantees. The decision covers these
  strengthenings, not arbitrary changes to the protected targets. Update only the affected
  `lean-loop accept-statement` snapshots once the concrete changes have been checked.
- Prove the generator bounds and backend charges for Schreier–Sims, including `M5Bounds`
  and the outstanding output-generator facts. If input normalization is needed, execute it
  and charge for it; `ssBounds` at `s = N²` cannot be applied to arbitrary generator lists.
  Demonstrate that the repaired contracts discharge the recursive hypothesis before
  extending the full dispatcher. Milestones 15 and 16 remain independent later work.

### 14.6 Stage 14j-5a: completion criteria (the contract repair)

The repair decided above, in place, for the specs of stages 14j-2 to 14j-4b. Stage 14j-5 is
split in three loops:
- **14j-5a**, the contract repair (this section);
- **14j-5b**, the Schreier–Sims discharge of the backend and generator-count hypotheses, and a
  recursion over the base case, the chain rule, M0 and M3 closed by induction with the repaired
  contracts (the demonstration the decision asks for before the full dispatcher);
- **14j-5c**, the full procedure. It was split again when 14j-5b was done (§14.8): **14j-5c**,
  every macro-step at the Schreier–Sims backend with no backend hypothesis left, and
  **14j-5d**, the dispatcher and the recursion.

Each gets its criteria when the previous one is done.

1. **The frame** (`Main/Frame.lean`).
   - `SizeChild sC I J` gains the field `gens_le`: the child's group has at most `sC`
     generators.
   - `ChildList` gains the field `pos : ∀ x ∈ ch, 1 ≤ x.1`. `ChildList.length_le` derives
     `ch.length ≤ c · n`.
   - **Closure** (`SizeChild.closed`): if the parent has at most `nB` string positions, degree
     at most `NB` with `2 nB ≤ NB`, and `sC ≤ sG`, then the child has at most `nB` string
     positions, degree at most `NB` and at most `sG` generators. So one bound `sG`, with
     `NB` and `nB`, is closed under every step whose `sC` is at most `sG`.
2. **The specs.** Every spec whose sub-solver predicate contains `SizeChild` names its bound
   `sC`, chosen from the bounds its proof already has for the children's generator lists. These
   bounds include the sequential reduction's `max s |gs|`, the kernel's generator count, `sIn`
   (`RDBounds.genOut`, `RDBounds.kerGens`, `DOutGens`, `hKs`, `hsR`, `hsK`), `s` (answers and
   `StepSubP`), and a re-based group's generator count.
   - **No new hypothesis on the parent.** The parent-input domain, `AnsOK`, the cost and the
     progress facts are unchanged. Where a bound is not available from the existing hypotheses,
     the spec takes the bound as an expression in the specific data, never as a new constraint.
   - Every `ChildList` conclusion gains `pos`. It is proved where the children are created:
     orbits are nonempty, a hinted window has at least two points (`HintValid.nonconst`), and
     M0's window has at least two points.
   - Internal predicates of the loops (`MlChild` of the block-stabilizer loop, and the like)
     gain the same generator bound where their children are passed to the sub-solver.
   - **Scope amendment (24 October 2026, user decision): `DOutGens` is strengthened.** The
     hinted children of reduce-and-derive's tags `1`, `2` and `4` have the group of a re-based
     `generate` call. Bounding it needs a valid input, and for tag `4` (the Johnson cells) that
     needs `K` to preserve the Johnson structure, which `rdProg` does not assume. So
     `DOutGens sIn r` now bounds the child's group by `sIn` for every tag `1`–`5`, and keeps
     the bound on the reduction's group `R` for tags `3` and `5`. This strengthens the
     `RDOrbit` assumption of reduce-and-derive, M4 and M5 (`hD`, `hD₁`, `hD₂ᵦ`, `hD₃`, and
     `rd_orbit_free`'s and `rd_orbit_cj`'s per-orbit facts). For these statements the old
     form no longer follows by forgetting the new fields; the record (item 3) lists each one.
     The recursive sub-solver predicate stays uniformly bounded (`SizeChild sIn`).
   - **A fresh bound with a satisfiable hypothesis.** M5's Case 2a (`m5Case2aProg`) solves
     each pullback sub-call after restricting it to its window, so the child's group is a
     `generate` output at a degree of at most `|W|/2`. No hypothesis of `m5Case2aProg` bounds
     that output. It takes a fresh bound `sR` with the hypothesis that `generate` returns at
     most `sR` generators at those degrees on valid inputs of at most `s` generators. There are
     finitely many such inputs, so some `sR` satisfies it for every backend; a Lean lemma proves
     this, so the parent domain is unchanged. M5's dispatch, core and step discharge it from
     their existing `Bm` (`BackendBounds` at every degree), with no new hypothesis.
   - **Obligation of stage 14j-5b:** discharge the strengthened `DOutGens` for Schreier–Sims
     at the actual callers. For tag `4`: Johnson preservation (the hypothesis `hK` of
     `rd_orbit_cj`, at that construction boundary), then validity of the re-based generators,
     then the backend's output bound. Tags `1` and `2` likewise from the M1 and M2a models.
     The strengthening itself proves nothing about the backend.
3. **The record** (`lean/docs/contract-repair.md`). For each changed protected target: the old
   and new sub-solver predicate (the bound `sC`), the new conclusion, and confirmation that no
   other hypothesis changed, or, for the statements with `RDOrbit`, the strengthened
   `DOutGens` (item 2's amendment). The changed definitions are `SizeChild`, `ChildList`, the
   loop predicates and `DOutGens`. The argument that the old statement follows, for the
   statements without `RDOrbit`: the old sub-solver hypothesis implies the new one
   (`HSubSolves.mono`, forgetting `gens_le`), and the new conclusion implies the old
   (forgetting `pos`). For those with `RDOrbit` it holds only under the strengthened
   `DOutGens`.
4. **Snapshots.** `lean-loop accept-statement` for each changed target, after checking its
   diff against item 2 and the record. No other protected statement changes.
5. **Checks.** The check modules use the new definitions:
   - the boolean children checks (`listB`, `childrenOK`) also check positive windows and the
     children's generator counts against the step's `sC`;
   - every check module still builds and passes.
6. **Audit and docs.** `status.md`, `theorem-map.md`, and the frame's documentation.

### 14.7 Stage 14j-5b: completion criteria (Schreier–Sims bounds and a closed recursion)

Stage 14j-5a is done (approved in round 1, `02acd0b`). This stage proves two things:
- the generator-count facts that the repaired specs take as hypotheses hold for Schreier–Sims;
- one recursion closes by well-founded induction using the repaired specs as they stand.

That recursion is the "mini procedure": the base case, the chain rule, M0 and M3. Its sub-solver
hypotheses are discharged by the induction hypothesis, with no further assumption.

**Restaging.** §14.6 put every backend hypothesis into this stage. Here only the hypotheses of
the four steps the mini procedure runs are discharged, plus every generator-count fact.
- **Moved to 14j-5c:** the Schreier–Sims charges of M1, M2a, M2b, reduce-and-derive, M4 and M5
  (`M1Charges`, `BlkCharges`, `M2bCharges`, `M5Bounds` and the charge hypotheses on specific
  calls).
- **Why:** each is a bound on a specific call, which is stated where the dispatcher makes that
  call.
- **What stays here:** the strengthened `DOutGens`, which the 24 October decision assigned to
  this stage.

1. **Uniform backend bounds** (`Main/SimsCounts.lean`, a new module downstream of
   reduce-and-derive, so that no existing module changes). The recursion's generator bound `sG`
   exceeds `M²` at degrees `M < NB`, so the bounds are restated at any `s ≥ M²`.
   - `ssBoundsS M s G₀ (h : M * M ≤ s) : BackendBounds ssCtx ssDV M s G₀`.
   - `rd_ss_boundsS n N sIn Lg (h : N * N ≤ sIn)`: `RDBounds` at `sIn`, with explicit charges
     monotone in `sIn`.
   - `ssBounds` and `rd_ss_bounds` are unchanged.
2. **The generator-count facts for Schreier–Sims.** At degree `M`, the backend's `generate`,
   `stabilizer` and `kernel` return at most `M²` generators on valid inputs
   (`generateModel_spec`, `stabModel_spec`, `kernelModel_spec`). Every fact below reduces to that
   bound, once the input is shown valid.
   - **`DOutGens`**, the obligation of §14.6 item 2, for every tag `1`–`5`:
     - **Statements:** `rd_ss_dOutGens_free` (tag `st.1 ≠ 2`) and `rd_ss_dOutGens_cj`
       (`st.1 = 2`). Each gives `DOutGens sIn (deriveModel ssOracle n N (N, gs, ()) O L st)` for
       every `(gs, d, O)` in `RDSet` when `N * N ≤ sIn`.
     - **Tags `1` and `2`:** the child's group is a re-based `generate` output. The re-based
       generators are valid because the base orbit (M1) or the blocks (M2a) are invariant. The
       child's degree is at most `N`.
     - **Tag `4`:** the cells' re-basing, in this order: Johnson preservation (`rd_orbit_cj`'s
       `hK`, restated for each `gs` with `gs ≤ gsK`), then validity of `rebaseGens` on the
       cells, then the output bound at degree `n + |cells| ≤ N`.
     - **Tags `3` and `5`:** `R` and the child are `generate` or `stabilizer` outputs at degree
       at most `N`. For tag `3` they are the block stabilizer and its re-basing onto the block;
       for tag `5`, the pointwise stabilizer of the cells' positions in `K` re-based onto the
       cells.
     - **The cost of the strengthening:** no hypothesis is added beyond those `rd_orbit_cj`
       already takes.
   - **Corollaries:** `rd_orbit_free_ss` and `rd_orbit_cj_ss`, with `rd_orbit_free`'s and
     `rd_orbit_cj`'s conclusions and the `DOutGens` part dropped from `hch`.
   - **The other facts, for Schreier–Sims:**
     - M4's `hKs`: `m4K`'s generator count;
     - M2b's `hsR` and `hsR'`: `generate` below `m2bRg`, and `m2bRb`;
     - M5's `hsK` and `hsKR`: the restriction's kernels;
     - Case 2a's `hgR`;
     - `Bm` with `sm M = M * M`, which is `ssBounds M ⊤`.

     Each is at most `M²` at its degree `M`, so at most `sIn` when `M ≤ N` and `N * N ≤ sIn`.
3. **The mini procedure** (`Main/Mini.lean`).
   - **The body** `miniBody`, a program of the cost language:
     - the base-case test (`fixedTestProg`); if it holds, `fixedStepProg`;
     - otherwise, with a hint, `m3Prog`;
     - otherwise the window's orbits (`winOrbitsProg`): `chainProg` if there are at least two,
       else `m0StepProg`;
     - the sub-solver of every step is `.recur`.

     The program is well formed (`Prog.Wf`).
   - **The entry** `miniEntry`, on a plain instance `(x, y, W, σ • G)` of degree `N` with any
     number of generators:
     - one `generate` on the input generators, charged at its Schreier–Sims cost
       (`genCost N |gs| + 2`);
     - then `.recur` on the hinted instance `(J', N, N, none)`, where `J'` carries the
       normalized group.

     The normalization is part of the executed and charged program, as the 24 October
     decision requires.
   - **The domain**, for bounds `nB` and `NB` with `2 nB ≤ NB`, and `sG = NB * NB`:
     - valid hinted instances with `J.n₀ = n₀`, `J.n ≤ nB`, degree at most `NB`, and at most
       `sG` generators.

     Each step's `sC` is at most `sG`, so `SizeChild.closed` keeps every child in the domain:
     - the chain rule: `max sG |gs|`;
     - M0: a `generate` output at degree `n + k ≤ 2n ≤ NB`;
     - M3: `max sG |Kb|`, with `Kb` a `kernel` output at degree `N`.
   - **The case analysis**, proved from the data:
     - a hinted instance is transitive on its window (`HInstValid.hint`);
     - an instance without a hint that is not fixed pointwise and has one orbit is transitive
       on at least two points (M0's hypotheses);
     - every child predicate gives `MeasLt` (`StepChild.measLt`, `FreeChild.measLt`,
       `ChainChild.measLt`), with the base of a hinted instance at least `1`.
   - **The cost function**, defined explicitly; neither `Classical.choose` nor `noncomputable` is
     used.
     - **The rank:** `rk(p, b) = p · (NB + 2) + b`, where `b` is the measure's base. Every base
       in the domain is at most `NB + 1`, so `MeasLt` lowers the rank.
     - **The bound:** `Cb 0 = Wm` and `Cb (r + 1) = cm · nB · (1 + Cb r) + Wm`. Here `Wm` bounds
       the dispatch and every step's work on the domain: the explicit Schreier–Sims charges
       at `(NB, nB, sG)`, by monotonicity of the work functions. `cm = NB!` bounds every
       branching factor: the chain rule and M0 have factor `1`, and M3's
       `|reps| ≤ (N − n)! ≤ NB!`.
     - Monotonicity of the work functions (`m0StepCost`, `kerRedCost`, `chainCost`,
       `fixedTestCost`, `fixedStepCost`) in every size argument, proved where each bound is
       used (`kerRedCost` is antitone in `n`, through `baseWinCost`).
   - **Correctness and cost by induction** (`mini_spec`). For every `J` in the domain:
     - `RunsWithin ssCtx miniBody (miniBody J) ans (Cb (rk (hmeasure J)))`;
     - `J.inst.OK ssDV ans`;
     - the answer has at most `sG` generators.

     The proof is strong induction on the rank. At each step the sub-solver hypothesis is
     `HSubSolves` for `.recur`, with `C x.1 x.2 = 1 + Cb (rk x)`. It comes from the induction
     hypothesis, through `RunsWithin.recur`, `SizeChild.closed` and `MeasLt`. The four specs
     are used as stated: `RunsWithin.fixedStepProg`, `RunsWithin.chainProg`,
     `RunsWithin.m0StepProg`, `RunsWithin.m3Prog`.
   - **The headline theorem** (`miniSolve_ss`, a new protected target). For every valid plain
     instance, with no hypothesis, `miniEntry` returns a correct answer at cost at most
     `genCost N |gs| + 2 + c₀ + 1 + Cb (rk …)`, where `nB = N`, `NB = 2N` and `c₀` is the
     entry's local work. That includes an empty window, by the base case and with its own
     constant.
   - **What it is.** An unconditional correct solver whose cost is exponential in the rank: M3
     branches over up to `NB!` cosets. It shows that the repaired contracts close. It is not
     the quasipolynomial bound, which is stage 14j-6's.
4. **Checks** (`GraphIsoChecks/MainMini.lean`). `miniEntry` runs on small fixtures by kernel
   `decide`, and the answers are compared with brute force. The fixtures reach:
   - the empty window;
   - a fixed window;
   - the chain rule;
   - M0 followed by M3 and its children;
   - both an isomorphic pair and a non-isomorphic pair.
5. **Audit and docs.**
   - Every new declaration is in the `AxiomAudit` closure.
   - `status.md` and `theorem-map.md` are updated.
   - `miniSolve_ss` and `mini_spec` are added to the loop's targets.

### 14.8 Stage 14j-5c: completion criteria (the Schreier–Sims steps)

Stage 14j-5b is done (approved in round 1, `f54d480`). The full procedure of §14.6 is split in
two loops:
- **14j-5c** (this section): every macro-step the dispatcher uses, at the Schreier–Sims
  backend, with no backend hypothesis left;
- **14j-5d**: the dispatcher and the recursion, closed by induction as in §14.7 item 3.

**Why the split.** The hypotheses that §14.7 moved here are bounds on specific backend calls:
`M1Charges`, `BlkCharges`, `M2bCharges`, `M4Charges`, `M5Bounds`, the charges inside
`RDOrbit`, and the charge hypotheses of the M5 cases. Discharging them is work on each step and
does not depend on the dispatcher. M5 alone takes about forty of them.

1. **The Schreier–Sims steps** (new modules downstream of the steps; no existing module
   changes, except as item 4 says). For each of M1, M2a, M2b, M4 and M5 (with coloured Johnson
   alignment, `m5StepCJProg`), a theorem at `ssCtx` whose hypotheses are only:
   - the validity of the hinted instance (`HInstValid ssDV`);
   - the step's case conditions, as the existing spec states them, plus the conditions item 3
     names;
   - numeric conditions on the parameters: `N * N ≤ sIn`, the bound `Lg` on `generate`'s
     input, M5's `k`, the union-cell bound `uB`. Each is satisfiable by an explicit choice,
     shown by a lemma;
   - the sub-solver hypothesis `HSubSolves` with the existing spec's predicate, and the
     monotonicity of its cost where the spec asks for it (M5's `hCmono`).

   No charge, generator-count, `BackendBounds`, `RDBounds` or `RDOrbit` hypothesis remains.
   - **The conclusion** is the existing spec's: the answer, the children with their predicate
     and factor, the generator bound, and M5's counted calls.
   - **The work** is an explicit function of the instance's sizes: the degree, the string
     positions, the window, the labels, `sIn`, `Lg`, `s`, `k` and `uB`. It is monotone in
     each, and the monotonicity is proved.
   - Data-dependent quantities in the existing costs, such as the lengths of model outputs, are
     bounded by functions of those sizes.
   - M4 also gets the variant without stuck orbits (`m4StepProg_ns`), with the same charge
     lemmas.
2. **The charges**, as lemmas the no-stuck variants can reuse.
   - **M1 and M2a:** the `orbits`, `generate` and `lift` charges of `m1StepProg` and
     `m2aStepProg`.
   - **M2b:** `M2bCharges`, and the hypotheses `hBlift`, `hBgen`, `hBo` and `hBgen₂`. `hsR`
     and `hsR'` come from 14j-5b.
   - **Reduce-and-derive:** `M1Charges` and `BlkCharges` on every orbit in `RDSet`, the tag-4
     charges of `rd_orbit_cj`, and an explicit `Bd`. With them, `RDOrbit` holds for every
     orbit, through `rd_orbit_free_ss` and `rd_orbit_cj_ss` of 14j-5b.
   - **M4:** `BackendBounds` (`ssBoundsS`), `M4Charges`, `RDBounds` (`rd_ss_boundsS`), `hKs`
     (14j-5b) and `hD`.
   - **M5:**
     - `M5Bounds` with explicit fields;
     - the charge hypotheses of Cases 1, 2a, 2b and 3 and of the Johnson routes;
     - the restriction's charges;
     - `B`, `Bk'` and `Bm` (`ssBoundsS`, `ssBm`);
     - every case's per-orbit `RDOrbit`.
   - **Route.** Every Schreier–Sims charge is an explicit function of the sizes of a call's
     input and, for some operations, of its output. Each charge is bounded by that function at
     bounded sizes:
     - input lengths come from the program's structure (for example, `extendGens` keeps the
       length);
     - lengths of earlier outputs come from the backend specs on valid inputs
       (`generateModel_spec`, `stabModel_spec` and `kernelModel_spec`: at most `M²` at degree
       `M`);
     - validity of those inputs comes from the existing run lemmas. Where it is established
       only inside a spec, it comes from the degree-aware invariant `ssBnd` of 14j-5b.
3. **Facts established inside a spec.** Some hypotheses need facts that only a spec's proof
   establishes. For example, M4's `hD` at a Johnson leaf needs `m4_cj_facts`, whose premises
   come from `m4_core`'s continuation. Those corollaries are proved through the core lemma, not
   the outer statement.
   - `m4_cj_facts` needs `2j ≤ m`, so the general M4 corollary assumes it too.
   - The dispatcher (14j-5d) tests such numeric conditions and falls back to M3 when they fail.
     Under the interfaces they hold for `m > ℓ` (§14.3, `m4_numeric`).
4. **Case 2b's Johnson route** (the one change to existing modules).
   - **The defect.** `RunsWithin.m5Case2bCJProg` uses its Johnson-route hypotheses `hBg1'`,
     `hD'` and `hu` only when `x`'s first leaf is a Johnson leaf (`c2bJD`, that is
     `X₀.1 = 2`), but it states them for every first leaf. For a partition leaf `X₀`, `hD'`
     asks for `RDOrbit` at the Johnson state `(2, cjFirst2bD … X₀)`, whose Johnson part is
     `X₀.2.2`, unused for such a leaf. No existing lemma gives that: `deriveProg_cj` needs
     `IsJohnson`.
   - **Where else.** `m5DispatchCJ`, `m5CoreCJProg` and `m5StepCJProg`, and the no-stuck
     versions `m5DispatchCJ_ns` and `m5CoreCJProg_ns`, carry the same hypotheses (`hBg1J₂`,
     `hDJ₂`, `hu₂`). Case 3's Johnson-route hypotheses already have the premise `X₀.1 = 2`.
   - **The repair.** New theorems state these hypotheses with the premise `X₀.1 = 2`, and the
     existing proofs move into them. Each existing statement is then derived from its new
     version: its hypotheses imply the new ones by ignoring the premise.
   - **Unchanged:** no protected statement changes, there is no `accept-statement`, and the
     gate reports `0` changed. The new theorems are added to the loop's targets.
   - **Further cases.** Any other hypothesis found to cover a route that its case does not take
     is handled the same way and listed in `status.md`.
5. **Checks** (a new check module), compared with executed runs under the verified oracle:
   - M1, M2a and M2b on 14j-2's fixtures, and M4 on 14j-3's `AGL(1,5)` fixture where the
     kernel allows, kernel-checked (`decide +kernel`, or `execRuns` pieces). In each run, the
     step's own cost under `ssB` is at most the corollary's explicit work. Every backend call of
     the step is within its charge lemma's bound.
   - M5 on 14j-4's `S₄` and `S₅` runs: by `#eval`, each backend call is within the bound of its
     charge lemma. These fixtures are outside M5's numeric conditions (`5 ≤ k`, `12 ≤ m`), so
     the step corollary itself is not checked on them.
6. **Not in this stage:**
   - the dispatcher and the recursion (14j-5d);
   - the step-level M5 variant without stuck orbits, which 14j-6 needs along with item 2's
     charges;
   - the cost bound (14j-6).
7. **Audit and docs.**
   - Every new declaration is in the `AxiomAudit` closure.
   - `status.md` and `theorem-map.md` are updated.
   - The step corollaries and item 4's new theorems are added to the loop's targets.

### 14.9 Stage 14j-5d: completion criteria (the dispatcher and the recursion)

Stage 14j-5c is done (approved in round 2, `381076a`). This stage builds the full procedure and
closes it by well-founded induction, as §14.7 item 3 did for the mini procedure.
- **Correctness** is unconditional.
- **The cost** is explicit. It is exponential in the rank, as `miniCost` is. The
  quasipolynomial bound is stage 14j-6's.

1. **The thresholds.** The body reads `k` and `ℓ` from a local program `thr` of `n₀`, which
   makes no backend call, so their computation is executed and charged.
   - The theorems hold for every `thr` meeting `ThrSpec thr kf ℓf cT`: on every `n₀` it returns
     `(kf n₀, ℓf n₀)` at a cost of at most `cT n₀`.
   - `thrConst k ℓ`, which returns two literals, meets it.
   - Stage 14j-6 supplies the program for `k(n₀)` and `ℓ(n₀)` (§15).
2. **The body** `mainBody thr` (`Main/Full.lean`), a program of the cost language. Every step's
   sub-solver is `.recur`, and the program is well formed (`Prog.Wf`).
   - **As in the mini procedure:**
     - the base-case test, then `fixedStepProg` if it holds;
     - without a hint, the window's orbits: `chainProg` if there are at least two, else
       `m0StepProg`.
   - **With a hint `L`**, on the base `m = N − n`:
     - **The base orbits** (`orbits` on `baseWin`): more than one gives M1 (`m1StepProg`).
     - **The maximal blocks** of the base (`baseBlocksProg`, `blkOKProg`, as in
       reduce-and-derive's block step), if they are proper:
       - some label not equidistributed (`neqProg`): M2a (`m2aStepProg`);
       - otherwise M2b (`m2bStepProg`) on these blocks.
     - **Otherwise**, with `(k, ℓ) = thr n₀`:
       - `m ≤ ℓ` gives M3 (`m3Prog`);
       - the giant test (`giantProg`) true, with M5's numeric conditions `5 ≤ k`,
         `k + 2 ≤ m`, `2k ≤ m` and `12 ≤ m`, gives M5 (`m5StepCJProg`, with a literal
         state `st`, `st.1 ≠ 2`);
       - the giant test false, with M4's conditions `4 + j ≤ m` and `2j ≤ m` (`j = dg − 1`,
         from `degreeProg`), gives M4 (`m4StepProg`);
       - in every other case, M3. This is the fallback of §14.8 item 3.
3. **The case analysis**, proved from the tests' run lemmas at `ssCtx`, with no hypothesis:
   - **M1:** `¬ IsTransOn` on the base, from the orbit count;
   - **M2a:** `htrB`, `hok` and `hne`;
   - **M2b:** `hbs`, `hGb`, `hΨ`, `hcard`, `htrB`, and a window point `u₀` with `heq`. They
     come from `blkOKD`, `neqD = false` and the label invariant (`HintValid.nonconst`, so the
     window is not empty);
   - **M4:** `htr` and `hng` (from `giantModel_iff` and `degreeModel_spec`: not giant means a
     degree below `m − 2`), with `hk4` and `2j ≤ m` from the tests;
   - **M5:** `haltP` (`giantModel_iff`) and the tested numeric conditions;
   - **the base case, the chain rule, M0 and M3:** as in §14.7 item 3.
4. **The parameters**, explicit functions of the domain's bounds (item 5).
   - Every step corollary of 14j-5c is applied with:
     - `sIn = sG`;
     - an explicit `Lg`, at least each step's `Lg` condition (`hLg`, `hLgJ`, `hLY`), by the
       monotonicity of those bounds in `m ≤ NB` and `k ≤ m`;
     - `uB = NB`.
   - Each condition is a lemma.
5. **The domain**, as `MiniDom`: valid hinted instances with `J.n₀ = n₀`, `J.n ≤ nB`, degree
   at most `NB` (`2 nB ≤ NB`) and at most `sG = NB * NB` generators.
   - Every step's `sC` is at most `sG`. This covers M1's and M2a's re-based groups (at most
     the degree squared), M2b, M4 and M5 (`sIn`, and M5's `max sIn (supTo sm (n / 2))` with
     `sm M = M * M`). So `SizeChild.closed` keeps every child in the domain.
6. **The step** (`main_step`), the form stage 14j-6 reuses.
   - **Hypotheses:** for every `J` in the domain, and every cost function `C` that is
     monotone in the window for instances without a hint (M5's `hCmono`), `HSubSolves` for
     `.recur` with the domain as predicate and cost `C`.
   - **Conclusion:** the conclusion of the case the dispatcher takes. That case, `mainCase J`,
     is computed from the data. The conclusion includes the answer, the children with their
     predicate and factor, M5's counted calls, and the work, which is the dispatch's tests
     plus that step's explicit work function from 14j-5c.
7. **The recursion** (`main_spec`), by strong induction on the rank, as `mini_spec`.
   - The rank `rk(p, b) = p · (NB + 2) + b` and `MeasLt` are as in §14.7.
   - The bound: `Cb 0 = Wm` and `Cb (r + 1) = cm · nB · (1 + Cb r) + Wm`, where:
     - `Wm` bounds the dispatch and every step's work on the domain;
     - `cm` bounds every multiplicity: M3's `NB!`, M2b's `NB`, M4's
       `m4R NB NB · NB!`, and M5's factors and counted calls.

     Both are explicit, by the monotonicity proved in 14j-5c.
   - For every `J` in the domain: `RunsWithin ssCtx (mainBody thr) (mainBody thr J) ans
     (Cb (rk …))`, `J.inst.OK ssDV ans`, and the answer has at most `sG` generators.
8. **The headline** (`mainSolve_ss`, a new protected target). For every `thr` with `ThrSpec`,
   and every valid plain instance, with no other hypothesis, `mainEntry thr` returns a correct
   answer at cost at most `genCost N |gs| + 2 + c₀ + Cb (rk …)`, where `c₀` counts the entry's
   local steps, with `nB = N` and `NB = 2N`.
   - The corollary at `thrConst` has no hypothesis at all.
9. **Checks** (`GraphIsoChecks/MainFull.lean`). `mainEntry` runs on small fixtures by kernel
   `decide` (or `execRuns` pieces), and the answers are compared with brute force.
   - The fixtures reach the steps that small sizes allow: M1, M2a, M2b and M3, and M4 on
     `AGL(1,5)` with `ℓ < 5` if the kernel allows (by `#eval` otherwise).
   - Path counts show which steps ran.
   - M5 needs `12 ≤ m` and is not reached. Its branch condition is checked on the `S₄` data.
10. **Not in this stage** (for 14j-6):
    - the quasipolynomial bound and the threshold programs;
    - the step-level M5 variant without stuck orbits;
    - sharper charges. The factorial factors (`(N − n)!` in `Lg` and in M4's and M3's
      multiplicities) bound the Johnson fallback by `m!` rather than `(ts)!`. Stage 14j-6
      needs the `(ts)!` bound of §2.4.
11. **Audit and docs.**
    - Every new declaration is in the `AxiomAudit` closure.
    - `status.md` and `theorem-map.md` are updated.
    - `mainSolve_ss`, `main_spec` and `main_step` are added to the loop's targets.

Stage 14j-6 gets its criteria when stage 14j-5d is done: `cost ≤ pot` under
`AltQuotientIso` and `TransitivityBound` with the thresholds `k(n₀)` and `ℓ(n₀)`, the closed
bound `exp(O((log n₀)⁸))`, and the string- and graph-isomorphism entries.

### 14.10 Stage 14j-6a: completion criteria (the label invariant)

Stage 14j-5d is done (approved in round 2, `dce8984`). Stage 14j-6 is split in three loops:
- **14j-6a**, the label invariant (this section);
- **14j-6b**, the sharp charges. Every case's factor and work become explicit functions of
  `n₀`, `n`, `m`, the label length `t`, `k` and `ℓ`, with no factorial of `m` when `m > ℓ`.
  This covers:
  - the union labels bounded by `t · s` (so `uB = t · λ(m)` instead of `m`);
  - M5's step-level variant without stuck orbits. Its partition leaves need the bound
    `(|Φ ∖ S| + 3)/2` from `leafTree`, and Case 3's structures and the absence of twins come
    under `Thresholds`;
  - Case 2b's count at the actual `j`;
  - under `TransitivityBound`, `j ≤ T(m)`, and no M3 fallback for `m > ℓ`.

  It is split again in two loops, 14j-6b-1 and 14j-6b-2 (§14.11);
- **14j-6c**, the potential and the final theorems:
  - the threshold program for `k(n₀)` and `ℓ(n₀)`;
  - `Q(n₀)` with every case's work at most `Q` and factor at most `Q²`;
  - `cost ≤ potO` by induction over the domain with the label invariant;
  - the closed bound `exp(O((log n₀)⁸))`;
  - the string- and graph-isomorphism entries.

Each gets its criteria when the previous one is done.

**Why the invariant is needed.** The Johnson fallback of reduce-and-derive branches over at most
`u!` cosets, where `u` counts the union cells at a point (`rd_cj_reps5`). That count is at most
`t · s`, for labels of length `t` and Johnson parameter `s ≤ λ(m)` (`s_le_lam`). The potential
needs `(t s)! ≤ Q` at every reachable instance with `m > ℓ`. So `t` must be polylogarithmic in
every instance the recursion reaches, not just at the parent. This is §5 item 8's invariant:
`t (λ(m) + 1)² ≤ 2 (λ(n₀) + 1)²` while `m > ℓ₀`. The step specs see their children only through
`SizeChild` (the sub-solver's predicate), so the invariant goes there.

**The design: in place, a semantic contract amendment** (user decision, 25 October 2026).
- **`SizeChild` gains one field, `lab : LabInv I → LabInv J`**, as `gens_le` did in 14j-5a.
- **`DOutcome`'s hinted constructors gain label facts.** Reduce-and-derive sees its derived
  children only through `RDOrbit`'s `DOutcome`, and the generic specs allow any structure `st`.
  So `SizeChild` alone cannot carry the invariant.
  - `inter`, `blockLab`, `blockStab`: `labLen L' ≤ labLen L`.
  - `johnUnion`: a witness `s` with `labLen L' ≤ labLen L · s`, `C(m', s) ≤ m`, `2 ≤ s` and
    `2s ≤ m'`.
- **Not every protected statement becomes stronger.**
  - Where `SizeChild` occurs only in a sub-solver predicate, the statement is stronger: a
    stronger predicate weakens the hypothesis.
  - The specs with `RDOrbit` hypotheses (reduce-and-derive, M4, M5 and their `_jp`/`_ns`
    forms) assume more of the derived hints. They **change meaning** although their text is
    unchanged, and their old forms do not follow by forgetting fields. This matches the
    `DOutGens` amendment of 14j-5a.
- **Discharged within this stage.** The facts are proved through:
  - `deriveProg_free` and `deriveProg_cj`;
  - the orbit constructors (`rd_orbit_free`, `rd_orbit_cj` and their Schreier–Sims forms);
  - the concrete M4 and M5 callers.

  At the Schreier–Sims level and the headlines, no `RDOrbit` hypothesis remains. The parent
  domains, correctness, progress and executed-cost guarantees are unchanged there.
- **Unprotected helpers get explicit premises.** `m1ContProg` and `blocksProg` used to allow
  labels unrelated to the parent's `L`. They take length-comparison premises, discharged by
  their callers.
- **The alternative,** parallel generic variants of about 45 specs with the old ones as
  corollaries, was declined.
- **The record** (item 5) lists the affected hypotheses and their discharge paths. Unchanged
  statement hashes alone do not establish semantic preservation.

1. **The invariant** (`Main/Frame.lean`).
   - `labLen L`: the maximum length of the lists of `L`, or `0`.
   - `ell0 n₀ = max 2¹¹ ((λ(n₀) + 1)³)`. It is fixed, so the invariant does not depend on
     the thresholds; stage 14j-6c chooses `ℓ(n₀) ≥ ell0 n₀`.
   - `LabInv J`:
     - `J.n ≤ J.n₀`;
     - for a hint `L` on a base of `m = J.inst.degree − J.n` points, `m ≤ J.n₀`;
     - if moreover `ell0 J.n₀ < m`, then `labLen L · (λ(m) + 1)² ≤ 2 (λ(J.n₀) + 1)²`.
   - Instances without a hint satisfy the hint parts trivially.
   - `mainEntry`'s instance satisfies `LabInv` (`n = n₀`, no hint).
2. **The frame.** `SizeChild sC I J` gains `lab : LabInv I → LabInv J`.
   - `SizeChild.closed` and `SizeChild.mono` keep their statements.
   - `SizeChild.lab_closed`: a parent with `LabInv` has children with `LabInv`.
3. **The label lemmas** (`Toolkit/Labels.lean` or a new `Main/LabLen.lean`), on data. Each is
   the length bound of one construction of a child's labels:
   - `mapLabels` with a shortening map (`filter`, `filterMap`): `labLen` does not grow;
   - restriction to positions (M5's `rbLabelsProg`, the dispatcher's `normLabProg`): `labLen`
     does not grow;
   - block labels (M2a, M2b, `deriveProg`'s colored partitions, tag `3`'s M1 child): `labLen`
     does not grow, and the base does not grow;
   - M0's labels: `labLen ≤ 1`, on a base of at most `n` points;
   - Johnson union labels (`labJUD`, `jUnionData`):
     - length at most `|l| · s` when every cell list has length at most `s`;
     - from a valid coloured Johnson structure, `labLen` at most `t · s` on a base of
       `m'` cells, with `C(m', s) ≤ m`, `2 ≤ s` and `2s ≤ m'`.
   - The invariant through a Johnson step is `johnson_step_label` (`Potential.lean`): with
     `m' > ell0 n₀`, it gives `t s (λ(m') + 1)² ≤ t (λ(m) + 1)²`, and `m ≥ C(m', s) > m'`
     places the parent in the invariant's range.
   - **The derived hints** (`Derive.lean`): `deriveProg_free` and `deriveProg_cj` prove
     `DOutcome`'s new label facts. For tag `4` the witness is the structure's Johnson
     parameter, with `C(nc, s) ≤ m` from `IsJohnson.surj`.
4. **The children.** Every step proves `lab` where it builds a child.
   - **Without a hint:** the chain rule, tag `0`, the certificates' sub-calls, Case 2a's
     pullbacks, tag `5`'s orbits. Only `n ≤ n₀` is needed (from `n_le`).
   - **Hinted:**
     - M0;
     - M1, M2a, M2b and the block-stabilizer loop;
     - M3 and the kernel reduction (tag `6`), with the same labels;
     - `viaChildProg` and `transferProg`;
     - reduce-and-derive's tags `1`–`4`;
     - M5's restriction to the window.
   - Each uses one lemma of item 3 and the base bound of its `StepChild` or `FreeChild`.
   - Internal predicates (`MlChild` and the like) carry the field where their children are
     passed on.
5. **The record** (`lean/docs/contract-repair.md`, a new section "The label invariant of stage
   14j-6a"):
   - the changed definitions: `SizeChild`, and `DOutcome`'s `inter`, `blockLab`, `blockStab`,
     `johnUnion`;
   - every protected statement whose type mentions `SizeChild`, `MlChild`, `RDOrbit` or
     `DOutcome`, with the polarity of each:
     - stronger: `SizeChild` only in a sub-solver predicate, or `DOutcome` as a conclusion;
     - changed meaning: `RDOrbit` hypotheses;
   - the discharge path of the strengthened hypotheses down to the Schreier–Sims level;
   - the unprotected helpers with new premises and their discharges.
6. **The step with the invariant** (`Main/FullStep.lean`). `main_step_lab` (a new target) is
   `main_step` with the sub-solver hypothesis only for the domain's instances with `LabInv`,
   for a parent with `LabInv`. It is the form stage 14j-6c's induction uses. `main_step`,
   `main_spec` and the headlines keep their statements.
7. **Checks** (`GraphIsoChecks/`):
   - the check modules build with the new field;
   - kernel checks of `labLen` on M0's labels and on a Johnson union of a small fixture, against
     the bound of item 3;
   - a negative control: an instance with long labels on a base above `ell0 n₀` fails
     `LabInv`.
8. **Audit and docs.**
   - Every new declaration is in the `AxiomAudit` closure.
   - `status.md` and `theorem-map.md` are updated.
   - `main_step_lab` is added to the loop's targets.

### 14.11 Stage 14j-6b-1: completion criteria (the steps without stuck orbits)

Stage 14j-6a is done (approved in round 1, `a6a29f8`). Stage 14j-6b is split in two loops:
- **14j-6b-1**, the steps without stuck orbits (this section). M4 and M5 at the Schreier–Sims
  backend, with factors and work free of `m!`, and every hypothesis of the no-stuck forms
  discharged except numeric ones and the interfaces;
- **14j-6b-2**, the sharp dispatcher:
  - M4's depth below `T(m)` (`m4_deg_le_T`);
  - for `m > ℓ`, no M3 fallback: the dispatcher takes M4 or M5;
  - the sharp case functions, explicit in `n₀`, `n`, `m`, `t`, `k`, `ℓ` and the sizes;
  - the step `main_step_sharp`, with these bounds.

  Its criteria are in §14.12.

**Why.** The corollaries of stage 14j-5c (`m4StepProg_ss`, `m5StepCJProg_ss`) have `m!` in
their factors, for two reasons:
- they charge reduce-and-derive's stuck orbits (the kernel reduction, with `m!` cosets);
- they bound the Johnson fallback's union cells by `m` (`uB ≥ m`).

The forms without stuck orbits exist below the step: `m4StepProg_ns` and its corollary
`m4StepProg_ns_ss`, and `m5CoreCJProg_ns`. Their remaining hypotheses are:
- M5's partition leaves: `hpart₂ᵦ` (Case 2b) and `hpart₃` (Case 3), each a colored
  `t`-partition with `4t ≤ 3m`;
- no twins in Case 3 (`hnt₃`);
- the union cells: `uB ≥ m` in `m4StepProg_ns_ss`, and `hu₂`, `hu₃` in M5.

This stage discharges them, and builds M5's step without stuck orbits.

1. **Partition leaves with their size** (`Case2b/`, `Case3/`, `Main/`).
   - **On the models.** `leafTree_spec` and `case3Tree_spec` give `ValidLeaf`, whose
     partitions have an unstated `t`. New forms give every partition leaf as a colored
     `t`-partition of `Γ` with `t ≤ max ((m' + 3) / 2) (|Γ| − m')`, for `m'` numbered points.
     - The bound is the maximum of Split-or-Johnson's `(m' + 3)/2`, the components' `m'/2`
       (`isColPart_comp`) and the complement block of the extension (`extPart_valid`).
     - It is carried by a refinement of `ValidLeaf` (e.g. `ValidLeafLe b`). `ValidLeaf` and
       the existing statements are unchanged.
   - **On data.**
     - Case 2b's first leaf (`m5Leaf2b`), when it is not a Johnson leaf, decodes to a colored
       `t`-partition with `t ≤ max ((|Φ| − j + 3) / 2) (m − |Φ| + j)`, where `j = degD − 1`
       (`firstLeafD_valid`'s route).
     - Case 3's first structure (`firstStructD`) likewise, with the numbered class of the
       Case 3 tree.
   - **The numerics.**
     - Case 2b (`|Φ| > m/2`): `4t ≤ 3m` follows from `m ≥ 12` and a numeric condition on `j`,
       such as `4j ≤ m`.
     - Case 3 (`2|S| < m`; the class has more than `tOf |Γ ∖ S|` points): `4t ≤ 3m` follows
       from these bounds alone.

     These discharge `hpart₂ᵦ` and `hpart₃`.
2. **Case 2b's depth under `TransitivityBound T`.** In Case 2b (`degD < |Φ| − 2`) the action
   on `Φ` does not contain `Alt(Φ)`. The computed degree is a degree of transitivity, so
   `degD ≤ T(|Φ|)` (as `m4_deg_le_T` for M4). With a depth bound `jB` such that
   `T(m') ≤ jB + 1` for every `m' ≤ m`:
   - Case 2b's count is `c2bR` at depth at most `jB`: `|Φ|^{jB} · m² (Z + 1)`, not
     `c2bRU m = (m + 1)^m …`;
   - item 1's condition on `j` follows from a numeric condition on `jB`.
3. **No twins** (`hnt₃`) from `m5_no_twins` under `Thresholds K |W| k`. Its `k ≤ tOf |Vx|`
   follows from Case 3's `2|S| < m` and a numeric condition such as `8k ≤ m`.
4. **Union cells bounded by the labels.** For a valid coloured Johnson structure with parameter
   `s` on a base of `m` points:
   - every Johnson union label has at most `labLen L · s` cells (`labLen_labJUD_le`);
   - `s ≤ λ(m)` (`s_le_lam`, from `C(m', s) ≤ m` and `2s ≤ m'`).

   So `uB = labLen L · λ(m)` meets `hu`, `hu₂` and `hu₃`, with no `uB ≥ m`. At M5 the
   restricted instance's labels are no longer (`labLen_rbLabels_le`).
5. **The steps** (new targets).
   - `RunsWithin.m4StepProg_nsL_ss`: `m4StepProg_ns_ss` with `uB = labLen L · λ(m)` and no
     `huB`.
   - `RunsWithin.m5StepCJProg_ns`: the restriction composed with `m5CoreCJProg_ns`, as
     `m5StepCJProg` composes `m5CoreCJProg`, with factor `m5CFnsCJ` and work
     `m5CoreWorkNsCJ`.
   - `RunsWithin.m5StepCJProg_ns_ss`: the same at `ssCtx`, with every backend hypothesis
     proved by `m5StepCJProg_ss`'s charge lemmas, and `uB = labLen L · λ(m)`. The remaining
     hypotheses:
     - validity, the giant and `k`'s conditions;
     - `TransitivityBound T` with the depth bound `jB` (item 2);
     - `Thresholds K |W| k` (item 3);
     - the numeric conditions of items 1–3;
     - `NP² ≤ sIn`, the sub-solver and the monotonicity of its cost;
     - `Lg` large enough: `max(m, uB!)`, Case 2b's count at `jB`, and Case 3's `c3R`.
6. **The work and the factor, explicitly.**
   - `m5WorkNsSS`: the monotone envelope of `m5CoreWorkNsCJ`, as `m5WorkSS` is of
     `m5CoreWorkCJ`. It has no kernel reduction, and Case 2b's depth is at most `jB`.
   - A named bound on `m5CFnsCJ` in `m`, `k`, `uB` and `jB` (e.g. `m5FBns`), and the parameter
     lemmas (`m5ns_params`, an `ssLgM5Ns`) as `m5_params` and `ssLgM5`.
   - **No `m!`.** The factors, `Lg` and the work of item 5 contain no factorial of `m`. They
     contain only `uB!`, `k!` and powers `m^{jB}`, `m^k`.
7. **Checks** (`GraphIsoChecks/`), kernel `decide` on small data:
   - the partition bound of item 1 on a fixture (a partition leaf extended by `extPart`);
   - the union bound of item 4 (14j-6a's `cj12` fixture);
   - `m5FBns` and `ssLgM5Ns` below `m!` at small parameters, where `m5FB` is not (a negative
     control).
8. **Audit and docs.**
   - Every new declaration is in the `AxiomAudit` closure.
   - `status.md` and `theorem-map.md` are updated.
   - The three steps of item 5 are added to the loop's targets.
   - No protected statement changes.

### 14.12 Stage 14j-6b-2: completion criteria (the sharp dispatcher)

Stage 14j-6b-1 is done (approved in round 1, `457047b`). It built M4's and M5's steps without stuck
orbits at the Schreier–Sims backend (`m4StepProg_nsL_ss`, `m5StepCJProg_ns_ss`), with factors and
work free of `m!`. This stage puts them in the full procedure.

**Why.** `main_step_lab` charges M4 and M5 through the corollaries with stuck orbits
(`main_m4`, `main_m5`). So `caseF` has `m!` for M4 and M5, and the dispatcher may still fall back
to M3, with `m!` cosets, at any base size. Stage 14j-6c's potential needs every factor at most
`Q²` when `m > ℓ`.

**The numeric hypotheses.** These are on the thresholds `k = kf n₀` and `ℓ = ℓf n₀`, and on the
interfaces' functions `T` and `K`. They are stated as hypotheses here and met by stage 14j-6c's
threshold program:
- `Thresholds K n₀ k` (milestone 12), and `TransitivityBound T`;
- `4k ≤ ℓ` and `12 ≤ ℓ`;
- `TBelow T ℓ := ∀ m, ℓ < m → 4 · supTo T m + 6 ≤ m`. Here `supTo T m` is `T`'s maximum over
  `[0, m]`, which serves as Case 2b's depth bound `jB`.

The procedure and its programs do not change.

1. **No M3 above `ℓ`.** Under the numeric hypotheses, the dispatcher takes M3 only when
   `m ≤ ℓ` (`mainCase_m3_le`). For `m > ℓ`:
   - A giant meets M5's test `m5OkD`, since `5 ≤ k`, `2k ≤ m` and `12 ≤ m`.
   - A non-giant has `m4Deg ≤ T(m)` (`m4_deg_le_T`, with `¬ Alt ≤ range` from
     `giantModel_iff`). So it meets M4's test `m4OkD`, and `2j + 6 ≤ m` (`mainCase_m4_sharp`).
2. **M4 in the procedure without stuck orbits** (`main_m4_sharp`):
   - It uses `m4StepProg_nsL_ss` at `sIn = NB²`, with the numeric conditions from `m4_numeric`.
   - `Lg = ssLgM4Ns m j (t λ(m)) NB²`, where `t = labLen L`.
   - The work is `m4WorkNsLSS` and the factor is `m4R m j · max m (t λ(m))!`.
3. **M5 in the procedure without stuck orbits** (`main_m5_sharp`):
   - It uses `m5StepCJProg_ns_ss`, with `jB = supTo T m`, `uB = t λ(m)` and
     `Lg = ssLgM5Ns m k uB jB NB²`.
   - `Thresholds K p k` for the window `p` follows from `Thresholds K n₀ k`, since `p ≤ n ≤ n₀`
     (`LabInv`) and `K` is monotone.
   - The factor is at most `m5FBns m k uB jB`. The counted calls are as in `main_m5`.
4. **The sharp case functions** `caseWorkS`, `caseFS` and `mainWorkS`:
   - They are `caseWork`, `caseF` and `mainWork` except at M4 and M5, where they take items 2
     and 3's work and factor.
   - They are explicit in `n`, `N`, `p`, `g`, `s`, `k`, `j`, the label length `t` and `jB`.
   - Apart from M3, whose base is at most `ℓ` (item 1), no case has a factorial of `m`.
5. **The step** `main_step_sharp` (a new target):
   - It has `main_step_lab`'s conclusion, with `mainWorkS` and `caseFS` and with `t` the
     parent's label length.
   - Its hypotheses are `main_step_lab`'s and the numeric hypotheses.
   - It also concludes `mainCase = .m3 → m ≤ ℓ`.
   - The proof reuses `main_step_lab` on the other cases. It redoes the dispatch path for M4 and
     M5, and leaves `main_step_gen` unchanged.
6. **The numeric hypothesis is satisfiable.** `TBelow` holds at Wielandt's
   `T k = 3 (⌊log₂ k⌋ + 1)` for an explicit `ℓ` (e.g. `ℓ = 128`, `tBelow_wielandt`). This shows
   item 5 is not vacuous for the intended `T`.
7. **Checks.** By kernel `decide` at large `m`:
   - `caseFS` and `caseWorkS` at M4 and M5 are below `m!`;
   - a negative control: `caseF` at M4 and M5 is at least `m!`;
   - `TBelow` at the Wielandt `T` on an initial range.
8. **Audit and docs.**
   - Every new declaration is in AxiomAudit.
   - theorem-map and status get a 14j-6b-2 section, with exactly what is proved and every
     hypothesis.
   - The new target is a protected statement of the loop.

### 14.13 Stage 14j-6c-1: completion criteria (the potential)

Stage 14j-6b-2 is done (approved in round 2, `5d6f81c`). Stage 14j-6c, the potential and the
final theorems, is split in three loops:
- **14j-6c-1**: the thresholds, an explicit `Q(n₀)`, and `cost ≤ potO` (this section). The
  headline bound is `Q^{O(log² n₀)}`.
- **14j-6c-2**: the closed bound `Q(n₀) ≤ 2^{c (λ(n₀) + 1)⁶}`, so the cost is
  `exp(O((log n₀)⁸))`. This is an asymptotic analysis of every work function, independent of
  the induction.
- **14j-6c-3**: the graph-isomorphism entry.

Each gets its criteria when the previous one is done.

**The interface hypotheses** `QPHyp K T C C'` are the growth assumptions of `PLAN-12.md` §2,
with `λ = ⌊log₂⌋`:
- `AltQuotientIso K`, `Monotone K`, and `K n ≤ C (λ(n) + 1)⁵` for every `n`;
- `TransitivityBound T`, and `T m ≤ C' (λ(m) + 1)` for every `m`.

They stay hypotheses until milestones 15 (`K`) and 16 (`T`). Neither `K` nor `T` appears in the
procedure or in the conclusions.

1. **The threshold program** `thrQP C C'`, a local program like `thrConst`, with
   `ThrSpec (thrQP C C') (kQP C) (ℓQP C C') (cTQP C C')`:
   - `kQP C n₀` is at least `5` and `C (λ(n₀) + 1)⁵`, and large enough that `n₀ < k!/2` (e.g.
     `C (λ(n₀) + 1)⁵ + λ(n₀) + 5`);
   - `ℓQP C C' n₀` is at least `4 · kQP C n₀`, `ell0 n₀`, and an explicit `ℓT C'` above which
     `4 C' (λ(m) + 1) + 6 ≤ m`;
   - `cTQP` is explicit. The language has no multiplication primitive. The existing local
     programs (`mulProg`, `powProg`, a logarithm by a loop) may be reused, and the cost may be
     crude (polynomial in `n₀`, `C` and `C'`);
   - `sharpHyp_qp`: under `QPHyp K T C C'`, `SharpHyp K T n₀ (kQP C n₀) (ℓQP C C' n₀)` and
     `ell0 n₀ ≤ ℓQP C C' n₀` hold for every `n₀`.
2. **What the step sees on the domain.** On `MiniDom n₀ n₀ (2n₀)` with `LabInv`, at item 1's
   thresholds:
   - M3 occurs only on bases of at most `ℓ` points (`mainCase_m3_le`).
   - M4 and M5 occur only on bases above `ℓ ≥ ell0 n₀`. So `LabInv` bounds the union cells:
     `t λ(m) ≤ uMax n₀ := 2 (λ(n₀) + 1)²`.
   - M4's depth is `j ≤ T(m) ≤ C' (λ(2n₀) + 1)`, and so is Case 2b's depth bound `supTo T m`.
   - M5 has `k = kQP C n₀`, `2k ≤ m` and `supTo T m < m`.
3. **`Q(n₀)`** (`QQP C C' n₀`) is an explicit sum of:
   - `n₀ + 2`;
   - the tests' cost and every case's work at the corner of its sizes on the domain:
     - the base case, the chain rule, M0, M1, M2a and M2b;
     - M3 on bases of at most `min(ℓ, 2n₀)` points;
     - M4 and M5 through the corner bounds of `SharpWork.lean`, maximized over the depths that
       item 2 allows;
   - every case's factor plus its counted calls (`caseFS + caseA + caseB`) at the same corners.

   The proofs use monotonicity lemmas of every cost function involved: the `CostMono` family,
   extended to the other cases' work, the tests and the factors. On every instance of the domain
   with `LabInv`, in the case the dispatcher takes, they give:
   - `mainWorkS ≤ Q`;
   - `F + a + b ≤ Q²`, for `main_step_sharp`'s factor and counted calls;
   - `|W| + 2 ≤ Q`.

   No factorial of a base above `ℓ` enters `Q`. The only factorials are `min(ℓ, 2n₀)!`,
   `uMax!` and `k!`.
4. **The potential inequalities with an offset.** An empty window has potential `0` but a
   positive cost, and M5's counted calls may be on empty windows (`|W| < k`). So the bound is
   `potO Q 2 |W| bo + Q`, and the inequalities of `Potential.lean` get the offset. For a step
   whose work is at most `Q`, the sum of `potO + Q` over the children and the counted calls,
   plus the work, is at most `potO Q 2 n bo + Q`. This holds:
   - with branching (as `pot_step`): `StepChild` children, counted calls on windows of at most
     `|W|/2` points, `c = F + a + b ≤ Q²`, and a base of at least two points;
   - without branching (as `pot_free`): `FreeChild` children. These are M0 (base `2|W| + 1`),
     M1, M2a, and M3 on a base of one point;
   - for the chain rule (`ChainChild`, no hint), a new inequality: the windows sum to at most
     `n`, and each is smaller than `n`.

   The base case has no children. There is room to spare: for `b = 2` the exponent of `Q` in
   `pot` is at least `288`.
5. **The induction** (`main_pot`, a new target), by strong induction on `miniRk` as in
   `main_spec`.
   - **Statement.** Assume `QPHyp K T C C'`. Let `J` be a valid instance of
     `MiniDom n₀ n₀ (2n₀)` with `LabInv J`. Then `mainBody (thrQP C C')` on `J` returns a
     correct answer with at most `(2n₀)²` generators, at cost at most
     `potO (QQP C C' n₀) 2 J.winSize J.baseOpt + QQP C C' n₀`.
   - The step is `main_step_sharp` with `C x o = potO Q 2 x o + Q`, which is monotone in the
     window.
   - Each case goes to the inequality of item 4 that its `casePred` names. A valid hint has a
     base of at least one point.
   - The induction may be proved for any `Q` meeting item 3's three bounds, then instantiated
     at `QQP`.
6. **The headline** (`mainSolve_qp`, a new protected target). Assume `QPHyp K T C C'`. For
   every valid plain instance (as in `mainSolve_ss`), `mainEntry (thrQP C C')` returns a correct
   answer within `genCost N |gs| + 2 + 15 + potO (QQP C C' N) 2 |W| none + QQP C C' N`.
   - A corollary through `pot0_le` gives at most
     `genCost N |gs| + 17 + (2N + 2) N² Q^{2 (5 λ(N) + 9 + 4 (λ(N) + 6)²)} + Q`, with
     `Q = QQP C C' N`. That is `Q^{O(log² N)}`.
   - `QPHyp` is not yet shown satisfiable: `K` and `T` with these growth bounds come from
     milestones 15 and 16. The docs say so, as they do for `SharpHyp`.
7. **Checks** (`GraphIsoChecks/Pot.lean`, kernel `decide`):
   - `thrQP 1 3` at a few `n₀` returns `(kQP 1 n₀, ℓQP 1 3 n₀)` within `cTQP`, with the values
     by `decide`;
   - the numeric parts of `SharpHyp` at those `n₀`: `4k ≤ ℓ`, `ell0 n₀ ≤ ℓ`, and `TBelow` at
     Wielandt's `T`;
   - item 4's inequalities at small explicit values;
   - a negative control: the branching inequality fails at explicit values with `c > Q²`;
   - the magnitude of `QQP 1 3 n₀` at a small `n₀` (between two powers of two), if the kernel
     evaluates it in reasonable time.
8. **Audit and docs.**
   - Every new declaration is in AxiomAudit.
   - theorem-map and status get a 14j-6c-1 section, with exactly what is proved and every
     hypothesis.
   - `main_pot` and `mainSolve_qp` are protected statements of the loop.

**Not in this stage:** the closed bound (14j-6c-2) and the graph-isomorphism entry (14j-6c-3).

### 14.14 Stage 14j-6c-2: completion criteria (the closed bound)

Stage 14j-6c-1 is done (approved in round 1 with no findings, `afad078`). This stage bounds
`Q(n₀) = QQP C C' n₀` in closed form, so `mainSolve_qp`'s cost becomes `2^{O((log N)⁸)}`.

An analysis of the 306 definitions in `QQP`'s call graph guides the proof. Each variable
exponent, factorial and binomial has a small exponent and a polynomial base:
- the exponents are `k`, `uB`, `j`, `jB` and `min(ℓ, 2n₀)`;
- the polynomial bases are base sizes and window sizes.

Two definitions in the graph are not quasi-polynomial, and `Q` never reads either:
- `c2bRU m = (m + 1)^m · …`, which `ssM5βns` overrides;
- `ssM5β`'s fields `Bcr3` and `Bgen3`, with `m!`.

1. **Growth classes** (`GraphIso/Main/Growth.lean`). Fix an index type `ι` and a size
   `L : ι → ℕ`, and write `X = L i + 1`.
   - `PLB L e v` (polylogarithmic) holds when `∃ c, ∀ i, v i ≤ c · X^e`.
   - `QPB L d v` (quasi-polynomial) holds when `∃ c, ∀ i, v i ≤ 2^{c · X^d}`.

   The closure lemmas:
   - Both classes contain the constants and are closed under `+`, `max`, `min`, truncated `-`
     (in the first argument) and `/`. `QPB L d` is also closed under `·` and constant powers.
     `PLB` multiplies degrees under products and constant powers.
   - Degrees can be raised. `PLB L e ⊆ QPB L 1`, and `Nat.log 2` and `Nat.clog 2` map
     `QPB L d` into `PLB L d`.
   - The growth steps take `x ∈ QPB L 1` and `y ∈ PLB L e`:
     - `x^y`, `y!` and `x.choose y` are in `QPB L (e + 1)`;
     - `2^y` is in `QPB L e`.
   - `supTo g b` and `∑_{i < b} g i` with `b ∈ PLB L e` re-index over the pairs `(i, j)` with
     `j ≤ b i` (respectively `j < b i`). The bound variable is then in `PLB` there.
2. **A growth lemma for every definition `Q` reads.**
   - A polynomial definition gets one lemma for every degree: all its arguments in `QPB L d`
     give the value in `QPB L d`.
   - Every other definition gets a lemma that says, for each argument, which class it must be
     in, as the analysis found.
   - Function arguments (`Bo`, `Bs`, `Bt`) and the bound record `M5Bounds` are allowed.
   - The lemmas may be generated by a script. They are proved by the closure lemmas, not by
     evaluation.
3. **The small parameters**, at `L = λ`:
   - `n₀ ∈ QPB λ 1`;
   - `kQP C` and `ℓQP C C'` are in `PLB λ 5`, and so is `min(ℓ, 2n₀)`;
   - `uMaxQ ∈ PLB λ 2` and `jMaxQ C' ∈ PLB λ 1`.
4. **The closed bound** (`QQP_le_exp`, a new target): for all `C`, `C'` there is `c` with
   `QQP C C' n₀ ≤ 2^{c (λ(n₀) + 1)⁶}` for every `n₀`. M3's factorial `(N − n)!` is
   `min(ℓ, 2n₀)!` at its corner, and is taken separately.
5. **The headline** (`mainSolve_qp_exp`, a new protected target). For all `C`, `C'` there is `c`
   such that for all `K`, `T` with `QPHyp K T C C'` and every valid plain instance (as in
   `mainSolve_qp`), `mainEntry (thrQP C C')` returns a correct answer (`AnsOK`) within
   `genCost N |gs| + 2^{c (λ(N) + 1)⁸}`. The constant `c` depends only on `C` and `C'`. The
   proof is `mainSolve_qp_closed` with item 4: the exponent of `Q` there is
   `O((λ(N) + 1)²)`. `QPHyp` is still not shown satisfiable (milestones 15 and 16), and the docs
   say so.
6. **Checks** (`GraphIsoChecks/QPBound.lean`):
   - Kernel `decide` checks of item 3's constants at several `n₀`, e.g.
     `kQP 1 n₀ ≤ 7 (λ(n₀) + 1)⁵` with the constant the proof uses.
   - Negative controls, as proofs:
     - `¬ QPB λ 6 (fun n => 2^n)`;
     - `¬ QPB λ 6 (fun m => (m + 1)^m)`, which is `c2bRU`'s growth;
     - a growth step needs its premises: `x^y` with `x = y = n` is not in `QPB λ 6`.
7. **Audit and docs.**
   - Every new declaration is in AxiomAudit.
   - theorem-map and status get a 14j-6c-2 section, with exactly what is proved and every
     hypothesis.
   - `QQP_le_exp` and `mainSolve_qp_exp` are protected statements of the loop.

**Not in this stage:** the graph-isomorphism entry (14j-6c-3), and explicit values of `c`.

### 14.15 Stage 14j-6c-3: completion criteria (the graph-isomorphism entry)

Stage 14j-6c-2 is done (approved in round 1 with no findings, `4b00ad6`). This stage runs the
procedure on graphs. Two graphs on `n` vertices become strings on the vertices and the ordered
pairs, under the lift of `Sym(V)`, and the answer is decoded to the coset of graph
isomorphisms. The procedure itself is unchanged.

1. **The encoding** (models, `GraphIso/Main/GraphEntry.lean`). Let `N = n + n · n`. The point
   `u < n` is the vertex `u`, and the point `n + u n + v` is the ordered pair `(u, v)`.
   - `liftPerm n : Perm (Fin n) →* Perm (Fin N)`, an injective homomorphism: `φ` on the
     vertices and `(u, v) ↦ (φ u, φ v)` on the pairs.
   - The string of `X` is `0` at the vertices, and at `(u, v)` it is `1` if `Adj X u v` and `0`
     otherwise.
   - The generators are the lifts of an `n`-cycle and a transposition, and there are none for
     `n ≤ 1`. They generate the image of `liftPerm` (mathlib's `closure_cycle_adjacent_swap`).
   - The window is all of `Ω`, and the representative is the identity.
   - **The reduction** (`iso_graph`): for valid data `X`, `Y` on `n` points of any degree
     (`ValidD n n`), `iso Ω 1 G x y` is the image under `liftPerm` of `{φ | IsIso n X Y φ}`.

   Ordered pairs with the vertices first replace §15's unordered pairs. Decoding is then a
   restriction to the first `n` points, and the language has no division.
2. **Decoding.** A permutation in the image of `liftPerm` maps `{0, …, n − 1}` onto itself.
   Restriction to it (the first `n` entries of both arrays) gives valid data of `Perm (Fin n)`
   and inverts `liftPerm` on the image. For an `AnsOK` answer `(τ, H)` of the encoded instance:
   - `τ` and every generator of `H` lie in the image;
   - with `φ₀` and `hs` the restrictions of `τ` and of `H`'s generators,
     `{φ | IsIso n X Y φ} = φ₀ • ⟨hs⟩`.

   A `none` answer means that there is no isomorphism.
3. **The programs** (`GraphIso/Main/GraphEntryProg.lean`). `giEntry thr` takes `(n, X, Y)`,
   builds the strings, the window, the identity and the generators, runs `mainEntry`, and
   decodes the answer. The output is `Option (PermData × GensData)`.
   - Every program is well formed and has a `RunsWithin` spec with an explicit polynomial cost:
     `encCost n` for the encoding on valid data, and `decCost n s` for decoding an answer with
     `s` generators.
   - There is no multiplication primitive: the row offsets `n + u n` are built by addition.
4. **The generator count.** Decoding is charged per generator. `mainSolve_qp` drops
   `main_pot`'s bound of `(2N)²` generators on the answer group, so new variants keep it
   (`mainSolve_ss_gens` from `main_spec`, `mainSolve_qp_gens` from `main_pot`). The protected
   statements are unchanged.
5. **Correctness on every valid input** (`giSolve_ss`, a new target). Take any threshold program
   with `ThrSpec` (for example `thrQP C C'` or `thrConst k ℓ`), with no growth hypothesis.
   - The closed program is the entry with the Schreier–Sims implementation substituted, run
     inside `WfProc.subst ⟨mainBody thr, _⟩ ⟨ssImpl, _⟩`, with no assumed oracle.
   - For valid data `X`, `Y` on `n` points of any degree, it returns `r` with
     `GICosetOK n X Y r`:
     - `r = none ↔ ¬ ∃ φ, IsIso n X Y φ`;
     - if `r = some (τ, hs)`, then `τ.Valid n`, every generator is valid, there are at most
       `(2N)²` generators, and `{φ | IsIso n X Y φ} = τ.denote n • ⟨hs.denote n⟩`.
6. **The headline** (`giSolve_qp_exp` and `gi_qp_simpleGraph`, new protected targets). For all
   `C`, `C'` there is `c` such that for all `K`, `T` with `QPHyp K T C C'`:
   - **graph data:** for valid data on `n` points, the closed program at `thrQP C C'` returns a
     `GICosetOK` result with local cost at most `2^{c (λ(n) + 1)⁸}`. The bound covers the
     encoding, `generate`, the recursion and the decoding, through `λ(N) ≤ 2 λ(n) + 2`;
   - **simple graphs:** for simple graphs `G`, `H` on `Fin n` (`GraphData.ofSimpleGraph`), the
     same bound, with `r = none ↔ IsEmpty (G ≃g H)` and the coset equal to the set of the
     permutations underlying the isomorphisms `e : G ≃g H`.

   `QPHyp` is still not shown satisfiable (milestones 15 and 16), and the docs say so.
   Correctness (item 5) does not depend on it.
7. **Checks** (`GraphIsoChecks/GraphQP.lean`, kernel `decide`):
   - the encoding on small graphs: the strings, the validity of the generators and the window,
     and `liftPerm`'s data against its model;
   - decoding of lifted permutations;
   - the entry, run with the verified Schreier–Sims oracle as in `MainFull`, on pairs of graphs
     on at most 3 points: isomorphic and non-isomorphic pairs, with the coset compared to the
     brute-force set of isomorphisms over all permutations. `Exec` pieces may be used if one
     declaration is too heavy. If 3 points are still too heavy, use 2 points and say why in the
     docs;
   - a negative control: with only the transposition as generator, the encoded group is too
     small, and the solution set misses an isomorphism of the graphs.
8. **Audit and docs.**
   - Every new declaration is in AxiomAudit.
   - theorem-map and status get a 14j-6c-3 section, with exactly what is proved and every
     hypothesis.
   - `giSolve_ss`, `giSolve_qp_exp` and `gi_qp_simpleGraph` are protected statements of the loop.
   - §15's design note on graph isomorphism describes the encoding used.

**Not in this stage:** a checked entry that validates arbitrary input (graph data whose lists
may be long), and explicit values of `c`.

## 15. Design notes

- **Cost.** The bound `exp(O((log n₀)⁸))` is deliberately generous. Every step is charged
  against one potential, with no case-specific recurrences.
- **Thresholds.** `k(n₀)` and `ℓ(n₀)` will be explicit programs of `n₀` and a constant `C`
  (Pyber's constant, fixed in milestone 15). They are chosen so that `Thresholds K n k` holds
  whenever `K n ≤ C (⌊log₂ n⌋ + 1)⁵`, with `ℓ ≥ 8k` (Case 3 needs `|Γ ∖ S| ≥ 4k`).
- **Graph isomorphism.** The entry is `Sym(V)` on the vertices and the ordered pairs (§14.15),
  with no hint. The first macro-steps rediscover `V` (M0, M4). An initial hint with labels
  `{a, b}` would also work.

## References

- László Babai, *Graph isomorphism in quasipolynomial time*, arXiv:1512.03547, §§3, 8–13.
- Harald A. Helfgott, *Graph isomorphisms in quasi-polynomial time*, arXiv:1710.04574, §§3,
  5.3, 6 and Appendix A.
- László Pyber, *A CFSG-free analysis of Babai's quasipolynomial GI algorithm*,
  arXiv:1605.08266.
