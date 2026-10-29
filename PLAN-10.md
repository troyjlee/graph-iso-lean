# Lean development plan, milestone 10: Weisfeiler–Leman and the Design Lemma

Prepared 21 October 2026. This continues `PLAN-9.md` (graphs of every bounded valence, commit
03b169c). The conventions, cost model, contracts and standards of `PLAN.md` and `lean/docs/`
remain in force.

## Babai's recursion: the roadmap

Babai's algorithm runs Luks's recursion until it meets a quotient of the group isomorphic to a
large alternating group `Alt(Γ)`, `|Γ| = m`. It then looks for structure on `Γ` that depends
canonically on the strings: a colouring without a dominant colour, a colored partition, or a
Johnson scheme. Each one either cuts the group down or shrinks `m`. Following Helfgott's
exposition (Bourbaki 1125, English translation arXiv:1710.04574), the work splits into
milestones:

- **10 (this plan): descent from a relational structure.** Coherent configurations, the
  `k`-ary Weisfeiler–Leman refinement as a costed program (Helfgott §§2.3–2.5), Fisher's
  inequality, the large clique lemma and **Babai's Design Lemma** (§5.1, Babai §6.1). Its
  algorithmic form takes a `k`-ary relational structure on `Γ`. It returns, canonically relative
  to at most `k − 1` individualized points, either a colouring of `Γ` without a dominant colour
  or a non-clique classical coherent configuration on a dominant colour class. The only other
  outcome is a twin class of more than half of `Γ`.
- **11: Split-or-Johnson** (§5.2, Babai §7): bipartite and coherent Split-or-Johnson, giving a
  canonical colored `α`-partition or an embedded Johnson scheme relative to a pointwise
  stabilizer of index `m^{O(log m)}`.
- **12: alternating quotients**: affected points (§4.1), the large-symmetry case (§4.2), and
  identification of Johnson groups and schemes (§2.8).
- **13: local certificates and their aggregation** (§6).
- **14: the main recursion** (§§3, 5.3, 6.3) and its quasipolynomial cost, with graph
  isomorphism as a corollary.

**The CFSG decision (made 21 October 2026, after milestone 10).** Two results that Babai's
analysis uses depend on the classification of finite simple groups (CFSG): Cameron's theorem
on large primitive groups (§3, Theorem 3.1) and Lemma 4.1 (primitive groups with a large
alternating quotient, through Schreier's hypothesis). The completion target is **CFSG-free**:

- **Lemma 4.1** is replaced by Pyber's CFSG-free version (arXiv:1605.08266). Its hypothesis is
  stronger: `k > max(C, (log |Ω|)⁵)` for an absolute constant `C`, against
  `k > max(8, 2 + log₂ |Ω|)` (Helfgott §4.1). This changes the exponent of the logarithm in the
  later thresholds, not only the constants. Quasipolynomial time survives, but the thresholds
  and the cost analysis of milestones 12–14 must be written for the weaker bound.
- **Cameron's theorem** is replaced by an argument, not a statement (Babai §13.1, Helfgott
  end of §3). On the blocks of a minimal block system, a uniprimitive action goes to
  Split-or-Johnson through its orbital configuration. A doubly transitive action that is not
  a giant is handled by individualizing fewer than `3 ln k` points (Wielandt 1934) or by
  Pyber's elementary order bound for doubly transitive groups (J. Combin. Theory A 62, 1993).
  Wielandt's bound also replaces "`d ≤ 5` by CFSG" in Helfgott §6 (Case 2b).
- **Explicit hypotheses** may serve only as temporary scaffolding. They must be stated in the
  weaker, CFSG-free form, because Pyber cannot discharge a hypothesis asserting the original,
  stronger result. The final completion theorem has none.
- **Before milestone 12:** specify the exact CFSG-free statements and the argument replacing
  each use of Cameron's theorem, and check the group-theory dependencies.

Milestones 10 and 11 are elementary and do not depend on this choice. One interface
consequence for milestone 11: Split-or-Johnson (Theorem 5.3) must be stated for an arbitrary
uniprimitive classical coherent configuration, not only for those that the Design Lemma
produces, because the replacement of Cameron's theorem feeds it orbital configurations.

## Objective and completion criteria

Points are a finite type `V` (`Fin m` for programs), and a `k`-ary partition structure is a
colouring `c : (Fin k → V) → ℕ` of the `k`-tuples.

- A **configuration** (Helfgott Def. 2.5): the colour of a tuple determines which of its
  entries are equal, and the colour of `x ∘ τ` for every map of positions
  `τ : Fin k → Fin k`.
- A **coherent configuration** (Def. 2.8) is a configuration in which, for every vector of
  colours `r`, the number of points `z` with `c (update x j z) = r j` for all `j` depends
  only on the colour of `x`.
- **Classical** coherent configurations (`k = 2`) are stated directly for `c : V → V → ℕ`,
  with the intersection numbers `#{z | c x z = r ∧ c z y = s}`.
- `u` and `v` are **twins** if the transposition `(u v)` preserves `c`.
- **Individualizing** a list `x` of fewer than `k` points gives the vertex colouring
  `u ↦ c (x, u, u, …, u)`. With fewer than `k − 1` points it also gives the classical
  structure `(u, v) ↦ c (x, u, v, …, v)`. These are the 1- and 2-skeletons of Helfgott's `X_x`.
- A colour class is **dominant** if it has more than `t` points, where `t ≥ |V|/2` is a
  threshold. Helfgott's `α|Γ|` is `t = ⌊α m⌋`.

The milestone is complete when:

1. **Coherent configurations** (`GraphIso/Coherent/`, mathlib imports only for the theory):
   the definitions above, with the facts the proofs use:
   - the colour of a tuple determines the colour of every tuple with entries among its own
     (Def. 2.5 (b));
   - counting with arbitrary predicates on the colour vector;
   - the individualized 2-skeleton of a `k`-ary coherent configuration is a classical
     coherent configuration (Exercises 2.11, 2.13);
   - its restriction to a vertex colour class is again one (Exercise 2.12).
2. **Fisher's inequality** (Prop. 2.19), in the form the proofs need: blocks given by any
   family `A : B → Finset P` (repeated blocks allowed), every point in `r` blocks, every pair
   of distinct points in `λ` blocks, and `λ < r`. Then `|P| ≤ |B|`.
3. **The large clique lemma** (Lemma 5.2): in a classical coherent configuration, a vertex
   colour class `C` with `2|C| > |V|` on which all off-diagonal pairs have one colour consists
   of pairwise twins. Its proof builds a block design on `C` and uses Fisher's inequality. The
   strict inequality is needed: with `2|C| = |V|`, the points and lines of the Fano plane give
   a counterexample.
4. **The Design Lemma** (Prop. 5.1, Babai Thm. 6.1.1), for a `k`-ary coherent configuration
   with `k ≥ 2` and a threshold `t` with `|V| ≤ 2t`. If no set of pairwise twins has more than
   `t` points, then some list `x` of fewer than `k` points satisfies one of the following:
   - (a) individualizing `x` gives a vertex colouring with no dominant colour; or
   - (b) `x` has fewer than `k − 1` points, the vertex colouring has a dominant class `C`,
     and the 2-skeleton restricted to `C` is not a clique.
5. **Weisfeiler–Leman** (`k`-ary, Algorithm 3), with the configuration functor `F₂` folded
   in. Each round colours a tuple `x` by a signature (sketched below).
   - **Signature:** its colour, the colours of `x ∘ τ` for all `τ`, and the sorted list of the
     vectors `(c (update x j z))_j` over the points `z`.
   - **Colours:** the new colour is the rank of the signature in the sorted list of all
     signatures. Round 0 adds the equality pattern of the entries.
   - **Stopping:** the rounds stop when the number of colours stops growing.
   - **Model:** a function `wl k m c` returning the stable colouring together with a list
     that decodes its colours into the input colours. The following are proved:
     - the result is a coherent configuration refining `c`;
     - the colour list decodes `c`;
     - **canonicity:** relabelling the input by `π ∈ Sym(m)` relabels the colouring by `π` and
       leaves the colour list unchanged;
     - **isomorphism transfer:** `π` maps `c` to `d` exactly when it maps `wl c` to `wl d`
       and the colour lists agree. In particular `wl c` and `c` have the same twins.
   - **Program:** `wlProg` computes the model on arrays indexed by the codes of the tuples
     (`finFunctionFinEquiv`), with no arithmetic beyond addition and comparison. Its
     `RunsWithin` cost is at most an explicit `C (m^k + 1)³ (k + 1)^{k + 1} (m + 1)²` (or a
     comparable explicit polynomial in `m^k`, `k^k` and `m`): at most `m^k + 1` rounds, each
     sorting and ranking `m^k` signatures.
6. **The Design Lemma as an algorithm** (Babai's procedure Split-or-UPCC without its
   primitivity test, which belongs to milestone 11). The procedure runs `wlProg`, then tries
   the lists `x` of length `0, 1, …, k − 1` in a fixed order. It returns the first `x` that
   satisfies (a) or (b), with its vertex colouring.
   - **Checked entry.** On every input `(k, m, t, c)` it returns `none` exactly when the input
     is invalid: `k < 2`, `2t < m`, or `c` is not an array of size `m^k`.
   - **Large twin class.** Otherwise it returns `some none` only if the input structure has a
     set of more than `t` pairwise twins.
   - **Result.** Otherwise it returns `some (some (x, col))`, where `col` is the vertex
     colouring of the Weisfeiler–Leman configuration individualized at `x`, and (a) or (b)
     holds. In case (b), the restricted 2-skeleton is a classical coherent configuration that
     is not a clique.
   - **Canonicity.** The outcome at a given `x` is canonical relative to `x`: relabelling by
     `π` maps it to the outcome at `π ∘ x`.
   - **Cost:** an explicit polynomial in `m^k`, `k^k` and `m`.
7. **Checks** (`GraphIsoChecks/Coherent.lean`):
   - kernel-evaluated runs on tiny inputs;
   - interpreter runs of `wlProg` (`k = 2` and `k = 3`) on small structures, with these
     checked:
     - the output is coherent (by brute force);
     - the output is unchanged under a relabelling;
     - the output separates non-isomorphic inputs where expected (for example a cycle against
       two triangles);
   - runs of the design entry with outcomes (a) and (b) and `some none`.
8. **Audit and docs**: axiom listing of the new principal theorems; `theorem-map.md`,
   `status.md`.

## Design notes

- **Colour names.** Colours are ranks of signatures in a sorted list. The list depends only on
  the set of signatures, so names are canonical, and the stable colouring of a structure and
  of its relabelling are equal as functions after relabelling, not merely as partitions.
  Signatures are `List (List ℕ)`, ordered lexicographically: mathlib's linear order on lists.
  Sorting is insertion sort, matched to `List.insertionSort`; the sorted distinct list is
  matched to `Finset.sort`.
- **Termination and cost.** A round refines the previous colouring (the signature starts with
  the old colour). Equally many colours means the same partition, so the loop stops after at
  most `m^k + 1` rounds. The cost is paid by the potential `(m^k + 1 − #colours)` times the
  round cost (`RunsWithin.loop_pot`).
- **Coherence at the fixpoint.** When a round does not split any class, equal colours have
  equal signatures. Equal signatures give the configuration axioms (the colours of `x ∘ τ`)
  and the intersection numbers (equal sorted vector lists are equal multisets).
- **The Design Lemma's proof** follows Helfgott.
  - Assume every individualization has a dominant class `C(x)` and, for fewer than `k − 1`
    points, a clique 2-skeleton on it. The large clique lemma then gives
    `C(x ++ [z]) = C(x) \ {z}`.
  - Some `u, v ∈ C(∅)` are not twins. The colour of a witness tuple is determined by that of
    its canonical rearrangement: the distinct entries other than `u` and `v`, then `u` and/or
    `v`. Individualizing those entries separates `u` from `v`, which contradicts dominance or
    the clique.
  - No minimal-length argument is needed.
- **Thresholds** are a natural number `t` with `|V| ≤ 2t` in place of a real `α ≥ 1/2`.
  Dominant means more than `t` points. An `α`-colouring is a colouring with every class of at
  most `t` points.
- **Size.** The theory is elementary, and only Fisher's inequality uses linear algebra
  (`ℚ`-vector spaces, `LinearMap.finrank_le_finrank_of_injective`). The `k^k` factor comes from
  folding `F₂` into each round. It is at most `m^k` when `k ≤ m`, which is Babai's regime
  (`k ≤ m/2`).

## References

- László Babai, *Graph isomorphism in quasipolynomial time*, arXiv:1512.03547, §§2.5, 6.1.
- Harald A. Helfgott, *Graph isomorphisms in quasi-polynomial time* (Séminaire Bourbaki 1125,
  English translation by J. Bajpai and D. Dona, arXiv:1710.04574), §§2.3–2.6 and 5.1.
- B. Weisfeiler, A. Leman, *The reduction of a graph to canonical form and the algebra which
  appears therein*, Nauchno-Technicheskaya Informatsia 9 (1968).
- R. A. Fisher, *An examination of the different possible solutions of a problem in
  incomplete blocks*, Annals of Eugenics 10 (1940).
