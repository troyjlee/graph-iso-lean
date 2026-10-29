# Lean development plan, milestone 8: the Babai–Cameron–Pálfy theorem

Prepared 21 October 2026. This continues `PLAN-7.md` (graphs of valence at most five, commit
904ff07). The conventions, cost model, contracts and standards of `PLAN.md` and `lean/docs/`
remain in force.

## Objective and completion criteria

Milestone 6 proved the solvable case of the Babai–Cameron–Pálfy theorem for a bounded number
of prime divisors. This milestone proves the theorem in the form of Helfgott's Theorem 2.3,
for groups whose composition factors have bounded order, solvable or not:

> **Theorem.** Let `G` be a primitive permutation group of degree `n ≥ 2` all of whose simple
> sections have order at most `k`. Then `|G| ≤ n^{f(k)}`, `f(k) = 3 k³ + 3 k² + 12 k + 1`.

A simple section is a simple quotient `H/M` of a subgroup `H ≤ G`. Every composition factor is
one, and (Jordan–Hölder) every simple section is a section of a composition factor, so the
hypothesis says that every composition factor has order at most `k`; the section form is the
one closed under subgroups, quotients and extensions, which the proof and its applications
use. With it, `PrimBounded` holds for every such group, and Luks's strategy decides string
isomorphism in polynomial time for groups with composition factors of bounded order. Using it
for graphs of every bounded valence is the next milestone.

**The argument.** It is elementary, and uses milestone 6's linear bounds; there is no induction
on the degree. Write `s` for the number of primes dividing `|G|` (all at most `k`, so `s ≤ k`)
and note `k! ≤ 2^{k²}`.

1. **Sections** (`BoundedSections k`): closed under subgroups, quotients, extensions and finite
   products; the primes dividing the order are at most `k`.
2. **Nonabelian minimal normal subgroups.** A minimal normal subgroup `N` of a finite group `X`
   that is nonabelian is the direct product of the conjugates of a minimal `N`-normal subgroup
   `T`: they are nonabelian simple, pairwise commuting and independent, and `X` permutes them
   transitively by conjugation.
3. **The action on the factors.** If `N` is such a product of `j` simple factors of order at
   most `k`, then `|X : C_X(N)| ≤ (k!)^j 2^{s (j − 1)}`: the kernel of the action on the
   factors maps into `∏ Perm(T_i)` with kernel `C_X(N)`, and the image in `Sym(j)` has each
   Sylow `r`-subgroup of order at most `2^{j − 1}` (milestone 6, Legendre).
4. **Subdirect products.** If `H ≤ T_1 × ⋯ × T_j` (nonabelian simple factors) contains no
   factor, then `2^j |H|² ≤ |T_1 × ⋯ × T_j|²`, by induction on `j`: either the first
   projection of `H` is proper, or `H` meets the first factor trivially and, by a commutator
   argument, at most one other factor lies in the projection of `H` to the remaining ones.
5. **Groups with trivial solvable radical** have a commuting independent family of `t`
   nonabelian simple subgroups with `|Q| ≤ (k! 2^s)^t`: take a minimal normal subgroup `M`,
   apply step 3, and recurse into `C_Q(M)`.
6. **Linear groups.** If `H ≤ GL(V)` (`V` over `ZMod p`) has no nontrivial normal `p`-subgroup
   and bounded sections, then `|H| ≤ |V|^{3k³ + 3k² + 12k}`:
   - its solvable radical `R` has order at most `|V|^{12 s}` (milestone 6);
   - `Q = H/R` has trivial solvable radical (step 5), and each of its `t` simple factors has
     a prime `r ≠ p` dividing its order; for each such `r`, `r^{t_r}` divides `|H|`, so a Sylow
     `r`-subgroup of `H` has order at least `2^{t_r}` and at most `|V|³` (milestone 6), hence
     `2^t ≤ |V|^{3s}`.
7. **Primitive groups.**
   - **Affine case**, a nontrivial abelian normal subgroup: milestone 6's reduction gives a
     regular elementary abelian `V` and a point stabilizer acting faithfully on it with no
     normal `p`-subgroup; step 6 bounds it.
   - **Otherwise** a minimal normal subgroup `N = T_1 × ⋯ × T_j` is nonabelian and transitive.
     The point stabilizer `N_α` contains no factor (the stabilizer `G_α` permutes the factors
     transitively), so `2^j ≤ n²` by step 4; `G_α` meets `C_G(N)` trivially, so
     `|G| ≤ n |G : C_G(N)| ≤ n · n^{2 (k² + s)}` by step 3.
   - Only quasiprimitivity is used.

The milestone is complete when:

1. **Group theory** (`GraphIso/Groups/`, mathlib imports only): the statements of steps 1–7,
   with `card_le_of_isQuasiPreprimitive_of_boundedSections` and
   `card_le_of_isPreprimitive_of_boundedSections` as the main theorems.
2. **Luks's strategy**: `primBounded_of_boundedSections` (`PrimBounded G₀ (f(k))` for every
   `G₀` with bounded sections) and `solve_luks_bounded`: with the Schreier–Sims backend, cost at
   most `6640 (n + 1)^{3 f(k) + 5} + 60 L (n + 1)²`.
3. **Checks**: interpreter runs of Luks's strategy on nonsolvable groups (for example `A₅` and
   `S₅`), against brute force and the default strategy, with the cost within the bound.
4. **Audit and docs**: axiom listing of the new principal theorems; `theorem-map.md`,
   `status.md`.

## Design notes

- Milestone 6's reduction for a regular elementary abelian normal subgroup is factored out of
  `card_le_of_isQuasiPreprimitive_of_isSolvable` (its statement unchanged) and reused.
- Finite families of simple factors are `Finset`s of subgroups; products are mathlib's
  `Subgroup.noncommPiCoprod`, injective by `iSupIndep`.
- The exponent `f(k)` is crude; it is polynomial in `k` and independent of `n`, which is what
  Luks's strategy needs.

## References

- László Babai, Peter J. Cameron, Péter P. Pálfy, *On the orders of primitive groups with
  restricted nonabelian composition factors*, J. Algebra 79 (1982), 161–168.
- Harald A. Helfgott, *Isomorphismes de graphes en temps quasi-polynomial*, Séminaire
  Bourbaki 1125 (2017), Theorem 2.3.
- Eugene M. Luks, *Isomorphism of graphs of bounded valence can be tested in polynomial time*,
  J. Comput. System Sci. 25 (1982).
