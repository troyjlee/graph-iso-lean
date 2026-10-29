# Lean development plan, milestone 6: primitive solvable groups

Prepared 20 October 2026. This continues `PLAN-5.md` (all graphs of maximum degree three,
commit b8eb8ed). The conventions, cost model, contracts and standards of `PLAN.md` and
`lean/docs/` remain in force.

## Objective and completion criteria

Milestone 3 bounds the cost of Luks's strategy by the orders of primitive sections:
`solve_luks` is polynomial for any group with `PrimBounded G₀ c`, and milestone 3 proved
`PrimBounded G₀ 1` for nilpotent groups. The next group-theoretic step of the programme is the
Babai–Cameron–Pálfy theorem: a primitive group of degree `n` whose composition factors have
bounded order has order `n^{O(1)}` (Helfgott, Theorem 2.3). The full theorem would take
several milestones. This milestone proves its **solvable case**, by an elementary argument
that uses a bounded number of prime divisors in place of the Pálfy–Wolf bound:

> **Theorem.** Let `G` be a primitive solvable permutation group of degree `n ≥ 2` whose
> order has at most `s + 1` distinct prime divisors. Then `|G| ≤ n^{12 s + 1}`.

For `s = 0` (`p`-groups) this is milestone 3's `|G| = n`. The groups of Luks's reduction for
graphs of valence at most five are solvable `{2, 3}`-groups (iterated extensions by subgroups
of products of `S₄`), so `s = 1` and the exponent is 13. Using these groups for graphs is the
next milestone.

**The argument.** Throughout, `p` and `r` are primes, `F = ZMod p`, and `V` is a finite
`F`-vector space.

1. **Linear `r`-groups.** If `r ≠ p` and `R ≤ GL(V)` is an `r`-group, then `2 |R| ≤ |V|³`
   for `V ≠ 0`. This is proved by strong induction on `|V|`.
   - Let `A` be an abelian normal subgroup of `R` of largest order.
   - Let `B ⊆ End(V)` be the subalgebra it generates. It is commutative. It is a quotient of
     the group algebra `F[A]`, which is semisimple by Maschke's theorem (`|A|` is a power of
     `r`, invertible in `F`). So `B` is reduced, hence a product of fields
     `∏_{𝔪} B/𝔪` over its maximal ideals (`IsArtinianRing.equivPi`).
   - The idempotents `e_𝔪` give `V = ⊕_𝔪 V_𝔪`, where `V_𝔪 = e_𝔪 V` is the subspace killed
     by `𝔪`. Each `V_𝔪` is nonzero. Conjugation by `R` preserves `B`, so `R` permutes the
     maximal ideals: `g V_𝔪 = V_{g𝔪}`.
   - **At least two maximal ideals, `t ≥ 2`.** The kernel `K` of the permutation action
     embeds in `∏_𝔪 GL(V_𝔪)`. By induction it has order at most
     `∏ |V_𝔪|³ / 2 = |V|³ / 2^t`.
     - The image in `Sym(t)` is an `r`-group of order at most `r^{v_r(t!)} ≤ 2^{t−1}`, by
       Legendre's formula.
   - **One maximal ideal.** `B` is a field and `A ↪ B^×` is cyclic, of order
     `< |B| ≤ |V|`.
     - By maximality `A` is its own centralizer, and `R/A` embeds in `Aut(A)` of order
       `φ(|A|) ≤ |A|`. So `|R| ≤ |A|² < |V|²`.
2. **Coprime action.** If a `p`-group `P ≤ Aut(N)` acts on a solvable group `N` with
   `p ∤ |N|`, then `|P| ≤ |N|³`. This is proved by strong induction on `|N|`.
   - For a prime `r` dividing `|N/N'|`, let `E` be the quotient of the abelianization by its
     `r`-th powers: a nonzero `ZMod r`-space. Let `M` be the kernel of `N → E`, a
     characteristic subgroup.
   - An element of `P` acting trivially on `M` and on `E` is trivial: `g ↦ x⁻¹ g(x)` is a
     homomorphism from a `p`-group into `M`, so it is trivial.
   - So `P` embeds in the product of its images in `Aut(M)` and in `GL(E)`. By induction and
     step 1, `|P| ≤ |M|³ |E|³ = |N|³`.
3. **The `p′`-core.** Let `H` be solvable with no nontrivial normal `p`-subgroup, and let
   `N` be its largest normal `p′`-subgroup. Then `C_H(N) ≤ N`.
   - Otherwise, the image of `C_H(N)` in `H/N` contains a nontrivial abelian normal
     subgroup (the last term of its derived series). Its part prime to `p` would enlarge
     `N`, so it is a `p`-group `L/N`.
   - `D = L ∩ C_H(N)` is normal in `H`. It is a central extension of the `p′`-group `D ∩ N`
     by the `p`-group `L/N`, hence nilpotent.
   - Its Sylow `p`-subgroup is then characteristic in `D`, normal in `H` and nontrivial: a
     contradiction.
4. **Solvable linear groups.** Let `H` act faithfully and linearly on `V`. Suppose `H` is
   solvable with no nontrivial normal `p`-subgroup, and let `s′` be the number of primes
   other than `p` dividing `|H|`. Then `|H| ≤ |V|^{12 s′}`.
   - Every Sylow `r`-subgroup with `r ≠ p` has order `≤ |V|³` (step 1). So the `p′`-core `N`
     has order `≤ |V|^{3 s′}`.
   - A Sylow `p`-subgroup `P` meets `C_H(N) ≤ N` trivially (step 3), so it acts faithfully on
     `N` and `|P| ≤ |N|³ ≤ |V|^{9 s′}` (step 2).
   - Multiply the Sylow orders.
5. **Primitive solvable groups.** Let `G` be primitive and solvable of degree `n ≥ 2`.
   - The last nontrivial term of its derived series is abelian and normal. Its elements of
     order dividing a prime `p` form a nontrivial elementary abelian normal subgroup `V`.
   - `V` is transitive (`IsQuasiPreprimitive`) and abelian, hence regular: `|V| = n`. The
     stabilizer `G_α` acts faithfully on `V` by conjugation.
   - **`G_α` has no nontrivial normal `p`-subgroup `Q`.** The fixed points of `Q` on `V` form
     a subgroup of order divisible by `p`, normalized by `V` and by `G_α`, hence normal in
     `G = V G_α`. So they are all of `V`, and `Q`, commuting with the transitive `V` and
     fixing `α`, is trivial.
   - Then `|G| = n |G_α| ≤ n^{1 + 12 s′}` (step 4), with `s′ ≤ s`.

The milestone is complete when:

1. **Linear `r`-groups**: `card_le_of_isPGroup` (step 1), for subgroups of
   `LinearMap.GeneralLinearGroup (ZMod p) V`.
2. **Coprime action**: `card_le_of_coprime` (step 2), for `p`-subgroups of `MulAut N`.
3. **The `p′`-core**: `exists_pcore` and `centralizer_pcore_le` (step 3).
4. **Solvable linear groups**: `card_le_of_isSolvable_linear` (step 4).
5. **Primitive solvable groups**: `card_le_of_isPreprimitive_of_isSolvable` (step 5).
   - `primBounded_of_isSolvable`: if `G₀` is solvable and `|G₀|` has at most `s + 1` prime
     divisors, then `PrimBounded G₀ (12 s + 1)`.
6. **The concrete theorem.** `solve_luks_solvable`: with Luks's strategy and the
   Schreier–Sims backend, string isomorphism for such a group costs at most
   `6640 (n + 1)^{36 s + 8} + 60 L (n + 1)²`. This recovers milestone 3's nilpotent bound
   for `s = 0`.
7. **Checks.** Interpreter runs of Luks's strategy on solvable groups that are not
   nilpotent, against brute force and within the new bound:
   - `S₄` (`s = 1`), `AGL(1, 5)` (`s = 1`), `S₃ wr S₂` (`s = 1`);
   - `AGL(1, 7)` (`s = 2`), where the stronger bound of `s = 1` is not claimed.
8. **Audit and docs.** The principal theorems are added to the axiom audit. `status.md`,
   `theorem-map.md` and the contracts are updated. The remaining parts of
   Babai–Cameron–Pálfy are listed: nonabelian composition factors, and primes counted with
   bounded size in place of bounded number.

## Design notes

- **Inductions on cardinality.** Steps 1 and 2 induct on `Nat.card V` and `Nat.card N`
  over all spaces and groups of smaller order, in one universe. Cardinalities multiply over
  the decompositions (`|V| = ∏ |V_𝔪|`, `|N| = |M| |E|`), so dimensions are not needed.
- **No isotypic components.** The decomposition in step 1 is the commutative algebra `B` and
  its maximal ideals, with the idempotents from `IsArtinianRing.equivPi`. The action of `R`
  is conjugation of `B` by units. This avoids semilinear maps between group-algebra modules.
- **Maschke from mathlib.** The group algebra of `A` over `F` is semisimple
  (`Mathlib/RepresentationTheory/Maschke.lean`). A surjective image of a semisimple ring is
  semisimple, and a commutative semisimple ring is reduced.
- **Elementary abelian quotients** come from `Abelianization N` and the subgroup of `r`-th
  powers. `ZMod r`-linearity of additive automorphisms comes from
  `AddMonoidHom.toZModLinearMap`.
- **Quasiprimitivity is enough.** Step 5 uses only that nontrivial normal subgroups are
  transitive (`IsQuasiPreprimitive`, implied by `IsPreprimitive`).
- **No new programs.** The algorithmic content is milestone 3's `solve_luks`; only the
  hypothesis `PrimBounded` is discharged for a larger class.
- **No choice in sources.** Every construction (the core `N`, the algebra `B`, the
  idempotents) lives inside proofs as an existential. No top-level `noncomputable` definition
  is introduced.
- **Relation to the literature.** Babai–Cameron–Pálfy allows arbitrary abelian composition
  factors and nonabelian factors from a fixed class, and the Pálfy–Wolf bound gives
  `|G| ≤ 24^{−1/3} n^{3.25}` for every primitive solvable group. Both need much more linear
  group theory: Clifford theory, extraspecial groups and symplectic modules. Bounding the
  number of primes lets every Sylow subgroup except one be bounded by step 1, and the
  remaining one by its coprime action on the `p′`-core.

## Phases

| Phase | Work | Gate |
|---|---|---|
| 0 | Plan; survey of the mathlib API for each step | Every step's dependencies located |
| 1 | Linear `r`-groups | `card_le_of_isPGroup` |
| 2 | Coprime action and the `p′`-core | `card_le_of_coprime`, `centralizer_pcore_le` |
| 3 | Solvable linear groups and primitive solvable groups | `card_le_of_isSolvable_linear`, `primBounded_of_isSolvable` |
| 4 | The concrete theorem | `solve_luks_solvable` |
| 5 | Checks, audit, documentation | Runs on solvable groups, axiom listing, docs |

## Layout

New modules under `lean/GraphIso/Groups/`:

- `LinearPGroup.lean` (step 1);
- `Coprime.lean` (step 2);
- `PCore.lean` (step 3);
- `SolvableLinear.lean` (step 4);
- `PrimitiveSolvable.lean` (step 5 and `primBounded_of_isSolvable`).

The concrete theorem goes in `lean/GraphIso/Solver/LuksSolvable.lean`, and checks in
`lean/GraphIsoChecks/LuksSolvable.lean`.

## References

- László Babai, Peter J. Cameron, Péter P. Pálfy, *On the orders of primitive groups with
  restricted nonabelian composition factors*, J. Algebra 79 (1982), 161–168.
- Harald Andrés Helfgott, *Graph isomorphisms in quasi-polynomial time*, Section 2.2
  (arXiv:1710.04574): Theorem 2.3 (BCP) and Theorem 2.4 (Luks).
- Péter P. Pálfy, *A polynomial bound for the orders of primitive solvable groups*,
  J. Algebra 77 (1982); Thomas R. Wolf, *Solvable and nilpotent subgroups of GL(n, q^m)*,
  Canad. J. Math. 34 (1982). The sharp bounds, not used here.
- Eugene M. Luks, *Isomorphism of graphs of bounded valence can be tested in polynomial
  time*, J. Comput. System Sci. 25 (1982).
