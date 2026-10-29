# Lean development plan, milestone 13: local certificates and their aggregation

Prepared 22 October 2026. This continues `PLAN-12.md` (alternating quotients and the CFSG-free
interfaces, commit bdb2766). The conventions and standards of `PLAN.md` and `lean/docs/` remain
in force, and so does the CFSG-free route: the classification enters only through the
interfaces `AltQuotientIso K` and `TransitivityBound T`, as explicit hypotheses.

## Scope

Babai's method of local certificates (Babai §10.1, Thm. 10.1.3 and Prop. 10.1.8; Helfgott
§6.1) and their aggregation (Helfgott §6.2), **as mathematics**. The certificates and the
aggregated structures are defined from the group, the giant representation and the string, and
the theorems are those Babai and Helfgott use:
- the certificates decide fullness correctly;
- they are canonical;
- the kernel acting on a newly affected window has short orbits, which is what makes the
  recursion pay off;
- each case of the aggregation produces the structure the main recursion consumes.

Computing the certificates calls string isomorphism recursively on windows of size at most
`|Ω|/k` (Babai's "Recompute `H(W)`" by strong Luks reduction). That computation, its programs
and its cost belong to the main recursion, milestone 14.

## Setting

- `G : Subgroup (Perm Ω)` acts on a finite type `Ω`.
- `φ : G →* Perm Γ` is a giant representation (`Alt(Γ) ≤ φ(G)`), with `m = |Γ|`.
- `x : Ω → Σ` is a string; `G` acts on strings by `(g • x) i = x (g⁻¹ • i)`.
- A test set `A ⊆ Γ` has `|A| = k`. `G_A` is its setwise stabilizer under `φ`, and
  `ψ_A : G_A → Sym(A)` is the restriction. `ψ_A` is a giant representation when `k + 2 ≤ m`.
- For a window `W ⊆ Ω` and `H ≤ G_A`, `Aut^W_H(x)` is the set of `h ∈ H` with `h • W = W` that
  preserve `x` on `W` (Babai's `Aut_H(x^W)`, `x^W` being `x` truncated outside `W`).
- `Aff(H)` is the set of points `i` with `Alt(A) ≰ ψ_A(H_i)` (Babai Def. 10.1.4).

## Completion criteria

1. **The beard** (Babai's procedure LocalCertificates, lines 01–05):
   - **Iteration:** `W₀ = ∅`, `H₀ = G_A`. While `ψ_A(H_i)` is a giant,
     `W_{i+1} = W_i ∪ Aff(H_i)` and `H_{i+1} = Aut^{W_{i+1}}_{H_i}(x)`; otherwise nothing
     changes.
   - **Facts:** `W_i` grows and `H_i` shrinks; `W_i` is `H_i`-invariant; and
     `Aut_{G_A}(x) ≤ H_i`.
   - **Stabilization:** the iteration is constant from step `|Ω|` on. Write `W(A)`, `H(A)` for
     the final values.
   - **The window group:** `H(A) = Aut_{G_A}(x^{W(A)})`, i.e. `Aut^{W(A)}_{G_A}(x)`.
2. **Local certificates** (Babai Thm. 10.1.3, Claims 10.1.6 and 10.1.7). `A` is full
   (Def. 10.1.2) if `Alt(A) ≤ ψ_A(Aut_{G_A}(x))`.
   - **Certificate of fullness:** if `ψ_A(H(A))` is a giant, then `K(A) = H(A)_(Ω \ W(A))` (the
     pointwise stabilizer of the complement) satisfies `K(A) ≤ Aut_G(x)` and
     `Alt(A) ≤ ψ_A(K(A))`. Hypotheses: `AltQuotientIso K` with `K` monotone, `5 ≤ k`,
     `K |Ω| ≤ k`, `|Ω| < k!/2`.
   - **Certificate of non-fullness:** otherwise `M(A) = ψ_A(H(A))` satisfies `Alt(A) ≰ M(A)`
     and `ψ_A(Aut_{G_A}(x)) ≤ M(A)`.
   - Hence `A` is full exactly when `ψ_A(H(A))` is a giant, under the same hypotheses.
3. **The kernel on the new window** (Babai's complexity argument, Cor. 8.3.7). For `H = H_i`
   with `ψ_A(H)` a giant and `N` the kernel of `ψ_A` on `H`, every point `u` affected by `H`
   satisfies `k · |u^N| ≤ |u^H|`. So `N`'s orbits on `W_{i+1} \ W_i` have at most `|Ω|/k`
   points.
4. **Canonicity** (Prop. 10.1.8 (v), Thm. 10.1.3). For `σ ∈ G`, the certificates of
   `(σ • x, φ(σ) • A)` are those of `(x, A)` moved by `σ`:
   - `W` is moved by `σ`;
   - `H` and `K` are conjugated by `σ`;
   - `M` is conjugated by the bijection `A → φ(σ) • A`;
   - fullness is invariant.

   In particular the comparison of certificates (Prop. 10.1.11) is determined: the
   `G`-isomorphisms of `(x, A)` to `(x', A')` that respect the windows form the set
   `Iso_{G}(x^{W(A)}, x'^{W(A')}) ∩ φ⁻¹(maps A to A')`.
5. **Aggregation** (Helfgott §6.2), for test sets of size `k`. `F(x)` is the subgroup generated
   by the `K(A)` with `A` full, `S` the support of `φ(F)` on `Γ`. Then `F(x) ≤ Aut_G(x)`, and
   `F` and `S` are canonical (moved by `σ`).
   - **Case 1** (`2|S| ≥ m`, no orbit of `φ(F)` with more than `m/2` points): colouring `Γ` by
     orbit length, with the orbits as blocks and the fixed points as one block, gives a colored
     `⌊m/2⌋`-partition (milestone 11's `IsColPart`).
   - **Case 2** (`2|S| ≥ m` and an orbit `Φ` with `2|Φ| > m`): `Φ` is the unique such orbit.
     - **(2a)** If `φ(F)` induces a group containing `Alt(Φ)` on `Φ`, `F` is a subgroup of
       `Aut_G(x)` with that property: the input of the pullback (milestone 14).
     - **(2b)** Otherwise the degree of transitivity `d` of the induced group satisfies
       `d ≤ T |Φ|` under `TransitivityBound T`. For any `d − 1` distinct points of `Φ`, their
       pointwise stabilizer acts on the rest of `Φ` transitively but not doubly transitively,
       so its orbital configuration is a homogeneous classical coherent configuration that is
       not a clique.
   - **Case 3** (`2|S| < m`): colour the ordered `k`-tuples of `Γ \ S` by the equivalence of
     certificates: `(T) ~ (T')` when some `g ∈ G` maps `T` to `T'` pointwise through `φ` and
     maps `x^{W(T)}` to `x^{W(T')}`. This colouring has **no set of `k` pairwise twins**.
     Otherwise every permutation of some `k`-set `T ⊆ Γ \ S` would be induced by `H(T)`, so `T`
     would be full and `F` would move it. The Design Lemma then applies (Helfgott: "a coloring
     of `(Γ \ S)^k` with no twin class with `≥ |Γ \ S|` elements", for `k ≤ |Γ|/4`).
6. **Checks** (`GraphIsoChecks/Certificates.lean`): the principal theorems instantiated at the
   witness interfaces of milestone 12. The objects are subgroups and windows, which are not
   computable at this level of abstraction; concrete runs come with the programs of
   milestone 14.
7. **Audit and docs:** axiom listing; `theorem-map.md`, `status.md`.

## Design notes

- **Windows as sets, groups as subgroups.** The iteration is a function of the step number
  (`|Ω| + 1` steps suffice), not a while loop. "Giant" is `Alt(A) ≤ ψ_A(H)` with `H` a subgroup
  of `G_A`.
- **The window group.** By induction, every `g ∈ G_A` preserving `x^{W(A)}` lies in each
  `H_i`, because `W_{i+1}` is `H_i`-invariant. So the recursively defined `H(A)` equals
  `Aut_{G_A}(x^{W(A)})`. Case 3 needs this; Babai's "Recompute" identity uses it implicitly.
- **Thresholds** are milestone 12's: `5 ≤ k`, `K |Ω| ≤ k`, `|Ω| < k!/2`, and `k + 2 ≤ m` so
  that `ψ_A` is a giant. Every orbit of a subgroup of `G` has at most `|Ω|` points.
- **Case 2b, not Bochert.** Babai's aggregation (Thm. 10.2.1) uses Bochert's minimal-degree
  bound and the "sideburns". Helfgott's uses the degree of transitivity; following Helfgott
  keeps the single interface `TransitivityBound`.
- **Not in this milestone:**
  - Babai's Case 1 (large sideburns, his Prop. 10.1.13) is not part of Helfgott's route.
  - The naming of orbital colours in Case 2b, which isomorphisms may permute (Babai's warning
    in 2b2), is settled where the configuration is handed to Split-or-Johnson (milestone 14).
  - The pullback for Case 2a is also milestone 14.

## References

- László Babai, *Graph isomorphism in quasipolynomial time*, arXiv:1512.03547, §10.
- Harald A. Helfgott, *Graph isomorphisms in quasi-polynomial time*, arXiv:1710.04574, §6.
