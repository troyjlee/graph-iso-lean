# Lean development plan, milestone 12: alternating quotients and the CFSG-free interfaces

Prepared 22 October 2026. This continues `PLAN-11.md` (Split-or-Johnson, commit 2c9e681). The
conventions, cost model, contracts and standards of `PLAN.md` and `lean/docs/` remain in force.

The decision of 21 October 2026 (`PLAN-10.md`) asked for two things before this milestone:
- the exact CFSG-free statements that replace the two CFSG-dependent results of Babai's
  analysis;
- the argument that replaces each use of Cameron's theorem.

This plan gives both. The milestone then proves the group theory of alternating quotients
against those statements, which enter the Lean development as explicit hypotheses
("interfaces"). The interfaces are in the weak CFSG-free form, so that Pyber's and Wielandt's
theorems can later discharge them. The final completion theorem will have no such hypothesis.

## 1. Where CFSG is used, and what replaces it

| Use (Helfgott / Babai) | CFSG input | CFSG-free replacement | Interface |
|---|---|---|---|
| Lemma 4.1 / Lemma 8.2.4: an epimorphism `φ : G → Alt(k)` from a primitive `G` of degree `n` is an isomorphism when `k > max(8, 2 + log₂ n)` | Schreier's hypothesis | Pyber, *A CFSG-free analysis of Babai's quasipolynomial GI algorithm*, Lemma 12: the same for `k > (log₂ n)⁵`, `k` larger than an absolute constant | `AltQuotientIso K` |
| Theorem 3.1 (Cameron–Maróti): large primitive groups | the classification | Babai §13.1: Split-or-Johnson on the orbital configuration, and Wielandt's bound on the degree of transitivity (argument in §2 below) | `TransitivityBound T` |
| §6, Case 2b: the degree of transitivity `d` of `φ(F)` on `Φ` is at most 5 | the classification | Wielandt (1934): a `t`-transitive group of degree `k` not containing `Alt(k)` has `t < 3 ln k` | `TransitivityBound T` |

### The interfaces

```lean
/-- Helfgott's Lemma 4.1 with threshold function `K`. -/
def AltQuotientIso (K : ℕ → ℕ) : Prop :=
  ∀ (Ω : Type) [Fintype Ω] [DecidableEq Ω] (G : Subgroup (Equiv.Perm Ω)),
    MulAction.IsPreprimitive G Ω →
    ∀ (Λ : Type) [Fintype Λ] [DecidableEq Λ] (φ : G →* alternatingGroup Λ),
      Function.Surjective φ → K (Fintype.card Ω) ≤ Fintype.card Λ → Function.Injective φ

/-- Wielandt's bound with threshold function `T`. -/
def TransitivityBound (T : ℕ → ℕ) : Prop :=
  ∀ (Λ : Type) [Fintype Λ] [DecidableEq Λ] (G : Subgroup (Equiv.Perm Λ)) (t : ℕ),
    t ≤ Fintype.card Λ → MulAction.IsMultiplyPretransitive G Λ t →
      ¬ alternatingGroup Λ ≤ G → t ≤ T (Fintype.card Λ)
```

What the literature gives for each interface:
- **Babai, with CFSG:** `AltQuotientIso (fun n => max 9 (⌊log₂ n⌋ + 3))`. This is not used.
- **Pyber, without CFSG:** `AltQuotientIso (fun n => max C ((⌊log₂ n⌋ + 1)⁵))` for an absolute
  constant `C`; the formalization will make `C` explicit. The threshold is a fifth power of
  `log n`, not a constant factor, so later thresholds and costs carry `(log n)⁵`. Quasipolynomial
  time survives.
- **Wielandt:** `TransitivityBound (fun k => 3 (⌊log₂ k⌋ + 1))`, since `3 ln k ≤ 3 log₂ k`.

The later milestones state their theorems for any `K` and `T` satisfying the interfaces, with
growth assumptions:
- `K` is monotone, `K n ≥ ⌊log₂ n⌋ + 3`, and `K n ≤ C (log₂ n + 1)⁵`;
- `T k ≤ C' (log₂ k + 1)`.

The final theorem instantiates `K` and `T` with the functions proved in milestones 15 and 16.

**Satisfiability.** Both interfaces have trivial witnesses, which shows they are consistent:
- `AltQuotientIso (· + 1)`: a group of permutations of `n` points has at most `n!` elements,
  fewer than `(n + 1)!/2` when `n ≥ 2`.
- `TransitivityBound id`.

These witnesses are useless for quasipolynomial time but certify that no interface is
contradictory.

### What discharging them will take (milestones 15, 16)

**Pyber's Lemma 12 (milestone 15).** Throughout, `CompA(H)` is the set of primes `p` such that
the cyclic group of order `p` is a composition factor of `H`.
- **The key result, Pyber's Theorem 7:** for a transitive `G` of degree `n` and a point
  stabilizer `G_x`, `|CompA(G_x)| < 2 (log₂ n)²`.
- **What Theorem 7 rests on:**
  - Jordan's lemma: in a primitive group, a prime dividing `|G_x|` divides the order of the
    group that `G_x` induces on each nontrivial suborbit;
  - Wielandt's lemma on the kernel of `G_x` on a suborbit, using Wielandt's 1939 theory of the
    smallest subnormal subgroup with prescribed composition factors;
  - the structure of the socle of a primitive group;
  - the reduction lemmas for imprimitive groups (Pyber's Lemma 8) and primitive groups (his
    Lemma 10);
  - the composition factors of subdirect products.
- **Lemma 12 from Theorem 7:**
  - A cyclic subgroup of `Alt(k)` whose order is a product of `r ≈ √(k / log k)` distinct
    primes is a product of disjoint cycles of prime lengths with sum at most `k`. Proving it
    exists needs a Chebyshev-type bound: the `m`-th prime is `O(m log m)`.
  - Its preimage in the transitive `G` (`ker φ` is transitive) then has more abelian composition
    factors than Theorem 7 and Pyber's Proposition 3 (`|CompA(G) \ CompA(G_x)| < log₂ n`) allow.

**Wielandt's bound (milestone 16):** a `t`-transitive group of degree `k` not containing
`Alt(k)` has `t < 3 ln k`. An alternative is Pyber's order bound for doubly transitive groups
(J. Combin. Theory A 62, 1993), with the matching change in §2 below.

## 2. The argument that replaces Cameron's theorem (Babai §13.1)

Setting: `G` transitive on `Ω` with a minimal block system `Φ`, `|Φ| = k`, so that `G` acts
primitively on `Φ`; `N` is the kernel of this action. Helfgott §3 used Cameron's theorem here.
The replacement procedure is used in milestone 14:
1. **Giant action.** If `G/N ≥ Alt(Φ)`, proceed as in Cameron's case (b) with Johnson
   parameter `1`: `φ : G → Sym(Φ)` is given by the action.
2. **Uniprimitive action.** Otherwise, if `G` is not doubly transitive on `Φ`, its orbital
   configuration on `Φ` is a uniprimitive classical coherent configuration (computed from the
   orbits on pairs). Split-or-Johnson (`split_or_johnson`, milestone 11) returns, at
   multiplicative cost `k^{O(log k)}`, one of these:
   - **a colored `t`-partition of `Φ`:** this is progress (Helfgott §5.3.2);
   - **a Johnson scheme:** an explicit bijection from `J ⊆ Φ`, `|J| > t`, onto the `s`-subsets
     of a set `Λ`. By the chain rule (Babai Lemma 5.2.1), the problem reduces to `J`, where `G`
     acts through `Λ`. Here `m = |Λ| < 1 + √(2k)`. If this action is giant, the setting is that
     of step 1 with Johnson parameter `s`; otherwise recurse on `Λ` (orbits, minimal blocks).
3. **Doubly transitive, not giant.** By `TransitivityBound T`, the degree of transitivity is
   at most `T(k)`.
   - Individualize `t − 1` points `S`, at multiplicative cost `k^{T(k)}`. Then `G_(S)` is
     transitive but not doubly transitive on `Φ \ S`.
   - If `G_(S)` is imprimitive there, its blocks give at most `k/2` blocks.
   - Otherwise it is uniprimitive, and step 2 applies.
4. **Cost.** Every step has multiplicative cost `k^{O(log k)}` and reduces `k` or the domain by
   a constant factor or to `O(√k)`, as Cameron's theorem did. Hence the recursion's
   quasipolynomial bound survives, with the exponent of `log n` set by `K` in §6 below.

`G/N ≅ Alt(m)` arises only in step 1, with `φ` given explicitly by the action on `Φ` or on `Λ`.
Consequently the identification of Johnson groups and schemes of Helfgott §2.8 (the Babai–Luks–
Seress construction from the smallest and largest orbitals) is **not needed on the CFSG-free
route**: Split-or-Johnson returns its Johnson schemes with `Λ` explicit. That item leaves the
roadmap.

**Local certificates (Helfgott §6).** These use Prop. 4.4 (this milestone) for windows `T` with
`|T| ≥ K(n)`, so `|T| ≈ C (log n)⁵`, and pay `|Ω|^{O(|T|)}`, which is `exp(O((log n)⁶))` per
level. Case 2b uses `TransitivityBound` instead of `d ≤ 5`.

## 3. Roadmap, revised

- **12 (this plan):** the interfaces, satisfiability witnesses, and the group theory of
  alternating quotients (Babai §§8.1, 8.3; Helfgott §4.1), proved against `AltQuotientIso`;
  the effect of a colouring on `t`-subsets (Babai §5.2).
- **13:** local certificates and their aggregation (Helfgott §6), against the interfaces.
- **14:** the main recursion (Helfgott §§3, 5.3, 6.3, with §2 above in place of Cameron), the
  costed programs of milestones 11–14, and the quasipolynomial cost, under the interfaces.
- **15:** Pyber's Lemma 12, discharging `AltQuotientIso` with an explicit `K`.
- **16:** Wielandt's bound, discharging `TransitivityBound`.
- **Completion:** graph isomorphism in quasipolynomial time, with no hypothesis.

## 4. Completion criteria for this milestone

Mathlib imports only, in `GraphIso/AltQuot/`. Throughout, `G : Subgroup (Equiv.Perm Ω)` acts on
a finite type `Ω`, and `φ` is a homomorphism to `alternatingGroup Λ` or `Equiv.Perm Λ` with
`k = |Λ|`.

1. **Interfaces.** `AltQuotientIso`, `TransitivityBound`, and the witnesses
   `altQuotientIso_succ : AltQuotientIso (· + 1)` and `transitivityBound_id`.
2. **Alternating groups** (`k ≥ 5`):
   - `Alt(k)` is perfect;
   - every proper subgroup of `Alt(k)` has index at least `k`;
   - every subgroup of `Sym(k)` not containing `Alt(k)` has index at least `k`.

   Proofs: the action on cosets is faithful by simplicity (mathlib's
   `alternatingGroup.isSimpleGroup`), and `(k − 1)! < k!/2`.
3. **Simple quotient of a subdirect product** (Babai Lemma 8.1.1). Given normal subgroups
   `M i` of `G` with trivial intersection and an epimorphism onto a nonabelian simple group,
   some `M i` lies in the kernel. Proof: images of normal subgroups are `⊥` or `⊤`, and
   `⁅A, B⁆ ≤ A ⊓ B` with `⁅S, S⁆ = S`.
4. **Transitive groups** (Babai Lemma 8.3.1, Helfgott Lemma 4.3 (a)).
   - **Hypotheses:** `AltQuotientIso K` with `K` monotone; `G` transitive on `Ω`; an
     epimorphism `φ : G → Alt(Λ)`; `5 ≤ k`, `K |Ω| ≤ k` and `|Ω| < k!/2`.
   - **Conclusion:** `φ(G_x) ≠ Alt(Λ)` for every `x`.
   - **Proof:** Babai's induction on `|G|`, through a maximal block containing `x`, the kernel
     of the primitive action on the blocks, and item 3 for the restrictions to its orbits.
5. **Some point is affected** (Babai Lemma 8.3.3, Helfgott 4.3 (b)): the same with `G`
   arbitrary, every orbit of size at most `N`, `K N ≤ k` and `N < k!/2`. Some `x` has
   `φ(G_x) ≠ Alt(Λ)`.
6. **The Unaffected Stabilizer Theorem** (Babai Theorem 8.3.5, Helfgott Prop. 4.4 (a)).
   - **Setting:** a giant representation `φ : G → Sym(Λ)`, i.e. `Alt(Λ) ≤ φ(G)`. A point `x`
     is affected if `Alt(Λ) ≰ φ(G_x)`. `D` is the set of unaffected points.
   - **Conclusion:** `Alt(Λ) ≤ φ(G_(D))`, the image of the pointwise stabilizer of `D`. The
     hypotheses are those of item 5.
7. **Orbits of the kernel** (Babai Prop. 8.3.6 and Cor. 8.3.7, Helfgott Prop. 4.4 (b)).
   - **Prop. 8.3.6:** for `φ` onto `H` and `y` in the orbit `Δ` of `x`,
     `|y^{ker φ}| · [H : φ(G_x)] = |Δ|`.
   - **Cor. 8.3.7:** for a giant `φ` with `k ≥ 5` and `x` affected,
     `k · |x^{ker φ}| ≤ |x^G|`.
8. **Colourings of `t`-subsets** (Babai §5.2).
   - **Prop. 5.2.3:** if `m₁ + m₂ = m`, `t₁ + t₂ = t`, `2t ≤ m` and `t₁, t₂ ≥ 1`, then
     `3 C(m₁, t₁) C(m₂, t₂) ≤ 2 C(m, t)`.
   - **Lemma 5.2.1:** colouring the `t`-subsets of `Γ` by their intersection numbers with the
     colour classes of `Γ`, every class not of the form `Δ_i^{(t)}` has at most
     `(2/3) C(m, t)` subsets, and `|Δ_i^{(t)}| m^t ≤ |Δ_i|^t C(m, t)`.
   - **Cor. 5.2.2:** if every colour class of `Γ` has at most `a` points, every class of
     `t`-subsets (`t ≥ 1`, `2t ≤ m`) has `3·size ≤ 2 C(m, t)` or `m·size ≤ a·C(m, t)`.
9. **Checks** (`GraphIsoChecks/AltQuot.lean`): kernel-checked numerical instances of item 8
   on small ranges, and instantiations of items 4–7 with the witness `K = (· + 1)` on abstract
   inputs. The milestone is theory, as milestones 6 and 8 were in their group-theoretic parts.
10. **Audit and docs:** axiom listing of the new principal theorems; `theorem-map.md`,
    `status.md` (including the CFSG table of §1 and the roadmap of §3).

## 5. Design notes

- **Statements over arbitrary finite types.** The induction of item 4 passes to the set of
  blocks and to orbits, which are new types; the interfaces quantify over all `Ω : Type`.
- **Thresholds.** Babai's `k > max(8, 2 + log₂ n)` splits in three:
  - `5 ≤ k`, for simplicity of `Alt(k)`;
  - `K n ≤ k`, the interface;
  - `n < k!/2`, the counting step of Lemma 8.3.1 (Babai uses `k!/2 > 2^{k−2} > n`).

  Every valid `K` exceeds `2 + log₂ n` (Babai's Remark 8.2.5 gives affine counterexamples at
  `k = 2 + log₂ n`), so the third condition costs nothing in the later milestones.
- **Giant representations** (codomain `Sym(Λ)`, image containing `Alt(Λ)`) are reduced to
  epimorphisms onto `Alt(Λ)` through `φ⁻¹(Alt(Λ))`, as Babai does. `Alt(k)` has no subgroup of
  index 2.
- Helfgott states Prop. 4.4 (b) for orbits "containing some unaffected elements". His proof,
  and Babai's Cor. 8.3.7, concern affected orbits; item 7 follows Babai.

## References

- László Babai, *Graph isomorphism in quasipolynomial time*, arXiv:1512.03547, §§5.2, 8, 13.1.
- Harald A. Helfgott, *Graph isomorphisms in quasi-polynomial time*, arXiv:1710.04574,
  §§3, 4.1, 6.
- László Pyber, *A CFSG-free analysis of Babai's quasipolynomial GI algorithm*,
  arXiv:1605.08266.
- Helmut Wielandt, *Abschätzungen für den Grad einer Permutationsgruppe von vorgeschriebenem
  Transitivitätsgrad*, Schriften Math. Sem. Univ. Berlin 2 (1934).
- László Pyber, *On the orders of doubly transitive permutation groups, elementary estimates*,
  J. Combin. Theory A 62 (1993).
