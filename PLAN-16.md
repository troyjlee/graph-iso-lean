# Lean development plan, milestone 16: the transitivity bound and the unconditional theorems

Prepared 26 October 2026. This continues `PLAN-15.md` (Pyber's Lemma 12; milestone 15 is
complete, `e4bff1d`). The conventions and standards of `PLAN.md` and `lean/docs/` remain in force.

## Goal

Discharge the interface `TransitivityBound T` of `PLAN-12.md` §1 without CFSG, and with it prove
the graph-isomorphism theorems of milestone 14 **with no hypothesis**:

```
Tq m = 256 (λ(m) + 1)²,   λ = ⌊log₂⌋ = Nat.log 2.
```

A `t`-transitive group of degree `n` not containing `Alt(n)` has `t ≤ Tq n`. This is weaker than
Wielandt's `t < 3 ln n` (`wielandtT`, `PLAN-12.md` §1), and `QPHyp` (`PLAN-14.md` §14.13) asks
for `T m ≤ C' (λ(m) + 1)`. So milestone 14's analysis is generalized to `T`-bounds of polynomial
growth in `λ`: the cost bound `2^{c (λ(n) + 1)⁸}` is unchanged.

## 1. The route, and where it departs from the plan

Throughout, `n` is the degree, `G ≤ Sym(Ω)`, and `supp x` is the set of points `x` moves.

- **Why not Wielandt's bound.** Wielandt's `t < 3 ln n` (1934) combines Bochert's minimal degree
  `n/3` for `3`-transitive groups with Wielandt's theorem that a group of minimal degree `αn`
  involves no `A_k` with `n < C(k, ℓ)`, `ℓ(ℓ−1)(ℓ−2) ≥ (1−α) k(k−1)(k−2)` (Babai 1982, Thm. 6.1).
  The applications involve `A_k` only as a *section* (`G_{Δ} ↠ Sym(Δ)`), and no source available
  here proves the section case (the dissertation and Babai's paper were not accessible). The
  elementary route below needs neither.
- **Support reduction** (Jordan–Bochert style). If `G` is `3`-transitive and `x ∈ G`, `x ≠ 1`,
  has `6 |supp x| ≤ n`, then `G` contains a `3`-cycle, so `Alt(n) ≤ G` (mathlib's Jordan
  theorem, `alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem`). With `a ∈ supp x`,
  `a' = x a` and `b ∉ supp x`, some `h ∈ G` with `h a = a`, `h a' = b` has
  `(n − 2) |supp x ∩ h(supp x)| ≤ (n − 2) + (s − 1)(s − 2)` (averaging: `3`-transitivity
  equidistributes the other images), and `⁅x, h x h⁻¹⁆ ≠ 1` moves at most `3` times the overlap:
  a `3`-cycle when the overlap is `{a}`, otherwise a smaller support.
- **Order versus support** (Babai and Seress 1987/2014). If `n^n < (ord σ)^s` then some
  `σ^m ≠ 1` moves fewer than `s` points.
- **A permutation of large order.** On `t ≥ x²` points the cycle type `p^{⌊log_p x⌋}`
  (`p ≤ x` prime) has order divisible by `lcm(1, …, x) ≥ 2^x / (x + 1)` (mathlib's
  `Chebyshev.two_pow_le_mul_lcmUpto`, as in stage 15d). `t`-transitivity lifts it to `g ∈ G`
  with `ord g ≥ n^6` for `x = 7 λ(n) + 14`, and Babai–Seress gives a power of support at most
  `n / 6`.
- **The milestone 14 hypothesis.** `T` enters milestone 14 only through `TBelow T (ℓT C')` and
  `supTo T m ≤ jMaxQ C' n₀` (`m ≤ 2 n₀`), and `jMaxQ` is used only in the growth class
  `PLB λ 5`. So a generalized hypothesis with a threshold `ℓt` and a bound `j ∈ PLB λ 5` in place
  of `ℓT C'` and `jMaxQ C'` keeps every exponent; the existing statements become corollaries,
  unchanged.

## 2. Stages

Each stage is its own lean-loop. Stage 16a's files are in `GraphIso/Wielandt/` (namespace
`GraphIso.Wielandt`) and import only mathlib and the interfaces.

- **16a: the transitivity bound** (§3 below): commutators with overlapping supports, the
  support reduction, Babai–Seress, the permutation of large order, lifting, and
  `transitivityBound_quad : TransitivityBound Tq`.
- **16b: the unconditional theorems** (§5 below): milestone 14's analysis under a generalized
  hypothesis `QPHypJ` with a depth bound `j ∈ PLB λ 5`, the generalized headlines, and the final
  theorems at `K = Kpy`, `T = Tq`, with no hypothesis.

## 3. Stage 16a: completion criteria (the transitivity bound)

1. **Commutators** (`Commutator.lean`). For `x, y ∈ Sym(Ω)` and `I = supp x ∩ supp y`:
   `supp ⁅x, y⁆ ⊆ I ∪ x(I) ∪ y(I)`, `|supp ⁅x, y⁆| ≤ 3 |I|`, `⁅x, y⁆` is even, and if `|I| = 1`
   and `⁅x, y⁆ ≠ 1` then `⁅x, y⁆` is a `3`-cycle.
2. **Support reduction** (`Support.lean`). For `G ≤ Sym(Ω)` `3`-transitive:
   - `3`-transitivity on triples of distinct points;
   - the averaging lemma (§1);
   - **`alternatingGroup_le_of_support_le`**: `x ∈ G`, `x ≠ 1`, `6 |supp x| ≤ |Ω|` give
     `Alt(Ω) ≤ G` (through `exists_isThreeCycle_mem`).
3. **Babai–Seress** (`Power.lean`): **`exists_pow_support_lt`** as in §1.
4. **The bound** (`Bound.lean`):
   - the permutation of large order on `t ≥ x²` points (`exists_perm_lcmUpto_dvd`);
   - lifting through `t`-transitivity (`exists_mem_orderOf_dvd`);
   - **`transitivityBound_quad : AltQuot.TransitivityBound Tq`**.
5. **Checks** (`GraphIsoChecks/WielandtBound.lean`): the commutator of two `3`-cycles meeting
   in one point is a `3`-cycle (kernel `decide`); Babai–Seress on a concrete permutation; a
   negative control: rotations of `Fin 4` are transitive and do not contain `Alt(4)`, so
   `TransitivityBound (fun _ => 0)` fails; the numbers `Tq 1 = 256`, `Tq 1024 = 30976`.
6. **Audit and docs**, as before. The targets are `alternatingGroup_le_of_support_le`,
   `exists_pow_support_lt`, `exists_mem_orderOf_dvd` and `transitivityBound_quad`.

**Not in this stage:** milestone 14's generalization and the unconditional theorems (16b).

## 4. Design notes

- **Constants.** `x = 7 λ + 14` makes `n^6 (x + 1) ≤ 2^x`; `x² ≤ 196 (λ + 1)² ≤ Tq n`.
- **Why `3`-transitivity.** The averaging needs the images of the points other than `a, a'`
  equidistributed under elements fixing `a` and sending `a'` to `b`: the stabilizer of two
  points must be transitive on the rest.

## 5. Stage 16b: completion criteria (the unconditional theorems)

Stage 16a is done (`3a240b2`). This stage adds `GraphIso/Main/QPJ.lean` (milestone 14's bounds
under a general depth bound) and `GraphIso/Wielandt/Final.lean` (the theorems with no
hypothesis). No milestone 14 module is edited, and no existing statement changes.

This is narrower than §1 and §2 foresaw. The threshold stays `ℓT C'`: the programs `thrQP C C'`
depend on `C'` only through it, and `TBelow Tq (ℓT 181)` holds, so `thrQP 192 181` and
`qpSolver 192 181` serve unchanged and no threshold `ℓt` is introduced. Milestone 14's
statements keep their proofs (they are not re-derived from the generalization); `QPHyp.toJ`
records that the generalization covers them.

1. **The generalized hypothesis** (`QPJ.lean`). `QPHypJ K T C C' j` is `QPHyp K T C C'` with
   `T m ≤ C' (λ(m) + 1)` replaced by its two consequences that milestone 14 uses:
   `TBelow T (ℓT C')` and `supTo T m ≤ j n₀` for `m ≤ 2 n₀`. `QPHyp.toJ` gives
   `QPHypJ K T C C' (jMaxQ C')`.
2. **Milestone 14's proofs with `j` for `jMaxQ C'`** (`QPJ.lean`): the corner values
   (`qpM4J`, `qpM5J`, `qpCasesJ`, `qpWorkJ`, `qpFacJ`, `QQPJ`, with
   `QQP C C' = QQPJ C C' (jMaxQ C')`, `QQP_eq_QQPJ`); the thresholds (`thresholds_qpJ`,
   `sharpHyp_qpJ`); the bounds (`caseWorkS_le_qpCasesJ`, `mainWorkS_le_QQPJ`,
   `caseFAB_le_QQPJ`, `winSize_add_two_le_QQPJ`); the potential (`pot_ind_stepJ`,
   `main_potJ`); the headlines (`mainSolve_qpJ`, `mainSolve_qp_closedJ`); the growth of `QQPJ`
   for `j ∈ PLB λ 5` (`Growth.Main.qpM4J_qpb` … `Growth.Main.QQPJ_qpb`, `QQPJ_le_exp`); and
   **`mainSolve_qp_expJ`**, `mainSolve_qp_gensJ`, `mainSolve_qp_exp_gensJ`,
   **`giSolve_qp_expJ`**, **`gi_qp_simpleGraphJ`**: milestone 14's headlines under `QPHypJ`
   for `j ∈ PLB λ 5`, at the same programs and cost `2^{c (λ + 1)⁸}`.
3. **The hypothesis holds** (`Final.lean`). `Tq` is monotone; `TBelow Tq (ℓT 181)`
   (`tBelow_Tq`, above `64 · 182² > 2²¹`); `jq n₀ = Tq (2 n₀) ∈ PLB λ 5` (`jq_plb`); hence
   **`qpHypJ_final : QPHypJ Kpy Tq 192 181 jq`** from `altQuotientIso_pyber`,
   `transitivityBound_quad` and these.
4. **The unconditional headlines** (`Final.lean`): **`mainSolve_final`**, **`giSolve_final`**
   and **`gi_simpleGraph_final`**: the statements of `mainSolve_qp_exp`, `giSolve_qp_exp` and
   `gi_qp_simpleGraph` at `C = 192`, `C' = 181` (programs `thrQP 192 181`, `qpSolver 192 181`),
   with no hypothesis: `∃ c`, for all inputs, the cost bound `2^{c (λ + 1)⁸}` and correctness.
5. **Checks** (`GraphIsoChecks/WielandtFinal.lean`): the thresholds' numbers (kernel `decide`);
   a negative control: for every `C'`, `Tq m ≤ C' (λ(m) + 1)` fails at `m = 2^{C'}`, so
   `¬QPHyp K Tq C C'` and the generalization is needed; `qpHypJ_final`; the final theorem on the
   empty graphs on `Fin 3` (a nonempty answer).
6. **Audit and docs**, as before. The targets are `QPHyp.toJ`, `mainSolve_qp_expJ`,
   `giSolve_qp_expJ`, `gi_qp_simpleGraphJ`, `qpHypJ_final`, `mainSolve_final`, `giSolve_final`
   and `gi_simpleGraph_final`. The docs record that the formalization's main theorems now have
   no hypothesis.

After this stage milestone 16, and the CFSG-free route of `PLAN-12.md`, is complete.

## References

- L. Babai and Á. Seress, *On the degree of transitivity of permutation groups: a short proof*,
  J. Combin. Theory Ser. A 45 (1987); *Element order versus minimal degree in permutation groups:
  an old lemma with new applications*, arXiv:1401.0489.
- B. Schomburg, *Bochert's results on the minimal degree of multiply transitive permutation
  groups*, arXiv:2209.12049 (the commutator technique).
- L. Babai, *On the order of doubly transitive permutation groups*, Invent. Math. 65 (1982),
  Theorem 6.1 (Wielandt's theorem).
- H. Wielandt, *Abschätzungen für den Grad einer Permutationsgruppe von vorgeschriebenem
  Transitivitätsgrad*, dissertation, Berlin, 1934.
