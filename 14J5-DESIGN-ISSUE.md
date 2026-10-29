# Stage 14j-5: the design issue and decision

24 October 2026. This memo came out of planning stage 14j-5: the recursive procedure, proved
correct by well-founded induction on `(n, m̂)`. No 14j-5 code has been written yet.

## Decision (24 October 2026)

**Option 1 is selected: strengthen the affected specifications in place.** Keep the theorem
names and repair the contracts before building the recursive dispatcher. The scope and
validation requirements are recorded in [PLAN-14.md, after §14.5](PLAN-14.md). The design
decision is settled; the contract repair, proofs and statement-snapshot updates remain to do.

The generator bound must be closed under the whole recursion, including degree changes,
oracle outputs and returned answer groups. A bound chosen independently at each parent does
not yet justify the uniform `C`. Keep it explicit in the sub-solver predicate, prove it at
every child-creation site, and discharge the concrete backend assumptions for Schreier–Sims.
Any initial normalization must be part of the executed and charged program.

The child list must export positive window sizes, with `ch.length ≤ c * n` as a consequence.
An empty initial window still needs a separate cost bound, since `pot(0, ·) = 0`.

For each affected protected target, retain an old/new contract diff including changes to
referenced definitions. Verify that the old guarantees follow by weakening the sub-solver
requirement and forgetting the extra conclusions, without narrowing the parent-input domain.
Only then update its statement snapshot. This decision does not accept unwritten statements
or weaken the build, axiom, correctness or cost requirements.

## The problem

All the macro-step specs (`RunsWithin.m0StepProg` … `RunsWithin.m5StepCJProg`, `rdProg`,
`m3Prog`, and so on) take the recursive call as a hypothesis:

```
HSubSolves X body DV sub (fun J => SizeChild I J ∧ StepChild … (J.winSize, J.baseOpt)) C s
```

with `C : ℕ → Option ℕ → ℕ`. So `sub` must solve **every** valid child `J` of a given measure
within one cost `C(measure)`. That cannot be proved by induction, and so neither 14j-5 nor 14j-6
can discharge it.

1. **The generator count is unbounded.** Neither `SizeChild` nor `HInstValid` bounds
   `J.gens.length`. The cost of a run grows with that length:
   - `fixedTestCost p s = s(5p+3)+9`;
   - `generate` is charged per input generator, and `BackendBounds` covers only `≤ n(s+1)`
     inputs;
   - local list work over the generators adds more.

   Normalizing the generators inside the procedure does not help: the normalization itself
   costs more as the list grows. No uniform `C` exists, even a huge one. So even "correctness
   with some cost" cannot be obtained by induction from the specs as stated. Milestone 1 avoids
   this because its `SolveSpec` quantifies over `gs.length ≤ s`.
2. **Children may have empty windows, as far as the specs say.** `ChildList` bounds only
   `Σ x.1 ≤ c · n`. So the specs allow any number of children with `x.1 = 0`, each costing at
   least 1 (the `recur` event), and no `C` covers them. The same gap breaks the plan's
   `cost ≤ pot`, since `pot(0, ·) = 0`. In reality every child window is a nonempty orbit, but
   the specs do not record it.

Both facts are true of the programs (children's groups come from oracle outputs or answers with
bounded generators, and windows are orbits). The specs just do not export them.

## What any fix needs

- **(a) A generator bound in the sub-solver predicate.** For example `J.gens.length ≤ sC`, with
  `sC` covering `s`, `sIn` and the oracle output bounds. It is proved at each place a child is
  created; these leaf sites are in `Transfer`, `StepsBase`, `DynSeq`/`RD`, `M2bLoop`, `M5Cert`
  and `M5Cases`. The specs' existing generator-count hypotheses (`DOutGens`, M4's `hKs`, M2b's
  `hsR`, M5's `hsK`/`hsKR`) are mostly the needed facts.
- **(b) Nonempty children**, `∀ x ∈ ch, 1 ≤ x.1`, threaded from the orbit lemmas through the
  combinators.
- **Under every option:** discharging the specs' remaining charges for Schreier–Sims.
  - Missing today: `M5Bounds` for Schreier–Sims, and the open generator-count facts above.
  - `ssBounds` fixes `s = n²`, which needs normalized inputs.

Almost every macro-step spec is a protected target: about 35 of the 238, including
`RunsWithin.m0StepProg` through `RunsWithin.m5StepCJProg`, `rdProg`, `m3Prog` and
`dynSeqProg`.

## Options

1. **Generalize in place (recommended).** Add (a) to the sub-solver predicates and (b) to
   `ChildList`, then re-prove the specs. The protected statements change; each change is a
   strengthening (fewer sub-calls required, more facts concluded). This is the selected
   approach; the concrete changes still need verification and `lean-loop accept-statement`
   updates for the affected targets (estimated at about 35). It gives the cleanest result for
   14j-5 and 14j-6.
2. **Corollary pattern.** Keep every protected statement. Add generalized `_g` variants with the
   proofs moved into them, and derive the old theorems as corollaries
   (`HSubSolves.mono` weakens the predicate). This needs no approvals, but doubles about 35
   headline theorems and touches the same proofs as option 1.
3. **Reorder.** Do milestones 15 (Pyber, discharging `AltQuotientIso`) and 16 (Wielandt,
   discharging `TransitivityBound`) first. They are independent of this issue. Return to
   14j-5/14j-6 after deciding between options 1 and 2.

Useful facts for the procedure, whichever option:
- `RunsWithin.m3Prog` needs no primitivity and no `m ≤ ℓ`, so M3 is a correct fallback for every
  hinted instance. The dispatcher can therefore test M4's and M5's numeric conditions on data
  and fall back to M3.
- `MeasLt` has no well-foundedness proof yet. Milestone 1's nested `Nat.strong_induction_on`
  pattern (`solve_spec`) fits.
