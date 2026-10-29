# Lean development plan, milestone 18: vertex bounds and single-tape graph isomorphism

Prepared 27 October 2026. This continues [PLAN-17.md](PLAN-17.md), whose TM2 graph-isomorphism
theorems are complete. The conventions in [lean/docs/conventions.md](lean/docs/conventions.md)
remain in force. This document plans implementation; it does not mark any new stage complete.

## Goal

1. **State the existing TM2 bounds in terms of the number of vertices.** Add decision and
   full-coset corollaries with time at most `2 ^ (c * (lam n + 1) ^ 8)`, where
   `lam n = Nat.log 2 n`. Retain the input-length theorems and the existing machines.
2. **Formalize a polynomial-time simulation of TM2 by a genuine single-tape machine.** Make
   the simulation reusable, then apply it to the GI decision and coset machines. Give the
   resulting single-tape theorems both in terms of encoded input length and vertex count.

Every headline has a constant and a fixed machine independent of the input. Correctness is
ordinary `SimpleGraph` isomorphism, with the coset describing all isomorphisms. The exponent
`8` is retained throughout. Empty graphs and singleton graphs remain covered.

The endpoint is mathlib's `Turing.TM0`: one doubly infinite tape, finite alphabet, finite
control, and individual move/write transitions. A one-way tape or a binary alphabet is not
required for this milestone. Neither a new GI algorithm nor a sharper quasipolynomial
exponent is part of the work.

## 1. Starting point and proof route

The relevant existing results are:

| Result | Location | Role |
|---|---|---|
| `gi_tm`, `gi_coset_tm` | `lean/GraphIso/TM/GI.lean` | Fixed TM2 machines, correct outputs, uniform bound in encoded length |
| `isoDecide_iff` | `lean/GraphIso/TM/GI.lean` | Boolean specification agrees with `Nonempty (G ≃g H)` |
| `GraphPair.enc`, `GraphPair.n_le_enc` | `lean/GraphIso/TM/GI.lean` | Existing input encoding and `n ≤ L` |
| `gi_runs`, `length_ser_coset_le` | `lean/GraphIso/TM/GI.lean` | Full output specification and polynomial coset serialization length |
| `toFinTM2`, `outputsInTime` | `lean/GraphIso/TM/Machine.lean` | Compilation of the project's structured stack programs |
| `TM2to1.tr`, `tr_respects`, `tr_supports` | mathlib `StackTuringMachine.lean` | Existing stack-to-tape simulation, correctness and finite support |
| `TM1to0.tr`, `tr_respects`, `tr_supports` | mathlib `PostTuringMachine.lean` | Existing translation to individual tape operations |

The mathlib translations prove qualitative simulation. The `TM2to1` module comment gives
an `O(T * (L + T))` estimate, but that comment is not a formal running-time theorem. Add
quantitative refinements locally, reusing the translations and their configuration relations.
Keep the pinned mathlib dependency unchanged. Upstreaming general lemmas can follow later.

Two details govern the design:

- `FinTM2` only bundles finiteness of the input alphabet. The generic simulation must also
  assume `∀ k, Fintype (M.Γ k)` or equivalent finite-alphabet data. The project's compiled
  machines meet this requirement, including the return-address stack.
- A TM2 `step` executes an entire statement. One step can perform several stack actions.
  The generic growth and timing proofs therefore need a machine-dependent bound on statement
  size; the project's one-symbol-per-structured-step lemma alone is insufficient.

The stages form the following dependency chain:

```text
18a: vertex-count corollaries ------------------------------------+
                                                                 |
18b: finite-machine and timed-output contracts                    |
  -> 18c: timed TM2 -> TM1 simulation                             |
  -> 18d: timed TM1 -> TM0 simulation and finite control           |
  -> 18e: input/output adapters and complete transfer theorem     |
  -> 18f: GI on a single tape, in terms of L and n <---------------+
```

Stage 18a is independently deliverable. The generic simulation modules should import mathlib
only, unless a narrowly useful existing project lemma is needed. Only the GI instantiation
should depend on Babai's development.

## 2. Stage 18a: vertex-count corollaries

Proposed file: `lean/GraphIso/TM/Vertices.lean`, importing `GraphIso.TM.GI`.
Checks: `lean/GraphIsoChecks/TMVertices.lean`.

### Encoding bounds

Prove named library lemmas for:

1. A list of naturals below `n`:
   `(ser (.list .nat) xs).length ≤ xs.length * (n + 1) + 1`.
2. Valid graph data `X.ValidD n n`:
   `(ser Ty.graph X).length ≤ n * (n * (n + 1) + 2) + 1`.
3. Every graph pair `p`:
   `p.enc.length ≤ 5 * (p.n + 1) ^ 3`.
4. The logarithmic comparison:
   `lam p.enc.length + 1 ≤ 8 * (lam p.n + 1)`.

The cubic estimate is intentionally coarse. It is sufficient to relate the complexity
parameters; a tighter `O(n² log n)` encoding theorem is unnecessary here.

The audit already kernel-checked these four facts and the decision corollary in a temporary
probe outside the repository. Its proofs may serve as a starting point, adapted to the
library's names and style. The coset corollary is still to be added.

### Headline statements

Add `gi_tm_vertices` with the following type, using the existing namespaces:

```lean
∃ c : ℕ, ∀ p : GraphPair,
  Nonempty (Turing.TM2OutputsInTime
    (toFinTM2 giDecProg .inp .out) p.enc
    (some (ser .bool (isoDecide p)))
    (2 ^ (c * (lam p.n + 1) ^ 8)))
```

Add `gi_coset_tm_vertices` by changing only the time parameter in `gi_coset_tm` from
`lam p.enc.length` to `lam p.n`. Preserve its entire conclusion: `none` iff there is no
isomorphism; otherwise valid permutation and generator data whose left coset is exactly
the set of isomorphisms.

Both follow by increasing the original constant from `c` to `c * 8 ^ 8`. Use the same
execution witnesses and machines. Do not change the encoding, rebuild the algorithm, or
interpret `TM2ComputableInTime.time p.n` as a vertex-count bound: that field takes encoded
input length. The original `gi_tm` continues to provide the bundled computability statement.

### Completion criteria

- Both corollaries have one constant preceding all graph pairs and no extra hypothesis on `n`.
- Kernel checks cover the encoding bounds at `n = 0, 1` and a small nonempty example.
- Instantiate the decision and coset theorems on an isomorphic and a nonisomorphic pair.
  These are theorem instantiations, not attempts to run the enormous GI machines.
- Register the new module and principal declarations in the import and axiom audits.

## 3. Stage 18b: finite machines and timed input/output

Proposed file: `lean/GraphIso/TM/SingleTape/Model.lean`.
Checks: `lean/GraphIsoChecks/TMSingleTapeModel.lean`.

Settle the following contracts before proving the simulation. The names below are proposed
project APIs, not claims that mathlib already provides them.

1. **Finite TM0 machines.** Add a small bundle around `Turing.TM0.Machine` containing a finite
   tape alphabet, its blank symbol, finite states, an initial state and the transition
   function. Reuse `TM0.step` as the operational semantics. Match mathlib's `Inhabited`
   conventions explicitly; do not accidentally substitute an arbitrary default state for
   the source machine's `main` or `initialState`.
2. **Timed outputs.** Define a `TM0OutputsInTime` interface from the existing step-counting
   machinery. It must require arrival at a genuinely halting configuration, the intended
   output, and a bound on actual `TM0.step` transitions. Fix whether the final halt detection
   is counted, and use that convention consistently.
3. **Tape input/output.** Choose a finite alphabet with distinct blank, data and boundary
   symbols, and fixed encoders `encodeIn` and `encodeOut`. Use ordinary left-to-right input
   and output strings with explicit framing. Prove the encodings injective and linear in
   string length. Prefer one symbol per data symbol plus two boundary symbols, giving
   lengths `x.length + 2` and `y.length + 2`; in any case prove both
   `x.length ≤ (encodeIn x).length` and a linear upper bound. An output must not disappear as
   trailing blanks in `ListBlank`; `true`, `false`, an empty output and a serialized `none`
   must remain distinct.
4. **Final configuration.** Specify the head at the start of the output, the output followed
   by blanks, and cleared work outside it. A configuration merely containing a decodable
   answer somewhere on its tape is not the public output contract.
5. **Compositional timing.** Supply the small lemmas needed to concatenate bounded runs and
   enlarge bounds. State a quantitative simulation relation that retains step counts;
   unbounded `Reaches` alone cannot establish polynomial time.

The public generic transfer theorem will have this schematic shape:

```text
For a fixed finite-alphabet TM2 machine M, compile M is a fixed finite TM0 machine.
There is a constant C_M such that, for all input x, output y and T,

  TM2OutputsInTime M x (some y) T
    implies
  TM0OutputsInTime (compile M) (encodeIn x) (encodeOut y)
    (C_M * (x.length + T + 1)^d).
```

The encoders and compiled machine depend only on `M`, not on `x`, `y`, the execution witness
or `T`. Quadratic overhead (`d = 2`) is the target. A larger explicit degree fixed for the
compiler is acceptable if it simplifies the proof; record that degree in the theorem and
documentation. All machine-specific factors belong in `C_M`. No optimization of constants
is required.

## 4. Stage 18c: quantitative TM2-to-TM1 simulation

Proposed file: `lean/GraphIso/TM/SingleTape/TM2Sim.lean`.
Checks: `lean/GraphIsoChecks/TM2Sim.lean`.

Reuse mathlib's `TM2to1.tr`, `TrCfg`, stack-bottom marker and product-track tape layout.

1. **Statement size.** Define a structural upper bound on the number of elementary actions
   executed by a TM2 statement. Maximize it over the machine's finite label set to obtain
   `sM ≥ 1`. Include every branch, even when a particular execution does not take it.
2. **Stack growth.** Starting with input length `L` and otherwise empty stacks, prove that
   every stack after `t` macrosteps has length at most `L + sM * t`. Bound intermediate
   configurations inside a macrostep as well, using `L + sM * (t + 1)`.
3. **Timed shuttles.** Refine the outward and return-scan lemmas underlying
   `tr_respects_aux₁`, `tr_respects_aux₂` and `tr_respects_aux₃`. Each stack operation costs
   at most a constant times the current stack length plus a constant. Handle empty stacks
   and preservation of the bottom marker explicitly.
4. **One macrostep.** Prove a bounded simulation of `TM2.step` by the existing translated
   TM1 machine, including statements with several consecutive stack actions.
5. **Whole runs.** Sum the bounds over `T` source steps. Obtain a bound of the form
   `A_M * (T + 1) * (L + T + 1)` between related initial and final configurations.

Use the configuration relation for the general input and output stacks. Mathlib's convenience
`TM2.eval` and `TM2to1.tr_eval` use one designated stack for both input and output; the GI
machines use distinct `.inp` and `.out` stacks. A transfer theorem restricted to the same-stack
case would not discharge the intended application.

Checks should execute tiny translated machines for push/pop/peek, an empty stack, two stacks
of different lengths, and several stack actions in one source macrostep. Include negative
controls for an incorrect output or a too-small step count. No GI execution is needed here.

## 5. Stage 18d: quantitative TM1-to-TM0 simulation and finite control

Proposed file: `lean/GraphIso/TM/SingleTape/TM1Sim.lean`.
Checks: `lean/GraphIsoChecks/TM1Sim.lean`.

1. Refine `TM1to0.tr_respects` to bound the number of individual TM0 moves/writes simulating
   one TM1 macrostep. The bound comes from statement size over the finite supported label
   set. Account for `goto`, `halt` and the extra halting-state transition.
2. Compose this with stage 18c, retaining the polynomial bound in `L + T + 1`.
3. Reuse `TM2to1.tr_supports` and `TM1to0.tr_supports` to obtain a finite closed set of
   reachable target states. Restrict the translated machine to that set, with the initial
   state included, and prove that restriction preserves each step and its count.
4. Supply actual finite alphabet and state instances for the resulting TM0 bundle. The
   intermediate label types contain statements and are infinite as ambient types; merely
   exhibiting those ambient types is not a finite-state endpoint.

Instantiation for the project's `toFinTM2` must cover the `Sym` alphabets and the finite
return-label alphabet. Any classical choice used to package finite control must be confined
to fixed machine data; no runtime oracle or input-dependent transition table is introduced.

Checks should cover a nontrivial branch, a tape move followed by a write, and halting.
Verify the finite-state restriction on a concrete translated machine and check exact small
step counts against the bound.

## 6. Stage 18e: complete input/output transfer

Proposed files: `lean/GraphIso/TM/SingleTape/IO.lean` and
`lean/GraphIso/TM/SingleTape/Compile.lean`.
Checks: `lean/GraphIsoChecks/TMSingleTape.lean`.

1. **Input adapter.** Starting from the framed input of stage 18b, construct the tape
   configuration used by `TM2to1.TrCfg`. Mathlib's `trInit` reverses the source stack's list
   and installs a bottom marker. Implement and charge the required conversion; do not
   assume a preloaded simulator configuration for free.
2. **Output adapter.** When the simulated TM2 machine reaches its prescribed output
   configuration, extract the designated output stack, restore list order, clear the work
   tape and leave the stage-18b output configuration. All moves, writes and scans count.
3. **Output length.** Derive `y.length ≤ L + sM * T` (or a comparable explicit bound) from
   TM2 stack growth. Use it to absorb output writing into the transfer bound. Do not silently
   import the unbounded-sharing issue of the project's higher-level cost language: these
   are already physical TM2 stacks, and each macrostep has a fixed action bound.
4. **Complete compiler.** Compose the adapters and simulation into one fixed machine.
   Establish the generic transfer theorem of stage 18b, with all preparation and cleanup
   included in its bound. Prove a bundled computability corollary if useful, while retaining
   a direct theorem about the actual encoded input and output.

Tests should run the complete compiled machine on tiny programs: identity/copy, reversal,
an empty output, and transfer between distinct input/output stacks. Check output framing,
head location, halting and time. Include wrong-output and wrong-bound negative controls.
Avoid exhaustive tests of arbitrary machines or large tape executions.

## 7. Stage 18f: single-tape GI and the final headlines

Proposed file: `lean/GraphIso/TM/SingleTape/GI.lean`.
Checks: `lean/GraphIsoChecks/TMGISingleTape.lean`.

1. Define `giDecTM0` and `giCosetTM0` by compiling the existing
   `toFinTM2 giDecProg .inp .out` and `toFinTM2 giCosetProg .inp .out`. Discharge every
   finite-alphabet and finite-state premise once, independently of the graph pair.
2. Define the corresponding graph-input and result encodings through the fixed adapters.
   Record their lengths relative to the original serialization. Express the input-length
   headlines in the actual single-tape input length `L0`, rather than an unexplained
   auxiliary size parameter.
3. Prove `gi_tm0` and `gi_coset_tm0` with time at most
   `2 ^ (c * (lam L0 + 1) ^ 8)`. Obtain these from the generic transfer theorem and the
   existing `gi_tm` and `gi_coset_tm`, without revisiting the GI recursion.
4. Prove `gi_tm0_vertices` and `gi_coset_tm0_vertices` with time at most
   `2 ^ (c * (lam p.n + 1) ^ 8)`. Use stage 18a and the adapter-length bounds. In particular,
   account for input preparation when passing from vertex count to machine time.
5. Preserve the complete mathematical specifications. The decision's output is the encoding
   of `isoDecide p`, connected by `isoDecide_iff` to ordinary graph isomorphism. The coset
   machine returns `none` iff no isomorphism exists and otherwise returns valid data whose
   left coset equals all isomorphisms. State behavior on the raw encodings, independently
   of any alphabet equivalences in bundled computability structures.

The growth calculation is elementary but should be named and proved: a fixed polynomial
in `L + 2 ^ (c * (lam L + 1) ^ 8) + 1` is at most
`2 ^ (c' * (lam L + 1) ^ 8)` for a constant `c'`. The outer polynomial changes the constant,
not the exponent `8`. Prove it uniformly, including length zero where applicable.

For checks, instantiate the theorems on empty graphs, singleton graphs, an isomorphic pair
and a nonisomorphic pair. Test generic simulation code through stage 18e's small programs;
do not run the compiled Babai algorithm merely to test the transfer theorem.

## 8. Validation and documentation

Each stage is a separate reviewable change with its stated completion criteria. Validation is
incremental: **no whole-project rebuild is part of this plan**. In particular, do not invoke a
full-build lean-loop gate as a shortcut for checking a small new module.

- Reuse existing compiled dependencies. Build only the new/changed modules and necessary
  dependants, then run focused probes. Distinguish cached-import checking from a fresh
  verification of the entire library in the audit record.
- Use `lean/scripts/guard.sh` for heavy Lean commands, respecting its shared lock, memory
  cap and time limit. Run check modules sequentially. Keep warnings clean and preserve
  `autoImplicit = false`; do not add heartbeat overrides.
- Add all new modules to the appropriate library/check roots and to the axiom audit's import
  closure. Audit the new endpoints' transitive dependencies, allowing only `propext`,
  `Classical.choice` and `Quot.sound`. No `sorry`, project axioms or `native_decide`.
  *Implementation note (28 October 2026):* every change to the library root `GraphIso.lean`
  rebuilds the check modules importing it and their dependants (measured at stage 18a: about
  100 minutes, 40 GB peak). The generic modules of stages 18b–18e therefore enter the axiom
  audit's import closure (through their check modules) as each stage completes, and the library
  root imports the single-tape modules once, in stage 18f.
- Put generic simulation tests in modules that avoid importing the full GI development.
  Keep large regression executions out of these new tests. Split a kernel execution if it
  exceeds the repository's established resource threshold.
- Update `lean/docs/status.md` and `lean/docs/theorem-map.md` as stages are completed.
  Present the vertex-count GI theorem as the mathematical headline and retain the
  input-length theorem as the machine-level statement.
- Reconcile the machine-model boundary in `PLAN-17.md` and the cost-model documentation
  once the single-tape transfer is proved. Preserve the historical scope of milestone 17
  and link to its completion here; do not make earlier stages appear to have proved more
  than they did.

## 9. Final acceptance criteria

The milestone is complete when:

1. `gi_tm_vertices` and `gi_coset_tm_vertices` are proved for the unchanged TM2 machines.
2. A reusable theorem transfers finite-alphabet TM2 computations to finite single-tape TM0
   computations with an explicit fixed polynomial overhead, including input/output work.
3. The two fixed GI machines have single-tape correctness and quasipolynomial bounds both
   in actual encoded input length and in vertex count.
4. No simulation premise remains in a GI headline; all constants precede all inputs.
5. The coset specification still gives all isomorphisms, and the decision is connected to
   `SimpleGraph.Iso` rather than only to an internal Boolean function.
6. Focused checks, axiom audits and documentation agree with the exact statements proved.

Remaining scope boundaries should be explicit: the claims concern simple graphs presented
by the specified encodings. This milestone does not require rejection of arbitrary malformed
strings, graph canonization, binary-alphabet normalization or optimal simulation constants.
