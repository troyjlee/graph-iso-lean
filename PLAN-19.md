# Lean development plan, milestone 19: a Palomar submission of single-tape graph isomorphism

Prepared 28 October 2026. This continues [PLAN-18.md](PLAN-18.md), whose single-tape theorems are
complete (`gi_tm0_vertices`, `a686eb7`). The conventions in
[lean/docs/conventions.md](lean/docs/conventions.md) remain in force. This document plans
implementation; it does not mark any new stage complete.

## Goal

Prepare the project for registration in [Palomar](https://palomar-registry.org/), the registry of
machine-checked Lean results (announced 18 August 2026, incubated by the Lean FRO and ICARM):

1. **A self-contained statement.** State the headline in a file that imports only Lean core and
   Mathlib (Palomar's `Challenge.lean`). There is a finite single-tape Turing machine (mathlib's
   `Turing.TM0`) that decides isomorphism of simple graphs on `n` vertices, given in a fixed
   encoding, within `2 ^ (c (⌊log₂ n⌋ + 1) ^ 8)` transitions (Appendix A). Another such machine
   outputs, within the same bound, either "not isomorphic", or an isomorphism `τ` and
   generators of a subgroup whose left coset by `τ` is exactly the set of all isomorphisms
   (Appendix B, D4).
2. **A proof of exactly that statement** from `gi_tm0_vertices`, by a short bridge in the
   library. Palomar's `lake comparator` checks that the proof establishes the recorded statement
   with only `propext`, `Quot.sound` and `Classical.choice`, in Lean's kernel and in NanoDa.
3. **A repository that meets Palomar's mechanical rules.** Every `.lean` file uses Lean's module
   system and has at most 10,000 lines. There is one root licence and a `formalization.yaml`. The
   Solution's closure builds and replays within Palomar's resource profile.

No mathematical result changes. Every protected statement keeps its exact text (`lean-loop`'s
statement snapshot). The exponent `8`, the machines and the encodings are those of milestone 18.
Publication, the licence, authorship and the submission itself are the user's decisions (§2).
Nothing is pushed, published or submitted by the loop.

## 1. Palomar's requirements and the project's state

Sources, read 28 October 2026:
- the [policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md);
- the [submission protocol](https://submit.palomar-registry.org/llms.txt);
- the [template](https://github.com/PalomarRegistry/PalomarTemplate);
- the [verifier](https://github.com/PalomarRegistry/PalomarSubmission) (`verification-profile.json`,
  `execution-profiles.json`).

Re-read them at stage 19e, since they change.

| Requirement | Project now | Action |
|---|---|---|
| Lean `v4.35.0-rc2` or later (where `lake comparator` appears) | `v4.35.0-rc2`; `lake comparator` present | none |
| Axioms only `propext`, `Quot.sound`, `Classical.choice`; no `sorryAx`, `Lean.ofReduceBool` | the project's own rule, audited | none |
| Statement file imports only Lean core, Mathlib (canonical history), Tau Ceti or CSLib (the last two flagged); ≤ 1,000 lines, ≤ 100 KiB | headline uses project definitions (`GraphPair.enc`, `ser`, `giDecTM0`, `TM0OutputsInTime`) | new statement surface importing Mathlib only, a project choice (19c) |
| Statement holes: `theorem … := by sorry` in `Challenge.lean`, proved under the same name in `Solution.lean` | `sorry` is forbidden in sources | generated files outside `lean/` (19e, D3) |
| Every committed `.lean` file uses `module` | none does (351 library files, 72 check files and the two roots) | port (19a, 19b) |
| At most 10,000 lines per `.lean` file; repository ≤ 500 MiB | largest 4,485 (`Main/M5StepCJ.lean`); about 92 MiB tracked | none |
| Exactly one root licence (SPDX) matching `formalization.yaml` | no licence | D1 |
| `formalization.yaml` (v0.4 schema), informal account, sources, automation disclosure | none | 19e, D5 |
| Public GitHub repository at a pinned commit | no remote | D1 |
| Verification budget: production 16 CPU / 32 GiB (retry tier 32 / 64), 19,800 s; public preflight on a GitHub-hosted `ubuntu-24.04` runner, at least 14 GiB | feasibility evidence only: the ported library compiled one module at a time on this Mac in 971 s, at most 2.8 GB per module (§1.2); Linux build, export and replay unmeasured | measured in 19e |

Mathlib's pin `065356127b` is on Mathlib's `master` history (checked against the GitHub API,
28 October 2026), as the statement file's canonical-Mathlib rule requires. All 8,536 files of the
pinned Mathlib already use `module`.

### 1.1 Facts established while drafting

1. **A `module` cannot import a non-`module` file.** A scratch file with `module` and
   `public import GraphIso.TM.SingleTape.GI` fails with "cannot import non-`module`". So the
   Solution's whole closure in the library has to be ported. A thin wrapper repository does not
   avoid this, because Palomar applies the same checks to a declared underlying repository. The
   converse direction works: non-module files import modules, as the project's files import
   Mathlib today.
2. **The mechanical port works on the single-tape modules.** Each file gets three changes:
   `module` first; `import` becomes `public import`; `@[expose] public section` after the module
   docstring. With these, the six Mathlib-only modules `Model`, `TM2Sim`, `TM1Sim`, `Sim`, `IO`
   and `Compile` compile unchanged in a scratch overlay. A deliberate error confirmed that they
   were elaborated.
3. **Module-sensitive constructs in the library are few.** The library has three macros
   (`prog_wf` in `Cost/WellFormed.lean`, `run_with`/`run_step` in `Cost/Spec.lean`) and 18 uses of
   `private`. It has no `run_cmd`, `#eval`, `initialize`, `implemented_by` or `Lean.*` imports.
   The meta code is in the checks: `GraphIsoChecks/Exec.lean` (`partial def`, `run_cmd
   execRuns`) and `GraphIsoChecks/AxiomAudit.lean` (`import Lean.Util.CollectAxioms`,
   `run_cmd`).
4. **The draft statement of Appendix A elaborates** against the pinned Mathlib as a `module` with
   Mathlib imports only. Its only warning is the deliberate `sorry`.
5. **The encoding bridge holds on fixtures.** A scratch file (non-module, importing the checks)
   copied Appendix A's definitions and mapped its symbols into the stack alphabet (`digit b ↦
   bit b`, `endNum ↦ nd`, `cons ↦ tag cons`, `nil ↦ tag nil`). Kernel `decide` showed:
   - `natWord n ++ graphWord G ++ graphWord H` maps to exactly `p.enc` on the two paths `pp`, on
     a path and the triangle `pt`, and on the empty graphs at `n = 0, 1`;
   - `Nat.bits k = toBits k` for `k < 65`;
   - the words of the two graphs of `pt` differ.

   `Nat.bits` is defined by well-founded recursion (`Nat.binaryRec`). One further kernel `decide`
   (an inequality of words with the vertices in increasing order) failed to reduce. So the
   checks of 19c should rewrite with the proved `Nat.bits = toBits` before deciding, rather
   than rely on the kernel unfolding `Nat.bits`.

   The round-1 audit of this plan went further. It proved, for all inputs, `Nat.bits = toBits`,
   the natural-number, list, graph, input and output encoding equalities, the injectivity and
   non-blankness of `ι`, and Appendix A's whole proposition from `gi_tm0_vertices`, with only
   the three permitted axioms (in a probe file of the audit, which is not published). Stage 19c
   can start from that probe.
6. **The repository tracks four paper PDFs** (Babai's paper and his 2017 correction, Helfgott's
   and Pyber's papers). A public repository must not redistribute them (D1).
7. **Axiom dependencies are still visible through ported modules; private declarations need
   care.** A non-module file reports the same axioms for the ported `compile_outputs` and
   `tr2_outputs` as for the originals. For a `sorry` planted in a scratch module, a non-module
   importer reports `sorryAx` on a public theorem that uses it, and so does `#print axioms` in a
   module, with `public import` or with `import all`.

   Coverage is different. The round-1 audit of this plan copied `AxiomAudit`'s enumeration of
   every declaration and planted an **unreferenced private axiom** in a scratch module
   (in the audit's probe logs, which are not published):
   - a non-module importer enumerates it;
   - a module enumerates it only with a direct `import all` of the module that contains it;
   - with `public import`, or `import all` of an intermediate module only, the audit passes
     falsely.

   So `AxiomAudit` stays non-module through 19a, which is safe, and becomes a module in 19b only
   with direct `import all` of every audited module (§4).

### 1.2 Measurements (trial port of the whole library)

A scratch script ported every library module (§1.1, item 2) and compiled them one at a time in
dependency order, without parallelism, on the development machine (30 cores, 103 GB). It
recorded each module's result, peak memory and time. The repository was not modified.

**All 352 library modules (351 files and the root) compile as modules after fixes in eight
files:**
- four files use `nlinarith` without importing it; they get `public import
  Mathlib.Tactic.Linarith` (`Graph/Domain`, `AltQuot/Interfaces`, `Recursion/Pullback`,
  `SoJTree/OrbitClosure`);
- two files get `Mathlib.Data.Set.Finite.Lemmas`, for `Set.exists_max_image` (`Groups/PCore`,
  `Groups/Radical`);
- `Coherent/ListProg`'s `insertionSort_eq_foldr` is reproved with `List.insertionSort_nil`,
  `List.insertionSort_cons`, `List.foldr_nil` and `List.foldr_cons`, instead of unfolding
  `List.insertionSort`;
- `Main/CJohnOps` has two inline `decide` examples on `cjohnIsoD` that no longer reduce, with
  either the elaborator or the kernel. The trial removed them. 19a must find which imported body
  is not visible, then move the examples to a check or rewrite them.

**Time and memory.** Compiled one at a time, the 350 timed modules took 971 s in total. The
slowest took 13 s (`SoJTree/StepProg`, `Main/SharpWork`). The largest peak was 2.8 GB
(`TM/Prims`), and no module exceeded 4 GB. These numbers are feasibility evidence from this Mac,
not a measurement of Palomar's Linux build. They suggest that the Solution's closure is small
next to the production profile (16 CPU, 32 GiB, 19,800 s) and the preflight runner (at least
14 GiB). Whether it fits is established only in 19e: a cold Linux build, the export, and the
independent kernel replay (NanoDa, con-ron), measured under the profile.

**Pilot for 19b.** Six check files compile as modules against the ported library:
`TMSingleTapeModel`, `TMCode` (after adding `Mathlib.Tactic.FinCases`, for `fin_cases`),
`TM2Sim`, `TMSingleTape`, `TMSim` and the toolkit `Exec`. In module form, the kernel rejects a
planted wrong transition count (63 changed to 62 in `TMSingleTape.rev_view`), so kernel
`decide` checks still run. Not yet tested: the users of `Exec`'s meta code (`run_cmd` from
another module). Their import chains include the heavy checks.

Gate builds of this repository (the cascades after edits to `Main/`, about 105 minutes and
40 GB peak) are dominated by the check modules, which the Solution does not import.

## 2. Decisions

The user decided D1–D5 on 28 October 2026. What they chose and what follows from it:

- **D1 — what is published: a new public GitHub repository** with a fresh history, holding a
  generated snapshot (§7).
  - **Included:**
    - the ported library and checks;
    - the docs;
    - the plans `PLAN.md` to `PLAN-19.md` and `14J5-DESIGN-ISSUE.md`, as they are (193 Lean
      files and the docs cite them about 440 times; they mention the review process but
      contain no audit reports);
    - the statement and solution files;
    - the metadata, a README and a root licence;
    - a **formalization notes** document (`lean/docs/formalization-notes.md`, written in 19e in
      this repository and copied into the snapshot).
  - **Not included:**
    - the audit reports, their evidence, the audit log and the loop's state;
    - the paper PDFs;
    - the local settings of Claude Code, and the untracked performance notes and measurements.
  - **Licence:** Apache-2.0, as recommended (the template supports only that root licence
    without extra CI work; Mathlib is Apache-2.0). Confirmed with the metadata in 19e.
  - **References to unpublished files:** 22 to the paper PDFs, 7 to the untracked performance notes.
    The snapshot script checks local CommonMark links and images, reference definitions, HTML
    `href`/`src` attributes, backticked paths and excluded file names; 19e resolves the findings
    in this repository, for example by citing the arXiv identifier instead of the local PDF.
- **D2 — the checks: converted to the module system (19b).** If one check module cannot be
  ported without weakening it, stop and ask the user. Excluding a module from the snapshot is
  no longer a default.
- **D3 — the deliberate `sorry`: only in the public copy.** In this repository:
  - the statement's definitions live in a Mathlib-only library module that has no `sorry`
    (`GraphIso/Palomar/Statement.lean`);
  - the theorems are proved under other names in `GraphIso/Palomar/Bridge.lean`.

  `Challenge.lean` (the definitions copied byte for byte, then the theorems with `by sorry`) and
  `Solution.lean` are generated into the snapshot by a script. This keeps the forbidden-`sorry`
  rule, `lean-loop`'s axiom gate and the axiom audit unchanged.
- **D4 — the coset theorem: included (19d is required).** The proposed statement is Appendix B,
  next to the decision theorem of Appendix A. Both are advertised to Comparator.
- **D5 — the metadata: the user confirms each field in 19e.**
  - Authors and responsible maintainers: only people. Palomar forbids listing AI systems there.
  - `automation.methods`: method `agent`. The models and framework are Claude Code with Claude
    models writing the Lean, and OpenAI Codex auditing each round through `lean-loop`.
  - The source relationships and the divergences (draft in §7).

  The submitter must be a responsible author or maintainer, or be authorized by one. This plan
  assumes the user, as the responsible maintainer.

## 3. Stage 19a: the library in Lean's module system

Proposed tool: `lean/scripts/port-module.py` (the transformation of §1.1, item 2; idempotent).
Files: every `lean/GraphIso/**/*.lean` and `lean/GraphIso.lean`.

1. Apply the transformation to every library file. Keep module docstrings directly after the
   header and imports, as the module system requires.
2. Fix the eight files the trial port reports (§1.2), in the same ways. The kinds found:
   - **Tactics and lemmas reached through Mathlib's private imports.** Mathlib's modules import
     tactics privately, so `nlinarith` and lemmas such as `Set.exists_max_image`
     (`Mathlib.Data.Set.Finite.Lemmas`) no longer arrive transitively. Add the explicit import.
   - **Definitions whose bodies Mathlib does not expose to modules.**
     `simp [List.insertionSort]` fails ("expected a definition with an exposed body"). Use the
     API lemmas (`List.insertionSort_nil`, `List.insertionSort_cons`).
   - **Inline `decide` examples that stop reducing** (`Main/CJohnOps`, on `cjohnIsoD`). Find
     which imported body the module no longer sees. Then move the examples into
     `GraphIsoChecks`, or rewrite them, keeping what they check.

   Watch also for `private` declarations used by exposed definitions, the three macros, and
   `deriving` handlers. Never weaken a definition or a statement to make a file compile.
3. Keep `GraphIsoChecks` as it is in this stage. Non-module files import module files, so the
   checks and `AxiomAudit` keep working unchanged.
4. Check that the protected statements are unchanged (the gate's snapshot comparison). Check that
   `AxiomAudit`, run from its non-module file, reports the same axiom sets as before the port.
   Record a before-and-after comparison of its output. Run the scratch negative control of §4,
   item 3: an unreferenced `private` axiom in a library module, reached only transitively. The
   non-module audit must report it.
5. Update `lean/scripts/build-seq.sh` only if its import parsing needs it (it reads
   `GraphIsoChecks` imports only).

**Completion criteria:**
- every library file starts with `module` and has public imports;
- the full build is `--wfail` clean;
- protected statements are byte-identical, and the axiom audit output is unchanged;
- `docs/conventions.md` records the module convention for new files.

The whole project rebuilds once (every library `.olean` changes). Measured cascades took about
105 minutes and 40 GB. A full rebuild may approach the gate's three-hour guard limit. If it
exceeds it, ask the user before raising the gate's time limit `-t`.

## 4. Stage 19b: the checks in Lean's module system (D2)

Files: every `lean/GraphIsoChecks/**/*.lean` and `lean/GraphIsoChecks.lean`.

1. **Pilot first:** port `Exec.lean` and the lightest check that runs its meta code through
   `run_cmd`, before the rest. Choose it by import weight; `ExecSteps`, `GraphQP`, `MainM4`,
   `MainM5`, `TMGI` and `AxiomAudit` use it. If code from a module cannot run at elaboration
   time in another module, stop and ask the user before porting anything else (D2).
2. Apply the same transformation to the checks. The pilot of §1.2 found one more missing tactic
   import (`fin_cases`).
3. Port the meta code by hand:
   - `Exec.lean`'s toolkit, whose `partial def`s run at elaboration time, becomes `meta`
     definitions, or is imported with `meta import`, as Lean's module reference requires for
     code evaluated by `run_cmd`.
   - `AxiomAudit.lean` must keep enumerating every project declaration, private ones included
     (§1.1, item 7). As a module, it imports every audited module directly with `import all`.
     Generate that import list from the module files, and check that it is complete. If that
     fails, stop and ask the user (D2).
   - **Negative control,** in a scratch copy, not committed: an unreferenced `private` axiom in
     a library module that is otherwise reached only transitively in the library's import
     graph. The generated list must import that module directly with `import all`, and the
     audit must report the axiom. A module audit that reaches the module only transitively
     falsely passes (round-2 audit, `AuditModuleTransitive.log`). The purely transitive test
     belongs to 19a, against the non-module audit.
   - The import-closure check and `build-seq.sh`'s import parsing must accept `public import`
     and `import all`.
4. Keep every `decide +kernel` check's resource profile. The port must not change what the
   kernel evaluates. Compare the guard peaks of the heavy checks (Align, Case2b, Case3, CertProg,
   Giant) with the measurements made before the port.
5. Update `build-seq.sh`'s import parsing for `public import`.

**Completion criteria:**
- every check file is a module;
- the full build is `--wfail` clean;
- the axiom audit is unchanged and still catches a planted axiom (shown in scratch);
- every check still checks what it checked.

## 5. Stage 19c: the self-contained statement and its bridge

Files:
- `lean/GraphIso/Palomar/Statement.lean`: imports Mathlib only; contains the definitions of
  Appendix A in namespace `GraphIsoPalomar`, under `@[expose] public section`;
- `lean/GraphIso/Palomar/Bridge.lean`;
- checks in `lean/GraphIsoChecks/Palomar.lean`.

1. **The statement's definitions** (Appendix A):
   - the symbols `Sym`;
   - `natWord` (Mathlib's `Nat.bits`, least significant first, then an end mark);
   - `listWord`;
   - `nbrs`;
   - `graphWord` (neighbour lists from vertex `n - 1` down to `0`, as the arrays are serialized);
   - `input`;
   - `output`.

   Each has a docstring that states its meaning.
2. **The encoding bridge.** For every `n`, `G`, `H`, the input word mapped by the symbol
   embedding `ι` equals `SingleTape.encodeIn p.enc` at `p = ⟨n, G, H⟩`. Likewise
   `(output b).map ι = SingleTape.encodeOut (ser .bool b)`. The lemmas are:
   - `Nat.bits = toBits` (strong induction);
   - `natWord` against `ser .nat`;
   - `listWord` against `ser (.list _)`;
   - `graphWord` against `ser Ty.graph` of `GraphData.ofSimpleGraph` (`Array.ofFn`, `List.ofFn`,
     reversal).
3. **The symbol embedding** `ι : Sym ↪ giDecTM0.Γ`:
   - `digit b ↦ inp (bit b)`, `endNum ↦ inp nd`, `cons ↦ inp (tag cons)`, `nil ↦ inp (tag nil)`;
   - `lmark ↦ lmark`, `rmark ↦ rmark`;
   - `yes ↦ out (tag tt)`, `no ↦ out (tag ff)`.

   It is injective, and no image is the blank (`work default`).
4. **The theorem** `GraphIsoPalomar.gi_singleTape_proof`, with Appendix A's statement (a new
   protected target), from `gi_tm0_vertices`:
   - witnesses `Γ = giDecTM0.Γ`, `Λ = giDecTM0.Λ`, the machine `giDecTM0.machine`, `ι`, and
     `gi_tm0_vertices`'s constant;
   - `b = isoDecide p`, with `isoDecide_iff`;
   - `TM0OutputsInTime` unfolded to `StepsIn`, which is the statement's iterate;
   - `lam = Nat.log 2`.
5. **Checks** (kernel `decide` on small fixtures; no machine runs):
   - `input` on the empty graphs at `n = 0, 1` and on the path pair of 18f, against
     `encodeIn p.enc` symbol by symbol;
   - `Nat.bits = toBits` on `0..64`;
   - the theorem instantiated;
   - negative controls: `output true ≠ output false` under every injective map; the input words
     of a path and of a triangle differ; the vertex order of `graphWord` is reversed, as
     documented.
6. **A Comparator dry run, before the checks.** Generate a scratch `Challenge.lean` and
   `Solution.lean` (§7, item 1). Run `lake comparator --inadvisably-no-sandbox` locally. This
   confirms that Comparator accepts definitions the Solution receives from an imported module
   (`GraphIso.Palomar.Statement`) under the same names as the Challenge's own. If it does not,
   stop and revise the layout before going on. Copying the definitions into `Solution.lean`
   under another namespace does **not** work: the copies of `Sym` are distinct inductive types,
   not definitionally equal (round-1 audit, `Fallback.log`).

   A candidate to probe:
   - the library proves the statement generically, for any type with the nine symbol values
     (both digits and the seven other symbols) given by an injective map;
   - `Solution.lean` defines `Sym` and the words verbatim and instantiates the generic theorem;
   - its words then agree with the generic ones by unfolding.

   Adopt it only after a probe succeeds, and record which layout is used.

**Completion criteria:**
- `Statement.lean` imports Mathlib only and is under 300 lines (Palomar warns above 300 lines or
  32 KiB);
- the theorem is proved for exactly Appendix A's statement, as revised and approved;
- AxiomAudit lists it;
- docs: the theorem map and status gain the Palomar statement, and the encoding is documented.

Any change to Appendix A's statement after this plan is approved is a change to the advertised
claim. Record it in this plan with the user's approval.

## 6. Stage 19d: the coset statement (D4)

Files: as 19c (the statement module gains Appendix B's definitions; the bridge and the checks
grow).

1. **Statement definitions** (Appendix B), reusing Appendix A's `Sym`, `natWord` and
   `listWord`:
   - `permWord σ`: the images `σ i`, then the inverse images `σ⁻¹ i`, each for `i` from `n - 1`
     down to `0`. This is how `ser Ty.perm` writes valid `PermData`: forward and inverse arrays,
     each reversed.
   - `cosetWord r`: `[lmark, no, rmark]` for `none`; for `some (τ, gs)`, `lmark`, `yes`, the
     word of `τ`, the list of the words of `gs`, then `rmark`.
2. **The output bridge.** For valid `τd : PermData` and `AllValid` generators `hs`, the output
   word mapped by the output embedding equals `ser Ty.giCoset (some (τd, hs))`, at
   `τ = PermData.denote n τd` and `gs = hs.map (PermData.denote n)`. Use `val_denote_apply` and
   `val_denote_inv_apply`, the arrays' sizes, and the reversals. `none` maps to `[tag none]`.
3. **The embeddings.** The coset theorem has its own machine, so it chooses its own embeddings:
   - `ιin`: as the decision theorem's `ι` on input symbols;
   - `ιout`: `digit b ↦ out (bit b)`, `endNum ↦ out nd`, `cons ↦ out (tag cons)`,
     `nil ↦ out (tag nil)`, `yes ↦ out (tag some)`, `no ↦ out (tag none)`, and the marks to the
     marks.

   Both are injective, and no image is blank. A single embedding cannot serve both: the machine
   writes `out` symbols, but reads `inp` ones.
4. **The theorems:**
   - `gi_coset_singleTape_proof`, with Appendix B's statement, from `gi_coset_tm0_vertices`.
     Take `r` to be the data's denotation. `r = none ↔ IsEmpty (G ≃g H)` is the existing
     clause. The iff `(∃ e : G ≃g H, e.toEquiv = φ) ↔ τ⁻¹ * φ ∈ Subgroup.closure {g | g ∈ gs}`
     follows from the existing coset equality, through `GensData.denote` (`Subgroup.closure`
     of `denoteSet`) and membership in a left coset.
   - `cosetWord_injective_proof`: `cosetWord` is injective at every `n`, so the output tape
     determines `r`. It is a prefix code: lengths determined by the marks, `Nat.bits`
     injective, and a permutation determined by its images.
5. **Checks:**
   - the output bridge on fixtures: a 3-cycle with generators `[swap, 3-cycle]`, and `none`.
     This already passes by kernel `decide` in scratch;
   - the theorems instantiated on `pp` (`some`) and `pt` (`none`);
   - negative controls: the images listed from `0` upward give a different word (also checked
     in scratch); `cosetWord none ≠ cosetWord (some _)`.

**Completion criteria:**
- the criteria of 19c, for Appendix B's statements;
- Comparator advertises three theorems: `gi_singleTape`, `gi_coset_singleTape` and
  `cosetWord_injective`.

## 7. Stage 19e: the submission snapshot and local verification

Files:
- `lean/scripts/palomar-snapshot.sh`: writes the snapshot into a directory that is not committed;
- `palomar/` at the repository root: templates for the snapshot's files.

The loop's configuration gains nothing. The generated `Challenge.lean` and `Solution.lean` are
never committed here (D3).

1. **The snapshot** (D1) contains:
   - `lean/` without `.lake`, with the libraries `Challenge` and `Solution` added and
     `defaultTargets = ["GraphIso", "Solution"]`. The checks are built only on request.
     **Warnings:**
     - `GraphIso` and `Solution` build under `--wfail`;
     - `Challenge` is built separately. The snapshot script accepts exactly one warning there,
       the deliberate `sorry` of each advertised theorem, and fails on any other;
     - this exception exists only in the generated snapshot. This repository's rules are
       unchanged;
   - the docs, including the formalization notes, and the plans (D1);
   - the generated `Challenge.lean`, `Solution.lean` and `comparator.json`, in the Lake project.
     `comparator.json` has the three theorem names (`gi_singleTape`, `gi_coset_singleTape`,
     `cosetWord_injective`), `definition_names: []` and the three axioms;
   - the root `LICENSE`, `README.md` and `formalization.yaml`.

   It contains no audit report or evidence, no audit log, no loop state and no paper PDF
   (D1). The script rejects local link destinations that do not resolve inside the snapshot
   and checks backticked paths, with explicit exceptions for files of other repositories and
   unimplemented proposals. Submission preparation uses whole-document CommonMark parsing
   (with tables) and HTML attribute parsing; it does not validate external URLs, fragment
   identifiers or arbitrary Markdown extensions. Code examples are not links.

   **`Challenge.lean`** is `Statement.lean`'s text with the three theorems appended, each with
   `by sorry`. **`Solution.lean`** imports `GraphIso.Palomar.Bridge` and states the same theorems,
   with the proofs `gi_singleTape_proof`, `gi_coset_singleTape_proof` and
   `cosetWord_injective_proof`. The script checks that the definitions in `Challenge.lean` are
   byte-identical to `Statement.lean`'s.
2. **Local verification:**
   - Run the template's `scripts/check-lean-sources.py` (module headers, line caps).
   - Validate `formalization.yaml` against the schema.
   - Run `lake comparator` on macOS with `--inadvisably-no-sandbox` during development.
   - Run it sandboxed, with `--paranoid` (Lean, NanoDa, lean4lean and the other bundled
     checkers), in a Linux container with `bwrap` (Docker or colima).
   - Record the times, the peaks, and the export's size and replay time.
3. **The informal account** (README, formalization notes, and the statement's docstrings):
   - the model (`Turing.TM0`: one tape, finite alphabet and control, individual moves);
   - the encodings of the input and of both outputs;
   - the bound in vertex count;
   - the proof route: Babai's algorithm, CFSG-free (Pyber's Lemma 4.1 replacement, an
     elementary quadratic transitivity bound), executed by compiled stack programs and simulated
     on one tape;
   - what is not claimed: malformed inputs are not rejected, the exponent `8` is not Babai's, the
     constant is not explicit, and there is no canonization.

   **The formalization notes** (`lean/docs/formalization-notes.md`, D1) cover, for readers of
   the public repository:
   - the results and where they are stated;
   - the trust surface (the statement file, Mathlib's `TM0` and `SimpleGraph`);
   - a map from the milestones to the source papers;
   - the proof route and its divergences from Babai and Pyber;
   - how the development was produced and checked: every stage built `--wfail`, with an axiom
     audit, protected statements, and an independent adversarial review per round. The reviews
     are summarized; the reports are not published;
   - how to reproduce the build and the Comparator check.
4. **Metadata draft** (D5):
   - sources: L. Babai, *Graph isomorphism in quasipolynomial time*, arXiv:1512.03547
     (`adapts`); L. Pyber, *A CFSG-free analysis of Babai's quasipolynomial GI algorithm*,
     arXiv:1605.08266 (`adapts`); H. A. Helfgott, with J. Bajpai and D. Dona, arXiv:1710.04574
     (`background` or `adapts`);
   - `fidelity.divergences` from the points of item 3;
   - `status.scope`, `sorry_count: 0`, `axioms: []`;
   - classification: arXiv `cs.CC` and `math.GR`; MSC `68Q25`, `05C60`, `20B40`, `68V20`. To be
     confirmed.

**Completion criteria:**
- the snapshot passes the template's source checks and metadata validation;
- `lake comparator` accepts it sandboxed, Lean and NanoDa both;
- the build-and-replay time and peak fit the production profile with margin, with the numbers
  recorded;
- no audit report, PDF, scratch or local settings file is in the snapshot, and the documented
  local-reference checks pass;
- the user has confirmed the metadata and the licence (D5).

## 8. Stage 19f: publication, preflight and submission (the user's actions)

Not part of any loop.
1. Create the public repository and push the snapshot (D1).
2. Run Palomar's reusable workflow (`PalomarRegistry/PalomarSubmission/.github/workflows/
   submission.yml` at a pinned commit, `mode: full`, `execution_profile: palomar-standard-v1`)
   until it reports `status: pass`.
3. Submit through the form with the full commit SHA. Palomar accepts a responsible author or
   maintainer, or someone authorized by one. This plan assumes the user submits, as the
   responsible maintainer.

At most two verifying submissions per repository owner are allowed, with a cooldown between
them, so submit only after a passing preflight. Editorial review results stay private until
registration, which is a separate public step.

## 9. Validation and documentation

- Each stage is a separate `lean-loop`. 19a and 19b each rebuild the whole project once. Do not
  combine them with other changes.
- Keep `--wfail`, `autoImplicit = false`, no heartbeat options, and the forbidden list. The
  module port adds no exemption.
- AxiomAudit lists the bridge and the statement's definitions. The statement module is in its
  import closure.
- `docs/status.md` and `docs/theorem-map.md` record each stage. `docs/conventions.md` records
  the module convention and the Palomar layout.
- PLAN-18's single-tape theorems and their documentation are unchanged. Milestone 19 adds a
  statement surface; it proves nothing new about graphs.

## 10. Final acceptance criteria

The milestone is complete when:
1. every `.lean` file of the snapshot is a module; this repository
   builds `--wfail` clean with protected statements unchanged; the snapshot builds `GraphIso`
   and `Solution` `--wfail` clean, and `Challenge` has only its deliberate `sorry` warnings;
2. Appendix A's and Appendix B's statements (as approved) are proved in the library, from
   `gi_tm0_vertices` and `gi_coset_tm0_vertices`, with only the three axioms;
3. the snapshot's `Challenge.lean` imports Mathlib only, contains the statement's definitions
   byte for byte, and `lake comparator` (sandboxed, Lean and NanoDa) accepts the snapshot;
4. the README and `formalization.yaml` state exactly what is proved, with the divergences;
5. the user has confirmed the metadata (D5). Publication and submission are theirs (§8).

## Appendix A: the proposed statement

Checked to elaborate with the pinned Mathlib (only the `sorry` warning). In the library, the
definitions go in `GraphIso/Palomar/Statement.lean` and the theorem is proved as
`gi_singleTape_proof`. In the snapshot, this text, followed by Appendix B's definitions and
theorems, is `Challenge.lean`.

```lean
module

public import Mathlib.Computability.TuringMachine.PostTuringMachine
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Nat.Bits
public import Mathlib.Data.Nat.Log

@[expose] public section

namespace GraphIsoPalomar

/-- The symbols of the input and output words. -/
inductive Sym where
  /-- A binary digit. -/
  | digit (b : Bool)
  /-- The end of a number. -/
  | endNum
  /-- Before each element of a list. -/
  | cons
  /-- The end of a list. -/
  | nil
  /-- The left end of a word on the tape. -/
  | lmark
  /-- The right end of a word on the tape. -/
  | rmark
  /-- The answer "isomorphic". -/
  | yes
  /-- The answer "not isomorphic". -/
  | no

/-- A natural number: its binary digits, least significant first, without trailing zeros
(`Nat.bits`), then `endNum`. -/
def natWord (k : ℕ) : List Sym :=
  (Nat.bits k).map Sym.digit ++ [Sym.endNum]

/-- A list of words: each after `cons`, then `nil`. -/
def listWord (ws : List (List Sym)) : List Sym :=
  (ws.map (Sym.cons :: ·)).flatten ++ [Sym.nil]

/-- The neighbours of `u` in `G`, in increasing order. -/
def nbrs {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u : Fin n) : List ℕ :=
  ((List.finRange n).filter fun v => G.Adj u v).map (·.val)

/-- A graph on `Fin n`: the list, from the last vertex `n - 1` down to `0`, of the neighbour
lists. -/
def graphWord {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : List Sym :=
  listWord ((List.finRange n).reverse.map fun u => listWord ((nbrs G u).map natWord))

/-- **The input**: `n`, then `G`, then `H`, between the marks. -/
def input {n : ℕ} (G H : SimpleGraph (Fin n)) [DecidableRel G.Adj] [DecidableRel H.Adj] :
    List Sym :=
  Sym.lmark :: (natWord n ++ graphWord G ++ graphWord H) ++ [Sym.rmark]

/-- **The output**: the answer between the marks. -/
def output (b : Bool) : List Sym :=
  [Sym.lmark, if b then Sym.yes else Sym.no, Sym.rmark]

/-- **Graph isomorphism is decided by a single-tape Turing machine in quasipolynomial time.**
There are a Turing machine `M` of mathlib's single-tape model `Turing.TM0`, with a finite tape
alphabet `Γ` and finitely many states, an injective map `ι` of the symbols above into `Γ`, none of
them blank, and a constant `c`, such that for all `n` and all simple graphs `G`, `H` on `Fin n`:
started (in its start state `default`, head on the first symbol, blanks elsewhere) on the tape
`ι (input G H)`, `M` makes at most `2 ^ (c (⌊log₂ n⌋ + 1) ^ 8)` transitions and halts (`step`
returns `none`) with the tape `ι (output b)`, head on its first symbol and blanks elsewhere, where
`b = true` exactly when `G` and `H` are isomorphic. -/
theorem gi_singleTape :
    ∃ (Γ Λ : Type) (_ : Inhabited Γ) (_ : Inhabited Λ), Finite Γ ∧ Finite Λ ∧
      ∃ (M : Turing.TM0.Machine Γ Λ) (ι : Sym ↪ Γ) (c : ℕ), (∀ s, ι s ≠ default) ∧
        ∀ (n : ℕ) (G H : SimpleGraph (Fin n)) [DecidableRel G.Adj] [DecidableRel H.Adj],
          ∃ b : Bool, (b = true ↔ Nonempty (G ≃g H)) ∧
            ∃ k ≤ 2 ^ (c * (Nat.log 2 n + 1) ^ 8), ∃ q : Λ,
              (flip bind (Turing.TM0.step M))^[k]
                  (some (Turing.TM0.init ((input G H).map ι))) =
                some ⟨q, Turing.Tape.mk₁ ((output b).map ι)⟩ ∧
              Turing.TM0.step M ⟨q, Turing.Tape.mk₁ ((output b).map ι)⟩ = none := by
  sorry

end GraphIsoPalomar
```

Why it says what it claims:
- **Quantifier order.** `M`, `ι` and `c` are chosen before `n`, `G` and `H`, so one machine works
  for all graphs.
- **No cheating through `ι`.** The input map `ι` is fixed and injective, so it cannot carry the
  answer. The output words for `true` and `false` differ at their second symbol, which is not
  blank, so the final tape determines `b`. `b` itself is pinned by `b = true ↔ Nonempty
  (G ≃g H)`.
- **The bound is not trivially satisfiable.** It is quasipolynomial in `n`, so brute force over
  the `n!` permutations does not meet it for any fixed `c`.
- **The machine model.** The step relation is mathlib's `TM0.step`, counted transition by
  transition, and halting is `step = none`.
- **Malformed inputs.** Words outside the image of `input` are not constrained, as stated in the
  informal account.

## Appendix B: the proposed coset statement (D4)

The statement file gains two imports and, before `end GraphIsoPalomar`, the definitions and
theorems below. `Sym`, `natWord`, `listWord` and `input` are Appendix A's. The merged file
elaborates with the pinned Mathlib; the only warnings are the deliberate `sorry`s. Kernel
`decide` in scratch shows that `permWord` and `cosetWord`, mapped to the stack alphabet, give
exactly `ser Ty.giCoset` on a 3-cycle of `Fin 3` with generators `[swap, 3-cycle]`, and on
`none`. Listing the images from `0` upward gives a different word.

```lean
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.GroupTheory.Perm.Basic
```

```lean
/-- A permutation `σ` of `Fin n`: the images `σ i`, then the inverse images `σ⁻¹ i`, each as a
list of numbers, for `i` from `n - 1` down to `0`. -/
def permWord {n : ℕ} (σ : Equiv.Perm (Fin n)) : List Sym :=
  listWord ((List.finRange n).reverse.map fun i => natWord (σ i)) ++
    listWord ((List.finRange n).reverse.map fun i => natWord (σ.symm i))

/-- **The output of the coset machine**, between the marks: `no` when there is no isomorphism;
otherwise `yes`, an isomorphism `τ`, and the list of generators `gs`. -/
def cosetWord {n : ℕ} : Option (Equiv.Perm (Fin n) × List (Equiv.Perm (Fin n))) → List Sym
  | none => [Sym.lmark, Sym.no, Sym.rmark]
  | some (τ, gs) =>
    Sym.lmark :: Sym.yes :: (permWord τ ++ listWord (gs.map permWord)) ++ [Sym.rmark]

/-- **The coset machine's output determines its answer**: `cosetWord` is injective. -/
theorem cosetWord_injective (n : ℕ) : Function.Injective (cosetWord (n := n)) := by
  sorry

/-- **All isomorphisms of two graphs, by a single-tape Turing machine in quasipolynomial time.**
There are a Turing machine `M` of mathlib's single-tape model `Turing.TM0`, with a finite tape
alphabet `Γ` and finitely many states, injective maps `ιin`, `ιout` of the symbols into `Γ`, none
of them blank, and a constant `c`, such that for all `n` and all simple graphs `G`, `H` on
`Fin n` there is an answer `r` with:
* `r = none` exactly when `G` and `H` are not isomorphic;
* if `r = some (τ, gs)`, a permutation `φ` of `Fin n` underlies an isomorphism `G ≃g H` exactly
  when `τ⁻¹ * φ` lies in the subgroup generated by `gs`: the isomorphisms form the left coset of
  that subgroup by `τ`;
* started (in its start state `default`, head on the first symbol, blanks elsewhere) on the tape
  `ιin (input G H)`, `M` makes at most `2 ^ (c (⌊log₂ n⌋ + 1) ^ 8)` transitions and halts with
  the tape `ιout (cosetWord r)`, head on its first symbol and blanks elsewhere. -/
theorem gi_coset_singleTape :
    ∃ (Γ Λ : Type) (_ : Inhabited Γ) (_ : Inhabited Λ), Finite Γ ∧ Finite Λ ∧
      ∃ (M : Turing.TM0.Machine Γ Λ) (ιin ιout : Sym ↪ Γ) (c : ℕ),
        (∀ s, ιin s ≠ default) ∧ (∀ s, ιout s ≠ default) ∧
        ∀ (n : ℕ) (G H : SimpleGraph (Fin n)) [DecidableRel G.Adj] [DecidableRel H.Adj],
          ∃ r : Option (Equiv.Perm (Fin n) × List (Equiv.Perm (Fin n))),
            (r = none ↔ IsEmpty (G ≃g H)) ∧
            (∀ τ gs, r = some (τ, gs) → ∀ φ : Equiv.Perm (Fin n),
              (∃ e : G ≃g H, e.toEquiv = φ) ↔ τ⁻¹ * φ ∈ Subgroup.closure {g | g ∈ gs}) ∧
            ∃ k ≤ 2 ^ (c * (Nat.log 2 n + 1) ^ 8), ∃ q : Λ,
              (flip bind (Turing.TM0.step M))^[k]
                  (some (Turing.TM0.init ((input G H).map ιin))) =
                some ⟨q, Turing.Tape.mk₁ ((cosetWord r).map ιout)⟩ ∧
              Turing.TM0.step M ⟨q, Turing.Tape.mk₁ ((cosetWord r).map ιout)⟩ = none := by
  sorry
```

Why it says what it claims, beyond Appendix A's reasons:
- **Two embeddings.** The coset machine writes output symbols (`out …`), which are distinct from
  the input symbols it reads (`inp …`), so it needs its own output embedding. Both embeddings
  are fixed before the input.
- **The tape determines `r`.** `cosetWord_injective` holds, and `ιout` is injective. So the
  final tape determines `r`, and `r` is constrained by the two clauses.
- **`τ` is an isomorphism.** Take `φ = τ`: then `τ⁻¹ * τ = 1` lies in every subgroup, so the
  iff makes `τ` underlie an isomorphism. The iff then says the isomorphisms are exactly
  `τ ⟨gs⟩`. This is `gi_coset_tm0_vertices`'s coset equality, stated without pointwise
  notation.
- **The empty generator list is allowed.** Its closure is trivial, so then `τ` is the only
  isomorphism.
