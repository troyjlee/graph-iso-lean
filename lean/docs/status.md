# Status (29 October 2026)

## Milestone 19, stage 19e: the submission snapshot and local verification (`PLAN-19.md` §7)

Stage 19d is done (`1066802`). This stage prepares the public snapshot and verifies it locally.
Nothing is pushed, published or submitted, and no statement or proof changes. Publication,
preflight and submission (stage 19f) are the author's, after the author confirms the metadata
(D5).

**Escalation follow-up (29 October).** The third audit kept the reference-check finding open:
line-by-line parsing still missed multiline and blockquote reference definitions, unquoted or
uppercase HTML attributes, and links between unequal backtick runs. Submission preparation
replaces that parser with pinned markdown-it-py (CommonMark, with tables), followed by Python's
HTML attribute parser, and checks unused and duplicate reference definitions too. URL escapes
are decoded before checking that a local target stays inside the snapshot. Lean comments are
parsed as whole documents, excluding string literals. The regression checks cover the reported
bypasses, images, multiline inline links, escaped destinations, code examples and containment.
This is a local-file check: it does not validate external URLs, fragment identifiers or arbitrary
Markdown extensions. Invalid link-like text is treated as text, following CommonMark.

The snapshot also installs a manually dispatched preflight workflow pinned to PalomarSubmission
`14aa8d6b3c2f14a8540605e37144560b9a00e7e7`, with `mode: full`, the standard execution profile,
`project_path: lean` and `comparator_config_path: lean/comparator.json`. The automation
disclosure now identifies Claude Opus 5.5 from the saved project sessions and includes Codex's
submission-preparation work. The loop totals at the close of 19e are corrected to 61 loops,
57 approved, 2 escalated, 2 abandoned, and 89 audit rounds. Milestones 1–6, before the loop,
were reviewed by Codex (gpt-6-astra at maximum effort), the author passing the messages
between the agents by hand (the author's account, 29 October); the README, the notes and the
metadata say so. No Lean statement or proof changes.

**D5 confirmed (29 October).** The author reviewed `palomar/formalization.yaml` and removed its
`DRAFT` line, so `palomar-snapshot.sh` now writes final snapshots of a committed tree. Stage 19f
(publication, hosted preflight, submission) remains the author's.

Follow-up validation: all 14 command-level controls pass in a disposable committed repository,
including a final-mode baseline, the reported bypasses, a multiline Lean-comment reference,
untracked-file exclusion, containment, literal code, dirty/staged source rejection, and the
draft guard. The parser regression suite passes. All 430 Lean files and the four build and
Comparator configuration files match the previously verified snapshot byte for byte. The
current Palomar source scanner checks all 430 files without an issue; its metadata validator
and the template's metadata check pass. Preflight workflow inputs and the matching full commit
pins are checked locally. These checks do not constitute a hosted Palomar preflight or a new
independent audit round.

1. **Palomar's rules, re-read** (29 October 2026: PalomarPolicy `28bd48b`, PalomarTemplate
   `2891de4`, PalomarSubmission `a93fc88`, and the submission protocol). Beyond §1:
   - a Lake project below the repository root is allowed (`project_path`). The snapshot keeps
     the project in `lean/`, with the licence at the root and `formalization.yaml` in `lean/`,
     its default place;
   - the project's toolchain must equal Mathlib's at the pinned revision: both are
     `v4.35.0-rc2`;
   - Palomar judges with the toolchain's own `lake comparator`: Lean's kernel and NanoDa,
     then con-ron (advisory). The preflight profile `palomar-standard-v1` is a GitHub-hosted
     `ubuntu-24.04` x86_64 runner with at least 14 GiB and 19800 s;
   - sources have the types `paper`, `book`, `web discussion`, `folklore`, `original-proof` or
     `other`; MSC2020 has no `20B40` (the plan's draft), so the draft uses `20-08`.
2. **References to unpublished files** are resolved in this repository. The plans cite the
   papers by arXiv identifier or URL and describe the unpublished files in words (`3e9dc6d`,
   committed outside the loop); this stage does the same in `docs/conventions.md`,
   `docs/status.md`, `docs/theorem-map.md`, `scripts/build-seq.sh`, and the docstrings of
   `GraphIsoChecks/Exec.lean`, `MainM5.lean`, `MainSimsSteps.lean` (16–60 GB, as measured under
   `scripts/guard.sh`; Babai's 2017 note by title and date).
3. **The snapshot** (`scripts/palomar-snapshot.sh`, with `scripts/palomar-snapshot.py`, which
   documents every step and check; `docs/conventions.md`). It writes the tracked files (never an
   untracked one) except the audit reports and evidence, the loop's state and the paper PDFs; a
   final snapshot requires the published files to be committed. It adds the root `README.md` and
   `LICENSE` and `lean/formalization.yaml` from `palomar/`, and generates `Challenge.lean` (152
   lines: `Statement.lean`'s text and the three theorems of the appendices, `by sorry`),
   `Solution.lean`, `comparator.json` and the lakefile's libraries. Its checks: Palomar's source
   rules; `Statement.lean`, without its docstring, equal to the appendices' imports and
   definitions; `Challenge.lean` beginning with `Statement.lean`'s text; `sorry` only there,
   once per theorem; CommonMark link/image destinations and reference definitions, and HTML
   `href`/`src` attributes, resolved inside the snapshot (Markdown files and Lean comments,
   relative to the document, URL escapes decoded, queries and fragments dropped; backticked
   paths as the documents write them),
   except the
   paths listed with their reason as files of Mathlib or Palomar's repositories or files that a
   plan proposed and did not create (an unused exception fails too); the metadata no longer a
   draft. Round 1's audit found three defects here, fixed in round 2: under macOS's Bash 3.2 the
   script failed without `--draft` (an empty array under `set -u`); it copied untracked files of
   `lean/`; and its reference check missed links with a fragment, only listed paths that exist
   nowhere, and resolved links by file name anywhere. Round 2's audit found further forms it
   missed (links with a title, reference-style links, targets outside the snapshot); round 3
   attempted to parse more CommonMark forms and HTML attributes, rejected unparseable link-like
   text, and enforced containment, but its audit still found missed destinations. The follow-up
   above replaces that parser and corrects its claimed coverage. Negative controls in a scratch
   clone: a confirmed-metadata final snapshot under Bash 3.2 passes; an untracked scratch file
   and an untracked local settings file under `lean/` are not copied; a link to an unpublished file
   with a fragment, a link to a missing file, a relative link valid only from another
   directory, and a backticked path that exists nowhere each fail; so do, in round 3, a titled
   link and a reference definition to an unpublished file, titled, angle-bracket and
   reference links to missing files, a link and a backticked path leaving the snapshot, an HTML
   `href` to an unpublished file, an unterminated title, and a link in a Lean comment to a
   missing file, while a titled link, a root-relative link and an anchor that resolve pass.
   The templates are in `lean/palomar/`, not at the repository root as the plan said, because
   the loop commits only `lean/`.
4. **The informal account**: the root `README.md` (the theorems in plain language, the model,
   the encodings, what is not claimed, the proof route, the sources, how the work was made,
   building and checking), `docs/formalization-notes.md` (the results and where they are
   stated, the trust surface, the milestones and their sources, the divergences, the production
   and checking process with counts, reproduction), and `Statement.lean`'s docstring, which now
   names the snapshot script. A brief search found no earlier formalization of Babai's
   algorithm; the README says that it was only brief.
5. **The metadata draft** (`palomar/formalization.yaml`, D5). Every field is filled, and the
   file starts with a `DRAFT` line, so `palomar-snapshot.sh` writes only `--draft` snapshots
   until the author removes it. The author confirms: authors and responsible maintainers (the
   draft names the author); the models (Claude Opus 5.5 via Claude Code; Codex's
   `gpt-6-astra`); the review status `agent-reviewed`; the sources and their relationships
   (Babai's paper and note, Pyber and Helfgott–Bajpai–Dona `adapts`, Luks `background`); the
   classification (`cs.DS`, `cs.CC`, `math.CO`, `math.GR`; `68Q25`, `05C60`, `20-08`, `20B15`,
   `68V20`); and the licence, Apache-2.0.
6. **Local verification** of a `--draft` snapshot of this round's tree:
   - the snapshot's checks pass, and `--build` builds `GraphIso` and `Solution` with warnings
     as errors and `Challenge` with exactly its three `sorry` warnings;
   - the template's `check-lean-sources.py` passes, and `validate-formalization.rb` finds no
     template value;
   - `lake comparator --inadvisably-no-sandbox` on macOS accepts (91 s, 3.8 GB);
   - **in a Linux container** (Docker on colima: `ubuntu:24.04`, aarch64, 8 CPUs, 16 GiB;
     `bubblewrap` 0.9.0), from the snapshot without `.lake`: Mathlib's cache (8915 files, a few
     minutes; one transient download failure, retried); `lake build --wfail Solution` from
     scratch, 179 s, container peak 4.5 GB; `lake comparator`, sandboxed, with Palomar's
     configuration (NanoDa and con-ron added as external kernels, as the template's
     `verify-comparator.sh` does): Lean's kernel, NanoDa and con-ron accept, 143 s, container
     peak 3.35 GB (page cache included); with `--paranoid` also Lean's paranoid checker,
     lean4lean and con-leche accept, 381 s. The export of the three theorems' closure has 42242
     declarations, 657 MB of NDJSON (106 MB compressed), written in 20 s at 4.0 GB. The sandbox
     needs `/run/user` and `/home` to exist in the container. The preflight's x86_64 runner has
     4 CPUs, so its times will be longer, but these leave a wide margin within 19800 s.

## Milestone 19, stage 19d: the Palomar coset statement (`PLAN-19.md` §6)

Stage 19c is done (`cb29dd5`). This stage states the single-tape coset theorem with definitions
that use Mathlib only (D4), and proves it and the injectivity of its output words. No existing
statement changes; the two new theorems are protected targets.

1. **The statement's definitions** (`GraphIso/Palomar/Statement.lean`, now 100 lines, Mathlib
   only): Appendix B's two imports and its definitions `permWord` and `cosetWord`, verbatim.
   Without the module docstring, the file is Appendix A's imports, Appendix B's imports,
   Appendix A's definitions and Appendix B's definitions, line for line, then
   `end GraphIsoPalomar`.
2. **The encoding lemmas, generic** (`GraphIso/Palomar/Bridge.lean`): `Writes f g` says that a
   map `f` of the symbols writes digits, `endNum`, `cons` and `nil` as `g` writes the library's
   `bit b`, `nd`, `tag cons`, `tag nil`. Under it, the words of numbers, lists, graphs, valid
   permutation data (`Writes.permWord_map`: the forward and inverse arrays, each from its last
   entry, by `PermData.fwd_eq_ofFn` and `inv_eq_ofFn`) and valid generators
   (`Writes.gensWord_map`) map to their serializations, and the input word to the input tape
   (`Writes.input_map`). Stage 19c's lemmas are now these lemmas at `symbolEmbedding`, with the
   same statements.
3. **The coset machine's embeddings** into `giCosetTM0`'s tape alphabet: `cosetIn` (as
   `symbolEmbedding`) and `cosetOut` (the digits, `endNum`, `cons`, `nil` to the output symbols,
   `yes` and `no` to `tag some` and `tag none`, the marks to the marks), both injective and never
   blank. One embedding cannot serve both: the machine reads input symbols and writes output
   symbols.
4. **The output bridge** (`cosetWord_map`): the answer is the denotation `cosetData n r` of the
   output data `r`, and for valid data `cosetWord (cosetData n r)` maps to
   `encodeOut (ser Ty.giCoset r)`.
5. **The theorems.** `cosetWord_injective_proof` (Appendix B's `cosetWord_injective`): the words
   of numbers, of lists of the words of a prefix code, and of permutations are prefix codes
   (`PrefixCode`), since a number's word ends at its first `endNum`, `Nat.bits` is injective
   (through `toBits` and `ofBits`), and the images determine a permutation.
   `gi_coset_singleTape_proof` (Appendix B's `gi_coset_singleTape`), from
   `gi_coset_tm0_vertices`: `r = cosetData n r₀`; the coset equality
   `{φ | ∃ e, e.toEquiv = φ} = τ • ⟨gs⟩` gives the iff through `mem_leftCoset_iff'` and
   `GensData.denote`. All three theorems use only `propext`, `Classical.choice`, `Quot.sound`.
6. **Comparator** (scratch, as in 19c, with the three theorems `gi_singleTape`,
   `cosetWord_injective`, `gi_coset_singleTape`): accepted (87 s, 3.8 GB). Rejected when the
   challenge's `permWord` lists the images from `0` upwards ("Const does not match between
   challenge and target 'GraphIsoPalomar.permWord'"), and when its coset clause has
   `φ * τ⁻¹` for `τ⁻¹ * φ` ("Challenge and solution theorem statement do not match:
   'GraphIsoPalomar.gi_coset_singleTape'").
7. **Checks** (`GraphIsoChecks/Palomar.lean`): the word of the 3-cycle `0 ↦ 1 ↦ 2 ↦ 0`; the
   output words of the 3-cycle with the generators `[swap, 3-cycle]`, and of `none`, against
   the output tapes, symbol by symbol (`wordEq`, now for any alphabet); the coset theorem on the
   two paths (`some (τ, gs)`, and `τ` underlies an isomorphism, since `τ⁻¹ τ = 1`) and on a path
   and the triangle (`none`); negative controls (the images from `0` upwards give another word;
   `cosetWord none` is not the word of any `some`). A scratch copy with a wrong word for the
   3-cycle, or with invalid data for it, is rejected by the kernel.
8. **Audit**: the new declarations are in `AxiomAudit`'s principal list; it passes for 45302
   declarations in 427 modules. Its last block of names is split in two: with the new names,
   its compilation exceeded the default heartbeat budget.

## Milestone 19, stage 19c: the Palomar statement and its bridge (`PLAN-19.md` §5)

Stage 19b is done (`4fb57a8`). This stage states the single-tape decision theorem with
definitions that use Mathlib only, and proves it from `gi_tm0_vertices`. No existing statement
changes; the new theorem is a protected target.

1. **The statement's definitions** (`GraphIso/Palomar/Statement.lean`, 80 lines, imports Mathlib
   only): Appendix A's definitions verbatim (`Sym`, `natWord`, `listWord`, `nbrs`, `graphWord`,
   `input`, `output`) in namespace `GraphIsoPalomar`, with a module docstring that describes
   the encoding. Without that docstring, the file is Appendix A's text up to the end of
   `output`, line for line, then `end GraphIsoPalomar`.
2. **The bridge** (`GraphIso/Palomar/Bridge.lean`, from the plan audit's probe): the symbol
   embedding `symbolEmbedding` into `giDecTM0`'s tape alphabet, injective and never blank;
   `Nat.bits = toBits`; the words against the serializations (`natWord_map`, `listWord_map`,
   `numberList_map`, `graphWord_map`); the input word as `encodeIn p.enc` and the output word as
   `encodeOut (ser .bool b)` (`input_map`, `output_map`); and **`gi_singleTape_proof`**, with
   exactly Appendix A's statement, from `gi_tm0_vertices` with `b = isoDecide p`. Its axioms are
   `propext`, `Classical.choice` and `Quot.sound`.
3. **The layout, tried with Comparator** (§5 item 6; scratch). A copy of the Lake project gains
   two libraries: `Challenge.lean`, which is `Statement.lean`'s text followed by Appendix A's
   theorem `gi_singleTape` with `by sorry`; and `Solution.lean`, which imports
   `GraphIso.Palomar.Bridge` and proves `gi_singleTape` by `gi_singleTape_proof`. `lake
   comparator --inadvisably-no-sandbox` accepts it ("Lean default kernel accepts the solution",
   86 s, 3.8 GB). With `yes` and `no` swapped in the challenge's `output`, it rejects it: "Const
   does not match between challenge and target 'GraphIsoPalomar.output'". So the solution may
   receive the definitions from the imported statement module, under the same names, as
   planned; no generic-theorem fallback is needed. The sandboxed run with the other checkers is
   stage 19e's.
4. **Checks** (`GraphIsoChecks/Palomar.lean`, `decide +kernel`): `natWord` at `0` and `6`;
   `Nat.bits = toBits` on `0, …, 64`; the input words of the empty pairs at `n = 0, 1`, of the
   two paths and of a path and the triangle against `encodeIn p.enc`, and both output words
   against `encodeOut`, compared symbol by symbol (`wordEq`, since the work symbols of the tape
   alphabet have no decidable equality); the theorem instantiated on the two paths (`output
   true`) and on a path and the triangle (`output false`); negative controls (the output words
   differ under every injective map; a path and the triangle have different words; `graphWord`
   lists the vertices in decreasing order). A scratch copy with the digits of `6` reversed, or
   with the triangle's input compared with the paths' tape, is rejected by the kernel.
5. **Audit**: the three new modules are in `AxiomAudit`'s generated header, and the new
   declarations are in its principal list; it passes for 45231 declarations in 427 modules.
   The library root `GraphIso.lean` does not import the new modules: editing it would rebuild
   every check that imports it. `docs/conventions.md` records the Palomar layout, and
   `docs/theorem-map.md` the new statements.

## Milestone 19, stage 19b: the checks in Lean's module system (`PLAN-19.md` §4)

Stage 19a is done (`9873249`). This stage ports the checks `GraphIsoChecks`, so the whole package
is now in the module system. No definition, statement or check changes.

1. **The port** (`scripts/port-module.py`, as in 19a): the 71 check files, the audit and the root
   `GraphIsoChecks.lean`. Two new options of the script cover what the checks need beyond the
   library (`docs/conventions.md`):
   - `--meta`, on the 32 files that evaluate code at elaboration time (`run_cmd`, `#eval`,
     `#guard`): `meta import M` next to each `public import M`, since that code sees only the
     code of the modules imported with `meta import`;
   - `--bodies`, on the 67 files that reduce the library's code (`decide`, `execRuns`): `import
     all` of `Init.Data.Array.Basic`, `Init.Data.List.Sort.Basic`, `Init.Data.Nat.Bitwise.Basic`
     and `Mathlib.Data.List.Sort`. A module sees an imported definition that its module does not
     expose as an axiom, to the elaborator and to the kernel alike. Enumerating the definitions
     the library's definitions reach finds four such in core and Mathlib that matter:
     `Array.range`, `List.mergeSort`, `List.insertionSort`, `Nat.land`. In a trial build without
     these imports, 32 of `Cost`'s `decide` examples stopped at `Array.range`, and the kernel
     rejected `GraphQP`'s `execRuns` pieces.
2. **Fixes in two files**, neither changing what is checked: `TMCode` imports
   `Mathlib.Tactic.FinCases` explicitly; `MainM4`'s derived `ToExpr Tok` uses core's
   `ToExpr Unit` (a local instance of high priority), because Mathlib's `ToExpr PUnit` is `meta`
   and ordinary code may not use it.
3. **The audit is a module.** It sees a module's private declarations only if it imports that
   module directly with `import all`. Its header, generated by the new
   `scripts/gen-audit-imports.py` (`--check` reports a stale header), therefore imports the
   other 423 modules of the package that way. Its coverage check now requires every source file
   to be loaded with `import all` and its data, not merely to be in the import closure. The
   principal theorems are listed in four blocks instead of two: in the module, the first
   block's 1200-line array literal exceeded the default heartbeat budget of its elaboration.
   `scripts/build-seq.sh` reads the module-system imports (`public`, `meta`, `all`).
4. **Build**: every check module builds `--wfail`, one at a time, in about 7400 s in all. The five
   heaviest checks, before (non-module, `lake env lean` on the 19a library) and after:

   | check | before | after |
   |---|---|---|
   | `Align` | 20.4 GB, 57 s | 19.0 GB, 59 s |
   | `Case2b` | 30.1 GB, 230 s | 28.7 GB, 236 s |
   | `Case3` | 40.5 GB, 355 s | 39.1 GB, 370 s |
   | `CertProg` | 31.1 GB, 297 s | 30.6 GB, 308 s |
   | `Giant` | 33.9 GB, 317 s | 32.5 GB, 322 s |

5. **The audit before and after**: it passes, and the axiom lists of the principal theorems are
   identical. The audited declarations went from 45006 to 45031: the library's are unchanged
   (27620), the checks' went from 17386 to 17411. The 369 names only before and the 394 only
   after are all auxiliary (`_proof_N`, matchers and their splitters, `_sparseCasesOn`,
   `_simp_N`, equation lemmas); most are the same auxiliary declarations, named with the
   `_private` prefix in the module.
6. **Negative controls** (scratch):
   - 19a's sentinel (an unreferenced `private axiom m19Sentinel : False` in a copy of
     `GraphIso.TM.Ser`, compiled into an overlay of the library's build): the module audit fails
     with "`_private.GraphIso.TM.Ser.0.m19Sentinel` (in `GraphIso.TM.Ser`) depends on forbidden
     axiom …";
   - the same, with the audit's `import all GraphIso.TM.Ser` replaced by `import
     GraphIso.TM.Ser`: the enumeration no longer sees the sentinel, and the coverage check
     fails with "module GraphIso.TM.Ser is not imported here with `import all`";
   - a pilot port of `Exec` and `TMGI`: the kernel-checked run `pe_runs` (567 declarations in
     both forms, with the same axioms) is rejected when its count is changed (`86100` to
     `86099`), and when `Exec`'s serialization is sabotaged (each value's tree wrapped in an
     extra node).

## Milestone 19, stage 19a: the library in Lean's module system (`PLAN-19.md` §3)

Milestone 18 is done (`a686eb7`). Milestone 19 prepares a submission of the single-tape theorems
to the Palomar registry, whose submissions must use Lean's module system (`PLAN-19.md`). This
stage ports the library `GraphIso`; no definition or statement changes. The checks
(`GraphIsoChecks`) stay non-module until stage 19b.

1. **The port** (`scripts/port-module.py`, idempotent): all 352 library files (351 modules and
   the root `GraphIso.lean`) start with `module`, import with `public import`, and open
   `@[expose] public section` after the module docstring. Every declaration stays public and
   every definition's body stays visible to the importing modules. The convention for new files
   is in `docs/conventions.md`.
2. **Fixes in eight files**, none changing a definition or a statement:
   - explicit imports of what Mathlib's modules import privately: `Mathlib.Tactic.Linarith`
     (`nlinarith`) in `Graph/Domain`, `AltQuot/Interfaces`, `Recursion/Pullback`,
     `SoJTree/OrbitClosure`; `Mathlib.Data.Set.Finite.Lemmas` (`Set.exists_max_image`) in
     `Groups/PCore`, `Groups/Radical`;
   - `Coherent/ListProg`: `insertionSort_eq_foldr` is reproved with `List.insertionSort_nil` and
     `List.insertionSort_cons`, since Mathlib does not expose `List.insertionSort`'s body to
     modules;
   - `Main/CJohnOps`: a private `import all Mathlib.Data.List.Sort`, so that its two `decide`
     examples on `cjohnIsoD` still reduce; the examples are unchanged.
3. **Build**: the full rebuild is `--wfail` clean (7396 s, peak 40.5 GB); the 374 protected
   statements are unchanged.
4. **The axiom audit before and after** (`GraphIsoChecks/AxiomAudit.lean`, run from its
   non-module file): it passes both times, and the axiom lists of the principal theorems agree
   except that seven no longer use `Classical.choice`: `Toolkit.RunsWithin.relColProg`,
   `SoJProg.RunsWithin.twinPartProg`, `SoJProg.RunsWithin.minBigDegProg`,
   `SoJTree.RunsWithin.actOutProg`, `Main.RunsWithin.cjOfProg`, `TM.ofBits_toBits`,
   `TM.strip_eq_toBits` (each now `[propext, Quot.sound]`). In a module the same proof text can
   elaborate to a different term, because a module sees only the public import closure of its
   imports. For `ofBits_toBits`, compiled in scratch from the same import and the same text, the
   non-module term contains `Nat.instTransOrd` (core, which uses `Classical.choice`) and the
   module term does not; `simp?` reports the same lemmas in both. The audited declarations went
   from 44978 to 45006. All 28 are in the library (27592 → 27620; the checks have 17386 both
   times). Comparing the names with a scratch build of the library at `fcfceca`, the 88 names
   only before and the 116 only after are all auxiliary (`_proof_N`, equation lemmas `eq_N`,
   matcher splitters, `_sparseCasesOn`, `_simp_N`, `_f`); no other declaration is added or
   removed.
5. **Negative control** (scratch): a copy of `GraphIso.TM.Ser` (imported by no check file) with
   an unreferenced `private axiom m19Sentinel : False`, compiled into an overlay of the library's
   build. The real `AxiomAudit`, run against the overlay, fails: "`_private.GraphIso.TM.Ser.0.
   m19Sentinel` (in `GraphIso.TM.Ser`) depends on forbidden axiom …". So the non-module audit
   still enumerates private declarations of modules it reaches only through the library.

## Milestone 18, stage 18f: graph isomorphism on a single tape (`PLAN-18.md` §7)

Stage 18e is done (`4adce6b`). This stage compiles the two machines of milestone 17 to finite
single-tape machines and transfers their bounds: `GraphIso/TM/SingleTape/GI.lean`. No existing
statement changes. With it milestone 18 is complete. The library root `GraphIso.lean` now
imports the single-tape modules of 18b–18f.

**The headline in the number of vertices** (`λ = Nat.log 2`; the input tape of a graph pair `p`
is `encodeIn p.enc`, its encoding between two marks; the output tape is the framed serialization
of the answer, with the head on its first symbol and blanks elsewhere; only the transitions of
the single-tape machine are counted, including the input's preparation and the output's
cleanup):

1. **Decision** (`gi_tm0_vertices`): there is `c` such that on every graph pair `p` on `n`
   vertices the finite single-tape machine `giDecTM0` halts on `encodeIn p.enc` after at most
   `2 ^ (c (λ(n) + 1) ^ 8)` transitions with the tape `encodeOut (ser .bool (isoDecide p))`, where
   `isoDecide_iff : isoDecide p = true ↔ Nonempty (p.G ≃g p.H)`.
2. **The coset** (`gi_coset_tm0_vertices`): there is `c` such that for every pair `p` the finite
   single-tape machine `giCosetTM0` halts on `encodeIn p.enc` after at most
   `2 ^ (c (λ(n) + 1) ^ 8)` transitions with the tape `encodeOut (ser Ty.giCoset r)`, where
   `r = none ↔ IsEmpty (p.G ≃g p.H)`, and for `r = some (τ, hs)` the data are valid and the coset
   `τ • ⟨hs⟩` is exactly the set of the permutations underlying the isomorphisms `p.G ≃g p.H`.

**The machine-level statements**, in the length `L₀ = |p.enc| + 2` of the input tape
(`length_giDec_tape`, `length_giCoset_tape`): `gi_tm0` and `gi_coset_tm0`, within
`2 ^ (c (λ(L₀) + 1) ^ 8)` transitions.

3. **The machines** (`giDecTM0`, `giCosetTM0`): `compile (toFinTM2 giDecProg .inp .out) _` and
   `compile (toFinTM2 giCosetProg .inp .out) _` (stage 18e), whose finite stack alphabets are
   discharged once (18d's `finite_toFinTM2`); they have finitely many states and symbols and do not
   depend on the input.
4. **The growth** (`compile_growth`): `C (L + 2 ^ (c (λ(L) + 1) ^ 8) + 1)² ≤
   2 ^ ((C + 2 c + 4) (λ(L + 2) + 1) ^ 8)` for all `C`, `c`, `L`: the compiler's quadratic
   overhead changes the constant, not the exponent `8`. With `gi_tm`, `gi_coset_tm` and
   `compile_outputs`, the constant is `compileConst _ + 2 c + 4`.
5. **In the number of vertices** (`GraphPair.lam_tape_le`: `λ(L₀) + 1 ≤ 8 (λ(n) + 1)`, from
   `L₀ ≤ 8 (n + 1)³`; `exp_tape_le_vertices`): the constant `c 8⁸`.
6. **Checks** (`GraphIsoChecks/TMGISingleTape.lean`; theorem instantiations, the compiled GI
   machines are not run, the compiler is run on small machines in 18e's checks):
   - the machines are finite; the input tapes have `42` symbols on the two paths `pp`, `49` on
     a path and the triangle `pt`, and `5`, `10` on the empty pairs at `n = 0, 1`;
   - `gi_tm0_vertices`: `true` on `pp`, `false` on `pt` within `2 ^ (c 2⁸)` transitions,
     `true` on the empty pairs at `n = 0, 1` within `2 ^ c`; `gi_coset_tm0_vertices`: `some` on
     `pp`, `none` on `pt` within `2 ^ (c 2⁸)`, `some` on the empty pairs within `2 ^ c`;
   - `gi_tm0`: `true` on `pp`, `false` on `pt` within `2 ^ (c 6⁸)`; `gi_coset_tm0`: `some` on
     `pp`, `none` on `pt` within `2 ^ (c 6⁸)` (`λ(42) = λ(49) = 5`);
   - **negative controls:** no output `true` on a path and the triangle within any bound; the
     input tape's length is neither the encoding's length nor the number of vertices;
     `λ(L₀) + 1 ≤ λ(n) + 1` fails on `pp`.

**Not claimed:** the claims concern simple graphs presented by the encodings `p.enc`; malformed
strings are not rejected; no canonization, no binary-alphabet normalization, no optimal
constants.

## Milestone 18, stage 18e: the compiler from stack machines to single-tape machines (`PLAN-18.md` §6)

Stage 18d is done (`bb4cc84`). This stage composes the input adapter, the counted simulations of
18c and 18d, and the output adapter into one finite single-tape machine:
`GraphIso/TM/SingleTape/IO.lean` and `GraphIso/TM/SingleTape/Compile.lean` (mathlib only). No
existing statement changes. The library root imports the single-tape modules at stage 18f.

**The transfer theorem** (`compile_outputs`): for a bundled stack machine `tm` (mathlib's
`FinTM2`) whose stack alphabets are finite (`hΓ`), if `TM2OutputsInTime tm x (some y) T`, then
`TM0OutputsInTime (compile tm hΓ) (encodeIn x) (encodeOut y) (compileConst tm * (|x| + T + 1)²)`,
with `compileConst tm = 4 (2 s² + 3 s + 6)`, `s = tmActs tm`. The machine and the constant depend
only on `tm`; the degree is `2`; every transition is counted, including the input's preparation
and the output's cleanup; the input and output stacks may differ.

1. **Mirrored work tapes and simulated statements** (`IO.lean`): `tapeMirror`, `workTape`;
   `simStmt f h q` runs a statement over the work symbols on the mirrored tape (moves reversed,
   `halt` replaced by a jump to `h`), computing exactly the image of its result
   (`stepAux_simStmt`), so runs map to runs of the same length (`steps_sim`); supports
   (`supportsStmt_simStmt`); scanning loops take exactly one step per symbol (`scan_steps`).
2. **The compiled machine** (`compM tm`, labels `Lab`: `inStart`, `inScan`, `inMark`, `sim l`,
   `outStart`, `outScan`):
   - **input** (`input_steps`): `|x| + 3` steps from `TM1.init (encodeIn x)` to mathlib's initial
     simulator configuration `TM1.init (trInit tm.k₀ x)`, mirrored (`inMark_tape`); mathlib's
     `trCfg_init` relates it to `initList tm x` (18d's `initList_eq_init`). The simulator's stacks
     grow to the left, so the input needs no reversal;
   - **simulation**: mathlib's `TM2to1.tr tm.m` on the mirrored tape, counted by `tr2_outputs`;
   - **output** (`output_steps`): `|y| + 2` steps from the simulator's halted configuration to
     `Tape.mk₁ (encodeOut y)`, halting; when `tm` halts every stack but the output stack is
     empty, so the simulator's tape holds exactly the output stack (`halt_tape`).
   So `compM tm` runs within `(2 s² + 3 s + 6) (|x| + T + 1)²` steps (`compM_run`, with
   `|y| ≤ |x| + s T`).
3. **Finite control**: every statement of `compM tm` has size at most `4` (`compM_size`;
   mathlib's simulator's statements at most `3`, 18d's `stmtSize_tr`), and the adapter labels with
   the simulator's support support it (`compM_supports`, from 18d's `tr_supports_univ`); the
   alphabet is finite (`finite_cSym`). So `compile tm hΓ = FinTM0.ofTM1 (compM tm) _`, and
   `ofTM1_outputs` gives the factor `4`.
4. **Checks** (`GraphIsoChecks/TMSingleTape.lean`, no GI imports; the compiled machines are run
   by the kernel and observed through the cells around the head):
   - the reversal machine of 18c, compiled: on `encodeIn [true, false]` it halts after exactly
     `63` transitions with the head on the left mark of `encodeOut [false, true]` and blanks
     around; `compile_outputs` gives the bound `80 · 36`, and with the run the timed output in
     exactly `63` (`rev_exact`); the empty input gives the empty output after `17`;
   - the negation machine of 17a (`negM`, input stack `0`, output stack `2`), compiled: for every
     input `l`, `compile_outputs` gives `encodeOut (l.map not)` within `44 (13 |l| + 10)²`
     (`neg_outputs`); run by the kernel: the empty output after `39` transitions, `[false]` on
     `[true]` after `101`;
   - **negative controls:** the reversal is not done within `62` transitions and outputs nothing
     else; the negation's output on `[true]` is not `[true]`.

**Not covered:** the GI machines on one tape (18f).

## Milestone 18, stage 18d: machines with local state on one tape, counted, with finite control (`PLAN-18.md` §5)

Stage 18c is done (`7dd64ee`). This stage counts the steps of mathlib's translation `TM1to0.tr`
of a machine with one tape and local state (`TM1`) into a single-tape machine (`TM0`), restricts
it to finitely many states, and composes it with stage 18c, for every `FinTM2` with finite stack
alphabets and for the project's compiled stack programs: `GraphIso/TM/SingleTape/TM1Sim.lean` and
`GraphIso/TM/SingleTape/Sim.lean` (mathlib only), `GraphIso/TM/SingleTape/Programs.lean` (also
`GraphIso.TM.Machine`). No existing statement changes. The library root imports the single-tape
modules at stage 18f.

1. **Statement size** (`stmtSize q`): the most moves and writes on a path through `q`, plus one
   for the final `goto` or `halt`, which the translation executes as a write of the scanned
   symbol.
2. **One step, counted** (`stepAux_steps`, `tr1_simIn`): a step of the `TM1` machine is between
   `1` and `stmtSize` transitions of the translation, between configurations related by
   mathlib's `TM1to0.trCfg`; with every statement of size at most `s`, `N` steps are at most
   `N s` transitions (`tr1_run`); a halted configuration translates to one where the translation
   halts (`tr1_halt`).
3. **Finite control** (`Reachable`, `restrict`): a single-tape machine restricted to the states
   reachable from its start state has the same runs (`restrict_steps`) and halts
   (`restrict_halt`); if a finite set of states contains the start state and is closed under
   transitions (mathlib's `TM0.Supports`), the reachable states are finite (`finite_reachable`).
4. **The finite machine** (`FinTM0.ofTM1 M h`): for a `TM1` machine with a finite alphabet,
   finitely many local states and a finite set of labels supporting it (`h : ∃ S,
   TM1.Supports M S`), the translation restricted to its reachable states, finite by mathlib's
   `TM1to0.tr_supports`. The finiteness is a proposition (`Finite`): mathlib's statement sets are
   classical, and no enumeration of the states is computed or needed; the transition function is
   the translation's. **`ofTM1_outputs`**: if `M` runs from `TM1.init l` to a halted
   configuration with the tape `Tape.mk₁ l'` in `N` steps, every statement of size at most `s`,
   then `TM0OutputsInTime (FinTM0.ofTM1 M h) l l' (N s)`.
5. **The composition with stage 18c** (`Sim.lean`): every statement of mathlib's simulator
   `TM2to1.tr M` has size at most `3` (`stmtSize_trNormal`, `stmtSize_tr`), so `N` steps of a
   stack machine from stacks of length at most `B` are at most `3 N (1 + s (2 (B + s N) + 2))`
   single-tape transitions of `TM1to0.tr (TM2to1.tr M)`, between configurations related by
   `TrCfg` and `trCfg` (`sim_run`); for a bundled machine with `TM2OutputsInTime tm x (some y) T`,
   within `3 (2 s² + 2 s + 1) (T + 1) (|x| + T + 1)` (`sim_outputs`, `s = tmActs tm`).
6. **The finite simulator** (`simTM0 tm hΓ`): the labels of `tm` support its program
   (`supportsStmt_univ`), so mathlib's `TM2to1.tr_supports` gives a finite support of the
   simulator (`tr_supports_univ`), and `TM1to0.tr_supports` (through `FinTM0.ofTM1`) finitely many
   reachable states; the alphabet `Γ'` is finite for finite stack alphabets (`finite_Γ'`); the start
   label is `normal tm.main` (`mainInhabited`) and `initList tm x = TM2.init tm.k₀ x`
   (`initList_eq_init`). **`simTM0_outputs`**: if `TM2OutputsInTime tm x (some y) T`, the finite
   simulator runs from mathlib's initial simulator tape `trInit tm.k₀ x` to a halting configuration
   whose tape holds the stacks of `haltList tm y` (`TrCfg`'s layout) within
   `3 (2 s² + 2 s + 1) (T + 1) (|x| + T + 1)` transitions. The framed input and output are stage
   18e.
7. **The project's machines** (`Programs.lean`): the stack alphabets of `toFinTM2 prog kin kout`,
   the program's symbols and the return labels, are finite (`finite_toFinTM2`); the local state is
   finite in every `FinTM2`. **`exec_simTM0`**: a run of `main` in `n` steps from the input
   configuration of `l` to the output configuration of `l'` gives a halting run of the finite
   simulator within `3 (2 s² + 2 s + 1) (n + 2) (|l| + n + 2)` transitions.
8. **Checks** (`GraphIsoChecks/TM1Sim.lean`, no GI imports): `walkM` (alphabet and local state
   `Bool`, one label: a load, a branch, a write and a move right, or a move left, a write and a
   halt; statements of size `3`, supported by its label):
   - on `[true, true]`: `3` steps, and the translation exactly `9 = 3 · 3` transitions to the
     same tape, halting (kernel reduction); the restriction to the reachable states takes the
     same `9` transitions; `tr1_run` instantiated;
   - on `[false]`: the output `[true, false]` within `3` transitions by `ofTM1_outputs`, and run
     by the kernel;
   - **negative controls:** not halted after `8` transitions; no other output; a trailing blank
     is invisible (`[true]` is the same output as `[true, false]`).
9. **Checks of the composition** (`GraphIsoChecks/TMSim.lean`, no GI imports; the finite
   simulators run by the kernel and observed through their tape cells):
   - the reversal machine of 18c: `simTM0 revTM _` halts after exactly `37` transitions from
     `trInit true [true, false]`, the input stack empty and the output stack `true, false` from
     the bottom, within the bound `3 · 312` of `simTM0_outputs` (instantiated);
   - the compiled negation program of 17a (`negM = toFinTM2 negProg 0 2`, finite by
     `finite_toFinTM2`): `simTM0 negM _` halts after exactly `161` transitions on `[true, false]`
     with the output stack holding `[false, true]`, within `18360` (`exec_simTM0` instantiated
     with the program's `32` steps); `25` on `[]`;
   - **negative controls:** neither halts earlier; the stacks are stored bottom first.

**Not covered:** the adapters and the compiler (18e), the GI machines on one tape (18f).

## Milestone 18, stage 18c: the simulation of stack machines on one tape, counted (`PLAN-18.md` §4)

Stage 18b is done (`79d7902`). This stage counts the steps of mathlib's simulation of a stack
machine (`TM2`) by a machine with one tape and local state (`TM1`), `TM2to1.tr`, with mathlib's
machine and configuration relation `TM2to1.TrCfg` unchanged: `GraphIso/TM/SingleTape/TM2Sim.lean`
(mathlib only). No existing statement changes. The library root imports the single-tape modules
at stage 18f (stage 18b's note).

1. **Stack actions** (`acts q`): the number of stack actions on the longest path through `q`,
   every branch included. A step changes each stack's length by at most `acts` of the executed
   statement (`stepAux_length_le`, `step_length_le`); after `N` steps from stacks of length at
   most `B`, every stack has length at most `B + s N` (`run_length_le`).
2. **The shuttles** (`go_steps`, `ret_steps`): travelling `n` cells towards a stack's top, and
   back to the bottom mark, are exactly `n` steps each (an empty stack: `n = 0`).
3. **One step** (`trNormal_steps`, `tr2_step`): from stacks of length at most `B`, with every
   statement having at most `s` stack actions, a step of the stack machine is simulated by at
   most `1 + s (2 (B + s) + 2)` steps, from any `TrCfg`-related configuration to a
   `TrCfg`-related one: one step to start, and per stack action at most `B + s` steps out, one
   at the top, at most `B + s` back and one to continue. Several stack actions in one statement
   are covered.
4. **Runs** (`tr2_run`): `N` steps from stacks of length at most `B` within
   `N (1 + s (2 (B + s N) + 2))` steps.
5. **Bundled machines** (`tmActs tm`: the largest `acts` of a statement of a `FinTM2`, over its
   finite labels; `tr2_outputs`): if `TM2OutputsInTime tm x (some y) T`, then from every
   configuration `TrCfg`-related to `initList tm x`, the simulator reaches one `TrCfg`-related to
   `haltList tm y` within `(2 s² + 2 s + 1) (T + 1) (|x| + T + 1)` steps (`run_bound_le`), and
   `|y| ≤ |x| + s T` (`length_out_le`). The input and output stacks may differ.
6. **Checks** (`GraphIsoChecks/TM2Sim.lean`, no GI imports; the simulator's configurations are
   observed through its tape cells):
   - the reversal machine `revTM` (input stack `true`, output stack `false`) outputs
     `[false, true]` on `[true, false]` in exactly `3` steps (kernel); its simulator, from
     mathlib's initial tape, halts after exactly `21` steps with the input stack empty and the
     output stack `true, false` from the bottom, within the bound `312` of `tr2_outputs`
     (instantiated, `tmActs revTM = 2`); on `[]`: `3` steps;
   - `mixM`: a peek, a pop of the empty stack, two pushes and a pop in one step, from the stacks
     `[true, false]` and `[]` to `[false]` and `[false, true]`; simulated in exactly `22` steps,
     within `1 + 5 (2 (2 + 5) + 2) = 81`;
   - **negative controls:** neither simulation is done a step earlier; the output stack is
     stored bottom first; `revTM` does not output its input.

**Not covered:** the simulation of `TM1` by `TM0` with finite control (18d), the adapters and
the compiler (18e), the GI machines on one tape (18f).

## Milestone 18, stage 18b: finite single-tape machines and timed outputs (`PLAN-18.md` §3)

Stage 18a is done (`5a75267`). This stage fixes the contracts of the single-tape simulation:
`GraphIso/TM/SingleTape/Model.lean`, which imports mathlib only. No existing statement changes.
The library root `GraphIso.lean` imports the single-tape modules at stage 18f (every change to
the root rebuilds the dependent check modules); until then they are in the axiom audit's import
closure through their check modules.

1. **Counted runs** (`StepsIn f n a b`): `f` takes `a` to `b` in exactly `n` transitions,
   `(flip bind f)^[n] (some a) = some b`, the iteration in mathlib's `EvalsTo`. Runs compose
   (`StepsIn.trans`) and are deterministic: two runs from `a` to configurations where `f`
   halts have the same length and end (`StepsIn.halt_unique`). They give mathlib's `Reaches`
   and `EvalsToInTime` (`StepsIn.reaches`, `StepsIn.evalsToInTime`, `EvalsToInTime.stepsIn`).
2. **Quantitative simulation** (`SimIn f₁ f₂ R κ`): every transition of `f₁` from `a₁` is
   matched, from each `R`-related configuration, by at most `κ a₁` transitions of `f₂` to an
   `R`-related configuration. `SimIn.run`: `N` transitions along which `κ ≤ K` are matched by
   at most `N K` transitions.
3. **Finite single-tape machines** (`FinTM0`): mathlib's `TM0.Machine` with a `Finite` tape
   alphabet `Γ`, its blank `blank`, `Finite` states `Λ` and a start state `start`. The
   `Inhabited` instances used by mathlib's `TM0.step` and `TM0.init` are exactly `blank` and
   `start`.
4. **Timed outputs** (`TM0OutputsInTime M l l' m`): from `TM0.init l` (state `start`, head on
   the first symbol of `l`, blanks elsewhere), `M` makes at most `m` transitions to a
   configuration where `TM0.step` returns `none` and whose tape is `Tape.mk₁ l'` (head on the
   first symbol of `l'`, blanks elsewhere). Transitions are counted; the halt is free. Then
   `ListBlank.mk l' ∈ TM0.eval M.machine l` (`mem_eval`), the output is unique up to trailing
   blanks (`unique`), and a timed output within `m` forces every halting run to have at most
   `m` transitions (`steps_le`); also `mono`.
5. **Framed tapes**: the alphabet `Sym W α β` (work symbols `W`, the blank being `work default`;
   `lmark`, `rmark`; input symbols `α`; output symbols `β`), `encodeIn x = lmark :: x.map inp ++
   [rmark]` and `encodeOut y = lmark :: y.map out ++ [rmark]`, of lengths `|x| + 2` and `|y| + 2`
   (`length_encodeIn`, `length_encodeOut`), injective (`encodeIn_injective`,
   `encodeOut_injective`) and injective as tapes (`mk_encodeIn_inj`, `mk_encodeOut_inj`: the
   final `rmark` is not blank, so no output is lost as trailing blanks; `mk_append_inj`).
6. **Checks** (`GraphIsoChecks/TMSingleTapeModel.lean`, no GI imports):
   - framed-tape lengths by the kernel; the empty output, `[false]` and `[true]` have pairwise
     distinct tapes;
   - `copyM` (alphabet `Sym Unit Bool Bool`, four states) rewrites each input symbol as an output
     symbol, returns to the left mark and halts: on `encodeIn [true, false]` it outputs
     `encodeOut [true, false]` after exactly `8` transitions, on `encodeIn []` after `2`, by
     kernel reduction of mathlib's `TM0.step` (`copy_run`, `copy_out`), hence in `TM0.eval`;
   - **negative controls:** no other output within any bound; not within `7` transitions; a
     trailing blank is invisible on a tape; `copyM` does not halt at the start.

**Not covered:** the simulations and the compiler (stages 18c–18e) and the GI machines on one
tape (18f); see the later stages above.

## Milestone 18, stage 18a: graph isomorphism in the number of vertices (`PLAN-18.md` §2)

Milestone 17 is done (`50ee3a4`). This stage restates the Turing-machine bounds of 17h in the
number of vertices `n`, for the same machines and the same encoding: `GraphIso/TM/Vertices.lean`.
No existing statement changes. The new targets are `gi_tm_vertices` and `gi_coset_tm_vertices`.

**The headline in the number of vertices** (`λ = Nat.log 2`):

1. **Decision** (`gi_tm_vertices`): there is `c` such that on every graph pair `p` on `n`
   vertices the machine `toFinTM2 giDecProg .inp .out` outputs `ser .bool (isoDecide p)` on
   `p.enc` within `2 ^ (c (λ(n) + 1) ^ 8)` steps, with
   `isoDecide_iff : isoDecide p = true ↔ Nonempty (p.G ≃g p.H)`.
2. **The coset** (`gi_coset_tm_vertices`): there is `c` such that for every pair `p` the
   machine `toFinTM2 giCosetProg .inp .out` outputs `ser Ty.giCoset r` on `p.enc` within
   `2 ^ (c (λ(n) + 1) ^ 8)` steps, where `r = none ↔ IsEmpty (p.G ≃g p.H)`, and for
   `r = some (τ, hs)` the data are valid and the coset `τ • ⟨hs⟩` is exactly the set of the
   permutations underlying the isomorphisms `p.G ≃g p.H`.

The machine-level statements stay in the input's length `L`: `gi_tm` (with its
`TM2ComputableInTime`, whose `time` field takes `L`) and `gi_coset_tm`.

3. **The encoding's length**: `length_ser_natList_le` (a list of naturals below `n`: at most
   `|xs| (n + 1) + 1` symbols), `length_ser_graph_le` (graph data with `GraphData.ValidD n n`:
   at most `n (n (n + 1) + 2) + 1`), `GraphPair.enc_length_le` (`L ≤ 5 (n + 1)³`, coarse:
   the encoding has `O(n² log n)` symbols) and `GraphPair.lam_enc_le`
   (`λ(L) + 1 ≤ 8 (λ(n) + 1)`). So `2 ^ (c (λ(L) + 1) ^ 8) ≤ 2 ^ (c 8⁸ (λ(n) + 1) ^ 8)`
   (`exp_enc_le_vertices`), and both corollaries take `gi_tm`'s and `gi_coset_tm`'s runs with
   the constant `c 8⁸` (`outputsInTime_mono`).
4. **Checks** (`GraphIsoChecks/TMVertices.lean`):
   - the encoding bounds by the kernel at `n = 0` and `n = 1` (empty graphs, `3` and `8`
     symbols) and on the two paths on `Fin 3` (`40` symbols), and the lemmas instantiated;
   - `gi_tm_vertices` instantiated: `true` on the two paths, `false` on a path and the
     triangle within `2 ^ (c 2⁸)` steps, `true` on the empty pairs at `n = 0, 1` within `2 ^ c`
     steps; `gi_coset_tm_vertices`: `some` on the two paths, `none` on a path and the triangle.
     These instantiate the theorems; the machines are not run;
   - **negative controls:** the input's length is not the number of vertices (`8 ≠ 1` on the
     one-vertex pair); `λ(L) + 1 ≤ λ(n) + 1` fails on the two paths; `L ≤ (n + 1)³` fails at
     `n = 0`.

**Also in this round** (folded from an abandoned documentation loop): `docs/efficient-backends.md`
and `docs/backend-contracts.md` describe the completed endpoints (`giSolve_final`,
`gi_simpleGraph_final`) and the Turing-machine simulation (`comp_sat`, `main_exec`, `main_tm`,
with the output's length in the bound) and list what remains; the module docs of
`Pyber/Discharge.lean` and `Main/GraphQP.lean` mark the route through the linear `QPHyp` as
historical (`qpHypJ_final`); the theorem map's introduction and the package description.

**Not covered:** the single-tape machines (stages 18b–18f).

## Milestone 17, stage 17h: graph isomorphism on Turing machines (`PLAN-17.md` §11)

Stage 17g is done (`18f4255`). This stage applies 17g to milestone 16's algorithm:
`GraphIso/TM/GI.lean`. No existing statement changes. The new targets are `gi_tm` and
`gi_coset_tm`. With it milestone 17 is complete.

1. **Graph pairs** (`GraphPair`): `n` and simple graphs `G`, `H` on `Fin n` with decidable
   adjacency. The encoding `GraphPair.enc p = ser Ty.giInput (n, GraphData.ofSimpleGraph G,
   GraphData.ofSimpleGraph H)`, over the machine's alphabet, is at least `n` long
   (`GraphPair.n_le_enc`). The specification `isoDecide p` is brute force over the permutations
   of `Fin n` (it states the problem; it is not the algorithm), and `isoDecide_iff : isoDecide p
   = true ↔ Nonempty (p.G ≃g p.H)`.
2. **The entries and programs**: `giCosetEntry` is milestone 16's entry with Schreier–Sims
   substituted (`(giEntry Ty.unit var x).subst ssImpl`); `giDecEntry` returns `true` exactly when
   it returns `some`. Both are well formed. `giCosetProg` and `giDecProg` are
   `mainProg (qpSolver 192 181) _`.
3. **The output's length** (`length_ser_coset_le`): for valid data with at most `4 gN(n)²`
   generators, `(ser Ty.giCoset r).length ≤ 16 (n + 1) ^ 6`.
4. **The runs** (`gi_runs`, `gi_bound`, `gi_dec_exec`): by `gi_simpleGraph_final` and
   `giSolve_final`, the coset entry runs on `p.data` within local cost `2 ^ (c (λ(n) + 1) ^ 8)`
   (`λ = Nat.log 2`), with the answer of `gi_simpleGraph_final` and at most `4 gN(n)²`
   generators. With `n ≤ L` (`L` the length of the encoding) and the output's length,
   `mainPoly + 1 ≤ 2 ^ ((120 (κ + c + 12) + 1) (λ(L) + 1) ^ 8)`; so by `main_exec` the decision
   program's `main` runs from `inCfg .inp p.enc` to `inCfg .out (ser .bool (isoDecide p))` within
   `2 ^ ((A + 1) (λ(L) + 1) ^ 8)` steps.
5. **Decision** (`gi_tm`): there are `c` and a `TM2ComputableInTime GraphPair.enc (ser .bool)
   isoDecide` whose machine is `toFinTM2 giDecProg .inp .out` and whose time on inputs of length
   `L` is at most `2 ^ (c (λ(L) + 1) ^ 8)`; and on every pair `p` that machine outputs
   `ser .bool (isoDecide p)` on `p.enc` within `2 ^ (c (λ(L) + 1) ^ 8)` steps.
6. **The coset** (`gi_coset_tm`): there is `c` such that for every pair `p`, with `L` the length
   of its encoding, some `r` has `TM2OutputsInTime (toFinTM2 giCosetProg .inp .out) p.enc
   (some (ser Ty.giCoset r)) (2 ^ (c (λ(L) + 1) ^ 8))`, `r = none ↔ IsEmpty (p.G ≃g p.H)`, and for
   `r = some (τ, hs)` valid data with the coset `τ • ⟨hs⟩` exactly the set of the permutations
   underlying the isomorphisms `p.G ≃g p.H`.
7. **Checks** (`GraphIsoChecks/TMGI.lean`), on graphs on `Fin 3`.
   - `isoDecide` by the kernel: the paths `0 - 1 - 2` and `1 - 0 - 2` are isomorphic
     (`pp_iso`), a path and the triangle are not (`pt_not_iso`); `isoDecide_iff` turns these
     into `Nonempty (path₁ ≃g path₂)` and `IsEmpty (path₁ ≃g tri)`.
   - The encoding of the two paths, `40` symbols.
   - `length_ser_coset_le` at the identity with the generator `(0 1)` (`43` symbols).
   - `gi_tm` instantiated: the decision machine outputs `ser .bool true` on the two paths and
     `ser .bool false` on the path and the triangle within `2 ^ (c 6 ^ 8)` steps (both encodings
     have `λ = 5`); `gi_coset_tm`: the coset machine outputs `some` on the two paths and `none`
     on the path and the triangle.
   - The coset entry in the cost model, by the kernel: on the empty graphs `some` at local cost
     `144`, on the one-vertex graphs `some` at `376`, on an edge and the empty graph (`pe`)
     `none` at `86100` (`pe_runs`: `54430` trace events, kernel-checked in pieces of at most
     `1000` events with `GraphIsoChecks.Exec`, the summary's sum proved part by part). The
     machines themselves are not run on graphs.
   - **Negative controls:** `pt_not_iso`; the encodings of the two pairs differ; the coset entry
     returns `none` on `pe`.

**Not covered** (`PLAN-17.md` §1): the polynomial equivalence of `TM2` with single-tape machines.

## Milestone 17, stage 17g: the simulation on Turing machines (`PLAN-17.md` §10)

Stage 17f is done (`49f0588`). This stage puts the pieces together: a main program that loads
the input, runs the compiled entry and writes the output, its running time, and the Turing
machine: `GraphIso/TM/Main.lean` (stages 17a–17f). No existing statement changes. The new
targets are `main_exec` and `main_tm`.

1. **Stack growth** (`Exec.length_le`): a run of `n` steps adds at most `n` symbols to each
   stack. So the heap loaded from an input of length `L` has at most `heapB` symbols, the bound
   on the loading's steps.
2. **Canonical pointers** (`canonPtr`, `canonPtr_sat`): the number on `ptr` with its high zero
   bits dropped. The compiled code leaves a pointer of at most `B` plus the number of cells
   bits; `write` needs one at most as long as the heap.
3. **The main program** (`mainProg Pr E`): the procedure `true` runs the compiled body of `Pr`;
   `main` initializes the counter, loads the input, binds it at level `0`, runs the compiled
   entry, drops the level, makes the pointer canonical, writes the result and erases `heap` and
   `cnt`.
4. **The run** (`main_sat`, `main_exec`): if `Prog.Wf true [⟨a', x₁, x₂⟩] (E Ty.denote x₁)
   (E Lv x₂)` for all `x₁`, `x₂`, then for every run `Runs O (Pr.proc Ty.denote) (E Ty.denote x)
   v tr`, `main` runs from `inCfg .inp (ser a' x)` to `inCfg .out (ser c v)` (every other stack
   empty, registers empty) within `mainT` steps, and so within
   `mainPoly = (κ (C + L + L' + 1)) ^ 120` (`mainT_le`): `C` the local cost of `tr`, `L`, `L'`
   the lengths of the input and the output, `κ = 4096 (wt a' + wt c + K + D + |E| + 1)` with
   `K`, `D` the size constants (`kP`, `dP`) and `|E| = psize 1 (E Lv 0)`. The proof feeds
   `comp_sat` (17e) and `primCode_spec` (17f) the bit bound `B` and the field bound `F` of the
   run (`bB`, `fB`), bounds the final heap's cells and symbols (`nCells`, `nSym`) and pays each
   unit of cost `qB = ctrlB + primB` at the final heap's size.
5. **On Turing machines** (`main_tm`): `TM2OutputsInTime (toFinTM2 (mainProg Pr E) .inp .out)
   (ser a' x) (some (ser c v)) (mainPoly + 1)`, the step count computed by the interpreter.
6. **The output's length** is in the bound because values share cells: at a cost of about `m`,
   a program can build a list of `m` copies of one list of `m` numbers, which the machine writes
   out in at least `m²` symbols (lists nested `d` deep: `m^d`). So no bound
   `C_P (C + L + 1)^d` with `d` independent of the program holds; the Goal's statement 1 is
   amended (`PLAN-17.md` §10.3). Graph isomorphism is unaffected (17h).
7. **Checks** (`GraphIsoChecks/TMMain.lean`).
   - Kernel runs of `main` from `inCfg .inp`, with the output, every other stack (including
     `heap` and `cnt`) empty, empty registers and exact step counts: the recursive copy on
     `[1, 2, 3]` (`42340` steps), arithmetic on `(5, 3)` (`45410`), `length` and `reverse`
     (`67665`), and `share` (`(pair x x, pair x x)`, an output four times as long as the input,
     for two units of cost: `102694`).
   - `canonPtr` on a pointer with a high zero bit (`75` steps).
   - Sharing in the cost model (`square`, `m` copies of one list of `m` numbers): at `m = 20`,
     local cost `62` and an input of `6` symbols, but an output of `2221` symbols.
   - The theorems on the recursive copy and `[1, 2, 3]` (local cost `12`): `copy_bound`
     (`mainPoly = 7577600 ^ 120`), `copy_exec` (`main_exec`), `copyTM` (`main_tm`), whose step
     count is `42341`.
   - **Negative controls:** `copyMain_not_42339` (a wrong step count), `copyMain_not_rev` (a
     wrong output).

**Not covered:** graph isomorphism on Turing machines (17h).

## Milestone 17, stage 17f: the primitives (`PLAN-17.md` §9)

Stage 17e is done (`e11b6f9`). This stage gives code for every primitive of the cost language
and proves the specification that 17e assumed: `GraphIso/TM/PrimLib.lean` (routines) and
`Prims.lean` (stages 17a–17e). No existing statement changes. The new target is
`primCode_spec`.

1. **Routines** (`PrimLib.lean`), each starting with empty registers, with every stack it does
   not name unchanged and an explicit step bound: allocation keeping `HeapBnd` (`allocB_sat`),
   a cell from the pointers on top of `work` (`allocArgs_sat`), fetching the cell or the bits of
   the natural of the pointer on top of `work` (`openTop_sat`, `natTo_sat`), moving or counting
   the numbers above a marker (`moveAll_sat`, `countAll_sat`; a count of `k` has at most
   `k + 1` bits), walking a list onto a stack (`walkList_sat`) and building a list from
   pointers on a stack, keeping `HeapBnd` (`buildListB_sat`). Frames are tracked by `Fr`. Each
   ends with empty registers except `openTop`, which leaves the fetched cell's tag in register
   `1` for the caller to test; the loop tests of `Prims.lean` (`mkTest`, `rangeTest`,
   `getTest`, `updTest`) likewise leave their results in registers. The code of every
   primitive ends with empty registers.
2. **Code for every primitive** (`primCode`, the 27 constructors of `Prim`). The arguments'
   pointers are on `work` (the last on top) and are replaced by the result's pointer:
   - `unit`, `boolLit`, `none`, `nil`, `pair`, `some`, `cons`: one cell; `natLit k`: one cell
     with the bits of `k`;
   - `fst`, `snd`, `and`, `or`: an existing pointer, no new cell; `not`: one cell;
   - `add`, `sub`, `natEq`, `natLt`: the 17b arithmetic on the arguments' bits, one cell;
   - `length` (walk, count), `reverse` (walk, reverse, cons onto a new `nil`), `append` (walk
     the first list, cons onto the second), `range k` (count up to `k`, a natural per count,
     cons onto a new `nil`);
   - `arrayMk k v` (`k` copies of a pointer), `arraySize` (count the fields), `arrayGet` (drop
     fields while counting the index down; past the fields, the cells of the default value),
     `arrayUpdate` (each write applied in order to the fields, out-of-bounds writes ignored,
     then one cell), `arrayOfList`, `arrayToList`.
3. **`primCode_spec`**: for every program `prog` and `B`, `F`, `K`, `Q` with `F + 1 ≤ B`,
   `2 ≤ F` and `primB (B + N) ≤ Q N` for every `N`, `PrimSpec prog primCode B F K Q`, with
   `primB M = (2 M + 10) (fcE M M + allocBound (M² + 3 M + 2) M + 100 M + 100)`. A unit of
   cost pays for a few lookups, the allocation of a cell of at most `(M + 1) (M + 2)` symbols,
   and scans over at most `2 M` numbers of at most `M` bits (the at most `F ≤ M` fields of a
   cell; the at most `tySize ≤ K ≤ B ≤ M` cells of a default value). New cells: at most
   `2 * cost ≤ K * cost` (for `range`), otherwise at most the cost, or `tySize` for `arrayGet`.
   The code looks cells up before it allocates any, so step bounds are fixed in advance
   (`PrimOut.of_sat`); `arrayGet` chooses its bound after its scan (`PrimOut.seq`).
4. **Checks** (`GraphIsoChecks/TMPrims.lean`).
   - Kernel runs of programs compiled with `primCode` (load the input, bind it, run, write the
     result), with the output, all other stacks but `heap` and `cnt` empty, empty registers
     and exact step counts, covering every primitive: arithmetic and comparisons on `(5, 3)`,
     `(3, 5)`, `(4, 4)` (`44992`, `44786`, `45140` steps); Booleans (`27646`, `27582`);
     `length` and `reverse` (`67077`); `append` and `range` (`142792`); `arrayOfList`,
     `arraySize`, reads in and out of bounds, `arrayMk`, `arrayToList` (`165549`);
     `arrayUpdate` with an out-of-bounds write (`251701`); the default value of a pair
     (`16626`); options and the unit (`38422`); the recursive copy (`41962`).
   - `primCode_spec` instantiated; `copy_spec`: `comp_sat` for the recursive copy with
     `primCode`, `K = 10`, `D = 28` and `Q N = ctrlB 28 (B + N) + primB (B + N)`, with no
     premise on the primitives (it replaces `copy_spec` of the 17e checks, whose premise
     `PrimSpec` for `pcDemo` could not hold: finding F1 of the 17e audit); `copy_nil`: a
     concrete instance (the empty list) with every premise discharged.
   - **Negative controls:** `natOps_not_44991` (a wrong step count), `arrOps_default` (an
     out-of-bounds read gives the default), `updOps_oob` (an out-of-bounds write changes
     nothing).

**Not covered:** the main program and the Turing machine with its time bound (17g), and graph
isomorphism (17h).

## Milestone 17, stage 17e: the compiler (`PLAN-17.md` §8)

Stage 17d is done (`a8aae08`). This stage compiles programs of the cost language to stack-program
code and proves that the code simulates `eval`: `GraphIso/TM/Env.lean` and `Compile.lean`
(stages 17a–17d and the cost language's `Program`, `Evaluation` and `WellFormed`). The
primitives are a parameter given by a specification (`PrimSpec`); their code is stage 17f. No
existing statement changes. The new target is `comp_sat`.

1. **Environments** (`Env.lean`). The stack `env` holds the pointers of the variables in scope,
   newest on top; `envEnc ls` is a frame whose level `k` is `ls[k]`. `moveN j a b` moves `j`
   numbers (`moveN_sat`); `fetchTo j dst` copies the number at offset `j` onto `dst` and restores
   `env` within `fetchB j E = (2 j + 1) (14 E + 25)` steps for numbers of at most `E` bits
   (`fetchTo_sat`); `fetchLv d k dst` copies the level `k` of a frame of depth `d`
   (`fetchLv_sat`).
2. **The size invariant** `HeapBnd B F h`: the cell at index `i` has an address of at most
   `B + i` bits, at most `F` fields, and fields of at most `B + i` bits. Every heap satisfies it
   for `B` and `F` at least its length in symbols (`HeapBnd.of_length`), a loaded input in
   particular. Under it, with `n = h.length`, the heap has at most
   `n * (B + n + 4 + F * (B + n + 1))` symbols (`length_encHeap_le_bnd`). Pointers (frame
   entries, arguments, results) have at most `B + h.length` bits.
3. **The compiler** `comp pc pb d p`, for programs over the empty signature instantiated with
   de Bruijn levels (`Lv t = ℕ`), in a frame of depth `d`; it pushes the pointer of the value
   onto `work`:
   - `ret`: copy the entry; `bind`: run, push the pointer onto `env`, run the continuation at
     depth `d + 1`, drop the entry; `prim p xs`: copy the arguments' pointers onto `work`, then
     `pc p`;
   - `ite`, `caseOption`, `caseList`: fetch the cell, branch on its tag, bind its fields as new
     levels;
   - `foldList`: a while loop with the remaining list at level `d` and, in each step, the
     accumulator and the element at levels `d + 1` and `d + 2`; `loop`: a while loop with the
     state at level `d`;
   - `recur`: push the argument's pointer (a new frame of depth `1`), call the procedure `pb`,
     drop the entry.

   `psize d p` is the program's size: a primitive weighs `pw p + 1` (`pw` covers a literal's bits
   and a default value's cells), a loop or a fold `2` plus its body.
4. **The primitive specification** `PrimSpec prog pc B F K Q`: for every primitive `p` with
   `pw p ≤ K` and arguments `xs` with `p.cost xs ≤ F`, from `HeapAt h`, `HeapBnd B F h`, empty
   registers and the arguments' pointers (of at most `B + h.length` bits) on `work`, the last on
   top, `pc p` appends at most `K * p.cost xs` cells keeping `HeapAt` and `HeapBnd B F`, replaces
   the arguments by a pointer (of at most `B` plus the new number of cells in bits) representing
   `p.eval xs`, ends with empty registers and every stack but `heap`, `cnt` and `work`
   unchanged, within `p.cost xs * Q N` steps, `N` the final heap's length in symbols.
5. **The simulation theorem** (`comp_sat`). Let `Pr : WfProc Signature.empty a b` be run by the
   procedure `pb` whose body is `comp pc pb 1 (Pr.proc Lv 0)`. The hypotheses: `PrimSpec`,
   `Q` monotone with `ctrlB D (B + N) ≤ Q N` (the control overhead of one construct), `K ≤ B`,
   `psize 1 (Pr.proc Lv 0) + 1 ≤ K` and `1 + 3 * psize 1 (Pr.proc Lv 0) ≤ D`. For every fuel,
   if `Prog.Wf true Γ p₁ p₂` (`p₁` at `Ty.denote`, `p₂` at levels),
   `eval O (Pr.proc Ty.denote) fuel p₁ = some (v, tr)` with `localCost tr ≤ F`, `HeapAt h c`,
   `HeapBnd B F h`, empty registers, a frame of depth `d` representing `Γ` (`EnvAt`: each
   `⟨t, x, k⟩ ∈ Γ` has `k < d` and its entry, of at most `B + h.length` bits, represents `x`),
   `psize d p₂ ≤ K` and `d + 3 * psize d p₂ ≤ D`, then `comp pc pb d p₂` (`Pushes`):
   - appends cells `h'`, at most `K * localCost tr`, with `HeapAt (h ++ h')` and
     `HeapBnd B F (h ++ h')`;
   - pushes onto `work` a pointer `l` with `Rep (h ++ h') t v (ofBits l)` and
     `l.length ≤ B + (h ++ h').length`;
   - ends with empty registers and every stack but `heap`, `cnt` and `work` unchanged;
   - runs within `(psize d p₂ + K * localCost tr) * Q N` steps, `N` the final heap's length in
     symbols.

   The proof is by induction on the fuel (`sim_all`), one lemma per construct (`sim_ret`,
   `sim_bind`, `sim_prim`, `sim_ite`, `sim_opt`, `sim_list`, `sim_fold`, `sim_loop`,
   `sim_recur`), and for the loops an inner induction on the remaining list (`foldLoop_sat`) or
   on the fuel (`loopLoop_sat`).
6. **Checks** (`GraphIsoChecks/TMCompile.lean`), with `pcDemo`, code for the primitives the test
   programs use (written for the checks only).
   - Kernel runs of compiled programs (load the input, bind it at level `0`, run, write the
     result), with the output, all other stacks but `heap` and `cnt` empty, empty registers and
     exact step counts: a fold reversing `[1, 2, 3]` (`47016` steps), a recursive copy of
     `[1, 2, 3]` (`41434`), a loop on a pair reversing `[1, 2]` (`81340`), and case analysis on
     an option with a branch on `some true`, `some false` and `none` (`2206`, `2242`, `1078`).
   - `comp_revFold`: the compiled code of the fold, with its levels; `psize` of the programs;
     `fetchLv` on a concrete frame; `HeapBnd`, `HeapBnd.of_length` and the heap-length bound on
     a concrete heap.
   - `copyRec_wf` and `O₀`, for the simulation theorem with the primitives' code (17f; the
     earlier `copy_spec` under `PrimSpec` for `pcDemo`, whose premise could not hold, was
     removed).
   - **Negative controls:** `revFold_not_47015` (a wrong step count), `copyRec_not_rev` (a wrong
     output), `optBr_not_two` (the wrong branch), `h₀_not_bnd` (heaps breaking `HeapBnd`).

**Not covered:** the code of the primitives (17f), the main program and the Turing machine
with its time bound (17g), and graph isomorphism (17h).

## Milestone 17, stage 17d: input and output (`PLAN-17.md` §7)

Stage 17c is done (`13c93ee`). This stage reads a serialized input into the heap and writes a
heap value to the output: `GraphIso/TM/Ser.lean`, `Load.lean` and `Write.lean` (mathlib and
stages 17a–17c), and the rule `Sat.loop_list` in `Sat.lean`. No existing statement changes. The
new targets are `load_sat` and `write_sat`.

1. **Serialization** (`Ser.lean`). `ser t v : List Sym` for every `Ty`, a prefix code:
   - the unit is empty, a Boolean is the tag `tt` or `ff`, a natural `n` is
     `bits (toBits n) ++ [nd]` with `toBits n` its canonical bits (`ofBits_toBits`);
   - a pair is its two components; an option is the tag `none`, or the tag `some` and its
     value;
   - a list is each element after the tag `cons`, then the tag `nil`; an array is the same for
     its elements in reverse order.
   - `wt t` is a weight of the type (constructors, lists and arrays counted twice).
2. **Loops over lists** (`Sat.loop_list`). With an invariant `I rs` indexed by the list `rs` of
   items still to process: if the condition holds and the body runs within `f a` steps from
   `I (a :: rs)` to `I rs`, and the condition fails in `I []` where `Q` holds, then the loop
   runs from `I rs` within `∑ (f a + 1) + 1` steps to `Q`.
3. **Loading** (`Load.lean`, `load_sat`). The hypotheses: `HeapAt h c`, empty registers,
   `ser t v ++ rest` on `inp`, and `h.length + cellsB t v ≤ U`. Then `load t` runs within
   `ldB t v U` steps and ends with:
   - empty registers and `rest` on `inp`;
   - cells `h'` appended, with `HeapAt (h ++ h')` and at most `cellsB t v` of them;
   - a pointer `l` pushed onto `work`, with `l.length ≤ U` and `Rep (h ++ h') t v (ofBits l)`;
   - every stack other than `heap`, `cnt`, `inp` and `work` unchanged.

   A list's elements are loaded first (`readElems`); then the `nil` cell and the `cons` cells,
   from the end of the list, are allocated (`buildList`). An array's elements, serialized in
   reverse order, leave their pointers in the order of the array cell's fields.
4. **Writing** (`Write.lean`, `write_sat`). The hypotheses: a well-formed heap `h` on `heap`,
   `scan` empty, empty registers, and `bits p ++ nd :: rp` on `ptr` with `Rep h t v (ofBits p)`
   and `p.length ≤ N`, where `N` is the heap's length in symbols. Then `write t` runs within
   `wrB t v N` steps and ends with:
   - empty registers, `ser t v` pushed onto `out`, and `rp` on `ptr`;
   - every other stack unchanged.

   A natural is written canonically whatever the length of its field: its leading zero bits
   are dropped (`strip_eq_toBits`). The routines: `fetchCell` (a lookup, then the cell's tag in
   register `1` and its fields on `work`), `closeCell`, `moveNum2`, `xferNums`, `writeElems`.
5. **Polynomial bounds**, with `L = (ser t v).length`:
   - `cellsB_le`: `cellsB t v ≤ wt t * (L + 1)`;
   - `ldB_le`: `ldB t v U ≤ wt t * (L + 1) * PL U` when `L ≤ U`, where
     `PL U = allocBound ((U + 1) (U + 2)) U + 30 U + 100` has degree 4;
   - `wrB_le`: `wrB t v N ≤ wt t * (L + 1) * visB N`, where
     `visB N = lookupBound N N + 2 N (6 N + 14) + 60 N + 100` bounds visiting one cell.
6. **Checks** (`GraphIsoChecks/TMIO.lean`), on `v₁ = (5, [some true, none])` of type
   `ℕ × List (Option Bool)`.
   - `ser_v₁` and `ser_arr` (an array, serialized in reverse order).
   - Kernel runs with all final stacks, registers and exact step counts:
     - `load` of `v₁` in `4660` steps builds the eight cells `h₁` and leaves the pointer `7`;
       the counter pads addresses with zeros (the address `k` has length `k + 1`);
     - `write` from `h₁` and the pointer `7` outputs `ser v₁` in `17743` steps;
     - a round trip (load, move the pointer, write) of the array `#[3, 0, 1]`;
     - `write .nat` of a cell holding `[0, 1, 0, 0]` through the pointer `[0, 0]` outputs the
       canonical `ser .nat 2`.
   - `rep_v₁` builds `Rep h₁ _ v₁ 7` from the constructors; `load_spec` and `write_spec` apply
     the specifications to concrete inputs.
   - **Negative controls:** `load_not_4659` (a wrong step count), `not_rep_some_false` (a wrong
     value) and `write_not_other` (the output of another value).

**Not covered:** the compiler, the primitives and the simulation on Turing machines (17e–17g),
and graph isomorphism (17h).

## Milestone 17, stage 17c: the heap (`PLAN-17.md` §6)

Stage 17b is done (`4bb8914`). This stage stores values for the simulator in an append-only heap
of cells on a stack: `GraphIso/TM/Heap.lean`, `Lookup.lean`, `Alloc.lean` and `Rep.lean`
(mathlib, stages 17a–17b, and `GraphIso.Cost.Program` for `Ty`). No existing statement changes.
The new targets are `lookup_sat`, `alloc_sat` and `Rep.mono`. Stage 17d is now input and
output; the compiler moves to 17e and graph isomorphism to 17f.

1. **Stacks** (`Heap.lean`). `Stk` names the simulator's stacks: input, output, heap, scan,
   allocation counter, work, pointer, environment, loop, and temporaries `t0`–`t4`.
2. **Cells and heaps** (`Heap.lean`).
   - A cell `⟨addr, tag, fields⟩` has an address (a bit list), a tag and fields (bit lists:
     addresses of other cells, or the bits of a natural). On a stack it is
     `mk 1 :: bits addr ++ nd :: tag :: (fields, each followed by nd) ++ [mk 0]` (`encCell`).
   - A heap is a list of cells, oldest first, stored newest on top (`encHeap`).
   - `HeapWF h`: the cell at index `i` has an address of value `i`.
3. **Routines.** As in 17b, each starts and ends with empty registers, leaves every stack it
   does not name unchanged, and has an explicit step bound.
   - `moveSeg2 s a b d` moves a segment `w ++ [s]` (`s ∉ w`) onto both `b` and `d`, reversed,
     in `6 |w| + 10` steps.
   - **Lookup** (`Lookup.lean`, `lookup_sat`). The hypotheses: a well-formed heap `h` on `heap`,
     `scan` empty, and a pointer `p` on `ptr` with `ofBits p < h.length`.
     - `lookup` pushes a copy of `encCell h[ofBits p]` onto `work` and consumes the pointer.
       It leaves `heap`, `scan` and every other stack as they were.
     - It moves the cells above the target to `scan`, testing each address with `addrTest`
       (`eqNum` on copies). Then it copies the target onto `heap` and `work` and moves the
       scanned cells back.
     - The bound is `lookupBound N |p|`, where `N` is the heap's length in symbols. It is at
       most `50 (N + |p| + 3)²` (`lookupBound_le`).
   - **Allocation** (`Alloc.lean`, `alloc_sat`).
     - `HeapAt h c` says that `c` holds `h`: well formed, on `heap`, `scan` empty, and a
       counter on `cnt` with value `h.length` and length at most `h.length + 1`.
     - From `HeapAt h`, with fields `fs` on `work` above the marker `mk 2`, `alloc t` gives
       `HeapAt (h ++ [⟨l, t, fs⟩])` with `ofBits l = h.length` and `l.length ≤ h.length + 1`
       (the address is a copy of the counter). It replaces the fields and the
       marker on `work` by the address `l` and leaves every other stack unchanged.
     - The bound is `allocBound (encFields fs).length h.length`, that is
       `2 Lf (6 Lf + 14) + 63 n + 300`. The fields pass twice through `moveNums`; the counter
       is copied twice and incremented.
4. **Representation** (`Rep.lean`). `Rep h t v p` says that the cell at index `p`, with the
   cells it points to, represents the value `v : t.denote`, for every `Ty`:
   - the unit, Booleans (tags `tt`, `ff`), `none` and `nil` are cells without fields;
   - a natural is a cell whose one field `l` has `ofBits l = v`;
   - a pair is a cell with two pointers, `some` a cell with one, and `cons` a cell with two
     (head and tail);
   - an array is a cell with one pointer per element.

   Pointers are read through `ofBits`, so they need not be canonical. `Rep.mono`:
   representations are kept when cells are appended. `Rep.lt`: they point into the heap.
5. **Checks** (`GraphIsoChecks/TMHeap.lean`), on the heap `h₃` holding `5`, `none` and the
   pair of them.
   - Kernel runs with all final stacks, registers and exact step counts:
     - `lookup` of each cell in `603`, `462` and `298` steps, deepest first;
     - a non-canonical pointer `[0, 1, 0, 0]` onto a non-empty `work`;
     - `alloc` of a `some` cell and of a pair cell at address `3`, with the counter becoming
       `4`.
   - `lookup_spec` and `alloc_spec` apply the specifications to concrete inputs.
   - `rep_pair` holds, and still holds after an allocation (`rep_pair_mono`); `rep_some` holds
     for the new cell.
   - **Negative controls:** `not_rep_pair` (a wrong value), `not_rep_bool` (a wrong type) and
     `not_wf` (a cell `0` with address `1`).

**Not covered:** serializing values, loading the input and writing the output (17d), the
compiler (17e), and graph isomorphism (17f).

## Milestone 17, stage 17b: numbers and arithmetic on stacks (`PLAN-17.md` §5)

Stage 17a is done (`7860b68`). This stage builds binary arithmetic for the simulator out of
stack programs: `GraphIso/TM/Sat.lean`, `Bits.lean`, `Num.lean` and `Arith.lean` (mathlib and
stage 17a only). No existing statement changes. The new targets are `addNum_sat`, `subNum_sat`,
`ltNum_sat` and `eqNum_sat`.

1. **Specifications** (`Sat.lean`). `Sat prog x c t Q` says that `x` runs (`Exec`) from `c`
   within `t` steps to a configuration satisfying `Q`. Since `Exec` is deterministic, this
   describes the unique run.
   - There is a rule for each construct. The budget forms (`Sat.seq_le`, `Sat.act_le`,
     `Sat.act_seq`, `Sat.ite_true_le`, `Sat.ite_false_le`) pass the steps left to what follows.
   - `Sat.loop` takes an invariant `I m` indexed by the number `m` of remaining iterations and
     gives `m (t + 1) + 1` steps.
2. **The alphabet and bit lists** (`Bits.lean`).
   - `Sym` has bits `bit b`, the end mark `nd`, cell tags `tag t` (from stage 17c) and markers
     `mk i`; it is a `Fintype`.
   - A number is a list of bits, least significant first and of any length, with value
     `ofBits`. There is no canonical form.
   - `zipL f xs ys c` is the serial bit processor: missing bits read as `false`, and the output
     has length `max |xs| |ys|`.
     - Adder: `addBits xs ys`, the output with the final carry appended, has value
       `ofBits xs + ofBits ys` (`ofBits_addBits`).
     - Subtractor: the borrow is set exactly when `ofBits xs < ofBits ys` (`zipL_sub_lt`), and
       `subBits xs ys` has value `ofBits xs - ofBits ys` (truncated; `ofBits_subBits`).
     - Comparator: the final carry is set exactly when the values differ (`zipL_diff_false`).
3. **Routines** (`Num.lean`, `Arith.lean`) over any stack names, with `4` registers.
   - A number `l` sits on a stack as `bits l ++ nd :: rest`, least significant bit on top.
   - Each routine starts and ends with empty registers.
   - Each names its stacks (which must be distinct where needed) and leaves every other stack
     unchanged.
   - Each specification is a `Sat` with an explicit linear bound, where `M = max |xs| |ys|`:

   | Routine | Effect | Steps |
   |---|---|---|
   | `moveBits` | moves a number to another stack, reversed | `6 \|l\| + 9` |
   | `moveBits2` | the same onto two stacks | `8 \|l\| + 11` |
   | `copyNum` | copies a number through a temporary that ends as it started | `14 \|l\| + 21` |
   | `dropNum` | removes a number | `2 \|l\| + 5` |
   | `pushNum` | pushes a constant (and keeps the registers) | `2 \|l\| + 1` |
   | `moveSeg s` | moves a segment `w ++ [s]` with `s ∉ w`, reversed | `4 \|w\| + 7` |
   | `dropSeg s` | drops such a segment | `2 \|w\| + 5` |
   | `erase` | empties a stack | `2 \|a\| + 5` |
   | `zipNum f c₀` | runs `zipL f` on two numbers; pushes the output and the final carry | `17 M + 21` |
   | `addNum` | `addBits xs ys` | `23 M + 37` |
   | `subNum` | `subBits xs ys` | `23 M + 37` |
   | `ltNum` | the bit `ofBits xs < ofBits ys` | `19 M + 33` |
   | `eqNum` | the bit `ofBits xs = ofBits ys` | `19 M + 34` |
   | `incNum` | `x + 1` | `23 \|xs\| + 64` |
   | `decNum` | truncated `x - 1` | `23 \|xs\| + 64` |

4. **Checks** (`GraphIsoChecks/TMArith.lean`).
   - Kernel runs with exact final stacks, registers and step counts:
     - `11 + 6 = 17` in `129` steps, which is the bound of `addNum_sat` attained exactly;
     - truncated `3 - 5 = 0` and `13 - 5 = 8`;
     - `5 < 13` and `¬ 13 < 5`;
     - `[1] = [1, 0, 0]` (non-canonical lengths) and `1 ≠ 2`;
     - `7 + 1` and `0 - 1 = 0`;
     - copying, moving a segment and erasing a stack.
   - `add_spec` and `eq_spec` derive the concrete results from the specifications.
   - **Negative control:** `add_not_128`, the same addition cannot finish within `128` steps,
     by determinism of `Exec`.

**Not covered:** cells and the heap (17c), input and output (17d), the compiler (17e), and
graph isomorphism (17f).

## Milestone 17, stage 17a: stack programs and Turing machines (`PLAN-17.md` §3)

Milestone 16 is done (`289e203`). Milestone 17 moves the cost bounds onto mathlib's Turing
machines (`Turing.FinTM2`, `TM2ComputableInTime`). This stage is the generic part:
`GraphIso/TM/Code.lean` and `GraphIso/TM/Machine.lean` (mathlib imports only). No existing
statement changes. The new targets are `outputsInTime` and `computableInTime`.

1. **Stack programs** (`Code.lean`), over stack names `K`, an alphabet `Γ` and `R` registers
   holding `Option Γ`:
   - actions `Act`: push a constant, push a register's symbol (`default` if empty), pop into a
     register (`none` from an empty stack), peek into a register, set a register (`Act.run`);
   - conditions `Cond` (a register holds a value; negation; conjunction; `Cond.eval`);
   - code `Code`: `skip`, `act`, `seq`, `ite`, `loop` (while), `call p`, with decidable
     equality;
   - programs `Program`: a body for each procedure `p : P` and a main procedure; procedures may
     recurse, and registers are global.
2. **Semantics:** `Exec prog x c c' n`, big-step with step counts: `1` for `skip`, an action, a
   `seq` and each test of `ite` and `loop`; a call costs its body plus `2`. The interpreter
   `run` (fuel-bounded, computable) agrees with `Exec` when the fuel is at least the count
   (`run_of_exec`) and is sound (`exec_of_run`). So `Exec` is deterministic in the result and
   the count (`Exec.det`).
3. **The machine** (`Machine.lean`). Labels are continuations: the code still to run in the
   current procedure.
   - `reach c k`: the labels met while running `c` before `k`. Local successors stay in
     `reach c k` or return to `k` (`reach_succ`), and so do tails (`reach_tail`).
   - `labs prog = {[]} ∪ ⋃_p reach (body p) []` is an explicit `Finset`. `Label prog` is its
     subtype.
   - `toFinTM2 prog kin kout : FinTM2`:
     - stacks `Option K`: `some k` for the program's stacks (alphabet `Γ`) and `none` for the
       return stack (alphabet `Label prog`);
     - local state: the registers and a return slot;
     - input stack `some kin`, output stack `some kout`; every alphabet is finite.
   - Each `skip`, action, `seq` and test is one step. `call p :: k` pushes `k` and jumps to
     `[body p]`; the label `[]` pops a return address into the slot and jumps to it, or halts
     on an empty return stack.
4. **Simulation** (`sim`): an `Exec` of `n` steps from `c` to `c'` is exactly `n` machine steps
   from the label `x :: k` to the label `k`. This holds for every continuation `k` and return
   stack, with the program's stacks and registers as in `c` and `c'`. **`halts`**: `main` takes
   one more step, to the halting configuration (return slot empty).
5. **Outputs.** `inCfg k l` is the configuration with `l` on stack `k`, every other stack
   empty and the registers empty; mathlib's `initList` and `haltList` are exactly these
   (`initList_eq`, `haltList_eq`).
   - **`outputsInTime`**: if `Exec prog (body main) (inCfg kin l) (inCfg kout l') n`, then
     `TM2OutputsInTime (toFinTM2 prog kin kout) l (some l') (n + 1)`.
   - **`computableInTime`**: if for every `a` some `n ≤ T |ea a|` has
     `Exec prog (body main) (inCfg kin (ea a)) (inCfg kout (eb (f a))) n`, then
     `TM2ComputableInTime ea eb f` with time `T + 1`, input and output alphabet `Γ`. The step
     counts are computed by `run` (`stepsOf`).
6. **Checks** (`GraphIsoChecks/TMCode.lean`):
   - **A recursive program** `negProg` over three stacks and one register complements a list
     of Booleans, preserving the order. The procedure pops a bit, saves it, calls itself,
     restores the bit and pushes its complement. Its exact semantics: `negBody_exec`
     (`12 |l| + 4` steps) and `main_exec` (`12 |l| + 8`). This gives
     `negTM : TM2ComputableInTime id id (List.map not)` with time `12 L + 9`.
   - **Kernel runs:** the interpreter on `[true, false, true]` (`44` steps). The compiled
     machine's `step` on `[true, false]` reaches the halting configuration after exactly `33`
     steps, with output `[false, true]`, other stacks empty and the state reset.
   - **Negative control:** it is still running before step `33` (`running_lt_33`), so
     `TM2OutputsInTime` in `32` steps is impossible (`not_outputs_32`).

**Not covered:** arithmetic, the heap, input and output, and the compiler from the cost
language (17b–17e), and graph isomorphism (17f).

## Milestone 16, stage 16b: the unconditional theorems (`PLAN-16.md` §5)

Stage 16a is done (`3a240b2`). This stage adds `GraphIso/Main/QPJ.lean` (imports
`GraphIso.Main.GraphQP`) and `GraphIso/Wielandt/Final.lean` (also `GraphIso.Pyber.Discharge` and
`GraphIso.Wielandt.Bound`). No milestone 14 module is edited, and no existing statement changes.
The new targets are `QPHyp.toJ`, `mainSolve_qp_expJ`, `giSolve_qp_expJ`, `gi_qp_simpleGraphJ`,
`qpHypJ_final`, `mainSolve_final`, `giSolve_final` and `gi_simpleGraph_final`.

**Milestone 16 is complete: the graph-isomorphism theorems hold with no hypothesis.** There is
`c` such that the closed entry at `qpSolver 192 181` (Schreier–Sims substituted, no oracle)
decides isomorphism of graphs on `n` points with local cost at most `2^{c (λ(n) + 1)⁸}`, and on
simple graphs returns exactly the coset of the isomorphisms. Both interfaces of milestone 12 are
discharged without CFSG: `AltQuotientIso Kpy` (milestone 15) and `TransitivityBound Tq`
(stage 16a).

`QPHyp` itself is still not shown satisfiable, so the notes of milestone 14 saying so stay true:
it asks for `T m ≤ C' (λ(m) + 1)` (Wielandt's bound), which `Tq` does not meet
(`not_qpHyp_Tq`). The unconditional theorems go through the generalized hypothesis `QPHypJ`.
Its `SharpHyp` (`sharpHyp_qpJ qpHypJ_final`) is the satisfiable instance that
`GraphIso.Main.FullSharp`'s note looks forward to.

1. **The generalized hypothesis** (`QPJ.lean`). `QPHypJ K T C C' j` has the fields of
   `QPHyp K T C C'` (`AltQuotientIso K`, `K` monotone, `K n ≤ C (λ(n) + 1)⁵`,
   `TransitivityBound T`), with `T m ≤ C' (λ(m) + 1)` replaced by the two consequences that
   milestone 14 uses: `TBelow T (ℓT C')` and `supTo T m ≤ j n₀` for `m ≤ 2 n₀`.
   `QPHyp.toJ`: `QPHyp K T C C'` gives `QPHypJ K T C C' (jMaxQ C')`.
2. **Milestone 14's proofs with `j` for `jMaxQ C'`** (`QPJ.lean`), at the same programs
   `thrQP C C'`:
   - the corner values `qpM4J`, `qpM5J`, `qpCasesJ`, `qpWorkJ`, `qpFacJ` and
     `Q(n₀) = QQPJ C C' j n₀`, with `QQP C C' = QQPJ C C' (jMaxQ C')` by definition
     (`QQP_eq_QQPJ`);
   - the thresholds (`thresholds_qpJ`, `sharpHyp_qpJ`); the bounds (`caseWorkS_le_qpCasesJ`,
     `mainWorkS_le_QQPJ`, `caseFAB_le_QQPJ`, `winSize_add_two_le_QQPJ`); the potential
     (`pot_ind_stepJ`, `main_potJ`); the headlines (`mainSolve_qpJ`, `mainSolve_qp_closedJ`);
   - for `j ∈ PLB λ 5`: the growth of the corner values (`Growth.Main.qpM4J_qpb` to
     `Growth.Main.QQPJ_qpb`), `QQPJ_le_exp` (`Q(n₀) ≤ 2^{c (λ(n₀) + 1)⁶}`), and
     **`mainSolve_qp_expJ`**, `mainSolve_qp_gensJ`, `mainSolve_qp_exp_gensJ`,
     **`giSolve_qp_expJ`**, **`gi_qp_simpleGraphJ`**: milestone 14's headlines with `QPHypJ` in
     place of `QPHyp`: for all `C`, `C'` and `j ∈ PLB λ 5` there is `c` such that under
     `QPHypJ K T C C' j` the statements of `mainSolve_qp_exp`, `giSolve_qp_exp` and
     `gi_qp_simpleGraph` hold, with the cost `2^{c (λ + 1)⁸}`.
3. **The hypothesis holds** (`Final.lean`). `Tq` is monotone (`Tq_mono`, `supTo_Tq_le`);
   `TBelow Tq (ℓT 181)` (`tBelow_Tq`: above `ℓT 181 = 64 · 182² > 2²¹`, `λ(m) ≥ 21` and
   `4 Tq m + 6 ≤ 1024 (λ(m) + 1)² + 6 ≤ 2^{λ(m)} ≤ m`, `sq_le_two_pow`); the depth bound
   `jq n₀ = Tq (2 n₀)` is in `PLB λ 5` (`jq_plb`). Hence
   **`qpHypJ_final : QPHypJ Kpy Tq 192 181 jq`**, from `altQuotientIso_pyber`, `Kpy_mono`,
   `Kpy_le_lam` and `transitivityBound_quad`.
4. **The unconditional headlines** (`Final.lean`), each `∃ c, ∀ inputs, …` with no hypothesis:
   - **`mainSolve_final`**: on every valid plain instance (window `w`, permutation `σd`,
     generators `gs` on `N` points, `w` invariant under `⟨gs⟩`), `mainEntry (thrQP 192 181)`
     returns a correct answer (`AnsOK`) within `genCost N |gs| + 2^{c (λ(N) + 1)⁸}`;
   - **`giSolve_final`**: on valid graph data `X`, `Y` on `n` points (any degree), the closed
     entry at `qpSolver 192 181` returns a `GICosetOK` result with local cost at most
     `2^{c (λ(n) + 1)⁸}`;
   - **`gi_simpleGraph_final`**: for simple graphs `G`, `H` on `Fin n`, the result `r` has local
     cost at most `2^{c (λ(n) + 1)⁸}`; `r = none` exactly when `G ≃g H` is empty, and
     `r = some (τ, hs)` gives valid data with `τ • ⟨hs⟩` equal to the set of the permutations
     underlying the isomorphisms `G ≃g H`.
5. **Checks** (`GraphIsoChecks/WielandtFinal.lean`): `ℓT 181 = 2119936 > 2²¹`, `jq 1 = 1024`
   (kernel `decide`) and `sq_le_two_pow` at `21`; a negative control: for every `C'`,
   `Tq m ≤ C' (λ(m) + 1)` fails at `m = 2^{C'}` (`not_tle_Tq`), so `¬QPHyp K Tq C C'`
   (`not_qpHyp_Tq`) and the generalization is needed; `qpHypJ_final`; `gi_simpleGraph_final`
   on the empty graphs on `Fin 3` gives a run with a nonempty answer.

**The CFSG-free route of `PLAN-12.md` is complete.** Weaker than planned: the transitivity bound
is `Tq m = 256 (λ(m) + 1)²`, not Wielandt's `3 ln m` (`PLAN-16.md` §1), which leaves the
exponent `8` unchanged.

## Milestone 16, stage 16a: the transitivity bound (`PLAN-16.md` §3)

Milestone 15 is done (`e4bff1d`). This stage is in `GraphIso/Wielandt/`: `Commutator.lean`,
`Support.lean`, `Power.lean` (mathlib imports only) and `Bound.lean` (also the interfaces). No
existing statement changes. The new targets are `alternatingGroup_le_of_support_le`,
`exists_pow_support_lt`, `exists_mem_orderOf_dvd` and `transitivityBound_quad`.

**`TransitivityBound` is discharged without CFSG**, with `Tq m = 256 (λ(m) + 1)²`: a
`t`-transitive group of degree `n` not containing `Alt(n)` has `t ≤ 256 (λ(n) + 1)²`. This is
weaker than Wielandt's `t < 3 ln n` (`wielandtT`), which `QPHyp` would need (`T m ≤ C' (λ(m) + 1)`);
stage 16b generalizes milestone 14's analysis to this `T`. The departure is recorded in
`PLAN-16.md` §1: Wielandt's proof needs his theorem on sections of groups of large minimal degree,
whose proof was not available.

1. **Commutators** (`Commutator.lean`). For `x, y ∈ Sym(Ω)` and `I = supp x ∩ supp y`:
   `supp ⁅x, y⁆ ⊆ I ∪ x(I) ∪ y(I)` (`support_commutatorElement_subset`), so
   `|supp ⁅x, y⁆| ≤ 3 |I|` (`card_support_commutatorElement_le`); commutators are even
   (`sign_commutatorElement`); if `|I| = 1` and `⁅x, y⁆ ≠ 1`, then `⁅x, y⁆` is a `3`-cycle
   (`isThreeCycle_commutatorElement`).
2. **Support reduction** (`Support.lean`), for `G ≤ Sym(Ω)` `3`-transitive (`|Ω| = n`):
   - `3`-transitivity on triples of distinct points (`exists_mem_map3`, via `emb3`);
   - **averaging** (`exists_mem_card_inter_le`): for `a, a' ∈ S` distinct and `b ∉ S`, some
     `h ∈ G` with `h a = a`, `h a' = b` has `(n − 2) |{w ∈ S | h w ∈ S}| ≤ (n − 2) +
     (|S| − 1)(|S| − 2)` (`card_inter_map_eq` turns this into `|S ∩ h(S)|`);
   - the arithmetic of the reduction (`three_mul_lt`);
   - **small supports give `3`-cycles** (`exists_isThreeCycle_mem`): `x ∈ G`, `x ≠ 1`,
     `6 |supp x| ≤ n`; with `y = h x h⁻¹` for `a ∈ supp x`, `a' = x a`, `b ∉ supp x` and `h` as
     above, `⁅x, y⁆ ≠ 1` (at `a`) is a `3`-cycle or has smaller support, by strong induction;
   - **`alternatingGroup_le_of_support_le`**: under the same hypotheses `Alt(Ω) ≤ G` (mathlib's
     Jordan theorem for primitive groups with a `3`-cycle).
3. **Babai–Seress** (`Power.lean`): **`exists_pow_support_lt`**: for `σ ∈ Sym(Ω)`, if
   `n^n < (ord σ)^s`, some `σ^m ≠ 1` moves fewer than `s` points (with
   `prod_dvd_of_pairwise_coprime` and `ordProj_dvd_of_not_dvd_div`).
4. **The bound** (`Bound.lean`):
   - the cycle lengths `p^{⌊log_p x⌋}` (`lcmCycles`), with sum at most `x²` (`card_primesLE_le`,
     `sum_lcmCycles_le`) and each at least `2` (`two_le_of_mem_lcmCycles`), give `τ ∈ Sym(t)`,
     `t ≥ x²`, with `lcm(1, …, x) ∣ ord τ` (`exists_perm_lcmUpto_dvd`);
   - **lifting** (`exists_mem_orderOf_dvd`): a `t`-transitive `G ≤ Sym(Λ)`, `t ≤ |Λ|`, has `g`
     with `ord τ ∣ ord g` for each `τ ∈ Sym(t)`;
   - **`transitivityBound_quad : AltQuot.TransitivityBound Tq`**: with `x = 7 λ(n) + 14`,
     `n^6 (x + 1) ≤ 2^x ≤ (x + 1) lcm(1, …, x)` (`seven_mul_add_le`,
     `Chebyshev.two_pow_le_mul_lcmUpto`), so `ord g ≥ n^6`, a power of `g` moves at most `n/6`
     points, and `Alt(n) ≤ G`.
5. **Checks** (`GraphIsoChecks/WielandtBound.lean`): `⁅(0 1 2), (2 3 4)⁆` in `Sym(5)` is a
   `3`-cycle (one common point, kernel `decide`); Babai–Seress on
   `σ = (0 1)(2 3 4)(5 6 7 8 9)` (`ord σ = 30`, `10^10 < 30^7`; `σ^15 = (0 1)`); a negative
   control: the rotations of `Fin 4` are transitive without `Alt(4)`, so
   `TransitivityBound (fun _ => 0)` fails; `Tq 1 = 256`, `Tq 1024 = 30976`.

**Not covered:** milestone 14's generalization to `Tq` and the unconditional theorems
(stage 16b).

## Milestone 15, stage 15d: Lemma 12 and the discharge (`PLAN-15.md` §6)

Stage 15c is done (`8275b46`). This stage is in `GraphIso/Pyber/`: `Primes.lean` (mathlib imports
only), `Lemma12.lean` (also `GraphIso.AltQuot.Interfaces`) and `Discharge.lean` (also the
milestone 14 headlines, `GraphIso.Main.GraphQP`). No existing statement changes. The new targets
are `card_primesLE_ge`, `exists_mem_alternatingGroup`, `injective_of_surjective_alt`,
`altQuotientIso_pyber`, `qpHyp_pyber`, `mainSolve_qp_exp_pyber`, `giSolve_qp_exp_pyber` and
`gi_qp_simpleGraph_pyber`.

**Milestone 15 is complete: `AltQuotientIso` is discharged without CFSG**, with the threshold
`Kpy n = 192 (λ(n) + 1)⁵`. `QPHyp` now reduces to `TransitivityBound T` with
`T m ≤ C' (λ(m) + 1)` (Wielandt's bound, milestone 16). The milestone 14 modules are not edited:
their notes that `QPHyp` is not yet shown satisfiable stay true until milestone 16.

1. **The primes** (`Primes.lean`). Pyber's Proposition 11 is replaced by Chebyshev's elementary
   bound in mathlib's natural-number form, `2^N ≤ (N + 1) lcm(1, …, N)`
   (`Chebyshev.two_pow_le_mul_lcmUpto`); no real analysis is used (`Chebyshev.pi_ge` of §1 is
   not needed).
   - `lcm(1, …, N) ≤ N^{π(N)}` (`lcmUpto_le_pow`), so `2^N ≤ (N + 1) N^{π(N)}`
     (`two_pow_le_mul_pow_card`);
   - **many primes** (`card_primesLE_ge`): `2 L² + 1 ≤ π(64 L³)` for `L ≥ 1`;
   - **odd primes** (`exists_odd_primes`): for `L ≥ 1` and `R ≤ 2 L²`, a set of `R` primes
     `≠ 2`, each at most `64 L³`;
   - **the permutation** (`exists_mem_alternatingGroup`): for a finite set `s` of odd primes
     with `∑ s ≤ |Λ|`, some `σ ∈ alternatingGroup Λ` has `p ∣ orderOf σ` for every `p ∈ s`.
2. **Lemma 12** (`Lemma12.lean`). `Kpy n = 192 (λ(n) + 1)⁵` is monotone (`Kpy_mono`).
   - **The abstract form** (`injective_of_surjective_alt`): for `G Ω Λ : Type`, `G` finite
     acting faithfully and primitively on a finite `Ω`, `Λ` a `Fintype` with decidable equality,
     and `φ : G →* alternatingGroup Λ` surjective with `Kpy |Ω| ≤ |Λ|`: `φ` is injective. With
     `ℓ = λ(|Ω|)`, a nontrivial kernel `N` is transitive; take `2 ℓ² + ℓ + 2` odd primes of at
     most `64 (ℓ + 1)³` each (sum at most `Kpy |Ω|`, `lemma12_arith`) and `σ` as in item 1;
     `H = φ⁻¹(⟨σ⟩) ⊇ N` is transitive and faithful and maps onto `⟨σ⟩`, so `compA H` contains
     the primes, against Theorem 7 (`ncard_compA_le_of_transitive`: at most `2 ℓ² + ℓ + 1`).
   - **The interface** (`altQuotientIso_pyber`): `AltQuot.AltQuotientIso Kpy`.
3. **The discharge** (`Discharge.lean`).
   - `qpHyp_pyber`: `TransitivityBound T` and `∀ m, T m ≤ C' (λ(m) + 1)` give
     `QPHyp Kpy T 192 C'` (`Kpy_le_lam`: `Kpy n ≤ 192 (lam n + 1)⁵`).
   - **The headlines under Wielandt's bound alone:** `mainSolve_qp_exp_pyber`,
     `giSolve_qp_exp_pyber` and `gi_qp_simpleGraph_pyber` are `mainSolve_qp_exp`,
     `giSolve_qp_exp` and `gi_qp_simpleGraph` at `C = 192`, with the hypothesis
     `QPHyp K T C C'` replaced by `TransitivityBound T` and `∀ m, T m ≤ C' (λ(m) + 1)`, and
     nothing else changed: for every `C'` there is `c` such that for every such `T` the closed
     programs at `thrQP 192 C'` are correct within `genCost N |gs| + 2^{c (λ(N) + 1)⁸}`
     (respectively local cost `2^{c (λ(n) + 1)⁸}` on graphs).
4. **Checks** (`GraphIsoChecks/PyberLemma12.lean`):
   - the prime count at `L = 1`: `π(64) = 18` (kernel `decide`) and `card_primesLE_ge`'s
     instance `3 ≤ π(64)`;
   - the permutation for `s = {3, 5, 7}` in `Alt(15)`;
   - a negative control for the threshold: `Sym(3)` on `Fin 3` maps onto the trivial `Alt(2)`
     (`subsingleton_alt2`) by a surjective, non-injective homomorphism; `|Λ| = 2 < Kpy 3`;
   - the numbers `Kpy 1 = 192`, `Kpy 3 = 6144`, and the arithmetic of Lemma 12 for `ℓ < 32`.

**Not covered:** Wielandt's bound `TransitivityBound T` with `T m ≤ C' (λ(m) + 1)`
(milestone 16). It is still a hypothesis of the headlines.

## Milestone 15, stage 15c: Theorem 7 (`PLAN-15.md` §5)

Stage 15b is done (`01b0d5c`). This stage is in `GraphIso/Pyber/` with mathlib imports only:
`Wielandt.lean`, `MinNormal.lean`, `Imprimitive.lean` and `Theorem7.lean`. No existing statement
changes. The new targets are `compA_suborbitKer_subset`, `compA_stabilizer_subset`,
`card_le_of_comm`, `compA_subset_of_noncomm`, `card_le_or_compA_subset`, `compA_subset_union_core`,
`exists_ncard_compA_le`, `ncard_compA_le_of_coreFree`, `ncard_compA_stabilizer_le` and
`ncard_compA_le_of_transitive`.

As in stage 15b, `H` is core-free when `H.normalCore = ⊥`, `Faithful G Ω` says that only `1`
fixes every point, `Δ(x) = orbit (stabilizer G x) y`, and `λ = Nat.log 2`. Write `G_{xy}` for
`stabilizer G x ⊓ stabilizer G y`.

1. **Wielandt's Lemma 4, self-paired form** (`Wielandt.lean`).
   - `suborbitKer G x y a` (`T(a)`) is the `fixingSubgroup` of `a` and of every `b` with
     `(a, b) ∈ orbit G (x, y)` (`mem_suborbitKer`). It lies in `G_a ⊓ G_b` for `(a, b)` in the
     orbital (`suborbitKer_le`) and is normal there (`suborbitKer_normal`,
     `suborbitKer_normal_self`); `T(g • a) = g T(a) g⁻¹` (`suborbitKer_smul`), and
     `G_{g a} ⊓ G_{g b} = g (G_a ⊓ G_b) g⁻¹` (`stabilizer_inf_smul`).
   - A chain does not change the residual (`resid_eq_of_schain`).
   - **The lemma** (`compA_suborbitKer_subset`): for a faithful primitive action of a finite
     group, `x ≠ y` and `(y, x) ∈ orbit G (x, y)`: `compA T(x) ⊆ compA (G_{xy} ⧸ T(x))`.
   - **The corollary** (Pyber's `(∗)`, `compA_stabilizer_subset`): under the same hypotheses,
     `compA G_x ⊆ compA P ∪ compA P_y`, where `P` is the range of
     `toPermHom (stabilizer G x) Δ(x)` and `P_y` the stabilizer of `⟨y, _⟩` in `P`. The kernel
     of `G_x → P` is `T(x)` (`ker_toPermHom_suborbit`).
2. **Minimal normal subgroups of primitive groups** (`MinNormal.lean`; Pyber's Lemma 10 without
   socles). For a faithful action:
   - primitive: a normal `N ≠ ⊥` is transitive (`isPretransitive_of_normal`);
   - a commutative transitive `N` has trivial point stabilizers (`stabilizer_eq_bot_of_comm`)
     and, for finite `G`, `|N| = |Ω|` (`card_eq_of_comm`);
   - for `N` transitive and generated by a list `l`, elements of `G_x` with the same conjugates
     of every member of `l` are equal (`conj_injective`);
   - finite `G` and `Ω`, primitive, `N` normal, commutative and `≠ ⊥`:
     `|G| ≤ |Ω|^(λ(|Ω|) + 1)` (`card_le_of_comm`);
   - finite `G`, primitive, `N` minimal normal and noncommutative: `compA G ⊆ compA G_x`
     (`compA_subset_of_noncomm`);
   - **the dichotomy** (`card_le_or_compA_subset`): finite nontrivial `G`, finite `Ω`, primitive:
     `|G| ≤ |Ω|^(λ(|Ω|) + 1)` or `compA G ⊆ compA G_x`.
3. **Lemma 8, abstract form** (`Imprimitive.lean`).
   - For a finite group `A` and any `L ≤ A`: `compA L ⊆ compA A ∪ compA L'`, where `L'` is the
     image of `L` in `A ⧸ L.normalCore` (`compA_subset_union_core`). `compA (K ⊓ H)` is the same
     inside `H` and inside `K` (`compA_subgroupOf_comm`).
   - **The lemma** (`exists_ncard_compA_le`): for any `F : ℕ → ℕ` and `n`, if every core-free
     subgroup of index `m < n` of a finite group in `Type` has `|compA| ≤ F m`, then every
     core-free `H` of index `n` of a finite `G : Type`, neither `⊤` nor maximal, has
     `|compA H| ≤ F t + F b + λ(b)` for some `t, b ≥ 2` with `t b = n`.
4. **Theorem 7** (`Theorem7.lean`):
   - for `G : Type` finite and `H` core-free, `|compA H| ≤ 2 λ([G : H])² + 1`
     (`ncard_compA_le_of_coreFree`, by strong induction on the index in
     `ncard_compA_le_of_coreFree_aux`);
   - for `G Ω : Type`, `G` finite, acting faithfully and transitively:
     `|compA G_x| ≤ 2 λ(|Ω|)² + 1` (`ncard_compA_stabilizer_le`), and, for `Ω` nonempty,
     `|compA G| ≤ 2 λ(|Ω|)² + λ(|Ω|) + 1` (`ncard_compA_le_of_transitive`);
   - the suborbit size: `|Δ(x)| < |Ω|` for `x ≠ y` and `Ω` finite (`ncard_suborbit_lt`);
   - the arithmetic: `tri_le_F`, `F_mono`, `F_add_le`, `F_add_add_le`, `log_pow_lt`,
     `log_pow_le_F`.
5. **Checks** (`GraphIsoChecks/PyberThm7.lean`):
   - Wielandt's lemma and its corollary on `Sym(3)` at the self-paired orbital of `(0, 1)`;
   - Theorem 7 on `Sym(4)` (`faithful_perm4`): `|compA G_0| ≤ 9` and `|compA G| ≤ 11`;
   - a negative control for core-freeness: in `Sym(3)`, `⊤` has index `1` and
     `|compA ⊤| = 2 > 2 λ(1)² + 1 = 1`;
   - the dichotomy: on `Alt(3)` (`isPreprimitive_alt3`, `nontrivial_alt3`), where the first
     alternative holds (`3 ≤ 9`); on `Sym(8)`, where `8! > 8^4` rules it out, so
     `compA Sym(8) ⊆ compA G_0`;
   - the three inequalities of the induction for small values (kernel `decide`).

**Not covered:** the primes, Lemma 12, and the discharge of `AltQuotientIso` (stage 15d).
`AltQuotientIso` and `TransitivityBound` are still hypotheses.

## Milestone 15, stage 15b: permutation groups and the odd-order bound (`PLAN-15.md` §4)

Stage 15a is done (`f877fa3`). This stage is in `GraphIso/Pyber/` with mathlib imports only:
`Bridge.lean`, `Orbital.lean` and `OddOrder.lean`. No existing statement changes. The new targets
are `card_primeFactors_le_of_odd`, `card_primeFactors_le_of_odd_action`, `prime_dvd_card_range`,
`eq_univ_of_closed`, `two_mul_ncard_suborbit_add_one_le`, `normalCore_stabilizer_eq_bot`,
`faithful_quotient`, `isPreprimitive_quotient`, `normalCore_map_mk`, `index_map_mk`,
`primeFactors_card_subset` and `compA_subset_compA_quot`. Wielandt's Lemma 4 moved to stage 15c.

A subgroup `H` is *core-free* when `H.normalCore = ⊥`. `Faithful G Ω` says that only `1` fixes
every point. The orbital of `(x, y)` is `orbit G (x, y)` for the diagonal action on `Ω × Ω`, and
the suborbit is `Δ(x) = orbit (stabilizer G x) y`; no new notion is defined for either.

1. **Bridges.**
   - A point stabilizer of a faithful transitive action is core-free
     (`normalCore_stabilizer_eq_bot`), of index `|Ω|` (mathlib's
     `index_stabilizer_of_transitive`). A subgroup of `Perm Ω` acts faithfully
     (`faithful_perm`); the image of a transitive action in `Perm Ω` acts transitively
     (`isPretransitive_range`).
   - For `H` core-free, `G` acts faithfully on `G ⧸ H` (`faithful_quotient`), where the
     stabilizer of the base coset is `H` (mathlib's `stabilizer_quotient`). `G ⧸ H` is
     nontrivial when `H ≠ ⊤` (`nontrivial_quotient`), and the action is primitive when `H` is
     maximal (`isPreprimitive_quotient`).
2. **Reductions.**
   - For every subgroup `L`, the image of `L` in `G ⧸ L.normalCore` is core-free
     (`normalCore_map_mk`) of index `[G : L]` (`index_map_mk`).
   - For finite `G`, `H` core-free, `K` normal, and `J` the core of `H ∩ K` in `K`
     (`(H.subgroupOf K).normalCore`): every prime factor of `|K|` is a prime factor of
     `|K ⧸ J|` (`primeFactors_card_subset`), and `compA K ⊆ compA (K ⧸ J)`
     (`compA_subset_compA_quot`).
   - If `H` is core-free, `H ⋖ M`, and `K ≤ M` is normal with `K ≠ ⊥`, then `K ⊔ H = M`
     (`sup_eq_of_covBy`); for finite `G`, `K ⊔ H = M` gives `[K : H ∩ K] = [M : H]`
     (`relIndex_eq_of_sup_eq`). For finite `G`, if `H` is neither `⊤` nor maximal, some `M ≠ ⊤`
     covers `H` (`exists_covBy_ne_top`).
3. **Orbitals.**
   - `b ∈ Δ(x) ↔ (x, b) ∈ orbit G (x, y)` (`mem_orbit_stabilizer_iff`);
     `|Δ(x)| = [G_x : G_y ⊓ G_x]` (`ncard_orbit_stabilizer`); the orbital is invariant
     (`smul_mem_orbit_pair`) and misses the diagonal when `x ≠ y` (`diag_notMem_orbit`).
   - For finite `G` and `Ω` and a transitive action, the paired suborbit
     `{b | (b, x) ∈ orbit G (x, y)}` has the size of `Δ(x)` (`ncard_paired_eq`, from
     `relIndex_comm_of_index_eq`).
   - For finite `G` of odd order and `x ≠ y`: `(y, x) ∉ orbit G (x, y)`
     (`swap_notMem_orbit`); and, for a transitive action on a finite `Ω`,
     `2 |Δ(x)| + 1 ≤ |Ω|` (`two_mul_ncard_suborbit_add_one_le`).
   - If `g * g = 1`, then `(g • x, x) ∈ orbit G (x, g • x)` (`swap_mem_orbit_of_mul_self`).
4. **Connectivity** (`eq_univ_of_closed`): for a primitive action of a finite group, `x ≠ y`,
   and `F ∋ x` with `a ∈ F → (a, b) ∈ orbit G (x, y) → b ∈ F`: `F = Set.univ`.
5. **Jordan's Lemma 1** (`prime_dvd_card_range`): for a faithful primitive action of a finite
   group and `x ≠ y`, every prime dividing `|G_x|` divides the order of the range of
   `toPermHom (stabilizer G x) Δ(x)`.
6. **The odd-order bound** (the claim in Pyber's Lemma 2), with `ω(m) = |m.primeFactors|` and
   `λ = Nat.log 2`:
   - for `G : Type` finite with `|G|` odd and `H` core-free,
     `ω(|G|) ≤ λ([G : H]) (λ([G : H]) + 1) / 2` (`card_primeFactors_le_of_odd`, by strong
     induction on the index in `card_primeFactors_le_of_odd_aux`);
   - for `G Ω : Type`, `G` finite of odd order, acting faithfully and transitively,
     `ω(|G|) ≤ λ(|Ω|) (λ(|Ω|) + 1) / 2` (`card_primeFactors_le_of_odd_action`);
   - the arithmetic: `tri_add_le`, `tri_mono`, `add_tri_le`, `two_mul_tri`, `log_add_log_le`,
     `log_add_one_le`, `card_primeFactors_mul_le`.
7. **Checks** (`GraphIsoChecks/PyberPerm.lean`):
   - `Sym(3)` on `Fin 3`: the orbital of `(0, 1)` is self-paired (`selfPaired_perm3`),
     `Δ(0) = {1, 2}` (`suborbit_perm3`), so `2 |Δ(0)| + 1 = 5 > 3`, a negative control for the
     odd-order hypothesis; Jordan's lemma with `|G_0| = 2` (`card_stabilizer_perm3`);
   - `Alt(3)` on `Fin 3` (odd order `3`): the orbital of `(0, 1)` is not self-paired,
     `2 |Δ(0)| + 1 ≤ 3`, and `ω(3) ≤ 1` from the odd-order bound;
   - a negative control for connectivity: the rotations of `Fin 4` act transitively
     (`isPretransitive_rot4`), and `{0, 2}` is closed along the orbital of `(0, 2)` (from
     `rot_add_two`) but is not everything;
   - the two inequalities of the induction for `n < 64` and for `t, b < 24` (kernel `decide`).

**Not covered:** Wielandt's Lemma 4 and Theorem 7 (stage 15c), and the primes and Lemma 12
(15d). `AltQuotientIso` and `TransitivityBound` are still hypotheses.

## Milestone 15, stage 15a: the group theory of `compA` (`PLAN-15.md` §3)

Milestone 14 is complete. Milestone 15 discharges the interface `AltQuotientIso` without CFSG,
following Pyber (arXiv:1605.08266), with the threshold `Kpy n = 192 (λ(n) + 1)⁵`
(`PLAN-15.md` §1). This first stage is group theory only, in `GraphIso/Pyber/` with mathlib
imports only: `CompA.lean`, `Families.lean`, `Residual.lean` and `Generators.lean`. No existing
statement changes. The new targets are `compA_sdiff_subset`, `compA_subset_union`,
`compA_subset_iUnion_of_iInf`, `compA_subset_iUnion_of_iSup`, `compA_eq_empty_of_charSimple` and
`compA_subset_of_schain`.

1. **The definition.** `compA G` is the set of primes `p` for which `G` has subgroups `B ≤ A`
   with `A` subnormal (mathlib's `Subgroup.IsSubnormal`), `B` normal in `A`, and
   `B.relIndex A = p`. By Schreier refinement and Jordan–Hölder these are the orders of the
   abelian composition factors (Pyber's `Comp_A`). That equivalence is neither proved nor used:
   every property is proved from the definition.
2. **Basic properties.**
   - For finite `G`, `compA G ⊆ primeFactors |G|` (`compA_subset_primeFactors`). Hence
     `|compA G| ≤ ω(|G|) ≤ ⌊log₂ |G|⌋` (`ncard_compA_le_card_primeFactors`, `ncard_compA_le`),
     with `|primeFactors m| ≤ ⌊log₂ m⌋` for every `m` (`card_primeFactors_le_log`).
   - A surjective homomorphism `G →* G'` gives `compA G' ⊆ compA G`, so isomorphic groups have
     equal `compA` (`compA_subset_of_surjective`, `compA_eq_of_mulEquiv`).
   - An injective homomorphism with subnormal range gives `compA G ⊆ compA G'`; in particular
     `compA H ⊆ compA G` for `H` subnormal (`compA_subset_of_injective`,
     `compA_subset_of_isSubnormal`).
   - A normal subgroup of prime index `p` gives `p ∈ compA G` (`mem_compA_of_index`). For finite
     commutative `G`, every prime dividing `|G|` is in `compA G` (`mem_compA_of_comm`). A finite
     nonabelian simple group has `compA G = ∅` (`compA_eq_empty_of_isSimpleGroup`).
   - **Extensions** (finite `G`, `N` normal): `compA G ⊆ compA N ∪ compA (G ⧸ N)`
     (`compA_subset_union`), from `[A : B] = [A ⊓ N : B ⊓ N] · [A ⊔ N : B ⊔ N]`
     (`relIndex_eq_mul_relIndex`). The form with a homomorphism `f` whose range is subnormal is
     `compA G ⊆ compA (ker f) ∪ compA G'` (`compA_subset_union_of_hom`).
3. **Pyber's Proposition 3** (`compA_sdiff_subset`): for finite `G` and every subgroup `H`,
   `compA G ∖ compA H ⊆ primeFactors [G : H]`. For `A` subnormal, `[A : A ⊓ H]` divides
   `[G : H]` (`relIndex_dvd_index_of_isSubnormal`).
4. **Families of normal subgroups** (finite `G`, finite index type, every `N i` normal):
   - if `⨅ i, N i = ⊥`, then `compA G ⊆ ⋃ i, compA (G ⧸ N i)` (`compA_subset_iUnion_of_iInf`,
     Pyber's Proposition 6). The general form takes homomorphisms with subnormal ranges and
     trivially intersecting kernels (`compA_subset_biUnion_of_ker`);
   - if `⨆ i, N i = ⊤`, then `compA G ⊆ ⋃ i, compA (N i)` (`compA_subset_iUnion_of_iSup`).
5. **Characteristically simple groups** (`compA_eq_empty_of_charSimple`): if `N` is finite,
   nontrivial and noncommutative, and its only characteristic subgroups are `⊥` and `⊤`
   (`CharSimple N`), then `compA N = ∅`. A nontrivial finite group has a minimal normal subgroup
   (`exists_isMinNormal`), and a minimal normal subgroup is characteristically simple as a group
   (`IsMinNormal.charSimple`). A finite join of normal solvable subgroups is solvable
   (`isSolvable_biSup`).
6. **Residuals** (Wielandt's `H*` for the class `compA ⊆ S`), for subgroups of a finite `G`:
   - `SChain S A L`: a chain from `A` down to `L`, each step normal with
     `compA (A_i ⧸ A_{i+1}) ⊆ S`. Its end is subnormal in `A` (`SChain.isSubnormal`). Chains
     compose (`SChain.trans`), and are closed under intersection (`SChain.inf`, from
     `SChain.inf_left`: cutting a chain by a subnormal `X` gives a chain from `X`).
   - `resid S A = sInf {L | SChain S A L}`, defined without choice, is reached
     (`schain_resid`).
   - `resid S (A.map e) = (resid S A).map e` for every isomorphism `e` of finite groups
     (`resid_map`). So anything normalizing `A` normalizes `resid S A`
     (`mem_normalizer_resid`).
   - If `B ≤ A` is normal in `A` with `compA (A ⧸ B) ⊆ S`, then `resid S A = resid S B`
     (`resid_eq_of_step`).
   - `SChain S A L → compA A ⊆ S ∪ compA L` (`compA_subset_of_schain`). So
     `resid S A = ⊥ → compA A ⊆ S` (`compA_subset_of_resid_eq_bot`).
7. **Short generating lists** (`exists_list_closure_eq_top`): every finite group is generated by
   a list of at most `⌊log₂ |G|⌋` elements.
8. **Checks** (`GraphIsoChecks/Pyber.lean`, instantiations with kernel `decide` for numbers):
   - `compA (Perm (Fin 3)) = {2, 3}`, and `compA` of the cyclic group of order `12` is `{2, 3}`;
   - a negative control: `compA (alternatingGroup (Fin 5)) = ∅`, while the prime factors of
     `60` are `{2, 3, 5}`, through both the simple-group and the characteristically simple
     theorems;
   - Proposition 3 on `Alt(3) ≤ Sym(3)`;
   - in `Sym(3)`, `resid {2, 3} ⊤ = ⊥` and `resid {2} ⊤ ≠ ⊥`;
   - `Sym(3)` is generated by at most `2` elements;
   - `|primeFactors m| ≤ ⌊log₂ m⌋` for `m < 65`.

**Not covered:** the permutation-group lemmas (stage 15b), Theorem 7 (15c), and the primes and
Lemma 12 (15d). `AltQuotientIso` and `TransitivityBound` are still hypotheses.

## Milestone 14, stage 14j-6c-3: the graph-isomorphism entry (`PLAN-14.md` §14.15)

The procedure run on graphs. The code is in `GraphIso/Main/GraphEntry.lean` (the encoding, the
reduction and the decoding), `GraphEntryProg.lean` (the programs and the entry) and
`GraphQP.lean` (the theorems). The procedure and its programs are unchanged, no protected
statement changes, and `giSolve_ss`, `giSolve_qp_exp` and `gi_qp_simpleGraph` are the new
targets.

1. **The encoding.** For graph data `X`, `Y` on `n` points, let `N = n + n · n`. The point
   `u < n` is the vertex `u`, and the point `n + v + n u` is the ordered pair `(u, v)`.
   - `liftPerm n : Perm (Fin n) →* Perm (Fin N)` is `φ` on the vertices and
     `(u, v) ↦ (φ u, φ v)` on the pairs. It is an injective homomorphism.
   - The string of `X` is `0` at the vertices and, at `(u, v)`, `1` if `Adj X u v` and `0`
     otherwise.
   - The generators are the lifts of `finRotate n` and of the transposition of `0` and `1`
     (none for `n ≤ 1`). They generate the image of `liftPerm` (`gensData_denote`, from mathlib's
     `closure_cycle_adjacent_swap`).
   - The window is all of `Ω`, and the representative is the identity.
   - **The reduction** (`iso_graph`): for valid data of any degree, the solutions are the lifts
     of the isomorphisms `{φ | IsIso n X Y φ}`.

   The ordered pairs follow the vertices, rather than the unordered pairs of the plan's first
   design note. Decoding is then a restriction to the first `n` points, and the language has no
   division.
2. **Decoding** (`decode_ok`). For a correct answer `(τ, H)` of the encoded instance, `τ` and
   every generator of `H` are in the image of the lift. Their restrictions to the first `n`
   points are valid data of `Perm (Fin n)` with `{φ | IsIso n X Y φ} = φ₀ • ⟨hs⟩`. A `none`
   answer means that there is no isomorphism. `GICosetOK n X Y r` collects this, with at most
   `(2N)²` generators.
3. **The programs.**
   - `giEntry` takes `(n, X, Y)`. It builds the offsets `n + n u` (by `mulProg` and addition),
     `N`, the two strings, the window, the identity and the generators. It then runs
     `mainEntry` (one `generate`, then the recursion) and decodes the answer.
   - Each piece computes its model exactly, at a polynomial cost on valid data: `encCost n` in
     all for the encoding, and `decCost n s` for `s` generators. `giEntry` is well formed.
4. **The generator count.** `mainSolve_ss` and `mainSolve_qp` drop the recursion's bound of
   `(2N)²` generators, and decoding is charged per generator. So `mainSolve_ss_gens`,
   `mainSolve_qp_gens` and `mainSolve_qp_exp_gens` keep it. Their proofs are those of the
   protected theorems, which are unchanged.
5. **Correctness on every valid input** (`giSolve_ss`). Take any threshold program with
   `ThrSpec`, with no growth hypothesis, and valid graph data `X`, `Y` on `n` points of any
   degree (`ValidD Δ n` for some `Δ`). The closed entry returns `r` with `GICosetOK n X Y r`,
   within `giCostSS cT n`, which is exponential in general. The closed entry is the program with
   the Schreier–Sims implementations substituted, inside `mainSolver thr`, with no oracle.
6. **The headline.**
   - `giSolve_qp_exp`: for all `C`, `C'` there is `c` such that for all `K`, `T` with
     `QPHyp K T C C'`, on valid graph data on `n` points, the closed entry at `thrQP C C'`
     returns a `GICosetOK` result with local cost at most `2^{c (λ(n) + 1)⁸}`. The bound covers
     the encoding, `generate`, the recursion and the decoding: `λ(N) + 1 ≤ 2 (λ(n) + 1)`, and the
     polynomial parts are at most `1000 (n + 1)¹²`. With `c₁` the constant of
     `mainSolve_qp_exp_gens`, `c = 256 c₁ + 23`.
   - `gi_qp_simpleGraph`: the same for simple graphs `G`, `H` on `Fin n` given by their
     adjacency lists. `r = none` exactly when `IsEmpty (G ≃g H)`, and otherwise `r` gives valid
     data `τ`, `hs` with `τ • ⟨hs⟩` equal to the set of the permutations underlying the
     isomorphisms `G ≃g H`.

   **`QPHyp` is not yet shown satisfiable** (milestones 15 and 16). Correctness (item 5) does not
   depend on it.
7. **Checks** (`GraphIsoChecks/GraphQP.lean`, kernel `decide`):
   - the encoding of the path `P₃` on `12` points, the generators' validity, the lifted `3`-cycle
     at a pair and at a vertex, the window, and the decoding of the lifted `3`-cycle;
   - the entry, run with the verified Schreier–Sims oracle and `mainBody (thrQP 1 3)`, against
     the brute-force set of isomorphisms. The pairs are `K₂` with itself and with the empty
     graph, the empty graph with itself, `P₃` with another `P₃` and with the triangle, and the
     triangle with itself;
   - a negative control: with only the lifted transposition of `0` and `1` as generator, the
     answer for two isomorphic `P₃`s centred at `1` and at `2` is `none`.

   The runs have `3 000` to `87 000` trace events, too many for one kernel declaration (one
   check needs about `0.9` MB of kernel memory per event). Each is proved in pieces of at most
   `5 000` events by `execRuns` (`GraphIsoChecks.Exec`), as the M5 checks are: every piece and
   the composition are checked by the kernel.

**Not covered:** a checked entry that validates arbitrary input (graph data whose lists may be
long), and explicit values of the constants `c`.

## Milestone 14, stage 14j-6c-2: the closed bound (`PLAN-14.md` §14.14)

Stage 14j-6c-1's `Q(n₀)` in closed form, and the headline with it. The code is in
`GraphIso/Main/Growth.lean` (the growth classes), `GrowthCosts.lean` (a growth lemma for every
definition `Q` reads, generated) and `QPBound.lean` (the small parameters, `Q`'s parts and the
headline). The procedure and its programs are unchanged, no protected statement changes, and
`QQP_le_exp` and `mainSolve_qp_exp` are the new targets.

1. **The growth classes**, over an index `ι` with a size `L` and `X = L + 1`:
   - `PLB L e v`: `v ≤ c X^e` (polylogarithmic);
   - `QPB L d v`: `v ≤ 2^{c X^d}` (quasi-polynomial).

   Both are closed under constants, `+`, `max`, `min`, `-` and `/`. `QPB L d` is closed under `·`
   and constant powers, and `PLB` adds degrees under products. `PLB L e ⊆ QPB L 1`, and `log₂`
   and `clog₂` map `QPB L d` into `PLB L d`. The growth steps take `x ∈ QPB L 1` and
   `y ∈ PLB L e`: `x^y`, `y!` and `x.choose y` are in `QPB L (e + 1)`, and `2^y` is in
   `QPB L e`. `supTo` and sums over `List.range` are bounded over the pairs `(i, j)` below the
   bound, where the bound variable is in `PLB` when the bound is.
2. **A growth lemma for each of the 261 definitions `Q` reads** (`GrowthCosts.lean`).
   - The polynomial ones hold at every degree `d`: arguments in `QPB L d` give the value in
     `QPB L d`.
   - Each of the others puts every argument in `PLB L 5` (exponents, factorials, binomials'
     lower indices, bounds of a `supTo` or sum whose variable is used), `QPB L 1` (bases of
     variable powers, binomials' upper indices, `sojZ`'s and `msCount`'s argument) or
     `QPB L 6`, and gives the value in `QPB L 6`.
   - M3's lemma assumes `N − n ∈ PLB L 5` for its factorial `(N − n)!`.
   - Each lemma is proved by unfolding the definition and applying item 1's lemmas along its
     syntax. A script generated them from the definitions' bodies. `ssM5β`'s fields that `Q`
     does not read are not reached: `c2bRU = (m + 1)^m · …`, and `Bcr3` and `Bgen3` with `m!`.
3. **The small parameters** at `L = λ`, with `X = λ(n₀) + 1`:
   - `n₀ < 2^X`;
   - `qpL ≤ 2X`, `kQP C ≤ (32C + 7) X⁵` and `ℓQP C C' ≤ (4 (32C + 7) + 2056 + ℓT C') X⁵`;
   - `min(ℓ, 2n₀) ≤ ℓ`, `uMaxQ = 2X²` and `jMaxQ C' ≤ 2C' X`.

   M3's factorial is at `N − n = 2n₀ − (2n₀ − min(ℓ, 2n₀)) ≤ min(ℓ, 2n₀)`.
4. **The closed bound** (`QQP_le_exp`): for all `C`, `C'` there is `c` with
   `QQP C C' n₀ ≤ 2^{c (λ(n₀) + 1)⁶}` for every `n₀`. The degree is `6` because of the factorials
   and powers of `k = O(X⁵)`: `k! ≤ k^k` and `m^k` with `m ≤ 2n₀`.
5. **The headline** (`mainSolve_qp_exp`): for all `C`, `C'` there is `c` such that for all `K`,
   `T` with `QPHyp K T C C'`, every valid plain instance of degree `N` gets a correct answer
   (`AnsOK`) within `genCost N |gs| + 2^{c (λ(N) + 1)⁸}`. The constant depends only on `C` and
   `C'`. In `mainSolve_qp_closed`, `Q`'s exponent is `2 (5 λ(N) + 9 + 4 (λ(N) + 6)²)`, which is
   at most `306 (λ(N) + 1)²` (`qp_exponent_le`). With `Q ≤ 2^{c₀ (λ(N) + 1)⁶}`, the rest is at
   most `2^{(306 c₀ + 7) (λ(N) + 1)⁸}` (`qp_closed_le`). **`QPHyp` is not yet shown
   satisfiable** (milestones 15 and 16).
6. **Checks** (`GraphIsoChecks/QPBound.lean`):
   - kernel `decide`: the small parameters' constants at `n₀ = 0, 30, 1000, 2¹⁶`, and
     `QQP 1 3 4 ≤ 2^{36 (λ(4) + 1)⁶}`, `QQP 1 3 16 ≤ 2^{7 (λ(16) + 1)⁶}`;
   - negative controls, as proofs: `2^n`, `(m + 1)^m` and `n^n` are not in `QPB λ 6`.

**Not covered:** explicit values of the constants `c`. The graph-isomorphism entry is stage
14j-6c-3.

## Milestone 14, stage 14j-6c-1: the potential (`PLAN-14.md` §14.13)

The full procedure's cost bounded by the potential, under the interfaces' growth assumptions.
The code is in `GraphIso/Main/PotThr.lean` (thresholds), `PotWork.lean` (monotonicity),
`PotQ.lean` (`Q`), `FullPot.lean` (the induction and the headline) and
`GraphIso/Recursion/PotOffset.lean` (the potential with an offset). The procedure and its
programs are unchanged, no protected statement changes, and `main_pot` and `mainSolve_qp` are
the new targets.

1. **The interface hypotheses** `QPHyp K T C C'` (`PLAN-12.md` §2):
   - `AltQuotientIso K`, `K` monotone, and `K n ≤ C (λ(n) + 1)⁵` for every `n`;
   - `TransitivityBound T`, and `T m ≤ C' (λ(m) + 1)` for every `m`.

   `K` and `T` appear in no program and in no conclusion. **`QPHyp` is not yet shown
   satisfiable.** The interfaces' satisfiable instances of this repository
   (`altQuotientIso_succ`, `transitivityBound_id`) do not have these growth bounds. Milestones 15
   (Pyber, `K`) and 16 (Wielandt, `T = 3 (λ + 1)`) are to supply them.
2. **The thresholds** (`thrQP C C'`, local, with `ThrSpec` at cost `cTQP C n₀`: `thrQP_spec`).
   With `L = ⌈log₂ (n₀ + 2)⌉ ≥ λ(n₀) + 1`:
   - `k = kQP C n₀ = C L⁵ + L + 5`;
   - `ℓ = ℓQP C C' n₀ = 4k + L³ + 2¹¹ + 64 (C' + 1)²`.

   They meet `SharpHyp` (`sharpHyp_qp`) and `ell0 n₀ ≤ ℓ` (`ell0_le_ℓQP`):
   - `Thresholds`: `K n₀ ≤ C L⁵ ≤ k` and `n₀ < 2^{k-1} ≤ k!/2`;
   - `TBelow` holds above `64 (C' + 1)²`, since `(λ(m) + 1)² ≤ 4m` (`tBelow_qp`).
3. **What a step sees on the domain** `MiniDom n₀ n₀ (2n₀)` with `LabInv`:
   - M3 occurs only on bases of at most `ℓ` points;
   - M4 and M5 occur only on bases above `ℓ ≥ ell0 n₀`, so the union cells are at most
     `2 (λ(n₀) + 1)²` (`labLen_mul_lam_le`);
   - M4's depth is at most `supTo T m` (`ss_m4J_le_T`), and that bound and Case 2b's
     `supTo T m` are at most `C' (λ(2n₀) + 1)` (`supTo_le_jMaxQ`).
4. **`Q(n₀)`** (`QQP C C' n₀`) is explicit: `n₀ + 2`, plus the work at the corners
   (`qpWork`), plus the factors at the corners (`qpFac`).
   - `qpWork` is the tests' cost and every case's work at the corner of its sizes:
     - M3 on a base of `min(ℓ, 2n₀)` points;
     - M4 and M5 through `SharpWork`'s corner bounds, maximized over the depths of item 3.
   - `qpFac` is every case's factor plus its counted calls at the same corners.
   - The only factorials are `min(ℓ, 2n₀)!`, `(2 (λ(n₀) + 1)²)!` and `k!`. This was checked by
     listing every `Nat.factorial` in the definitions `QQP` unfolds to. M5's bound record
     `ssM5β` also has two fields with `m!` (`Bcr3` and `Bgen3`, read by the kernel step of
     the earlier `m5DispNum`). The cost `Q` bounds, `m5DispNumNs` through `ssM5βns`, never
     reads them.

   On every instance of the domain with `LabInv`, in the case the dispatcher takes:
   - the step's work is at most `Q` (`mainWorkS_le_QQP`);
   - its factor plus its counted calls is at most `Q`, hence `Q²` (`caseFAB_le_QQP`);
   - `|W| + 2 ≤ Q`.

   The corners use the 227 monotonicity lemmas of `SharpWork` and 25 more (`PotWork`), as
   generated there, with `m5WorkUB_mono`.
5. **The potential with an offset** (`PotOffset.lean`). An empty window has potential `0` but a
   positive cost, and M5's counted calls may be on empty windows. So the bound is
   `potO Q 2 |W| bo + Q`, and a child is charged `potO + (Q + 1)`, the `1` being the recursive
   call's own charge. For a step whose work is at most `Q`, the children's `potO + R` (any
   `R ≤ 2Q`) plus the work is at most the parent's potential plus `Q`:
   - with branching: `pot_step_off`, under `pot_step`'s hypotheses and at most `Q³` children;
   - without branching: `pot_free_off`, for nonempty windows;
   - the chain rule: `pot_chain_off`, a new inequality.
6. **The induction** (`main_pot`), by strong induction on the rank, with `main_step_sharp` as the
   step. Each case goes to the inequality its children's predicate names (`pot_case_le`):
   - the chain rule;
   - without branching: M0 (base `2|W| + 1`), M1, M2a, and M2b and M3 on a base of one point;
   - with branching: the others, the counted calls joining the children with
     `c = F + a + b ≤ Q`.
7. **The headline** (`mainSolve_qp`). Under `QPHyp K T C C'`, every valid plain instance of
   degree `N` gets a correct answer within
   `genCost N |gs| + 2 + 15 + potO (QQP C C' N) 2 |W| none + QQP C C' N`.
   - Through `pot0_le` this is at most
     `genCost N |gs| + 17 + (2N + 2) N² Q^{2 (5 λ(N) + 9 + 4 (λ(N) + 6)²)} + Q`
     (`mainSolve_qp_closed`), i.e. `Q^{O(log² N)}`.
8. **Checks** (`GraphIsoChecks/Pot.lean`, kernel `decide`, at `C = 1`, `C' = 3`):
   - `thrQP 1 3` run by the evaluator at `n₀ = 0` and `30`, with the thresholds' values at
     `n₀ = 1000` and `2¹⁶`. At `2¹⁶`, `k = 1419879` and `ℓ = 5687501`: at practical sizes
     every large base goes to M3;
   - `SharpHyp`'s numeric parts;
   - the offset inequalities at explicit values, with negative controls;
   - `2^95171 ≤ QQP 1 3 16 < 2^95172`.

**Not covered** (stages 14j-6c-2 and 14j-6c-3):
- the closed bound `Q(n₀) ≤ 2^{c (λ(n₀) + 1)⁶}`, hence `exp(O((log n₀)⁸))` (done in 14j-6c-2,
  above);
- the graph-isomorphism entry (done in 14j-6c-3, above).

## Milestone 14, stage 14j-6b-2: the sharp dispatcher (`PLAN-14.md` §14.12)

The full procedure's step with M4 and M5 charged through stage 14j-6b-1's steps without stuck
orbits (`GraphIso/Main/FullSharp.lean`), and corner bounds of their work
(`GraphIso/Main/SharpWork.lean`). The procedure and its programs are unchanged, no protected
statement changes, and `main_step_sharp` is the one new target.

1. **The numeric hypotheses** `SharpHyp K T n₀ k ℓ`, at `k = kf n₀` and `ℓ = ℓf n₀`:
   - `Thresholds K n₀ k` (milestone 12);
   - `AltQuot.TransitivityBound T`;
   - `4k ≤ ℓ`;
   - `TBelow T ℓ`: every `m > ℓ` has `4 · supTo T m + 6 ≤ m`.

   `12 ≤ ℓ` (in the plan) is not assumed: it follows from `4k ≤ ℓ` and `5 ≤ k`. `Thresholds`
   passes to the window `p ≤ n ≤ n₀` (`Thresholds.of_le`, with `LabInv`).
2. **No M3 above `ℓ`** (`mainCase_m3_le`):
   - A giant base above `ℓ` meets M5's test.
   - A base above `ℓ` that is not a giant has `m4Deg ≤ T(m)` (`m4_deg_le_T`, the giant test
     through `giantModel_iff`). So `2j + 6 ≤ m` (`ss_m4J_sharp`), and it meets M4's test.
3. **M4 without stuck orbits** (`main_m4_sharp`):
   - It uses `m4StepProg_nsL_ss` at `sIn = NB²`, with `m4_numeric`'s conditions.
   - The union-cell bound is `t · λ(m)`, for any `t ≥ labLen L`.
   - `Lg = ssLgM4Ns m j (t λ(m)) NB²`; the work is `m4WorkNsLSS` and the factor is
     `m4R m j · max(m, (t λ(m))!)`.
4. **M5 without stuck orbits** (`main_m5_sharp`):
   - It uses `m5StepCJProg_ns_ss`, with `jB = supTo T m`, `uB = t λ(m)` and
     `Lg = ssLgM5Ns m k uB jB NB²`.
   - The factor is at most `m5FBns m k uB jB`, and the counted calls are as in `main_m5_at`.
5. **The sharp case functions**: `caseWorkS`, `caseFS` and `mainWorkS`.
   - They are `caseWork`, `caseF` and `mainWork` except at M4 and M5.
   - They take the label length `t = labT I` and `jB = supTo T m`.
   - At M4 and M5, the dispatcher passes the normalized labels, whose length is at most `t`
     (`labLen_normLabD_le`).
6. **The step** `main_step_sharp`:
   - It has `main_step_lab`'s hypotheses and `SharpHyp`.
   - Its conclusion is `main_step_lab`'s, with `mainWorkS` and `caseFS`, plus
     `mainCase = .m3 → m ≤ ℓ`.
   - The other cases come from `main_step_lab`, unchanged. For M4 and M5, the dispatch path is
     redone with the sharp steps.
7. **Satisfiability of `TBelow`.**
   - At Wielandt's `wielandtT k = 3 (⌊log₂ k⌋ + 1)` it holds above `ℓ = 128`
     (`tBelow_wielandt`).
   - At the trivial bound `T = id` it holds at no `ℓ` (`not_tBelow_id`).
   - So `SharpHyp` needs milestone 16 (`TransitivityBound wielandtT`) and milestone 15 (a
     small `K` for `Thresholds`). Until then `main_step_sharp` is proved under a hypothesis not
     yet shown satisfiable.
8. **Corner bounds of the sharp work** (`GraphIso/Main/SharpWork.lean`). The work of M4 and M5
   is an envelope over a box of sizes (`envSup`), too large to evaluate at a large base. It is
   bounded by values at the box's corner:
   - every cost function the two works call is monotone (`CostMono.*`, 227 lemmas, each by
     `unfold` and `gcongr`, with side conditions for differences `a - b`, powers with a varying
     exponent, binomials and function arguments);
   - M4 (`caseWorkS_m4_le`, for `m ≥ 1`): at most the maximum over `j' ≤ j` of M4's work at
     the corner, since the work is monotone in every size but `j` (`m4PtNsL_mono`);
   - M5 (`caseWorkS_m5_le`, for `1 ≤ k`, `2k ≤ m` and `jB < m`): at most the restriction's work
     plus `m5WorkUB`, the certificates' and the case decision's work at the corner and the
     maximum over Case 2b's depth `j ≤ jB` of the dispatch's work at the corner of its data.
9. **Checks** (`GraphIsoChecks/Sharp.lean`, kernel `decide`):
   - `caseWorkS` at M4 and M5 is below `m!` at `m = 65536` (`sharp_m4_work_lt`,
     `sharp_m5_work_lt`; `n = p = 65536`, `N = g = 131072`, `s = (2N)²`, `k = 5`, `j = 51`,
     `t = 2`, `jB = 51`), compared through `(m/2)^(m - m/2) ≤ m!`;
   - M4's work is at least `msCount (m - j)⁸` at any sizes, so at `m = 3000` it is above
     `3000!`: the work is quasi-polynomial in `m` and below `m!` only at a large base;
   - `caseFS` at M4 and M5 is below `m!` at `m = 3000` and `m = 65536`, and `caseF` is not at
     `m = 3000` (a negative control);
   - `TBelow`'s inequality at Wielandt's bound holds at `129` and `3000`, and fails at `64`.

**Not covered** (stage 14j-6c):
- the threshold program for `k(n₀)` and `ℓ(n₀)` meeting `SharpHyp`;
- the potential `Q(n₀)` and the bounds of every case's work and factor by `Q`;
- the induction `cost ≤ potO`;
- the closed bound.

## Milestone 14, stage 14j-6b-1: the steps without stuck orbits (`PLAN-14.md` §14.11)

M4 and M5 at the Schreier–Sims backend without stuck orbits, with no factorial of the base size
`m` in their factors, `Lg` or work. Every hypothesis of the no-stuck forms is discharged except
numeric ones and the two interfaces. No protected statement changes; three new targets.

1. **Partition leaves with their size.**
   - On the models: `PartLe b` (a partition leaf is a colored `t`-partition with `t ≤ b`).
     - The leaf tree: `t ≤ max ((m' + 3)/2) (|Γ| − m')` for `m'` numbered points
       (`leafTree_partLe`, `extPart_partLe`).
     - Case 2b's tree under `Case2bHyp`: `case2bTree_partLe`.
     - Case 3's tree: `t ≤ max ((m' + 3)/2) (|Γ| − thr m' − 1)` (`splitTree_partLe`,
       `outTree_partLe`, `case3Tree_partLe`).
   - On data: `firstLeafD_partLe` (Case 2b) and `firstStructD_partLe` (Case 3, without twins).
   - The numerics at `ssCtx`:
     - Case 2b, from `2|Φ| > m`, `j ≤ jB`, `4 jB ≤ m` and `m ≥ 6` (`ss_m5_hpart₂ᵦ`);
     - Case 3, from `2|Vx| > m` alone (`ss_m5_hpart₃`).
2. **Case 2b's depth under `TransitivityBound T`.** `degD ≤ T |Φ|` in Case 2b (`degD_le_T`,
   `ss_m5_degD_le_T`), so `degD − 1 ≤ jB` when `T m' ≤ jB + 1` for `m' ≤ m` (`ss_m5_depth_le`).
   - Case 2b's count is then `c2bRj m jB = (m + 1)^jB · m² (Z + 1)`, not `c2bRU m = c2bRj m m`.
   - The core's `hBgen₂ᵦ` and `hLY₂` (Case 2b's counts for `y`) were unconditional. For `y` in
     Case 2a its degree may be close to `|Φ|`, so they are now assumed only for `y` in Case 2b,
     the only case that uses them (`RunsWithin.m5DispatchCJ_ns_jpC`,
     `RunsWithin.m5CoreCJProg_ns_jpC`). The protected `_ns_jp` forms follow.
3. **No twins** (`ss_m5_hnt₃`): `m5_no_twins` under `Thresholds K |W| k`, with `k ≤ tOf |Vx|`
   from `2|Vx| > m` and `4k ≤ m`.
4. **Union cells bounded by the labels.**
   - `ss_union_le_lab`: at most `labLen L · s ≤ labLen L · λ(m)`.
   - **Not in the plan**: the derived hints' work `ssBdJ` charged the Johnson fallback at `N − n`
     union cells, hence at `(N − n)!` cosets (`jfallbackCost`). `ssBdJU … u` takes the bound as a
     parameter (`ssBdJ_eq`); `rd_orbit_cj_ssUB` proves `RDOrbit` at any bound on the union
     labels, `rd_orbit_cj_ssL` at the labels' bound. M4's `ss_m4_hDU` and `m4WhUSS` follow.
5. **The steps** (new targets).
   - `RunsWithin.m4StepProg_nsL_ss`: factor `|reps| · max m (labLen L · λ(m))!`, work
     `m4WorkNsLSS`, from `RunsWithin.m4StepProg_ns_ssU` (any factor and work bounds on the union
     labels, at the instance's sizes), which also gives `RunsWithin.m4StepProg_ns_ss`.
   - `RunsWithin.m5StepCJProg_ns`: the restriction composed with
     `RunsWithin.m5CoreCJProg_ns_jpC`, as `RunsWithin.m5StepCJProg_jp` composes
     `RunsWithin.m5CoreCJProg_jp`. Its hypotheses are `m5StepCJProg_jp`'s, except:
     - no kernel reduction charges;
     - `m · (sIn + 1) ≤ Lg`;
     - the partition, twin and conditioned Case 2b hypotheses.
   - `RunsWithin.m5StepCJProg_ns_ss`: at `ssCtx` with `ssM5βns`, at `uB = labLen L · λ(m)`, and
     the work `m5WorkNsSS |W| m k |W| s sIn Lg uB jB`. The remaining hypotheses:
     - validity, the giant, `k`'s conditions, `NP² ≤ sIn`, the sub-solver and its monotone cost;
     - `Lg` for `max(m, uB!)`, `c2bRj m jB` and `c3R`;
     - `TransitivityBound T` with `T m' ≤ jB + 1` and `4 jB ≤ m`;
     - `Thresholds K |W| k` and `4k ≤ m`.
6. **The work and the factor.**
   - `m5WorkNsSS` is the envelope of `m5WorkRawNs`, built from `m5DispNumNs`: no kernel. Case
     2b's depth is taken only in Case 2b (`m5WnsCJ_le`), bounded by `jB`
     (`m5CoreWorkNsCJ_le`).
   - `m5FBns m k uB jB` bounds the factor (`ss_m5CFnsCJ_le`); `ssLgM5Ns` and `m5ns_params` give
     the parameters.
   - The only factorials left are `uB!` and the certificates' `k!`.
7. **Checks** (`GraphIsoChecks/NoStuck.lean`, kernel `decide`):
   - the partition bound on a fixture extended by `extPart`;
   - the union bound on 14j-6a's `cj12` fixture;
   - `m5FBns`, `ssLgM5Ns` and `ssLgM4Ns` below `3000!`, with `m5FB`, `ssLgM5`, `ssLgM4` at least
     `3000!` (a negative control). The crossover lies above `2048`: Split-or-Johnson's count
     `2^(129 (⌈log₂ m⌉ + 2)²)` is in every bound.

**What is not covered (stages 14j-6b-2 and 14j-6c).**
- The sharp dispatcher:
  - M4's depth under `TransitivityBound` (`m4_deg_le_T`, `m4_numeric`);
  - for `m > ℓ`, no M3 fallback;
  - the sharp case functions;
  - `main_step_sharp`.
- The potential, the threshold programs, and the final theorems.

## Milestone 14, stage 14j-6a: the label invariant (`PLAN-14.md` §14.10)

The label invariant of §5 item 8 is threaded through every step, in place. **This is a
semantic contract amendment**, decided by the user on 25 October 2026. Protected statement
texts are unchanged, but the specs with `RDOrbit` hypotheses assume more of the derived hints.
`lean/docs/contract-repair.md` ("The label invariant of stage 14j-6a") lists every affected
statement with its polarity and the discharge paths.

1. **The invariant** (`Main/Frame.lean`).
   - The ingredients: `labLen L`, the largest length of the label lists
     (`Toolkit/Labels.lean`); `ell0 n₀ = max 2¹¹ ((⌊log₂ n₀⌋ + 1)³)`; `LabInvAt n₀ m t`.
   - `LabInv J`, for a hint on a base of `m = N − n` points:
     - `n ≤ n₀`;
     - `m ≤ n₀`;
     - `ell0 n₀ < m → labLen L · (⌊log₂ m⌋ + 1)² ≤ 2 (⌊log₂ n₀⌋ + 1)²`.
   - How it survives a step:
     - a smaller base with shorter labels (`LabInvAt.mono`);
     - labels of length at most one on a base of at most `n₀` points (`LabInvAt.of_le_one`);
     - a Johnson step with `C(m', s) ≤ m`, `2 ≤ s`, `2s ≤ m'` and labels at most `s` times
       longer (`LabInvAt.johnson`, from `johnson_step_label`).
   - The entry's instance `(J, N, N, none)` has it (`LabInv.entry`).
2. **The frame.** `SizeChild sC I J` gains `lab : LabInv I → LabInv J`
   (`SizeChild.lab_closed`).
3. **The derived hints** (`Main/Derive.lean`).
   - `DOutcome`'s `inter`, `blockLab` and `blockStab` gain `labLen L' ≤ labLen L`.
   - `johnUnion` gains a witness `s` with `labLen L' ≤ labLen L · s`, `C(m', s) ≤ m`, `2 ≤ s`
     and `2s ≤ m'`.
   - `deriveProg_free` and `deriveProg_cj` prove these:
     - `m1ContProg` and `blocksProg` take the comparison of their input labels with `L` as a
       premise;
     - tag `4`'s witness is the structure's Johnson parameter, `C(nc, s) ≤ m` by
       `dv_cj_choose_le`.
   - The orbit constructors and the Schreier–Sims callers discharge `RDOrbit` as before, so no
     corollary at `ssCtx` and no headline has a new hypothesis.
4. **The label lemmas, on data.**
   - `labLen_mapLabels_le`, `labLen_mapLabels_short`, `length_blockLab_le`;
   - `labLen_labM0D`, `labLen_labM1D_le` (with `m1O_facts`), `labLen_labM2aD_le`,
     `labLen_m2bLabels_le`;
   - `labLen_labJUD_le`, `labLen_labDiffD_le`, `labLen_rbLabels_le`, `labLen_normLabD_le`.
5. **The children.** Every step proves `lab` where it builds a child.
   - No hint: `SizeChild.lab_none`.
   - M0, M1, M2a: `childHInst_labInv`.
   - M2b and tag `3`: `MlChildL` and `RunsWithin.m2bLoopProg_lab`. `RunsWithin.m2bLoopProg`
     is its corollary, unchanged.
   - Tags `1`, `2`, `4`: `rd_sem124`'s `hLab`.
   - Tag `6`: the same labels.
   - M5's restriction: `labLen_rbLabels_le`.
6. **The step with the invariant** (`main_step_lab`, a new target). For a parent with `LabInv`,
   the conclusion of `main_step` holds from `MainSubL`: the recursive call solves the domain's
   instances with `LabInv` of smaller measure. `main_step` (unchanged) and `main_step_lab` are
   the cases of `main_step_gen`. The FullStep step lemmas take a flag `b` with
   `LabInvIf b I` and `MainSubB`.
7. **Checks** (`GraphIsoChecks/MainSteps.lean`).
   - `kidsSizeOK` now also checks the label field (`labInvB`, with `labInvAtB_iff`) on every
     recorded child of the step fixtures.
   - Kernel checks:
     - M0's labels have length `1`;
     - the Johnson union of `fRD5`'s labels through `cj12`'s cells has length `4 = labLen L · s`,
       with `C(4, 2) ≤ 12`.
   - A negative control: labels of length `3` on a base of `2500 > ell0 3000` points fail
     `LabInvAt` (`not_labInvAt`), and an instance with them fails `LabInv`.

**What is not covered (stages 14j-6b and 14j-6c).**
- The sharp charges: union cells bounded by `t · s`, M5's step-level variant without stuck
  orbits, and the interfaces' exclusions.
- The potential, the threshold programs, and the final theorems.

## Milestone 14, stage 14j-5d: the dispatcher and the recursion (`PLAN-14.md` §14.9)

The full procedure `mainBody thr` is a program of the cost language, closed by strong induction
on the rank of the measure: it is correct on every valid instance, with an explicit cost, for
every threshold program `thr`. The code is in `Main/FullProg.lean` (programs), `FullCase.lean`
(the tests and the branches), `FullStep.lean` (the steps) and `Full.lean` (the step, the
recursion and the headline), with `Cost/Local.lean` (local programs). No existing module
changes; the gate reports no changed protected statement.

1. **The thresholds.** `ThrSpec thr kf ℓf cT`: `thr` is well formed in every context (`ThrWf`),
   **local** in every variable type, and, whatever the body, returns `(kf n₀, ℓf n₀)` within
   `cT n₀` at `ssCtx`. `thrConst k ℓ` meets it with `cT = 3` (`thrConst_spec`).
   - **Local** (round 2, finding F1): `Prog.Local p` says that `p` has no backend call and no
     recursive call, hereditarily through every continuation (`Cost/Local.lean`). A local
     program's evaluation, under any oracle and any body, has a trace without backend events
     (`Prog.Local.eval_calls`, `Prog.Local.runs_calls`); so every run of a threshold program
     has none (`ThrSpec.calls`). Round 1's contract only bounded the cost, which a program
     calling the backend could meet. The checks include a calling threshold program that is not
     local, so it has no `ThrSpec` (`thrCall`).
2. **The body** (`mainBody thr`, well formed: `mainBody_wf`). Every step's sub-solver is
   `.recur`.
   - As in the mini procedure: the base-case test; without a hint, the window's orbits, the
     chain rule on at least two, else M0.
   - **With a hint** (`hintProg`):
     - **The labels are normalized** to the `n` string positions (`normLabProg`; not in the
       plan). The work of M2a, M2b and M4 depends on the size of the label array, which the
       children's predicates do not bound. Only window points (below `n`) are read, so the hint
       and the instance's validity are unchanged (`HintValid.normLab`, `HInstValid.normLab`),
       and so is the measure. The steps run on the instance with the normalized labels.
     - **The base orbits** (`orbits` on `baseWin`): more than one gives M1 (`base_trans_iff`:
       the base is transitive iff it has at most one orbit).
     - **The maximal blocks** of the base (`baseBlocksProg`, `blkOKProg`): if they are proper,
       some window label not equidistributed (`neqProg`) gives M2a, otherwise M2b.
     - **Otherwise** (`bigProg`), with `(k, ℓ) = thr n₀`: `m ≤ ℓ` gives M3. Else the degree of
       transitivity `dg` of the base action, capped at `m − 2` (`degreeProg`). This is
       `giantProg`'s computation inlined, so `dg` serves both tests: `dg = m − 2` is the giant
       test (`giantModel_iff`), and `j = dg − 1` is M4's depth (`m4J`).
       - A giant with `5 ≤ k`, `2k ≤ m` and `12 ≤ m` (`m5OkD`; these imply `k + 2 ≤ m`) gives
         M5, with the state without structure `noStD` (tag `0`, read as the default value).
       - A non-giant with `4 + j ≤ m` and `2j ≤ m` (`m4OkD`) gives M4.
       - Every other case gives M3.
   - `mainEntry` is the mini procedure's entry (one `generate`, then the recursion without a
     hint, `n₀ = n = N`).
3. **The case analysis.** `mainCase kf ℓf I` computes the case from the data (`hintCase`,
   `bigCase`). Each branch's run is a lemma: `RunsWithin.hintProg_m1`, `hintProg_m2a`,
   `hintProg_m2b`, `hintProg_big`, `bigProg_small`, `bigProg_m5`, `bigProg_m5_m3`,
   `bigProg_m4` and `bigProg_m4_m3`, each at the tests' cost (`hintPreCost`, `blkTestCost`,
   `neqTestCost`, `bigTestCost`). The step conditions follow from the tests:
   - M1's `¬ IsTransOn` from the orbit count;
   - M2a's and M2b's block facts from `blkOKD` (`ss_mb_facts`, through `dv_blocks_facts`), and
     M2b's equidistributed window point from `neqD = false` and the nonempty window;
   - M4's `hng` from `degreeModel_spec` (`dg ≤ m − 2`, `dg ≠ m − 2`);
   - M5's `haltP` from `giantModel_iff`.
4. **The steps** (`main_chain`, `main_m0`, `main_m1`, `main_m2a`, `main_m2b`, `main_m3`,
   `main_m4`, `main_m5`), from one hypothesis `MainSub`: the recursive call solves every valid
   instance of the domain with a smaller measure. Every step's predicate gives the domain and a
   smaller measure (`main_pred`, `MainSub.step`, `SizeChild.closed`).
   - **The parameters:** `sIn = s = NB²` (the domain's generator bound; every step's `sC` is
     at most it). M4 and M5 are proved at any `Lg` (and `uB`) meeting the corollaries'
     conditions (`main_m4_at`, `main_m5_at`, M5's factor at `uB ≥ m`: `m5FBu`,
     `ss_m5CFCJ_le_u`), and instantiated twice:
     - **at the domain's bounds** (§14.9 item 4; round 2, finding F2): `Lg = domLgM4 NB NB²`
       for M4, and `Lg = domLgM5 NB NB²`, `uB = NB` for M5 (`main_m4_dom`, `main_m5_dom`).
       Each condition is a lemma for every `m ≤ NB`, `j ≤ NB` and `k ≤ NB` (`m4_dom_params`:
       `hLg`, `hLR`; `m5_dom_params`: `hLg`, `huB`, `hLgJ`, `hLY`), from the monotonicity of
       `m!`, `m4R`, `c2bRU` and `c3R` (`m4R_le_dom`, `c2bRU_mono`, `c3R_le_dom`);
     - **at the instance's sizes**: `Lg = ssLgM4 m j NB²`, and `Lg = ssLgM5 m k NB²` with
       `uB = m` (`main_m4`, `main_m5`), as 14j-5c's `m4_params` and `m5_params` choose them.
       `main_step` uses these: each step's work is then a function of its own sizes, which
       stage 14j-6 needs, and it is at most the work at the domain's parameters
       (`ssLgM4_le_dom`, `ssLgM5_le_dom`, `caseWork_le_dom`; item 6).
   - M5's factor and counted calls are bounded with Schreier–Sims (`ss_m5CFCJ_le`,
     `ss_m5CKCJ_le`, `m5CH_le`), from the certificates' validity and base invariance
     (`M5Full`).
5. **The step** (`main_step`, the form stage 14j-6 reuses). Take a cost `C` monotone in the
   window without a hint, and assume `MainSub` at `I` with cost `C`. Then the procedure on `I`
   returns a correct answer with at most `NB²` generators, at cost at most
   `Σ_ch C + a·C(|W|/k, none) + b·C(|W|/2, none) + mainWork kf ℓf cT NB² I`. Here:
   - `mainWork` is the dispatch's tests (`mainTestCost`, over every path) plus the work of the
     case taken (`caseWork`, the 14j-5c functions at the instance's sizes, and `m0WorkSS`,
     `m3WorkSS`, `rbOverSS` for M0, M3 and M5's restriction);
   - the children `ch` satisfy the predicate of the case (`casePred`: `ChainChild`, M0's
     `FreeChild` with base `2|W| + 1`, M1's and M2a's `FreeChild`, `StepChild` for M2b, M3, M4
     and M5), with a factor `F ≤ caseF` (`1`, `m`, `m!`, `m4R m j · m!`, `m5FB m k`);
   - `a` and `b` are M5's counted calls (`a ≤ caseA`, `b ≤ caseB`, zero for the other cases).
6. **The recursion** (`main_spec`), by strong induction on the rank `miniRk NB p bo` of §14.7.
   - The bound is `mainCost t nB NB = miniC (mainA nB NB) (mainW t nB NB)`, so
     `Cb (r + 1) = A (1 + Cb r) + W`.
   - `W = mainW` bounds every step's work on the domain: the monotone envelopes (`workEnv`,
     over `n, |W| ≤ nB`, `N, k, j ≤ NB`, `|gs| ≤ NB²`) of the tests' cost and of every case's
     work (`mainWork_le`). M5's `k` and M4's `j` are at most `m ≤ NB` in their cases
     (`mainCase_kj`).
   - `A = mainA` bounds every step's number of sub-calls: the envelopes of `nB · caseF`,
     `caseA` and `caseB` (`main_count_le`). This plays the role of the plan's `cm · nB`.
   - The children and M5's counted calls have smaller rank (`casePred_rk`, `miniRk_none_lt`,
     with `k ≥ 5` and `m ≥ 12`), and the step's cost is within the bound (`main_cost_le`).
   - **At the domain's parameters:** `mainWDom` is `mainW` with each case's work at the
     parameters of item 4 (`caseWorkDom`). Then `mainW ≤ mainWDom` (`mainW_le_dom`, through
     `workEnv_mono_box`), and `main_spec_dom` gives the bound `miniC mainA mainWDom`.
7. **The headline** (`mainSolve_ss`). For every `thr` with `ThrSpec`, every valid plain instance
   gets a correct answer within `genCost N |gs| + 2 + 15 + mainCost (cT N) N (2N) (miniRk (2N)
   |W| none)`. `mainSolve_ss_const` is the same at `thrConst k ℓ`, with no hypothesis.
   `mainSolve_ss_dom` (a protected target) is the same with the work bound `mainWDom` at the
   domain's parameters.
8. **Checks** (`GraphIsoChecks/MainFull.lean`, about two minutes). These run the full procedure
   at `thrConst 5 ℓ` with the verified oracle. Each check compares the answer with brute force,
   the path (the number of nodes of each case), and **every node's own work** (outside its
   children's runs, read from a second run whose body records each node's case and bound)
   with `mainWork`. For an M4 node the bound is the tests' cost plus `m4CostSS` at the node's
   sizes, the function under `m4WorkSS`'s envelope: that envelope ranges over `Lg` up to about
   `2^2064` and is not evaluated, nor is the headline bound.
   - **Kernel-checked:**
     - from the entry, the mini procedure's fixtures (the base case, the chain rule, M0, M3);
     - with a hint, the body on stage 14j-2's fixtures: M1, M2a, M2b and M3, each followed by
       its children's steps;
     - a negative control: with every node's bound `0`, the check fails.
   - **By `#eval`** (through `check`): M4 on `AGL(1, 5)` at `ℓ = 0` (one M4 node, then its
     children), and M3 at `ℓ = 10`.
   - **M5 is not reached** (it needs `12 ≤ m`). On the `S₄` data the base is a giant and M5's
     test fails, so the dispatcher takes M3 (`bigCase`, kernel-checked, and both runs by
     `#eval`); `m5OkD 5 12` holds.
   - M1, M2a, M2b and M4 are reached from hinted instances given to the body, as the
     recursion runs it on a hinted child, not from the entry. Small entry instances do not reach
     them: M0's children have a primitive base (the maximal blocks).

**What is not covered (stage 14j-6).**
- The quasipolynomial bound and the threshold programs `k(n₀)`, `ℓ(n₀)`. The bound here is
  exponential in the rank: M3 branches over up to `m!` cosets.
- The step-level M5 variant without stuck orbits.
- Sharper charges. The factorial factors (`m!` in `Lg` and in M4's and M3's multiplicities)
  bound the Johnson fallback by `m!` rather than `(ts)!`; stage 14j-6 needs the `(ts)!` bound
  of §2.4.

## Milestone 14, stage 14j-5c: the Schreier–Sims steps (`PLAN-14.md` §14.8)

Every macro-step the dispatcher uses has a corollary at the Schreier–Sims backend (`ssCtx`) whose
hypotheses are only validity, the step's case conditions, numeric conditions on the parameters
and the sub-solver hypothesis. No charge, generator-count, `BackendBounds`, `RDBounds` or
`RDOrbit` hypothesis remains. The code is in `Main/SimsSteps.lean`, `SimsRD.lean`, `SimsM4.lean`
and `SimsM5.lean`. No protected statement changed; M5's Case 2b and Case 3 routes gain variant
theorems (item 4), from which the originals are derived.

1. **The corollaries.**

   | Step | Theorem | Work | Further hypotheses |
   |---|---|---|---|
   | M1 | `RunsWithin.m1StepProg_ss` | `m1WorkSS n m \|W\| \|gs\| s` | none |
   | M2a | `RunsWithin.m2aStepProg_ss` | `m2aWorkSS n m \|W\| \|gs\| s \|L\|` | none |
   | M2b | `RunsWithin.m2bStepProg_ss` | `m2bWorkSS n m \|W\| \|gs\| \|L\| sIn` | `N² ≤ sIn`, `s ≤ sIn` |
   | M4 | `RunsWithin.m4StepProg_ss` | `m4WorkSS n m j \|W\| s \|L\| sIn Lg` | `2j ≤ m`; `\|gs\|, N², s ≤ sIn`; `Lg` (`hLg`, `hLR`) |
   | M4, no stuck orbit | `RunsWithin.m4StepProg_ns_ss` | `m4WorkNsSS … uB` | as above, `m4StepProg_ns`'s numeric conditions, `m ≤ uB` |
   | M5 | `RunsWithin.m5StepCJProg_ss` | `m5WorkSS \|W\| m k \|W\| s sIn Lg uB` | `k`'s conditions; `NP², \|gsP\|, s ≤ sIn`; `hCmono`; `Lg` (`hLg`, `hLgJ`, `hLY`); `m ≤ uB`; `st.1 ≠ 2` |

   Here `m` is the base size (degree `n + m`), `j` M4's individualization depth and `k` M5's
   certificate size. The conclusions are those of the specs: the answer, the children with their
   predicate and factor, the generator bound, and M5's counted calls (`certCount`, `m5CKCJ`,
   `m5CH`).
   - **The work is monotone in every argument.** For M1, M2a and M2b it is the spec's cost at
     the charges below, written in `n` and `m` (`m1WorkSS_mono`, `m2aWorkSS_mono`,
     `m2bWorkSS_mono`, by `gcongr`). M4's and M5's costs are not monotone in every size (M4's
     structure lives on the remaining `m − j` points; M5's cost is the case it takes, with that
     case's data). Their work is the **monotone envelope** `envSup`: the largest value of the cost
     over the box of smaller sizes (`le_envSup`, `envSup_mono`; `m4WorkSS_mono`,
     `m5WorkSS_mono`). M4's depth `j` stays an argument, so stage 14j-6 can bound `m^j` by the
     transitivity degree.
   - **M5's work** (`m5CoreWorkCJ_le`, `m5WCJ_le`). The dispatch's work is at most the sum of
     every case's work at its data (`m5DispNum`), and the envelope ranges over bounds on the data:
     the generators (`≤ sIn`), the partition and set generators (`≤ m² + m`), the orbits, fixed
     points and degree (`≤ m`), the kernel (`m!` representatives, `N²` generators), and the first
     leaf's generators (`cjB m`, `olB m`, from its size `outSize ≤ leafB m`).
2. **The charges.** A Schreier–Sims charge depends only on the degree, the number of input
   generators and the window (`ssB`). Each step's charges are bounded by these functions at
   bounded sizes.
   - **Lengths without validity:** re-basing, extension and restriction keep the number of
     generators; `stabInPL` at most doubles it (`stabInPL_length_le`); a partition's generators
     number at most `m² + m` (`partGensD_length_le`); a leaf's or a Johnson structure's at most a
     function of its size (`johnGensD_length_le_bound`, `cjohnGensD_length_le_bound`,
     `outGensD_length_le_bound`).
   - **Lengths with validity:** `generate`, `stabilizer` and `kernel` outputs at most `M²` at
     degree `M` (`generateModel_spec`, …); where the validity of an input is internal to a spec,
     through the invariant `ssBnd` of 14j-5b (`ss_blockStab_sizes`, `ss_leafStab_sizes`,
     `ss_iterStab_le`, `ss_m4_pre`).
   - **The block stabilizer** (M2b, the block step): `ss_blockStab_sizes`; **the leaf
     stabilizer** (M4): `ss_leafStab_sizes`, `ss_m4Charges`, with the leaf orbit at most
     `msCount (m − j)` (`ss_m4_pre`); **M5:** `ssM5β`, `ssBg1J`, and the restricted instance's
     setting `ss_m5_rb`.
   - **The charge lemmas** (round 2, for reuse by the variants without stuck orbits). Each
     hypothesis of a spec is discharged by a named lemma that the corollary cites:
     - M1 and M2a: `ss_hint_hBo`, `ss_hint_hB`, `ss_hint_hBlift`, `ss_hint_hBgen`;
     - M2b: `ss_m2bCharges` (`M2bCharges`), `ss_m2b_hBlift`, `ss_m2b_hBgen`, `ss_m2b_hBo`,
       `ss_m2b_hBgen₂`, from the sizes `ss_m2b_sizes`;
     - M4: `ssBoundsS`, `ss_m4Charges`, `rd_ss_boundsS`, `ss_m4_hD`;
     - M5: `ss_m5_h…` for each of the 38 charge, route and restriction hypotheses of
       `RunsWithin.m5StepCJProg_jp` (`ss_m5_hBgP` to `ss_m5_hBgnR`), on a generic restricted
       instance `(N, gs)` with only the facts each one needs, together with `ssBoundsS`,
       `ssBm`, `rd_ss_boundsS` and `ss_hsK`.
   - **The parameter choices** (round 2). Every numeric condition of the corollaries holds at an
     explicit choice: `sIn = ssSIn N s |gs| = max (N²) (max s |gs|)` (`ssSIn_spec`,
     `m2b_params`); M4's `Lg = ssLgM4 m j sIn` and, without stuck orbits, `ssLgM4Ns m j m sIn`
     with `uB = m` (`m4_params`, `m4ns_params`); M5's `Lg = ssLgM5 m k sIn` with `uB = m` for any
     `k` with `5 ≤ k` and `2k ≤ m ≥ 12` (`m5_params`), for instance `k = 5`
     (`m5_params_five`). The remaining hypotheses are the cases' conditions, which the
     dispatcher tests.
3. **Reduce-and-derive.** `RDOrbit` holds for every orbit of `RDSet`
   (`rd_orbit_free_ssU`, `rd_orbit_cj_ssU`), with explicit work bounds `ssBdF`, `ssBdJ`.
   - **Every orbit, not only those where the calls happen** (`rd_orbit_free_ss`'s `hch` asks for
     all). M1's orbit is an orbit of the base action whenever the base is nonempty, which a hint
     ensures (`HintValid.base_pos`, `ss_m1O_facts`). Its child is valid and transitive on its base
     (`ss_m1_child`). The maximal blocks of that base are a block list permuted by the group,
     including a one-point base (`ss_mbD_facts`).
   - **The Johnson cells:** at most `m` cells (`ss_cells_le`), a valid re-basing
     (`dv_cellPos_perm`), and union labels of at most `|cells|` entries (`ss_union_le`).
   - **M4** uses `m4_cj_facts` for a Johnson leaf, which needs `2j ≤ m` (item 3 of §14.8): the
     corollaries assume it, and the dispatcher (14j-5d) tests it, falling back to M3.
4. **The premises of M5's routes** (§14.8 item 4, including its "further cases"). Each new
   theorem states the hypotheses of Case 2b's and Case 3's routes with the premises under which
   the route uses them; each original statement is derived from its new version.
   - **The planned defect.** Case 2b's Johnson-route hypotheses were stated for every first leaf,
     but used only for a Johnson leaf: premise `X₀.1 = 2` (`m5Case2bCJProg_jp`).
   - **The Johnson routes' facts.** Discharging `RDOrbit` at a Johnson state needs the validity
     of the coloured pair and `IsJohnson` (`rd_orbit_cj_ssU`), which the routes establish before
     aligning. The Johnson-route hypotheses therefore also take `CJFacts` of the pair:
     `c2bCJProg_jp`, `c3CJRouteProg_jp`, `m5Case2bCJProg_jp`, `m5Case3CJProg_jp`.
   - **The partition routes' charges** (`hBg1₂ᵦ`, `hBg1₃`) take `X₀.1 ≠ 2`, under which they run,
     so the leaf's generators are a partition's.
   - **`x`'s case.** At the dispatch, core and step levels (`m5DispatchCJ_jp`,
     `m5DispatchCJ_ns_jp`, `m5CoreCJProg_jp`, `m5CoreCJProg_ns_jp`, `m5StepCJProg_jp`) the eight
     hypotheses above also take `x`'s case (Case 2b: tag `2`, not Case 2a; Case 3: tag neither `1`
     nor `2`). The discharge does not need these premises; they only weaken the hypotheses.
   - The gate reports no changed protected statement.
5. **Checks** (`GraphIsoChecks/MainSimsSteps.lean`, about a minute). `spySub` brackets each
   sub-call between two marker calls, so the step's own events are those outside the brackets.
   - **Per call site** (round 2; round 1 compared each call with the largest bound of its
     operation, which let one site's bound cover another's call). Each charge lemma is a *site*:
     the calls it bounds and its bound. A lemma about one specific call (M1's re-basing, M2b's
     block stabilizer, M4's leaf stabilizer, M5's restriction and base action, …) matches exactly
     that input, computed by the model functions its statement names. A lemma quantified over
     inputs (`BackendBounds`, `RDBounds`, the transfer's `generate`, M5's `generate` families,
     …) matches its statement's degree, window and size conditions; the semantic conditions
     (validity, subgroups, `M5Full`) are not tested, which only makes the check stricter. Every
     own call must match some site and be within the bound of every site it matches
     (`sitesOK`).
   - **Kernel-checked** (`decide +kernel`): M1, M2a and M2b (with and without hinted children)
     on stage 14j-2's fixtures. In each run, the step's own cost under `ssB` is within the
     corollary's work, and every own call within its sites' bounds. Negative controls: with M1's
     re-basing or M2b's extended group bounded by `0`, the check fails.
   - **Interpreter runs** (`#eval` through `check`, which fails the build on a false result):
     M4 on `AGL(1, 5)`, the own cost within `m4CostSS` at the run's depth (the function under
     the envelope) and the charges per site; M5 on `S₄` (`fA`, `fB`) and on `S₅` (`x` constant,
     an isomorphic and a non-isomorphic pair), `k = 3`, the charges per site at the parameters
     `ssSIn`, `ssLgM5`. Negative controls for M4's leaf stabilizer and M5's restriction. These
     runs are too large for one kernel check. The M5 fixtures are outside M5's numeric
     conditions, so the corollary itself is not checked there.

**What is not covered.**
- The dispatcher and the recursion (stage 14j-5d).
- M5's step-level variant without stuck orbits, which stage 14j-6 needs with these charges.
- The cost bound (stage 14j-6).

## Milestone 14, stage 14j-5b: Schreier–Sims counts and the mini procedure (`PLAN-14.md` §14.7)

Two things are proved. First, the generator-count facts that the repaired specs of stage 14j-5a
take as hypotheses hold for Schreier–Sims. Second, one recursion closes by induction using
those specs as they stand. No existing statement changes.

1. **Uniform backend bounds** (`Main/SimsCounts.lean`). They hold at any generator bound
   `s ≥ M²`, so one bound serves every degree of a recursion:
   - `ssBoundsS` (`BackendBounds`);
   - `rd_ss_boundsS` (`RDBounds`).
2. **The strengthened `DOutGens`**, for tags `1`–`5` (`rd_ss_dOutGens_free`,
   `rd_ss_dOutGens_cj`). This is the obligation the 14j-5a scope amendment left to this stage.
   - **The invariant.** The derive specs are generic in the data invariant `DV`. Schreier–Sims
     meets every contract for `ssBnd S M gs _ : |gs| ≤ max S M²` (`ssOracle_meets_bnd`),
     because at degree `M` its `generate`, `stabilizer` and `kernel` return at most `M²`
     generators on valid inputs.
   - **The outcome.** `RunsWithin.deriveProg_free` and `RunsWithin.deriveProg_cj`, instantiated
     with `ssBnd S` and the exact charges of their calls, give a `DOutcome` whose groups satisfy
     `ssBnd S`. They have degree at most `N` (`dOutGens_of_dOutcome`), so at most `S`
     generators.
   - **Tag `4`, the cells' re-basing.**
     - `rd_orbit_cj`'s Johnson preservation `hK` is restated for each `gs ≤ gsK`.
     - `deriveProg_cj` then proves the re-based generators valid, as `generate`'s precondition
       requires.
     - The invariant's output bound then bounds the child.
   - **Corollaries.** `rd_orbit_free_ss` and `rd_orbit_cj_ss` are `rd_orbit_free` and
     `rd_orbit_cj` for Schreier–Sims, without the `DOutGens` part of `hch`.
3. **The other generator counts**, each at most `M²` at its degree `M`:
   - M4's `hKs` (`ss_m4K_gens_le`), through M4's construction for `ssBnd S`;
   - M2b's `hsR` (`ss_hsR`) and `hsR'` (`ss_m2bRb_gens_le`, through `RunsWithin.m2bProg` for
     `ssBnd 0`);
   - M5's `hsK` and `hsKR` (`ss_hsK`, `ss_kernel_gens_le`);
   - Case 2a's `hgR` (`ss_hgR`);
   - `Bm` with `sm M = M²` (`ssBm`).
4. **The mini procedure** (`Main/Mini.lean`).
   - **The program.** `miniBody` is the base-case test; then M3 with a hint; without one, the
     chain rule on at least two orbits, else M0. Every sub-solver is `.recur`, and the program
     is well formed.
   - **The entry.** `miniEntry` makes one charged `generate`, then `.recur` on the instance
     without a hint, with `n₀ = n = N`.
   - **The domain.** `MiniDom`: `n₀`, `n ≤ nB`, degree at most `NB`, at most `NB²`
     generators, and `2 nB ≤ NB`. Every step's `sC` is at most `NB²`, so `SizeChild.closed`
     keeps every child in the domain:
     - chain rule: `max NB² |gs|`;
     - M0: a re-based group at degree `n + k ≤ 2n`;
     - M3: `max NB² |K_b|`.
   - **The cost.**
     - The rank is `miniRk NB p b = p (NB + 2) + b`.
     - The bound is `miniC A W` with `A = NB! · nB`, so every step has at most `A` children.
     - `W = miniW nB NB` bounds the dispatch and every step's work on the domain, from the
       explicit Schreier–Sims charges.
     - Every valid instance has rank at least `1` (`HInstValid.base_pos`).
   - **`mini_spec`**: on the domain, the answer is correct, has at most `NB²` generators, and
     comes within `miniCost nB NB` of the rank. The proof is strong induction on the rank; each
     step's sub-solver hypothesis is the induction hypothesis (`mini_hsub`). The four specs are
     used as stated.
   - **`miniSolve_ss`**: on every valid plain instance, with no hypothesis, the cost is at most
     `genCost N |gs| + 2 + 15 + miniCost N (2N) (miniRk (2N) |W| none)`. An empty window is the
     base case.
5. **Checks** (`GraphIsoChecks/MainMini.lean`, `decide +kernel`, about 30 seconds in all).
   - **What is checked.** `miniEntry` runs with the verified oracle on six fixtures. For each,
     the answer equals the brute-force coset, the trace's cost is within `miniSolve_ss`'s
     bound, and the path is counted: recursive calls, `kernel` calls, and re-based
     `generate` calls.
   - **The fixtures:**
     - an empty window;
     - a fixed window, with and without an isomorphism;
     - the chain rule on `⟨(0 1), (2 3)⟩`, then M0 and M3 on each orbit;
     - `D₄`: M0, M3 and the children, with and without an isomorphism.

**What is not covered (stage 14j-5c).**
- The full dispatcher (M1, M2a, M2b, reduce-and-derive, M4, M5).
- The Schreier–Sims charges of those steps (`M1Charges`, `BlkCharges`, `M2bCharges`,
  `M5Bounds` and the specific calls), moved there by §14.7's restaging.
- The mini procedure's cost is exponential in the rank. The quasipolynomial bound is stage
  14j-6's.

## Milestone 14, stage 14j-5a: the contract repair (`PLAN-14.md` §14.6)

The macro-step specs of stages 14j-2 to 14j-4b are strengthened in place, so that stage 14j-5
can close the recursion by induction with one cost per measure. The full record is
`docs/contract-repair.md`: every changed definition, every changed protected statement, and
how each old statement follows from the new one.

1. **The frame** (`Main/Frame.lean`).
   - `SizeChild sC I J` bounds the child's generators by `sC`.
   - `ChildList` has nonempty windows (`pos`), so `ch.length ≤ c · n` (`ChildList.length_le`).
   - `SizeChild.closed`: a parent with at most `nB` string positions, degree at most
     `NB ≥ 2 nB` and a step bound `sC ≤ sG` has children with the same bounds and at most `sG`
     generators. So one bound is closed under the recursion.
2. **The sub-solver predicates.** Each step names its `sC` from the bounds its proof already has:
   - `max s |gs|` for the chain rule;
   - `max s |K_b|` for the kernel reduction and M3;
   - the re-based group's count for M0, M1 and M2a;
   - `sIn` for the block-stabilizer loop, M2b, reduce-and-derive, M4, Align with
     reduce-and-derive, and M5's Cases 1, 2b and 3;
   - `max sIn (supTo sm (|W| / 2))` for M5's dispatch, core and step.

   No parent hypothesis changes, except:
   - **`DOutGens` (scope amendment, user decision).** It now also bounds the child of
     reduce-and-derive's tags `1`, `2`, `4` by `sIn`. This strengthens the `RDOrbit` assumption
     of reduce-and-derive, M4 and M5. Those children are re-based `generate` outputs, and for
     tag `4` a bound needs Johnson preservation, which `rdProg` does not assume.
   - **Case 2a** (`RunsWithin.m5Case2aProg`). It takes a fresh `sR` with the hypothesis `hgR`,
     which `generate` bounds at degrees at most `|W| / 2`. Some `sR` meets `hgR` for every
     backend (`m5_exists_genOut_le`). M5's dispatch discharges it from its `Bm`.
3. **Positive windows** are proved where children are created: orbits, `DynHandle`'s nonempty
   orbits, hinted windows (`HInstValid.win_pos`), and M0's `2 ≤ |W|`.
4. **Checks.**
   - `listB` checks nonempty windows (`listB_iff` against the new `ChildList`).
   - `childrenOK` and `kidsSizeOK` check every recorded child's generator count against the
     step's bound: the spec's expression for the chain rule, M0, M1, M2a and the kernel
     reduction, and `N²`, the Schreier–Sims value of `sIn`, for the steps through
     reduce-and-derive and M5.
5. **Snapshots.** 29 protected statements changed, all listed in the record; their snapshots
   were accepted after the diff was checked. `RunsWithin.viaChildProg` and
   `RunsWithin.m5CertProg` take an abstract predicate and are unchanged.

**What is not covered (stage 14j-5b).**
- The Schreier–Sims discharge of the strengthened `DOutGens` and of `hKs`, `hsR`, `hsR'`,
  `hsK`, `hsKR` and `M5Bounds`.
- Backend bounds at `s = NB²` below the top degree.
- A recursion over the base case, the chain rule, M0 and M3 closed by induction.

## Milestone 14, stage 14j-4b: coloured Johnson alignment in M5 (`PLAN-14.md` §14.5)

Stage 14j-4 hands the Johnson leaves of Cases 2b and 3 to reduce-and-derive with no structure,
which is correct but can reach the stuck fallback. This stage aligns coloured Johnson pairs
`(J, Q)` instead (stage 14j-1's `cjohnOps`), so that `rd_ns_cj` applies. The code is in
`GraphIso/Main/M5CJLeaf.lean`, `M5CJData.lean`, `M5CJProg.lean`, `M5Case2bCJ.lean`,
`M5Case3CJ.lean`, `M5StepCJ.lean` and `M5CJWf.lean`. The new programs are variants; no approved
statement changed.

**Acceptance decision (24 October 2026).** `PLAN-14.md` §14.5 item 5 now accepts the staged
Clebsch check. Stage 14j-4b is accepted with this coverage limit; audit F1 is closed by amending
the criterion. The archived round-2 verdict remains **CHANGES REQUESTED** against the old
criterion. No end-to-end Johnson-route execution or full-list child summary has been proved.

1. **Johnson leaves stay inside their domain** (`M5CJLeaf.lean`). Every reachable Johnson leaf
   of Case 2b's leaf tree, of Split-or-UPCC and of Case 3's outcome is the extension, along the
   numbering of `Φ ∖ S` or of the dominant class `C`, of a Johnson embedding on more than
   `(m' + 3)/2` of its `m'` points (`leafTree_jleaf`, `splitTree_jleaf`, `outTree_jleaf`; from
   `split_or_johnson` at `t = (m' + 3)/2`). On data: `choiceLeavesD_along`, `outcomeD_along`
   (`JAlong`), and the dominant class has more than `(|V| + 1)/2` points (`c3ClsD_facts`).
2. **The canonical colourings and the coloured pairs** (`M5CJData.lean`).
   - Case 2b: `q2bD` (`0` off `Φ`, `1` on `Φ ∖ S`, `2 + i` at the `i`-th point of the tuple
     `S`); `x`'s pair is the first leaf with its tuple's colouring, `y`'s pairs are the
     coloured Johnson leaves over all choices (`cjLeaves2bD`).
   - Case 3: `q3D` (`1` on `C`, `2` on `V ∖ C`, `0` on the support); `x`'s pair is the first
     structure with the first good list's colouring, `y`'s pairs are the coloured Johnson
     structures over all good lists (`cjStructs3D`).
   - **Canonicity**, choice by choice: an isomorphism carries `x`'s coloured pair to one of
     `y`'s (`cj2b_reach`, `cj3_reach`).
   - **The colour bound `hq` of `rd_ns_cj`** (each colour class off `V₀` has at most `m/2`
     points), from item 1 and the case conditions alone: `m < 2|Φ|` in Case 2 (`cj2b_hq`),
     `m ≤ 2|V|` in Case 3 (`cj3_hq`). Validity: `cj2b_valid`, `cj3_valid`.
3. **The variants** (`M5Case2bCJ.lean`, `M5Case3CJ.lean`).
   - `m5Case2bCJProg` tests whether `x`'s first leaf is a Johnson leaf (`c2bJTestProg`,
     `c2bJD`). Its Johnson route answers `none` if the degrees of transitivity differ.
   - `m5Case3CJProg` answers `none` if the numbers of fixed points differ; otherwise it computes
     the colourings, the twins flag and the first structure.
   - A Johnson leaf or structure goes to the Johnson route: Align with `cjohnOps` over `y`'s
     coloured pairs, then `rdBranch` at `st = (2, X₀)`. Anything else runs 14j-4's program.
   - `RunsWithin.c2bCJProg`, `RunsWithin.c3CJRouteProg`: the answer is correct; the children
     are `StepChild |W| m` with factor `c2bR · max(m, uB!)` or `c3R · max(m, uB!)`; no orbit is
     stuck (`alignRd_cj_ns`, with `hq`, alignment and validity proved, not assumed).
   - `RunsWithin.m5Case2bCJProg`, `RunsWithin.m5Case3CJProg`: the answer is correct in both
     branches. 14j-4's partition-route hypotheses are needed only when the leaf or structure is
     not a Johnson one. Case 3 counts `2 · c3Count` comparisons, since the colourings are
     computed again inside `m5Case3Prog`, and its factor is the sum of the two routes'.
4. **The dispatcher and the step** (`M5StepCJ.lean`). `m5DispatchCJ`, `m5CoreCJProg` and
   `m5StepCJProg` are 14j-4's programs with the two variants.
   - `RunsWithin.m5DispatchCJ`, `RunsWithin.m5CoreCJProg` and `RunsWithin.m5StepCJProg` hold
     under 14j-4's hypotheses and those of the Johnson routes. These are `RDOrbit` at
     `st = (2, X₀)`, the align charges `Bg1J₂` and `Bg1J₃`, a bound `uB` on the union cells'
     labels, and `Lg` large enough for the numbers of candidates. The answer is correct, and
     the children are as in 14j-4 with factor `m5CFCJ`.
   - **No stuck orbit** (`RunsWithin.m5DispatchCJ_ns`, `RunsWithin.m5CoreCJProg_ns`): in every
     case except a partition leaf of Case 2b or a partition structure of Case 3. Those keep
     14j-4's hypothesis (a colored `t`-partition with `4t ≤ 3m`), and Case 3 keeps "no twins".
     The factor `m5CFnsCJ` has no `m!`.
   - Well-formedness: `wf_m5Case2bCJProg`, `wf_m5Case3CJProg`, `wf_m5DispatchCJ`,
     `wf_m5CoreCJProg`, `wf_m5StepCJProg`.
5. **Checks** (`GraphIsoChecks/MainM5CJ.lean`; about 3.5 minutes, peak 10 GB).
   - **Why the case programs do not run whole.** A Johnson leaf needs `V₀` on more than half
     of a numbered set (item 1); the smallest case is the Clebsch graph (16 points, see
     `MainM5CJRoute` below).
     - Case 3 needs `k ≥ 5` for nontrivial certificates (`16⁵` tuples); its certificates are
       trivial for `k ≤ 2`, and a hand-given Petersen colouring has a coloured partition first
       (checked).
     - Case 2b: one choice of `Case2b.choiceProg` on the Clebsch graph takes 160 s and a trace
       of 213 million events (12 GB) in the interpreter, and `y`'s candidates need 240 choices.
       (`Sₖ` on the pairs of `[5]` gives coloured partitions: Split-or-Johnson splits `T(5)`.)
   - **Kernel-checked** (`decide +kernel`):
     - the colourings against their definitions and their programs;
     - the coloured leaves (`cjOfD`, `cjOfProg`, `firstTupleProg`);
     - a coloured Johnson leaf of Case 3's shape (`J(5, 2)` on `32` points with `q3D`;
       `j32_johnson`, `j32_valid`) and its colour bound `cj32_hq`, with a control: uncoloured,
       a class of `17 > 16` points;
     - a transported pair found among `y`'s pairs by `cjohnIsoD`, with the program agreeing.
   - **The Johnson routes' Align call** (`al_j42`, kernel-checked in pieces by `execRuns`):
     `Align.alignProg (rdBranch … (2, X₀)) (cjohnGensProg m) (cjohnIsoProg m) …`, the last call
     of both routes.
     - Fixture: `S₄` on the letters and on the pairs and letters, with `X₀ = J(4, 2)` twisted by
       `(0 1)` (not `S₄`-invariant), and `y`'s pairs its images plus a 3-cycle twist.
     - Results: the answer is the brute-force coset; the children are `StepChild` with factor
       `|Ys| · m`; `halign` holds.
   - **`#eval`:**
     - the Align call on further `J(4, 2)` and `J(5, 2)` fixtures;
     - `m5Case3CJProg`, `m5Case2bCJProg` and `m5StepCJProg` on 14j-4's fixtures (answers and
       children against the CJ specs' bounds, `uB = m`);
     - the Petersen colouring.
   - **Staged check of Case 2b's Johnson route on the Clebsch graph**
     (`GraphIsoChecks/MainM5CJRoute.lean`,
     `#eval`, about 5 minutes, under 3 GB): the instance is in Case 2b's setting.
     - `G = Sym(16)` alike on a window of 16 points and the base, giant. `F(x)` is the Clebsch
       graph's group `2⁴ : Sym(5)` and `F(y)` its conjugate by the unique isomorphism `g₀`.
       `Φ` is the base, the degree is `1`, and `c2bJD` holds.
     - `x`'s first leaf is `J(5, 2)` on the ten non-neighbours of a vertex, with
       `|V₀| = 10 > 9`; `hq` holds.
     - `y`'s candidates `cjLeaves2bD` are 3840 coloured pairs, 16 of them distinct. They are
       computed by a memoized version proved equal (`ys2bM_eq`).
     - The Align suffix of `c2bCJProg` runs with modified input: `cjohnOps` and
       reduce-and-derive at `(2, X₀)` on the 16 distinct candidates. The answer is `{g₀}`,
       `halign` holds, and there are 22 children, `StepChild` with the factor `16 · m`.
     - The test, the degrees, the first leaf and the candidates are evaluated through the data
       functions that `RunsWithin` proves the programs return, since the programs are too slow
       (above). Candidate membership suffices for `halign` and the answer-correctness
       argument (`RunsWithin.alignRd`). Execution still iterates over the list: its cost and
       child summary depend on multiplicities. The 22 children are only those of the suffix
       on 16 candidates, not of the case program on all 3840 candidates.

**Validation.** The individual files compile without warnings under `scripts/guard.sh`. No Lean
line exceeds 100 characters, and the sources contain no `sorry`, `admit`, `native_decide`,
`noncomputable`, axiom or option override. The axiom audit lists 43 more library theorems and
seven check theorems. Size: about 6,200 lines of library code, 720 lines of checks.

**What is not covered.**

- An end-to-end Case 2b or Case 3 execution reaching a Johnson leaf (optional follow-up).
- Case 2b's and Case 3's partition leaves keep 14j-4's `4t ≤ 3m` hypothesis for no stuck orbit.
- The dispatcher over M0–M5 and the recursion (14j-5).
- The cost bound (14j-6).

**14j-5 design decision.** Strengthen the affected macro-step specs in place, as recorded in
`PLAN-14.md` and `14J5-DESIGN-ISSUE.md`: bounded input generators in the sub-solver predicates,
nonempty children in `ChildList`, and proofs that both invariants propagate. The bound must
hold throughout recursion; an empty root needs its own cost bound. The contract repair,
Schreier–Sims bounds, statement-snapshot updates and recursive implementation remain open.

## Milestone 14, stage 14j-4: M5, correctness and the plain cases (`PLAN-14.md` §14.4)

The giant macro-step, in `GraphIso/Main/M5*.lean`. The setting is a hinted instance whose base
action contains `Alt(Γ)`.

1. **Restriction to window and base** (`M5Restrict.lean`, Babai Obs. 3.1.10).
   - `restrictBaseProg` restricts the group to `w ∪ base`. The window, in list order, becomes
     the string positions `[0, |w|)` and the base stays a base. The target is aligned
     (`y ∘ σ`, representative `1`), and the labels are re-indexed.
   - The continuation's answer is lifted back with the kernel of the restriction
     (`AnsOK.rb_lift`, `rb_iso_eq`).
   - **The restricted hinted instance is valid** (`rbHInst_valid`). Its group is faithful on
     the new string positions because the base action is a giant (`rb_baseHom_eq_one`):
     - an element fixing the window fixes every label, and some label is proper and nonempty
       (`rb_proper_label`);
     - so its base image fixes every point, since `Alt(m)` is 2-transitive for `m ≥ 4`
       (`rb_alt_two`).
   - Its measure is unchanged, and its window contains every string position
     (`rbHInst_measure`).
2. **Certificates and the case decision** (`M5Cert.lean`).
   - `m5CertProg` is `fullProg` with the hinted sub-solver (`m5_stepSub`): calls without a
     hint, on windows of at most `n/k` points. The calls are counted: the cost is at most
     `certCount · C(n/k) + certWork` (`fullCost_le_count`), assuming `C` is monotone in the
     window.
   - The full-group map `m5Fmap` comes with everything the case programs need: contained in
     `G`, base-invariant, local, natural under relabelling (`m5Fmap_relabel`), and matching
     `x` on the window.
   - The case decision `m5CaseProg` adds the Case 2a/2b separation (`m5Case_spec`). It
     decides `(|Φ| − 2)`-transitivity with `degD`, using the classical lemma
     `alt_le_of_tupTrans`, from mathlib's `IsMultiplyPretransitive.alternatingGroup_le`.
3. **Align composed with reduce-and-derive** (`M5Align.lean`).
   - Align's sub-solver hypothesis takes one cost for every valid representative. So every
     branch is charged the most expensive one (`ar_branch_max`), over all valid
     representatives (`exists_allPermsD`).
   - `RunsWithin.alignRd` has `StepChild` children with factor `|candidates| · F`.
   - Variants: the general factor (`alignRd_general`), and no stuck orbit for a partition or
     a coloured Johnson structure (`alignRd_part_ns`, `alignRd_cj_ns`).
4. **The cases** (`M5Cases.lean`).
   - **Case 1** (`m5Case1Prog`, `_ns`): Align on the orbit partition, then reduce-and-derive.
   - **Case 2a** (`m5Case2aProg`): the pullback. Its sub-calls are restricted to their
     windows (`pbSubR`), so they are valid instances without a hint, on at most `|w|/2`
     points. There are `(s + 1)·|w|` of them.
   - **Case 2b** (`m5Case2bProg`): Align on the leaf, then reduce-and-derive. Its factor is
     the general `m!`, or `m` for a partition leaf with `4t ≤ 3m` (`m5Case2bProg_part`).
   - **Case 3** (`m5Case3Prog`): counted comparisons on windows of at most `n/k` points, then
     Align on the first structure (unique, `m5_c3First_unique`), then reduce-and-derive. On
     the fallback signal it runs M3.
   - **Case 3 with a partition leaf** (`m5Case3Prog_part`, in `M5CasesNs.lean`). It assumes no
     large twins (`¬ C3Twins`, from the thresholds by `m5_no_twins` and `m5_fix_iff_supp`) and
     that `x`'s first structure is a colored `t`-partition with `4t ≤ 3m`. Then there is no
     fallback, no orbit is stuck, and the factor is `c3R · m`. Round 1 found this
     corollary missing (finding F1).
5. **The dispatcher and the step** (`M5Core.lean`, `M5Step.lean`).
   - `m5CoreProg` runs the certificates for `x` and `y`, then the case decision for each,
     then `m5Dispatch`.
   - If Case 2 is decided differently for `x` and `y`, there is no isomorphism
     (`m5_large_iso`, `m5_isA_iff`, `m5_tupTrans_iso`).
   - `RunsWithin.m5CoreProg` gives the correct answer. Its cost is:
     - the Align children, as a `ChildList` with `StepChild` and factor `m5CF`;
     - the counted calls: `2 · certCount + m5CK` at `C(n/k)`, and `m5CH` at `C(|w|/2)`;
     - the work.
   - **No stuck orbit** (`m5Dispatch_ns`, `m5CoreProg_ns`): with partition leaves in Cases
     2b and 3 and no twins in Case 3, the factor is `m5CFns`, a multiple of `m` with no
     factorial.
   - `RunsWithin.m5StepProg` is the restriction plus the core, for the parent coset `σ • G`.
     The restricted instance's validity, the certificate setting, `φ` (`exists_phi`), the
     giant condition after the restriction (`m5s_giant`) and the sub-solver predicate are
     all derived.
6. **Hypotheses still taken:**
   - the backend charges, bundled in `M5Bounds` and `RDBounds`; those depending on `F(x)` or
     `F(y)` are stated for every group `M5Full` allows;
   - the per-orbit `RDOrbit` of reduce-and-derive (`hD₁`, `hD₂ᵦ`, `hD₃`);
   - the numeric conditions `5 ≤ k`, `k + 2 ≤ m`, `2k ≤ m`, `12 ≤ m`.

   Cases 2b and 3 use the general reduce-and-derive factor `m!`, except for Case 2b's
   partition leaves. Their Johnson leaves get progress in 14j-4b.
7. **Checks** (`GraphIsoChecks/MainM5.lean`, `MainM5b.lean`; about 14 and 25 minutes, peaks
   12 and 9 GB).
   - **Kernel-checked executions in pieces.** The executions too large for one kernel check
     (16–60 GB each, measured under `scripts/guard.sh`) are theorems
     `∃ v s, RunsS ssOracle body0 recF P v s ∧ Q v s = true` about the **actual program** `P`,
     run with the verified Schreier–Sims oracle, milestone 1's solver as the recursive
     procedure and the instrumented sub-solver `spySub`. `s` is the list of recorded children
     (`flatMap_recF`: `MainSteps.records` of the trace). `Q` compares the answer with the
     brute-force coset and the children with the stated bounds of the program's spec
     (`kidsOK`: valid, with the size facts and a smaller measure; at most `cK` counted calls
     with `k · window ≤ n`, at most `cH` with `2 · window ≤ |W|`, and `StepChild` children
     whose windows sum to at most `cF · |W|`). The bounds are the spec's constants (`certCount`,
     `m5CK`, `m5CH`, `m5CF`, `c3Count`, `c3R`, `c2bR`), not the observed counts. They are
     proved from `execRuns` (`GraphIsoChecks/Exec.lean`): every piece of at most 5000 trace
     events and every composition step is its own declaration, under the default budgets; `Q`
     is a `decide +kernel`.
     - the dispatch (`disp_case1`, `disp_differ`, `disp_case2a`) with `F = Aut`;
     - the certificates on the restricted instance (`cert_xA`, `cert_yA`, `cert_xB`,
       `cert_yB`): their values are the full groups the step's bounds use, and their children
       meet `certCount`;
     - **the whole M5 step** on `S₄` (`m = 4`, `k = 3`; `step_iso`, `step_noniso`);
     - **Case 3** (`c3_iso`, `c3_noniso`, `c3_fallback`: `S₃`, `k = 1`, including the
       fallback to M3);
     - **Case 2b** (`c2b_klein`: `S₄` with `F` the Klein group, about a million trace events);
     - **the whole M5 step at base size 5** (`step5`: `S₅`, `k = 3`, six isomorphisms), with
       the certificates' values `cert_x5`, `cert_y5` (through the literal restricted instance
       `R5`, `R5_eq`).
   - **Single kernel checks** (`decide`): the restriction on `S₄ × ⟨(4 5)⟩` (valid restricted
     instance, the giant survives, one sub-call, the answer contains `(4 5)`), the case
     decision for Cases 1, 2a, 2b and 3, and `alt_le_of_tupTrans` on data.
   - **Relaxed parameters.** Every fixture has `k ≤ 3`, `m ≤ 5`, outside the spec's `5 ≤ k`,
     `k + 2 ≤ m`, `2k ≤ m`, `12 ≤ m`, so these checks stand on their own, not as instances of
     the spec. The smallest admissible fixture (`S₁₂`, `k = 5`) did not finish in 30 minutes
     under the interpreter. All the kernel-checked runs stay within the stated bounds anyway;
     one `#eval` run does not (`A₄` with `x` constant: 576 certificate calls per string
     against `certCount = 384`), and the check records that.
   - **`#eval` only:** further dispatch fixtures (`S₅` and `A₄` in Case 2a, Case 3 with
     `k = 2`, Case 2b on pairs), the whole step's children on `S₄` acting on pairs and with
     `k = 2`, the `A₄` run above, and the step at `m = 5` on further strings.

**Validation.** `scripts/build-seq.sh --wfail` succeeds under `scripts/guard.sh` with
mathlib prebuilt (no single process above 40 GB). No Lean line exceeds 100
characters, and the sources contain no `sorry`, `admit`, `native_decide`, `noncomputable`,
axiom or option override. Size: about 7,150 lines of library code (with `M5CasesNs.lean`),
640 lines of checks (`MainM5.lean`, `MainM5b.lean`), and the kernel execution toolkit
(`GraphIsoChecks/Exec.lean`, `ExecSteps.lean`, about 670 lines).

**What is not covered.**
- The coloured Johnson alignment for Cases 2b and 3 (done in 14j-4b, above).
- The dispatcher over M0–M5 and the recursion (14j-5).
- The cost bound (14j-6).

## Milestone 14, stage 14j-3: M4 (`PLAN-14.md` §14.3)

M4 is the macro-step for a hinted instance whose base action `P` is transitive but not a giant.
The code is in `GraphIso/Main/M4Bridge.lean`, `M4Struct.lean` and `M4Step.lean`. There is no
alignment, because the tree depends on `G` alone.

1. **Covers and bridges** (`M4Bridge.lean`).
   - `IsLeftCover.trans` composes covers. On data, `prodRepsD` and `isLeftCover_prodRepsD`
     give the product list of representatives, of length `|rs| · |rs'|`.
   - `leafStabProg` computes its stabilizer through the restriction to a window. On the base
     window `[n', N)` that restriction is `baseHom` (`baseHom_winE`,
     `restrictHom_baseWin_val`).
   - A structure on `Γ ∖ S` extends to `Γ` along the window's numbering (`decodeOut_extD_shE`).
     If `K` is a leaf stabilizer, `baseHom K` preserves the extended structure
     (`leafStab_baseHom_extOut`).
   - For a Johnson leaf, the colouring `{S, rest}` (`restColsD`) gives a coloured Johnson
     structure that `K` preserves (`cj_ext_stab`). Its colour classes outside `V₀` have at
     most `m/2` points when `2|S| ≤ m` (`cj_ext_hq`, from `IsJohnson.card_gt`).
2. **Individualization** (`M4Bridge.lean`).
   - `degreeModel_spec` with `cap = m − 2` gives the degree `d`. The non-giant condition is
     `d < m − 2`.
   - `H = fixFirst G n (d − 1)` is computed by `pointStabsProg`. It covers `G` by at most
     `m^(d−1)` cosets, and has at most `s` generators (`m4_ps_gens_le`).
   - `H` is transitive and not 2-transitive on the rest of the base (`indiv_of_degree`,
     `indiv_trans`, `indiv_not_two`).
3. **The structure** (`M4Struct.lean`).
   - `orbitalProg` at `n' = n + d − 1` gives the orbital configuration of `H` on `Γ ∖ S`.
     It is coherent, homogeneous and not a clique (`ms_config`), and `H` fixes it
     (`ms_relab`).
   - If some colour graph is disconnected, the leaf is the components partition and
     `K = H` (`ms_comp_fixed`).
   - Otherwise the configuration is uniprimitive (`ms_uniprimitive`). The first leaf of the
     Split-or-Johnson tree is taken with `t = (k + 3)/2`, and its stabilizer `K` is computed by
     `leafStabProg`. It covers `H` by at most `2^(129(⌈log₂ k⌉+2)²)` cosets (`ms_leaves`,
     `m4Struct_spec`).
   - The leaf is a colored `t`-partition or a trimmed Johnson structure (`M4Out`).
4. **The step** (`M4Step.lean`).
   - `m4StepProg` runs, in order: the degree, the individualization, the structure, the
     composed cover (`|reps| ≤ m^(d−1) · count`, `m4R`), the extension of the leaf to the
     base (`m4St`), and `rdProg`.
   - `RunsWithin.m4StepProg`: the answer is correct, the children are `StepChild |W| m`, and
     `c = |reps| · m!`.
   - `RunsWithin.m4StepProg_ns` assumes `4 · max((k+3)/2, d−1) ≤ 3m`, `2(d−1) ≤ m`, `m ≥ 5`
     and the union-cell bound. Then no orbit is stuck, and `c = |reps| · max(m, uB!)`:
     - a partition leaf goes through `rdProg_part_ns` (`m4_part_facts`);
     - a Johnson leaf goes through `rdProg_cj_ns` (`m4_cj_facts`: `JValid`, `IsJohnson`,
       `K` preserves `cjdec`, and the colour bound).
   - **Route to the cost stage.** Under `TransitivityBound T`, the computed degree is at most
     `T(m)` (`m4_deg_le_T`). The single condition `2(d − 1) + 6 ≤ m` gives all the numeric
     hypotheses (`m4_numeric`).
   - **Hypotheses still taken:**
     - `hKs`, the generator count of the computed `K`. As with 14j-2's `DOutGens`, the
       validity of the truncated stabilizer generators inside `leafStabProg` is not
       exported.
     - `hD`, the per-orbit `RDOrbit`, as in `rdProg`.
     - `hu`, the union-cell bound.
     - The case conditions: the base action transitive, not a giant, and `4 + d − 1 ≤ m`.
5. **Checks** (`GraphIsoChecks/MainM4.lean`), about 3.5 minutes in total. The two whole-step
   checks (each above 24 GB as a single kernel check) are kernel-checked in pieces since
   stage 14j-4 (`m4_step_agl`, `m4_step_c5`, on the run's tokens `tokF`; `m4RunQ_flatMap`
   shows the tokens read exactly the children, chain steps and `kernel` calls of the trace,
   so `m4_step_agl_tr`, `m4_step_c5_tr` state the checks on the trace).
   - **Kernel-checked examples** (`decide`):
     - `m4StructProg` on `D₄`, the disconnected case: the components partition, `K = H`,
       one rep, and program = model;
     - the soj leaf and its stabilizer, checked by brute force on the models for `D₅` and
       `C₅`;
     - `M4Out` of the leaves;
     - the composed cover `S₄ → S₃ → S₂`;
     - individualization on `AGL(1,5)` and `D₅`.
   - **The whole M4 step on `AGL(1,5)`**, which needs individualization (`H = C₄` on the other
     four points) and takes the components branch, **and on `C₅`**, which takes the
     uniprimitive (Split-or-Johnson) branch. On `C₅` the kernel also checks that no colour
     graph is disconnected; the leaf count is 5. Round 1 found the uniprimitive branch
     without a full-step kernel check (finding F1); the `C₅` check is adapted from the
     auditor's probe. With the instrumented sub-solver of 14j-2, the kernel checks:
     - the answer against the brute-force coset;
     - the children against `StepChild`, `ChildList` with factor `|reps| · m!`, `SizeChild`
       and `MeasLt`, each child being valid, and the hinted ones transitive with valid labels;
     - that the reduce-and-derive tags are `{0, 2}` on `AGL(1,5)` and `{0}` on `C₅`, with no
       stuck orbit.
   - **The M4 pieces on `D₅`:** the case conditions, the cover, and the extended structure
     preserved by `K`.
   - **`#eval` only:**
     - the whole step on `D₅`;
     - the Petersen action of `S₅`;
     - program = model for `m4StructProg` on `C₅` and `D₅`.

     These exceed the kernel's limits. No Johnson leaf arises at these sizes; `IsJohnson` is
     checked on a constructed structure in 14j-1's `MainHints`.

**Validation.** `lake build --wfail` succeeds with mathlib prebuilt. No Lean line exceeds 100
characters, and the sources contain no `sorry`, `admit`, `native_decide`, `noncomputable`,
axiom or option override. Size: about 2,500 lines of library code and 310 lines of
checks.

**What is not covered.** M5 (14j-4), the dispatcher and the recursion (14j-5), and the cost
bound (14j-6).

## Milestone 14, stage 14j-2: the macro-step framework and M0–M3 (`PLAN-14.md` §14.2)

The second loop of the main recursion, in `GraphIso/Main/`. Every macro-step is a program with
a hinted sub-solver `sub` as a parameter; stage 14j-5 will instantiate it with `.recur`.

1. **The framework** (`Frame.lean`).
   - `HSubSolves`: `sub` solves every valid hinted instance satisfying a predicate `P`, at
     cost `C (window size, base)` (`HInstData.baseOpt` is the base size, or `none` without a
     hint), with at most `s` output generators.
   - A step's spec gives three things:
     - its run, within the sum of `C` over a list `ch` of children's measures plus explicit
       work;
     - a correct answer for the parent (`InstData.OK`);
     - `ChildList n c pred ch`: the window sizes sum to at most `c · n`, and each child
       satisfies `pred`.
   - The predicates are the hypotheses of the potential lemmas: `StepChild` for `pot_step`,
     `FreeChild` for `pot_free`, and `ChainChild` for the chain rule. Each implies a smaller
     measure (`StepChild.measLt` etc., lexicographic on `(window size, base)`).
   - Each predicate bounds the child's window by the parent's. Round 1 found that
     `FreeChild` did not (finding F1), so a free step's sub-solver hypothesis also covered
     instances of larger measure.
   - `SizeChild` records the size facts a child keeps: the same `n₀`, at most the parent's
     string positions, and degree at most `max N (2n)`.
2. **Transfer** (`Transfer.lean`).
   - `viaChildProg` solves a parent coset `σ • K` through a re-based child `G'` that acts on
     the string positions as `K` does:
     1. align the coset (the target string becomes `y ∘ σ`);
     2. pad the strings to the child's degree;
     3. call `sub` on the hinted child (`childHInst`, valid by `childHInst_valid`);
     4. restrict the answer to the string positions and `lift` it into `K` (`transferProg`);
     5. shift the answer back by `σ`.
   - `RunsWithin.viaChildProg` gives `AnsOK` for the parent. The parent needs only base
     invariance: the lifted representative is the right one because the child is faithful on
     the string positions (`tr_eq_of_agree`).
   - `sameDegProg` makes a call without a hint at the same degree.
3. **Steps without re-based children** (`StepsBase.lean`). Each step's sub-calls have no
   hint and the same degree (`plainSub`).
   - **Base case:** a window fixed pointwise, including the empty window (`fixedTest_iff`,
     `RunsWithin.fixedStepProg`).
   - **Chain rule** (`RunsWithin.chainProg`): `seqProg` over the orbits; `ChainChild`
     children, `c = 1`.
   - **Kernel reduction** (`RunsWithin.kerRedProg`): the kernel of the base action and its
     coset representatives, at most `m!` of them, then `seqProg` over the kernel's orbits.
     These lie inside label fibres, so the children have no hint and at most half of the
     window (`sb_half_of_fix`): `StepChild` children.
   - **M3** (`RunsWithin.m3Prog`) is the kernel reduction applied to the instance itself.
4. **The free coarsenings** (`StepsHint.lean`).
   - `RunsWithin.m0StepProg`: no hint, a transitive group, `|W| ≥ 2`.
   - `RunsWithin.m1StepProg`: an intransitive base action, `k < m`.
   - `RunsWithin.m2aStepProg`: a proper block system with a non-equidistributed label,
     `2m' ≤ m`.
   - Each makes one hinted child through `viaChildProg`. Children are `FreeChild`, `c = 1`,
     and carry `SizeChild` facts.
5. **The dynamic chain** (`DynSeq.lean`, a design correction to `PLAN-14.md` §14.2).
   - `seqProg` processes a fixed list of orbits. Each later orbit is solved in the coset
     returned so far, and that group need not be transitive on it. A hinted child must be
     transitive on its window.
   - `dynSeqProg` instead takes, at each step, the first orbit of the *current* group on the
     remaining window. `RunsWithin.dynSeqProg` gives the run and the correct answer. The
     processed orbits are orbits of subgroups of the starting group, and their sizes sum to at
     most `|W|`.
   - The checks include a fixture on which the static chain hands a child a non-transitive
     group.
6. **The block-stabilizer loop and M2b** (`M2bLoop.lean`).
   - `m2bLoopProg` branches over the cosets of `R = Stab(B₀)`, then runs the dynamic chain.
     Each step's orbit `O''` becomes one of two children:
     - a hinted child on the block, when `L ∩ B₀` is not constant on `O''`;
     - a child without a hint otherwise. Then `2|O''| ≤ |O_R|` by `card_le_of_const`, since
       `R` is transitive with the hint on the `R`-orbit `O_R ⊇ O''`. This is `ml_handle`.
   - `RunsWithin.m2bStepProg`: `StepChild |W| m` children, with `c = |reps| ≤ #blocks`.
7. **Reduce-and-derive** (`RD.lean`).
   - `rdProg` branches over a cover of `G` by cosets of `K`, then runs the dynamic chain.
     Each step's orbit `O`, an orbit of some `H ≤ K`, goes through `deriveProg` and is
     dispatched on its tag:
     - tag 0: a call without a hint;
     - tags 1, 2, 4: a re-based child;
     - tag 3: `m2bLoopProg` inside the M1 child;
     - tag 5: the Johnson fallback's cosets, then a static chain without hints, inside the
       group re-based onto the cells;
     - tag 6: the kernel reduction on the orbit.
   - `RunsWithin.rdProg` and `RunsWithin.rdProg_general`: `StepChild |W| m` children with
     `c = |rs| · (N − n)!`.
   - With no stuck orbit, the factor drops:
     - `RunsWithin.rdProg_part_ns` (`K` preserves a colored `t`-partition with `4t ≤ 3m`):
       `c = |rs| · m`;
     - `RunsWithin.rdProg_cj_ns` (a coloured Johnson structure, with at most `uB` union
       cells): `c = |rs| · max(m, uB!)`;
     - the tag-5 factor comes from `rd_cj_reps5`. The progress theorems of 14j-1 discharge
       the no-stuck hypothesis for every `H ≤ K` (`rd_ns_part`, `rd_ns_cj`).
   - **Hypotheses:**
     - The charges are bundled in `RDBounds`, uniform over groups of degree at most `N` with
       at most `sIn` generators.
     - `rd_ss_bounds` proves `RDBounds` for the Schreier–Sims backend with `sIn = N²`.
     - `DOutGens`, the generator counts of the subgroups `R` and children of tags 3 and 5, is
       a hypothesis on model outputs. It is not proved for the Schreier–Sims backend: the
       validity of the truncated stabilizer generators inside `blockStabProg` is not
       exported.
8. **Checks** (`GraphIsoChecks/MainSteps.lean`). Kernel-checked examples (`decide`), about
   2 minutes in total.
   - **How they are run.** An instrumented sub-solver records each sub-call's measure,
     sizes, window, group and labels through a marker backend call, then solves the child
     with milestone 1's solver and the verified Schreier–Sims oracle. The recorded children
     are exactly the calls made. Each answer is compared with the brute-force coset, and the
     children are checked against `ChildList` with the step's predicate and factor, `MeasLt`,
     `SizeChild`, validity, and (for hinted children) transitivity and valid labels.
   - **Steps covered:**
     - the base case;
     - the chain rule;
     - M0 on `D₄`, including a coset outside it;
     - M1 and M2a;
     - M3 and the kernel reduction (`C₂ ≀ C₂`);
     - transfer back from the M0 and M1 children;
     - `sameDegProg`.
   - **`dynSeqProg`:** a fixture where the static chain would hand a child a non-transitive
     group.
   - **The M2b step:** on `C₄`, with and without unhinted children.
   - **`rdProg`:** each step's tag is recomputed from the trace.
     - Tags 0 and 1: a preserved colored partition on `D₄`.
     - Tag 3: `m2bLoopProg` inside, on `C₄`.
     - Tag 6: `C₃`, the kernel fallback.
     - Tags 4 and 5: the coloured Johnson structure of stage 14j-1 at degree 16.
   - **Negative controls** in a scratch copy, not in the file: wrong predicates and factors,
     violated case conditions, a sub-solver that always fails, a dropped coset
     representative, a broken structure.

**Validation.** `lake build --wfail` succeeds with mathlib prebuilt. No Lean line exceeds 100
characters, and the sources contain no `sorry`, `admit`, `native_decide`, `noncomputable`,
axiom or option override. Size: about 6,300 lines of library code and 630 lines of
checks.

**What is not covered.** M4 (14j-3), M5 (14j-4), the dispatcher and the recursion (14j-5), and
the cost bound (14j-6).

## Milestone 14, stage 14j-1: hinted instances and derived hints (`PLAN-14.md` §14.1)

The first of four loops for the main recursion, in `GraphIso/Main/`, namespace
`GraphIso.Main`. A hinted instance has degree `N = n + m`: string positions `[0, n)`, base
`[n, N)`, and labels as `LabelData`.

1. **Hinted instances as data** (`HInst.lean`).
   - `HInstData` holds an instance, `n₀`, `n`, and optional labels.
   - `HInstValid` is the representation invariant: a valid instance, the window inside
     `[0, n)`, an invariant base, and a group faithful on the string positions. With labels,
     it adds `HintValid` and transitivity on the window.
   - Bridges to stage 14a: `HInstValid.isHint` and `HInstValid.transitive`. `hmeasure` is the
     pair `(n, m)` that the potential charges.
2. **Free coarsenings** (`Free.lean`). Each spec gives the run and an explicit cost, valid
   group data, `HintValid`, an invariant window with the group transitive on it, faithfulness,
   an isomorphism with the same action on the string positions, and the new base size:
   - **M0** (`RunsWithin.m0Prog`): the maximal blocks of the window become the base, so the
     new `m` is at most `|w| ≤ n`;
   - **M1** (`RunsWithin.m1Prog`): the first base orbit on which the labels are not constant,
     `k ≤ m`;
   - **M2a** (`RunsWithin.m2aProg`): block labels on a proper block system of the base,
     `2 m' ≤ m`.
3. **Reductions** (`Reduce.lean`):
   - **M2b** (`RunsWithin.m2bProg`, `m2b_hintValid`, `m2b_card`): the stabilizer of a block,
     with a left cover by at most `|Ψ|` cosets. Re-based onto the block, its base has
     `2 m' ≤ m`. The labels intersected with the block are a hint on *every* nonempty invariant
     part of the window (`hint_blockStab`).
   - **The Johnson fallback** (`RunsWithin.jfallbackProg`, `jfallback_half`,
     `length_jUnionData_le`). The group is first re-based onto the cells. The fallback is
     the pointwise stabilizer of the positions of the `u` cells in the Johnson union, so its
     elements fix each union cell as a set. It comes with a left cover by at most `u!`
     cosets, where `u ≤ |lab u₀| · s` (`jfallback_cells_le`, the data form of
     `card_jUnion_le`).
     - When the labels outside `V₀` and the union labels are constant, its orbits in the
       window have at most half of it.
     - Round 1 found an earlier version that fixed every point of the union cells
       (finding F1). Its factor could exceed `u!`.
4. **The derived hint, model** (`DeriveModel.lean`). `Derived` lists the children of a
   `K`-orbit `O`, each meeting `pot_step`'s measure:
   - `noHint` with `2|O| ≤ |W|`;
   - `inter` with `4m' ≤ 3m`;
   - `blocks`, by labels or by a block stabilizer, with `2m' ≤ m`;
   - `johnUnion` with `4m' ≤ 3m`;
   - `johnFallback`, with orbits of at most `|W|/2` points.

   Which outcomes each structure yields:
   - `derived_colPart`: a colored `t`-partition with `4t ≤ 3m`;
   - `derived_johnson`: a Johnson structure with `m ≤ 4t`;
   - `derived_cjohnson`: a coloured Johnson pair `(Q, J)` whose classes outside `V₀` have at
     most `m/2` points;
   - `derived_extPart` and `isColPart_ext_bound`: the extended partitions of stages 14h and
     14i, when the leaf blocks and the rest have at most `3m/4` points each.

   **A preserved set alone gives no progress** (`derived_set`). When `K` preserves `Φ` with
   `2|Φ| > m`, the labels may be non-constant on `O` only inside `Φ`. Cases 2a and 2b
   therefore need their final structures (the pullback, or the structure of Case 2b).
5. **Coloured Johnson structures** (`CJohnOps.lean`). This is the design correction of
   `PLAN-14.md` §14.1 item 5: a trimmed Johnson embedding alone leaves the points outside
   `V₀ ∪ ⋃Λ` free, and a base orbit there can have about `7m/8` points.
   - `cjohnOps_spec` makes `(Q, J)` a `StructOps`. The stabilizer `Stab(Q) ∩ Stab(J)` has
     explicit generators (`cjohnGensD_closure`, at most `3m²` of them by
     `length_cjohnGensD_le`).
   - The isomorphism search respects the colours (`cjohnIsoD_some`, `cjohnIsoD_none`).
   - The pairs themselves are built from the leaves of stages 14h and 14i in stage 14j-2.
6. **The derived hint as a program** (`Derive.lean`). `deriveProg` dispatches on the structure
   tag:
   - `deriveFreeProg` handles no structure or a colored partition, which the program does not
     read. It tests constancy, then runs M1, then takes the maximal blocks of the M1 child's
     base and runs M2a or M2b on them.
   - `deriveCJProg` handles a coloured Johnson structure. It runs M1 and the block step on
     the labels outside `V₀`, then the Johnson union re-based onto the cells, then the
     fallback.

   `DOutcome` states each tag's guarantee as a property of the output, using `DSetting` (the
   parent hint, `K ≤ G`, and the `K`-orbit `O`) and `ChildOK` (a hinted child isomorphic to
   `K` with the same action on the string positions). Every child's window is `O` itself,
   so `|w'| ≤ |w|`. Round 1 found the kept-hint outcomes missing this constraint (finding
   F2).

   - tag 0, no hint: `2|O| ≤ |w|`;
   - tag 1, M1: `ChildOK`, `4m' ≤ 3m`;
   - tag 2, M2a: `ChildOK`, `2m' ≤ m`;
   - tag 3, M2b: `P` is the M1 child, `R ≤ P`, and a cover of `P` by at most `m` cosets of
     `R`. The child is `R` re-based with `2m' ≤ m`, and `HintValid` holds on every nonempty
     `R`-invariant part of `O`;
   - tag 4, Johnson union: `ChildOK`, `4m' ≤ 3m`;
   - tag 5, Johnson fallback: `P` is `K` re-based onto the cells, with the same action
     on the string positions. `R` is the pointwise stabilizer in `P` of the `u` union-cell
     positions, with a cover of `P` by at most `u!` cosets of `R` and `u ≤ m`. Each part of
     `O` on which `R` is transitive has at most `|O|/2` points;
   - tag 6, stuck: no guarantee.

   The specs are `RunsWithin.deriveProg_free` and `RunsWithin.deriveProg_cj`. Their backend
   charges are hypotheses on the specific inputs (`M1Charges`, `BlkCharges`, the re-basing
   charge, `BackendBounds` at the degree of the group re-based onto the cells). The
   fallback's cost includes `uB!` through `kerACost`, where `uB` bounds the number of union
   cells.

   `stuck` is excluded under these hypotheses:
   - `derivePart_ne_stuck`: `K` preserves a colored `t`-partition with `4t ≤ 3m` and
     `m ≥ 2`. The partition's blocks make the M1 child's base action imprimitive
     (`dv_not_prim`).
   - `deriveCJ_ne_stuck`: `K` preserves a coloured Johnson structure whose colour classes
     outside `V₀` have at most `m/2` points, with `m ≥ 5`.

   Without a structure, `stuck` can occur. With a preserved set alone, the program receives
   no structure.
7. **Checks** (`GraphIsoChecks/MainHints.lean`). Kernel-checked examples (`decide`), about
   55 s in total. Each compares the program run by the interpreter with the verified
   oracle against brute force on data:
   - **The pieces:**
     - M0 on `D₄` and `S₄`;
     - M1, M2a and M2b on `C₄`, and the Johnson fallback on `S₂ × S₂`;
     - `cjohnOps` twice: with uniform colours, and with a colour that separates a point.
   - **`deriveProg` on eight fixtures:**
     - each fixture's setting is checked by brute force (valid parent hint, transitivity,
       faithfulness, `K ≤ G`, `O` a `K`-orbit);
     - the program's output equals `deriveModel`;
     - each child acts on the string positions as the group it comes from does.
   - **One fixture per tag**, each checked for its outcome:
     - tags 0–3 on `C₄`;
     - tags 4 and 5 on a coloured Johnson structure with `m = 12`, `s = 2` and four cells
       (two of them of two points). `IsJohnson`, `JValid` and the colour bound of
       `deriveCJ_ne_stuck` are proved by kernel `decide`. `K = C₂ ≀ C₂` also permutes points
       inside the cells.
     - Tag 4: the child is `K` re-based onto the cells, with the brute-force union labels.
     - Tag 5: `P` is `K` re-based onto the cells. `R` is exactly the pointwise stabilizer of
       the union-cell positions. Two coset representatives cover `P`; the point-based
       stabilizer of round 1 would need 8. The `R`-orbits have `|O|/2` points. Round 1 found
       the earlier three-cell fixtures invalid, since they violate `IsJohnson.le_half`
       (finding F3).
     - Every child window is `O`.
   - **A negative control:** `C₃` with no structure has a primitive base action and reaches
     `stuck`.
   - **A preserved partition:** `C₆` with two colored partitions satisfying `4t ≤ 3m` gives
     tag 2, not `stuck`.

   Altered fixtures and outputs make the checks fail; these were tried in a scratch copy, not
   in the file. They include a wrong tag, a non-orbit `O`, an unpreserved structure, tag 3
   without its representatives, and a tag 5 output with `R := P`, a dropped representative,
   or the group at the parent's degree.

**Validation.** `lake build --wfail` succeeds with mathlib prebuilt. No Lean line exceeds 100
characters, and the sources contain no `sorry`, `admit`, `native_decide`, `noncomputable`,
axiom or option override. Size: about 7,800 lines of library code and 580 lines of
checks.

**What is not covered.** Stages 14j-2 to 14j-4:
- the macro-step programs M0–M5 with their children's measure, and `AnsOK` relative to the
  sub-solver;
- building the coloured Johnson pairs from the leaves of stages 14h and 14i;
- splitting tag 3's window into `R`-orbits;
- the recursive procedure;
- the cost bound and the final theorems.

## Milestone 14, stage 14i: Case 3 (`PLAN-14.md` §13)

Case 3 of the giant macro-step M5, in `GraphIso/Case3/`. The support `S` of `F` has fewer than
`m/2` points. As in Case 2b, the reduction is Align in the original group: `x`'s first
structure against all of `y`'s.

1. **The colouring** (`Colouring.lean`).
   - `CertIso` is an equivalence across strings (`certIso_refl`, `certIso_symm`,
     `certIso_trans`).
   - Isomorphisms induce it (`certIso_of_relabel`).
   - The `k`-tuples of `Γ ∖ S` are coloured by certificate equivalence, with names consistent
     across `x` and `y`:
     - a tuple of `x` is named by its first equivalent tuple of `x`;
     - a tuple of `y` is named by its first equivalent tuple of `x`, or else by a fresh name.
   - Every isomorphism maps `x`'s colouring to `y`'s (`tupleCol_iso`). `x`'s colours are
     milestone 13's `SameColour` (`colX_eq_iff`).
   - `tupleColProg` makes at most `3 m^{2k}` `certIsoProg` calls.
2. **The structures** (`Model.lean`). `case3Tree` has a node over the good lists of the
   Design Lemma (threshold `⌈m'/2⌉`). Each good list yields one of:
   - the vertex colouring, when every class is small;
   - Split-or-UPCC or `soj` on the dominant class's 2-skeleton.
   The leaves are trimmed and extended as in stage 14h.
   - The tree is natural under relabelling (`case3Tree_relabel`, `case3_reach_eOf`).
   - Without `t + 1` pairwise twins it is live and valid, with count at most
     `m'^k · 2^{129 (⌈log₂ m'⌉ + 2)²}` (`case3Tree_spec`).
   - The thresholds exclude such twins (`no_twins_of_thresholds`, from `no_large_twins`).
3. **The pipeline and the link** (`Pipeline.lean`, `PipelineProg.lean`, `Link.lean`).
   - The pipeline consists of milestone 10's `k`-ary Weisfeiler–Leman program, all good lists
     (stage 14c's pattern), the per-list outcome (reusing stage 14h's leaves and extension),
     and the enumerations.
   - The decoded list of `y`'s structures is the tree's `leafMs` (`allStructsD_leafMs`).
   - `x`'s first structure is reachable (`firstStructD_reach`).
   - Every structure is valid (`allStructsD_valid`).
   - Each `soj` tree has size at most `sojZ` (`outSzD_le`).
4. **The program** (`Case3Prog.lean`). `case3Prog` returns one of three outcomes:
   - `none` (the fallback to M3) when the Design Lemma finds no good list for `x`'s colouring.
     That implies more than `t` pairwise twins (`twinsD_spec`), but large twins need not
     trigger it. Round 1 found the documentation claiming the converse (finding F1);
   - `some none` when the two complements differ in size;
   - otherwise Align's answer.

   `RunsWithin.case3Prog_canonical` gives a correct answer for `G`, with the alignment,
   validity (for `y` without a twins hypothesis), sizes and first structure derived. It
   assumes the window contains every string position, as it does after the restriction of
   Babai's Obs. 3.1.10. Under the thresholds there is no fallback (`case3_no_fallback`).
   The Schreier–Sims charges hold with bounded lists (`c3_ss_charges`).
5. **Checks** (`GraphIsoChecks/Case3.lean`): Kernel-checked examples (`decide`), about 4.5 minutes in total:
   - the colourings on data: consistent names under a relabelling, and fresh names;
   - the pipeline programs against brute force on `C₄`, `2K₂`, a constant colouring (twins,
     no structures) and `C₅` (`soj` leaves);
   - canonicity of the complete structure lists;
   - `case3Prog` end to end with the Schreier–Sims oracle and milestone 1's solver, on `S₃`:
     an isomorphic pair (the brute-force coset), a non-isomorphic pair, and the fallback (no
     good list);
   - `case3Prog` on an empty window: `S₃`, `k = 2`, with complements listed in two orders.
     There are three Align candidates and the coset is the whole group. The colouring there
     has large twins but good lists, so the program answers (`emptyWin_large_twins`). Round 1
     found this check missing (finding F2).

   Supplementary interpreter runs:
   - `tupleColProg` on `S₅` with `k = 2` against brute-force certificate comparisons;
   - `case3Prog` on `S₅` with `k = 3`, with nontrivial certificates, against the brute-force
     coset.

   Not kernel-checked:
   - with `k ≤ 2`, `Alt(A)` is trivial, so nontrivial certificates need `k ≥ 3` and a base of
     5 points, which only the interpreter reaches;
   - milestone 10's `wlA` does not reduce in the kernel;
   - no Johnson leaves arise in these fixtures.

**Validation.** `lake build --wfail` succeeds with mathlib prebuilt. No Lean line exceeds 100
characters, and the sources contain no `sorry`, `admit`, `native_decide`, `noncomputable`,
axiom or option override. Size: about 4,400 lines of library code and 430 lines of
checks.

**What is not covered.** The main recursion (14j), which composes M0–M5, connects the
fixed points of `ψ(F)` to the support of `fullGroupK`, and handles the fallback.

## Milestone 14, stage 14h: Case 2b (`PLAN-14.md` §12)

Case 2b of the giant macro-step M5, in `GraphIso/Case2b/`. `F` has an orbit `Φ` of more than `m/2`
points, on which it is not a giant. Alignment happens in the original group:
- `x`'s structure comes from its first choices;
- `y`'s structures come from every choice;
- canonicity supplies Align's hypothesis.

1. **The choice tree** (`Tree.lean`). `case2bTree` builds, in order:
   - a node over the `(d − 1)`-tuples of `Φ`;
   - a node over the pairs of `Φ ∖ S`;
   - `wlRel` of the orbital under `P_(S)`;
   - the components of the least disconnected colour, or `soj` with `t = (m' + 3)/2`;
   - leaves trimmed and extended to the base, with the rest as one block of colour `0`.
   It is canonical (`case2bTree_relabel`) and live, every leaf is valid (`case2bTree_valid`),
   and its count is at most `|Φ|^{d+1} · 2^{129 (⌈log₂ |Φ|⌉ + 2)²}` (`case2bTree_count_le`).
   `case2bHyp_of_degree` turns the degree of transitivity into the tree's hypotheses.
2. **Leaves as structures** (`OutOps.lean`). `outOps` dispatches to `partOps` and `johnOps`
   (`outOps_spec`). The stabilizer of a valid leaf has at most `3m² + m` generators
   (`length_outGensD_le`).
3. **The data pipeline** (`Pipeline.lean`, `PipelineProg.lean`, `ChoiceProg.lean`). Each step
   is a program:
   - the pointwise stabilizer restricted to `Φ ∖ S`, generated at its degree;
   - its orbital array, the pair's colouring, and `wlRel` by milestone 10's Weisfeiler–Leman
     program (`colOf_wlColD`);
   - the components or `sojProg`, trimming, and the extension;
   - the enumeration of the choices.
4. **The link** (`Link.lean`).
   - The decoded list of `y`'s structures is the tree's `leafMs` (`allLeavesD_leafMs`).
   - `x`'s first structure exists and is reachable (`firstLeafD_ne_none`,
     `firstLeafD_reach`).
   - Every listed structure is valid for `outOps` (`allLeavesD_valid`).
   - Each `soj` tree has size at most `sojZ (N − n)`, by liveness, height and the
     Split-or-Johnson count (`sojSz_le`).
5. **The program** (`Case2bProg.lean`).
   - The degree of transitivity is computed with the toolkit (`degD_spec`, `case2bHyp_degD`).
   - `case2bProg` returns `none` when the two degrees differ.
   - `RunsWithin.case2bProg_canonical'` gives a correct answer for `G` from canonical `F` and
     `Φ`, with the alignment, validity, sizes and first leaf derived. Its cost is at most
     `|Φ|^{d−1} (N − n)²` choices, each a polynomial times `sojZ`, plus Align and the
     sub-calls.
   - The Schreier–Sims charges hold with bounded lists (`c2b_ss_charges`).
6. **Checks** (`GraphIsoChecks/Case2b.lean`): Kernel-checked examples (`decide`), about 110 s in total:
   - the enumerations;
   - the orbital colouring against brute force (`C₄`; `AGL(1,5)` with a point individualized);
   - the degree for `C₄`;
   - one `C₄` choice: the WL colouring against a brute-force refinement, and the leaf against
     brute-force components;
   - `case2bProg` end to end with the Schreier–Sims oracle on an empty window, where `G = S₄`
     and `F` is the Klein group: the answer is all 24 permutations;
   - all 12 leaves of the Klein group with multiplicity, for both listings of `Φ`, equal to
     their images under a relabelling (canonicity of the complete lists);
   - `outOps` dispatch on Johnson leaves with `s = 2`. Round 1 found these whole-program and
     whole-list checks run only by `#eval` (finding F1);
   - the leaves against milestone 11's model: the components leaf on `C₄`, compared exactly
     with a failing control (round 1, F2), and the trimmed `soj` leaves on `C₅`;
   - trimming and extension, including a Johnson leaf with cells outside `V₀`;
   - canonicity of one choice under a relabelling;
   - `outOps`'s isomorphism search.

   Supplementary interpreter runs:
   - degrees for `D₄`, `C₅`, `D₅`, `AGL(1,5)`, `PSL(2,5)` and `S₅` on pairs;
   - every choice against the brute-force concatenation (12 to 100 leaves, all valid);
   - canonicity over all choices;
   - `case2bProg` with `S₄` on graphs with 4 vertices against brute-force isomorphism cosets,
     including different degrees and a rejection by the sub-solver.

   Not kernel-checked:
   - milestone 10's `wlA` gets stuck in the kernel, so the WL data models are checked through
     program runs or `#eval`;
   - the model tree itself, whose `wlRel` reruns WL at every query, is checked through its
     pieces;
   - `case2bProg` with a nonempty window and milestone 1's solver as the sub-solver is too
     slow for the kernel; it runs by `#eval` on graphs with 4 vertices;
   - no Johnson leaf arises from these small fixtures, so Johnson trimming and extension are
     checked directly.

**Validation.** `lake build --wfail` succeeds with mathlib prebuilt. No Lean line exceeds 100
characters, and the sources contain no `sorry`, `admit`, `native_decide`, `noncomputable`,
axiom or option override. Size: about 6,700 lines of library code and 600 lines of
checks.

**What is not covered.** Case 3 (14i) and the main recursion (14j).

## Milestone 14, stage 14g: aggregation, Case 1 and Case 2a (`PLAN-14.md` §11)

The first half of the giant macro-step M5 after the certificates, in `GraphIso/Giant/`.
Recursive calls go through a sub-solver parameter, and the backend charges are explicit or
bounded through `BackendBounds`.

1. **The full group** (`FullGroup.lean`). `fullGroupK` is generated by the certificates `K(A)`
   that pass the test `Alt(A) ≤ ψ_A(K(A))`, which is the test `certProg` computes.
   - It consists of automorphisms with no hypothesis (`fullGroupK_le_autG`).
   - It is canonical (`fullGroupK_relabel`).
   - Under the thresholds it equals milestone 13's `fullGroup` (`fullGroupK_eq_fullGroup`).
2. **Aggregation** (`Aggregate.lean`).
   - The `k`-subsets of the base are enumerated exactly once each, `C(m, k)` of them
     (`ksubsD_finsetOf`, `length_ksubsD`).
   - `fullProg` runs `certProg` on each and generates `F` step by step, keeping at most `s`
     generators. Its result denotes `fullGroupK` (`RunsWithin.fullProg`).
   - Its charge premises concern only bounded generator lists and the enumerated subsets, and
     hold for the Schreier–Sims backend (`ag_ss_charges`). Round 1 found them stated for
     unbounded lists (finding F1).
   - The case decision is exact in terms of `F`'s orbits and support (`caseD_spec`,
     `RunsWithin.caseProg`).
3. **Case 1** (`Case1.lean`).
   - The orbit-length colouring is computed from the backend's orbits and satisfies
     `IsOrbitPart` (`orbitPartD_spec`). It is always a colored partition
     (`isColPart_of_isOrbitPart`) and is canonical (`orbitPart_canonical`).
   - `case1Prog` aligns the partitions of `x` and `y` by `alignProg` with `partOps`. Its answer
     is correct (`RunsWithin.case1Prog`), with the alignment hypothesis discharged by
     canonicity.
4. **Case 2a** (`Case2a.lean`).
   - `pullbackProg` takes the pointwise stabilizer `K` of `Φ` and branches over the identity
     and `H`'s generators (`c2_cover`, so no parity is computed). In each branch it solves on
     `K`'s orbits and adds `F`'s generators. Its answer is correct for the coset
     (`RunsWithin.pullbackProg`).
   - `case2aProg` aligns `Φ(x)` with `Φ(y)` with `setOps` and runs the pullback inside
     (`RunsWithin.case2aProg`).
   - The unique large orbit is canonical (`largeOrbit_canonical`). So the alignment hypothesis
     is derived from canonical `F` (`RunsWithin.case2aProg_canonical`, finding F2). What
     remains assumed is `F(x) ≤ Aut(x)`, which `fullGroupK_le_autG` supplies.
   - The orbits of `K` have at most `n/2` points. This is derived from the giant hint's labels
     by `card_orbit_le_half` (`c2_hhalf_of_labels`, `RunsWithin.case2aProg_of_labels`).
5. **Checks** (`GraphIsoChecks/Giant.lean`): Kernel-checked examples (`decide`), each against brute force in the same
   term:
   - the `k`-subsets;
   - the case decision and the orbit partition for four groups on `[4]`;
   - one full-group step (control flow only, since `K(A)` is trivial for `k ≤ 2`);
   - `case1Prog` in `S₃` and `A₃`, with isomorphic and non-isomorphic pairs;
   - `augProg`;
   - `case2aProg` in `S₃`, which aligns `Φ` and then runs the pullback.

   Supplementary interpreter runs:
   - `fullProg` with `k = 3` in `S₆`, where 4 of the 20 sets pass and `F = Sym{0,1,2,3}`, equal
     to the brute-force group;
   - `case2aProg` in `S₅`;
   - the case decision on `[6]`.

   `fullProg` with `k = 5` needs `m ≥ 10`, which means 252 certificates, each running the
   solver, so it is not checked. The program runs for any `k` with `k + 2 ≤ m`; only the
   thresholds of the spec need `5 ≤ k`.

**Validation.** `lake build --wfail` succeeds with mathlib prebuilt. No Lean line exceeds 100
characters, and the sources contain no `sorry`, `admit`, `native_decide`, `noncomputable`,
axiom or option override. Size: about 4,000 lines of library code and 320 lines of
checks.

**What is not covered.** Case 2b (14h), Case 3 (14i), and the composition of M5 with its cost
in the main recursion (14j).

## Milestone 14, stage 14f: structures on the base and Align (`PLAN-14.md` §10)

Babai's procedure Align, in `GraphIso/Align/`: canonical structures on the base `Fin m`, their
stabilizers and isomorphisms, and the alignment of `x`'s structure with `y`'s.

1. **Trimmed Johnson embeddings** (`Trim.lean`). `trimJ` keeps `f` only on `V₀`.
   - It commutes with the action and keeps `IsJohnson` (`trimJ_smul`, `isJohnson_trimJ`).
   - Trimming the leaves keeps `soj` canonical (`trim_canonical`).
   - Every Johnson leaf of `soj` has cells disjoint from `V₀` (`soj_johnson_disjoint`,
     unconditionally). For `bsoj` this holds when the input cells are disjoint from `V₁`
     (`bsoj_johnson_disjoint`, an invariant of the recursion). Without that hypothesis it
     fails: round 1 exhibited a valid Johnson leaf whose cells overlap `V₀`.
2. **The interface** (`Interface.lean`). A `StructOps` gives a decoding, stabilizer generators
   and an isomorphism search. Its `Spec` requires:
   - the generators to generate exactly the stabilizer in `Sym(Fin m)`;
   - the search to return an isomorphism, or none exactly when none exists.
3. **The three kinds of structure.**
   - **Colored partitions** (`PartOps.lean`, `partOps_spec`):
     - generators: transpositions inside blocks, and exchanges of blocks of one colour
       (`partGens_closure`);
     - isomorphism: a greedy matching of blocks by colour and size.
   - **Sets** (`SetOps.lean`, `setOps_spec`): reduced to two-block colored partitions.
   - **Trimmed Johnson embeddings** (`JohnOps.lean`, `johnOps_spec`):
     - generators: transpositions inside cells and among the remaining points, and swaps of
       equal-size cells together with the permutation they induce on `V₀`
       (`johnGensD_closure`);
     - isomorphism: matching by profile.
     - The data invariant `JValid` follows from `IsJohnson` together with `JShape`
       (`jvalid_of_isJohnson`). `JShape` collects the representation conditions:
       duplicate-free lists in range, cells pairwise disjoint and disjoint from `V₀`, and
       trimmed data. `IsJohnson` alone does not imply them (round 1, F1).
   - All six programs have polynomial costs.
4. **Align** (`AlignProg.lean`).
   - Membership in `P = ψ(G)` uses the backend's `mem` on `P` generated at the base degree.
   - `Stab(X) ∩ P` comes from Schreier generators of index at most 2 (`closure_stabInPL`).
   - Isomorphisms inside `P` are corrected for parity (`isoInPL_spec`).
   - The preimage `ψ⁻¹(L)` is built from lifts and the backend's kernel (`closure_lifts_ker`,
     `RunsWithin.preProg`).
   - `alignProg` lifts an isomorphism for each structure of `y`, calls the sub-solver in its
     coset of `G₁ = ψ⁻¹(Stab(X(x)) ∩ P)`, and combines the answers.
     - Its answer is correct for `G` (`RunsWithin.alignProg`), given that every isomorphism
       carries `X(x)` to one of the listed structures. That hypothesis is supplied by
       `iso_reach` for canonical trees.
     - `iso_eq_iUnion_isoTo` is the decomposition.
5. **Checks** (`GraphIsoChecks/Align.lean`): Six kernel-checked examples (`decide`), each comparing a program with
   the data function and with brute force in the same term:
   - sets in `[4]`;
   - colored partitions in `[4]`: exact stabilizers, an isomorphic pair and a non-isomorphic
     pair;
   - a trimmed Johnson embedding with `m = 4`;
   - `Stab ∩ P` and isomorphisms inside `P` for `Alt(4)` and `Sym(4)`, including `none` when
     the only isomorphism is odd;
   - `alignProg` in `S₃` and in `A₃` (with a parity correction), with the Schreier–Sims backend
     and milestone 1's solver as the sub-solver, equal to the brute-force isomorphism coset.

   Six supplementary interpreter runs on larger fixtures:
   - sets in `[5]`, partitions in `[5]` and `[6]`, including `S₂ ≀ S₃`;
   - Johnson embeddings with stabilizers of order 16, checked against brute force over
     `Sym(8)`, and of order 24, checked by stabilization only;
   - parity in `Alt(5)` and `Sym(5)`;
   - `alignProg` with a non-isomorphic pair and an unreachable extra candidate.

**Validation.** `lake build --wfail` succeeds with mathlib prebuilt. No Lean line exceeds 100
characters, and the sources contain no `sorry`, `admit`, `native_decide`, `noncomputable`,
axiom or option override. Size: about 7,400 lines of library code and 340 lines of
checks.

**What is not covered.** The structures' origins (the Split-or-Johnson leaves of Case 2b and
Case 3, the set `Φ` of Case 2a) and the derived hints after Align are later stages (14g–14j).

## Milestone 14, stage 14e: local certificates as programs (`PLAN-14.md` §9)

Milestone 13's local certificates and their comparison, as programs in `GraphIso/CertProg/`,
for the giant macro-step M5.
- The programs call the backend, with the backend charges bounded through `BackendBounds` or
  stated as explicit hypotheses.
- Every recursive call goes through a sub-solver parameter `sub`, as `seqProg` and
  `branchProg` take one. The specs assume `SubSolves` for windows of at most `n / k` points
  inside the current group (`StepSubP`).

1. **The paired beard** (`PairBeard.lean`, model level). `pairCoset φ A A' x x' i` is the coset
   of elements mapping `A` to `A'`, the windows of `x` at `A` onto those of `x'` at `A'` and `x`
   to `x'` on the `i`-th window.
   - For `x' = x` and `A' = A` it is the beard's group (`pairCoset_self`).
   - It is a left coset of that group (`pairCoset_eq_smul`).
   - Its elements conjugate the two beards (`beardG_conj`, `beardW_succ_conj`), so one beard
     computation suffices.
   - Each step is a string-isomorphism coset on the next window (`pairCoset_succ`).
   - `CertIso` holds exactly when the final coset maps the tuple `T` to `T'` (`certIso_iff`).
     The proof uses canonicity and the locality of the beard (`pb_beard_congr`).
2. **The setting** (`Setting.lean`).
   - The group is faithful on the string positions `[0, n)`.
   - Milestone 13's `φ` is any representation of the restricted group agreeing with the base
     action (`IsPhi`, which exists by `exists_phi`). It is not a definition, because its
     inverse isomorphism is not computable.
   - `toStab` transports subgroups of `G` to subgroups of `G_A`.
3. **Test sets** (`TestSets.lean`).
   - `G_A` comes from the toolkit's giant set stabilizer. An element mapping `T` to `T'`
     pointwise comes from an even permutation and a lift (`moveD_spec`, `RunsWithin.moveProg`).
   - The giant test of `ψ_A(H)` runs on degree `k` (`giantAModel_iff`).
4. **Affected points** (`Affected.lean`): equal to milestone 13's `aff` (`RunsWithin.affProg`).
5. **The kernel** (`Kernel.lean`). `N = H ∩ ker ψ_A` has at most `k!` coset representatives
   (`pointStabs_reps_le_factorial`; the toolkit's spec gave only `(N - n)^k`). Its orbits on the
   affected points have at most `n / k` points (`kerOrbit_length_le`, from `kernel_orbit`).
6. **The beard step and the loop** (`Step.lean`, `Cert.lean`).
   - The step does three things:
     - it branches over the kernel's cosets;
     - inside each branch, it processes the kernel's orbits on the affected points
       sequentially, calling `sub`;
     - it computes the next paired coset (`RunsWithin.beardStepProg`).
   - `pairLoopProg` runs at most `n` rounds, as a fold with a stop flag, which
     `pairCoset_stable` justifies. Its result represents the final paired coset (none exactly
     when it is empty) and lists the final window (`RunsWithin.pairLoopProg`).
7. **The certificate and the comparison** (`CertIso.lean`).
   - `certProg` returns `W(A)`, `H(A)`, `K(A)` and the fullness test. These equal milestone 13's
     `beardW`, `beardH` and `certK`, and `IsGiantOn φ A (certK …)` (`RunsWithin.certProg`).
   - `certIsoProg` decides `CertIso` (`RunsWithin.certIsoProg`), through the paired beard from
     `(τ, G_A)` and a tuple transporter (`Transporter.lean`, `RunsWithin.tupleTransProg`).
   - `G_A`'s generator count is proved from `BackendBounds` (`stabSet_gens_le`).
   - Costs are polynomial × `k!`, plus at most `n · k! · n` sub-calls of cost `Cb`
     (`certCost_le`, `certIsoCost_le`). The kernel's cost uses factorial bounds on the
     intermediate representative lists (`cp_ps_run`). Round 1 found that the toolkit's bound
     `m^k` remained there (finding F3).
   - The sub-solver hypothesis bounds the input generators (`StepSubP`'s `sIn`). Round 1 found
     this missing (F1).
   - The returned groups are exactly the preimages of milestone 13's `H(A)` and `K(A)`
     (`Denotes`). Round 1 found only a projection exported (F2).
8. **Checks** (`GraphIsoChecks/CertProg.lean`). Ten kernel-checked examples (`decide`) compare
   each program with a brute-force value computed in the same term. The fixture is `S₃` and
   `A₃` on `[3]` with a base of three points, using the Schreier–Sims backend and milestone 1's
   solver as the sub-solver:
   - `stabSetProg`, `moveProg`, `giantAProg`, `affProg`, `kerAProg` with `kerOrbitsProg`,
     `tupleTransProg`;
   - `beardStepProg` and `pairLoopProg` with `k = 3`;
   - `certProg` and `certIsoProg` with `k = 1`, which checks control flow only, since
     `k + 2 ≤ m` leaves only `k = 1` there.

   Round 1 found the checks were `#eval` only (finding F4). The 14 interpreter runs below are
   kept as supplementary checks. They run the Schreier–Sims backend with milestone 1's solver
   as the sub-solver (`.recur` of the solver), each compared with brute force over every group
   element:
   - fixtures: `S₅` and `A₅` on the ten pairs of `[5]` (graphs, `k = 3`), `S₅` and `A₅` on `[5]`
     (colourings, `k = 3`), and `S₇` on `[7]` with `k = 5`;
   - `G_A`, the move `τ`, the giant test, the affected points, the kernel (at most `k!`
     representatives, a cover) and its orbits (`k · |o| ≤ n` for `k = 5`), the tuple
     transporter;
   - the beard step and the paired loop for `x' ≠ x`: the final coset is nonempty for a
     relabelled graph and empty against `C₅`;
   - the certificate (`W(A)`, `H(A)`, `K(A)`, fullness) on graphs and colourings with and
     without a full test set, and `CertIso`, true and false cases.

   Whole certificates are checked with `k = 3`. With `k = 5` one certificate takes about 40 s
   (120 kernel cosets, each running the solver), so `k = 5` is checked through `G_A`, the
   affected points and the kernel. The programs do not depend on `k ≥ 5`; only the window
   bound of the sub-calls does. `S₇` on the 21 pairs is too slow for a check (one beard step
   takes minutes).

**Validation.** `lake build --wfail` succeeds with mathlib prebuilt. No Lean line exceeds 100
characters, and the sources contain no `sorry`, `admit`, `native_decide`, `noncomputable`,
axiom or option override. Size: about 5,000 lines of library code and 420 lines of
checks.

**What is not covered.** Aggregation (Cases 1–3, the pullback), the colouring of `k`-tuples by
certificate equivalence with Weisfeiler–Leman and the Design Lemma, and Align are stages
14f–14i. The certificates' sub-solver is instantiated by the main recursion in stage 14j.

## Milestone 14, stage 14d: Split-or-Johnson trees and leaf stabilizers (`PLAN-14.md` §8)

Whole Split-or-Johnson trees and leaf stabilizers, in `GraphIso/SoJTree/`.
- The tree programs make no backend calls and no `.recur` call; `.recur` is reserved for the
  main recursion. They are `.loop`s over a stack of frames.
- The leaf stabilizer calls the backend through the group signature, with the backend charges
  as explicit hypotheses, as `blockStabProg` does.

1. **Leaf multisets and sizes** (`Measure.lean`).
   - `CTree.leafMs` is the multiset of the leaves of all paths. Its cardinality is the count,
     and its elements are the reachable leaves.
   - `CTree.size` counts vertices and edges. A live tree has size at most
     `2 (height + 1) · count`.
   - `bsoj` has height at most `2 |V₂| + 1`, and `soj` at most `2 |Γ| + 2`.
   - **The M4 index bound** (`card_orbit_le_count`): if a group preserves the colouring, the
     orbit of a reachable leaf of `soj` has at most `count` elements.
2. **Leaf data** (`LeafData.lean`, `LeafProg.lean`). Leaves of `Option (Out (Fin m))` are data
   decoded through stage 14c's `cpartOf` and `jembOf`. Programs compute `addPieceOut`,
   `extendOut`, equality of decoded leaves (`outEqD_iff`), and a permutation acting on leaves
   (`decodeOut_actOutD`). The equality compares the total functions at every point of `Fin m`.
3. **One frame** (`Frame.lean`). A frame is a pending call of `bsoj` with the pieces and the
   extension to apply to its leaves.
   - `stepD` runs one level on data: `bstep`, `dlCont` with the `cohSoj` level on the numbered
     points and cells, `cohCont`, and the guards.
   - The frame tree's `leafMs` is the produced leaves plus the children's (`stepD_leafMs`), and
     the step's work plus the children's sizes is at most the frame tree's size
     (`stepD_size`).
   - Two model lemmas carry this:
     - `bsoj_congr`: `bsoj` reads its relation only on its cells, up to unreachable branches
       (`TEq`, which preserves `leafMs` and `size`);
     - `cohSoj_agree`: `cohSoj` is natural along injective maps.
   - The `sojAt` frames therefore equal the model's subtrees up to `TEq` (`sojAtD_frame`).
4. **The step program** (`StepProg.lean`) computes `stepD` at cost at most
   `stepK m q t · (1 + work + produced leaves)`.
   - `stepK` is an explicit polynomial in `m + q + t` of degree 192 (crude, from stacked
     bounds).
   - The invariant `ValidP` (at most `2t` points, at most `q` cells, bounded wrappers) is
     preserved by the children.
5. **The worklist** (`Worklist.lean`). A generic `.loop` over a stack of frames, with the
   multiset of its outputs (`worklistD_ms`). Its cost is at most
   `(K + 11) · Σ (rank + 2) · size + 7`, where `K` bounds a step's cost per unit of work.
6. **The tree programs** (`Trees.lean`): `bsojProg`, `sojAtProg` and `sojProg`. Round 1 found
   that `sojAtProg` only initialized its frames (finding F1). It now enumerates the whole tree.
   - Their outputs decode to exactly the model's `leafMs` (`bsojProg_leafMs`, `sojProg_leafMs`).
     So the length is the count, and the elements are the reachable leaves.
   - Their costs are a polynomial times the size.
   - Every leaf they output has data size at most `m² + m + q + 1` (`sojProg_outSize`). This
     bounds the leaf stabilizer's cost (round 1, F2).
   - Under the hypotheses of `bipartite_split_or_johnson` and `split_or_johnson`, the closed
     bounds are a polynomial in `m` times `2^{128 (⌈log₂ t⌉ + 2)²}` and
     `2^{129 (⌈log₂ m⌉ + 2)²}` (`bsojProg_cost_le`, `sojProg_cost_le`).
7. **Orbits and stabilizers.**
   - `OrbitClosure.lean`: a generic orbit enumeration of a structure under permutation
     generators. It returns the orbit without repetition and each generator's index map
     (`orbitD_spec`), and its length is the orbit's size (`orbitD_length_eq`).
   - `OrbitStab.lean`: the generic stabilizer of a point of a finite G-set given by index maps.
     The generators are extended to degree `N + r`, the backend's stabilizer and transversal
     are taken, and the result is truncated (`RunsWithin.orbitStabProg`).
   - `LeafStab.lean`: the leaf stabilizer `{g ∈ G | ψ(g) • o = o}`, with at most `r`
     representatives forming an `IsLeftCover` (`RunsWithin.leafStabProg`). If `ψ(G)` preserves
     the colouring and `o` is reachable in `soj`, then `r ≤ count`
     (`leafStab_index_le_count`).
   - `LeafBound.lean` gives macro-step M4's bound for a leaf output by `sojProg`
     (`RunsWithin.leafStabProg_sojLeaf`): `1000 (N + k + |gs| + r + outB + 2)⁸`, plus terms in
     the backend's output lengths and the four charges, with `r ≤ count`.
8. **Checks** (`GraphIsoChecks/SoJTree.lean`): 38 checks (each `#eval` throws on a failure):
   - leaf data: equality, the permutation action, pieces and extensions, against the model on
     decoded leaves;
   - frame steps against the model (`stepD_leafMs`'s multiset equation and `stepD_size`'s
     inequality) on the twin partition, the Johnson leaf of `J(5, 2)`, the base case (24
     leaves), large twin classes, and the Design Lemma node with arity 1;
   - the `cohSoj` level on data only (a `cohSoj` node, the partition into components, and a
     bipartite leaf whose `cohCont` gives a child frame), with the children's steps against the
     model;
   - whole trees: the worklist on data against the model's `leafMs` and count for `bsoj` and
     for `soj` (Petersen, `K₅`, two random colourings);
   - interpreter runs of `bsojProg`, `sojAtProg`, `sojProg` and `stepProg` against the data
     models and the model, with `outSize ≤ outB` for every output leaf;
   - direct continuation coverage: hand-built inputs to the continuations take every branch of
     `dlCont` and `cohCont`, `allSmall` included. Each is checked in the interpreter, on the data
     model, and against the model's `dlCont` and `cohCont`. Round 1 found `allSmall` unexercised
     (finding F3). This is local coverage; a whole valid frame need not reach these branches;
   - leaf orbits and `leafStabProg` with the Schreier–Sims backend against brute force
     (stabilizer orders 12, 2, 24, 120), the cover, and the M4 index bound.

   Not compared with the model:
   - The `cohSoj` level is checked on data only. Milestone 11's `wlOn` and `cohOn` rerun
     Weisfeiler–Leman at every evaluation, so a Design Lemma node with arity 2 does not finish
     in five minutes.
   - Through whole valid frames, four branches are argued unreachable on small inputs in the
     checks' docstring: the empty `C₁`, the constant rectangle, a small `W`, and the shrink
     guard. The shrink guard always passes. `allSmall` is neither reached nor excluded through
     whole frames; the direct fixtures cover all five locally.

**Validation.** `lake build --wfail` succeeds with mathlib prebuilt. No Lean line exceeds 100
characters, and the sources contain no `sorry`, `admit`, `native_decide`, `noncomputable`,
axiom or option override. Size: about 13,000 lines of library code and 810 lines of
checks.

**What is not covered.** The trees are not yet used by macro-steps; M4's composition (the
degree of transitivity, individualization, the orbital configuration, `sojProg`, the leaf
stabilizer and the coarsening of the leaf into a hint) is stage 14j. The bound `stepK` is
crude.

## Milestone 14, stage 14c: Split-or-Johnson programs I (`PLAN-14.md` §7)

Programs for one level of milestone 11's Split-or-Johnson, in `GraphIso/SoJProg/`.
- No program calls the backend. Each has a data model, an explicit polynomial cost and a
  `RunsWithin` spec.
- Each data model is proved equal, after decoding, to the milestone 11 function it implements.
- The data are lists of indices for sets and cells, `m × m` arrays for colourings of pairs, and
  Boolean arrays for bipartite relations (`Data.lean`).

1. **Step 1, twins and degrees** (`Twins.lean`): degrees, twin classes, the points without
   twins of each degree, the large degrees, and the twin partition.
2. **Step 2, the Johnson test** (`Johnson.lean`): complemented neighbourhoods, binomial
   coefficients by Pascal's rows, the test, and the Johnson leaf.
3. **Step 0, the base case** (`BaseCase.lean`): all orderings of the cells, equal to `enums`.
   The cost is `k!` times a polynomial, which the base case's size bound `k² ≤ 27 L³` keeps
   small. Then the neighbourhood codes and the colored partition.
4. **Step 3, the `d`-ary structure** (`Dary.lean`, `WLSets.lean`):
   - `Nat.clog` and the arity;
   - the colouring `daryCol`;
   - twins by swap invariance, `bigTwins` and `pickSide`;
   - Weisfeiler–Leman on sets: milestone 10's `wlA` along a bijection computes `wlOn`, on the
     cells and on `V₁' ⊔ V₂` (`cohOn`).
5. **The Design Lemma test** (`DLTest.lean`): milestone 10's `goodA` decides milestone 11's
   `DLGood`, the good lists equal the filtered `tuplesLt`, and the pieces of `dlCont` are
   covered (class sizes, dominant classes, the constancy test, `selThird`).
6. **One level of Coherent Split-or-Johnson** (`Coherent.lean`): the data tree decodes to
   milestone 11's `cohSoj` exactly, at cost at most `903 (N + 1)⁷`. The edges of a bipartite
   leaf are computed by a costed query and a materialized relation array, both equal to
   `bipEdge` (`bipEdgeD_eq`, `relOf_bipRelD`). Round 1 found these missing (finding F1).
7. **Checks** (`GraphIsoChecks/SoJProg.lean`): 41 comparisons with the model:
   - `J(5, 2)`, `J(6, 3)` and a non-Johnson example;
   - the base case and the arity;
   - `bigTwins` and `pickSide`;
   - small Weisfeiler–Leman runs;
   - the Design Lemma test and `selThird`;
   - one level of Coherent Split-or-Johnson reaching every branch, with the leaf kinds and the
     bipartite relations compared. The fixtures are certified coherent: the `J(5, 2)` incidence
     configuration with `C₂` a clique and with `C₂` the Petersen configuration (bipartite
     leaves), pentagon configurations, `J(6, 2) ⊔ ([6] × {0, 1})` (the contraction), a constant
     colouring, and two copies of the Clebsch configuration. A non-coherent input is kept
     deliberately. Round 1 found the bipartite leaves and the Clebsch comparison missing
     (finding F2);
   - `bipRelProg` against `bipEdge`.

   Three fixtures compare the data model `cohSojD`, which `RunsWithin.cohSojProg` proves equal
   to the program's result, because an interpreter run on them takes minutes. Helfgott's
   `|C₁| > |C₂|` holds for `J(6, 2) ⊔ ([6] × {0, 1})` but not for the Petersen and doubled
   Clebsch fixtures; their outputs are still checked against `cohSoj`.

   Two values are also checked by the kernel.

**Validation.** `lake build --wfail` succeeds with mathlib prebuilt. No Lean line exceeds 100
characters, and the sources contain no `sorry`, `admit`, `native_decide`, `noncomputable`,
axiom or option override. Size: about 7,400 lines of library code and 580 lines of
checks.

**What is not covered.** The steps are not yet chained into the trees `bsoj`, `sojAt` and
`soj`; that is stage 14d. Stage 14d also numbers `α ⊕ Finset α` (points, then cells) for
`cohSoj`, applies `dlCont`'s and `cohCont`'s continuations, enumerates the leaves, and computes
leaf stabilizers. The `d`-ary costs contain `v^d`, which is polynomial because the arity
satisfies `v^d ≤ 64 t¹²` (milestone 11's `pow_arity_le`).

## Milestone 14, stage 14b: the group toolkit (`PLAN-14.md` §6)

Costed programs for the macro-steps of the recursion, in `GraphIso/Toolkit/`.
- Each has a well-formedness lemma, a model, an explicit cost, and a `RunsWithin` spec for any
  oracle meeting the contract on the operations it calls, with the backend charges as
  hypotheses.
- Hinted instances live on extended degrees `N = n + m`: the strings and windows lie on
  `[0, n)`, and the base on `[n, N)`. So the backend's orbits, stabilizers, kernels and lifts
  on base positions compute the base action's orbits, the preimages of its stabilizers,
  `ker ψ` and lifts.

1. **Hints as data** (`Base.lean`). Valid label data denotes stage 14a's `IsHint` for the
   generated group (`HintValid.isHint`). Valid data consists of duplicate-free lists that are
   equivariant on the generators and not constant. Duplicate-freeness is the representation
   invariant the label programs need (round 1, F2).
2. **Re-basing** (`Extend.lean`).
   - `rebaseProg` moves a hinted group onto a new base given by blocks of the old one (a block
     system for M2a, or Johnson cells for the Johnson union). It extends by the induced action,
     drops the old base, and generates at degree `n + k`.
   - When the old group acts faithfully on the string positions, `rebase_iso` gives an
     isomorphism agreeing on the string positions and inducing the block action. Faithfulness
     is inherited (`rebase_faithful`).
3. **Label programs** (`Labels.lean`): the coarsenings of stage 14a on data (intersection,
   block label, equidistribution, Johnson union, complement). Each is linked to its 14a
   definition on duplicate-free lists. Costs are polynomial, `O(k t + m)`: persistent arrays
   copy on update, so counting is not linear in this cost model. The plan's criterion was
   revised accordingly (round 1, F4).
4. **Transitivity and blocks of the base** (`Transitivity.lean`, `BaseBlocks.lean`):
   - the degree of transitivity, capped (`degreeModel_spec`);
   - the giant test (`giantModel_iff`, through `alt_le_iff`);
   - the maximal blocks of the base, giving either a primitive action or an `IsBlockSys`
     (`baseBlocks_spec`).
5. **Reductions** (`Reduce.lean`, `BlockStab.lean`). Charges are bounded as in
   `BackendBounds`, so the Schreier–Sims backend can discharge them; round 1 found unbounded
   charge hypotheses (F1). The reductions are:
   - `ker ψ` with a transversal of length `|ψ(G)|`;
   - pointwise stabilizers of base points with a left cover by at most `m^r` representatives;
   - the setwise stabilizer of one block (M2b) with a left cover by at most `k` representatives;
   - lifts;
   - for a giant base action, setwise stabilizers of sets of base points (generators only).
6. **Orbital configurations** (`Orbital.lean`):
   - the array of orbital indices, whose spec is the hypothesis of `orbital_uniprimitive`;
   - the colouring by one orbital, which feeds `wlRel` (`arrRel_orbital`).
7. **Checks** (`GraphIsoChecks/Toolkit.lean`): interpreter runs over the Schreier–Sims
   backend:
   - degrees of transitivity and giant tests for `Sym(5)`, `Alt(5)` and `D₅`;
   - primitivity of the bases;
   - the Petersen orbital configuration;
   - a trivial kernel with `120` representatives;
   - the Johnson labels' generator condition;
   - a re-basing.

**Validation.** `lake build --wfail` succeeds with mathlib prebuilt. No Lean line exceeds 100
characters, and the sources contain no `sorry`, `admit`, `native_decide`, `noncomputable`,
axiom or option override. `Classical.choose` appears only inside proofs
(`Toolkit/BaseBlocks.lean`), never in a definition or in program-returned data. Size: about
5,200 lines of library code and 120 lines of checks.

**What is not covered.** The toolkit's programs are not yet composed into macro-steps; that is
stages 14d–14f. Answers on a re-based degree are carried back to the old degree through `θ`
(computable by `lift` on the string positions), which is also a later stage's (`PLAN-14.md` §4). Split-or-Johnson
programs and leaf stabilizers are stage 14c.

## Milestone 14, stage 14a: the recursion's mathematics (`PLAN-14.md`)

`PLAN-14.md` specifies Babai's main recursion on the CFSG-free route, the six stages that will
formalize it, and its cost analysis. Neither source gives a recursion that can be formalized as
it stands:
- Babai relies on the Main Structure Theorem (standard blocks, through Jordan–Liebeck) and only
  outlines the replacement of Cameron's theorem (§13.1);
- Helfgott carries towers of block systems and leaves the CFSG-free branch to a remark.

The plan instead uses **labelled hints**. An instance may carry a base `Γ`, a representation
`ψ : G → Sym(Γ)`, and labels `lab : W → 2^Γ` that are equivariant and not constant on the
window. Each macro-step reduces the group and coarsens the hint:
- M1 to an orbit of the base;
- M2 to a block system or one block;
- M4 and Align through the Johnson union to the point set `Λ` of a Johnson scheme.

The cost is charged to the potential `pot Q b n m = n² (m + 1) Q^{b (κ(m) + 4 (λ(n) + 6)²)}`,
which gives `exp(O((log n)⁸))` overall. Correctness will not depend on the interfaces; only the
cost will.

Stage 14a proves the mathematics the macro-steps use, in `GraphIso/Recursion/`, before any
program is written:
1. **Hints** (`Hint.lean`): fibres are blocks of at most `|W|/2` points under transitivity, so
   constant labels mean a small set (`card_le_of_const`); hints restrict to subgroups and
   subwindows. The recursion keeps the invariant that a hinted instance is transitive on its
   window: after a reduction each orbit keeps the hint or has at most half of the window
   (`orbit_child`). Without transitivity the half-window bound fails; this was round 1's
   finding F1.
2. **Coarsenings** (`Coarsen.lean`). Each is equivariant and not constant:
   - invariant subsets (`hint_inter`, `exists_nonConst_inter`);
   - block labels (`hint_blockLabel`, with `|Ψ| ≤ |Γ|/2` and labels not growing);
   - the block stabilizer (`hint_blockStab`);
   - the Johnson union (`hint_jUnion`), with its fallback `fix_of_jUnion_const`, and
     `|Λ|(|Λ| − 1) ≤ 2|V₀|`.
3. **Primitive quotients** (`Primitive.lean`):
   - the giant test `alt_le_iff`;
   - giants are transitive on subsets of each size;
   - block stabilizers are transitive on their block;
   - the orbital configuration of a primitive, not doubly transitive group satisfies the
     hypotheses of `split_or_johnson` (`orbital_uniprimitive`);
   - for Case 2b, where the group depends on the string and isomorphisms may permute numbered
     orbitals (round 1, F2), one orbital is chosen and refined by 2-ary Weisfeiler–Leman
     (`wlRel`). The refinement is natural with its colour names, coherent, homogeneous, not a
     clique and invariant, and it is uniprimitive for primitive groups (`wlRel_natural`,
     `wlRel_spec`, `wlRel_uniprimitive`). The step branches on the configuration
     (`wlRel_split_or_uniprimitive`): a disconnected colour gives a colored partition by its
     components, and otherwise the refinement is uniprimitive. Branching on the action instead
     fails, since an imprimitive action can give a primitive refinement (round 2, F3).
4. **Progress** (`Progress.lean`): orbits under a colored `t`-partition (`colPart_orbit`) and
   under a Johnson structure (`johnson_orbit`).
5. **Coset decompositions** (`Align.lean`):
   - canonical structures are transported by isomorphisms;
   - Babai's alignment (`iso_eq_align`);
   - choice-tree leaves (`iso_reach`);
   - the index of a leaf stabilizer for a group-invariant tree is at most the count
     (`index_stab_le_count`).
6. **The pullback of Case 2a** (`Pullback.lean`):
   - `H = K F ∪ τ K F` when `Alt(Φ) ≤ r(F)` (`cover_of_alt_le`);
   - the solutions and automorphisms of `H` from those of `K` and `τ K` (`iso_pullback`,
     `aut_pullback`);
   - orbits fixing more than half of a giant base pointwise have at most half of the window
     (`card_orbit_le_half`, via `2 C(a, j) ≤ C(m, t)`).
7. **The potential** (`Potential.lean`):
   - a macro-step with branching at most `Q²` (`pot_step`) or none (`pot_free`) is paid for;
   - the closed form `pot0_le`;
   - the label invariant (`s_le_lam`, `johnson_step_label`): labels stay polylogarithmic, so the
     Johnson fallback costs at most a polylogarithmic factorial.
8. **Checks** (`GraphIsoChecks/Recursion.lean`): a concrete hint (`Sym(4)` on pairs), a
   kernel-computed block label, and kernel-checked ranges of `κ`'s drop and of the binomial
   count; the step inequality on a concrete macro-step.

**Validation.** `lake build --wfail` succeeds with mathlib prebuilt. No Lean line exceeds 100
characters, and the sources contain no `sorry`, `admit`, `native_decide`, `noncomputable`,
`Classical.choose`, axiom or option override. Size: about 2,000 lines of library code and 60 lines
of checks.

**What is not covered.** There are no programs yet. Stages 14b–14j (`PLAN-14.md` §4, since
restaged) implement the toolkit, Split-or-Johnson, the certificates, Align, the aggregation and
the main recursion; they also prove that the macro-steps compose into the recursion and that
their costs satisfy `pot_step` and `pot_free`. The assembly of the progress lemmas into derived
hints (choosing the orbit, then the block coarsening or the Johnson union) belongs to the main
recursion, stage 14j. The Main
Structure Theorem and the Jordan–Liebeck theorem are not used.

## Milestone 13: local certificates and their aggregation (`PLAN-13.md`)

Babai's method of local certificates (Babai §10.1; Helfgott §6.1) and their aggregation
(Helfgott §6.2), as mathematics, against milestone 12's interfaces `AltQuotientIso K` and
`TransitivityBound T`. The certificates are defined from the group `G ≤ Sym(Ω)`, a
representation `φ : G → Sym(Γ)` and the string `x`; computing them calls string isomorphism
recursively on windows of size at most `|Ω|/k`, and that computation, its programs and its cost
belong to the main recursion (milestone 14).

1. **The beard** (`Certificates/Basic.lean`, `Certificates/Beard.lean`; Babai's procedure
   LocalCertificates). For a test set `A ⊆ Γ`, `G_A` is its setwise stabilizer and
   `ψ_A : G_A → Sym(A)` the restriction. The windows `W_i ⊆ Ω` and groups `H_i ≤ G_A` are a
   function of the step number (`beard`): `W₀ = ∅`, `H₀ = G_A`; while `ψ_A(H_i)` is a giant,
   `W_{i+1} = W_i ∪ Aff(H_i)` and `H_{i+1} = Aut^{W_{i+1}}_{H_i}(x)`. Windows are sets and groups
   are subgroups, so the iteration needs no decidability. Proved: it is constant from step
   `|Ω|` on (`beard_stable`); `W_i` is `H_i`-invariant and preserved with `x` (`beardH_le_autW`);
   `Aut_{G_A}(x) ≤ H_i` (`autW_univ_le_beard`); the final group is the window group
   `H(A) = Aut^{W(A)}_{G_A}(x)` (`beardH_eq_autW`), which Babai's "Recompute `H(W)`" and Case 3
   use; and a giant `H(A)` affects only points of `W(A)` (`aff_subset_beardW`).
2. **Local certificates** (`Certificates/Local.lean`; Babai Thm. 10.1.3, Claims 10.1.6–10.1.7).
   The hypotheses are milestone 12's, collected in `Thresholds K |Ω| |A|`: `AltQuotientIso K`,
   `K` monotone, `5 ≤ |A|`, `K |Ω| ≤ |A|`, `|Ω| < |A|!/2`.
   - `cert_full`: if `ψ_A(H(A))` is a giant, `K(A) = H(A)_(Ω \ W(A))` consists of automorphisms
     of `x` and `ψ_A(K(A)) ≥ Alt(A)` (through the Unaffected Stabilizer Theorem);
   - `cert_not_full`: otherwise `M(A) = ψ_A(H(A))` is not a giant and contains
     `ψ_A(Aut_{G_A}(x))`;
   - `isFull_iff`: `A` is full exactly when `ψ_A(H(A))` is a giant;
   - `kernel_orbit`: for `ψ_A(H_i)` a giant and `u ∈ Aff(H_i)`,
     `|A| · |u^{H_i ∩ ker ψ_A}| ≤ |u^{H_i}|` (the Affected Orbit Lemma), so the kernel's orbits
     on the new window have at most `|Ω|/|A|` points.
3. **Canonicity** (`Certificates/Relabel.lean`; Prop. 10.1.8 (v)): for `σ ∈ G`, the beard of
   `(σ • x, φ(σ) • A)` has the windows moved by `σ` and the groups conjugated by `σ`
   (`beard_relabel`); giant-ness, fullness and `K(A)` follow (`isGiantOn_relabel`,
   `isFull_relabel`, `certK_relabel`), and `M(A)` is conjugated by the bijection
   `A → φ(σ) • A` (`certM_relabel`).
4. **Aggregation** (`Certificates/Cases.lean`, `Certificates/Aggregate.lean`; Helfgott §6.2).
   `F(x)` is generated by the `K(A)` with `|A| = k` and `ψ_A(H(A))` a giant, and `S` is the
   support of `φ(F)`. `F(x) ≤ Aut_G(x)` (`fullGroup_le_autG`), and `F`, `S` are canonical
   (`fullGroup_relabel`, `supp_conj`).
   - Case 1 (`orbitPart_valid`): the orbit colouring is a colored `⌊m/2⌋`-partition when the
     moved points are at least half of `Γ` and no orbit has more than half.
   - Case 2: the large orbit is unique (`large_orbit_unique`). Case 2b: a transitive group not
     containing `Alt(Φ)` has a degree of transitivity `d`, with `1 ≤ d`, `d + 2 ≤ |Φ|` and
     `d ≤ T |Φ|` under `TransitivityBound T` (`exists_degree`); fixing `d − 1` points leaves a
     transitive, not doubly transitive action (`fixing_transitive_not_two`), whose orbital
     configuration is a homogeneous classical coherent configuration that is not a clique
     (`orbital_config`): the input of Split-or-Johnson.
   - Case 3 (`no_large_twins`): colouring the `k`-tuples of `Γ \ S` by the equivalence of
     certificates leaves no `k` pairwise twins — a twin set would make some `k`-set `T` full
     (through `beardH_eq_autW`: its window group induces every transposition of `T`), so `F`
     would move `T`.
5. **Checks** (`GraphIsoChecks/Certificates.lean`): the beard's first and stable steps;
   `Thresholds` is inhabited at the witness interface `K n = n + 1` (`thresholds_succ`), and the
   principal theorems are instantiated there, where they are vacuous for giant representations;
   `exists_degree` is instantiated at the witness `T k = k`.

**Validation.** `lake build --wfail` succeeds with mathlib prebuilt. No Lean line exceeds 100
characters, and the sources contain no `sorry`, `admit`, `native_decide`, `noncomputable`,
`Classical.choose`, axiom or option override. Size: about 1,220 lines of library code and 80
lines of checks.

**What is not covered.** The certificates are not computed here: Babai's "Recompute `H(W)`"
(string isomorphism on the windows, by strong Luks reduction), the comparison of certificates
as a program, and their costs are milestone 14. Case 2a's pullback and the naming of orbital
colours handed to Split-or-Johnson (Babai's warning in 2b2) are milestone 14 too. The Design
Lemma's application to the Case 3 colouring (`k ≤ |Γ|/4`) is milestone 10's theorem, invoked in
milestone 14. Babai's own aggregation (Thm. 10.2.1, with Bochert's bound and the "sideburns",
and his Prop. 10.1.13) is not followed: Helfgott's needs only `TransitivityBound`.

## Milestone 12: alternating quotients and the CFSG-free interfaces (`PLAN-12.md`)

The group theory of alternating quotients (Babai §§8.1, 8.3; Helfgott §4.1), the effect of a
colouring on `t`-subsets (Babai §5.2), and the CFSG-free route made precise. `PLAN-12.md` lists
every use of the classification in Babai's analysis with its replacement, gives the argument
that replaces Cameron's theorem (Babai §13.1: Split-or-Johnson on the orbital configuration and
Wielandt's bound), and revises the roadmap (milestones 13–16).

1. **Interfaces** (`AltQuot/Interfaces.lean`). The two CFSG-dependent results enter as explicit
   hypotheses, in their weak CFSG-free form:
   - `AltQuotientIso K`, Helfgott's Lemma 4.1 with threshold function `K`: every epimorphism
     from a primitive permutation group of degree `n` onto `Alt(k)`, `k ≥ K n`, is injective.
     Pyber's Lemma 12 proves it for `K n = max C ((⌊log₂ n⌋ + 1)⁵)` (milestone 15); Babai's
     `K n = max 9 (⌊log₂ n⌋ + 3)` needs Schreier's hypothesis and is not used.
   - `TransitivityBound T`, Wielandt's bound: a `t`-transitive group of degree `k ≥ t` not
     containing `Alt(k)` has `t ≤ T k` (`t < 3 ln k`; milestone 16).
   - Both are satisfiable with useless thresholds (`altQuotientIso_succ`: `K n = n + 1`;
     `transitivityBound_id`), so neither hypothesis is contradictory.
2. **Alternating groups** (`AltQuot/Alternating.lean`): `Alt(Λ)` is perfect, and its proper
   subgroups (and the subgroups of `Sym(Λ)` not containing it) have index at least `|Λ|`, for
   `|Λ| ≥ 5`.
3. **Simple quotients of subdirect products** (`exists_le_ker_of_simple`, Babai Lemma 8.1.1).
4. **Affected points** (`AltQuot/Affected.lean`, `AltQuot/Unaffected.lean`), against
   `AltQuotientIso K` with `K` monotone. Babai's threshold `k > max(8, 2 + log₂ n)` is split
   into `5 ≤ k` (simplicity of `Alt(k)`), `K n ≤ k` (the interface) and `n < k!/2` (the counting
   step), all three explicit. The counting condition is not implied by the interface in
   general — the witness `K n = n + 1` equals `2 + log₂ n` at `n = 2`, and Babai's Remark 8.2.5
   shows tightness only for an infinite affine family. For the threshold that milestone 15
   proves (Pyber's, of order `(log₂ n)⁵` with a large constant), `K n ≤ k` will imply
   `n < k!/2`, and that implication will be proved there. `PLAN-12.md` §5 claims that every
   valid `K` exceeds `2 + log₂ n`; that is false, and this paragraph corrects it (round 1,
   finding F1).
   - `stabilizer_map_ne_top` (Lemma 8.3.1; Helfgott 4.3 (a)): transitive `G`, `φ` onto
     `Alt(Λ)` ⟹ `φ(G_x) ≠ Alt(Λ)`;
   - `exists_affected` (Lemma 8.3.3; 4.3 (b)): orbits of at most `N` points ⟹ some point is
     affected;
   - `unaffected_stabilizer` (the Unaffected Stabilizer Theorem, Thm. 8.3.5; Prop. 4.4 (a)):
     for a giant representation, `Alt(Λ) ≤ φ(G_(D))`, `D` the unaffected points;
   - `card_orbit_ker_mul_index` (Prop. 8.3.6) and `affected_orbit` (the Affected Orbit Lemma,
     Cor. 8.3.7; Prop. 4.4 (b)): `k · |x^{ker φ}| ≤ |x^G|` for affected `x`.
5. **Colourings of `t`-subsets** (`AltQuot/Subsets.lean`): the binomial inequality
   `3 C(m₁, t₁) C(m₂, t₂) ≤ 2 C(m, t)` (Prop. 5.2.3), mixed and monochromatic classes (Lemma
   5.2.1), colourings without large classes (Cor. 5.2.2).
6. **Checks** (`GraphIsoChecks/AltQuot.lean`): the interfaces are inhabited; kernel-checked
   instances of Prop. 5.2.3 and Lemma 5.2.1 (b) on small ranges; the Unaffected Stabilizer
   Theorem instantiated at the witness interface, where it is vacuous.

**Validation.** `lake build --wfail` succeeds with mathlib prebuilt. No Lean line exceeds 100
characters, and the sources contain no `sorry`, `admit`, `native_decide`, `noncomputable`,
`Classical.choose`, axiom or option override. Size: about 1,100 new lines of library code and 60
lines of checks.

**What is not covered.** The interfaces are hypotheses; nothing in this milestone uses the
classification, and nothing proves the quasipolynomial thresholds yet (milestones 15–16).
Helfgott states Prop. 4.4 (b) for orbits "containing some unaffected elements"; his proof, and
Babai's Cor. 8.3.7, concern affected points, which is the version proved. The identification of
Johnson groups and schemes (Helfgott §2.8) leaves the roadmap: on the CFSG-free route,
Split-or-Johnson returns Johnson schemes with their point set `Λ` explicit (`PLAN-12.md` §2).
Babai's Main Structure Theorem (§8.5, through the Jordan–Liebeck theorem) is not needed by
Helfgott's local certificates and is not formalized.

## Milestone 11: Split-or-Johnson (`PLAN-11.md`)

The second stage of Babai's recursion: **Split-or-Johnson** (Helfgott Thm. 5.3 with Props. 5.7
and 5.8, Babai §7 with the correction in Babai's note *Fixing the UPCC case of
Split-or-Johnson*, January 2017). From a uniprimitive classical coherent configuration on `Γ`,
a procedure finds, canonically relative to choices of total multiplicative cost
`|Γ|^{O(log |Γ|)}`, a colored `t`-partition of `Γ` or a Johnson scheme embedded in `Γ` on more
than `t` points. Everything is elementary, and the theorem holds for
every uniprimitive input, as the CFSG-free route of `PLAN-10.md` needs (orbital configurations of
uniprimitive groups). This milestone is at the **model level**: the procedures are computable Lean
functions with correctness, canonicity and multiplicative-cost theorems, and no running time is
claimed; their costed programs are deferred to milestone 14.

1. **Choice trees** (`SplitJohnson/CTree.lean`): Babai's canonicity relative to arbitrary
   choices (Def. 4.0.4). A node chooses from a canonically determined finite set; the number of
   root-to-leaf paths (`count`) is the multiplicative cost; `Live` says every reachable node set
   is nonempty. A procedure is canonical when `F (σ • X) = (F X).act σ`, an equality of trees, so
   relabellings carry reachable leaves to reachable leaves (`reach_act`).
2. **Outputs** (`SplitJohnson/Output.lean`): colored `t`-partitions (`IsColPart`, Babai Def.
   5.1.1: admissible colored equipartitions with blocks of at most `t` points; blocks are named
   by a block map, which is canonical) and Johnson embeddings (`IsJohnson`: a bijection from
   `V₀`, `|V₀| > t`, onto the `s`-subsets of a set of nonempty pairwise disjoint cells, `2 ≤ s`,
   `2s ≤ |Λ|`). Cells (`Finset α`) are Babai's ideal points.
3. **Classical configurations on a set** (`Coherent/Classical.lean`, `Coherent/BipGraph.lean`):
   Exercises 2.12, 2.15–2.18, 5.4–5.6 and B.7, primitivity with computed components (`comp`,
   `mem_comp`). Exercise 2.16 (a) is the invariance of walk counts with any colour sequence
   (`walkCount_eq`). Helfgott's Exercise 2.15 as stated is false without homogeneity (the orbital
   configuration of `Sym({0,1,2})` on `{0,1,2,3}`); the homogeneous version is proved, which is
   the case the proof of Prop. 5.7 uses.
4. **Ray-Chaudhuri–Wilson** (`ray_chaudhuri_wilson`, Prop. 2.20), by an injective `ℚ`-linear
   map: the quadratic form of the incidence map is a nonnegative combination of squares with a
   positive coefficient on `Σ x_S²`.
5. **Weisfeiler–Leman on any finite type** (`wlOn`): milestone 10's `wl` transported along an
   enumeration, independent of it, computable through `Trunc.lift`; coherent, refining, with the
   same twins, and natural under equivalences (`wlOn_natural`).
6. **Coherent Split-or-Johnson** (`coherent_split_or_johnson`, `_relabel`): at most `|C₂|`
   paths; leaves are colored `|C₁|/2`-partitions of `C₁` or bipartite graphs `(W₁, W₂; A')` with
   `|W₁| ≥ |C₁|/2`, `W₂` a set of at most `|C₂|/2` ideal points (nonempty pairwise disjoint
   subsets of `C₂`), and twin classes of at most `|W₁|/2`. Helfgott's statement has
   `W₂ ⊆ C₂`, but his contraction (Exercise 2.18) produces blocks of `C₂`; the formalization states
   what the proof gives. Babai's corrected argument for a primitive `X[C₂]` (Helfgott, footnote
   17) is used.
7. **Bipartite Split-or-Johnson** (`bipartite_split_or_johnson`, `_relabel`), Helfgott's proof
   with a fixed threshold `t` (his "original value of `|V₁|`"): the points dropped at a level get
   new colours, one block each (`addPiece`), so a colored partition found deeper extends. Each
   level takes the twin and degree step, then the Johnson test, then the base case
   `v² ≤ 27 ⌈log₂ 2t⌉³` (Helfgott's `|V₂| ≤ (6 log |V₁|)^{3/2}`, which he takes first); the
   `d`-ary structure with
   `d = min(s, 6j)`, `j = ⌈log_v n₁⌉`, is non-symmetric by Ray-Chaudhuri–Wilson
   (`bigTwins_card_lt`); the Design Lemma's choice costs `v^d < (v n₁)^6`. A guard (`shrink`)
   makes every recursive call after a choice have at most two thirds of the cells; the proof
   shows it always passes, and it makes the count bound unconditional: at most
   `2^{128 (⌈log₂ t⌉ + 2)²}` paths whenever `|V₂| ≤ t` and `|V₁| ≤ 2t` (`bsoj_count_le`).
8. **Split-or-Johnson** (`split_or_johnson`, `split_or_johnson_relabel`,
   `split_or_johnson_reach`): for a uniprimitive classical coherent configuration on a finite
   type `Γ` and `t` with `|Γ| + 2 ≤ 2t`, `t < |Γ|`: live, at most `2^{129 (⌈log₂ |Γ|⌉ + 2)²}`
   paths, every leaf a colored `t`-partition of `Γ` or a Johnson embedding on more than `t`
   points; canonical under `Sym(Γ)`. The colours `beige` and `cyan` of Helfgott's proof (from
   arbitrary `z` and `y`) are taken as the least admissible pair, so no extra choice is made.
9. **Checks** (`GraphIsoChecks/SplitJohnson.lean`): Theorem 5.3 end to end on the Petersen graph
   (`t = 6`, 10 leaves, colourings) and the Clebsch graph (`t = 9`, 16 leaves, each the Johnson
   scheme `J(5, 2)` on the non-neighbours of `x`), with inputs checked uniprimitive and coherent,
   every leaf valid and canonicity at every `x`; Prop. 5.8 on the orbital configurations of
   `Sym(5)` (ordered pairs and 2-subsets, `X[C₁]` imprimitive) and `Sym(7)` (3-subsets and
   2-subsets, both sides primitive, one choice); Prop. 5.7 on the incidence graph of the
   3-subsets of a 7-set (one Johnson leaf `J(7, 3)`) and of the 2-subsets of a 6-set less one
   (not Johnson; the base case, 720 leaves).

**Validation.** `lake build --wfail` succeeds with mathlib prebuilt. No Lean line exceeds 100
characters, and the sources contain no `sorry`, `admit`, `native_decide`, `noncomputable`,
`Classical.choose`, axiom or option override. Size: about 7,300 new lines of library code (50,600
in all) and 300 lines of checks; the new check module runs in about two minutes.

**Deviations and what is not covered.**
- **Thresholds.** Helfgott's `α ≥ 2/3` (Thm. 5.3) and `2/3 ≤ β < 1` (Prop. 5.7) become a natural
  `t` with `|V| + 2 ≤ 2t` and `t < |V|`. A class has more than `α|V|` points exactly when it has
  more than `⌊α|V|⌋`, so Helfgott's statement for a given `α < 1` is the case `t = ⌊α|V|⌋`, which
  is covered exactly when `|V| + 2 ≤ 2⌊α|V|⌋`. For `α = 2/3` this holds for `|V| = 6` and every
  `|V| ≥ 8`, but not for `|V| = 7` (`⌊14/3⌋ = 4`, and `9 > 8`) or `|V| ≤ 5`; Helfgott settles such
  small cases by brute force, and they are not covered. `PLAN-11.md` (and the docs of round 1)
  described the range as "any `α > 1/2 + 1/|V|`", which ignores the floor; this paragraph
  corrects it. Prop. 5.7 assumes twin classes of at most `t` points (weaker than Helfgott's
  `2|V₁|/3`) and `|V₂| ≤ t` (weaker than `|V₂| < β|V₁|`), and returns Johnson embeddings on more
  than `t` points.
- **Order of the steps.** Prop. 5.7 takes the twin and degree step and the Johnson test before
  the base case (Helfgott takes the base case first). Both make no choice, so validity and the
  count bound are unaffected, and small inputs reach the Johnson outcome (round 1, finding F3).
- **Johnson schemes** `J(r, s)` are allowed with `2s ≤ r`, as in Helfgott §5.3.3 (his §2.7
  defines them for `r ≥ 2s + 1`); Prop. 5.7's Johnson case gives `s ≤ |V₂|/2`, so `r = 2s` can
  occur.
- **Canonicity** in Prop. 5.7 is under `Sym(α)` acting on points and cells together, not under
  Helfgott's `Sym(V₁) × Sym(V₂)`; this is what Theorem 5.3 and the later stages need (the
  configurations live on one set `Γ`).
- **Checks.** The deeper branches of Prop. 5.7 (the `d`-ary structure, the Design Lemma's choice,
  Coherent Split-or-Johnson inside the recursion) are covered by the proofs only: at sizes that
  can be run the base case applies whenever the Johnson test fails, and the `d`-ary
  Weisfeiler–Leman step is a polynomial of degree about `6d`. Theorem 5.3 is run end to end with
  both outcome types.
- **Running time.** No running time is proved for these procedures; the costed programs, and
  the cost of enumerating the leaves of a choice tree, belong to milestone 14.

## Milestone 10: Weisfeiler–Leman and the Design Lemma (`PLAN-10.md`)

The first stage of Babai's recursion (Helfgott §§2.3–2.6 and 5.1, Babai §6.1): **descent from a
relational structure**. From a `k`-ary relational structure on `Γ = Fin m`, the `k`-ary
Weisfeiler–Leman refinement computes a canonical coherent configuration, and the Design Lemma
finds, canonically relative to fewer than `k` individualized points, a colouring of `Γ` with no
dominant colour or a non-clique classical coherent configuration on a dominant colour class;
the only other outcome is a large set of pairwise twins. Everything is elementary.
`PLAN-10.md` also lays out the later stages of Babai's recursion (milestones 11–14).

1. **Configurations** (`Coherent/Basic.lean`, `Coherent/Skeleton.lean`): `k`-ary configurations
   and coherent configurations (`IsConfig`, `IsCoherent`: Helfgott's Definitions 2.5 and 2.8),
   classical coherent configurations (`IsCoherent2`), twins, cliques, and the individualized
   1- and 2-skeletons `skel1 c x`, `skel2 c x`. Counting with any predicate on the colours
   depends only on the colour (`IsCoherent.card_filter_pred`); the individualized 2-skeleton of
   a coherent configuration is a classical coherent configuration (`isCoherent2_skel2`), and so
   is its restriction to a vertex colour class (`isCoherent2_restrict`).
2. **Fisher's inequality** (`fisher_inequality`, repeated blocks allowed, `λ < r`), by an
   injective `ℚ`-linear map: `Σ_b (Σ_{p ∈ A_b} x_p)² = (r − λ) Σ x_p² + λ (Σ x_p)²`.
3. **The large clique lemma** (`isTwin2_of_large_clique`): a vertex colour class `C` with
   `2|C| > |V|` on which all pairs of distinct points have one colour consists of pairwise
   twins. A point outside `C` that sees `C` in two colours gives a block design on `C` with
   blocks indexed by its own colour class, and Fisher's inequality gives a contradiction.
   Helfgott states `|C| ≥ |Γ|/2`, but his proof needs the strict inequality.
4. **The Design Lemma** (`design_lemma_of_le_succ`, Helfgott's Prop. 5.1, Babai's Thm. 6.1.1) with a
   natural threshold `t` in place of `α|Γ|` ("dominant" means more than `t` points), for every `t`
   with `|V| ≤ 2t + 1`. A class has more than `α|V|` points exactly when it has more than `⌊α|V|⌋`,
   and `|V| ≤ 2⌊α|V|⌋ + 1` for every `α ≥ 1/2`, so this is Helfgott's whole range; `design_lemma` is
   the case `|V| ≤ 2t`. For a `k`-ary coherent configuration, `k ≥ 2`, with no set of more than `t`
   pairwise twins, some list `x` of fewer than `k` points has (a) an individualized vertex colouring
   with no class of more than `t` points, or (b) `x.length + 2 ≤ k`, a class of more than `t`
   points, and an individualized 2-skeleton that is not a clique on it. Helfgott's minimal-length
   argument is replaced by rearranging a witness tuple (a tuple whose entries are among those of
   another is a composition with a map of positions, so its colour is determined).
5. **Weisfeiler–Leman** (`Coherent/WL.lean`): the model `wl k m c` (round 0 adds the equality
   pattern; each round colours a tuple by its colour, the colours of `x ∘ τ` for all
   `τ : Fin k → Fin k`, and the sorted vectors of the colours with one position replaced; colours
   are ranks of signatures in the sorted list of distinct signatures). The result is a coherent
   configuration (`wl_isCoherent`) refining the input (`wl_refines`, via the colour list
   `wl_decode`); **canonical, colour names included** (`wl_relabel`); with exactly the
   isomorphisms of the input given equal colour lists (`wl_iso_iff`), hence the same twins
   (`isTwin_wl_iff`); stable after at most `m^k + 1` rounds (`wlStep_wlIter`).
6. **The refinement as a program** (`Coherent/ListProg.lean` to `Coherent/WLProg.lean`):
   lexicographic comparison, insertion sort, sorting without repetition and positions, matched
   to mathlib's `List.insertionSort`, `Finset.sort`, `List.idxOf`; tuples stored by their codes
   (`finFunctionFinEquiv`), with the codes of the neighbours and of the rearrangements computed
   from a table of products `z · mʲ`, so the programs only add, subtract and compare. A round on
   arrays is the round of the model (`stepA_repSt`), and `wlProg` computes `wl`
   (`RunsWithin.wlProg`, `wlA_eq`), the loop paid by the potential
   `(m^k + 1 − #colours)(roundCost + 2)`.
7. **The Design Lemma as an algorithm** (`Coherent/DesignArray.lean`,
   `Coherent/DesignProg.lean`): for every list `x` of fewer than `k` points in a fixed order, the
   individualized vertex colouring, the first point of a class of more than `t` points, and
   whether the 2-skeleton is a clique on that class; the test is exactly the Design Lemma's
   conclusion (`goodA_iff`, for `m ≤ 2t`), and the search returns the first `x` where it holds.
   Babai's primitivity test (lines 07–09 of Split-or-UPCC) belongs to Split-or-Johnson
   (milestone 11).
8. **Concrete theorems** (`Solver/Coherent.lean`), over the empty backend, on every input:
   - **`wl_checked`**: `wlChecked (k, m, col)` returns `none` exactly when `col` is not an
     array of `m^k` colours, and otherwise the array of `wl k m (toFun col)` and its colour list,
     at cost at most **`720 (m^k + 1)³ ((m + 2)(k + 2))² (k^k + 1)`**;
   - **`descent_checked`**: `descentChecked (k, m, t, col)` returns `none` exactly when `k < 2`,
     `2t < m` or `col` is not of size `m^k` (the entry takes the thresholds `t ≥ m/2`); `some none`
     only if `toFun col` has more than `t` pairwise twins; and otherwise a list `x` of fewer than
     `k` points with the Design Lemma's conclusion for the refinement (`DesignGood`) and its
     individualized vertex colouring, at cost at most
     **`1000 (m^k + 1)³ ((m + 2)(k + 2))² (k^k + 1)`**. The outcome at `x` is canonical relative
     to `x` (`skel1_wl_relabel`), and the restricted 2-skeleton is a classical coherent
     configuration (`isCoherent2_wl_skel2`).
9. **Checks** (`GraphIsoChecks/Coherent.lean`), tied to the two theorems by `runWL_spec` and
   `runDescent_spec`: kernel-evaluated runs on one and two points; interpreter refinements of
   `P₃`, `C₅`, `C₆`, `2K₃` (`k = 2`) and a ternary structure on `P₃` (`k = 3`), each checked to be
   coherent by brute force, to refine the input and to be canonical under a relabelling; `C₆`
   and `2K₃` are separated; descents with outcome (a), outcome (b), `some none` (`K₄`), and
   rejected inputs.

**Validation.** `lake build --wfail` succeeds with mathlib prebuilt; the new check module takes a
few seconds. No Lean line exceeds 100 characters, and the sources contain no `sorry`, `admit`,
`native_decide`, `noncomputable`, `Classical.choose`, axiom or option override. Size: about
43,300 lines of library code (6,200 of them new for this milestone) and 3,500 lines of checks.

**What is not covered.** The refinement is the plain `k`-ary algorithm with the configuration
functor folded into every round; its cost `O((m^k)³ m² k² k^k)` is far from Babai's
`O(k² m^{2k+1} log m)`, but it is `m^{O(k)}` for `k ≤ m`, which is what the recursion needs.
Coherence of the result is proved; that it is the coarsest coherent refinement is not. The
search returns the first good list in its fixed order; canonicity is relative to the
individualized points, as in Babai and Helfgott. Thresholds are a natural number `t`. The
checked descent requires `m ≤ 2t`: Helfgott's `α|Γ|` with `α ≥ 1/2` corresponds to
`t = ⌊αm⌋`, which satisfies `m ≤ 2t` except when `m` is odd and `⌊αm⌋ = (m − 1)/2` (that is,
`α < (m + 1)/(2m)`); those thresholds are covered by the Design Lemma itself
(`design_lemma_of_le_succ`) but rejected by the entry. `PLAN-10.md` states the conversion
`t = ⌊αm⌋` without this qualification; this paragraph corrects it. Split-or-Johnson, local
certificates and the recursion itself are later milestones (`PLAN-10.md`).

## Milestone 9: graphs of every bounded valence (`PLAN-9.md`)

Luks's theorem: **for every `Δ ≥ 2`, isomorphism of graphs of maximum degree at most `Δ` in time
polynomial in `n`**, connected or not. Milestone 7's reduction is unchanged; for `Δ ≥ 6` its
layer groups need not be solvable (a twin class of five points gives `S₅`), and milestone 8's
bound replaces milestone 6's. No new programs besides the checked entries for `Δ`.

1. **Sections of `p`-groups** (`Groups/Sections.lean`): a finite `p`-group has simple sections
   of order `p` (`boundedSections_of_isPGroup`: a simple `p`-group is its own centre); bounds
   may be raised (`BoundedSections.mono`).
2. **Bounded layer groups** (`Valence/Bounded.lean`): a point has at most `Δ − 1` twins for
   every `Δ` (`card_tw_le_pred`; milestone 7's bound of four is the case `Δ ≤ 5`), so the
   kernel of the restriction `A_{r+1} → A_r`, which embeds in the product of the permutation
   groups of the twin classes, has simple sections of order at most `(Δ − 1)!`
   (`boundedSections_ker`). `A₀` is a `2`-group; by extensions, **every layer group has simple
   sections of order at most `k`, for every `k ≥ 2` with `(Δ − 1)! ≤ k`**
   (`boundedSections_autR`), so every homomorphic image of every layer group has
   `PrimBounded _ (3 k³ + 3 k² + 12 k + 1)` (`layerPrim_bounded`).
3. **The step constant as a parameter** (in place, milestone 7's modules): `LayerPrim Δ c` says
   that every homomorphic image of every layer group has `PrimBounded _ c`. The layer step
   (`RunsWithin.stepProg`), the edge test, the algorithm and the matching of components take
   `c ≥ 1` and `LayerPrim Δ c` in place of `Δ ≤ 5`; their costs `stepCost Δ c`, `layerCost Δ c`,
   `edgeCost Δ c`, `mainCost Δ c` have the solver's exponent `3c + 5`, and the matching takes a
   bound `B` on the connected test (`allCost Δ B`). The checked entries are stated for every
   `Δ` (`giBoundedChecked Δ`, `giBoundedAllChecked Δ`, `RunsWithin.giBoundedChecked`,
   `RunsWithin.giBoundedAllChecked`). Milestone 7 is the case `Δ = 5`, `c = 13`
   (`layerPrim_solvable`, which replaces `induced_isSolvable`), `B = mainBound n`: its programs,
   closed forms and protected statements are unchanged.
4. **Closed forms** (`Solver/ValenceBounded.lean`), for every `Δ ≥ 2` and `c ≥ 1`. With
   `K = N + 2` and `T = K^Δ`: a layer domain has fewer than `T` points (`pow_add_succ_le`),
   there are at most `T²` generators, and `Δ, N ≤ T`, so every term of a layer step other than
   the solver's `6640 (D + 1)^{3c + 5}` is a polynomial of degree at most six in `T`. One layer
   step costs at most `7300 (N + 2)^{Δ (3c + 5)}` (`layerCost_le_pow`), the algorithm at most
   `7700 Δ (2n + 2)^{Δ (3c + 5) + 2}` (`mainCost_le_pow`), the checked entries at most
   `8100 Δ (2n + 2)^{Δ (3c + 5) + 2}` (connected, `checkedCostB_le_pow`) and
   `2300 Δ (2n + 2)^{Δ (3c + 5) + 4}` (all graphs, `allCheckedCostB_le_pow`). With milestone
   8's `c = 3k³ + 3k² + 12k + 1`, `3c + 5 = 9k³ + 9k² + 36k + 8`.
5. **Concrete theorems** with the Schreier–Sims backend, with no assumed oracle, for every
   `Δ ≥ 2` and every `k ≥ 2` with `(Δ − 1)! ≤ k`:
   - **`gi_bounded_checked`**: the checked entry `giBoundedChecked Δ`, on every input, returns
     `none` exactly when the input is not valid connected data of maximum degree at most `Δ`
     (`GIValidB Δ`; `Conn 0` is vacuous), and otherwise a correct answer (`GIAnswer`), at cost
     at most **`8100 Δ (2n + 2)^{Δ (9k³ + 9k² + 36k + 8) + 2}`**;
   - **`gi_bounded_simpleGraph'`**: connected simple graphs on `Fin n` with every degree at most
     `Δ`;
   - **`gi_bounded_all_checked`**: the checked entry `giBoundedAllChecked Δ` for all graphs of
     maximum degree at most `Δ` (`GIValidAllB Δ`), at cost at most
     **`2300 Δ (2n + 2)^{Δ (9k³ + 9k² + 36k + 8) + 4}`**;
   - **`gi_bounded_all_simpleGraph'`**: any simple graphs on `Fin n` with every degree at most
     `Δ`.
6. **Checks** (`GraphIsoChecks/ValenceBounded.lean`), tied to `gi_bounded_checked` and
   `gi_bounded_all_checked` for `Δ = 6`, `k = 120` by `runGIB_spec` and `runAllB_spec`:
   - kernel-evaluated runs: no points and one point (connected entry, costs 80 and 174), no
     points (all-graphs entry, cost 39);
   - interpreter runs against brute force, every returned isomorphism checked: `P₃` against a
     relabelling (50,699,515 units); three isolated points (1,209) and `2K₂` against `P₄`
     (3,194) with the all-graphs entry; a vertex of degree seven rejected by both entries. The
     closed forms' exponents (about `9.4 · 10⁷` for `Δ = 6`, `k = 120`) are too large to
     evaluate; the runs check the costs against `8100 Δ (2n + 2)^{44Δ + 2}` and
     `2300 Δ (2n + 2)^{44Δ + 4}`, which are smaller;
   - **a layer group that is not a `{2, 3}`-group**: the first layer step of two stars `K₁,₆`
     (115,800,876 units) returns 71 generators of `A₁` (each checked to lie in `A₁`), whose
     group has order `28800 = 2 · (5!)²` from a Sims table: the root symmetry exchanging the
     stars, and `S₅ × S₅` on the two twin classes of five leaves. No brute-force count: the two
     levels have `4! · 10!` permutations. A whole run on `K₁,₆` does not fit the interpreter
     (its second layer has 848 subsets).
7. **Milestone 8's open finding F1**: `exists_elementary_of_abelian` now concludes `V ≤ A`, as
   its docstring said.

**Validation.** `lake build --wfail` succeeds with mathlib prebuilt; the new check module takes
about a minute. No Lean line exceeds 100 characters, and the sources contain no `sorry`,
`admit`, `native_decide`, `noncomputable`, `Classical.choose`, axiom or option override. Size:
about 37,100 lines of library code (600 of them new for this milestone) and 3,200 lines of
checks.

**What is not covered.** The exponent is enormous (`k ≥ max 2 (Δ − 1)!`, so `9k³` is already about
`1.6 · 10⁷` for `Δ = 6`); it is polynomial in `n` for each fixed `Δ`, which is Luks's theorem, and
far from practical. The plan allowed a factor `C (Δ + 1)³`; the proof gives `C Δ`. For `Δ ≤ 5`
milestone 7's bounds are much better. Valence one is the case `Δ = 2`. Checks of whole runs with a
vertex of degree above three do not fit the interpreter, as in milestone 7.


## Milestone 8: the Babai–Cameron–Pálfy theorem (`PLAN-8.md`)

The Babai–Cameron–Pálfy theorem in the form of Helfgott's Theorem 2.3, solvable or not: **a
primitive subgroup `G` of `Sym(n)`, `n ≥ 2`, all of whose simple sections have order at most
`k`, has order at most `n^{3 k³ + 3 k² + 12 k + 1}`**
(`card_le_of_isPreprimitive_of_boundedSections`; only quasiprimitivity is used). With it,
`PrimBounded` holds for every group with bounded simple sections, and string isomorphism is
polynomial for such groups. No new programs: the algorithm is milestone 3's `solve_luks`. The
argument is elementary, with no induction on the degree and no classification of finite simple
groups.

1. **Sections** (`Groups/Sections.lean`): `BoundedSections k G` says that every simple quotient
   `H/M` of a subgroup `H ≤ G` has order at most `k`. Every composition factor is such a
   section, and by Jordan–Hölder every simple section is a section of a composition factor, so
   this says that the composition factors have order at most `k` (Jordan–Hölder is not
   formalized; the theorems are stated with sections). The property passes to subgroups,
   quotients, extensions (`of_ker`) and finite products (`pi`); the primes dividing `|G|` are
   at most `k`, so there are at most `k` of them. A finite group has sections of order at most
   its own (`boundedSections_card`).
2. **Minimal normal subgroups** (`Groups/MinimalNormal.lean`), relative to a subgroup `Y` of a
   finite group: a nonabelian minimal normal subgroup `N` of `Y` is the product of the
   `Y`-conjugates of a minimal subgroup `T` normalized by `N`; they are nonabelian simple,
   pairwise commuting and independent, and `Y` permutes them transitively
   (`exists_simple_factors`).
3. **The action on the factors** (`Groups/FactorAction.lean`): if `Y` permutes a finite set
   `F` of subgroups of order at most `k` with supremum `N`, then
   `|Y| ≤ |C_Y(N)| (k! 2^k)^{|F|}`. The image in `Sym(F)` has Sylow `r`-subgroups of order at
   most `2^{|F| − 1}` (milestone 6, Legendre) and at most `k` prime divisors; the kernel acts
   on each factor through `Sym(A)`, of order `|A|! ≤ k!`, with kernel centralizing `N`.
4. **Subgroups of products** (`Groups/Subdirect.lean`): if `T_i` (`i ∈ ι`) are nonabelian
   simple of equal order `m` and `H ≤ ∏ T_i` contains no factor, then
   `2^{|ι|} |H|² ≤ m^{2 |ι|}` (`two_pow_mul_card_sq_le`). The induction kills one coordinate
   `a`; if the image contains a factor `T_b`, the elements of `H` supported on `{a, b}` lift
   every element of `T_a` (`exists_lift`, using `|T_a| = |T_b|`), a commutator argument shows
   that the image contains no second factor (`not_hasFactor_two`), and the induction kills `b`
   as well.
5. **Linear groups** (`Groups/Radical.lean`, `NoAbelian.lean`, `BoundedLinear.lean`): a group
   `H` with bounded sections acting faithfully on a `ZMod p`-space `V` with no nontrivial
   normal `p`-subgroup has `|H| ≤ |V|^{3 k³ + 3 k² + 12 k}`
   (`card_le_of_boundedSections_linear`):
   - its solvable radical `R` (`exists_radical`, from `isSolvable_sup`) has no normal
     `p`-subgroup (`eq_bot_of_normal_isPGroup_of_normal`), so `|R| ≤ |V|^{12 k}` by
     milestone 6;
   - `H/R` has no nontrivial abelian normal subgroup (`eq_bot_of_abelian_normal_quotient`); for
     such groups `|Y| ≤ (k! 2^k)^t` with `2^t` at most the `p′`-part of `|Y|`
     (`exists_card_le_of_noAbelianNormal`), by recursion into the centralizer of a minimal
     normal subgroup, to which the property passes (`NoAbelianNormal.centralizer`); a
     nonabelian simple group is not a `p`-group, so each factor contributes at least `2` to the
     `p′`-part;
   - the `p′`-part of `|H|` is at most `|V|^{3 k}`: Sylow `r`-subgroups with `r ≠ p` have
     order at most `|V|³` (milestone 6; `ordCompl_card_le_linear`).
6. **Primitive groups** (`Groups/PrimitiveBounded.lean`): take a minimal normal subgroup `N`.
   - `N` abelian: milestone 6's affine reduction, factored out as
     `card_le_of_isQuasiPreprimitive_of_abelian` (the statement of
     `card_le_of_isQuasiPreprimitive_of_isSolvable` is unchanged), with item 5 for the point
     stabilizer.
   - `N` nonabelian (`card_le_of_isQuasiPreprimitive_of_nonabelian`, exponent
     `2 k² + 2 k + 1`): `N` is transitive; its centralizer acts semiregularly, so has order at
     most `n`; the point stabilizer in `N` contains no factor (a factor is normal in `N`, so it
     would fix every point), so `2^j ≤ n²` by item 4; and item 3 gives
     `|G| ≤ n (k! 2^k)^j ≤ n (2^j)^{k² + k}`.
7. **Luks's strategy**: `primBounded_of_boundedSections`
   (`PrimBounded G₀ (3 k³ + 3 k² + 12 k + 1)`) and `solve_luks_bounded`: with the
   Schreier–Sims backend, cost at most
   `6640 (n + 1)^{9 k³ + 9 k² + 36 k + 8} + 60 L (n + 1)²`.
8. **Checks** (`GraphIsoChecks/LuksBounded.lean`): Luks's strategy on `A₅` and `S₅` on five
   points and on `A₅ ≅ PSL(2, 5)` on six points (five string pairs, with and without
   solutions) agrees with brute force and with the default strategy; the order is computed from
   a Sims table, and the cost is within the bound of `solve_luks_bounded` for `k` the order.
   Luks's strategy costs 6.2 to 24.8 million units, 9 to 20 times the default strategy.

**Validation.** `lake build --wfail` succeeds (2105 jobs) with mathlib prebuilt; the new
check module takes about thirty seconds and 3 GB. No Lean line exceeds 100 characters, and the
sources contain no `sorry`, `admit`, `native_decide`, `noncomputable`, `Classical.choose`,
axiom or option override. Size: about 36,400 lines of library code (1,700 of them new for this
milestone) and 3,000 lines of checks.

**What is not covered.** Jordan–Hölder is not formalized, so the hypothesis is stated for simple
sections, not composition factors. The exponent `3 k³ + 3 k² + 12 k + 1` is crude; it is
polynomial in `k` and independent of `n`, which is what Luks's strategy needs. Graphs of
every bounded valence are milestone 9.


## Milestone 7: graphs of maximum degree five (`PLAN-7.md`)

Luks's layered reduction of milestones 4 and 5, for maximum degree `Δ`: isomorphism of graphs
of maximum degree at most five in polynomial time, connected or not. The layer groups are
solvable `{2, 3}`-groups, proved from the construction, and milestone 6's
`primBounded_of_isSolvable` with `s = 1` bounds every string-isomorphism call.

1. **The degree-free theory, for maximum degree `Δ`** (in place, in `Graph/`):
   `GraphData.ValidD Δ` with `GraphData.Valid = ValidD 3`; `LayeredD Δ` (with `2 ≤ Δ`, so
   that two adjacent points of a level form a subset read by the layer string) with
   `Layered = LayeredD 3`; `SubL Δ` (subsets of at most `Δ` points), `xval Δ` (an edge adds
   `Δ + 1`, which is `4` for `Δ = 3`), `HR … Δ`. Levels, the lifts, the extension criterion,
   the roots, the swap criterion, components, balance, gluing and the simple-graph conversions
   are stated for every `Δ`, and milestones 4 and 5 use them at `Δ = 3`: their protected
   statements are unchanged. Twin classes have at most `Δ − 1` points (`cnt_le`). The
   decomposition of the restriction kernel into twin transpositions
   (`mem_closure_twinSwaps`) no longer uses classes of at most two points; that fact remains
   for `Δ ≤ 3` (`kernel_apply_apply`), where it gives milestone 4's `2`-groups.
2. **Subsets** (`Valence/Subsets.lean`, `Domain.lean`): a subset of a level with at most `Δ`
   points is a sublist of the increasing list of the level's points (`subsR Δ`, the empty one
   first), determined by its elements (`eq_of_toFinset_eq`); there are at most
   `(ℓ + 1)^Δ` of them (`length_subsR_le`). The image of a subset is found by a linear search
   for the member with the image's elements (`findSub`, `subImg`); no index array. The layer
   string on the subsets characterizes `HR Δ r` (`xstr_iff`), and readback gives generators
   of `HR Δ r` (`readback`).
3. **Solvable layer groups** (`Valence/Solvable.lean`), for `Δ ≤ 5`:
   - restriction `A_{r+1} →* A_r` (`resHom`); its kernel embeds in the product over the points
     of the permutation groups of their twins (`twinHom`, `twinHom_injective`), each of at most
     `Δ − 1 ≤ 4` points (`card_tw_le_pred`, `card_tw_le`);
   - so the kernel is solvable (`isSolvable_ker`, by `Equiv.Perm.isSolvable` and
     `isSolvable_pi`, a finite product of solvable groups) and its elements satisfy
     `k¹² = 1` (`ker_pow_twelve`, from the cycle type);
   - by induction on `r` (`A₀` is a `2`-group): **every `A_r` is solvable**
     (`isSolvable_autR`), every element has order dividing `2^i 3^j`
     (`exists_pow_eq_one`), and by Cauchy's theorem **`|A_r|` has at most two prime
     divisors** (`card_primeFactors_autR_le`). Burnside's `pᵃqᵇ` theorem is not used.
4. **Programs** (`Valence/LevelsProg.lean` to `Valence/Step.lean`), each with an exact value,
   an explicit cost and a well-formedness proof: the sublists by one fold from the right
   (`subsProg`), the linear search and the induced generators (`indProg`, equal to
   `indData`), the layer string (`xArrProg`), and the cost bounds of milestone 4's degree-free
   programs (levels, union, lifts, twin swaps, edges, components) for maximum degree `Δ`.
   **One layer step** (`RunsWithin.stepProg`) calls `solveEntry` with
   `PrimBounded _ 13` from `primBounded_of_isSolvable` (`layerPrim_solvable`), so the solver
   costs at most `6640 (D + 1)⁴⁴ + 60 L (D + 1)²` (`luksSimsCost_le_pow`, `c = 13`). Since
   milestone 9 the constant is a parameter (`LayerPrim Δ c`) and milestone 7 is the case
   `c = 13`.
5. **The algorithms** (`Valence/EdgeProg.lean` to `Valence/All.lean`): the edge test, the
   loop over the edges of `Y` (`mainProg Δ`), the validity check of maximum degree `Δ` on every
   input (`validGraphProg Δ`, by case analysis on the first `Δ + 1` cells), and milestone 5's
   matching of components with `mainProg 5` as the connected test (`allProg 5`).
6. **Concrete theorems** with the Schreier–Sims backend, with no assumed oracle:
   - **`gi5_checked`**: the checked entry `gi5Checked`, on every input, returns `none`
     exactly when the input is not valid connected data of maximum degree at most five
     (`GIValid5`; `Conn 0` is vacuous, as in milestone 4), and otherwise a correct answer
     (`GIAnswer`). **The cost is at most `28600 (2n + 2)²²²`** (`checkedCost5_le`). A layer
     domain has at most `(N + 2)⁵ − 1` points for `N = 2n` (`domBound_five_succ_le`), so one
     layer step costs at most `9000 (N + 2)²²⁰` (`layerCost_five_le`);
   - **`gi5_simpleGraph'`**: connected simple graphs on `Fin n` with every degree at most five;
   - **`gi5_all_checked`**: the checked entry `gi5AllChecked` for all graphs of maximum degree
     at most five (`GIValidAll5`), **at cost at most `7200 (2n + 2)²²⁴`**
     (`allCheckedCost5_le`);
   - **`gi5_all_simpleGraph'`**: any simple graphs on `Fin n` with every degree at most five.
7. **Checks** (`GraphIsoChecks/Valence.lean`), tied to `gi5_checked` and `gi5_all_checked` by
   `runGI5_spec` and `runAll5_spec`:
   - kernel-evaluated runs: no points and one point (connected entry, costs 80 and 174), no
     points (all-graphs entry, cost 39);
   - interpreter runs against brute force over all `n!` permutations, every returned
     isomorphism checked: `P₃` against a relabelling (50,699,515 units); the star `K₁,₃`
     against a relabelling, with a twin class of two points (125,661,344); `K₃` against `P₃`,
     not isomorphic (171,114,633); with the all-graphs entry, three isolated points (1,209),
     `K₂ ⊔ K₁` against a relabelling (42,437,378), `2K₂` against `P₄` (3,194);
   - six invalid inputs rejected: a vertex of degree six (both entries), a disconnected graph,
     a wrong number of lists, an asymmetric list, a loop;
   - **narrower than the plan**: a whole run on a graph with a vertex of degree four does not
     fit the interpreter, which keeps the full trace. For `K₁,₄` the second layer is a
     string-isomorphism instance on 73 points (63 subsets of the six leaves); a run of
     `K₁,₄` against a relabelling was stopped after fourteen minutes and 35 GB. The degree-four
     case is checked at the first layer step of `K₁,₄ ⊔ K₁,₄` instead (78,629,977 units): its
     39 generators lie in `A₁`, and the group they generate has order `72 = 2³ · 3²` (from a
     Sims table), equal to a brute-force count of `A₁` over the permutations of the two
     levels. Only the two root symmetries mapping centres to centres extend, and the kernel is
     `S₃ × S₃` on the two twin classes of three leaves.

   On these small graphs the degree-five entry costs about 1.3 times milestone 4's
   (`K₁,₃`: 125.7 against 99.1 million units): the subsets now include the empty one and the
   sets of four points.
8. **Audit and docs.** The build lists the axioms of 47 more principal theorems: only
   `propext`, `Classical.choice` and `Quot.sound` (the well-formedness lemmas only `propext`).
   The audit covers 7285 declarations in 139 modules. `theorem-map.md` has the
   statement-by-statement map.

**Deviations from the plan.**
- The subsets include the empty one (always fixed, with layer string `0`), so a level with no
  points still gives a one-point window.
- The checks of a vertex of degree four are a single layer step, not a whole run (item 7).
- `LayeredD` carries `2 ≤ Δ`, so that two adjacent points of a level form a subset read by the
  layer string; `layered_union` takes it as a hypothesis.

**Validation.** `lake build --wfail` succeeds (2094 jobs) with mathlib prebuilt; the new
check module takes about four minutes, in parallel with the other graph checks. No Lean line
exceeds 100 characters, and the sources contain no `sorry`, `admit`, `native_decide`,
`noncomputable`, `Classical.choose`, axiom or option override. Size: about 34,700 lines of
library code (4,300 of them new for this milestone, plus the in-place generalization of
milestones 4 and 5) and 3,000 lines of checks.

**What is not covered.** From valence six the layer groups need not be solvable (`A₅` and
`S₅` act on twin classes of five points), and the cost bound would need the nonsolvable part of
the Babai–Cameron–Pálfy theorem. The exponents are crude: `12 s + 1 = 13` for the primitive
sections, and `(N + 1)⁵` subsets per layer.

## Milestone 6: primitive solvable groups (`PLAN-6.md`, complete)

The solvable case of the Babai–Cameron–Pálfy theorem in the form of Helfgott's Theorem 2.3
(composition factors of bounded order), by an elementary argument for a bounded number of
prime divisors. With it, string isomorphism is polynomial for solvable groups whose order has
a bounded number of prime divisors. No new programs: the algorithm is
milestone 3's `solve_luks`, whose hypothesis `PrimBounded` is discharged for a larger class.
The milestone of `PLAN-6.md` is complete.

1. **Linear `r`-groups** (`Groups/LinearPGroup.lean`): for primes `r ≠ p`, an `r`-subgroup
   `R` of `GL(V)`, with `V` a nonzero finite `ZMod p`-space, has `2 |R| ≤ |V|³`
   (`card_le_of_isPGroup`; `card_le_of_isPGroup'` gives `|R| ≤ |V|³`, also for `V = 0`).
   The proof is by strong induction on `|V|`:
   - a maximal abelian normal subgroup `A` of `R` is self-centralizing
     (`centralizer_le_of_maximal`);
   - the algebra `B ⊆ End(V)` that `A` generates is reduced, by Maschke's theorem for
     `ZMod p[A]` (`isReduced_adjoin_range`). Its idempotents split `V` into the subspaces
     killed by its maximal ideals, with `|V| = ∏ |V_𝔪|` (`exists_idempotents`,
     `card_eq_prod_zeroSpace`);
   - `R` permutes the maximal ideals by conjugation (`maxAct`, `apply_mem_zeroSpace_maxAct`);
   - with two or more maximal ideals, the kernel of that action embeds in `∏ GL(V_𝔪)`
     (`fixSub`, `resGL`). Its image in `Sym(t)` has order at most `2^{t−1}`, by Legendre's
     formula (`card_le_two_pow_of_isPGroup_perm`, `card_le_of_two_le_card`);
   - with one, `B` is a field, so `A` is cyclic of order `< |V|`, and
     `|R| ≤ |A| |Aut A| ≤ |A|²` (`card_le_of_card_eq_one`).
2. **Coprime action** (`Groups/Coprime.lean`): a `p`-group of automorphisms of a finite
   solvable group `N` with `p ∤ |N|` has order at most `|N|³` (`card_le_of_coprime`).
   - The induction passes through the kernel `M` of the map from `N` onto its abelianization
     modulo `r`-th powers.
   - An automorphism acting trivially on `M` and on that quotient is trivial: `x⁻¹ g(x)`
     defines a homomorphism from a `p`-group into `M` (`map_one_of_isPGroup`).
3. **The `p′`-core** (`Groups/PCore.lean`): every finite group has a largest normal subgroup
   of order prime to `p` (`exists_pcore`).
   - If `H` is solvable with no nontrivial normal `p`-subgroup, the centralizer of its
     `p′`-core lies in the core (`centralizer_le_of_pcore`, the plan's
     `centralizer_pcore_le`).
   - Otherwise the image of the centralizer in the quotient by the core contains a nontrivial
     normal `p`-subgroup (`exists_normal_isPGroup_le`). The part of its preimage that
     centralizes the core is nilpotent (`Subgroup.isNilpotent_of_ker_le_center`), and its
     Sylow `p`-subgroup would be a nontrivial normal `p`-subgroup of `H`.
4. **Solvable linear groups** (`Groups/SolvableLinear.lean`): a solvable group acting
   faithfully on `V`, with no nontrivial normal `p`-subgroup, has order at most `|V|^{12 s′}`,
   where `s′` is the number of primes other than `p` dividing its order
   (`card_le_of_isSolvable_linear`).
   - Each Sylow `r`-subgroup with `r ≠ p` has order at most `|V|³` (item 1).
   - A Sylow `p`-subgroup acts faithfully on the `p′`-core (item 3), so it has order at most
     `|V|^{9 s′}` (item 2).
5. **Primitive solvable groups** (`Groups/PrimitiveSolvable.lean`): a primitive solvable
   subgroup of `Sym(k)` with `k ≥ 2`, whose order has `s + 1` prime divisors, has order at
   most `k^{12 s + 1}` (`card_le_of_isPreprimitive_of_isSolvable`).
   - It has a nontrivial elementary abelian normal subgroup `V`, which is regular. The
     stabilizer acts faithfully on `V` with no nontrivial normal `p`-subgroup (item 4).
   - Only quasiprimitivity is used: the bound is proved for quasiprimitive groups
     (`card_le_of_isQuasiPreprimitive_of_isSolvable`), and the primitive statement follows.
   - `primBounded_of_isSolvable` gives `PrimBounded G₀ (12 s + 1)` for every solvable `G₀`
     whose order has at most `s + 1` prime divisors. It is in `Luks/Solvable.lean` rather
     than in `PrimitiveSolvable.lean` as planned, so that `Groups/` depends on mathlib
     alone.
6. **The concrete theorem** (`Solver/LuksSolvable.lean`): `solve_luks_solvable`, with Luks's
   strategy and the Schreier–Sims backend, no assumed oracle.
   - For a solvable group whose order has at most `s + 1` prime divisors, **the cost is at
     most `6640 (n + 1)^{36 s + 8} + 60 L (n + 1)²`**.
   - It follows from `luksSimsCost_le_pow`, which gives
     `6640 (n + 1)^{3c + 5} + 60 L (n + 1)²` for primitive sections bounded by `k ^ c`, with
     `c ≥ 1`.
   - For `s = 0` this is milestone 3's nilpotent bound.
7. **Checks** (`GraphIsoChecks/LuksSolvable.lean`): interpreter runs of Luks's strategy on
   solvable groups that are not nilpotent. Each run is compared with brute force over the group
   and with the default strategy. The number of prime divisors of the order is computed from a
   complete Sims table, and the cost is checked against the bound:

   | Group | Order | `s` | Solutions | Luks cost | Default cost |
   |---|---|---|---|---|---|
   | `S₄` | 24 | 1 | 4 | 820,975 | 195,043 |
   | `S₄` | 24 | 1 | 0 | 810,506 | 172,940 |
   | `AGL(1, 5)` | 20 | 1 | 2 | 1,072,068 | 221,660 |
   | `AGL(1, 5)` | 20 | 1 | 0 | 1,062,128 | 207,460 |
   | `S₃ wr S₂` | 72 | 1 | 12 | 1,662,390 | 1,155,904 |
   | `AGL(1, 7)` | 42 | 2 | 3 | 6,373,949 | 949,358 |
8. **Audit and docs.** The build lists the axioms of 16 more principal theorems: only
   `propext`, `Classical.choice` and `Quot.sound`. `luksSimsCost_le_pow` sits in
   `Solver/Luks.lean`, and milestone 3's `luksSimsCost_one_le` is now its case `c = 1`.

**Deviations from the plan.**
- The plan says the algebra `B` and its action live inside proofs as existentials. They are
  top-level definitions (`gensOf`, `algOf`, `zeroSpace`, `conjB`, `maxAct`, `maxAction`,
  `fixSub`, `resGL`). All are computable, and none uses `Classical.choose`. Only the
  idempotents, built from `IsArtinianRing.equivPi`, stay inside a proof.
- The abelian normal subgroup `A` of step 1 is maximal for inclusion, not of largest order.
  Self-centralizing needs only that.

**What is not covered.**
- **Helfgott's Theorem 2.3 is covered for solvable groups.** Composition factors of order at
  most `k` allow at most `π(k)` primes, so `s + 1 ≤ π(k)`.
- **Babai–Cameron–Pálfy, Theorem 1.1, allows arbitrary abelian factors**, that is, any number
  of primes. For solvable groups that is the Pálfy–Wolf bound, which needs Clifford theory
  and extraspecial groups. It is not proved here.
- **Nonsolvable primitive groups in `Γ_d` are not covered.** These are affine groups with a
  nonsolvable point stabilizer (for example `2⁴:A₅` on 16 points, in `Γ₅`) and groups with
  nonabelian socle.

**Validation.** A clean `lake build --wfail` succeeds in about eight minutes, with mathlib
prebuilt (2047 jobs, more than before because the group theory imports more of mathlib).
After the cleanups of the final review, an incremental `lake build --wfail` (2048 jobs,
rebuilding everything downstream of `Solver/Luks.lean`) also succeeds. The solvable checks
take about ten seconds. The audit covers 6419 declarations in 121 modules. No Lean line
exceeds 100 characters, and the sources contain no `sorry`, `admit`, `native_decide`,
`noncomputable`, `Classical.choose`, axiom or option override. Size: about 30,500 lines of
library code (1,600 of them for this milestone) and 2,700 lines of checks.

## Milestone 5: all graphs of maximum degree three (`PLAN-5.md`, complete)

Milestone 4 without the connectivity hypothesis: isomorphism of **all** graphs of maximum
degree at most three in polynomial time, by the standard reduction to components. Each pair of
candidate components is decided by milestone 4's connected test `mainProg`. The milestone of
`PLAN-5.md` is complete.

1. **Components** (`Graph/Components.lean`), for valid data `G` on `n` points:
   - reachability (`Reach`, steps along adjacency) is read off the levels:
     `get (levels n G [u]) v < n` exactly when `u` reaches `v` (`lev_lt_iff_reach`, the plan's
     `lev_lt_iff_reachable`, stated for `Reach` rather than for walks of the simple graph; the
     proof passes through mathlib's walks by `reachable_of_reach`);
   - the components (`comps`) are the components of the points that reach no smaller point.
     They are nonempty, closed under adjacency and pairwise disjoint, and every point lies in
     one (`exists_mem_comps`, `eq_of_mem_comps`, `closed_of_mem_comps`);
   - the component data `subG G cs`, relabelled by position, are valid and connected
     (`valid_subG`, `conn_subG`);
   - **invariance**: an isomorphism maps each component onto a component with isomorphic data
     (`giso_imgComp`), so `X` and `Y` have equally many components in each isomorphism class
     (`balanced_comps`). The plan's count "for every graph `C`" is `Balanced`, stated through
     every Boolean invariant of isomorphism, which includes the indicator of each class; the
     bijection of components is built inside the proof;
   - **the greedy step**: a balanced component has a partner (`Balanced.exists`), removing a
     matched pair keeps the rest balanced (`Balanced.step`), and only the empty list balances
     the empty list (`Balanced.eq_nil`);
   - **gluing**: matched components with isomorphisms of their data give an isomorphism,
     whatever the order of the writes (`glue_spec`).
2. **Programs** (`Graph/CompProg.lean`, `Graph/All.lean`), each with an exact value or an
   invariant, an explicit cost and a well-formedness proof:
   - the components, one level computation from each point (`RunsWithin.compsProg`,
     `O(n⁴)`);
   - the component data (`RunsWithin.subGProg`);
   - one candidate partner, which calls `mainProg` when the sizes agree
     (`RunsWithin.partnerStepProg`), and the matching of one component
     (`RunsWithin.matchStepProg`);
   - the gluing by `arrayUpdate` (`RunsWithin.glueProg`).
3. **The algorithm.** `allProg` runs inside `luksBody`. For valid data it returns `none`
   exactly when `X` and `Y` are not isomorphic, and otherwise lists the values of an
   isomorphism (`RunsWithin.allProg`). The matching fails when a component of `X` has no
   partner or a component of `Y` is left over. If `X ≅ Y` the remaining components stay
   balanced, so neither happens. The search keeps the remaining components of `Y` in reverse
   order (the invariants hold up to permutation), so "first" refers to that order: three
   isolated points are matched by `[0, 2, 1]`. The final check for a left-over component of
   `Y` cannot fire on valid data (matched sizes sum to `n`), but makes the proof local.
4. **Concrete theorems** with the Schreier–Sims backend, with no assumed oracle:
   - **`gi3_all_checked`**: the checked entry `gi3AllChecked`, on every input, returns `none`
     exactly when `X` or `Y` is not valid data of maximum degree three (`GIValidAll`; no
     connectivity condition, so the empty input is valid with answer `some #[]`); otherwise
     a correct answer (`GIAnswer`). **The cost is at most `5100 (2n + 1)²⁸`**
     (`allCheckedCost_le`; the algorithm alone at most `4750 (2n + 1)²⁸`, `allCost_le`);
   - **`gi3_all_simpleGraph'`** (the plan's `gi3_all_simpleGraph`; the unprimed name is the
     data version, as in milestone 4): for **any** simple graphs `G` and `H` on `Fin n` with every
     degree at most three, given by their adjacency lists, the result is `some none` exactly
     when there is no isomorphism `G ≃g H`, and `some (some arr)` gives one with values `arr`.
     `gi3_all_simpleGraph` states it for valid data through `GraphData.toSimpleGraph`.
5. **Checks** (`GraphIsoChecks/GraphAll.lean`), tied to `gi3_all_checked` by `runAll_spec`:
   - kernel-evaluated runs on no points and on two isolated points;
   - interpreter runs against brute force over all `n!` permutations, every returned
     isomorphism checked: three isolated points (matched by `[0, 2, 1]`); `K₂ ⊔ K₁` against a
     relabelling; `2K₂` against a relabelling whose components `{0, 2}` and `{1, 3}` are not
     intervals; `2K₂` against `P₄` (sizes differ, no connected test); `K₃ ⊔ K₁` against
     `P₃ ⊔ K₁` (not isomorphic); `P₃ ⊔ K₃` against `K₃ ⊔ P₃` (the partner of `P₃` is found
     after a failed test against `K₃`);
   - four invalid inputs rejected by the validity check.

   The executable model of components, greedy matching and gluing, with a brute-force
   connected test (phase 0, outside the build), agreed with brute force on every pair of valid
   graphs with up to five points: on five points, 768 graphs and 589,824 pairs, 37,420 of them
   isomorphic, every glued map checked.
6. **Audit and docs.** The build lists the axioms of 22 more principal theorems: only
   `propext`, `Classical.choice` and `Quot.sound`. The brute-force helpers of the graph checks
   moved to `GraphIsoChecks/GraphBrute.lean`, so the two graph check modules build in
   parallel.

**Validation.** A clean `lake build --wfail` succeeds (1728 jobs) in about eight minutes, with
mathlib prebuilt; the two graph check modules build in parallel, about four minutes each. The
audit covers 6253 declarations in 113 modules. No Lean line exceeds 100 characters, and the
sources contain no `sorry`, `admit`, `native_decide`, `noncomputable`, `Classical.choose`,
axiom or option override. Size: about 28,700 lines of library code (1,800 of them for this
milestone) and 2,600 lines of checks.

## Milestone 4: graphs of maximum degree three (`PLAN-4.md`, complete with documented deviations)

The project's first graph-isomorphism theorem: Luks's polynomial-time test for connected graphs
of maximum degree at most three, by a layered `2`-group reduction to string isomorphism, run
with Luks's strategy and the Schreier–Sims backend. The milestone of `PLAN-4.md` is complete
with the deviations recorded in items 1, 2 and 5.

1. **Layers.** For graph data of maximum degree three (`GraphData.Valid`), rooted at an edge of
   each graph in the union `Z = X ⊔ Y`:
   - levels by relaxation to a fixpoint, characterized by `IsLevels` (`levels_spec`);
   - the layer groups `A_r` (`AutR`): `A₀` is generated by three involutions of the four roots
     (`closure_gens0`); every `A_r` is a `2`-group (`isPGroup_autR`). **Deviation:** the plan's
     "`A₀` is dihedral of order 8" is not proved as such; the algorithm needs only the
     generators and the `2`-group property (every element of `A₀` has order dividing 4,
     `autR0_pow_four`);
   - **the extension criterion**: the elements of `A_r` that extend to `A_{r+1}` are those
     preserving the layer string on the subsets of level `r` with at most three points
     (`mem_HR_iff_extends`, with `HR` read on the subsets by `xstr_iff`), and `A_{r+1}` is
     generated by the canonical lifts of generators of `HR r` and the twin transpositions
     (`autR_succ_eq`);
   - **the swap criterion**: an isomorphism sending one root edge to the other exists exactly
     when some generator of `A_{2n}` moves a root to the other side (`iso_iff_exists_gen`).
2. **Programs.** Every component is a program of the cost language with an exact value and an
   explicit polynomial cost, and is well-formed: levels (a loop paid by the sum of the levels),
   the union, level lists, the canonical triples of the subsets, the position, offset and index
   arrays, the layer string, the induced generators, readback by truncation, lifts, twin swaps,
   the swap test and the validity and connectivity checks. The induced action is an injective
   homomorphism on any group mapping the level into itself (`indHom`), with truncation to the
   first `N` points as a left inverse (`readback`).

   **Deviation.** The answer generators of each layer are not compressed by `generate` at
   degree `2n`: their number is bounded by the string-isomorphism solver's own output bound
   (`D²` for the layer's domain size `D`), so every layer has at most
   `genBound N = (N + N³)² + N²` generators. The bound stays polynomial.
3. **The algorithm.** `mainProg` (the plan's `gi3Prog`) runs inside the procedure `luksBody`.
   For each directed edge of `Y` it computes the levels, the generators of `A₀`, `2n` layer steps
   (each calling `solveEntry`), and the swap test, and returns the first isomorphism found
   (`RunsWithin.mainProg`). One layer step is `RunsWithin.stepProg`, the edge test
   `RunsWithin.edgeProg`.
4. **Concrete theorems** with the Schreier–Sims backend, with no assumed oracle:
   - **`gi3_checked`** (the plan's `gi3_spec`): the checked entry `gi3Checked`, on every
     input, returns `none` exactly when the input is not valid connected data of maximum
     degree three; otherwise it returns `some none` exactly when there is no isomorphism, and
     `some (some arr)` only when `arr` lists the `n` values of an isomorphism. Connectivity
     is `Conn`, which holds vacuously on no points: the empty input `(0, #[], #[])` is
     accepted, with answer `some #[]`, although mathlib's graphs on `Fin 0` are not
     connected. **The cost is at most `17500 (2n + 1)²⁶`**
     (`checkedCost_le`; one layer step costs at most `8100 (N + 1)²⁴`);
   - **`gi3_simpleGraph'`**: the same for mathlib's simple graphs. For connected simple graphs
     `G` and `H` on `Fin n` with every degree at most three, given to the entry by their
     adjacency lists (`GraphData.ofSimpleGraph`, valid by `valid_ofSimpleGraph`), the result is
     `some none` exactly when there is no isomorphism `G ≃g H`, and `some (some arr)` gives an
     isomorphism with values `arr`. `gi3_simpleGraph` states it for valid data through
     `GraphData.toSimpleGraph` (`nonempty_iso_iff`, `conn_iff_connected`).
5. **Checks** (`GraphIsoChecks/Graph.lean`), tied to `gi3_checked` by `runGI_spec`:
   - kernel-evaluated runs on one point and on none (the empty input, accepted);
   - interpreter runs against brute force over all `n!` permutations, with every returned
     isomorphism checked: `K₂`; `P₃` and `P₄` against relabellings; `P₄` against the star
     `K₁,₃` (same number of edges, not isomorphic); `K₄` against itself with permuted lists;
   - five invalid inputs rejected by the validity and connectivity checks.

   **Narrower than the plan.** `K₃,₃` against the prism is not checked: its second layer has a
   domain of about a hundred points, beyond the interpreter. The trees are `P₃`, `P₄` and
   `K₁,₃`. Each run on two or more points costs 30–300 million units (12–110 seconds),
   dominated by the first layer's domain of `2n + 14` points; a non-isomorphic pair runs the
   edge test for every directed edge of `Y`. `C₄` against the paw (437 million units, 161
   seconds) was run once outside the build and agrees with brute force.
6. **Audit and docs.** The build lists the axioms of the milestone's principal theorems: only
   `propext`, `Classical.choice` and `Quot.sound`. The theorem map is updated.

**Validation.** A clean `lake build --wfail` succeeds (1722 jobs) in about eleven minutes,
with mathlib prebuilt; the graph checks take about four minutes of that. The audit covers 5957
declarations in 107 modules. No Lean line exceeds 100 characters, and the sources contain no
`sorry`, `admit`, `native_decide`, `noncomputable`, `Classical.choose`, axiom or option
override. Size: about 27,000 lines of library code (8,000 of them for this milestone) and
2,500 lines of checks.

**How the layer step works.** On level `r` with `ℓ` points, the instance has `N + m` points:
the graph's `N` points and the `m = ℓ + C(ℓ, 2) + C(ℓ, 3)` nonempty subsets of the level with at
most three points, each as its canonical triple (`Subsets.lean`). A subset's image is the
canonical triple of the image positions, found through an index array keyed by the triple
(`get_cidxArr`). The layer string counts the new points with each neighbourhood and marks the
edges inside the level. The solver returns the subgroup preserving it; truncation to the first
`N` points gives generators of `HR r` (`readback`).

**What is not covered.** Graphs of larger valence (Luks's general theorem needs the bound on
primitive sections of `Γ_d` groups, the Babai–Cameron–Pálfy theorem). Disconnected graphs are
milestone 5.

## Milestone 3: Luks's strategy (`PLAN-3.md`, complete)

A second solver procedure, `luksBody`, whose cost does not depend on the group order. On a
transitive window it computes a maximal block system and runs the block reduction, branching
over the cosets of the block kernel. The number of cosets is the order of a primitive group
on the blocks. The milestone of `PLAN-3.md` is complete with the documented deviations:
there is no separate correctness theorem without backend bounds (item 2), and the check
suite is narrower than planned (item 5).

1. **Maximal block systems.** `maxBlocksProg` makes no backend calls. For a group transitive
   on a window of at least two points, `maxBlocks_spec` gives:
   - a block list that the group permutes, with at least two blocks of equal size;
   - a primitive action of the group on the blocks (`MulAction.IsPreprimitive` of the image
     of `blockHom`).

   The cost is at most `maxBlocksCost n m s = O(m² (n + m + s))` (`RunsWithin.maxBlocksProg`).
   It rests on `closure_spec`: the closure of a partition and a pair is the finest invariant
   coarsening joining them.
2. **The strategy.** `luksBody` is well-formed (`luksBody_wf`). It calls only `orbits`,
   `generate`, `kernel` and `cosetReps`. Correctness is by induction on the window size
   alone. Unlike the plan's `luks_correct`, there is no separate correctness theorem without
   backend bounds: correctness is part of `luks_spec`. For every group it holds with the
   Schreier–Sims backend (`solve_luks_any`).
3. **The cost bound.** `luks_spec` assumes `PrimBounded G₀ c` (primitive sections of degree
   `k` have order at most `k ^ c`) and `LuksBounds` with `n ^ c ≤ R`. Under these, the cost
   is at most `luksBound Q c m = 2 Q m ^ (c + 1) − Q` for a window of size `m ≥ 1`, and `Q`
   for the empty window. The entries are `luksEntry_spec`,
   `luksChecked_spec` and `luks_backend_refinement`.
4. **Concrete theorems** with the Schreier–Sims backend, with no assumed oracle:
   - `solve_luks`, `solve_luks_checked`;
   - `solve_luks_any`: every group, with `c = n` (`primBounded_degree`);
   - **`solve_luks_nilpotent`: for nilpotent groups, in particular `p`-groups, the cost is
     at most `6640 (n + 1)⁸ + 60 L (n + 1)²`.** A primitive nilpotent group has order equal
     to its degree (`card_eq_of_isPreprimitive_of_isNilpotent`).

   The unit is `luksSimsQ n R ≤ 3200 (n+1)⁶ + 50 R (n+1)⁴ + 13 R² (n+1)⁴` (`luksSimsQ_le`).
5. **Checks** (`GraphIsoChecks/Luks.lean`).
   - A kernel-evaluated run at degree 2 tied to `solve_luks_any`, with a brute-force
     comparison.
   - `maxBlocks` on eight transitive groups, against their expected maximal blocks.
   - 4,224 runs against brute force:
     - the sweep families of degrees 1–4, with the identity and one cycle as outer
       representatives in degrees 1–3 and the identity in degree 4;
     - selected groups of degrees 6–8, and `PSL(3, 2)` with distinct symbols.
   - Iterated wreath products of `C₂`:
     - on 8 points (order 128), against brute force, with the default strategy alongside;
     - on 16 points (order 32768), against the solutions found by enumerating the group
       from a complete table.

   Their costs are within the nilpotent bound.

   **Narrower than the plan.** There is one kernel-evaluated run, not several. The sweep uses
   fewer outer representatives than the default strategy's sweep. Costs are checked against
   the nilpotent bound only on the wreath products.
6. **Audit and docs.** The build lists the axioms of 21 more principal theorems: only
   `propext`, `Classical.choice` and `Quot.sound`. The theorem map, backend contracts and
   remaining work are updated.

**Validation.** A clean `lake build --wfail` succeeds (1680 jobs) in about seven minutes, with
mathlib prebuilt. The Luks checks take about four minutes of that. The audit covers 4374
declarations in 83 modules. No Lean line exceeds 100 characters, and the sources contain no
`sorry`, `admit`, `native_decide`, `noncomputable`, axiom or option override.

**What is not covered.** `PrimBounded` for groups with composition factors in `Γ_d` is the
Babai–Cameron–Pálfy theorem, which is not formalized. For such groups `solve_luks` holds with
that bound as a hypothesis.

## Milestone 2: the Schreier–Sims backend (`PLAN-2.md`, complete)

The string-isomorphism library now has a verified group backend whose charges are polynomial
in the degree. Every completion criterion of `PLAN-2.md` is met. The checks cover less than
the plan's verification list; item 5 records the difference.

1. **Implementation.** `ssImpl` implements all eight operations over the empty signature,
   including `mem`. It is well-formed (`ssImpl_wf`), and `ssOracle` meets every contract
   (`ssOracle_meets`).
2. **Charges.** `ssImpl_implements` proves that the programs compute the oracle within the
   schedule `ssB`. Every charge is an explicit polynomial in the degree, the generator counts
   and, for `cosetReps`, the number of representatives. For example
   `genCost n L ≤ 100 (n+1)⁶ + 60 L (n+1)²`.
3. **Bounds.** `ssBounds n G₀` gives the solver's backend bounds with `s = n²` for every
   ambient group, independently of its order.
4. **Concrete theorems.** These are closed programs with no assumed oracle:
   - `solve_sims`: correctness, and cost at most `simsCost n L m N`, which `simsCost_le`
     bounds by `13 + 100 (n+1)⁶ + 60 L (n+1)² + 800 (m+1) N (n+1)⁶`;
   - `solve_sims_checked`, the validating entry, on every input;
   - `restrict_sims` and `blockReduce_sims`.
5. **Checks** (`GraphIsoChecks/Sims.lean`).
   - Four kernel-evaluated solver runs at degree 3, tied to `solve_sims`, with brute-force
     comparisons; kernel-evaluated table orders for `S₃` and `D₄`.
   - Tables of `S₁₀`, `A₁₀`, `M₁₁`, `M₁₂`, `S₄ ≀ S₃` and `PSL(3, 2)` with their known
     orders.
   - The operation programs on `S₈`, `M₁₁` and `PSL(3, 2)`, within their charges.
   - 12,888 solver and reduction runs agreeing with brute force: sweeps through degree 4 for
     the solver and degree 3 for the reductions, and selected groups of degrees 6–8,
     including `PSL(3, 2)` on the Fano plane.

   **Narrower than the plan.** Against `PLAN-2.md`'s verification list:
   - Kernel-evaluated solver runs stop at degree 3. The planned runs on `C₄`, `D₄`, `A₄`,
     `S₄`, an intransitive group and a degree-5 group are not kernel-evaluated; the
     degree-4 groups appear only in the interpreter sweep.
   - The interpreter sweep stops at degree 4 (solver) and degree 3 (reductions), not 5. It
     compares answers with brute force only, not with the reference backend.
   - `S₁₀`, `A₁₀`, `M₁₁`, `M₁₂` and `S₄ ≀ S₃` are checked through their tables and the
     operation programs, with no solver runs on them. The solver's cost is linear in the
     group order (a run on `S₆` costs about 12 million units), so solver runs stop at
     degree 8 and groups of order at most 168.
6. **Audit and docs.** The build lists the axioms of the new principal theorems: only
   `propext`, `Classical.choice` and `Quot.sound`. The theorem map, backend contracts and
   remaining work are updated.

**How it works.** A Sims table has a full base, so a successful sift leaves the identity.
- *Construction.* It is a worklist over Knuth's closure criterion, which needs no group
  order. Termination counts filled slots, at most `n²` of them.
- *Correctness.* It rests on the closure criterion: if `τ σ ∈ Γ_k` for the entries of row
  `k` and of later rows, then each `Γ_k` is a group. With the generators in `Γ₀`, `Γ_k` is
  the pointwise stabilizer of the first `k` base points (`complete_of_closed`).
- *Costs.* They come from the executed programs, through a generic loop lemma paid by a
  potential (`RunsWithin.loop_pot`).

**What it does not change.** The default strategy's bound `solveBound Q m N` is still linear
in the group order `N`, so solver runs remain exponential in `n` for large groups. A
polynomial strategy for bounded composition factors (Luks) is the next step.

Validation at this checkpoint:

- A clean `lake build --wfail` succeeds (1661 jobs) in about three and a half minutes, with
  mathlib prebuilt. The Schreier–Sims checks take about a minute and a quarter of that.
- The logical audit passes for 3936 project declarations in 71 modules. Every source file is
  in the audited import closure.
- A source scan finds no `sorry`, `admit`, `native_decide`, `noncomputable`,
  `Classical.choose`, `implemented_by`, heartbeat or recursion-depth overrides, and no lines
  over 100 characters.
- Size: about 16,100 lines of library code (4,700 of them for this milestone) and 2,100 lines
  of checks.

## Milestone 1: string isomorphism (`PLAN.md`, complete)

Phases 0–7 of `PLAN.md` are complete, so the string-isomorphism milestone is complete. See:

- `theorem-map.md` for the theorem-by-theorem map, PLAN's final targets and the hypotheses of
  the principal theorems;
- `backend-contracts.md` for the data, cost model, contracts and reference backend;
- `efficient-backends.md` for the work that remains for faster backends.

The completion criterion of `PLAN.md` is met as follows:

- **An executable solver with a proved backend.**
  - `solve_reference` covers the closed solver over the empty signature, with the reference
    backend substituted and no assumed oracle. On every valid input it returns `none` or a
    representative and generators describing all isomorphisms, within
    `referenceCost n N |gs| |W|`.
  - `solve_reference_checked` does the same for the validating entry, on every input.
- **The same proofs for a backend with costs as hypotheses.**
  - `solve_correct`, `solve_none_iff`, `solve_some_group`, `solve_cost_le`, `solveEntry_spec`
    and `solve_backend_refinement` take the contracts and `BackendBounds` as explicit
    hypotheses.
  - So do the reductions and their compositions with the solver.

The six required deliverables:

| Deliverable | Where |
|---|---|
| 1. Semantics and exact correctness theorems, full and windowed | `Semantics/`, phase 1 |
| 2. Finite representations with proved interpretations | `Representation/`, phase 2 |
| 3. Group-operation interface with semantic, cost and output-size contracts | `GroupOps/Interface.lean`, `Solver/Cost.lean` |
| 4. Correctness and cost composition for orbits, subgroup branching, and restriction with lifting (and block systems) | `Reductions/`, `Solver/Compose.lean`, phases 4, 5, 7 |
| 5. Terminating solver using them, with a verified enumeration backend | `Solver/`, `GroupOps/Enumeration*.lean`, phase 6 |
| 6. Boundary between proved backend costs and assumptions about future backends | `backend-contracts.md` (proved versus assumed), `efficient-backends.md` |

Phase 7 delivers the integration:

- **Compositions** (`Solver/Compose.lean`). `SubSolves.solve` turns `solve_spec` into the
  sub-solver hypothesis of the reductions.
  - `restrict_solve_spec`: the restriction reduction with the solver as sub-solver, called at
    the window's degree `m`.
  - `blockReduce_solve_spec`: the block reduction with one solver call per block in each
    coset of the block kernel.
- **Reference instantiations** (`Solver/ReferenceCompose.lean`). `restrict_reference` and
  `blockReduce_reference` prove correctness and explicit finite cost bounds for the closed
  reduction programs inside `referenceSolver`. The bounds are `restrictReferenceCost` and
  `blockReferenceCost`, with `R = N / |K|` branches.
- **Concrete runs tied to the theorems.** `runRestrict_spec` and `runBlocks_spec` do this for
  the phase-5 runs. The coverage runs (`GraphIsoChecks/Coverage.lean`) handle the
  verification-list cases not covered before: the trivial group, a singleton domain, constant
  strings, linked orbits, and the dihedral group solved directly.
- **Comparisons over families** (`GraphIsoChecks/Sweep.lean`). 25,126 interpreter runs of the
  solver and both reductions, in degrees 1–4, agree with an independent brute force on answer
  sets, data validity and the proved cost bounds.
- **Final audit.** The build lists the axioms of the 18 principal theorems by name: only
  `propext`, `Classical.choice` and `Quot.sound`.

The default solver does not use the restriction or block reductions; they are the library
reductions for later strategies such as Luks's.

The audit of commit 85f026a reported two issues, both fixed:

1. **Eager evaluation of an untaken branch.** `eval` passed both branches of `caseList` as
   arguments, so compiled code evaluated the untaken one. On `G = ⟨(1 2)⟩` with window
   `[0, 1, 2]`, that branch re-solved the unchanged problem: the running time grew with the
   fuel while answers, traces and costs stayed the same. `eval` now matches before evaluating
   a branch, which also covers `caseOption` and `loop`. `GraphIsoChecks/Execution.lean` times
   compiled runs at small and large fuel, and fails against the old evaluator.
2. **Input contract.** `solveEntry` checks nothing and decodes strings totally. This is now
   documented, and a validating entry is added:
   - `solveChecked` checks the full contract `InputValid q`, which is `InstanceData.validB`.
     It does so in the cost language, charged by `validCost`.
   - `solve_reference_checked` holds on every input with no hypotheses. The result is `none`
     exactly on invalid input; otherwise it is a correct answer.

   The alphabet bound is checked, but it enters no complexity statement yet.

The audit of commit 8a326e6 confirmed the phase-5 claims and reported one issue, fixed: the
trace sums (`Trace.localCost`, `callCost`, `cost`) were `List.sum`s of the mapped trace, which
compiled to non-tail recursion. On the 1.8 million events of the block reduction for `S₄` on
the empty window, the interpreter ran out of stack while summing. They are now left folds,
restated as sums by `localCost_eq_sum`, `callCost_eq_sum` and `cost_eq_sum`, and
`GraphIsoChecks/Execution.lean` sums that trace; with the old sum the check aborts the build.

Validation at the milestone-1 checkpoint (commit c084d83):

- `lake build --wfail` succeeds (1645 jobs).
- The logical audit passes for 3023 project declarations in 55 modules, allowing only
  `propext`, `Classical.choice` and `Quot.sound`. Every source file is in the audited import
  closure.
- A source scan finds no `sorry`, `admit`, `native_decide`, `noncomputable`,
  `Classical.choose`, `implemented_by`, heartbeat or recursion-depth overrides, and no lines
  over 100 characters.
- A clean build of the project, with mathlib prebuilt, takes about two and a half minutes.
  Of that, the sweep takes about a minute and the coverage runs about half a minute.

Size: about 11,400 lines of library code and 1,800 lines of checks.

Known limits (details in `efficient-backends.md`):
- the cost bounds depend on the group order `N`, which can reach `n!`. The default strategy's
  bound `2 m N Q - Q` stays linear in `N` even with an efficient backend;
- naturals are unit-cost words;
- termination gives the existence of enough fuel, but there is no runner with a proved fuel
  bound;
- nothing specific to Babai's algorithm is formalized yet: the graph-to-string reduction, an
  efficient group backend, local certificates, Split-or-Johnson.

## Design decisions

1. **Semantics** over an arbitrary type `Ω` with `W : Set Ω`, `G : Subgroup (Perm Ω)`, left
   cosets `σ • (G : Set _)`. `aut` takes the invariance proof as an argument.
2. **Representations** are plain arrays and lists of naturals whose Lean types coincide with
   the cost language's value types (`Ty.perm.denote = PermData`, etc.), with total
   denotations and `validB` checkers proved equivalent to validity.
3. **Cost language**: a PHOAS deep embedding, with an explicit relational well-formedness
   witness (`Proc.Wf`, Chlipala-style) required of accepted procedures. The PHOAS type alone
   does not enforce parametricity (classical case analysis can inspect `var`); the witness is
   what excludes computation outside the charged constructors. Evaluation is fuel-bounded
   (fuel is not cost) and returns the trace. Naturals are unit-cost words; a later
   bounded-word interpretation will need bounds on intermediate values.
4. **Groups** carry their degree, generators and opaque backend data of a backend-chosen
   value type; the denotation depends only on the generators.
5. **Backend substitution** is a syntactic replacement of calls by implementations. The
   client's recursion type is visible to an implementation, so calls back into the client
   are excluded explicitly: accepted implementations satisfy `Impl.Wf`, which forbids
   `recur`. Well-formedness is preserved by substitution.
6. **Restriction** is expressed through the `kernel` and `lift` operations plus local
   reindexing in window order (`WinData.reindex`, positions `WinData.pos`); images are
   generated with `generate`. The semantic restriction is a homomorphism on `G` transported
   along the reindexing (`restrictHom`), so the lifting theorem is `comap ρ (map ρ ⟨L⟩) =
   ⟨L⟩ ⊔ ker ρ` (`Subgroup.comap_map_eq`).

7. **The solver** is one recursive procedure over the backend signature. Its termination,
   correctness and cost are proved together (`solve_spec`) by strong induction on the window
   size and then on the group order. Every case either shrinks the window (orbits) or keeps it
   and passes to a point stabilizer of order `N / k`, `k ≥ 2`. The cost bound
   `2 m N Q - Q` counts invocations of the recursion tree (each splitting invocation has at
   least two children) and charges each one the worst-case node cost `Q`.
8. **Backend hypotheses are relative to the input group**: `BackendBounds X DV n s G₀`
   bounds the charges and output generator counts only for subgroups of `G₀`. This is what a
   uniform bound for the reference backend needs: its charges grow with the group order.
9. **The reference backend** represents a group by all its elements, as both generators and
   data. So `s = N`; no generator compression is needed for termination or bounds, at the cost
   of loose bounds (`referenceCost 3 6 2 3 = 2506915` for an actual cost of 8689 on `S₃`).

10. **The block kernel is not a backend primitive.** It is the kernel of the induced action
    on blocks: every generator is extended to degree `n + k`, permuting `k` extra block points
    as it permutes the blocks (`extendHom`). The existing `kernel` operation then gives the
    pointwise stabilizer of the block points, and truncation to the first `n` points recovers
    the block kernel (`denote_truncTo`). Correctness of the block reduction needs only that
    the blocks are invariant under `K`. That `G` permutes the blocks (`PermutesBlocks`) is
    needed only for the induced action.

11. **Composition goes through the sub-solver hypothesis.** The reductions take any
    sub-solver satisfying `SubSolves`. `SubSolves.solve` derives that hypothesis from
    `solve_spec` for a recursive call of the solver, so the compositions need no new
    induction. Their sub-calls are bounded by `solveBound` at the sub-instance's window size
    and the input group's order.
12. **The Schreier–Sims backend stores no data.** Every operation that needs a stabilizer
    chain rebuilds a complete table from the generators. Stored chains would need an
    invariant carried through every output group and every reduction; rebuilding costs a
    polynomial factor only.
13. **Full bases and slot tables.** A base order lists all `n` points and the table has
    `n × n` slots, so a successful sift leaves the identity, and the construction terminates
    by counting filled slots. Output groups are generated by table entries, which bounds
    their generators by `n²` without a separate filter.
14. **Loops are paid by potentials.** `RunsWithin.loop_pot` turns a potential, which drops by
    at least the charge of each iteration, into a cost bound for the whole loop, and also
    bounds the iterations. The construction's potential is amortized: each pending item
    carries one sift, and each fillable slot carries the items its insertion queues.
15. **Maximal blocks are computed locally**, not by a new backend operation. The closure of a
    partition and a pair is a worklist on label arrays over the generators alone. One pass
    over the window suffices, because closures are monotone in the input partition. The
    signature `groupSig` and both backends are unchanged.
16. **The cost hypothesis is about sections.** `PrimBounded G₀ c` bounds every primitive
    homomorphic image of a subgroup of `G₀`, in mathlib's terms (`MulAction.IsPreprimitive`
    of `φ.range`). The strategy meets such images as the block action of the current group
    on a maximal system. The number of cosets of the block kernel equals the image's order
    (`card_range_mul_card_blockKernel`).
17. **`luksBody` reuses the milestone-1 block reduction unchanged.** `blockReduceProg`
    already takes the block list as data and computes the block kernel by the induced
    action. The strategy only supplies a maximal block list and the recursive sub-solver.

## Observations from phase 7

- **The reductions need nothing new from the solver.** Composing them with it needed no
  change to the solver or its proof: `solve_spec` already quantifies over every valid instance
  of a degree with its own backend bounds. The restriction's sub-call is covered by
  instantiating it at degree `m`.
- **Kernel evaluation** is the bottleneck for concrete checks. A full-window `S₃` solver run
  takes about 4 s, and constant strings on `S₃` (cost 30480) about 15 s. Broad comparisons
  therefore run in the interpreter (about 0.8 ms per solver run in degree 3, and up to about
  30 ms per block-reduction run in degree 4).
- **The reference bounds are loose.**
  - The phase-5 restriction run: cost 3283 against a bound of 245677.
  - The block run: cost 26133 against a bound of 30233029.

## Observations from milestone 2

- **Kernel evaluation of the Schreier–Sims programs is feasible** for degree 3: the four
  solver runs and two table constructions take about half a minute together.
- **The interpreter runs the programs quickly enough for broad checks.** The 12,888 brute-force
  comparisons take about a minute.
- **The proved charges are loose by about a factor of 20–30** on actual runs (`generate` on
  `M₁₁`: cost 2,065,437 against a charge of 60,875,390). They are worst-case polynomials in
  the degree.
- **The heartbeat budget shaped the proofs.** Long program chains in one declaration exceed
  it, so each branch of a loop body has its own specification lemma, and well-formedness is
  proved program by program (`GraphIso/Sims/Wf.lean`).

## Observations from milestone 3

- **Luks's per-node overhead is large at small sizes.** On the wreath product of `C₂` on 8
  points (order 128), Luks's strategy costs 6.6 million units against 2.3 million for the
  default strategy. Each node computes the block kernel at degree `n + k` and a quadratic
  coset search.
- **The order of the group stops mattering.** On 16 points (order 32768), Luks's strategy
  costs 172 million units, about 70 seconds in the interpreter. The default strategy's bound
  is linear in the group order there.
- **Primitive groups are the expensive case.** `PSL(3, 2)` has trivial block kernel on its
  point blocks, so the block reduction branches over all 168 elements. One run takes about 40
  seconds.
- **Kernel evaluation reaches degree 2.** The degree-2 run costs 12,976 units and takes about
  12 seconds; degree-3 runs cost 50,000–90,000 units.

## Observations from milestone 4

- **The first layer dominates.** At level 0 the four roots give 14 subsets, so the first
  string-isomorphism instance has `2n + 14` points. Its Luks run costs about 30–40 million
  units even for a group of order 8; later layers on small levels are cheap.
- **Ordered triples were too slow.** A first version used all `ℓ³` ordered triples of the
  level (64 for the roots). On `P₃` the run did not finish within twenty minutes; canonical
  triples of the subsets (14 for the roots) bring it to about 17 seconds.
- **The closed form is far from the runs.** The bound `17500 (2n + 1)²⁶` is about `2.6 · 10²²`
  for `n = 2`, where `K₂` costs `3.2 · 10⁷`, and about `1.1 · 10²⁹` for `n = 4`, where the runs
  cost `1.0`–`3.0 · 10⁸`.

## Observations from milestone 5

- **Components cost almost nothing.** The components, component data and gluing cost a few
  thousand units on small graphs (three isolated points: 1,209). Each connected test on two or
  more points costs what milestone 4's entry costs: 30–300 million units on these small
  graphs.
- **Size first.** Components of different sizes are never tested, so `2K₂` against `P₄` costs
  3,194 units; a mismatch of equal sizes runs a full connected test (`K₃` against `P₃`: about
  130 million units).
- **The bound is dominated by the pairs.** `allCost n` is `16900 n² (2n + 1)²⁶` plus a
  polynomial of degree four: at most `n²` candidate pairs of components, each bounded by the
  closed form of milestone 4's `mainCost`, `16900 (2n + 1)²⁶` (`mainCost_le`).

## Observations from milestone 6

- **Luks's strategy is not cheaper on small solvable groups.** On the checked groups it costs
  1.4 to 6.7 times the default strategy.
  - The primitive `AGL(2, 3)` on nine points (order 432) agreed with brute force at
    841 million units, about eleven minutes, against 7.6 million for the default strategy.
    That run is not in the build.
  - On a primitive window the block kernel is trivial, so Luks's strategy branches over one
    coset per group element, each with a block reduction.
  - The polynomial bound concerns the growth in the degree.
- **The exponent is crude.** `12 s + 1` against the Pálfy–Wolf exponent `3.25` for every
  primitive solvable group. For `{2, 3}`-groups, `c = 13` and the solver's bound is
  `(n + 1)⁴⁴`. The argument trades sharpness for elementary linear algebra: Maschke's
  theorem and commutative algebra in place of Clifford theory and extraspecial groups.
- **Statements first.** The five group-theory modules were written as stubs with fixed
  statements and then proved independently. Only the statements of the stubs crossed module
  boundaries.

## Next steps

1. **Babai's recursion**, continued: milestone 14, stage 14j (`PLAN-14.md` §4): the main
   recursion with its quasipolynomial cost. Milestones 15 and 16 then discharge the interfaces
   (Pyber's Lemma 12, Wielandt's bound). The completion theorem will have no hypothesis.

Optional:
- a sharper exponent for primitive solvable groups (Pálfy–Wolf);
- a cheaper first layer (for example, starting the layers at the root edges' neighbourhoods);
- refinements of the backend: stored chains, a cheaper construction, Jerrum's filter;
- a bounded-word cost model with the alphabet bound;
- a runner with a proved fuel bound;
- tighter reference bounds.
