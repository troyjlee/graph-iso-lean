# Conventions

These conventions are fixed for the whole library. Phase 0 checks that exercise them are in
`GraphIsoChecks/Conventions.lean`; the exact mathlib signatures relied on are restated in
`GraphIsoChecks/MathlibAPI.lean`.

## Toolchain

- Lean `leanprover/lean4:v4.35.0-rc2`, mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`, as a
  git dependency pinned by commit.
- `autoImplicit = false`. Build with `lake build --wfail`; the full build is
  `scripts/guard.sh -m 64000 -t 10800 -- scripts/build-seq.sh --wfail`.
- **Memory.** Some kernel checks need 20–40 GB each (stage 19b's measurements in
  `docs/status.md`). Every heavy Lean run (a build, `lake env lean` on a check file, profiling)
  goes through `scripts/guard.sh`: a global lock runs one guarded command at a time, and the
  process tree is killed above a memory cap or a time limit (`-m MB`, `-t s`), with one line
  per run logged to `~/.cache/graphiso-lean-guard/runs.log`. `scripts/build-seq.sh` builds the
  library with Lake's parallelism, then the check modules one at a time, dependencies first.
  Never build check modules in parallel.
- `GraphIsoChecks/AxiomAudit.lean` requires every project declaration to depend only on
  `propext`, `Classical.choice` and `Quot.sound`, and requires every source file to be in the
  audited import closure. No `sorry`, `admit`, project axioms or `native_decide`; concrete
  checks use kernel `decide`.
- **Large executions** are kernel-checked in pieces (`GraphIsoChecks/Exec.lean`).
  ``run_cmd execRuns `n (← `(RunsS O body f p)) O body f p cfg`` adds
  `n : RunsS O body f p v s` for the actual program `p`, and the check is the ordinary theorem
  `∃ v s, RunsS O body f p v s ∧ Q v s = true := ⟨_, _, n, by decide +kernel⟩`. The compiled
  interpreter only proposes the split and the intermediate values. Every piece (at most
  `cfg.budget` trace events, checked by the kernel's evaluation) and every composition step is
  its own declaration, elaborated under the default budgets. A new check whose single kernel
  check would exceed about 16 GB uses this form.
- **No heartbeat overrides**, in any form: no `set_option maxHeartbeats` and no resetting of the
  heartbeat baseline (`withCurrHeartbeats`). Work that does not fit one declaration's budget is
  split into several declarations.
- **Lean's module system** (`PLAN-19.md` §3–§4). Every library and check file starts with
  `module`, imports with `public import`, and opens `@[expose] public section` after its module
  docstring. Every declaration is then public, and every definition's body is visible to the
  modules importing it, as before the port. `scripts/port-module.py` applies these changes and
  is idempotent. Three consequences:
  - A tactic or lemma must be imported where it is used. Mathlib's modules import their tactics
    privately, so `nlinarith`, for instance, no longer arrives through other imports.
  - A Mathlib definition whose body Mathlib does not expose (`List.insertionSort`) cannot be
    unfolded in a module, by `simp`, `decide` or the kernel. Use its lemmas
    (`List.insertionSort_cons`). Where a concrete computation needs the body, add a private
    `import all` of the defining module (`Main/CJohnOps.lean`: `import all
    Mathlib.Data.List.Sort`).
  - Code evaluated at elaboration time (`#eval`, `#guard`, `run_cmd`, such as `execRuns`) runs
    in the meta phase, which sees only the code of modules imported with `meta import`. A check
    file that evaluates code therefore also has `meta import M` for each of its imports `M`
    (`scripts/port-module.py --meta`). Its own definitions need nothing: `TMGI`'s
    `execRunsParts` runs in the same file. Conversely, ordinary code may not use `meta`
    definitions, such as Mathlib's `ToExpr` instances: `MainM4`'s derived `ToExpr Tok` takes
    core's `ToExpr Unit` (a local instance of high priority), not Mathlib's `ToExpr PUnit`.
  - A module sees an imported definition that its module does not expose as an axiom, to the
    elaborator and to the kernel alike, so `decide` and `decide +kernel` stop there. The
    library's code reaches four such definitions in core and Mathlib: `Array.range`,
    `List.mergeSort`, `List.insertionSort`, `Nat.land`. Every check file that reduces the
    library's code (`decide`, `execRuns`) imports their modules with `import all`
    (`scripts/port-module.py --bodies`), which restores the bodies the checks saw before the
    port. Without it, `Cost`'s `decide` examples stop at `Array.range`, and the kernel rejects
    `GraphQP`'s `execRuns` pieces.

  `GraphIsoChecks/AxiomAudit.lean` must see private declarations too. A module sees them only
  in the modules it imports directly with `import all` (not in their imports), so the audit's
  header imports every module of the package that way. `scripts/gen-audit-imports.py`
  generates the header (`--check` reports a stale one); a new file needs a rerun. The audit
  fails on any module file not loaded with all its data.

## The Palomar statement

`PLAN-19.md` §5–§7. For the Palomar registry, the single-tape theorems are stated with
definitions that use Mathlib only.
- `GraphIso/Palomar/Statement.lean` imports Mathlib only and holds the statement's definitions
  exactly as `PLAN-19.md`'s appendices give them. Changing them changes the advertised claim:
  it needs the user's approval, recorded in the plan.
- The theorems are proved in `GraphIso/Palomar/Bridge.lean` under names ending in `_proof`
  (`gi_singleTape_proof`, `gi_coset_singleTape_proof`, `cosetWord_injective_proof`). This
  repository has no `sorry`.
- Palomar's `Challenge.lean` (the statement file's text, then the theorems with `by sorry`) and
  `Solution.lean` (importing the bridge, with `theorem gi_singleTape : … := gi_singleTape_proof`)
  are generated outside this repository (stage 19e). Comparator matches the challenge's
  constants with the solution's by name and value, and the solution receives the definitions
  from `GraphIso.Palomar.Statement`. So the definitions must not be renamed, moved or copied
  into another namespace: two copies of an inductive type are different types.
- The statement's `Sym` derives nothing; `GraphIsoChecks/Palomar.lean` derives `DecidableEq` for
  its own checks.
- **The published snapshot** is written by `scripts/palomar-snapshot.sh OUT` (`--build` also
  builds it; `scripts/palomar-snapshot.py` documents every step and check). It copies the
  tracked files, committed, except the audit reports, the audit evidence, the loop's state and
  the paper PDFs; adds `README.md`, `LICENSE` and `lean/formalization.yaml` from `palomar/`; and
  generates `Challenge.lean` (from `Statement.lean` and `PLAN-19.md`'s appendices),
  `Solution.lean`, `comparator.json` and the lakefile's two libraries. It also installs the
  manually dispatched Palomar preflight workflow, pinned to a full verifier commit. The
  reference check uses whole-document CommonMark parsing (with tables) and HTML attribute
  parsing for Markdown files and Lean comments. Local link/image destinations and reference
  definitions must resolve inside the snapshot; URL escapes are decoded, and queries and
  fragments are dropped. Code examples are not links. External URLs, fragment validity and
  arbitrary Markdown extensions are outside this check. Documents cite papers by arXiv
  identifier or URL, and a path that names another repository's file must be listed in the
  script with its reason.
  The statement must stay identical to the appendices. While `palomar/formalization.yaml`
  starts with its `DRAFT` line, only `--draft` snapshots are written: the author confirms the
  metadata first.
  Before using the script, install `scripts/palomar-snapshot-requirements.txt` into a Python
  3.10-or-newer virtual environment and activate it. The script does not install dependencies
  automatically. From the repository root, its regression checks run with
  `python3 -m unittest discover -s lean/scripts -p test_palomar_snapshot.py`.

## Permutations

- Permutations of a domain `Ω` are `Equiv.Perm Ω`, multiplied by composition:
  `(g * h) u = g (h u)` (`Equiv.Perm.mul_apply`). So `g * h` applies `h` first.
- `g⁻¹ u = g.symm u`. `GraphIso.perm_apply_inv_self` and `perm_inv_apply_self` are the simp
  lemmas for `g (g⁻¹ u) = u` and `g⁻¹ (g u) = u`.

## Strings and their relabelling

- A string over the alphabet `α` is `x : Ω → α`. Only decidable equality on `α` is used.
- `relabel g x = fun u => x (g⁻¹ u)`: the symbol at `u` moves to `g u`. This is mathlib's
  `arrowAction` (a definition, not a global instance); `relabel_eq_smul` is the bridge, and
  `relabel (g * h) x = relabel g (relabel h x)`.
- `Matches W g x y :↔ ∀ u ∈ W, x u = y (g u)`. It never inverts `g`, so executable checks
  do not construct inverses. `matches_univ_iff : Matches univ g x y ↔ relabel g x = y`.

## Cosets

- Left cosets only: `σ • (G : Set (Perm Ω)) = {σ * h | h ∈ G}`, with
  `x ∈ σ • G ↔ σ⁻¹ * x ∈ G` (`GraphIso.mem_leftCoset_iff'`).
- Sources using right actions (e.g. Babai, Helfgott) must be translated: their `x^g` with
  `(x^g)^h = x^{gh}` corresponds here to `relabel`, and their right cosets `Gσ` become left
  cosets `σ • G`.

## Windows

- A window is `W : Set Ω`. `IsInvariant G W :↔ ∀ g ∈ G, ∀ u ∈ W, g u ∈ W`; this is an
  explicit hypothesis wherever a single-coset answer is claimed. The coset representative
  need not preserve `W`.
- For a finite window, invariance under `Subgroup.closure S` is checked on the generators
  (`isInvariant_closure_iff`).

## Solution sets and answers

- `iso W σ G x y = {g ∈ σ • G | Matches W g x y}`.
- `aut hW x = {h ∈ G | Matches W h x x}` for `hW : IsInvariant G W`; a subgroup because of
  `hW`.
- Normalization: `iso W σ G x y = σ • iso W 1 G x (fun u => y (σ u))`.
- A semantic answer is `Option (Perm Ω × Subgroup (Perm Ω))`, denoting `∅` or `τ • H`.
  `Answer.IsCorrect a W σ G x y :↔ a.denote = iso W σ G x y`. A correct `some (τ, H)` has
  `H = aut hW x` (`Answer.IsCorrect.of_some`): the full automorphism subgroup, not merely
  some automorphisms.
