# Formalization notes

Notes for readers of the published development: what is proved and where, what must be trusted,
how the formalization relates to its sources, and how it was produced and checked. The
repository's `README.md` has the short account; `docs/theorem-map.md` lists every result by
milestone, and `docs/status.md` records each stage as it was done.

## 1. The results and where they are stated

**The statements of record** (`Challenge.lean`, generated for the Palomar submission; its
definitions are `GraphIso/Palomar/Statement.lean`, which imports Mathlib only):

| Statement | Challenge name | Proof in the library |
|---|---|---|
| A single-tape `TM0` machine decides isomorphism of simple graphs on `Fin n` in at most `2 ^ (c (⌊log₂ n⌋ + 1) ^ 8)` transitions | `GraphIsoPalomar.gi_singleTape` | `gi_singleTape_proof` |
| A single-tape `TM0` machine outputs, in the same bound, `no` or an isomorphism `τ` and generators `gs` with the isomorphisms exactly the left coset `τ ⟨gs⟩` | `GraphIsoPalomar.gi_coset_singleTape` | `gi_coset_singleTape_proof` |
| The second machine's output word determines its answer | `GraphIsoPalomar.cosetWord_injective` | `cosetWord_injective_proof` |

The proofs are in `GraphIso/Palomar/Bridge.lean`. They take the library's single-tape theorems
and prove that the statement's encodings (Mathlib's `Nat.bits`, lists, neighbour lists from vertex
`n - 1` down to `0`, permutations as their images then their inverse images) are the library's
serializations under fixed injective maps of the symbols into the machines' tape alphabets.

**The library's headline theorems**, each stated with the library's own definitions:

| Result | Names | File |
|---|---|---|
| Graph isomorphism in the cost model, with no hypothesis: the coset of all isomorphisms within local cost `2 ^ (c (λ(n) + 1) ^ 8)`, `λ = Nat.log 2` | `giSolve_final`, `gi_simpleGraph_final` | `GraphIso/Wielandt/Final.lean` |
| On Mathlib's multi-stack machines `TM2`, in the input's length `L` | `gi_tm`, `gi_coset_tm` | `GraphIso/TM/GI.lean` |
| The same in the number of vertices | `gi_tm_vertices`, `gi_coset_tm_vertices` | `GraphIso/TM/Vertices.lean` |
| On single-tape `TM0` machines, in the number of vertices and in the tape's length | `gi_tm0_vertices`, `gi_coset_tm0_vertices`, `gi_tm0`, `gi_coset_tm0` | `GraphIso/TM/SingleTape/GI.lean` |

## 2. What must be trusted

* **Lean's kernel**, and the three axioms `propext`, `Quot.sound` and `Classical.choice`. Every
  declaration of the library and of the checks uses at most these
  (`GraphIsoChecks/AxiomAudit.lean`, which enumerates all of them, private ones included). For
  the statements of record, Comparator also replays the proof in independent kernels.
* **The statement file** (about 150 lines): the symbols, the word encodings `natWord`,
  `listWord`, `nbrs`, `graphWord`, `input`, `output`, `permWord`, `cosetWord`, and the three
  theorem statements.
* **Mathlib's definitions** used by the statements: `Turing.TM0.Machine`, `Turing.TM0.step`,
  `Turing.TM0.init`, `Turing.Tape.mk₁`, `SimpleGraph`, graph isomorphisms `≃g`, `Equiv.Perm`,
  `Subgroup.closure`, `Nat.bits`, `Nat.log`, `Function.Embedding`, `Finite`, `Inhabited`.

The development itself (about 200,000 lines in 428 modules, with the checks, plus the generated
Challenge and Solution) need not be read to trust the statements: the kernel checks it.

## 3. The milestones and their sources

| Milestone | Plan | Content | Sources |
|---|---|---|---|
| 1 | `PLAN.md` | String isomorphism under a permutation group with explicit operation costs; the recursive solver; a reference backend | Babai §2; Helfgott §§2.1–2.2 and Appendix A |
| 2 | `PLAN-2.md` | Schreier–Sims: a polynomial-time group backend | Sims (1970); Knuth (1991); Seress, Ch. 4; Jerrum (1986) |
| 3 | `PLAN-3.md` | Luks's strategy (block systems, primitive actions) | Luks (1982); Babai–Cameron–Pálfy (1982); Atkinson (1975); Seress §§5.5, 6 |
| 4–5 | `PLAN-4.md`, `PLAN-5.md` | Graphs of maximum degree three | Luks (1982), §2 |
| 6 | `PLAN-6.md` | Primitive solvable groups | Babai–Cameron–Pálfy; Helfgott §2.2 |
| 7–9 | `PLAN-7.md`–`PLAN-9.md` | Graphs of bounded valence; an elementary Babai–Cameron–Pálfy theorem | Luks (1982); Babai–Cameron–Pálfy; Helfgott, Thm. 2.3 |
| 10 | `PLAN-10.md` | Weisfeiler–Leman refinement and the Design Lemma | Babai §§2.5, 6.1; Helfgott §§2.3–2.6, 5.1 |
| 11 | `PLAN-11.md` | Split-or-Johnson | Babai §§4, 5.1, 7, with the 2017 correction; Helfgott §§2.4–2.7, 5.2 |
| 12 | `PLAN-12.md` | Alternating quotients; the CFSG-free interfaces | Babai §§5.2, 8, 13.1; Helfgott §§3, 4.1, 6; Pyber |
| 13 | `PLAN-13.md` | Local certificates and their aggregation | Babai §10; Helfgott §6 |
| 14 | `PLAN-14.md` | Babai's recursion: the macro-steps, the dispatcher, the potential, the closed bound | Babai §§3, 8–13; Helfgott §§3, 5.3, 6 and Appendix A; Pyber |
| 15 | `PLAN-15.md` | Pyber's CFSG-free bound (Theorem 7, Lemma 12) | Pyber |
| 16 | `PLAN-16.md` | An elementary transitivity bound; the unconditional theorems | Babai–Seress (1987); Babai (1982); Wielandt |
| 17 | `PLAN-17.md` | Compilation to Mathlib's multi-stack Turing machines | Mathlib's `TM2`; Cook–Reckhow (1973) |
| 18 | `PLAN-18.md` | Bounds in the number of vertices; compilation to single-tape machines | Mathlib's `TM0` |
| 19 | `PLAN-19.md` | The module system; the statements of record and their proofs | Palomar's requirements |

"Babai" is *Graph isomorphism in quasipolynomial time* (arXiv:1512.03547), with *Fixing the
UPCC case of Split-or-Johnson* (January 2017); "Helfgott" is Helfgott, Bajpai and Dona,
*Graph isomorphisms in quasi-polynomial time* (arXiv:1710.04574); "Pyber" is *A CFSG-free
analysis of Babai's quasipolynomial GI algorithm* (arXiv:1605.08266). Each plan's references
section gives the full citations.

## 4. The proof route and its divergences from the sources

The algorithm is written as programs in a small language with a cost semantics: a program's cost
is read off its executed trace, so every bound is about the program that actually runs. Babai's
recursion (milestones 10–14) follows Babai and Helfgott; the bound on the recursion's work comes
from a potential function on the instances.

Divergences:

* **No classification of finite simple groups.** Its two uses are replaced (milestones 12, 15
  and 16). The alternating-quotient lemma (Babai's Lemma 8.2.4, Helfgott's Lemma 4.1) is taken in
  Pyber's weak form, for `k > (log₂ n) ^ 5`, proved from Pyber's Theorem 7 and Lemma 12. Cameron's
  theorem on large primitive groups is replaced by the argument of Babai's §13.1: Split-or-Johnson
  on the orbital configuration, with an elementary bound, quadratic in `λ(n)`, on the degree of
  transitivity, proved after Wielandt.
* **The exponent.** The bound `2 ^ (c (λ(n) + 1) ^ 8)` comes from this formalization's
  accounting, with its own thresholds and potential; the exponent `8` is not optimized, and the
  constant `c` is not computed. Babai proves `exp((log n) ^ O(1))`. Helfgott, Bajpai and Dona
  (end of §6 and Appendix A) obtain `exp(O((log n) ^ 3))`, with an analysis that uses the
  classification (Cameron and Maróti's theorem on primitive groups, their Theorem 3.1). Pyber's
  classification-free lemma, used here with Babai's §13.1, makes the bound worse but still
  quasipolynomial; neither computes the exponent of that route.
* **The model.** The cost model's operations are executed by a verified Schreier–Sims backend;
  the programs are compiled to Mathlib's multi-stack machines (polynomial overhead) and then to
  single-tape machines (quadratic overhead). The sources argue in a RAM-like model.
* **Encodings and malformed inputs.** Inputs are fixed encodings of `n` and the neighbour lists;
  nothing is claimed on words that encode no pair of graphs.
* **Scope.** Graph isomorphism and its coset of isomorphisms are covered, through string
  isomorphism under a group. Canonical forms (Babai's later canonization) are not.

### Related formalization: Theo

The Theo project reports a separate Lean development in
[*Beyond the Library: An Agentic Framework for Autoformalizing Research Mathematics*](https://openreview.net/forum?id=XF8jQ5EnrA),
§3.2.9 and Appendix C.10 of the ICLR 2027 submission. It follows Babai's version 2.5 of
2 November 2018. The comparison below uses that paper and the project's
[public source archive](https://github.com/BeyondTheLibrary/formal_archive/tree/2ff27f984baa1f0f5c9031fb6eb2302f89ab4afa/files/GraphIsomorphism/lean_workspace),
inspected at commit `2ff27f984baa1f0f5c9031fb6eb2302f89ab4afa`. This was a source inspection;
the Theo development was not rebuilt or replayed in independent kernels here.

| Aspect | Theo's paper and source | This submission |
|---|---|---|
| Advertised results | String Isomorphism, including an isomorphism representative and automorphism generators; Graph Isomorphism and Coset Intersection | Graph-isomorphism decision, the coset of all graph isomorphisms, and injectivity of the output encoding |
| Machine bound | Quasipolynomial RAM time in encoded input length | Single-tape `TM0` transitions bounded by `2 ^ (c (⌊log₂ n⌋ + 1) ^ 8)` in vertex count |
| Assumptions beyond `propext`, `Quot.sound`, `Classical.choice` | Five cited group-theoretic inputs | None |

The public code contains `Algo.theorem_1_1_1` (String Isomorphism search) and
`Algo.corollary_1_1_2` (Graph Isomorphism and Coset Intersection decision) in the
[main theorem file](https://github.com/BeyondTheLibrary/formal_archive/blob/2ff27f984baa1f0f5c9031fb6eb2302f89ab4afa/files/GraphIsomorphism/lean_workspace/Workspace/Algo/TopMasterClose.lean).
Its RAM has explicit instruction and execution semantics. Its
[graph input encoding](https://github.com/BeyondTheLibrary/formal_archive/blob/2ff27f984baa1f0f5c9031fb6eb2302f89ab4afa/files/GraphIsomorphism/lean_workspace/Workspace/Machine/TargetsGI.lean)
also proves that encoded length and vertex count are polynomially related
(`RAM.Targets.GIInput.size_bounds`), so this parameter difference does not distinguish the
quasipolynomial complexity class. The distinctions are the formal machine model, the fixed
logarithmic exponent in our bound, and the additional assumptions.

The five inputs listed in Appendix C.10 are the Cameron–Maróti theorem on large primitive
groups, polynomial-time computation of Cameron-group structure, the degree-of-transitivity
bound for non-giant groups, the bound on alternating groups involved in general linear groups,
and Schreier's hypothesis. The public source declares these as `Babai.Theorem_11_2_3`,
`Babai.cameronStructure_polyTime`, `Babai.degtrans_le_five`,
`Babai.le_add_two_of_involved_GL` and `Babai.schreierHypothesis`, respectively. A static scan
of the downloaded source found these five `axiom` declarations and no `sorry` or `admit`
tokens outside comments and strings; this is not a kernel dependency audit. This project's
classification-free route uses the proved Pyber bound and an elementary transitivity bound
(§4 above).

Appendix C.10 also reports three gaps and repairs in Babai's 2018 manuscript. The corresponding
parts of this project's design are:

* **Jordan–Liebeck exceptions.** The paper restores exceptional alternatives omitted from the
  printed statement. This project's labelled-hint recursion avoids the Main Structure Theorem
  and Jordan–Liebeck theorem (`PLAN-14.md` §1).
* **Transitivity after descent.** The paper rechecks transitivity and applies the Chain Rule
  when it is lost. Here, `HInstValid.hint` requires transitivity whenever a hint is present
  (`Main/HInst.lean`); `orbit_child` handles restriction to a subgroup and a smaller window
  (`Recursion/Hint.lean`). Transitivity of the parent alone does not supply the child's invariant.
* **Progress when the Johnson parameter is one.** The paper replaces a claimed `2n/3` window
  bound by `4n/5`. Here progress is proved with a separate base/window potential:
  `StepChild` explicitly requires a hinted base of at most `3m/4` or an unhinted window of at
  most `n/2` (`Main/Frame.lean`, `Recursion/Potential.lean`). The colored-partition progress
  theorem explicitly handles an orbit lying in a single block (`Recursion/Progress.lean`).

These are correspondences between the proof designs, not a new exhaustive audit of either
development. No Lean statement or proof was changed as part of this comparison.

This related work was identified on 29 October 2026, during submission preparation, after the
three statements of record had been proved. It was not an input to this development. The
earlier README sentence reporting no known prior formalization has been removed; no priority
claim is made. The abstract of the indexed [arXiv version 3](https://arxiv.org/abs/2606.31134v3),
dated 5 August 2026, describes seven case studies and does not mention Babai; the supplied
OpenReview paper describes nine. That version difference may have contributed to the search
miss, but the original brief search was insufficient to support the withdrawn statement.

## 5. How the development was produced and checked

The development took place from 18 to 29 October 2026. The Lean code, the plans and the initial
documentation were written by an AI agent, Claude Code with Claude Opus 5.5. The human
author set the goals, made the decisions recorded in the plans, and approved each plan, including
the statements of record (`PLAN-19.md`, Appendices A and B). Every milestone followed a written
plan (`PLAN.md` to `PLAN-19.md`), and every stage was recorded in `docs/status.md`.

**Standards** (`docs/conventions.md`): every build has warnings as errors; no `sorry`, `admit`,
custom axiom, `native_decide`, heartbeat override or `noncomputable` code; concrete checks are
kernel-checked (`decide +kernel`), large executions in pieces; costs come from executed semantics.

**The write–audit loop.** From milestone 7 (20 October 2026) on, every stage ran in a loop:
1. a mechanical gate: the full build, an axiom check of the changed declarations, the banned
   constructs, and a snapshot of the protected theorem statements (the headline results of every
   milestone), which may change only with the author's approval;
2. an adversarial audit by OpenAI's Codex (gpt-6-astra at maximum effort), which could read the
   repository and write and run its own Lean probes in a scratch folder, reporting findings as
   blocker, major or minor;
3. answers to the findings (fixes, or disputes with evidence), and another audit, at most three
   rounds; a stage closed only when the audit approved it, or went to the author.

At the close of stage 19e there were 61 completed loops (57 approved, 2 referred to the author,
2 abandoned) with 89 audit rounds. The audit reports are not published. Before the loop existed,
milestones 1 to 6 were reviewed by OpenAI's Codex (gpt-6-astra at maximum effort), with the
author passing the messages between Claude Code and Codex by hand.
OpenAI Codex later repaired the remaining stage 19e finding in the snapshot reference checker,
added regression checks, and revised the submission documentation and metadata. This follow-up
did not change a Lean statement or proof and is not counted as another independent audit round.

**What was not done.** The Lean proofs were not reviewed line by line by a person. Their
correctness rests on the kernel and the independent checkers; their meaning rests on the
statement file, which is short and was approved by the author.

## 6. Reproducing the build and the checks

From `lean/` with the toolchain of `lean-toolchain`:

```text
lake exe cache get                       # Mathlib's prebuilt files
lake build                               # GraphIso and the solution
lake build Challenge                     # the statements; three deliberate `sorry` warnings
lake comparator                          # the solution against the challenge (Linux, bubblewrap)
scripts/build-seq.sh --wfail             # everything, the checks one module at a time
```

The checks (`GraphIsoChecks`) take about two hours on one machine, and a few modules need 20–40
GB of memory; `scripts/guard.sh` runs them under a memory cap and a time limit. The axiom audit
is `GraphIsoChecks/AxiomAudit.lean`.

The published repository is generated from the development repository by
`scripts/palomar-snapshot.sh` (`PLAN-19.md` §7), which leaves out the audit reports and
evidence, the paper PDFs and the loop's state, and writes `Challenge.lean`, `Solution.lean` and
`comparator.json`.
