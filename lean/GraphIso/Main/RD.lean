module

public import GraphIso.Main.M2bLoop
public import GraphIso.Main.StepsBase
public import GraphIso.Main.StepsHint
public import GraphIso.Solver.Sims
public import GraphIso.Solver.Luks

/-!
# Reduce-and-derive

Stage 14j-2, item 4 (`PLAN-14.md` §14.2): the common tail of M4 and M5. A hinted parent
`(σ • G, W, L)` (transitive on `W`, `HInstValid`), a left cover `rs` of `G` by cosets of
`K ≤ G`, and a structure `st` that `K` preserves.

* **`rdProg`**: a branch over the cover (`branchProg`); each coset `σ r • K` is solved by
  the dynamic chain over `W` (`rdBranch`, `dynSeqProg`). Every step's orbit `O` is an orbit of
  some `H ≤ K` (which preserves `st` too); its handle (`rdHandle`) runs `deriveProg` for `H`
  and dispatches on the tag (`rdTail`):
  - **tag 0**: a sub-call without a hint on `O` (`2|O| ≤ |W|`);
  - **tags 1, 2, 4**: a sub-call on the hinted child (base `m' ≤ 3m/4`), with `viaChildProg`;
  - **tag 3**: through the M1 child `P` (`viaChildProg`), the block-stabilizer loop
    `m2bLoopProg` with the cover of `P` by at most `m` cosets of `R` (`rd3Inner`); its children
    have a hint on at most `m/2` base points or no hint on at most `|O|/2` points;
  - **tag 5**: through `P`, `K` re-based onto the cells, a branch over the cover of `P` by
    cosets of `R`, each by `seqProg` over the `R`-orbits of `O` without a hint (`rd5Inner`;
    each child has at most `|O|/2` points);
  - **tag 6** (stuck): the kernel reduction (`kerRedProg`) of `O`, inside the hinted instance
    `(O, τ • H, L)` (its labels are not constant there, `rd_model_nc`), with at most `m!`
    cosets.
* **Specs.** The per-tag lemmas `rd_sem0`, `rd_sem124`, `rd_sem3`, `rd_sem5`, `rd_sem6` (with
  the control flow `rd_tail0` … `rd_tail6`), the handle `rd_handle` (a `DynHandle`), a branch
  `rd_branch`, and **`RunsWithin.rdProg`**: a correct answer for `σ • G` on `W`, within the
  children's costs plus `rdCost`, with children `StepChild |W| m` whose windows sum to at most
  `|rs| · F · |W|`. `F ≥ m` bounds the branching inside an orbit: `|reps| ≤ m` for tag 3, the
  Johnson fallback's cover for tag 5 (`h5`: `m! ≤ F`, or a direct bound on the outputs), and
  the kernel's `m!` cosets for tag 6 unless no orbit is stuck (`h6`). Corollaries:
  `RunsWithin.rdProg_general` (`F = m!`, no further hypothesis) and `RunsWithin.rdProg_ns`
  (no stuck orbit: no kernel work, `W6 = 0`).
* **Hypotheses.** `RDOrbit`: for every orbit that can occur (`RDSet`: an orbit of some `H ≤ K`
  with at most `sIn` generators), the derived hint runs within `Bd`, its outcome (`DOutcome`)
  holds, the degree of the reduction's group for tags `3` and `5` is at most `N`, and the
  generator counts are bounded (`DOutGens`, a hypothesis): the reduction's `R` and the child for
  tags `3` and `5`, and the child for tags `1`, `2`, `4`. The last part was added by the contract
  repair of stage 14j-5a (`PLAN-14.md` §14.6): those children are re-based `generate` outputs,
  whose generator count needs a valid input (for tag `4`, Johnson preservation).
* **The children's generators.** Every child has at most `sIn` generators (`SizeChild sIn`):
  the dynamic chain's current group (tag `0`), `DOutGens` (tags `1`–`5`), and
  `RDBounds.kerGens` with `s ≤ sIn` (tag `6`). Every child has a nonempty window (`ChildList`'s
  `pos`).
* **The children's labels** (stage 14j-6a, `PLAN-14.md` §14.10): `SizeChild`'s field `lab`.
  Children without a hint (tags `0`, `5`) satisfy it trivially; tag `6` keeps the labels;
  tags `1`, `2` and `4` take it from `DOutcome`'s label facts (`rd_sem124`'s `hLab`, by
  `LabInvAt.mono` and `LabInvAt.johnson`); tag `3` from `DOutcome.blockStab`'s through
  `MlChildL` (`RunsWithin.m2bLoopProg_lab`).
  - `rd_orbit_free` and `rd_orbit_cj` derive `RDOrbit` from `RunsWithin.deriveProg_free` and
    `RunsWithin.deriveProg_cj`, with the degree proved from the model: the M1 child for tag
    `3` (`rd_m1_deg`), and the cells' re-basing for tag `5` (`rd_cells_rebase`, by `JValid`).
    See `rd_deg_free` and `rd_deg_cj`. The structure hypotheses for `K` hold for every
    subgroup.
  - `RDBounds` gives uniform backend charges on bounded inputs: degree at most `N`, at most
    `sIn` generators, `generate` on at most `Lg` generators. The kernel's coset
    representatives are charged only for groups keeping the base invariant.
* **The Schreier–Sims backend.** `rd_ss_bounds` proves `RDBounds` for `ssCtx`, with `sIn = N²`
  and explicit charges.
* **The Johnson fallback's factor.** `rd_cj_reps5`: with a coloured Johnson structure, a tag-`5`
  output has at most `u!` coset representatives, where `u` counts the union cells at the first
  point of the orbit. The proof follows the model to `jfallbackModel` and the factorial bound
  of the pointwise stabilizers.
* **No stuck orbits.** `rd_ns_part` (a preserved colored `t`-partition with `4t ≤ 3m`) and
  `rd_ns_cj` (a preserved coloured Johnson structure) give `h6`'s left case, through
  `derivePart_ne_stuck` and `deriveCJ_ne_stuck`.
* **Corollaries.** With these, the structured corollaries need neither `h5` nor `h6`:
  - `RunsWithin.rdProg_part_ns` (factor `m`);
  - `RunsWithin.rdProg_cj_ns` (factor `max m uB!`, where `uB` bounds the union cells).
* Well-formedness: `wf_rdProg` and the lemmas of the pieces.
-/

@[expose] public section

namespace GraphIso.Main

open Equiv Cost GraphIso GraphIso.Programs GraphIso.Toolkit GraphIso.Recursion
  GraphIso.SplitJohnson GraphIso.Solver

/-! ### Programs -/

section Progs

variable {D : Ty} {rec : Ty × Ty} {var : Ty → Type}

/-- **Tag 3**, the solver of the M1 child's instance: the block-stabilizer loop. -/
def rd3Inner (sub : var (hinstTy D) → Prog (groupSig D) rec var (Ty.answer D))
    (R G' : var (Ty.group D)) (reps : var Ty.gens) (O : var (.list .nat))
    (L' : var (.array (.list .nat))) (n₀ n : var .nat) (J : var (hinstTy D)) :
    Prog (groupSig D) rec var (Ty.answer D) :=
  .bind (.op1 .fst J) fun I => .bind (.op1 .fst I) fun xy => .bind (.op1 .snd I) fun wc =>
  .bind (.op1 .snd wc) fun c => .bind (.op1 .fst c) fun σ =>
  m2bLoopProg sub xy σ R G' reps O L' n₀ n

/-- **Tag 5**, the solver of the instance re-based onto the cells: a branch over the cover by
cosets of `R`, each solved by `seqProg` over the `R`-orbits of the window, without a hint. -/
def rd5Inner (sub : var (hinstTy D) → Prog (groupSig D) rec var (Ty.answer D))
    (R : var (Ty.group D)) (reps : var Ty.gens) (n₀ n : var .nat) (J : var (hinstTy D)) :
    Prog (groupSig D) rec var (Ty.answer D) :=
  .bind (.op1 .fst J) fun I => .bind (.op1 .fst I) fun xy => .bind (.op1 .snd I) fun wc =>
  .bind (.op1 .fst wc) fun w => .bind (.op1 .snd wc) fun c => .bind (.op1 .fst c) fun σ =>
  .bind (.op2 .pair R w) fun Rw =>
  .bind (Prog.call (S := groupSig D) GroupOp.orbits Rw) fun os =>
  branchProg (blockBranch (plainSub sub n₀ n) xy os) xy w σ R reps

/-- The instance `(x, y, O, c)` at degree `N`, without a hint. -/
def rdPlainInst (N : var .nat) (xy : var Ty.strs) (c : var (Ty.coset D)) (O : var (.list .nat)) :
    Prog (groupSig D) rec var (Ty.inst D) :=
  .bind (mkWindow N O) fun wO => .bind (.op2 .pair wO c) fun wc => .op2 .pair xy wc

/-- **The dispatch on the derived hint** `r` of the orbit `O` of the current coset `c = τ • H`
(degree `N`): a sub-call without a hint (tag `0`), the block-stabilizer loop through the M1 child
(tag `3`), the Johnson fallback through the group re-based onto the cells (tag `5`), the kernel
reduction (tag `6`), or a sub-call on the hinted child (tags `1`, `2`, `4`). -/
def rdTail (sub : var (hinstTy D) → Prog (groupSig D) rec var (Ty.answer D))
    (n₀ n N : var .nat) (xy : var Ty.strs) (c : var (Ty.coset D)) (τ : var Ty.perm)
    (H : var (Ty.group D)) (O : var (.list .nat)) (r : var (deriveTy D)) :
    Prog (groupSig D) rec var (Ty.answer D) :=
  .bind (.op1 .fst r) fun tag => .bind (.op1 .snd r) fun r₁ =>
  .bind (.op1 .fst r₁) fun red => .bind (.op1 .snd r₁) fun chd =>
  .bind (.op1 .fst red) fun P => .bind (.op1 .snd red) fun rr =>
  .bind (.op1 .fst rr) fun R => .bind (.op1 .snd rr) fun reps =>
  .bind (.op1 .fst chd) fun G' => .bind (.op1 .snd chd) fun wl =>
  .bind (.op1 .fst wl) fun w' => .bind (.op1 .snd wl) fun L' =>
  .bind (.op0 (.natLit 0)) fun k₀ => .bind (.op2 .natEq tag k₀) fun t₀ =>
  .ite t₀ (.bind (rdPlainInst N xy c O) fun J => plainSub sub n₀ n J)
  (.bind (.op0 (.natLit 3)) fun k₃ => .bind (.op2 .natEq tag k₃) fun t₃ =>
  .ite t₃ (.bind (.op1 .fst P) fun N₁ => .bind (mkWindow N₁ O) fun w₁ =>
      .bind (.op0 .none) fun nl =>
      viaChildProg (rd3Inner sub R G' reps O L' n₀ n) xy τ H n₀ n P w₁ nl)
  (.bind (.op0 (.natLit 5)) fun k₅ => .bind (.op2 .natEq tag k₅) fun t₅ =>
  .ite t₅ (.bind (.op1 .fst P) fun N₅ => .bind (mkWindow N₅ O) fun w₅ =>
      .bind (.op0 .none) fun nl =>
      viaChildProg (rd5Inner sub R reps n₀ n) xy τ H n₀ n P w₅ nl)
  (.bind (.op0 (.natLit 6)) fun k₆ => .bind (.op2 .natEq tag k₆) fun t₆ =>
  .ite t₆ (.bind (rdPlainInst N xy c O) fun J => kerRedProg sub n₀ n J)
    (.bind (.op1 .some L') fun sL => viaChildProg sub xy τ H n₀ n G' w' sL))))

/-- **The handle of reduce-and-derive**: on the orbit `O` of the current coset `c = τ • H`, the
derived hint (`deriveProg`) and the dispatch on it (`rdTail`). -/
def rdHandle (sub : var (hinstTy D) → Prog (groupSig D) rec var (Ty.answer D))
    (n₀ n : var .nat) (L : var (.array (.list .nat))) (st : var stTy) (xy : var Ty.strs)
    (c : var (Ty.coset D)) (O : var (.list .nat)) : Prog (groupSig D) rec var (Ty.answer D) :=
  .bind (.op1 .fst c) fun τ => .bind (.op1 .snd c) fun H => .bind (.op1 .fst H) fun N =>
  .bind (deriveProg n N H O L st) fun r => rdTail sub n₀ n N xy c τ H O r

/-- **One branch**: the coset of the instance `J`, by the dynamic chain over its window. -/
def rdBranch (sub : var (hinstTy D) → Prog (groupSig D) rec var (Ty.answer D))
    (n₀ n : var .nat) (L : var (.array (.list .nat))) (st : var stTy) (J : var (Ty.inst D)) :
    Prog (groupSig D) rec var (Ty.answer D) :=
  .bind (.op1 .fst J) fun xy => .bind (.op1 .snd J) fun wc =>
  .bind (.op1 .fst wc) fun w => .bind (.op1 .snd wc) fun c =>
  .bind (.op1 .fst w) fun pts => dynSeqProg (rdHandle sub n₀ n L st) xy c pts

/-- **Reduce-and-derive** on the hinted instance `I`, with the cover `rs` of its group by cosets
of `K` and the structure `st` that `K` preserves. -/
def rdProg (sub : var (hinstTy D) → Prog (groupSig D) rec var (Ty.answer D))
    (I : var (hinstTy D)) (rs : var Ty.gens) (K : var (Ty.group D)) (st : var stTy) :
    Prog (groupSig D) rec var (Ty.answer D) :=
  .bind (.op1 .fst I) fun J => .bind (.op1 .snd I) fun r₁ =>
  .bind (.op1 .fst r₁) fun n₀ => .bind (.op1 .snd r₁) fun r₂ =>
  .bind (.op1 .fst r₂) fun n => .bind (.op1 .snd r₂) fun lab =>
  .caseOption lab (.op0 .none) fun L =>
  .bind (.op1 .fst J) fun xy => .bind (.op1 .snd J) fun wc =>
  .bind (.op1 .fst wc) fun w => .bind (.op1 .snd wc) fun c => .bind (.op1 .fst c) fun σ =>
  branchProg (rdBranch sub n₀ n L st) xy w σ K rs

end Progs

/-! ### The control flow of the dispatch -/

section Runs

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b}

theorem RunsWithin.rdPlainInst (N : ℕ) (xy : StrData × StrData) (c : CosetData D)
    (O : List ℕ) :
    RunsWithin X body (Main.rdPlainInst N xy c O) ((xy, (WinData.ofPoints N O, c)) : InstData D)
      (2 * N + 5 * O.length + 9) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.mkWindow _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim _ _
  case hc =>
    simp only [Prim.cost]
    omega

variable {sub : HInstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)}
  {n₀ n N : ℕ} {xy : StrData × StrData} {τ : PermData} {H : GroupData D.denote}
  {O : List ℕ} {k : ℕ} {P R G' : GroupData D.denote} {reps : List PermData} {w' : WinData}
  {L' : LabelData} {ans : AnswerData D} {K : ℕ}

/-- The projections of the derived hint and the test of tag `0`. -/
local macro "rd_proj" : tactic => `(tactic| (
  run_step (RunsWithin.prim _ _)
  run_step (RunsWithin.prim _ _)
  run_step (RunsWithin.prim _ _)
  run_step (RunsWithin.prim _ _)
  run_step (RunsWithin.prim _ _)
  run_step (RunsWithin.prim _ _)
  run_step (RunsWithin.prim _ _)
  run_step (RunsWithin.prim _ _)
  run_step (RunsWithin.prim _ _)
  run_step (RunsWithin.prim _ _)
  run_step (RunsWithin.prim _ _)
  run_step (RunsWithin.prim _ _)
  run_step (RunsWithin.prim _ _)
  run_step (RunsWithin.prim _ _)))

/-- A further tag test. -/
local macro "rd_test" : tactic => `(tactic| (
  run_step (RunsWithin.prim _ _)
  run_step (RunsWithin.prim _ _)))

/-- **Tag `0`**: the sub-call without a hint. -/
theorem rd_tail0 (hk : k = 0)
    (h : RunsWithin X body (Main.plainSub sub n₀ n (xy, (WinData.ofPoints N O, (τ, H)))) ans K) :
    RunsWithin X body
      (Main.rdTail sub n₀ n N xy (τ, H) τ H O (k, ((P, (R, reps)), (G', (w', L'))))) ans
      (K + 2 * N + 5 * O.length + 30) := by
  subst hk
  apply RunsWithin.mono
  case h =>
    rd_proj
    exact RunsWithin.ite_true (RunsWithin.step (RunsWithin.rdPlainInst N xy (τ, H) O) h)
  case hc =>
    simp only [Prim.cost]
    omega

/-- **Tag `3`**: the block-stabilizer loop through the M1 child `P`. -/
theorem rd_tail3 (hk : k = 3)
    (h : RunsWithin X body (Main.viaChildProg (Main.rd3Inner sub R G' reps O L' n₀ n) xy τ H n₀ n P
      (WinData.ofPoints P.1 O) none) ans K) :
    RunsWithin X body
      (Main.rdTail sub n₀ n N xy (τ, H) τ H O (k, ((P, (R, reps)), (G', (w', L'))))) ans
      (K + 2 * P.1 + 5 * O.length + 40) := by
  subst hk
  apply RunsWithin.mono
  case h =>
    rd_proj
    run_with RunsWithin.ite_false _
    rd_test
    run_with RunsWithin.ite_true _
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.mkWindow _ _)
    run_step (RunsWithin.prim _ _)
    exact h
  case hc =>
    simp only [Prim.cost, Prim.eval]
    omega

/-- **Tag `5`**: the Johnson fallback through the group `P` re-based onto the cells. -/
theorem rd_tail5 (hk : k = 5)
    (h : RunsWithin X body (Main.viaChildProg (Main.rd5Inner sub R reps n₀ n) xy τ H n₀ n P
      (WinData.ofPoints P.1 O) none) ans K) :
    RunsWithin X body
      (Main.rdTail sub n₀ n N xy (τ, H) τ H O (k, ((P, (R, reps)), (G', (w', L'))))) ans
      (K + 2 * P.1 + 5 * O.length + 50) := by
  subst hk
  apply RunsWithin.mono
  case h =>
    rd_proj
    run_with RunsWithin.ite_false _
    rd_test
    run_with RunsWithin.ite_false _
    rd_test
    run_with RunsWithin.ite_true _
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.mkWindow _ _)
    run_step (RunsWithin.prim _ _)
    exact h
  case hc =>
    simp only [Prim.cost, Prim.eval]
    omega

/-- **Tag `6`**: the kernel reduction. -/
theorem rd_tail6 (hk : k = 6)
    (h : RunsWithin X body (Main.kerRedProg sub n₀ n (xy, (WinData.ofPoints N O, (τ, H)))) ans K) :
    RunsWithin X body
      (Main.rdTail sub n₀ n N xy (τ, H) τ H O (k, ((P, (R, reps)), (G', (w', L'))))) ans
      (K + 2 * N + 5 * O.length + 50) := by
  subst hk
  apply RunsWithin.mono
  case h =>
    rd_proj
    run_with RunsWithin.ite_false _
    rd_test
    run_with RunsWithin.ite_false _
    rd_test
    run_with RunsWithin.ite_false _
    rd_test
    run_with RunsWithin.ite_true _
    exact RunsWithin.step (RunsWithin.rdPlainInst N xy (τ, H) O) h
  case hc =>
    simp only [Prim.cost]
    omega

/-- **Tags `1`, `2`, `4`**: the sub-call on the hinted child. -/
theorem rd_tail124 (hk : k = 1 ∨ k = 2 ∨ k = 4)
    (h : RunsWithin X body (Main.viaChildProg sub xy τ H n₀ n G' w' (some L')) ans K) :
    RunsWithin X body
      (Main.rdTail sub n₀ n N xy (τ, H) τ H O (k, ((P, (R, reps)), (G', (w', L'))))) ans
      (K + 50) := by
  rcases hk with rfl | rfl | rfl
  all_goals
    apply RunsWithin.mono
    case h =>
      rd_proj
      run_with RunsWithin.ite_false _
      rd_test
      run_with RunsWithin.ite_false _
      rd_test
      run_with RunsWithin.ite_false _
      rd_test
      run_with RunsWithin.ite_false _
      run_step (RunsWithin.prim _ _)
      exact h
    case hc =>
      simp only [Prim.cost]
      omega

end Runs

/-! ### Hypotheses and costs -/

section Hyps

variable {D : Ty}

/-- **Uniform backend bounds** for reduce-and-derive, on bounded inputs: groups of degree at most
`N` with at most `sIn` generators, `generate` on at most `Lg` generators. The generator counts
of `generate` and of the kernel are at most `sIn`. The coset representatives of the kernel are
charged only for groups keeping the base invariant (the kernel's index is then at most `m!`).
`rd_ss_bounds` gives them for the Schreier–Sims backend. -/
structure RDBounds (X : Ctx (groupSig D)) (DV : ℕ → GensData → D.denote → Prop)
    (n N sIn Lg Blift Bgen Bo Bk Bcr : ℕ) : Prop where
  lift : ∀ M, M ≤ N → ∀ (gs : GensData) (d : D.denote), GroupValid DV M gs d →
    gs.length ≤ sIn → ∀ π' : PermData, π'.Valid n →
      X.B.call GroupOp.lift ((M, gs, d), (strWin M n, π'))
        (X.O.run GroupOp.lift ((M, gs, d), (strWin M n, π'))) ≤ Blift
  gen : ∀ M, M ≤ N → ∀ hs : GensData, GensData.AllValid M hs → hs.length ≤ Lg →
    X.B.call GroupOp.generate (M, hs) (X.O.run GroupOp.generate (M, hs)) ≤ Bgen
  genOut : ∀ M, M ≤ N → ∀ hs : GensData, GensData.AllValid M hs →
    (X.O.run GroupOp.generate (M, hs)).2.1.length ≤ sIn
  orbits : ∀ (Hd : GroupData D.denote) (w : WinData), Hd.1 ≤ N → Hd.2.1.length ≤ sIn →
    GroupPre DV .orbits (Hd, w) →
      X.B.call GroupOp.orbits (Hd, w) (X.O.run GroupOp.orbits (Hd, w)) ≤ Bo
  kernel : ∀ (gs : GensData) (d : D.denote), GroupValid DV N gs d → gs.length ≤ sIn →
    X.B.call GroupOp.kernel ((N, gs, d), baseWin n N) (kerModel X.O n (N, gs, d)) ≤ Bk
  kerGens : ∀ (gs : GensData) (d : D.denote), GroupValid DV N gs d → gs.length ≤ sIn →
    (kerModel X.O n (N, gs, d)).2.1.length ≤ sIn
  kerOrbits : ∀ (gs : GensData) (d : D.denote) (w : WinData), GroupValid DV N gs d →
    gs.length ≤ sIn → w.Valid N →
    X.B.call GroupOp.orbits (kerModel X.O n (N, gs, d), w) (krOrbits X.O n (N, gs, d) w) ≤ Bo
  cosetReps : ∀ (gs : GensData) (d : D.denote), GroupValid DV N gs d → gs.length ≤ sIn →
    IsInvariant (GensData.denote N gs) (baseSet n N) →
    X.B.call GroupOp.cosetReps ((N, gs, d), kerModel X.O n (N, gs, d))
      (kerReps X.O n (N, gs, d)) ≤ Bcr

/-- **The generator counts of a derived hint**: with a reduction (tags `3` and `5`), its `R`
and the child's group have at most `sIn` generators; with a hinted child (tags `1`, `2`, `4`),
the child's group has at most `sIn` generators. The second part was added by the contract repair
of stage 14j-5a (`PLAN-14.md` §14.6, a scope amendment): those children are re-based `generate`
outputs, whose generator count the other hypotheses do not bound. -/
def DOutGens (sIn : ℕ) (r : DOut D) : Prop :=
  (r.1 = 3 ∨ r.1 = 5 → r.2.1.2.1.2.1.length ≤ sIn ∧ r.2.2.1.2.1.length ≤ sIn) ∧
    (r.1 = 1 ∨ r.1 = 2 ∨ r.1 = 4 → r.2.2.1.2.1.length ≤ sIn)

/-- **The derived hint of one orbit**: `deriveProg` runs within `Bd` to its model, the outcome
holds (`RunsWithin.deriveProg_free`, `RunsWithin.deriveProg_cj`), the reduction's group has
degree at most `N` for tags `3` and `5` (proved by `rd_deg_free`, `rd_deg_cj`), and the
generator counts are bounded. -/
structure RDOrbit (X : Ctx (groupSig D)) {a b : Ty}
    (body : a.denote → Prog (groupSig D) (a, b) Ty.denote b)
    (DV : ℕ → GensData → D.denote → Prop) (n N : ℕ) (w : WinData) (L : LabelData)
    (st : ℕ × CJData) (sIn Bd : ℕ) (gs : GensData) (d : D.denote) (O : List ℕ) : Prop where
  run : RunsWithin X body (Main.deriveProg n N (N, gs, d) O L st)
    (deriveModel X.O n N (N, gs, d) O L st) Bd
  out : DOutcome DV n N w L gs d O (deriveModel X.O n N (N, gs, d) O L st)
  deg : (deriveModel X.O n N (N, gs, d) O L st).1 = 3 ∨
      (deriveModel X.O n N (N, gs, d) O L st).1 = 5 →
    (deriveModel X.O n N (N, gs, d) O L st).2.1.1.1 ≤ N
  gens : DOutGens sIn (deriveModel X.O n N (N, gs, d) O L st)

end Hyps

/-- The work of tag `5` beyond its children: the orbits of `R`, at most `F` branches over at
most `p` orbits, and the final `generate`. -/
def rd5Cost (N p F sIn Bo Bgen : ℕ) : ℕ :=
  Bo + F * (24 * N + p * (2 * N + 17) + 5 * p + sIn + 48) + Bgen + 40

/-- The work of tag `6` (the kernel reduction) beyond its children, on at most `p` points. -/
def rd6Cost (N n p s sIn Bk Bo Bcr Bgen : ℕ) : ℕ :=
  kerRedCost N n p (N - n).factorial sIn s Bk Bo Bcr Bgen

/-- **The work of one orbit** beyond its children, on at most `p` points: the derived hint
(`Bd`), and the work of every tag (`W6` for tag `6`). -/
def rdOrbitWork (N n p s sIn F Bd Blift Bgen Bo W6 : ℕ) : ℕ :=
  Bd + 2 * N + 5 * p + 60 + viaChildCost N N n s Blift Bgen +
    (viaChildCost N N n sIn Blift Bgen + m2bLoopCost N N n p (N - n) sIn sIn Blift Bgen Bo Bgen) +
    (viaChildCost N N n sIn Blift Bgen + rd5Cost N p F sIn Bo Bgen) + W6

/-- **The work of reduce-and-derive** beyond its children: `r` branches, each a dynamic chain on
`p` points with the work `Wh` per orbit, and the final `generate`. -/
def rdCost (N p r sIn Wh Bo Bgen : ℕ) : ℕ :=
  r * (24 * N + (p * Wh + dynSeqCost N p Bo + 10) + sIn + 45) + Bgen + 40

theorem rd_viaChildCost_mono {N N' N₁ N₁' n s Blift Bgen : ℕ} (h : N ≤ N') (h₁ : N₁ ≤ N₁') :
    viaChildCost N N₁ n s Blift Bgen ≤ viaChildCost N' N₁' n s Blift Bgen := by
  simp only [viaChildCost, transferCost]
  omega

theorem rd_m2bLoopCost_mono {N₁ N' N n p p' r r' sIn sR Blift Bgen Bo Bgen₂ : ℕ}
    (h₁ : N₁ ≤ N) (h' : N' ≤ N) (hp : p ≤ p') (hr : r ≤ r') :
    m2bLoopCost N₁ N' n p r sIn sR Blift Bgen Bo Bgen₂ ≤
      m2bLoopCost N N n p' r' sIn sR Blift Bgen Bo Bgen₂ := by
  have hv := rd_viaChildCost_mono (n := n) (s := sIn) (Blift := Blift) (Bgen := Bgen) h₁ h'
  simp only [m2bLoopCost, mlBranchCost, mlHandleCost, ncBCost, ncCost, ncPairCost, interOCost,
    SoJTree.setEqCost, baseWinCost, dynSeqCost, dynStepCost]
  have hs : N' - n ≤ N - n := Nat.sub_le_sub_right h' n
  gcongr

theorem rd_kerRedCost_mono {N n p p' r r' sK sK' s Bk Bo Bcr Bgen : ℕ} (hp : p ≤ p')
    (hr : r ≤ r') (hs : sK ≤ sK') :
    kerRedCost N n p r sK s Bk Bo Bcr Bgen ≤ kerRedCost N n p' r' sK' s Bk Bo Bcr Bgen := by
  simp only [kerRedCost]
  have : max s sK ≤ max s sK' := max_le_max le_rfl hs
  gcongr

/-! ### Facts about the derived hint's model -/

section ModelFacts

variable {D : Ty} {DV : ℕ → GensData → D.denote → Prop}

/-- The M1 continuation outputs tag `3` only with the M1 child as its `P`. -/
theorem rd_m1Cont_tag3 {Or : Oracle (groupSig D)} {n N : ℕ}
    {r : GroupData D.denote × (WinData × LabelData)} (h : (m1ContD Or n N r).1 = 3) :
    (m1ContD Or n N r).2.1.1 = r.1 := by
  revert h
  unfold m1ContD blocksD m2aOutD m2bOutD outD
  cases leQD (r.1.1 - n) (N - n) <;>
    cases blkOKD (r.1.1 - n) (mbD n r.1.1 r.1.2.1) <;>
    cases neqD n r.1.1 (mbD n r.1.1 r.1.2.1) r.2.2 r.2.1.1 <;> simp

/-- The M1 continuation never outputs tag `5`. -/
theorem rd_m1Cont_ne5 {Or : Oracle (groupSig D)} {n N : ℕ}
    {r : GroupData D.denote × (WinData × LabelData)} : (m1ContD Or n N r).1 ≠ 5 := by
  unfold m1ContD blocksD m2aOutD m2bOutD outD
  cases leQD (r.1.1 - n) (N - n) <;>
    cases blkOKD (r.1.1 - n) (mbD n r.1.1 r.1.2.1) <;>
    cases neqD n r.1.1 (mbD n r.1.1 r.1.2.1) r.2.2 r.2.1.1 <;> simp

/-- The Johnson step never outputs tag `3`. -/
theorem rd_john_ne3 {Or : Oracle (groupSig D)} {n N : ℕ} {K : GroupData D.denote}
    {O : List ℕ} {L : LabelData} {jd : Align.JData} : (johnStepD Or n N K O L jd).1 ≠ 3 := by
  unfold johnStepD outD
  cases ncBD n (n + jd.2.1.length) (labJUD jd.2.1.length (markArr (N - n) jd.1) jd.2.2.2 L O) O <;>
    cases leQD jd.2.1.length (N - n) <;> simp

/-- Without a coloured Johnson structure, the derived hint never has tag `5`. -/
theorem rd_free_ne5 {Or : Oracle (groupSig D)} {n N : ℕ} {K : GroupData D.denote}
    {O : List ℕ} {L : LabelData} {st : ℕ × CJData} (hst : st.1 ≠ 2) :
    (deriveModel Or n N K O L st).1 ≠ 5 := by
  have he : (st.1 == 2) = false := by simpa using hst
  simp only [deriveModel, he, Bool.cond_false]
  unfold deriveFreeModel
  cases ncBD n N L O
  · simp [noHintD, outD]
  · exact rd_m1Cont_ne5

/-- The degree of the M1 child is at most `N`. -/
theorem rd_m1_deg {X : Ctx (groupSig D)} (hO : MeetsContractOn DV m1Ops X.O) {n N : ℕ}
    {gs : GensData} {d : D.denote} {w : WinData} {L : LabelData} (hGv : GroupValid DV N gs d)
    (hL : HintValid n N gs w L) : (m1Model X.O n N (N, gs, d) w L).1.1 ≤ N := by
  obtain ⟨hnd, hb, horb, -⟩ := dv_m1O hO hGv hL
  set Ob := m1O X.O n N (N, gs, d) w L with hObdef
  have hwO : (WinData.ofPoints N Ob).Valid N :=
    WinData.valid_ofPoints hnd fun x hx => (hb x hx).2
  obtain ⟨hdeg, -, -⟩ := dv_rebase_den (X := X) (DV := DV)
    (fun op x hop hx => hO op x (Or.inr hop) hx) hL.le hL.base_inv hwO mf_sing_isBlockList
    (mf_sing_permutes horb) hGv.1
  have hm : (m1Model X.O n N (N, gs, d) w L).1 = rebaseModel X.O n N (singD Ob) gs := rfl
  rw [hm, hdeg, length_singD]
  have hnd' : (Ob.map (· - n)).Nodup := hnd.map_on fun x hx y hy h => by
    have := (hb x hx).1
    have := (hb y hy).1
    omega
  have := mf_length_le_of_nodup hnd' (m := N - n) fun j hj => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hj
    have := hb x hx
    omega
  rw [List.length_map] at this
  have := hL.le
  omega

/-- The group re-based onto the cells of a Johnson structure has degree `n + #cells ≤ N`, is
valid and denotes the re-based group. -/
theorem rd_cells_rebase {X : Ctx (groupSig D)} (hO : MeetsContractOn DV rebaseOps X.O)
    {n N : ℕ} {gsG gs : GensData} {w : WinData} {L : LabelData} {d : D.denote} {O : List ℕ}
    (hS : DSetting DV n N gsG w L gs d O) {jd : Align.JData} (hJv : Align.JValid (N - n) jd)
    (hK : ∀ g : ↥(GensData.denote N gs),
      baseHom (GensData.denote N gs) n hS.base_inv g • Align.jdec (N - n) jd =
        Align.jdec (N - n) jd) :
    (rebaseModel X.O n N (cellPosD n jd.2.1) gs).1 = n + (cellPosD n jd.2.1).length ∧
      n + (cellPosD n jd.2.1).length ≤ N ∧
      GroupValid DV (n + (cellPosD n jd.2.1).length)
        (rebaseModel X.O n N (cellPosD n jd.2.1) gs).2.1
        (rebaseModel X.O n N (cellPosD n jd.2.1) gs).2.2 ∧
      GensData.denote (n + (cellPosD n jd.2.1).length)
          (rebaseModel X.O n N (cellPosD n jd.2.1) gs).2.1 =
        (rebaseHom hS.hint.le (isInvariant_strSet hS.base_inv) (dv_cellPos_valid hJv hS.hint.le)
          (dv_cellPos_blocks hJv) (dv_cellPos_perm hS.base_inv hJv hK)).range := by
  obtain ⟨hdeg, hval, hden⟩ := dv_rebase_den (X := X) (DV := DV) hO hS.hint.le hS.base_inv
    (dv_cellPos_valid hJv hS.hint.le) (dv_cellPos_blocks hJv)
    (dv_cellPos_perm hS.base_inv hJv hK) hS.kvalid.1
  refine ⟨hdeg, ?_, hval, hden⟩
  rw [dv_length_cellPos]
  have := dv_nc_le hJv
  have := hS.hint.le
  omega

/-- The M1 child of the CJ path is a hinted child with labels outside `V₀` when those are not
constant; its degree is at most `N`. -/
theorem rd_deg_cj3 {X : Ctx (groupSig D)} (hO : MeetsContractOn DV deriveOps X.O) {n N : ℕ}
    {gsG gs : GensData} {w : WinData} {L : LabelData} {d : D.denote} {O : List ℕ}
    (hS : DSetting DV n N gsG w L gs d O) {jd : Align.JData}
    (hK : ∀ g : ↥(GensData.denote N gs),
      baseHom (GensData.denote N gs) n hS.base_inv g • Align.jdec (N - n) jd =
        Align.jdec (N - n) jd)
    (hcA : ncBD n N (labDiffD (markArr (N - n) jd.1) L O) O = true) :
    (m1Model X.O n N (N, gs, d) (WinData.ofPoints N O)
      (labDiffD (markArr (N - n) jd.1) L O)).1.1 ≤ N :=
  rd_m1_deg (fun op x h hx => hO op x (deriveOps_of_m1 h) hx) hS.kvalid
    (dv_labDiff_hint hS hK hcA)

/-- **The degree of `P` for tags `3` and `5`**, without a coloured Johnson structure (where tag
`5` does not occur). -/
theorem rd_deg_free {X : Ctx (groupSig D)} (hO : MeetsContractOn DV deriveOps X.O) {n N : ℕ}
    {gsG gs : GensData} {w : WinData} {L : LabelData} {d : D.denote} {O : List ℕ}
    (hS : DSetting DV n N gsG w L gs d O) {st : ℕ × CJData} (hst : st.1 ≠ 2)
    (h : (deriveModel X.O n N (N, gs, d) O L st).1 = 3 ∨
      (deriveModel X.O n N (N, gs, d) O L st).1 = 5) :
    (deriveModel X.O n N (N, gs, d) O L st).2.1.1.1 ≤ N := by
  rcases h with h | h
  · have he : (st.1 == 2) = false := by simpa using hst
    simp only [deriveModel, he, Bool.cond_false] at h ⊢
    unfold deriveFreeModel at h ⊢
    cases hc : ncBD n N L O
    · rw [hc] at h
      simp [noHintD, outD] at h
    · rw [hc] at h
      simp only [Bool.cond_true] at h ⊢
      rw [rd_m1Cont_tag3 h]
      exact rd_m1_deg (fun op x h' hx => hO op x (deriveOps_of_m1 h') hx) hS.kvalid
        (hS.hintK hc)
  · exact absurd h (rd_free_ne5 hst)

/-- **The degree of `P` for tags `3` and `5`** with a coloured Johnson structure. -/
theorem rd_deg_cj {X : Ctx (groupSig D)} (hO : MeetsContractOn DV deriveOps X.O) {n N : ℕ}
    {gsG gs : GensData} {w : WinData} {L : LabelData} {d : D.denote} {O : List ℕ}
    (hS : DSetting DV n N gsG w L gs d O) {st : ℕ × CJData} (hst : st.1 = 2)
    (hJv : Align.JValid (N - n) st.2.1)
    (hK : ∀ g : ↥(GensData.denote N gs),
      baseHom (GensData.denote N gs) n hS.base_inv g • Align.jdec (N - n) st.2.1 =
        Align.jdec (N - n) st.2.1)
    (h : (deriveModel X.O n N (N, gs, d) O L st).1 = 3 ∨
      (deriveModel X.O n N (N, gs, d) O L st).1 = 5) :
    (deriveModel X.O n N (N, gs, d) O L st).2.1.1.1 ≤ N := by
  have he : (st.1 == 2) = true := by simpa using hst
  simp only [deriveModel, he, Bool.cond_true] at h ⊢
  unfold deriveCJModel at h ⊢
  cases hc : ncBD n N L O
  · rw [hc] at h
    simp [noHintD, outD] at h
  rw [hc] at h
  simp only [Bool.cond_true] at h ⊢
  cases hcA : ncBD n N (labDiffD (markArr (N - n) st.2.1.1) L O) O
  · rw [hcA] at h
    simp only [Bool.cond_false] at h ⊢
    rcases h with h | h
    · exact absurd h rd_john_ne3
    · revert h
      unfold johnStepD outD
      cases ncBD n (n + st.2.1.2.1.length)
          (labJUD st.2.1.2.1.length (markArr (N - n) st.2.1.1) st.2.1.2.2.2 L O) O
      · intro _
        simp only [Bool.cond_false]
        rw [(rd_cells_rebase (fun op x h' hx => hO op x (by
          rw [show op = .generate from h']; simp [deriveOps]) hx) hS hJv hK).1]
        exact (rd_cells_rebase (fun op x h' hx => hO op x (by
          rw [show op = .generate from h']; simp [deriveOps]) hx) hS hJv hK).2.1
      · cases leQD st.2.1.2.1.length (N - n) <;> simp
  · rw [hcA] at h
    simp only [Bool.cond_true] at h ⊢
    rcases h with h | h
    · rw [rd_m1Cont_tag3 h]
      exact rd_deg_cj3 hO hS hK hcA
    · exact absurd h rd_m1Cont_ne5

/-- **The factor of the Johnson fallback** (tag `5`): at most `u!` coset representatives, where
`u` is the number of union cells at the first point of `O`. -/
theorem rd_cj_reps5 {X : Ctx (groupSig D)} (hO : MeetsContractOn DV deriveOps X.O) {n N : ℕ}
    {gsG gs : GensData} {w : WinData} {L : LabelData} {d : D.denote} {O : List ℕ}
    (hS : DSetting DV n N gsG w L gs d O) {st : ℕ × CJData} (hst : st.1 = 2)
    (hJv : Align.JValid (N - n) st.2.1)
    (hK : ∀ g : ↥(GensData.denote N gs),
      baseHom (GensData.denote N gs) n hS.base_inv g • Align.jdec (N - n) st.2.1 =
        Align.jdec (N - n) st.2.1)
    (h5 : (deriveModel X.O n N (N, gs, d) O L st).1 = 5) :
    (deriveModel X.O n N (N, gs, d) O L st).2.1.2.2.length ≤
      ((labJUD st.2.1.2.1.length (markArr (N - n) st.2.1.1) st.2.1.2.2.2 L O).getD
        (O.headD 0) []).length.factorial := by
  have he : (st.1 == 2) = true := by simpa using hst
  simp only [deriveModel, he, Bool.cond_true] at h5 ⊢
  unfold deriveCJModel at h5 ⊢
  cases hc : ncBD n N L O
  · rw [hc] at h5
    simp [noHintD, outD] at h5
  rw [hc] at h5
  simp only [Bool.cond_true] at h5 ⊢
  cases hcA : ncBD n N (labDiffD (markArr (N - n) st.2.1.1) L O) O
  swap
  · rw [hcA] at h5
    exact absurd h5 rd_m1Cont_ne5
  rw [hcA] at h5
  simp only [Bool.cond_false] at h5 ⊢
  unfold johnStepD outD at h5 ⊢
  cases hcU : ncBD n (n + st.2.1.2.1.length)
    (labJUD st.2.1.2.1.length (markArr (N - n) st.2.1.1) st.2.1.2.2.2 L O) O
  swap
  · rw [hcU] at h5
    cases hq : leQD st.2.1.2.1.length (N - n) <;> simp [hq] at h5
  simp only [Bool.cond_false]
  -- the group re-based onto the cells
  have hOr : MeetsContractOn DV rebaseOps X.O := fun op x h' hx => hO op x (by
    rw [show op = .generate from h']; simp [deriveOps]) hx
  obtain ⟨hdeg, -, hval, hden⟩ := rd_cells_rebase hOr hS hJv hK
  have hn := hS.hint.le
  have hbase := hS.base_inv
  have hstr := isInvariant_strSet hbase
  have hw := dv_cellPos_valid (n := n) hJv hn
  have hbs := dv_cellPos_blocks (N := N) (n := n) hJv
  have hGb := dv_cellPos_perm hbase hJv hK
  set N₄ := n + (cellPosD n st.2.1.2.1).length with hN₄
  set LU := labJUD st.2.1.2.1.length (markArr (N - n) st.2.1.1) st.2.1.2.2.2 L O with hLU
  set u₀ := O.headD 0 with hu₀def
  have hu₀ : u₀ ∈ O := by
    obtain ⟨a, rest, h⟩ := List.exists_cons_of_ne_nil hS.ne
    rw [hu₀def, h]
    exact List.mem_cons_self
  have hu₀N : u₀ < N := hS.owin.lt u₀ hu₀
  set cl := LU.getD u₀ [] with hcl
  have hclnd : cl.Nodup := by
    rw [hcl, hLU, dv_getD_labJU hS.nodup hu₀]
    exact nodup_jUnionData _ _ _ _
  have hcllt : ∀ c ∈ cl, c < st.2.1.2.1.length := fun c hc => ((dv_mem_labJU hS hJv hu₀ c).1 hc).1
  have hconst : ∀ v ∈ O, ∀ c < st.2.1.2.1.length, c ∈ LU.getD v [] ↔ c ∈ cl := by
    intro v hv c hc
    have h := congrArg (fun T => (⟨c, by omega⟩ : Fin (n + st.2.1.2.1.length - n)) ∈ T)
      (DSetting.const hcU v hv u₀ hu₀)
    simpa only [SoJProg.mem_setOf, eq_iff_iff] using h
  rcases hG4 : rebaseModel X.O n N (cellPosD n st.2.1.2.1) gs with ⟨N₄', gs₄, d₄⟩
  rw [hG4] at hdeg hval hden
  change N₄' = N₄ at hdeg
  subst hdeg
  have hHS : ∀ g ∈ GensData.denote N₄ gs₄, ∀ u : Fin N₄, u.val ∈ cl.map (n + ·) →
      (g u).val ∈ cl.map (n + ·) := by
    rw [hden]
    rintro _ ⟨g, rfl⟩ u hu
    obtain ⟨c, hc, hcu⟩ := List.mem_map.1 hu
    have hcl' := hcllt c hc
    rw [rebaseHom_ge hn hstr hw hbs hGb g (show n ≤ u.val by omega)]
    refine List.mem_map.2 ⟨_, ?_, rfl⟩
    have hgc := (dv_labJU_equivar hS hJv hK g.2 hu₀ hu₀N _).2 ⟨c, hc, rfl⟩
    have hgu₀ : (g.1 ⟨u₀, hu₀N⟩).val ∈ O := hS.oinv g.1 g.2 ⟨u₀, hu₀N⟩ hu₀
    rw [show u.val - n = c by omega]
    refine (hconst _ hgu₀ _ ?_).1 hgc
    exact ((dv_mem_labJU hS hJv hgu₀ _).1 hgc).1
  have hOs : MeetsContractOn DV stabOps X.O := fun op x h' hx => hO op x (by
    rcases h' with h' | h' <;> simp [deriveOps, h']) hx
  have := CertProg.pointStabs_reps_le_factorial (X := X) (S := cl.map (n + ·)) hOs hval
    (hclnd.map fun a b h => by simpa using h)
    (fun u hu => by
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hu
      have := hcllt c hc
      rw [hN₄, dv_length_cellPos]
      omega) hHS
  rw [List.length_map] at this
  change (pointStabsModel X.O (N₄, gs₄, d₄) (cl.map (n + ·))).2.length ≤ _
  exact this

end ModelFacts

/-! ### The tags -/

section TagSpecs

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}

/-- The backend operations of reduce-and-derive. -/
def rdOps (op : GroupOp) : Prop :=
  op = .orbits ∨ op = .generate ∨ op = .stabilizer ∨ op = .orbitTransversal ∨ op = .lift ∨
    op = .kernel ∨ op = .cosetReps

/-- **The result of one orbit**: a correct answer for the orbit `O` in the coset `τ • ⟨gs⟩`
with at most `sIn` generators, within the children's costs plus `W`; the children `g` have
windows of at most `F · |O|` points in total and are `StepChild` children of the parent. -/
def RDRes (X : Ctx (groupSig D)) (body : a.denote → Prog (groupSig D) (a, b) Ty.denote b)
    (DV : ℕ → GensData → D.denote → Prop) (C : ℕ → Option ℕ → ℕ) (N n : ℕ) (w : WinData)
    (xy : StrData × StrData) (τ : PermData) (gs : GensData) (O : List ℕ) (sIn F W : ℕ)
    (p : Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)) : Prop :=
  ∃ (ans : AnswerData D) (g : List (ℕ × Option ℕ)),
    RunsWithin X body p ans ((g.map fun x => C x.1 x.2).sum + W) ∧
    AnsOK DV N (ptsSet N O) (PermData.denote N τ) (GensData.denote N gs) (xy.1.denote N)
      (xy.2.denote N) ans ∧
    (∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sIn) ∧
    (g.map Prod.fst).sum ≤ F * O.length ∧ (∀ x ∈ g, StepChild w.1.length (N - n) x) ∧
      ∀ x ∈ g, 1 ≤ x.1

theorem RDRes.mono {C : ℕ → Option ℕ → ℕ} {N n : ℕ} {w : WinData} {xy : StrData × StrData}
    {τ : PermData} {gs : GensData} {O : List ℕ} {sIn F W W' : ℕ}
    {p : Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)}
    (h : RDRes X body DV C N n w xy τ gs O sIn F W p) (hW : W ≤ W') :
    RDRes X body DV C N n w xy τ gs O sIn F W' p := by
  obtain ⟨ans, g, hr, hok, hg, hs, hc⟩ := h
  exact ⟨ans, g, hr.mono (by omega), hok, hg, hs, hc⟩

variable {sub : HInstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)}
  {C : ℕ → Option ℕ → ℕ} {s : ℕ} {xy : StrData × StrData} {w : WinData} {σd : PermData}
  {N : ℕ} {gsG : GensData} {dG : D.denote} {n₀ n : ℕ} {L : LabelData}
  {sIn Lg F Blift Bgen Bo Bk Bcr : ℕ} {τ : PermData} {gs : GensData} {d : D.denote}
  {O : List ℕ}

/-- **Tag `0`**: the labels are constant on `O`, a sub-call without a hint. -/
theorem rd_sem0 (hI : HInstValid DV (((xy, w, σd, N, gsG, dG), n₀, n, some L) : HInstData D))
    (hsub : HSubSolves X body DV sub
      (fun J => SizeChild sIn (((xy, w, σd, N, gsG, dG), n₀, n, some L) : HInstData D) J ∧
        StepChild w.1.length (N - n) (J.winSize, J.baseOpt)) C s)
    (hs : s ≤ sIn) (hF1 : 1 ≤ F) (hτ : τ.Valid N) (hS : DSetting DV n N gsG w L gs d O)
    (hgs : gs.length ≤ sIn) (hhalf : 2 * O.length ≤ w.1.length) :
    RDRes X body DV C N n w xy τ gs O sIn F 4
      (Main.plainSub sub n₀ n (xy, (WinData.ofPoints N O, (τ, (N, gs, d))))) := by
  have hJv : InstData.Valid (D := D) (xy, (WinData.ofPoints N O, (τ, (N, gs, d)))) DV :=
    ⟨hS.owin, hτ, hS.kvalid, hS.oinv⟩
  have hHI := sb_hinstValid_plain (n₀ := n₀) hJv hI.le hS.base_inv hS.win_lt hS.kfaith
  obtain ⟨ans, hr, hok, hg⟩ := hsub _ hHI
    ⟨⟨rfl, le_rfl, le_max_left _ _, hgs, SizeChild.lab_none rfl le_rfl rfl⟩, hS.len_le,
      Or.inr ⟨rfl, hhalf⟩⟩
  refine ⟨ans, [(O.length, none)], ?_, hok, fun c hc => (hg c hc).trans hs, ?_, ?_, ?_⟩
  · refine (RunsWithin.plainSub n₀ n _ hr).mono ?_
    change C O.length none + 4 ≤ _
    simp
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    exact Nat.le_mul_of_pos_left _ hF1
  · intro x hx
    rw [List.mem_singleton] at hx
    subst hx
    exact ⟨hS.len_le, Or.inr ⟨rfl, hhalf⟩⟩
  · intro x hx
    rw [List.mem_singleton] at hx
    subst hx
    exact List.length_pos_of_ne_nil hS.ne

/-- **Tags `1`, `2`, `4`**: a sub-call on the hinted child, with base at most `3m/4`. -/
theorem rd_sem124 (hO : MeetsContractOn DV rdOps X.O)
    (hPre : ∀ op x, rdOps op → GroupPre DV op x → X.Pre op x)
    (hI : HInstValid DV (((xy, w, σd, N, gsG, dG), n₀, n, some L) : HInstData D))
    (hsub : HSubSolves X body DV sub
      (fun J => SizeChild sIn (((xy, w, σd, N, gsG, dG), n₀, n, some L) : HInstData D) J ∧
        StepChild w.1.length (N - n) (J.winSize, J.baseOpt)) C s)
    (hB : RDBounds X DV n N sIn Lg Blift Bgen Bo Bk Bcr) (hs : s ≤ sIn)
    (hLg : F * (sIn + 1) ≤ Lg) (hF1 : 1 ≤ F) (hτ : τ.Valid N)
    (hS : DSetting DV n N gsG w L gs d O) (hgs : gs.length ≤ sIn) {N' : ℕ} {gs' : GensData}
    {d' : D.denote} {w' : WinData} {L' : LabelData} (hc : ChildOK DV n N gs N' gs' d' w' L')
    (hw : w'.1 = O) (hm : 4 * (N' - n) ≤ 3 * (N - n)) (hgs' : gs'.length ≤ sIn)
    (hLab : LabInvAt n₀ (N - n) (labLen L) → LabInvAt n₀ (N' - n) (labLen L')) :
    RDRes X body DV C N n w xy τ gs O sIn F (viaChildCost N N n s Blift Bgen)
      (Main.viaChildProg sub xy τ (N, gs, d) n₀ n (N', gs', d') w' (some L')) := by
  have hOt : MeetsContractOn DV transferOps X.O := fun op x h => hO op x (by
    rcases h with h | h <;> simp [rdOps, h])
  have hPt : ∀ op x, transferOps op → GroupPre DV op x → X.Pre op x := fun op x h hx =>
    hPre op x (by rcases h with h | h <;> simp [rdOps, h]) hx
  have hN' : N' ≤ N := by
    have := hc.hint.le
    have := hI.le
    change n ≤ N at this
    omega
  have hLs : s ≤ Lg := by
    have : sIn + 1 ≤ F * (sIn + 1) := Nat.le_mul_of_pos_left _ hF1
    omega
  obtain ⟨ans, hr, hok, hg⟩ := RunsWithin.viaChildProg (X := X) (body := body) (n₀ := n₀)
    (n := n) (N := N) hOt hPt hsub hS.kvalid hI.le hS.base_inv hτ xy hc.rel hc.labels
    ⟨⟨rfl, le_rfl, le_max_of_le_left hN', hgs',
      fun hI' => childHInst_labInv hI'.n_le (hLab (hI'.hint L rfl))⟩, by
      change w'.1.length ≤ w.1.length
      rw [hw]
      exact hS.len_le, Or.inl ⟨N' - n, rfl, hm⟩⟩
    (hB.lift N le_rfl gs d hS.kvalid hgs)
    (fun hs' hv hl _ => hB.gen N le_rfl hs' hv (hl.trans hLs))
  rw [hw] at hr hok
  refine ⟨ans, [(O.length, some (N' - n))], ?_, hok,
    hg sIn (fun hs' hv _ => hB.genOut N le_rfl hs' hv), ?_, ?_, ?_⟩
  · refine hr.mono ?_
    have := rd_viaChildCost_mono (n := n) (s := s) (Blift := Blift) (Bgen := Bgen)
      (le_refl N) hN'
    change C O.length (some (N' - n)) + _ ≤ _
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    omega
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    exact Nat.le_mul_of_pos_left _ hF1
  · intro x hx
    rw [List.mem_singleton] at hx
    subst hx
    exact ⟨hS.len_le, Or.inl ⟨N' - n, rfl, hm⟩⟩
  · intro x hx
    rw [List.mem_singleton] at hx
    subst hx
    exact List.length_pos_of_ne_nil hS.ne

/-- **Tag `6`** (stuck): the kernel reduction of the orbit `O`, whose labels are not constant,
inside the hinted instance `(O, τ • H, L)`. -/
theorem rd_sem6 (hO : MeetsContractOn DV rdOps X.O)
    (hPre : ∀ op x, rdOps op → GroupPre DV op x → X.Pre op x)
    (hI : HInstValid DV (((xy, w, σd, N, gsG, dG), n₀, n, some L) : HInstData D))
    (hsub : HSubSolves X body DV sub
      (fun J => SizeChild sIn (((xy, w, σd, N, gsG, dG), n₀, n, some L) : HInstData D) J ∧
        StepChild w.1.length (N - n) (J.winSize, J.baseOpt)) C s)
    (hB : RDBounds X DV n N sIn Lg Blift Bgen Bo Bk Bcr) (hs : s ≤ sIn)
    (hLg : F * (sIn + 1) ≤ Lg) (hF6 : (N - n).factorial ≤ F) (hτ : τ.Valid N)
    (hS : DSetting DV n N gsG w L gs d O) (hgs : gs.length ≤ sIn)
    (hnc : ncBD n N L O = true) :
    RDRes X body DV C N n w xy τ gs O sIn F (rd6Cost N n w.1.length s sIn Bk Bo Bcr Bgen)
      (Main.kerRedProg sub n₀ n (xy, (WinData.ofPoints N O, (τ, (N, gs, d))))) := by
  have hOk : MeetsContractOn DV kerRedOps X.O := fun op x h => hO op x (by
    rcases h with h | h | h | h <;> simp [rdOps, h])
  have hPk : ∀ op x, kerRedOps op → GroupPre DV op x → X.Pre op x := fun op x h hx =>
    hPre op x (by rcases h with h | h | h | h <;> simp [rdOps, h]) hx
  have hJv : InstData.Valid (D := D) (xy, (WinData.ofPoints N O, (τ, (N, gs, d)))) DV :=
    ⟨hS.owin, hτ, hS.kvalid, hS.oinv⟩
  have hIP : HInstValid DV (((xy, WinData.ofPoints N O, τ, N, gs, d), n₀, n, some L) :
      HInstData D) :=
    ⟨hJv, hI.le, hS.base_inv, hS.win_lt, hS.kfaith, fun L' h => by
      cases h
      exact ⟨hS.hintK hnc, hS.otrans⟩⟩
  -- the number of kernel cosets
  obtain ⟨-, -, -, -, -, -, -, hrlen⟩ := RunsWithin.kerProg (X := X) (body := body) (n := n)
    (fun op x hop hx => hO op x (by rcases hop with h | h <;> simp [rdOps, h]) hx)
    (fun op x hop hx => hPre op x (by rcases hop with h | h <;> simp [rdOps, h]) hx)
    hS.kvalid hS.base_inv (hB.kernel gs d hS.kvalid hgs)
    (hB.cosetReps gs d hS.kvalid hgs hS.base_inv)
  have hfact : (kerReps X.O n (N, gs, d)).length ≤ (N - n).factorial := by
    rw [hrlen]
    calc Nat.card (baseHom (GensData.denote N gs) n hS.base_inv).range
        ≤ Nat.card (Perm (Fin (N - n))) := Subgroup.card_le_card_group _
      _ = (N - n).factorial := by
          rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  have hkg := hB.kerGens gs d hS.kvalid hgs
  have hOw : O.length ≤ w.1.length := hS.len_le
  obtain ⟨ans, ch, hr, hok, hg, hch, -⟩ := RunsWithin.kerRedProg (X := X) (body := body) hOk hPk
    hIP hJv le_rfl (fun i hi => hi)
    (hsub.mono fun J hJ => ⟨⟨hJ.1.n₀, hJ.1.n_le, hJ.1.degree_le,
      hJ.1.gens_le.trans (max_le hs hkg), fun hI' => hJ.1.lab ⟨hI'.n_le, hI'.hint⟩⟩,
      hJ.2.1.trans hOw,
      hJ.2.2.imp id fun h => ⟨h.1, h.2.trans hOw⟩⟩)
    (hB.kernel gs d hS.kvalid hgs) (hB.kerOrbits gs d _ hS.kvalid hgs hS.owin)
    (hB.cosetReps gs d hS.kvalid hgs hS.base_inv)
    (fun hs' hv hl _ => hB.gen N le_rfl hs' hv (by
      have h1 : max s (kerModel X.O n (N, gs, d)).2.1.length ≤ sIn := max_le hs hkg
      have h2 : (kerReps X.O n (N, gs, d)).length *
          (max s (kerModel X.O n (N, gs, d)).2.1.length + 1) ≤ (N - n).factorial * (sIn + 1) :=
        Nat.mul_le_mul hfact (by omega)
      have h3 : (N - n).factorial * (sIn + 1) ≤ F * (sIn + 1) := Nat.mul_le_mul_right _ hF6
      omega))
  have e : (WinData.ofPoints N O).1 = O := rfl
  rw [e] at hr
  refine ⟨ans, ch, ?_, hok, hg sIn (fun hs' hv _ => hB.genOut N le_rfl hs' hv), ?_, ?_,
    hch.pos⟩
  · refine hr.mono ?_
    have := rd_kerRedCost_mono (N := N) (n := n) (s := s) (Bk := Bk) (Bo := Bo) (Bcr := Bcr)
      (Bgen := Bgen) hOw hfact hkg
    simp only [rd6Cost]
    omega
  · have h1 := hch.sum_le
    change (ch.map Prod.fst).sum ≤ (kerReps X.O n (N, gs, d)).length * O.length at h1
    have h2 : (kerReps X.O n (N, gs, d)).length * O.length ≤ F * O.length :=
      Nat.mul_le_mul_right _ (hfact.trans hF6)
    omega
  · intro x hx
    obtain ⟨h1, h2⟩ := hch.pred x hx
    exact ⟨h1.trans hOw, h2.imp id fun h => ⟨h.1, h.2.trans hOw⟩⟩

/-- **Tag `3`**: the block-stabilizer loop (`m2bLoopProg`) on the M1 child `P`, through which
the coset of `H` is solved (`viaChildProg`); the children are `M2bChild` children of `O` with a
base of at most `m/2` points, `|reps| ≤ m` copies. -/
theorem rd_sem3 (hO : MeetsContractOn DV rdOps X.O)
    (hPre : ∀ op x, rdOps op → GroupPre DV op x → X.Pre op x)
    (hI : HInstValid DV (((xy, w, σd, N, gsG, dG), n₀, n, some L) : HInstData D))
    (hsub : HSubSolves X body DV sub
      (fun J => SizeChild sIn (((xy, w, σd, N, gsG, dG), n₀, n, some L) : HInstData D) J ∧
        StepChild w.1.length (N - n) (J.winSize, J.baseOpt)) C s)
    (hB : RDBounds X DV n N sIn Lg Blift Bgen Bo Bk Bcr) (hs : s ≤ sIn)
    (hLg : F * (sIn + 1) ≤ Lg) (hF1 : 1 ≤ F) (hFm : N - n ≤ F) (hτ : τ.Valid N)
    (hS : DSetting DV n N gsG w L gs d O) (hgs : gs.length ≤ sIn)
    {N₁ : ℕ} {gs₁ : GensData} {d₁ : D.denote} {w₁ : WinData} {L₁ : LabelData}
    {Rgs : GensData} {Rd : D.denote} {reps : List PermData} {N' : ℕ} {gs' : GensData}
    {d' : D.denote} {L' : LabelData}
    (hP : ChildOK DV n N gs N₁ gs₁ d₁ w₁ L₁) (hw₁ : w₁.1 = O)
    (hR : GroupValid DV N₁ Rgs Rd)
    (hRP : GensData.denote N₁ Rgs ≤ GensData.denote N₁ gs₁)
    (hreps : ∀ r ∈ reps, PermData.Valid N₁ r)
    (hcov : IsLeftCover (GensData.denote N₁ gs₁) (GensData.denote N₁ Rgs)
      (fun i : Fin reps.length => PermData.denote N₁ (reps.get i)))
    (hlen : reps.length ≤ N - n)
    (hG' : GroupValid DV N' gs' d') (hm : 2 * (N' - n) ≤ N - n)
    (hfaith : ∀ g ∈ GensData.denote N' gs', (∀ j : Fin N', j.val < n → g j = j) → g = 1)
    (hinv : IsInvariant (GensData.denote N' gs') ((WinData.ofPoints N' O).denote N'))
    (hiso : ∃ θ : ↥(GensData.denote N₁ Rgs) ≃* ↥(GensData.denote N' gs'),
      ∀ (g : ↥(GensData.denote N₁ Rgs)) (j : ℕ) (hj : j < N₁) (hj' : j < N'), j < n →
        ((θ g : Perm (Fin N')) ⟨j, hj'⟩).val = (g.1 ⟨j, hj⟩).val)
    (hhint : ∀ wO : WinData, (∀ i ∈ wO.1, i ∈ O) → wO.1 ≠ [] →
      IsInvariant (GensData.denote N₁ Rgs) (wO.denote N₁) → HintValid n N' gs' wO L')
    (hN₁ : N₁ ≤ N) (hRs : Rgs.length ≤ sIn) (hgs' : gs'.length ≤ sIn)
    (hlab : labLen L' ≤ labLen L) :
    RDRes X body DV C N n w xy τ gs O sIn F
      (viaChildCost N N n sIn Blift Bgen +
        m2bLoopCost N N n w.1.length (N - n) sIn sIn Blift Bgen Bo Bgen + 5)
      (Main.viaChildProg (Main.rd3Inner sub (N₁, Rgs, Rd) (N', gs', d') reps O L' n₀ n) xy τ
        (N, gs, d) n₀ n (N₁, gs₁, d₁) (WinData.ofPoints N₁ O) none) := by
  have hOt : MeetsContractOn DV transferOps X.O := fun op x h => hO op x (by
    rcases h with h | h <;> simp [rdOps, h])
  have hPt : ∀ op x, transferOps op → GroupPre DV op x → X.Pre op x := fun op x h hx =>
    hPre op x (by rcases h with h | h <;> simp [rdOps, h]) hx
  have hOm : MeetsContractOn DV m2bLoopOps X.O := fun op x h => hO op x (by
    rcases h with h | h | h <;> simp [rdOps, h])
  have hPm : ∀ op x, m2bLoopOps op → GroupPre DV op x → X.Pre op x := fun op x h hx =>
    hPre op x (by rcases h with h | h | h <;> simp [rdOps, h]) hx
  have hnN : n ≤ N := hI.le
  have hOw : O.length ≤ w.1.length := hS.len_le
  have hn₁ : n ≤ N₁ := hP.hint.le
  have hOP : IsInvariant (GensData.denote N₁ gs₁) (ptsSet N₁ O) := by
    have h := hP.inv
    rw [← ptsSet_eq_denote, hw₁] at h
    exact h
  have hRb : IsInvariant (GensData.denote N₁ Rgs) (baseSet n N₁) :=
    fun g hg => hP.hint.base_inv g (hRP hg)
  have hHO : HintValid n N' gs' (WinData.ofPoints N' O) L' :=
    hhint _ (fun i hi => hi) hS.ne (fun g hg u hu => hOP g (hRP hg) u hu)
  have hnN' : n ≤ N' := hHO.le
  have hN'N : N' ≤ N := by omega
  have hc3 : ChildRel DV n N₁ Rgs N' gs' d' (WinData.ofPoints N' O) :=
    ⟨hG', hnN', hHO.base_inv, WinData.valid_ofPoints hS.nodup (fun i hi => by
      have := hS.win_lt i hi
      omega), hHO.win_lt, hinv, hfaith, hiso⟩
  have hcP : ChildRel DV n N gs N₁ gs₁ d₁ (WinData.ofPoints N₁ O) :=
    ⟨hP.valid, hn₁, hP.hint.base_inv, WinData.valid_ofPoints hS.nodup (fun i hi => by
      have := hS.win_lt i hi
      omega), hS.win_lt, hOP, hP.faithful, hP.iso⟩
  have hsIn : sIn ≤ Lg := by
    have : sIn + 1 ≤ F * (sIn + 1) := Nat.le_mul_of_pos_left _ hF1
    omega
  have hrL : reps.length * (sIn + 1) ≤ Lg := by
    have : reps.length * (sIn + 1) ≤ F * (sIn + 1) :=
      Nat.mul_le_mul_right _ (hlen.trans hFm)
    omega
  -- the loop on the child instance
  obtain ⟨ans₁, ch, hr₁, hok₁, hg₁, hch₁⟩ := RunsWithin.m2bLoopProg_lab (X := X) (body := body)
    (gsP := gs₁) (xy := (padD N₁ xy.1, padCompD N₁ xy.2 τ)) (σd := PermData.one N₁) hOm hPm
    (hsub.mono fun J hJ => by
      obtain ⟨⟨h1, h2, h3, h5, h4⟩, hJL⟩ := hJ
      refine ⟨⟨h1, h2.le, ?_, h5, fun hI' => hI'.of_le h1 h2.le fun L₂ hL₂ =>
        ⟨L, rfl, ?_, by rw [hJL L₂ hL₂]; exact hlab⟩⟩, M2bChild.stepChild h4 hOw hm⟩
      · rw [h3]
        exact le_max_of_le_left hN'N
      · show J.inst.degree - J.n ≤ N - n
        rw [h3, h2]
        omega)
    hn₁ hR hRP hRb hOP hreps hcov hc3 hhint hs hgs' (PermData.valid_one N₁)
    (hB.lift N₁ hN₁ Rgs Rd hR hRs)
    (fun hs' hv hl _ => hB.gen N₁ hN₁ hs' hv (hl.trans hsIn))
    (fun Hd w₀ h1 h2 _ hpre => hB.orbits Hd w₀ (by rw [h1]; exact hN'N) h2 hpre)
    (fun hs' hv _ => hB.genOut N₁ hN₁ hs' hv)
    (fun hs' hv hl _ => hB.gen N₁ hN₁ hs' hv (hl.trans hrL))
  set K₃ := (ch.map fun x => C x.1 x.2).sum +
    m2bLoopCost N₁ N' n O.length reps.length sIn sIn Blift Bgen Bo Bgen + 5 with hK₃
  have hinner : HSubSolves X body DV
      (Main.rd3Inner (var := Ty.denote) (rec := (a, b)) (D := D) sub (N₁, Rgs, Rd) (N', gs', d')
        reps O L' n₀ n)
      (fun J => J = childHInst xy.1 xy.2 τ n₀ n (N₁, gs₁, d₁) (WinData.ofPoints N₁ O) none)
      (fun _ _ => K₃) sIn := by
    rintro J - rfl
    refine ⟨ans₁, ?_, hok₁, hg₁ sIn fun hs' hv _ => hB.genOut N₁ hN₁ hs' hv⟩
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      exact hr₁
    case hc =>
      simp only [Prim.cost]
      omega
  obtain ⟨ans, hr, hok, hg⟩ := RunsWithin.viaChildProg (X := X) (body := body) (n₀ := n₀)
    (n := n) (N := N) hOt hPt hinner hS.kvalid hnN hS.base_inv hτ xy hcP (L' := none)
    (fun _ h => by cases h) rfl (hB.lift N le_rfl gs d hS.kvalid hgs)
    (fun hs' hv hl _ => hB.gen N le_rfl hs' hv (hl.trans hsIn))
  refine ⟨ans, ch, ?_, hok, hg sIn (fun hs' hv _ => hB.genOut N le_rfl hs' hv), ?_, ?_,
    hch₁.pos⟩
  · refine hr.mono ?_
    have h1 := rd_m2bLoopCost_mono (n := n) (sIn := sIn) (sR := sIn) (Blift := Blift)
      (Bgen := Bgen) (Bo := Bo) (Bgen₂ := Bgen) hN₁ hN'N hOw hlen
    have h2 := rd_viaChildCost_mono (n := n) (s := sIn) (Blift := Blift) (Bgen := Bgen)
      (le_refl N) hN₁
    rw [hK₃]
    omega
  · have h1 := hch₁.sum_le
    have h2 : reps.length * O.length ≤ F * O.length :=
      Nat.mul_le_mul_right _ (hlen.trans hFm)
    omega
  · intro x hx
    exact M2bChild.stepChild (hch₁.pred x hx) hOw hm

/-- **The base of an isomorphic copy is invariant**: if `θ : K ≃* P` keeps the action on the
string positions `[0, n)` and `K` keeps its base invariant, so does `P`. -/
theorem rd_base_inv_of_iso {N N' n : ℕ} {K : Subgroup (Perm (Fin N))}
    {P : Subgroup (Perm (Fin N'))} (θ : ↥K ≃* ↥P)
    (hθ : ∀ (g : ↥K) (j : ℕ) (hj : j < N) (hj' : j < N'), j < n →
      ((θ g : Perm (Fin N')) ⟨j, hj'⟩).val = (g.1 ⟨j, hj⟩).val)
    (hK : IsInvariant K (baseSet n N)) (hn : n ≤ N) : IsInvariant P (baseSet n N') := by
  intro p hp u hu
  change n ≤ u.val at hu
  change n ≤ (p u).val
  by_contra hlt
  have hlt' : (p u).val < n := Nat.lt_of_not_le hlt
  set j := (p u).val with hj
  have hjN : j < N := by omega
  have hjN' : j < N' := (p u).2
  set g := θ.symm ⟨p⁻¹, P.inv_mem hp⟩ with hg
  have e := hθ g j hjN hjN' hlt'
  have h1 : ((θ g : ↥P) : Perm (Fin N')) = p⁻¹ := by
    rw [hg, MulEquiv.apply_symm_apply]
  have h2 : (p⁻¹ : Perm (Fin N')) ⟨j, hjN'⟩ = u := by
    have : (⟨j, hjN'⟩ : Fin N') = p u := Fin.ext rfl
    rw [this]
    exact p.symm_apply_apply u
  rw [h1, h2] at e
  have hs := isInvariant_strSet hK g.1 g.2 ⟨j, hjN⟩ hlt'
  change (g.1 ⟨j, hjN⟩).val < n at hs
  omega

/-- **Tag `5`** (the Johnson fallback): through the group `P` re-based onto the cells, a branch
over the cover of `P` by cosets of `R`, each by `seqProg` over the `R`-orbits of `O` without a
hint; the children have at most `|O|/2` points, `|reps| ≤ F` copies. -/
theorem rd_sem5 (hO : MeetsContractOn DV rdOps X.O)
    (hPre : ∀ op x, rdOps op → GroupPre DV op x → X.Pre op x)
    (hI : HInstValid DV (((xy, w, σd, N, gsG, dG), n₀, n, some L) : HInstData D))
    (hsub : HSubSolves X body DV sub
      (fun J => SizeChild sIn (((xy, w, σd, N, gsG, dG), n₀, n, some L) : HInstData D) J ∧
        StepChild w.1.length (N - n) (J.winSize, J.baseOpt)) C s)
    (hB : RDBounds X DV n N sIn Lg Blift Bgen Bo Bk Bcr) (hs : s ≤ sIn)
    (hLg : F * (sIn + 1) ≤ Lg) (hF1 : 1 ≤ F) (hτ : τ.Valid N)
    (hS : DSetting DV n N gsG w L gs d O) (hgs : gs.length ≤ sIn)
    {N' : ℕ} {Pgs : GensData} {Pd : D.denote} {Rgs : GensData} {Rd : D.denote}
    {reps : List PermData} (hN' : n ≤ N') (hPv : GroupValid DV N' Pgs Pd)
    (hPfaith : ∀ g ∈ GensData.denote N' Pgs, (∀ j : Fin N', j.val < n → g j = j) → g = 1)
    (hPinv : IsInvariant (GensData.denote N' Pgs) ((WinData.ofPoints N' O).denote N'))
    (hPiso : ∃ θ : ↥(GensData.denote N gs) ≃* ↥(GensData.denote N' Pgs),
      ∀ (g : ↥(GensData.denote N gs)) (j : ℕ) (hj : j < N) (hj' : j < N'), j < n →
        ((θ g : Perm (Fin N')) ⟨j, hj'⟩).val = (g.1 ⟨j, hj⟩).val)
    (hR : GroupValid DV N' Rgs Rd) (hRP : GensData.denote N' Rgs ≤ GensData.denote N' Pgs)
    (hreps : ∀ r ∈ reps, PermData.Valid N' r)
    (hcov : IsLeftCover (GensData.denote N' Pgs) (GensData.denote N' Rgs)
      (fun i : Fin reps.length => PermData.denote N' (reps.get i)))
    (hRinv : IsInvariant (GensData.denote N' Rgs) ((WinData.ofPoints N' O).denote N'))
    (hhalf : ∀ O' : List ℕ, O'.Nodup → (∀ v ∈ O', v ∈ O) →
      (∀ v ∈ O', ∀ v' ∈ O', SameOrbit (GensData.denote N' Rgs) v v') →
      2 * O'.length ≤ O.length)
    (hlenF : reps.length ≤ F) (hN'N : N' ≤ N) (hRs : Rgs.length ≤ sIn) :
    RDRes X body DV C N n w xy τ gs O sIn F
      (viaChildCost N N n sIn Blift Bgen + rd5Cost N w.1.length F sIn Bo Bgen)
      (Main.viaChildProg (Main.rd5Inner sub (N', Rgs, Rd) reps n₀ n) xy τ (N, gs, d) n₀ n
        (N', Pgs, Pd) (WinData.ofPoints N' O) none) := by
  have hOt : MeetsContractOn DV transferOps X.O := fun op x h => hO op x (by
    rcases h with h | h <;> simp [rdOps, h])
  have hPt : ∀ op x, transferOps op → GroupPre DV op x → X.Pre op x := fun op x h hx =>
    hPre op x (by rcases h with h | h <;> simp [rdOps, h]) hx
  have hOg : MeetsContractOn DV (· = .generate) X.O := fun op x h => hO op x (by
    simp [rdOps, h])
  have hPg : ∀ x, GroupPre DV .generate x → X.Pre .generate x := fun x hx =>
    hPre _ x (by simp [rdOps]) hx
  have hnN : n ≤ N := hI.le
  have hOw : O.length ≤ w.1.length := hS.len_le
  have hsIn : sIn ≤ Lg := by
    have : sIn + 1 ≤ F * (sIn + 1) := Nat.le_mul_of_pos_left _ hF1
    omega
  obtain ⟨θ, hθ⟩ := hPiso
  have hPb : IsInvariant (GensData.denote N' Pgs) (baseSet n N') :=
    rd_base_inv_of_iso θ hθ hS.base_inv hnN
  have hwv : (WinData.ofPoints N' O).Valid N' := WinData.valid_ofPoints hS.nodup (fun i hi => by
    have := hS.win_lt i hi
    omega)
  -- the orbits of `R` on `O`
  have hopre : GroupPre DV .orbits ((N', Rgs, Rd), WinData.ofPoints N' O) := ⟨hR, hwv, hRinv⟩
  have hos := hO .orbits _ (Or.inl rfl) hopre
  set os : List (List ℕ) := X.O.run GroupOp.orbits ((N', Rgs, Rd), WinData.ofPoints N' O)
    with hosdef
  obtain ⟨hseq, hunion⟩ := seqInputs_of_isOrbitPartition (n := N') hwv hos
  have hoO : ∀ o ∈ os, ∀ i ∈ o, i ∈ O := fun o ho i hi => sb_mem_win hos ho i hi
  have hoW : ∀ o ∈ os, o.length ≤ w.1.length ∧ 2 * o.length ≤ w.1.length := by
    intro o ho
    have h1 := sb_length_le_of_sub (hseq o ho).1 hS.nodup (hoO o ho)
    have h2 := hhalf o (hseq o ho).1 (hoO o ho) fun i hi j hj =>
      ((hos.2 o ho).2 i hi j).1 hj
    omega
  -- the sequential reduction inside each branch
  set xy' : StrData × StrData := (padD N' xy.1, padCompD N' xy.2 τ) with hxy'
  have hsq : SeqSub X body DV (fun J => Main.plainSub sub n₀ n J) xy' N' os
      (fun o => C o.length none + 4) s (max s Rgs.length) (GensData.denote N' Rgs) := by
    refine sb_seqSub hsub ?_
    rintro ⟨xy₂, w₂, σ₂, N₂, gs₂, d₂⟩ h1 hJv hdeg ⟨o, ho, hwo⟩ hgl hG
    change N₂ = N' at hdeg
    subst hdeg
    change w₂ = WinData.ofPoints N₂ o at hwo
    subst hwo
    refine ⟨sb_hinstValid_plain hJv hN' (fun g hg => hPb g (hRP (hG hg))) ?_
      (fun g hg => hPfaith g (hRP (hG hg))),
      ⟨rfl, le_rfl, le_max_of_le_left hN'N, hgl.trans (max_le hs hRs),
        SizeChild.lab_none rfl le_rfl rfl⟩,
      (hoW o ho).1, Or.inr ⟨rfl, (hoW o ho).2⟩⟩
    intro i hi
    exact hS.win_lt i (hoO o ho i hi)
  set Cb := blockBranchCost N' (fun o => C o.length none + 4) os with hCb
  have hbr : SubSolves X body DV (fun J => Programs.blockBranch (Main.plainSub sub n₀ n) xy' os J)
      (fun J => J.1 = xy' ∧ J.2.1 = WinData.ofPoints N' O ∧ J.2.2.2 = (N', Rgs, Rd) ∧
        (∃ r ∈ reps, J.2.2.1 = (PermData.one N').mul r) ∧ J.Valid DV)
      (fun _ => Cb) (max s Rgs.length) := by
    rintro ⟨xy₃, w₃, σ₃, Kd⟩ ⟨h₁, h₂, h₃, ⟨r, hr, h₄⟩, hJv⟩
    change xy₃ = xy' at h₁
    change w₃ = WinData.ofPoints N' O at h₂
    change Kd = (N', Rgs, Rd) at h₃
    change σ₃ = (PermData.one N').mul r at h₄
    subst xy₃ w₃ Kd σ₃
    obtain ⟨ans, hrun, hok, hg⟩ := RunsWithin.seqProg (X := X) (body := body)
      (sub := fun J => Main.plainSub sub n₀ n J) (n := N') (σd := (PermData.one N').mul r)
      (Gd := (N', Rgs, Rd)) rfl hJv.rep hR hseq hsq
    refine ⟨ans, ?_, ?_, hg⟩
    · apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        exact hrun
      case hc =>
        simp only [Prim.cost, hCb, blockBranchCost]
        omega
    · change AnsOK DV N' (WinData.denote N' (WinData.ofPoints N' O)) _ _ _ _ ans
      rw [← hunion]
      exact hok
  have hrL : reps.length * (max s Rgs.length + 1) ≤ Lg := by
    have h1 : max s Rgs.length ≤ sIn := max_le hs hRs
    have h2 : reps.length * (max s Rgs.length + 1) ≤ F * (sIn + 1) :=
      Nat.mul_le_mul hlenF (by omega)
    omega
  obtain ⟨ans₁, hr₁, hok₁, hg₁⟩ := RunsWithin.branchProg (X := X) (body := body) hOg hPg hwv
    (PermData.valid_one N') hR hRP hPinv hreps (ml_isLeftCover_map hcov) hbr
    (fun gs₀ hv hl _ => hB.gen N' hN'N gs₀ hv (hl.trans hrL))
  -- the children and the inner solver
  set osc := ((os.map fun o => ((o.length, none) : ℕ × Option ℕ)).map fun x => C x.1 x.2).sum
    with hosc
  set K₅ := 7 + Bo + reps.length * (24 * N' + Cb + max s Rgs.length + 45) + Bgen + 19 with hK₅
  have hBo' : X.B.call GroupOp.orbits ((N', Rgs, Rd), WinData.ofPoints N' O) os ≤ Bo :=
    hB.orbits _ _ hN'N hRs hopre
  have hinner : HSubSolves X body DV
      (Main.rd5Inner (var := Ty.denote) (rec := (a, b)) (D := D) sub (N', Rgs, Rd) reps n₀ n)
      (fun J => J = childHInst xy.1 xy.2 τ n₀ n (N', Pgs, Pd) (WinData.ofPoints N' O) none)
      (fun _ _ => K₅) sIn := by
    rintro J - rfl
    refine ⟨ans₁, ?_, hok₁, hg₁ sIn fun hs' hv _ => hB.genOut N' hN'N hs' hv⟩
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step ((RunsWithin.call (x := ((N', Rgs, Rd), WinData.ofPoints N' O))
        (hPre _ _ (Or.inl rfl) hopre)).mono hBo')
      exact hr₁
    case hc =>
      simp only [Prim.cost, hK₅]
      omega
  obtain ⟨ans, hr, hok, hg⟩ := RunsWithin.viaChildProg (X := X) (body := body) (n₀ := n₀)
    (n := n) (N := N) hOt hPt hinner hS.kvalid hnN hS.base_inv hτ xy
    (⟨hPv, hN', hPb, hwv, hS.win_lt, hPinv, hPfaith, θ, hθ⟩ :
      ChildRel DV n N gs N' Pgs Pd (WinData.ofPoints N' O))
    (L' := none) (fun _ h => by cases h) rfl (hB.lift N le_rfl gs d hS.kvalid hgs)
    (fun hs' hv hl _ => hB.gen N le_rfl hs' hv (hl.trans hsIn))
  refine ⟨ans,
    (List.replicate reps.length (os.map fun o => ((o.length, none) : ℕ × Option ℕ))).flatten,
    ?_, hok, hg sIn (fun hs' hv _ => hB.genOut N le_rfl hs' hv), ?_, ?_, ?_⟩
  · refine hr.mono ?_
    have hsum := sb_sum_length hos
    have hklen := sb_length_le hos
    change os.length ≤ O.length at hklen
    change (os.map List.length).sum = O.length at hsum
    have hCb' : Cb = 3 + osc + os.length * (2 * N' + 17) + 5 * O.length := by
      rw [hCb, blockBranchCost, sb_sum_seqCost, hsum, hosc]
      ring
    rw [sb_sum_replicate, ← hosc]
    have hv := rd_viaChildCost_mono (n := n) (s := sIn) (Blift := Blift) (Bgen := Bgen)
      (le_refl N) hN'N
    have hX : 24 * N' + 3 + os.length * (2 * N' + 17) + 5 * O.length + max s Rgs.length + 45 ≤
        24 * N + w.1.length * (2 * N + 17) + 5 * w.1.length + sIn + 48 := by
      have h1 : os.length * (2 * N' + 17) ≤ w.1.length * (2 * N + 17) :=
        Nat.mul_le_mul (by omega) (by omega)
      have h2 : max s Rgs.length ≤ sIn := max_le hs hRs
      omega
    have hY := Nat.mul_le_mul hlenF hX
    have e : reps.length * (24 * N' + Cb + max s Rgs.length + 45) = reps.length * osc +
        reps.length * (24 * N' + 3 + os.length * (2 * N' + 17) + 5 * O.length +
          max s Rgs.length + 45) := by
      rw [hCb']
      ring
    change K₅ + _ ≤ _
    simp only [hK₅, rd5Cost]
    omega
  · rw [sb_sum_replicate, List.map_map]
    have hsum := sb_sum_length hos
    change (os.map List.length).sum = O.length at hsum
    simp only [Function.comp_def]
    rw [hsum]
    exact Nat.mul_le_mul_right _ hlenF
  · intro x hx
    obtain ⟨l, hl, hxl⟩ := List.mem_flatten.1 hx
    obtain rfl := List.eq_of_mem_replicate hl
    obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hxl
    exact ⟨(hoW o ho).1, Or.inr ⟨rfl, (hoW o ho).2⟩⟩
  · intro x hx
    obtain ⟨l, hl, hxl⟩ := List.mem_flatten.1 hx
    obtain rfl := List.eq_of_mem_replicate hl
    obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hxl
    exact List.length_pos_of_ne_nil (hos.2 o ho).1

end TagSpecs

/-! ### The handle -/

section HandleSpec

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}

/-- **A derived hint with a nonzero tag has labels that are not constant** on the orbit (tag `0`
is exactly the constant case). -/
theorem rd_model_nc {Or : Oracle (groupSig D)} {n N : ℕ} {K : GroupData D.denote}
    {O : List ℕ} {L : LabelData} {st : ℕ × CJData} (h : (deriveModel Or n N K O L st).1 ≠ 0) :
    ncBD n N L O = true := by
  by_contra hc
  rw [Bool.not_eq_true] at hc
  apply h
  unfold deriveModel deriveCJModel deriveFreeModel
  cases st.1 == 2 <;> simp [hc, noHintD, outD]

variable {sub : HInstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)}
  {n₀ n N : ℕ} {L : LabelData} {st : ℕ × CJData} {xy : StrData × StrData} {τ : PermData}
  {gs : GensData} {d : D.denote} {O : List ℕ}

/-- The handle runs the derived hint, then the dispatch on it. -/
theorem rd_handle_run {r : DOut D} {Bd : ℕ} {ans : AnswerData D} {K : ℕ}
    (hder : RunsWithin X body (Main.deriveProg n N (N, gs, d) O L st) r Bd)
    (ht : RunsWithin X body (Main.rdTail sub n₀ n N xy (τ, (N, gs, d)) τ (N, gs, d) O r) ans K) :
    RunsWithin X body (Main.rdHandle sub n₀ n L st xy (τ, (N, gs, d)) O) ans (Bd + K + 3) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step hder
    exact ht
  case hc =>
    simp only [Prim.cost]
    omega

/-- **The orbits the handle receives**: an orbit `O` of a group `⟨gs⟩ ≤ K` with at most `sIn`
generators, inside the parent's window (the setting `DSetting` of the derived hint). -/
def RDSet (DV : ℕ → GensData → D.denote → Prop) (n N : ℕ) (gsG : GensData) (w : WinData)
    (L : LabelData) (gsK : GensData) (sIn : ℕ) (gs : GensData) (d : D.denote) (O : List ℕ) :
    Prop :=
  DSetting DV n N gsG w L gs d O ∧ gs.length ≤ sIn ∧
    GensData.denote N gs ≤ GensData.denote N gsK

variable {s : ℕ} {C : ℕ → Option ℕ → ℕ} {w : WinData} {σd : PermData} {gsG : GensData}
  {dG : D.denote} {sIn Lg F Blift Bgen Bo Bk Bcr : ℕ}

/-- **The handle is correct** on every orbit of the dynamic chain: the derived hint and the
dispatch on its tag give a correct answer, at the children's cost plus `rdOrbitWork`, with
children of at most `F · |O|` points in total, each a `StepChild` of the parent. -/
theorem rd_handle (hO : MeetsContractOn DV rdOps X.O)
    (hPre : ∀ op x, rdOps op → GroupPre DV op x → X.Pre op x)
    (hI : HInstValid DV (((xy, w, σd, N, gsG, dG), n₀, n, some L) : HInstData D))
    (hsub : HSubSolves X body DV sub
      (fun J => SizeChild sIn (((xy, w, σd, N, gsG, dG), n₀, n, some L) : HInstData D) J ∧
        StepChild w.1.length (N - n) (J.winSize, J.baseOpt)) C s)
    (hB : RDBounds X DV n N sIn Lg Blift Bgen Bo Bk Bcr) (hs : s ≤ sIn)
    (hLg : F * (sIn + 1) ≤ Lg) (hF1 : 1 ≤ F) (hFm : N - n ≤ F) {gsK : GensData}
    (hKG : GensData.denote N gsK ≤ GensData.denote N gsG) {Bd W6 : ℕ}
    (hD : ∀ gs d O, RDSet DV n N gsG w L gsK sIn gs d O →
      RDOrbit X body DV n N w L st sIn Bd gs d O)
    (h5 : (N - n).factorial ≤ F ∨ ∀ gs d O, RDSet DV n N gsG w L gsK sIn gs d O →
      (deriveModel X.O n N (N, gs, d) O L st).1 = 5 →
        (deriveModel X.O n N (N, gs, d) O L st).2.1.2.2.length ≤ F)
    (h6 : (∀ gs d O, RDSet DV n N gsG w L gsK sIn gs d O →
        (deriveModel X.O n N (N, gs, d) O L st).1 ≠ 6) ∨
      ((N - n).factorial ≤ F ∧ rd6Cost N n w.1.length s sIn Bk Bo Bcr Bgen ≤ W6)) :
    DynHandle X body DV (fun xy c O => Main.rdHandle sub n₀ n L st xy c O) xy N
      (GensData.denote N gsK) w.1 sIn
      (fun _ (g : List (ℕ × Option ℕ)) => (g.map fun x => C x.1 x.2).sum +
        rdOrbitWork N n w.1.length s sIn F Bd Blift Bgen Bo W6)
      (fun O (g : List (ℕ × Option ℕ)) => 1 ≤ O.length ∧ (g.map Prod.fst).sum ≤ F * O.length ∧
        (∀ x ∈ g, StepChild w.1.length (N - n) x) ∧ ∀ x ∈ g, 1 ≤ x.1) := by
  intro τ Hd O hτ hHd hHv hHs hHle hnd hne hsubO horb
  obtain ⟨Nd, gs, d⟩ := Hd
  change Nd = N at hHd
  subst Nd
  change GroupValid DV N gs d at hHv
  change gs.length ≤ sIn at hHs
  change GensData.denote N gs ≤ GensData.denote N gsK at hHle
  have hS : DSetting DV n N gsG w L gs d O :=
    ⟨(hI.hint L rfl).1, hI.valid.group.1, hI.valid.win, hI.valid.invariant, (hI.hint L rfl).2,
      hI.faithful, hHv, hHle.trans hKG, hnd, hsubO, horb, hne⟩
  have hset : RDSet DV n N gsG w L gsK sIn gs d O := ⟨hS, hHs, hHle⟩
  have hOw : O.length ≤ w.1.length := hS.len_le
  have hnN : n ≤ N := hI.le
  obtain ⟨hrun, hout, hdg, hsz⟩ := hD gs d O hset
  have h5' : (N - n).factorial ≤ F ∨ ((deriveModel X.O n N (N, gs, d) O L st).1 = 5 →
      (deriveModel X.O n N (N, gs, d) O L st).2.1.2.2.length ≤ F) :=
    h5.imp id fun h => h gs d O hset
  have h6' : (deriveModel X.O n N (N, gs, d) O L st).1 ≠ 6 ∨
      ((N - n).factorial ≤ F ∧ rd6Cost N n w.1.length s sIn Bk Bo Bcr Bgen ≤ W6) :=
    h6.imp (fun h => h gs d O hset) id
  have hnc : (deriveModel X.O n N (N, gs, d) O L st).1 = 6 → ncBD n N L O = true :=
    fun h => rd_model_nc (by rw [h]; decide)
  generalize deriveModel X.O n N (N, gs, d) O L st = r at hrun hout hdg hsz h5' h6' hnc
  have hW : 2 * N + 5 * O.length + 60 ≤ 2 * N + 5 * w.1.length + 60 := by omega
  cases hout with
  | noHint hc hhalf =>
    obtain ⟨ans, g, hr, hok, hg, hsum, hpred⟩ := rd_sem0 (sub := sub) (C := C) (n₀ := n₀)
      (d := d) hI hsub hs hF1 hτ hS hHs hhalf
    refine ⟨ans, g, (rd_handle_run hrun (rd_tail0 rfl hr)).mono ?_, hok, hg,
      List.length_pos_of_ne_nil hne, hsum, hpred⟩
    simp only [rdOrbitWork]
    omega
  | inter hc hw hm hlab =>
    obtain ⟨ans, g, hr, hok, hg, hsum, hpred⟩ := rd_sem124 (n₀ := n₀) hO hPre hI hsub hB hs
      hLg hF1 hτ hS hHs hc hw hm (hsz.2 (Or.inl rfl)) fun h => h.mono (by omega) hlab
    refine ⟨ans, g, (rd_handle_run hrun (rd_tail124 (Or.inl rfl) hr)).mono ?_, hok, hg,
      List.length_pos_of_ne_nil hne, hsum, hpred⟩
    simp only [rdOrbitWork]
    omega
  | blockLab hc hw hm hlab =>
    obtain ⟨ans, g, hr, hok, hg, hsum, hpred⟩ := rd_sem124 (n₀ := n₀) hO hPre hI hsub hB hs
      hLg hF1 hτ hS hHs hc hw (by omega) (hsz.2 (Or.inr (Or.inl rfl)))
      fun h => h.mono (by omega) hlab
    refine ⟨ans, g, (rd_handle_run hrun (rd_tail124 (Or.inr (Or.inl rfl)) hr)).mono ?_, hok, hg,
      List.length_pos_of_ne_nil hne, hsum, hpred⟩
    simp only [rdOrbitWork]
    omega
  | blockStab hP hw₁ hR hRP hreps hcov hlen hG' hm hfaith hinv hiso hhint hlab =>
    obtain ⟨hRs, hgs'⟩ := hsz.1 (Or.inl rfl)
    have hN₁ := hdg (Or.inl rfl)
    obtain ⟨ans, g, hr, hok, hg, hsum, hpred⟩ := rd_sem3 (n₀ := n₀) hO hPre hI hsub hB hs hLg
      hF1 hFm hτ hS hHs hP hw₁ hR hRP hreps hcov hlen hG' hm hfaith hinv hiso hhint hN₁ hRs hgs'
      hlab
    refine ⟨ans, g, (rd_handle_run hrun (rd_tail3 rfl hr)).mono ?_, hok, hg,
      List.length_pos_of_ne_nil hne, hsum, hpred⟩
    simp only [rdOrbitWork]
    dsimp only at hN₁ ⊢
    omega
  | johnUnion hc hw hm hlab =>
    obtain ⟨s', hl', hC', hs2, hs'⟩ := hlab
    obtain ⟨ans, g, hr, hok, hg, hsum, hpred⟩ := rd_sem124 (n₀ := n₀) hO hPre hI hsub hB hs
      hLg hF1 hτ hS hHs hc hw hm (hsz.2 (Or.inr (Or.inr rfl)))
      fun h => h.johnson hC' hs2 hs' hl'
    refine ⟨ans, g, (rd_handle_run hrun (rd_tail124 (Or.inr (Or.inr rfl)) hr)).mono ?_, hok,
      hg, List.length_pos_of_ne_nil hne, hsum, hpred⟩
    simp only [rdOrbitWork]
    omega
  | @johnFallback N' Pgs Pd Rgs Rd reps u hN' hPv hPfaith hPinv hPiso hR hRP hreps hcov hlen hu
      hRinv hhalf =>
    obtain ⟨hRs, -⟩ := hsz.1 (Or.inr rfl)
    have hN'N := hdg (Or.inr rfl)
    have hlenF : reps.length ≤ F := by
      rcases h5' with h | h
      · exact hlen.trans ((Nat.factorial_le hu).trans h)
      · exact h rfl
    obtain ⟨ans, g, hr, hok, hg, hsum, hpred⟩ := rd_sem5 (n₀ := n₀) hO hPre hI hsub hB hs hLg
      hF1 hτ hS hHs hN' hPv hPfaith hPinv hPiso hR hRP hreps hcov hRinv hhalf hlenF hN'N hRs
    refine ⟨ans, g, (rd_handle_run hrun (rd_tail5 rfl hr)).mono ?_, hok, hg,
      List.length_pos_of_ne_nil hne, hsum, hpred⟩
    simp only [rdOrbitWork]
    dsimp only at hN'N ⊢
    omega
  | stuck r h =>
    obtain ⟨k, ⟨⟨P, ⟨R, reps⟩⟩, ⟨G', ⟨w', L'⟩⟩⟩⟩ := r
    change k = 6 at h
    subst h
    obtain ⟨hF6, hW6⟩ := h6'.resolve_left (by simp)
    obtain ⟨ans, g, hr, hok, hg, hsum, hpred⟩ := rd_sem6 (n₀ := n₀) hO hPre hI hsub hB hs hLg
      hF6 hτ hS hHs (hnc rfl)
    refine ⟨ans, g, (rd_handle_run hrun (rd_tail6 rfl hr)).mono ?_, hok, hg,
      List.length_pos_of_ne_nil hne, hsum, hpred⟩
    simp only [rdOrbitWork]
    omega

end HandleSpec

/-! ### Reduce-and-derive -/

section Spec

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}
  {sub : HInstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)}
  {C : ℕ → Option ℕ → ℕ} {s : ℕ} {xy : StrData × StrData} {w : WinData} {σd : PermData}
  {N : ℕ} {gsG : GensData} {dG : D.denote} {n₀ n : ℕ} {L : LabelData} {st : ℕ × CJData}
  {sIn Lg F Blift Bgen Bo Bk Bcr Bd W6 : ℕ} {gsK : GensData} {dK : D.denote}

/-- **One branch**: the coset `σr • K` of the window, by the dynamic chain with the handle of
reduce-and-derive. -/
theorem rd_branch (hO : MeetsContractOn DV rdOps X.O)
    (hPre : ∀ op x, rdOps op → GroupPre DV op x → X.Pre op x)
    (hI : HInstValid DV (((xy, w, σd, N, gsG, dG), n₀, n, some L) : HInstData D))
    (hsub : HSubSolves X body DV sub
      (fun J => SizeChild sIn (((xy, w, σd, N, gsG, dG), n₀, n, some L) : HInstData D) J ∧
        StepChild w.1.length (N - n) (J.winSize, J.baseOpt)) C s)
    (hB : RDBounds X DV n N sIn Lg Blift Bgen Bo Bk Bcr) (hs : s ≤ sIn)
    (hLg : F * (sIn + 1) ≤ Lg) (hF1 : 1 ≤ F) (hFm : N - n ≤ F)
    (hKv : GroupValid DV N gsK dK) (hKG : GensData.denote N gsK ≤ GensData.denote N gsG)
    (hKs : gsK.length ≤ sIn)
    (hD : ∀ gs d O, RDSet DV n N gsG w L gsK sIn gs d O →
      RDOrbit X body DV n N w L st sIn Bd gs d O)
    (h5 : (N - n).factorial ≤ F ∨ ∀ gs d O, RDSet DV n N gsG w L gsK sIn gs d O →
      (deriveModel X.O n N (N, gs, d) O L st).1 = 5 →
        (deriveModel X.O n N (N, gs, d) O L st).2.1.2.2.length ≤ F)
    (h6 : (∀ gs d O, RDSet DV n N gsG w L gsK sIn gs d O →
        (deriveModel X.O n N (N, gs, d) O L st).1 ≠ 6) ∨
      ((N - n).factorial ≤ F ∧ rd6Cost N n w.1.length s sIn Bk Bo Bcr Bgen ≤ W6))
    {σr : PermData} (hσ : σr.Valid N) :
    ∃ (ans : AnswerData D) (ch : List (ℕ × Option ℕ)),
      RunsWithin X body (Main.rdBranch sub n₀ n L st (xy, (w, (σr, (N, gsK, dK))))) ans
        ((ch.map fun x => C x.1 x.2).sum +
          (w.1.length * rdOrbitWork N n w.1.length s sIn F Bd Blift Bgen Bo W6 +
            dynSeqCost N w.1.length Bo + 5)) ∧
      AnsOK DV N (ptsSet N w.1) (PermData.denote N σr) (GensData.denote N gsK)
        (xy.1.denote N) (xy.2.denote N) ans ∧
      (∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sIn) ∧
      (ch.map Prod.fst).sum ≤ F * w.1.length ∧ (∀ x ∈ ch, StepChild w.1.length (N - n) x) ∧
        ∀ x ∈ ch, 1 ≤ x.1 := by
  have hOo : MeetsContractOn DV (· = .orbits) X.O := fun op x h => hO op x (Or.inl h)
  have hPo : ∀ x, GroupPre DV .orbits x → X.Pre .orbits x :=
    fun x h => hPre _ x (Or.inl rfl) h
  have hwv : w.Valid N := hI.valid.win
  have hinv : IsInvariant (GensData.denote N gsK) (ptsSet N w.1) :=
    fun g hg u hu => hI.valid.invariant g (hKG hg) u hu
  set Wh := rdOrbitWork N n w.1.length s sIn F Bd Blift Bgen Bo W6 with hWh
  obtain ⟨ans, steps, hr, hok, hg, hsum, hQ⟩ := RunsWithin.dynSeqProg (X := X) (body := body)
    (handle := fun xy c O => Main.rdHandle sub n₀ n L st xy c O) (xy := xy) hOo hPo hσ hKv hKs
    hwv.nodup hwv.lt hinv
    (rd_handle (sub := sub) (C := C) (n₀ := n₀) (σd := σd) (dG := dG) (Bk := Bk) (Bcr := Bcr)
      (Bd := Bd) (W6 := W6) hO hPre hI hsub hB hs hLg hF1 hFm hKG hD h5 h6)
    (fun Hd w₀ h1 h2 _ hpre => hB.orbits Hd w₀ (by rw [h1]) h2 hpre)
  rw [← hWh] at hr
  set ch := (steps.map Prod.snd).flatten with hch
  have hlen : steps.length ≤ w.1.length := ml_steps_le hsum fun s hs => (hQ s hs).1
  have hC : (steps.map fun s => (s.2.map fun x => C x.1 x.2).sum + Wh).sum =
      (ch.map fun x => C x.1 x.2).sum + steps.length * Wh := by
    rw [ml_sum_add (fun s : List ℕ × List (ℕ × Option ℕ) => (s.2.map fun x => C x.1 x.2).sum),
      hch, List.map_flatten, List.sum_flatten, List.map_map, List.map_map]
    rfl
  refine ⟨ans, ch, ?_, hok, hg, ?_, ?_, ?_⟩
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      exact hr
    case hc =>
      have := Nat.mul_le_mul_right Wh hlen
      simp only [Prim.cost]
      omega
  · have e : (ch.map Prod.fst).sum = (steps.map fun s => (s.2.map Prod.fst).sum).sum := by
      rw [hch, List.map_flatten, List.sum_flatten, List.map_map, List.map_map]
      rfl
    have h1 : (steps.map fun s => (s.2.map Prod.fst).sum).sum ≤
        (steps.map fun s => F * s.1.length).sum :=
      List.sum_le_sum fun s hs => (hQ s hs).2.1
    have h2 : (steps.map fun s => F * s.1.length).sum =
        F * (steps.map fun s => s.1.length).sum := by
      rw [List.sum_map_mul_left]
    have h3 : F * (steps.map fun s => s.1.length).sum ≤ F * w.1.length :=
      Nat.mul_le_mul_left _ hsum
    omega
  · intro x hx
    obtain ⟨l, hl, hxl⟩ := List.mem_flatten.1 hx
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hl
    exact (hQ s hs).2.2.1 x hxl
  · intro x hx
    obtain ⟨l, hl, hxl⟩ := List.mem_flatten.1 hx
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hl
    exact (hQ s hs).2.2.2 x hxl

/-- **Reduce-and-derive.** Let `(σ • G, W, L)` be a valid hinted instance (so `G` is
transitive on `W` with the hint `L`), `rs` a left cover of `G` by cosets of `K ≤ G`, and `st` a
structure for the derived hints of the orbits of the subgroups of `K` (`hD`: their run, outcome
and sizes). The result is a correct answer for `σ • G` on `W`, at the cost of the children plus
`rdCost`, with at most `sIn` generators. The children are `StepChild` children of the parent
(a hint with base at most `3m/4`, or no hint on at most `|W|/2` points) whose windows sum to at
most `|rs| · F · |W|`. Here `F ≥ m` bounds the branching of the block-stabilizer loops (tag
`3`), of the Johnson fallbacks (tag `5`, `h5`) and of the kernel reductions (tag `6`, `h6`);
when no orbit is stuck (`h6`, left), the kernel reductions and their work `W6` disappear. -/
theorem RunsWithin.rdProg (hO : MeetsContractOn DV rdOps X.O)
    (hPre : ∀ op x, rdOps op → GroupPre DV op x → X.Pre op x)
    (hI : HInstValid DV (((xy, w, σd, N, gsG, dG), n₀, n, some L) : HInstData D))
    (hsub : HSubSolves X body DV sub
      (fun J => SizeChild sIn (((xy, w, σd, N, gsG, dG), n₀, n, some L) : HInstData D) J ∧
        StepChild w.1.length (N - n) (J.winSize, J.baseOpt)) C s)
    (hB : RDBounds X DV n N sIn Lg Blift Bgen Bo Bk Bcr) (hs : s ≤ sIn)
    (hLg : F * (sIn + 1) ≤ Lg) (hF1 : 1 ≤ F) (hFm : N - n ≤ F)
    (hKv : GroupValid DV N gsK dK) (hKG : GensData.denote N gsK ≤ GensData.denote N gsG)
    (hKs : gsK.length ≤ sIn) {rs : List PermData} (hrs : ∀ r ∈ rs, PermData.Valid N r)
    (hcov : IsLeftCover (GensData.denote N gsG) (GensData.denote N gsK)
      (fun i : Fin rs.length => PermData.denote N (rs.get i)))
    (hLr : rs.length * (sIn + 1) ≤ Lg)
    (hD : ∀ gs d O, RDSet DV n N gsG w L gsK sIn gs d O →
      RDOrbit X body DV n N w L st sIn Bd gs d O)
    (h5 : (N - n).factorial ≤ F ∨ ∀ gs d O, RDSet DV n N gsG w L gsK sIn gs d O →
      (deriveModel X.O n N (N, gs, d) O L st).1 = 5 →
        (deriveModel X.O n N (N, gs, d) O L st).2.1.2.2.length ≤ F)
    (h6 : (∀ gs d O, RDSet DV n N gsG w L gsK sIn gs d O →
        (deriveModel X.O n N (N, gs, d) O L st).1 ≠ 6) ∨
      ((N - n).factorial ≤ F ∧ rd6Cost N n w.1.length s sIn Bk Bo Bcr Bgen ≤ W6)) :
    ∃ (ans : AnswerData D) (ch : List (ℕ × Option ℕ)),
      RunsWithin X body
        (Main.rdProg sub (((xy, w, σd, N, gsG, dG), n₀, n, some L) : HInstData D) rs
          (N, gsK, dK) st) ans
        ((ch.map fun x => C x.1 x.2).sum +
          rdCost N w.1.length rs.length sIn
            (rdOrbitWork N n w.1.length s sIn F Bd Blift Bgen Bo W6) Bo Bgen) ∧
      InstData.OK (D := D) (xy, w, σd, N, gsG, dG) DV ans ∧
      (∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sIn) ∧
      ChildList w.1.length (rs.length * F) (StepChild w.1.length (N - n)) ch := by
  have hOg : MeetsContractOn DV (· = .generate) X.O := fun op x h => hO op x (by simp [rdOps, h])
  have hPg : ∀ x, GroupPre DV .generate x → X.Pre .generate x := fun x hx =>
    hPre _ x (by simp [rdOps]) hx
  have hwv : w.Valid N := hI.valid.win
  have hσ : σd.Valid N := hI.valid.rep
  set Wb := w.1.length * rdOrbitWork N n w.1.length s sIn F Bd Blift Bgen Bo W6 +
    dynSeqCost N w.1.length Bo + 5 with hWb
  -- the branches, and the most expensive one
  set Pb : PermData → List (ℕ × Option ℕ) → Prop := fun r ch =>
    (∃ ans : AnswerData D,
      RunsWithin X body (Main.rdBranch sub n₀ n L st (xy, (w, (σd.mul r, (N, gsK, dK))))) ans
        ((ch.map fun x => C x.1 x.2).sum + Wb) ∧
      AnsOK DV N (ptsSet N w.1) (PermData.denote N (σd.mul r)) (GensData.denote N gsK)
        (xy.1.denote N) (xy.2.denote N) ans ∧
      ∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sIn) ∧
    (ch.map Prod.fst).sum ≤ F * w.1.length ∧ (∀ x ∈ ch, StepChild w.1.length (N - n) x) ∧
      ∀ x ∈ ch, 1 ≤ x.1 with hPb
  have hbr : ∀ r ∈ rs, ∃ ch, Pb r ch := by
    intro r hr
    obtain ⟨ans, ch, hrun, hok, hg, hsum, hch⟩ := rd_branch (σd := σd) (dG := dG) hO hPre hI hsub
      hB hs hLg hF1 hFm hKv hKG hKs hD h5 h6 (hσ.mul (hrs r hr))
    exact ⟨ch, ⟨ans, hrun, hok, hg⟩, hsum, hch⟩
  obtain ⟨ch₀, hch₀, hmax⟩ := ml_exists_max (fun ch : List (ℕ × Option ℕ) =>
    (ch.map fun x => C x.1 x.2).sum) [] Pb rs hbr
  have hgood : (ch₀.map Prod.fst).sum ≤ F * w.1.length ∧
      (∀ x ∈ ch₀, StepChild w.1.length (N - n) x) ∧ ∀ x ∈ ch₀, 1 ≤ x.1 := by
    rcases hch₀ with rfl | ⟨r, -, h⟩
    · simp
    · exact h.2
  set Cb := (ch₀.map fun x => C x.1 x.2).sum + Wb with hCb
  have hsubB : SubSolves X body DV
      (Main.rdBranch (var := Ty.denote) (rec := (a, b)) (D := D) sub n₀ n L st)
      (fun I => I.1 = xy ∧ I.2.1 = w ∧ I.2.2.2 = (N, gsK, dK) ∧
        (∃ r ∈ rs, I.2.2.1 = σd.mul r) ∧ I.Valid DV) (fun _ => Cb) sIn := by
    rintro ⟨xy', w', σ', G'⟩ ⟨h1, h2, h3, ⟨r, hr, h4⟩, -⟩
    change xy' = xy at h1
    change w' = w at h2
    change G' = (N, gsK, dK) at h3
    change σ' = σd.mul r at h4
    subst h1 h2 h3 h4
    obtain ⟨ch, ⟨⟨ans, hrun, hok, hg⟩, -⟩, hle⟩ := hmax r hr
    refine ⟨ans, hrun.mono ?_, hok, hg⟩
    change _ ≤ Cb
    rw [hCb]
    omega
  obtain ⟨ans, hrun, hok, hg⟩ := RunsWithin.branchProg (X := X) (body := body) hOg hPg hwv hσ hKv
    hKG hI.valid.invariant hrs (ml_isLeftCover_map hcov) hsubB
    (fun gs hv hl _ => hB.gen N le_rfl gs hv (hl.trans hLr))
  refine ⟨ans, (List.replicate rs.length ch₀).flatten, ?_, hok,
    hg sIn (fun hs' hv _ => hB.genOut N le_rfl hs' hv), ?_, ?_, ?_⟩
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_with RunsWithin.caseOption_some _
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      exact hrun
    case hc =>
      rw [ml_sum_replicate]
      have e : rs.length * (24 * N + Cb + sIn + 45) =
          rs.length * (ch₀.map fun x => C x.1 x.2).sum + rs.length * (24 * N + Wb + sIn + 45) := by
        rw [hCb]
        ring
      simp only [Prim.cost, rdCost]
      have e' : Wb = w.1.length * rdOrbitWork N n w.1.length s sIn F Bd Blift Bgen Bo W6 +
          dynSeqCost N w.1.length Bo + 5 := hWb
      have : rs.length * (24 * N + Wb + sIn + 45) ≤ rs.length * (24 * N +
          (w.1.length * rdOrbitWork N n w.1.length s sIn F Bd Blift Bgen Bo W6 +
            dynSeqCost N w.1.length Bo + 10) + sIn + 45) :=
        Nat.mul_le_mul_left _ (by omega)
      omega
  · rw [ml_sum_replicate]
    have := Nat.mul_le_mul_left rs.length hgood.1
    rw [Nat.mul_assoc]
    exact this
  · intro x hx
    obtain ⟨l, hl, hxl⟩ := List.mem_flatten.1 hx
    rw [List.eq_of_mem_replicate hl] at hxl
    exact hgood.2.1 x hxl
  · intro x hx
    obtain ⟨l, hl, hxl⟩ := List.mem_flatten.1 hx
    rw [List.eq_of_mem_replicate hl] at hxl
    exact hgood.2.2 x hxl

/-- **Reduce-and-derive, general factor**: with `F = m!`, no further hypothesis on the tags. -/
theorem RunsWithin.rdProg_general (hO : MeetsContractOn DV rdOps X.O)
    (hPre : ∀ op x, rdOps op → GroupPre DV op x → X.Pre op x)
    (hI : HInstValid DV (((xy, w, σd, N, gsG, dG), n₀, n, some L) : HInstData D))
    (hsub : HSubSolves X body DV sub
      (fun J => SizeChild sIn (((xy, w, σd, N, gsG, dG), n₀, n, some L) : HInstData D) J ∧
        StepChild w.1.length (N - n) (J.winSize, J.baseOpt)) C s)
    (hB : RDBounds X DV n N sIn Lg Blift Bgen Bo Bk Bcr) (hs : s ≤ sIn)
    (hLg : (N - n).factorial * (sIn + 1) ≤ Lg)
    (hKv : GroupValid DV N gsK dK) (hKG : GensData.denote N gsK ≤ GensData.denote N gsG)
    (hKs : gsK.length ≤ sIn) {rs : List PermData} (hrs : ∀ r ∈ rs, PermData.Valid N r)
    (hcov : IsLeftCover (GensData.denote N gsG) (GensData.denote N gsK)
      (fun i : Fin rs.length => PermData.denote N (rs.get i)))
    (hLr : rs.length * (sIn + 1) ≤ Lg)
    (hD : ∀ gs d O, RDSet DV n N gsG w L gsK sIn gs d O →
      RDOrbit X body DV n N w L st sIn Bd gs d O) :
    ∃ (ans : AnswerData D) (ch : List (ℕ × Option ℕ)),
      RunsWithin X body
        (Main.rdProg sub (((xy, w, σd, N, gsG, dG), n₀, n, some L) : HInstData D) rs
          (N, gsK, dK) st) ans
        ((ch.map fun x => C x.1 x.2).sum +
          rdCost N w.1.length rs.length sIn
            (rdOrbitWork N n w.1.length s sIn (N - n).factorial Bd Blift Bgen Bo
              (rd6Cost N n w.1.length s sIn Bk Bo Bcr Bgen)) Bo Bgen) ∧
      InstData.OK (D := D) (xy, w, σd, N, gsG, dG) DV ans ∧
      (∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sIn) ∧
      ChildList w.1.length (rs.length * (N - n).factorial) (StepChild w.1.length (N - n)) ch :=
  RunsWithin.rdProg hO hPre hI hsub hB hs hLg (Nat.factorial_pos _) (Nat.self_le_factorial _) hKv
    hKG hKs hrs hcov hLr hD (Or.inl le_rfl) (Or.inr ⟨le_rfl, le_rfl⟩)

/-- **Reduce-and-derive without stuck orbits** (`hns`, from `rd_ns_part` or `rd_ns_cj`): the
kernel reductions disappear, and the factor `F` bounds only the block-stabilizer loops (`m ≤ F`)
and the Johnson fallbacks (`h5`). -/
theorem RunsWithin.rdProg_ns (hO : MeetsContractOn DV rdOps X.O)
    (hPre : ∀ op x, rdOps op → GroupPre DV op x → X.Pre op x)
    (hI : HInstValid DV (((xy, w, σd, N, gsG, dG), n₀, n, some L) : HInstData D))
    (hsub : HSubSolves X body DV sub
      (fun J => SizeChild sIn (((xy, w, σd, N, gsG, dG), n₀, n, some L) : HInstData D) J ∧
        StepChild w.1.length (N - n) (J.winSize, J.baseOpt)) C s)
    (hB : RDBounds X DV n N sIn Lg Blift Bgen Bo Bk Bcr) (hs : s ≤ sIn)
    (hLg : F * (sIn + 1) ≤ Lg) (hF1 : 1 ≤ F) (hFm : N - n ≤ F)
    (hKv : GroupValid DV N gsK dK) (hKG : GensData.denote N gsK ≤ GensData.denote N gsG)
    (hKs : gsK.length ≤ sIn) {rs : List PermData} (hrs : ∀ r ∈ rs, PermData.Valid N r)
    (hcov : IsLeftCover (GensData.denote N gsG) (GensData.denote N gsK)
      (fun i : Fin rs.length => PermData.denote N (rs.get i)))
    (hLr : rs.length * (sIn + 1) ≤ Lg)
    (hD : ∀ gs d O, RDSet DV n N gsG w L gsK sIn gs d O →
      RDOrbit X body DV n N w L st sIn Bd gs d O)
    (h5 : (N - n).factorial ≤ F ∨ ∀ gs d O, RDSet DV n N gsG w L gsK sIn gs d O →
      (deriveModel X.O n N (N, gs, d) O L st).1 = 5 →
        (deriveModel X.O n N (N, gs, d) O L st).2.1.2.2.length ≤ F)
    (hns : ∀ gs d O, RDSet DV n N gsG w L gsK sIn gs d O →
      (deriveModel X.O n N (N, gs, d) O L st).1 ≠ 6) :
    ∃ (ans : AnswerData D) (ch : List (ℕ × Option ℕ)),
      RunsWithin X body
        (Main.rdProg sub (((xy, w, σd, N, gsG, dG), n₀, n, some L) : HInstData D) rs
          (N, gsK, dK) st) ans
        ((ch.map fun x => C x.1 x.2).sum +
          rdCost N w.1.length rs.length sIn
            (rdOrbitWork N n w.1.length s sIn F Bd Blift Bgen Bo 0) Bo Bgen) ∧
      InstData.OK (D := D) (xy, w, σd, N, gsG, dG) DV ans ∧
      (∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sIn) ∧
      ChildList w.1.length (rs.length * F) (StepChild w.1.length (N - n)) ch :=
  RunsWithin.rdProg (Bk := Bk) (Bcr := Bcr) hO hPre hI hsub hB hs hLg hF1 hFm hKv hKG hKs hrs
    hcov hLr hD h5 (Or.inl hns)

end Spec

/-! ### No stuck orbits, and the derived hints of the orbits -/

section Progress

variable {D : Ty} {DV : ℕ → GensData → D.denote → Prop} {X : Ctx (groupSig D)}
  {n N : ℕ} {gsG gsK : GensData} {w : WinData} {L : LabelData} {sIn : ℕ} {st : ℕ × CJData}

/-- **No stuck orbit for a colored partition**: if `K` preserves a colored `t`-partition with
`4t ≤ 3m` and `m ≥ 2` (and `st` is not a coloured Johnson structure), no orbit of a subgroup of
`K` is stuck (`derivePart_ne_stuck`). -/
theorem rd_ns_part (hO : MeetsContractOn DV deriveOps X.O) (hst : st.1 ≠ 2)
    (hKb : IsInvariant (GensData.denote N gsK) (baseSet n N)) {p : CPart (Fin (N - n))} {t : ℕ}
    (hp : IsColPart Finset.univ t p)
    (hpK : ∀ g : ↥(GensData.denote N gsK), baseHom (GensData.denote N gsK) n hKb g • p = p)
    (ht : 4 * t ≤ 3 * (N - n)) (hm : 2 ≤ N - n) :
    ∀ gs d O, RDSet DV n N gsG w L gsK sIn gs d O →
      (deriveModel X.O n N (N, gs, d) O L st).1 ≠ 6 := by
  rintro gs d O ⟨hS, -, hle⟩
  have he : (st.1 == 2) = false := by simpa using hst
  have hm' : deriveModel X.O n N (N, gs, d) O L st = deriveFreeModel X.O n N (N, gs, d) O L := by
    simp only [deriveModel, he, Bool.cond_false]
  rw [hm']
  refine derivePart_ne_stuck hO hS hp (fun g => ?_) ht hm
  obtain ⟨π, hπ⟩ := g
  rw [dv_baseHom_le hle hKb hS.base_inv hπ]
  exact hpK ⟨π, hle hπ⟩

/-- **No stuck orbit for a coloured Johnson structure**: if `K` preserves the coloured Johnson
structure `st.2` (a Johnson embedding, colour classes outside `V₀` of at most `m/2` points,
`m ≥ 5`), no orbit of a subgroup of `K` is stuck (`deriveCJ_ne_stuck`). -/
theorem rd_ns_cj (hO : MeetsContractOn DV deriveOps X.O) (hst : st.1 = 2)
    (hKb : IsInvariant (GensData.denote N gsK) (baseSet n N)) (hJv : Align.JValid (N - n) st.2.1)
    {t : ℕ} (hJ : IsJohnson Finset.univ t (Align.jdec (N - n) st.2.1))
    (hK : ∀ g : ↥(GensData.denote N gsK),
      baseHom (GensData.denote N gsK) n hKb g • cjdec (N - n) st.2 = cjdec (N - n) st.2)
    (hq : ∀ c, 2 * (Finset.univ.filter fun γ =>
      γ ∉ (Align.jdec (N - n) st.2.1).V0 ∧ cjcol (N - n) st.2 γ = c).card ≤ N - n)
    (hm : 5 ≤ N - n) :
    ∀ gs d O, RDSet DV n N gsG w L gsK sIn gs d O →
      (deriveModel X.O n N (N, gs, d) O L st).1 ≠ 6 := by
  rintro gs d O ⟨hS, -, hle⟩
  have he : (st.1 == 2) = true := by simpa using hst
  have hm' : deriveModel X.O n N (N, gs, d) O L st =
      deriveCJModel X.O n N (N, gs, d) O L st.2 := by
    simp only [deriveModel, he, Bool.cond_true]
  rw [hm']
  refine deriveCJ_ne_stuck hO hS hJv hJ (fun g => ?_) hq hm
  obtain ⟨π, hπ⟩ := g
  rw [dv_baseHom_le hle hKb hS.base_inv hπ]
  exact hK ⟨π, hle hπ⟩

variable {a b : Ty} {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b}

/-- **The derived hints without a coloured Johnson structure** (`RunsWithin.deriveProg_free`),
from the charges on the orbits that can occur. -/
theorem rd_orbit_free (hO : MeetsContractOn DV deriveOps X.O)
    (hPre : ∀ op x, deriveOps op → GroupPre DV op x → X.Pre op x) (hst : st.1 ≠ 2)
    {Borb Bgen s₁ Bgen₂ Bge Bst Btr Bgt sS Lt sH Bgen₃ Bd : ℕ}
    (hch : ∀ gs d O, RDSet DV n N gsG w L gsK sIn gs d O →
      M1Charges X n N gs d (WinData.ofPoints N O) L Borb Bgen ∧
      BlkCharges X n (m1Model X.O n N (N, gs, d) (WinData.ofPoints N O) L).1.1
        (m1Model X.O n N (N, gs, d) (WinData.ofPoints N O) L).1.2.1
        s₁ Bgen₂ Bge Bst Btr Bgt sS Lt sH Bgen₃ ∧
      deriveFreeCost n N O.length gs.length Borb Bgen s₁ sS Lt sH Bgen₂ Bge Bst Btr Bgt Bgen₃ +
        5 ≤ Bd ∧
      DOutGens sIn (deriveModel X.O n N (N, gs, d) O L st)) :
    ∀ gs d O, RDSet DV n N gsG w L gsK sIn gs d O →
      RDOrbit X body DV n N w L st sIn Bd gs d O := by
  rintro gs d O hset
  obtain ⟨hB, hB', hc, hsz⟩ := hch gs d O hset
  obtain ⟨hrun, hout⟩ := RunsWithin.deriveProg_free (body := body) hO hPre hset.1 hst hB hB'
  exact ⟨hrun.mono hc, hout, fun h => rd_deg_free hO hset.1 hst h, hsz⟩

/-- **The derived hints with a coloured Johnson structure** (`RunsWithin.deriveProg_cj`): the
structure hypotheses are stated once for `K` and hold for every subgroup; the charges on the
orbits that can occur. -/
theorem rd_orbit_cj (hO : MeetsContractOn DV deriveOps X.O)
    (hPre : ∀ op x, deriveOps op → GroupPre DV op x → X.Pre op x) (hst : st.1 = 2)
    (hKb : IsInvariant (GensData.denote N gsK) (baseSet n N)) (hJv : Align.JValid (N - n) st.2.1)
    {V : Finset (Fin (N - n))} {t : ℕ} (hJ : IsJohnson V t (Align.jdec (N - n) st.2.1))
    (hK : ∀ g : ↥(GensData.denote N gsK),
      baseHom (GensData.denote N gsK) n hKb g • cjdec (N - n) st.2 = cjdec (N - n) st.2)
    {Borb Bgen s₁ Bgen₂ Bge Bst Btr Bgt sS Lt sH Bgen₃ Bgen₄ uB Bd : ℕ}
    (hch : ∀ gs d O, RDSet DV n N gsG w L gsK sIn gs d O →
      M1Charges X n N gs d (WinData.ofPoints N O) (labDiffD (markArr (N - n) st.2.1.1) L O)
        Borb Bgen ∧
      BlkCharges X n (m1Model X.O n N (N, gs, d) (WinData.ofPoints N O)
          (labDiffD (markArr (N - n) st.2.1.1) L O)).1.1
        (m1Model X.O n N (N, gs, d) (WinData.ofPoints N O)
          (labDiffD (markArr (N - n) st.2.1.1) L O)).1.2.1
        s₁ Bgen₂ Bge Bst Btr Bgt sS Lt sH Bgen₃ ∧
      X.B.call GroupOp.generate (n + (cellPosD n st.2.1.2.1).length,
          rebaseGens n N (cellPosD n st.2.1.2.1) gs)
        (rebaseModel X.O n N (cellPosD n st.2.1.2.1) gs) ≤ Bgen₄ ∧
      ((labJUD st.2.1.2.1.length (markArr (N - n) st.2.1.1) st.2.1.2.2.2 L O).getD
        (O.headD 0) []).length ≤ uB ∧
      (∃ (s' : ℕ) (G₀ : Subgroup (Perm (Fin (n + (cellPosD n st.2.1.2.1).length))))
        (B : BackendBounds X DV (n + (cellPosD n st.2.1.2.1).length) s' G₀),
        (rebaseModel X.O n N (cellPosD n st.2.1.2.1) gs).2.1.length ≤ s' ∧
        GensData.denote (n + (cellPosD n st.2.1.2.1).length)
          (rebaseModel X.O n N (cellPosD n st.2.1.2.1) gs).2.1 ≤ G₀ ∧
        deriveCJCost n N O.length L.size gs.length Borb Bgen s₁ sS Lt sH Bgen₂ Bge Bst Btr Bgt
          Bgen₃ Bgen₄ uB B.Btr B.Bstab + 5 ≤ Bd) ∧
      DOutGens sIn (deriveModel X.O n N (N, gs, d) O L st)) :
    ∀ gs d O, RDSet DV n N gsG w L gsK sIn gs d O →
      RDOrbit X body DV n N w L st sIn Bd gs d O := by
  rintro gs d O hset
  obtain ⟨hB, hB', hB4, hu, ⟨s', G₀, B, hs', hG₀, hc⟩, hsz⟩ := hch gs d O hset
  obtain ⟨hS, -, hle⟩ := hset
  have hKH : ∀ g : ↥(GensData.denote N gs),
      baseHom (GensData.denote N gs) n hS.base_inv g • cjdec (N - n) st.2 =
        cjdec (N - n) st.2 := by
    rintro ⟨π, hπ⟩
    rw [dv_baseHom_le hle hKb hS.base_inv hπ]
    exact hK ⟨π, hle hπ⟩
  obtain ⟨hrun, hout⟩ := RunsWithin.deriveProg_cj (body := body) hO hPre hS hst hJv hJ hKH hB hB'
    hB4 hu B hs' hG₀
  exact ⟨hrun.mono hc, hout,
    fun h => rd_deg_cj hO hS hst hJv (fun g => ((cj_smul_eq_iff' _ _ _).1 (hKH g)).1) h, hsz⟩

end Progress

/-! ### Reduce-and-derive with a structure -/

section Structured

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}
  {sub : HInstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)}
  {C : ℕ → Option ℕ → ℕ} {s : ℕ} {xy : StrData × StrData} {w : WinData} {σd : PermData}
  {N : ℕ} {gsG : GensData} {dG : D.denote} {n₀ n : ℕ} {L : LabelData} {st : ℕ × CJData}
  {sIn Lg Blift Bgen Bo Bk Bcr Bd : ℕ} {gsK : GensData} {dK : D.denote}

/-- **Reduce-and-derive with a preserved colored partition**: no orbit is stuck
(`rd_ns_part`), no Johnson fallback occurs, and the factor is `m = N − n`. -/
theorem RunsWithin.rdProg_part_ns (hO : MeetsContractOn DV rdOps X.O)
    (hPre : ∀ op x, rdOps op → GroupPre DV op x → X.Pre op x)
    (hI : HInstValid DV (((xy, w, σd, N, gsG, dG), n₀, n, some L) : HInstData D))
    (hsub : HSubSolves X body DV sub
      (fun J => SizeChild sIn (((xy, w, σd, N, gsG, dG), n₀, n, some L) : HInstData D) J ∧
        StepChild w.1.length (N - n) (J.winSize, J.baseOpt)) C s)
    (hB : RDBounds X DV n N sIn Lg Blift Bgen Bo Bk Bcr) (hs : s ≤ sIn)
    (hLg : (N - n) * (sIn + 1) ≤ Lg)
    (hKv : GroupValid DV N gsK dK) (hKG : GensData.denote N gsK ≤ GensData.denote N gsG)
    (hKs : gsK.length ≤ sIn) {rs : List PermData} (hrs : ∀ r ∈ rs, PermData.Valid N r)
    (hcov : IsLeftCover (GensData.denote N gsG) (GensData.denote N gsK)
      (fun i : Fin rs.length => PermData.denote N (rs.get i)))
    (hLr : rs.length * (sIn + 1) ≤ Lg)
    (hD : ∀ gs d O, RDSet DV n N gsG w L gsK sIn gs d O →
      RDOrbit X body DV n N w L st sIn Bd gs d O)
    (hst : st.1 ≠ 2) (hKb : IsInvariant (GensData.denote N gsK) (baseSet n N))
    {p : CPart (Fin (N - n))} {t : ℕ} (hp : IsColPart Finset.univ t p)
    (hpK : ∀ g : ↥(GensData.denote N gsK), baseHom (GensData.denote N gsK) n hKb g • p = p)
    (ht : 4 * t ≤ 3 * (N - n)) (hm : 2 ≤ N - n) :
    ∃ (ans : AnswerData D) (ch : List (ℕ × Option ℕ)),
      RunsWithin X body
        (Main.rdProg sub (((xy, w, σd, N, gsG, dG), n₀, n, some L) : HInstData D) rs
          (N, gsK, dK) st) ans
        ((ch.map fun x => C x.1 x.2).sum +
          rdCost N w.1.length rs.length sIn
            (rdOrbitWork N n w.1.length s sIn (N - n) Bd Blift Bgen Bo 0) Bo Bgen) ∧
      InstData.OK (D := D) (xy, w, σd, N, gsG, dG) DV ans ∧
      (∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sIn) ∧
      ChildList w.1.length (rs.length * (N - n)) (StepChild w.1.length (N - n)) ch := by
  have hO' : MeetsContractOn DV deriveOps X.O := fun op x h hx => hO op x (by
    rcases h with h | h | h | h <;> simp [rdOps, h]) hx
  exact RunsWithin.rdProg_ns (Bk := Bk) (Bcr := Bcr) hO hPre hI hsub hB hs hLg (by omega) le_rfl
    hKv hKG hKs hrs hcov hLr hD (Or.inr fun gs d O _ h5 => absurd h5 (rd_free_ne5 hst))
    (rd_ns_part hO' hst hKb hp hpK ht hm)

/-- **Reduce-and-derive with a preserved coloured Johnson structure**: no orbit is stuck
(`rd_ns_cj`), and the factor is `max m uB!`, where `uB` bounds the number of union cells at
the first point of every orbit that can occur: the Johnson fallback has at most that many
factorial cosets (`rd_cj_reps5`). -/
theorem RunsWithin.rdProg_cj_ns (hO : MeetsContractOn DV rdOps X.O)
    (hPre : ∀ op x, rdOps op → GroupPre DV op x → X.Pre op x)
    (hI : HInstValid DV (((xy, w, σd, N, gsG, dG), n₀, n, some L) : HInstData D))
    (hsub : HSubSolves X body DV sub
      (fun J => SizeChild sIn (((xy, w, σd, N, gsG, dG), n₀, n, some L) : HInstData D) J ∧
        StepChild w.1.length (N - n) (J.winSize, J.baseOpt)) C s)
    (hB : RDBounds X DV n N sIn Lg Blift Bgen Bo Bk Bcr) (hs : s ≤ sIn) {uB : ℕ}
    (hLg : max (N - n) uB.factorial * (sIn + 1) ≤ Lg)
    (hKv : GroupValid DV N gsK dK) (hKG : GensData.denote N gsK ≤ GensData.denote N gsG)
    (hKs : gsK.length ≤ sIn) {rs : List PermData} (hrs : ∀ r ∈ rs, PermData.Valid N r)
    (hcov : IsLeftCover (GensData.denote N gsG) (GensData.denote N gsK)
      (fun i : Fin rs.length => PermData.denote N (rs.get i)))
    (hLr : rs.length * (sIn + 1) ≤ Lg)
    (hD : ∀ gs d O, RDSet DV n N gsG w L gsK sIn gs d O →
      RDOrbit X body DV n N w L st sIn Bd gs d O)
    (hst : st.1 = 2) (hKb : IsInvariant (GensData.denote N gsK) (baseSet n N))
    (hJv : Align.JValid (N - n) st.2.1) {t : ℕ}
    (hJ : IsJohnson Finset.univ t (Align.jdec (N - n) st.2.1))
    (hK : ∀ g : ↥(GensData.denote N gsK),
      baseHom (GensData.denote N gsK) n hKb g • cjdec (N - n) st.2 = cjdec (N - n) st.2)
    (hq : ∀ c, 2 * (Finset.univ.filter fun γ =>
      γ ∉ (Align.jdec (N - n) st.2.1).V0 ∧ cjcol (N - n) st.2 γ = c).card ≤ N - n)
    (hm : 5 ≤ N - n)
    (hu : ∀ gs d O, RDSet DV n N gsG w L gsK sIn gs d O →
      ((labJUD st.2.1.2.1.length (markArr (N - n) st.2.1.1) st.2.1.2.2.2 L O).getD
        (O.headD 0) []).length ≤ uB) :
    ∃ (ans : AnswerData D) (ch : List (ℕ × Option ℕ)),
      RunsWithin X body
        (Main.rdProg sub (((xy, w, σd, N, gsG, dG), n₀, n, some L) : HInstData D) rs
          (N, gsK, dK) st) ans
        ((ch.map fun x => C x.1 x.2).sum +
          rdCost N w.1.length rs.length sIn
            (rdOrbitWork N n w.1.length s sIn (max (N - n) uB.factorial) Bd Blift Bgen Bo 0)
            Bo Bgen) ∧
      InstData.OK (D := D) (xy, w, σd, N, gsG, dG) DV ans ∧
      (∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sIn) ∧
      ChildList w.1.length (rs.length * max (N - n) uB.factorial)
        (StepChild w.1.length (N - n)) ch := by
  have hO' : MeetsContractOn DV deriveOps X.O := fun op x h hx => hO op x (by
    rcases h with h | h | h | h <;> simp [rdOps, h]) hx
  refine RunsWithin.rdProg_ns (Bk := Bk) (Bcr := Bcr) hO hPre hI hsub hB hs hLg
    (le_max_of_le_right (Nat.factorial_pos _)) (le_max_left _ _) hKv hKG hKs hrs hcov hLr hD
    (Or.inr fun gs d O hset h5 => ?_) (rd_ns_cj hO' hst hKb hJv hJ hK hq hm)
  have huB := hu gs d O hset
  obtain ⟨hS, -, hle⟩ := hset
  have hKj : ∀ g : ↥(GensData.denote N gs),
      baseHom (GensData.denote N gs) n hS.base_inv g • Align.jdec (N - n) st.2.1 =
        Align.jdec (N - n) st.2.1 := by
    rintro ⟨π, hπ⟩
    rw [dv_baseHom_le hle hKb hS.base_inv hπ]
    exact ((cj_smul_eq_iff' _ _ _).1 (hK ⟨π, hle hπ⟩)).1
  exact (rd_cj_reps5 hO' hS hst hJv hKj h5).trans
    ((Nat.factorial_le huB).trans (le_max_right _ _))

end Structured

/-! ### The Schreier–Sims backend -/

section SimsBounds

open Sims

theorem rd_liftCost_mono₂ {n n' L L' m m' : ℕ} (hn : n ≤ n') (hL : L ≤ L') (hm : m ≤ m') :
    Sims.liftCost n L m ≤ Sims.liftCost n' L' m' := by
  unfold Sims.liftCost
  gcongr
  exact buildCost_mono₂ hn hL

theorem rd_orbitsCost_mono₂ {n n' L L' m m' : ℕ} (hn : n ≤ n') (hL : L ≤ L') (hm : m ≤ m') :
    orbitsCost n L m ≤ orbitsCost n' L' m' := by
  unfold orbitsCost transCost
  gcongr

/-- **The uniform bounds of reduce-and-derive hold for the Schreier–Sims backend**, with
`sIn = N²` (the generator counts of its `generate` and `kernel` outputs) and explicit charges:
`liftCost N N² n + 7`, `genCost N Lg + 2`, `orbitsCost N N² N + 5`, `kerCost N N² N + 5`, and
`repsCost N N² N² m! + 7` for the kernel's coset representatives (at most `m!` of them,
`m = N − n`, by `kerProg`). -/
theorem rd_ss_bounds (n N Lg : ℕ) :
    RDBounds ssCtx ssDV n N (N * N) Lg (Sims.liftCost N (N * N) n + 7) (genCost N Lg + 2)
      (orbitsCost N (N * N) N + 5) (kerCost N (N * N) N + 5)
      (repsCost N (N * N) (N * N) (N - n).factorial + 7) where
  lift M hM gs d _ hgs π' _ := by
    change Sims.liftCost M gs.length (List.range n).length + 7 ≤ _
    rw [List.length_range]
    exact Nat.add_le_add_right (rd_liftCost_mono₂ hM hgs le_rfl) 7
  gen M hM hs _ hl := by
    change genCost M hs.length + 2 ≤ _
    exact Nat.add_le_add_right (genCost_mono₂ hM hl) 2
  genOut M hM hs hv := by
    change (generateModel M hs).length ≤ N * N
    exact (generateModel_spec hv).2.2.trans (Nat.mul_le_mul hM hM)
  orbits Hd w hN hs hpre := by
    obtain ⟨M, gs, d⟩ := Hd
    obtain ⟨-, hw, -⟩ := hpre
    change orbitsCost M gs.length w.1.length + 5 ≤ _
    exact Nat.add_le_add_right
      (rd_orbitsCost_mono₂ hN hs ((WinData.length_le hw).trans hN)) 5
  kernel gs d _ hgs := by
    change kerCost N gs.length (baseWin n N).1.length + 5 ≤ _
    exact Nat.add_le_add_right
      (kerCost_mono₂ le_rfl hgs (WinData.length_le (baseWin_valid n N))) 5
  kerGens gs d hv _ := by
    change (kernelModel N gs (baseWin n N)).length ≤ N * N
    exact (kernelModel_spec hv.1 (baseWin_valid n N)).2.2
  kerOrbits gs d w hv _ hw := by
    change orbitsCost N (kernelModel N gs (baseWin n N)).length w.1.length + 5 ≤ _
    exact Nat.add_le_add_right (rd_orbitsCost_mono₂ le_rfl
      (kernelModel_spec hv.1 (baseWin_valid n N)).2.2 (WinData.length_le hw)) 5
  cosetReps gs d hv hgs hbase := by
    obtain ⟨-, -, -, -, -, -, -, hrlen⟩ := RunsWithin.kerProg (X := ssCtx) (DV := ssDV)
      (a := Ty.unit) (b := Ty.unit)
      (body := fun x => (Prog.ret x : Prog (groupSig Ty.unit) (Ty.unit, Ty.unit) Ty.denote Ty.unit))
      (n := n) (fun op x _ hx => ssOracle_meets op x hx) (fun _ _ _ h => h) hv hbase le_rfl le_rfl
    have hfact : (kerReps ssCtx.O n (N, gs, d)).length ≤ (N - n).factorial := by
      rw [hrlen]
      calc Nat.card (baseHom (GensData.denote N gs) n hbase).range
          ≤ Nat.card (Perm (Fin (N - n))) := Subgroup.card_le_card_group _
        _ = (N - n).factorial := by
            rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    change repsCost N gs.length (kernelModel N gs (baseWin n N)).length
      (kerReps ssCtx.O n (N, gs, d)).length + 7 ≤ _
    exact Nat.add_le_add_right (repsCost_mono₃ hgs
      (kernelModel_spec hv.1 (baseWin_valid n N)).2.2 hfact) 7

end SimsBounds

/-! ### Well-formedness -/

section Wf

variable {D : Ty} {rec : Ty × Ty} {var₁ var₂ : Ty → Type} {r : Bool} {Γ : WfCtx var₁ var₂}

/-- Membership in a context extended by bound variables. -/
local macro "rd_mem" : tactic =>
  `(tactic| repeat (first | exact List.mem_cons_self | assumption | apply List.mem_cons_of_mem))

theorem wf_rd3Inner {sub₁ : var₁ (hinstTy D) → Prog (groupSig D) rec var₁ (Ty.answer D)}
    {sub₂ : var₂ (hinstTy D) → Prog (groupSig D) rec var₂ (Ty.answer D)}
    (hsub : WfFun r Γ sub₁ sub₂) {R₁ G₁ : var₁ (Ty.group D)} {R₂ G₂ : var₂ (Ty.group D)}
    {reps₁ : var₁ Ty.gens} {reps₂ : var₂ Ty.gens} {O₁ : var₁ (.list .nat)}
    {O₂ : var₂ (.list .nat)} {L₁ : var₁ (.array (.list .nat))}
    {L₂ : var₂ (.array (.list .nat))} {n₀₁ n₁ : var₁ .nat} {n₀₂ n₂ : var₂ .nat}
    (hR : ⟨Ty.group D, R₁, R₂⟩ ∈ Γ) (hG : ⟨Ty.group D, G₁, G₂⟩ ∈ Γ)
    (hreps : ⟨Ty.gens, reps₁, reps₂⟩ ∈ Γ) (hO : ⟨.list .nat, O₁, O₂⟩ ∈ Γ)
    (hL : ⟨.array (.list .nat), L₁, L₂⟩ ∈ Γ) (hn₀ : ⟨.nat, n₀₁, n₀₂⟩ ∈ Γ)
    (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) :
    WfFun r Γ (rd3Inner sub₁ R₁ G₁ reps₁ O₁ L₁ n₀₁ n₁)
      (rd3Inner sub₂ R₂ G₂ reps₂ O₂ L₂ n₀₂ n₂) := by
  intro Γ' hΓ J₁ J₂ hJ
  unfold rd3Inner
  refine .bind (.prim _ (.cons hJ .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by rd_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  have hR' := hΓ hR
  have hG' := hΓ hG
  have hreps' := hΓ hreps
  have hO' := hΓ hO
  have hL' := hΓ hL
  have hn₀' := hΓ hn₀
  have hn' := hΓ hn
  refine wf_m2bLoopProg (fun Γ₃ h₃ => hsub Γ₃ fun y hy => h₃ ?_) (by rd_mem) (List.Mem.head _)
    (by rd_mem) (by rd_mem) (by rd_mem) (by rd_mem) (by rd_mem) (by rd_mem) (by rd_mem)
  have := hΓ hy
  rd_mem

theorem wf_rd5Inner {sub₁ : var₁ (hinstTy D) → Prog (groupSig D) rec var₁ (Ty.answer D)}
    {sub₂ : var₂ (hinstTy D) → Prog (groupSig D) rec var₂ (Ty.answer D)}
    (hsub : WfFun r Γ sub₁ sub₂) {R₁ : var₁ (Ty.group D)} {R₂ : var₂ (Ty.group D)}
    {reps₁ : var₁ Ty.gens} {reps₂ : var₂ Ty.gens} {n₀₁ n₁ : var₁ .nat} {n₀₂ n₂ : var₂ .nat}
    (hR : ⟨Ty.group D, R₁, R₂⟩ ∈ Γ) (hreps : ⟨Ty.gens, reps₁, reps₂⟩ ∈ Γ)
    (hn₀ : ⟨.nat, n₀₁, n₀₂⟩ ∈ Γ) (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) :
    WfFun r Γ (rd5Inner sub₁ R₁ reps₁ n₀₁ n₁) (rd5Inner sub₂ R₂ reps₂ n₀₂ n₂) := by
  intro Γ' hΓ J₁ J₂ hJ
  unfold rd5Inner
  refine .bind (.prim _ (.cons hJ .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by rd_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by rd_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  have hR' := hΓ hR
  have hreps' := hΓ hreps
  have hn₀' := hΓ hn₀
  have hn' := hΓ hn
  refine .bind (.prim _ (.cons (by rd_mem) (.cons (by rd_mem) .nil))) fun _ _ => ?_
  refine .bind (.call _ (List.Mem.head _)) fun _ _ => ?_
  refine wf_branchProg ?_ (by rd_mem) (by rd_mem) (by rd_mem) (by rd_mem) (by rd_mem)
  intro Γ₄ h₄ K₁ K₂ hK
  have e₀ : ⟨.nat, n₀₁, n₀₂⟩ ∈ Γ₄ := h₄ (by rd_mem)
  have e₁ : ⟨.nat, n₁, n₂⟩ ∈ Γ₄ := h₄ (by rd_mem)
  have e₂ : ∀ y, y ∈ Γ → y ∈ Γ₄ := fun y hy => h₄ (by have := hΓ hy; rd_mem)
  have e₃ : ⟨.list (.list .nat), _, _⟩ ∈ Γ₄ := h₄ (List.Mem.head _)
  unfold blockBranch
  refine .bind (.prim _ (.cons hK .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine wf_seqProg (wf_plainSub (fun Γ₅ h₅ => hsub Γ₅ fun y hy => h₅ ?_) ?_ ?_) ?_
    (List.Mem.head _) ?_
  · have := e₂ y hy
    rd_mem
  · rd_mem
  · rd_mem
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (h₄ (by rd_mem)))
  · rd_mem

theorem wf_rdPlainInst {N₁ : var₁ .nat} {N₂ : var₂ .nat} {xy₁ : var₁ Ty.strs}
    {xy₂ : var₂ Ty.strs} {c₁ : var₁ (Ty.coset D)} {c₂ : var₂ (Ty.coset D)}
    {O₁ : var₁ (.list .nat)} {O₂ : var₂ (.list .nat)} (hN : ⟨.nat, N₁, N₂⟩ ∈ Γ)
    (hxy : ⟨Ty.strs, xy₁, xy₂⟩ ∈ Γ) (hc : ⟨Ty.coset D, c₁, c₂⟩ ∈ Γ)
    (hO : ⟨.list .nat, O₁, O₂⟩ ∈ Γ) :
    Prog.Wf (rec := rec) r Γ (rdPlainInst N₁ xy₁ c₁ O₁) (rdPlainInst N₂ xy₂ c₂ O₂) := by
  unfold rdPlainInst
  refine .bind (wf_mkWindow hN hO) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) (.cons (by rd_mem) .nil))) fun _ _ => ?_
  exact .prim _ (.cons (by rd_mem) (.cons (List.Mem.head _) .nil))

theorem wf_rdTail {sub₁ : var₁ (hinstTy D) → Prog (groupSig D) rec var₁ (Ty.answer D)}
    {sub₂ : var₂ (hinstTy D) → Prog (groupSig D) rec var₂ (Ty.answer D)}
    (hsub : WfFun r Γ sub₁ sub₂) {n₀₁ n₁ N₁ : var₁ .nat} {n₀₂ n₂ N₂ : var₂ .nat}
    {xy₁ : var₁ Ty.strs} {xy₂ : var₂ Ty.strs} {c₁ : var₁ (Ty.coset D)}
    {c₂ : var₂ (Ty.coset D)} {τ₁ : var₁ Ty.perm} {τ₂ : var₂ Ty.perm} {H₁ : var₁ (Ty.group D)}
    {H₂ : var₂ (Ty.group D)} {O₁ : var₁ (.list .nat)} {O₂ : var₂ (.list .nat)}
    {r₁ : var₁ (deriveTy D)} {r₂ : var₂ (deriveTy D)}
    (hn₀ : ⟨.nat, n₀₁, n₀₂⟩ ∈ Γ) (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (hN : ⟨.nat, N₁, N₂⟩ ∈ Γ)
    (hxy : ⟨Ty.strs, xy₁, xy₂⟩ ∈ Γ) (hc : ⟨Ty.coset D, c₁, c₂⟩ ∈ Γ) (hτ : ⟨Ty.perm, τ₁, τ₂⟩ ∈ Γ)
    (hH : ⟨Ty.group D, H₁, H₂⟩ ∈ Γ) (hO : ⟨.list .nat, O₁, O₂⟩ ∈ Γ)
    (hr : ⟨deriveTy D, r₁, r₂⟩ ∈ Γ) :
    Prog.Wf r Γ (rdTail sub₁ n₀₁ n₁ N₁ xy₁ c₁ τ₁ H₁ O₁ r₁)
      (rdTail sub₂ n₀₂ n₂ N₂ xy₂ c₂ τ₂ H₂ O₂ r₂) := by
  unfold rdTail
  refine .bind (.prim _ (.cons hr .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by rd_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by rd_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by rd_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by rd_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by rd_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by rd_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by rd_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by rd_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ .nil) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by rd_mem) (.cons (List.Mem.head _) .nil))) fun _ _ => ?_
  refine .ite (List.Mem.head _) ?_ ?_
  · refine .bind (wf_rdPlainInst (by rd_mem) (by rd_mem) (by rd_mem) (by rd_mem)) fun _ _ => ?_
    exact wf_plainSub hsub hn₀ hn _ (fun y hy => by rd_mem) _ _ (List.Mem.head _)
  refine .bind (.prim _ .nil) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by rd_mem) (.cons (List.Mem.head _) .nil))) fun _ _ => ?_
  refine .ite (List.Mem.head _) ?_ ?_
  · refine .bind (.prim _ (.cons (by rd_mem) .nil)) fun _ _ => ?_
    refine .bind (wf_mkWindow (List.Mem.head _) (by rd_mem)) fun _ _ => ?_
    refine .bind (.prim _ .nil) fun _ _ => ?_
    refine wf_viaChildProg (wf_rd3Inner (hsub.mono fun y hy => by rd_mem) (by rd_mem)
      (by rd_mem) (by rd_mem) (by rd_mem) (by rd_mem) (by rd_mem) (by rd_mem)) (by rd_mem)
      (by rd_mem) (by rd_mem) (by rd_mem) (by rd_mem) (by rd_mem) (by rd_mem)
      (List.Mem.head _)
  refine .bind (.prim _ .nil) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by rd_mem) (.cons (List.Mem.head _) .nil))) fun _ _ => ?_
  refine .ite (List.Mem.head _) ?_ ?_
  · refine .bind (.prim _ (.cons (by rd_mem) .nil)) fun _ _ => ?_
    refine .bind (wf_mkWindow (List.Mem.head _) (by rd_mem)) fun _ _ => ?_
    refine .bind (.prim _ .nil) fun _ _ => ?_
    refine wf_viaChildProg (wf_rd5Inner (hsub.mono fun y hy => by rd_mem) (by rd_mem)
      (by rd_mem) (by rd_mem) (by rd_mem)) (by rd_mem) (by rd_mem) (by rd_mem) (by rd_mem)
      (by rd_mem) (by rd_mem) (by rd_mem) (List.Mem.head _)
  refine .bind (.prim _ .nil) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by rd_mem) (.cons (List.Mem.head _) .nil))) fun _ _ => ?_
  refine .ite (List.Mem.head _) ?_ ?_
  · refine .bind (wf_rdPlainInst (by rd_mem) (by rd_mem) (by rd_mem) (by rd_mem)) fun _ _ => ?_
    exact wf_kerRedProg (hsub.mono fun y hy => by rd_mem) (by rd_mem) (by rd_mem)
      (List.Mem.head _)
  refine .bind (.prim _ (.cons (by rd_mem) .nil)) fun _ _ => ?_
  exact wf_viaChildProg (hsub.mono fun y hy => by rd_mem) (by rd_mem) (by rd_mem) (by rd_mem)
    (by rd_mem) (by rd_mem) (by rd_mem) (by rd_mem) (List.Mem.head _)

theorem wf_rdHandle {sub₁ : var₁ (hinstTy D) → Prog (groupSig D) rec var₁ (Ty.answer D)}
    {sub₂ : var₂ (hinstTy D) → Prog (groupSig D) rec var₂ (Ty.answer D)}
    (hsub : WfFun r Γ sub₁ sub₂) {n₀₁ n₁ : var₁ .nat} {n₀₂ n₂ : var₂ .nat}
    {L₁ : var₁ (.array (.list .nat))} {L₂ : var₂ (.array (.list .nat))} {st₁ : var₁ stTy}
    {st₂ : var₂ stTy} {xy₁ : var₁ Ty.strs} {xy₂ : var₂ Ty.strs} {c₁ : var₁ (Ty.coset D)}
    {c₂ : var₂ (Ty.coset D)} {O₁ : var₁ (.list .nat)} {O₂ : var₂ (.list .nat)}
    (hn₀ : ⟨.nat, n₀₁, n₀₂⟩ ∈ Γ) (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ)
    (hL : ⟨.array (.list .nat), L₁, L₂⟩ ∈ Γ) (hst : ⟨stTy, st₁, st₂⟩ ∈ Γ)
    (hxy : ⟨Ty.strs, xy₁, xy₂⟩ ∈ Γ) (hc : ⟨Ty.coset D, c₁, c₂⟩ ∈ Γ)
    (hO : ⟨.list .nat, O₁, O₂⟩ ∈ Γ) :
    Prog.Wf r Γ (rdHandle sub₁ n₀₁ n₁ L₁ st₁ xy₁ c₁ O₁)
      (rdHandle sub₂ n₀₂ n₂ L₂ st₂ xy₂ c₂ O₂) := by
  unfold rdHandle
  refine .bind (.prim _ (.cons hc .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by rd_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (wf_deriveProg (by rd_mem) (List.Mem.head _) (by rd_mem) (by rd_mem) (by rd_mem)
    (by rd_mem)) fun _ _ => ?_
  exact wf_rdTail (hsub.mono fun y hy => by rd_mem) (by rd_mem) (by rd_mem) (by rd_mem)
    (by rd_mem) (by rd_mem) (by rd_mem) (by rd_mem) (by rd_mem) (List.Mem.head _)

theorem wf_rdBranch {sub₁ : var₁ (hinstTy D) → Prog (groupSig D) rec var₁ (Ty.answer D)}
    {sub₂ : var₂ (hinstTy D) → Prog (groupSig D) rec var₂ (Ty.answer D)}
    (hsub : WfFun r Γ sub₁ sub₂) {n₀₁ n₁ : var₁ .nat} {n₀₂ n₂ : var₂ .nat}
    {L₁ : var₁ (.array (.list .nat))} {L₂ : var₂ (.array (.list .nat))} {st₁ : var₁ stTy}
    {st₂ : var₂ stTy} (hn₀ : ⟨.nat, n₀₁, n₀₂⟩ ∈ Γ) (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ)
    (hL : ⟨.array (.list .nat), L₁, L₂⟩ ∈ Γ) (hst : ⟨stTy, st₁, st₂⟩ ∈ Γ) :
    WfFun r Γ (rdBranch sub₁ n₀₁ n₁ L₁ st₁) (rdBranch sub₂ n₀₂ n₂ L₂ st₂) := by
  intro Γ' hΓ J₁ J₂ hJ
  have hn₀' := hΓ hn₀
  have hn' := hΓ hn
  have hL' := hΓ hL
  have hst' := hΓ hst
  unfold rdBranch
  refine .bind (.prim _ (.cons hJ .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by rd_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by rd_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by rd_mem) .nil)) fun _ _ => ?_
  refine wf_dynSeqProg (fun Γ'' hΓ'' x₁ x₂ c₁ c₂ o₁ o₂ hx hc ho => ?_) (by rd_mem) (by rd_mem)
    (List.Mem.head _)
  exact wf_rdHandle (hsub.mono fun y hy => hΓ'' (by have := hΓ hy; rd_mem))
    (hΓ'' (by rd_mem)) (hΓ'' (by rd_mem)) (hΓ'' (by rd_mem)) (hΓ'' (by rd_mem)) hx hc ho

theorem wf_rdProg {sub₁ : var₁ (hinstTy D) → Prog (groupSig D) rec var₁ (Ty.answer D)}
    {sub₂ : var₂ (hinstTy D) → Prog (groupSig D) rec var₂ (Ty.answer D)}
    (hsub : WfFun r Γ sub₁ sub₂) {I₁ : var₁ (hinstTy D)} {I₂ : var₂ (hinstTy D)}
    {rs₁ : var₁ Ty.gens} {rs₂ : var₂ Ty.gens} {K₁ : var₁ (Ty.group D)}
    {K₂ : var₂ (Ty.group D)} {st₁ : var₁ stTy} {st₂ : var₂ stTy}
    (hI : ⟨hinstTy D, I₁, I₂⟩ ∈ Γ) (hrs : ⟨Ty.gens, rs₁, rs₂⟩ ∈ Γ)
    (hK : ⟨Ty.group D, K₁, K₂⟩ ∈ Γ) (hst : ⟨stTy, st₁, st₂⟩ ∈ Γ) :
    Prog.Wf r Γ (rdProg sub₁ I₁ rs₁ K₁ st₁) (rdProg sub₂ I₂ rs₂ K₂ st₂) := by
  unfold rdProg
  refine .bind (.prim _ (.cons hI .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by rd_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by rd_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by rd_mem) .nil)) fun _ _ => ?_
  refine .caseOption (List.Mem.head _) (.prim _ .nil) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by rd_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by rd_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by rd_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  exact wf_branchProg (wf_rdBranch (hsub.mono fun y hy => by rd_mem) (by rd_mem) (by rd_mem)
    (by rd_mem) (by rd_mem)) (by rd_mem) (by rd_mem) (List.Mem.head _) (by rd_mem) (by rd_mem)

end Wf

end GraphIso.Main
