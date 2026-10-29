module

public import GraphIso.Luks.MaxBlocksProg
public import GraphIso.Luks.Cost
public import GraphIso.Solver.Correctness
public import GraphIso.Reductions.BlockKernelProg

/-!
# Luks's strategy

`luksBody D` is one closed recursive procedure over `groupSig D`, structured like `solveBody`
(`GraphIso/Solver/Basic.lean`). On the instance `(x, y, W, σ • G)`:

1. **Empty window.** Return the input coset.
2. **Pointwise-fixed window.** Check whether `σ` carries `x` to `y` on `W` (`fixedCase`).
3. **Several orbits.** Process the orbits sequentially (`seqProg`), each by a recursive call.
4. **Transitive window.** Compute a maximal block system (`maxBlocksProg`, no backend calls)
   and run the block reduction (`blockReduceProg`): for each coset of the block kernel `K`,
   process the blocks sequentially, each by a recursive call.

Every recursive call has a smaller window: orbits are proper subsets of the window, and there
are at least two blocks. The procedure is well-formed (`luksBody_wf`).

The bounds the cost theorem needs from a backend are `LuksBounds`: charges of the calls the
strategy makes, for groups with at most `s` generators inside an ambient group `G₀`, with at
most `R` coset representatives, and generator counts of the groups the backend returns. The
per-invocation unit is `luksQ`.
-/

@[expose] public section

namespace GraphIso.Luks

open Equiv Cost Programs Solver

variable {var : Ty → Type} {D : Ty}

/-- The transitive case: a maximal block system and the block reduction. -/
def luksTransitive (xy : var Ty.strs) (w : var Ty.win) (pts : var (.list .nat))
    (σ : var Ty.perm) (G : var (Ty.group D)) : Prog (groupSig D) (Rec D) var (Ty.answer D) :=
  .bind (.op1 .fst G) fun n => .bind (.op1 .snd G) fun gd => .bind (.op1 .fst gd) fun gens =>
  .bind (maxBlocksProg n gens pts) fun bs =>
  blockReduceProg (fun J => .recur J) xy w σ G bs

/-- The window is not fixed pointwise: split into orbits, or use blocks if transitive. -/
def luksMoved (xy : var Ty.strs) (w : var Ty.win) (pts : var (.list .nat))
    (c : var (Ty.coset D)) (σ : var Ty.perm) (G : var (Ty.group D)) :
    Prog (groupSig D) (Rec D) var (Ty.answer D) :=
  .bind (.op2 .pair G w) fun Gw =>
  .bind (Prog.call (S := groupSig D) GroupOp.orbits Gw) fun os =>
  .caseList os (.op0 .none) fun _ orest =>
    .caseList orest (luksTransitive xy w pts σ G) fun _ _ => seqProg (fun J => .recur J) xy c os

/-- A nonempty window: test pointwise fixing by the generators, then dispatch. -/
def luksNonempty (xy : var Ty.strs) (w : var Ty.win) (pts : var (.list .nat))
    (c : var (Ty.coset D)) (σ : var Ty.perm) (G : var (Ty.group D)) :
    Prog (groupSig D) (Rec D) var (Ty.answer D) :=
  .bind (.op1 .snd G) fun gd => .bind (.op1 .fst gd) fun gens =>
  .bind (fixesProg gens pts) fun fixed =>
  .ite fixed (fixedCase xy pts σ c) (luksMoved xy w pts c σ G)

/-- Luks's strategy. -/
def luksBody (D : Ty) : Proc (groupSig D) (Ty.inst D) (Ty.answer D) := fun _ I =>
  .bind (.op1 .fst I) fun xy => .bind (.op1 .snd I) fun wc =>
  .bind (.op1 .fst wc) fun w => .bind (.op1 .snd wc) fun c =>
  .bind (.op1 .fst c) fun σ => .bind (.op1 .snd c) fun G =>
  .bind (.op1 .fst w) fun pts =>
  .caseList pts (.op1 .some c) fun _ _ => luksNonempty xy w pts c σ G

/-- Luks's strategy is a well-formed procedure. -/
theorem luksBody_wf : (luksBody D).Wf := by
  intro var₁ var₂ x₁ x₂
  unfold luksBody
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun xy₁ xy₂ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun wc₁ wc₂ =>
    .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun w₁ w₂ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun c₁ c₂ =>
    .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun σ₁ σ₂ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun G₁ G₂ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun pts₁ pts₂ =>
    .caseList (List.Mem.head _) (.prim _ (.cons (by simp) .nil)) fun _ _ _ _ => ?_
  unfold luksNonempty
  refine .bind (.prim _ (.cons (by simp) .nil)) fun gd₁ gd₂ =>
    .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun gs₁ gs₂ =>
    .bind (wf_fixesProg (List.Mem.head _) (by simp)) fun f₁ f₂ =>
    .ite (List.Mem.head _) ?_ ?_
  · unfold fixedCase
    exact .bind (wf_matchesProg (by simp) (by simp) (by simp)) fun o₁ o₂ =>
      .ite (List.Mem.head _) (.prim _ (.cons (by simp) .nil)) (.prim _ .nil)
  unfold luksMoved
  refine .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun Gw₁ Gw₂ =>
    .bind (.call _ (List.Mem.head _)) fun os₁ os₂ =>
    .caseList (List.Mem.head _) (.prim _ .nil) fun _ _ or₁ or₂ =>
    .caseList (by simp) ?_ fun _ _ _ _ => ?_
  · unfold luksTransitive
    refine .bind (.prim _ (.cons (by simp) .nil)) fun n₁ n₂ =>
      .bind (.prim _ (.cons (by simp) .nil)) fun gd₁ gd₂ =>
      .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun gs₁ gs₂ =>
      .bind (wf_maxBlocksProg (by simp) (List.Mem.head _) (by simp)) fun bs₁ bs₂ =>
      wf_blockReduceProg ?_ (by simp) (by simp) (by simp) (by simp) (List.Mem.head _)
    intro Γ' _ J₁ J₂ hJ
    exact .recur rfl hJ
  · refine wf_seqProg ?_ (by simp) (by simp)
      (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
    intro Γ' _ J₁ J₂ hJ
    exact .recur rfl hJ

/-! ### Peeling the program -/

section Peel

variable {X : Ctx (groupSig D)} {xy : StrData × StrData} {σd : PermData}
  {G : GroupData D.denote}

theorem run_luksBody {w : WinData} {ans : AnswerData D} {k : ℕ}
    (h : RunsWithin X (luksBody D Ty.denote)
      (Prog.caseList (a := .nat) w.1 (.op1 .some (σd, G))
        fun _ _ => luksNonempty (D := D) xy w w.1 (σd, G) σd G) ans k) :
    RunsWithin X (luksBody D Ty.denote) (luksBody D Ty.denote (xy, w, σd, G)) ans (7 + k) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact h
  case hc =>
    simp only [Prim.cost]
    omega

theorem run_luksNonempty_fixed {w : WinData} {ans : AnswerData D} {k : ℕ}
    (hfix : GensData.fixesB G.gens w = true)
    (h : RunsWithin X (luksBody D Ty.denote) (fixedCase (D := D) xy w.1 σd (σd, G)) ans k) :
    RunsWithin X (luksBody D Ty.denote) (luksNonempty (D := D) xy w w.1 (σd, G) σd G) ans
      (G.gens.length * (5 * w.1.length + 3) + 4 + k) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.fixesProg G.gens w)
    rw [hfix]
    exact RunsWithin.ite_true h
  case hc =>
    simp only [Prim.cost, GroupData.gens]
    omega

theorem run_luksNonempty_moved {w : WinData} {ans : AnswerData D} {k : ℕ}
    (hfix : GensData.fixesB G.gens w = false)
    (h : RunsWithin X (luksBody D Ty.denote) (luksMoved (D := D) xy w w.1 (σd, G) σd G) ans k) :
    RunsWithin X (luksBody D Ty.denote) (luksNonempty (D := D) xy w w.1 (σd, G) σd G) ans
      (G.gens.length * (5 * w.1.length + 3) + 4 + k) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.fixesProg G.gens w)
    rw [hfix]
    exact RunsWithin.ite_false h
  case hc =>
    simp only [Prim.cost, GroupData.gens]
    omega

theorem run_luksFixed {w : WinData} :
    RunsWithin X (luksBody D Ty.denote) (fixedCase (D := D) xy w.1 σd (σd, G))
      (if matchesB w σd xy.1 xy.2 then some (σd, G) else none) (7 * w.1.length + 5) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.matchesProg w σd xy)
    cases matchesB w σd xy.1 xy.2
    · exact RunsWithin.ite_false (RunsWithin.prim _ _)
    · exact RunsWithin.ite_true (RunsWithin.prim _ _)
  case hc =>
    simp only [Prim.cost]
    omega

/-- The orbit case, given the orbit list returned by the backend. -/
theorem run_luksMoved {w : WinData} {ans : AnswerData D} {k : ℕ}
    (hk : RunsWithin X (luksBody D Ty.denote)
      (Prog.caseList (a := .list .nat) (X.O.run .orbits (G, w)) (.op0 .none) fun _ orest =>
        Prog.caseList orest (luksTransitive (D := D) xy w w.1 σd G) fun _ _ =>
          seqProg (fun J => .recur J) xy (σd, G) (X.O.run .orbits (G, w))) ans k)
    (hpre : X.Pre .orbits (G, w)) :
    RunsWithin X (luksBody D Ty.denote) (luksMoved (D := D) xy w w.1 (σd, G) σd G) ans
      (1 + X.B.call .orbits (G, w) (X.O.run .orbits (G, w)) + k) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.call hpre)
    exact hk
  case hc =>
    simp only [Prim.cost, Prim.eval]
    omega

/-- The transitive case, given the run of the block reduction on the maximal blocks. -/
theorem run_luksTransitive {n : ℕ} {gs : GensData} {d : D.denote} {w : WinData}
    (hW : Win n gs w.1) {ans : AnswerData D} {k : ℕ}
    (h : RunsWithin X (luksBody D Ty.denote)
      (blockReduceProg (fun J => .recur J) xy w σd (n, gs, d) (maxBlocks n gs w.1)) ans k) :
    RunsWithin X (luksBody D Ty.denote) (luksTransitive (D := D) xy w w.1 σd (n, gs, d)) ans
      (3 + maxBlocksCost n w.1.length gs.length + k) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.maxBlocksProg hW)
    exact h
  case hc =>
    simp only [Prim.cost, Prim.eval]
    omega

end Peel

/-! ### Primitive sections and backend bounds -/

/-- **Bounded primitive sections**: every primitive permutation group of degree `k ≥ 2` that is a
homomorphic image of a subgroup of `G₀` has order at most `k ^ c`. -/
def PrimBounded {n : ℕ} (G₀ : Subgroup (Perm (Fin n))) (c : ℕ) : Prop :=
  ∀ H : Subgroup (Perm (Fin n)), H ≤ G₀ → ∀ (k : ℕ) (φ : H →* Perm (Fin k)), 2 ≤ k →
    MulAction.IsPreprimitive φ.range (Fin k) → Nat.card φ.range ≤ k ^ c

/-- The operations Luks's strategy calls. -/
def luksOps (op : GroupOp) : Prop :=
  op = .orbits ∨ op = .generate ∨ op = .kernel ∨ op = .cosetReps

/-- Bounds on a group backend at degree `n`, for subgroups of an ambient group `G₀` given by at
most `s` generators, with at most `R` coset representatives of block kernels: charges of the
calls Luks's strategy makes, and generator counts of the groups the backend returns. -/
structure LuksBounds (X : Ctx (groupSig D)) (DV : ℕ → GensData → D.denote → Prop)
    (n s R : ℕ) (G₀ : Subgroup (Perm (Fin n))) where
  /-- Bound on an `orbits` charge. -/
  Borb : ℕ
  /-- Bound on generating the extended group of a block system. -/
  Bge : ℕ
  /-- Bound on its kernel on the block points. -/
  Bke : ℕ
  /-- Bound on generating the block kernel from the truncated kernel generators. -/
  Bgt : ℕ
  /-- Bound on the generator count of the kernel on the block points. -/
  sKe : ℕ
  /-- Bound on a `cosetReps` charge for a block kernel with at most `R` cosets. -/
  Bcr : ℕ
  /-- Bound on a `generate` charge, for at most `R (s + 1)` input generators. -/
  Bgen : ℕ
  orbits : ∀ (gs : GensData) (d : D.denote) (w : WinData), gs.length ≤ s →
    GensData.denote n gs ≤ G₀ → GroupPre DV .orbits ((n, gs, d), w) →
    X.B.call .orbits ((n, gs, d), w) (X.O.run .orbits ((n, gs, d), w)) ≤ Borb
  blocks : ∀ (gs : GensData) (d : D.denote) (w : WinData) (bs : List (List ℕ)),
    gs.length ≤ s → GensData.denote n gs ≤ G₀ → GroupValid DV n gs d → w.Valid n →
    IsBlockList w bs → PermutesBlocks (GensData.denote n gs) bs →
    X.B.call GroupOp.generate (n + bs.length, extendGens n bs gs) (extGroup X.O n bs gs) ≤ Bge ∧
    X.B.call GroupOp.kernel (extGroup X.O n bs gs, blockWin n bs.length)
      (extKernel X.O n bs gs) ≤ Bke ∧
    X.B.call GroupOp.generate (n, (extKernel X.O n bs gs).2.1.map (PermData.truncTo n))
      (blockKernelModel X.O n bs gs) ≤ Bgt ∧
    (extKernel X.O n bs gs).2.1.length ≤ sKe ∧ (blockKernelModel X.O n bs gs).2.1.length ≤ s
  cosetReps : ∀ (gs : GensData) (d : D.denote) (w : WinData) (bs : List (List ℕ)),
    gs.length ≤ s → GensData.denote n gs ≤ G₀ → GroupValid DV n gs d → w.Valid n →
    IsBlockList w bs → PermutesBlocks (GensData.denote n gs) bs →
    (X.O.run GroupOp.cosetReps ((n, gs, d), blockKernelModel X.O n bs gs)).length ≤ R →
    X.B.call GroupOp.cosetReps ((n, gs, d), blockKernelModel X.O n bs gs)
      (X.O.run GroupOp.cosetReps ((n, gs, d), blockKernelModel X.O n bs gs)) ≤ Bcr
  generate : ∀ hs : GensData, GensData.AllValid n hs → hs.length ≤ R * (s + 1) →
    GensData.denote n hs ≤ G₀ → X.B.call .generate (n, hs) (X.O.run .generate (n, hs)) ≤ Bgen
  /-- Generated groups have at most `s` generators. -/
  genOut : ∀ hs : GensData, GensData.AllValid n hs → GensData.denote n hs ≤ G₀ →
    (X.O.run .generate (n, hs)).2.1.length ≤ s

/-- Local work and backend charges of one invocation, besides its recursive calls. -/
def luksNode (n s Borb Bge Bke Bgt sKe Bcr Bgen : ℕ) : ℕ :=
  s * (5 * n + 3) + 7 * n + Borb + maxBlocksCost n n s + blockKernelCost n n n s sKe Bge Bke Bgt +
    Bcr + Bgen + 60

/-- Overhead of one recursive call on an orbit or a block. -/
def luksEdge (n : ℕ) : ℕ := 7 * n + 14

/-- Overhead of one branch of the block reduction. -/
def luksBranch (n s : ℕ) : ℕ := 24 * n + s + 48

/-- The per-invocation unit of Luks's strategy. -/
def luksQ (n s Borb Bge Bke Bgt sKe Bcr Bgen : ℕ) : ℕ :=
  luksNode n s Borb Bge Bke Bgt sKe Bcr Bgen + 2 * (luksEdge n + luksBranch n s)

end GraphIso.Luks
