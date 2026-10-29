module

public import GraphIso.Reductions.Blocks
public import GraphIso.Solver.Facts

/-!
# The block-system reduction

`blockProg sub xy w σ G K bs` solves `iso W (σ G) x y` for a block list `bs` of the window and
a group `K` inside the block kernel of `G`:

1. the backend lists coset representatives `R` of `K` in `G` (`cosetReps`);
2. each branch `σ r • K` is solved by processing the blocks one after the other
   (`seqProg`), each block window by the sub-solver `sub`; every block is `K`-invariant;
3. the branch answers are combined (`branchProg`).

`RunsWithin.blockProg` proves the answer correct, with cost

  `2 + B_cr + |R| (24 n + C_b + s' + 45) + B_gen + 19`,

where `C_b = 3 + Σ_b (C b + 2 n + 5 |b| + 13)` is the cost of one branch and
`|R| · |K| = |G|`: the number of branches is the index `[G : K]`, left explicit.
-/

@[expose] public section

namespace GraphIso.Programs

open Equiv Cost

section Program

variable {D : Ty} {rec : Ty × Ty} {var : Ty → Type}

/-- The branch sub-solver: process the blocks inside the branch coset. -/
def blockBranch (sub : var (Ty.inst D) → Prog (groupSig D) rec var (Ty.answer D))
    (xy : var Ty.strs) (bs : var (.list (.list .nat))) (J : var (Ty.inst D)) :
    Prog (groupSig D) rec var (Ty.answer D) :=
  .bind (.op1 .snd J) fun wc => .bind (.op1 .snd wc) fun c => seqProg sub xy c bs

/-- Branch over the cosets of `K` in `G`, processing the blocks in each branch. -/
def blockProg (sub : var (Ty.inst D) → Prog (groupSig D) rec var (Ty.answer D))
    (xy : var Ty.strs) (w : var Ty.win) (σ : var Ty.perm) (G K : var (Ty.group D))
    (bs : var (.list (.list .nat))) : Prog (groupSig D) rec var (Ty.answer D) :=
  .bind (.op2 .pair G K) fun gk =>
  .bind (Prog.call (S := groupSig D) GroupOp.cosetReps gk) fun rs =>
  branchProg (blockBranch sub xy bs) xy w σ K rs

end Program

section Reduction

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}

/-- The backend operations used by the block reduction. -/
def blockOps (op : GroupOp) : Prop := op = .generate ∨ op = .cosetReps

/-- A transversal given by represented elements, as the cover `branchProg` expects. -/
theorem isLeftCover_map {n : ℕ} {G K : Subgroup (Perm (Fin n))} (rs : List PermData)
    (h : IsLeftTransversal G K fun i : Fin rs.length => PermData.denote n (rs.get i)) :
    IsLeftCover G K fun i : Fin (rs.map (PermData.denote n)).length =>
      (rs.map (PermData.denote n)).get i := by
  refine ⟨fun i => ?_, fun g hg => ?_⟩
  · have := h.mem ⟨i, lt_of_lt_of_eq i.2 (List.length_map _)⟩
    simpa using this
  · obtain ⟨j, hj⟩ := h.cover g hg
    exact ⟨⟨j, lt_of_lt_of_eq j.2 (List.length_map _).symm⟩, by simpa using hj⟩

/-- The cost of one branch: processing the blocks. -/
def blockBranchCost (n : ℕ) (Cw : List ℕ → ℕ) (bs : List (List ℕ)) : ℕ :=
  3 + (bs.map (seqCost n Cw)).sum

/-- **The block-system reduction.** -/
theorem RunsWithin.blockProg (hO : MeetsContractOn DV blockOps X.O)
    (hPre : ∀ op x, blockOps op → GroupPre DV op x → X.Pre op x)
    {sub : InstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)}
    {xy : StrData × StrData} {w : WinData} {σd : PermData} {n : ℕ} {gs ks : GensData}
    {d e : D.denote} {bs : List (List ℕ)} (hw : w.Valid n) (hσ : σd.Valid n)
    (hGv : GroupValid DV n gs d) (hWG : IsInvariant (GensData.denote n gs) (w.denote n))
    (hKv : GroupValid DV n ks e) (hK : GensData.denote n ks ≤ blockKernel (GensData.denote n gs) bs)
    (hbs : IsBlockList w bs) {Cw : List ℕ → ℕ} {s Bcr Bgen : ℕ}
    (hsub : SeqSub X body DV sub xy n bs Cw s (max s ks.length) (GensData.denote n ks))
    (hBcr : X.B.call GroupOp.cosetReps ((n, gs, d), (n, ks, e))
      (X.O.run GroupOp.cosetReps ((n, gs, d), (n, ks, e))) ≤ Bcr)
    (hB : ∀ hs : GensData, GensData.AllValid n hs →
      hs.length ≤ (X.O.run GroupOp.cosetReps ((n, gs, d), (n, ks, e))).length *
        (max s ks.length + 1) →
      GensData.denote n hs ≤ GensData.denote n gs →
      X.B.call GroupOp.generate (n, hs) (X.O.run GroupOp.generate (n, hs)) ≤ Bgen) :
    ∃ ans : AnswerData D,
      RunsWithin X body (Programs.blockProg sub xy w σd (n, gs, d) (n, ks, e) bs) ans
        (2 + Bcr + (X.O.run GroupOp.cosetReps ((n, gs, d), (n, ks, e))).length *
          (24 * n + blockBranchCost n Cw bs + max s ks.length + 45) + Bgen + 19) ∧
      AnsOK DV n (w.denote n) (PermData.denote n σd) (GensData.denote n gs) (xy.1.denote n)
        (xy.2.denote n) ans ∧
      (X.O.run GroupOp.cosetReps ((n, gs, d), (n, ks, e))).length *
          Nat.card (GensData.denote n ks) = Nat.card (GensData.denote n gs) ∧
      ∀ sGen, (∀ hs, GensData.AllValid n hs → GensData.denote n hs ≤ GensData.denote n gs →
          (X.O.run GroupOp.generate (n, hs)).2.1.length ≤ sGen) →
        ∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sGen := by
  have hKG : GensData.denote n ks ≤ GensData.denote n gs := hK.trans (blockKernel_le _ _)
  have hcrpre : GroupPre DV .cosetReps ((n, gs, d), (n, ks, e)) := ⟨hGv, hKv, rfl, hKG⟩
  obtain ⟨hrsv, htrans⟩ := hO .cosetReps _ (Or.inr rfl) hcrpre
  have hrsv' : ∀ r ∈ (show List PermData from
      X.O.run GroupOp.cosetReps ((n, gs, d), (n, ks, e))), r.Valid n := hrsv
  have hcover : IsLeftCover (GensData.denote n gs) (GensData.denote n ks)
      fun i : Fin ((show List PermData from X.O.run GroupOp.cosetReps ((n, gs, d), (n, ks, e))).map
        (PermData.denote n)).length =>
        ((show List PermData from X.O.run GroupOp.cosetReps ((n, gs, d), (n, ks, e))).map
          (PermData.denote n)).get i :=
    isLeftCover_map _ htrans
  obtain ⟨hseq, hunion⟩ := seqInputs_of_blocks hw hbs hK
  have hbr : SubSolves X body DV (fun J => Programs.blockBranch sub xy bs J)
      (fun J => J.1 = xy ∧ J.2.1 = w ∧ J.2.2.2 = (n, ks, e) ∧
        (∃ r ∈ (show List PermData from X.O.run GroupOp.cosetReps ((n, gs, d), (n, ks, e))),
          J.2.2.1 = σd.mul r) ∧ J.Valid DV)
      (fun _ => blockBranchCost n Cw bs) (max s ks.length) := by
    rintro ⟨xy', w', σ', Kd⟩ ⟨h₁, h₂, h₃, ⟨r, hr, h₄⟩, hJv⟩
    change xy' = xy at h₁
    change w' = w at h₂
    change Kd = (n, ks, e) at h₃
    change σ' = σd.mul r at h₄
    subst xy' w' Kd σ'
    obtain ⟨ans, hrun, hok, hg⟩ := RunsWithin.seqProg (X := X) (body := body) (sub := sub)
      (n := n) (σd := σd.mul r) (Gd := (n, ks, e)) rfl hJv.rep hKv hseq hsub
    refine ⟨ans, ?_, ?_, hg⟩
    · apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        exact hrun
      case hc =>
        simp only [Prim.cost, blockBranchCost]
        omega
    · change AnsOK DV n (WinData.denote n w) _ _ _ _ ans
      rw [← hunion]
      exact hok
  obtain ⟨ans, hrun, hok, hgen⟩ := RunsWithin.branchProg (X := X) (body := body)
    (fun op x hop hx => hO op x (Or.inl hop) hx) (fun x hx => hPre .generate x (Or.inl rfl) hx)
    hw hσ hKv hKG hWG hrsv' hcover hbr hB
  refine ⟨ans, ?_, hok, ?_, hgen⟩
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.call (hPre _ _ (Or.inr rfl) hcrpre))
      exact hrun
    case hc =>
      simp only [Prim.cost, Prim.eval]
      omega
  · have := htrans.card_eq hKG
    rw [this, Nat.mul_comm]

end Reduction

section Wf

variable {D : Ty} {rec : Ty × Ty} {var₁ var₂ : Ty → Type} {r : Bool} {Γ : WfCtx var₁ var₂}

theorem wf_blockProg {sub₁ : var₁ (Ty.inst D) → Prog (groupSig D) rec var₁ (Ty.answer D)}
    {sub₂ : var₂ (Ty.inst D) → Prog (groupSig D) rec var₂ (Ty.answer D)}
    (hsub : WfFun r Γ sub₁ sub₂) {xy₁ : var₁ Ty.strs} {xy₂ : var₂ Ty.strs}
    {w₁ : var₁ Ty.win} {w₂ : var₂ Ty.win} {σ₁ : var₁ Ty.perm} {σ₂ : var₂ Ty.perm}
    {G₁ K₁ : var₁ (Ty.group D)} {G₂ K₂ : var₂ (Ty.group D)}
    {bs₁ : var₁ (.list (.list .nat))} {bs₂ : var₂ (.list (.list .nat))}
    (hxy : ⟨Ty.strs, xy₁, xy₂⟩ ∈ Γ) (hw : ⟨Ty.win, w₁, w₂⟩ ∈ Γ) (hσ : ⟨Ty.perm, σ₁, σ₂⟩ ∈ Γ)
    (hG : ⟨Ty.group D, G₁, G₂⟩ ∈ Γ) (hK : ⟨Ty.group D, K₁, K₂⟩ ∈ Γ)
    (hbs : ⟨.list (.list .nat), bs₁, bs₂⟩ ∈ Γ) :
    Prog.Wf r Γ (blockProg sub₁ xy₁ w₁ σ₁ G₁ K₁ bs₁) (blockProg sub₂ xy₂ w₂ σ₂ G₂ K₂ bs₂) := by
  unfold blockProg
  refine .bind (.prim _ (.cons hG (.cons hK .nil))) fun gk₁ gk₂ => .bind (.call _ (List.Mem.head _))
    fun rs₁ rs₂ => wf_branchProg ?_ (by simp [hxy]) (by simp [hw]) (by simp [hσ]) (by simp [hK])
      (List.Mem.head _)
  · intro Γ' hΓ' J₁ J₂ hJ
    unfold blockBranch
    refine .bind (.prim _ (.cons hJ .nil)) fun wc₁ wc₂ => .bind (.prim _ (.cons (by simp) .nil))
      fun c₁ c₂ => wf_seqProg (hsub.mono ?_) ?_ (by simp) ?_
    · exact fun y hy => by simp [hΓ' (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hy))]
    · simp [hΓ' (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hxy))]
    · simp [hΓ' (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hbs))]

end Wf

end GraphIso.Programs
