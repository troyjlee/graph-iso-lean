module

public import GraphIso.Main.M5StepCJ

/-!
# Coloured Johnson pairs in M5: well-formedness

Stage 14j-4b (`PLAN-14.md` §14.5): the relational well-formedness (`Prog.Wf`) of the programs of
the stage, from the colourings to `m5StepCJProg` (`wf_m5StepCJProg`), as for 14j-4's programs.
-/

@[expose] public section

namespace GraphIso.Main

open Cost GraphIso GraphIso.Programs GraphIso.Toolkit GraphIso.SoJProg GraphIso.SoJTree
  GraphIso.Case2b GraphIso.Align GraphIso.Recursion GraphIso.Solver GraphIso.Certificates
  GraphIso.CertProg

section Wf

variable {D : Ty} {rec : Ty × Ty} {var₁ var₂ : Ty → Type} {r : Bool} {Γ : WfCtx var₁ var₂}

local macro "m5_mem" : tactic =>
  `(tactic| repeat (first | exact List.mem_cons_self | assumption | apply List.mem_cons_of_mem))

theorem wf_q2bProg {S : Signature} {m₁ : var₁ .nat} {m₂ : var₂ .nat}
    {Φ₁ Sl₁ : var₁ (.list .nat)} {Φ₂ Sl₂ : var₂ (.list .nat)} (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ)
    (hΦ : ⟨.list .nat, Φ₁, Φ₂⟩ ∈ Γ) (hS : ⟨.list .nat, Sl₁, Sl₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (q2bProg m₁ Φ₁ Sl₁) (q2bProg m₂ Φ₂ Sl₂) := by
  unfold q2bProg mapList
  prog_wf

theorem wf_q3Prog {S : Signature} {M₁ : var₁ .nat} {M₂ : var₂ .nat}
    {V₁ C₁ : var₁ (.list .nat)} {V₂ C₂ : var₂ (.list .nat)} (hM : ⟨.nat, M₁, M₂⟩ ∈ Γ)
    (hV : ⟨.list .nat, V₁, V₂⟩ ∈ Γ) (hC : ⟨.list .nat, C₁, C₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (q3Prog M₁ V₁ C₁) (q3Prog M₂ V₂ C₂) := by
  unfold q3Prog mapList
  prog_wf

theorem wf_cjOfProg {S : Signature} {q₁ : var₁ (.array .nat)} {q₂ : var₂ (.array .nat)}
    {o₁ : var₁ outTy} {o₂ : var₂ outTy} (hq : ⟨.array .nat, q₁, q₂⟩ ∈ Γ)
    (ho : ⟨outTy, o₁, o₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (cjOfProg q₁ o₁) (cjOfProg q₂ o₂) := by
  unfold cjOfProg
  prog_wf

theorem wf_firstTupleProg {S : Signature} {Φ₁ : var₁ (.list .nat)} {Φ₂ : var₂ (.list .nat)}
    {j₁ : var₁ .nat} {j₂ : var₂ .nat} (hΦ : ⟨.list .nat, Φ₁, Φ₂⟩ ∈ Γ) (hj : ⟨.nat, j₁, j₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (firstTupleProg Φ₁ j₁) (firstTupleProg Φ₂ j₂) := by
  unfold firstTupleProg
  exact .bind (wf_tuplesProg hΦ hj) fun _ _ =>
    .caseList (by simp) (.prim _ .nil) fun _ _ _ _ => .ret (by simp)

theorem wf_cjLeaves2bProg {N₁ n₁ j₁ : var₁ .nat} {N₂ n₂ j₂ : var₂ .nat}
    {F₁ : var₁ (Ty.group D)} {F₂ : var₂ (Ty.group D)} {Φ₁ : var₁ (.list .nat)}
    {Φ₂ : var₂ (.list .nat)} (hN : ⟨.nat, N₁, N₂⟩ ∈ Γ) (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ)
    (hF : ⟨Ty.group D, F₁, F₂⟩ ∈ Γ) (hΦ : ⟨.list .nat, Φ₁, Φ₂⟩ ∈ Γ) (hj : ⟨.nat, j₁, j₂⟩ ∈ Γ) :
    Prog.Wf (S := groupSig D) (rec := rec) r Γ (cjLeaves2bProg N₁ n₁ F₁ Φ₁ j₁)
      (cjLeaves2bProg N₂ n₂ F₂ Φ₂ j₂) := by
  unfold cjLeaves2bProg
  refine .bind (wf_tuplesProg hΦ hj) fun _ _ => Align.wf_joFlatMap (by simp)
    fun Γ' hΓ S₁ S₂ hS => ?_
  have hN' : (⟨.nat, N₁, N₂⟩ : Σ t : Ty, var₁ t × var₂ t) ∈ Γ' := hΓ (List.mem_cons_of_mem _ hN)
  have hn' : (⟨.nat, n₁, n₂⟩ : Σ t : Ty, var₁ t × var₂ t) ∈ Γ' := hΓ (List.mem_cons_of_mem _ hn)
  have hF' : (⟨Ty.group D, F₁, F₂⟩ : Σ t : Ty, var₁ t × var₂ t) ∈ Γ' :=
    hΓ (List.mem_cons_of_mem _ hF)
  have hΦ' : (⟨.list .nat, Φ₁, Φ₂⟩ : Σ t : Ty, var₁ t × var₂ t) ∈ Γ' :=
    hΓ (List.mem_cons_of_mem _ hΦ)
  refine .bind (.prim _ (.cons hN' (.cons hn' .nil))) fun m₁ m₂ =>
    .bind (wf_q2bProg (by simp) (by simp [hΦ']) (by simp [hS])) fun q₁ q₂ =>
    .bind (wf_phiSProg (by simp) (by simp [hΦ']) (by simp [hS])) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (Case2b.wf_pairsProg (by simp)) fun _ _ =>
    Align.wf_joFlatMap (by simp) fun Γ'' hΓ' ab₁ ab₂ hab => ?_
  have hN'' : (⟨.nat, N₁, N₂⟩ : Σ t : Ty, var₁ t × var₂ t) ∈ Γ'' := hΓ' (by simp [hN'])
  have hn'' : (⟨.nat, n₁, n₂⟩ : Σ t : Ty, var₁ t × var₂ t) ∈ Γ'' := hΓ' (by simp [hn'])
  have hF'' : (⟨Ty.group D, F₁, F₂⟩ : Σ t : Ty, var₁ t × var₂ t) ∈ Γ'' := hΓ' (by simp [hF'])
  have hΦ'' : (⟨.list .nat, Φ₁, Φ₂⟩ : Σ t : Ty, var₁ t × var₂ t) ∈ Γ'' := hΓ' (by simp [hΦ'])
  have hS'' : (⟨.list .nat, S₁, S₂⟩ : Σ t : Ty, var₁ t × var₂ t) ∈ Γ'' := hΓ' (by simp [hS])
  have hq'' : (⟨.array .nat, q₁, q₂⟩ : Σ t : Ty, var₁ t × var₂ t) ∈ Γ'' := hΓ' (by simp)
  exact .bind (.prim _ (.cons hab .nil)) fun _ _ => .bind (.prim _ (.cons (by simp [hab]) .nil))
    fun _ _ => .bind (wf_choiceProg (by simp [hN'']) (by simp [hn'']) (by simp [hF''])
      (by simp [hΦ'']) (by simp [hS'']) (by simp) (by simp)) fun _ _ =>
    Align.wf_joFlatMap (by simp) fun _ hΓ'' _ _ ho => wf_cjOfProg (hΓ'' (by simp [hq''])) ho

theorem wf_c3ClsProg {S : Signature} {t₁ : var₁ .nat} {t₂ : var₂ .nat}
    {rk₁ rm₁ z₁ : var₁ (.list .nat)} {rk₂ rm₂ z₂ : var₂ (.list .nat)}
    {VA₁ W₁ : var₁ (.array .nat)} {VA₂ W₂ : var₂ (.array .nat)}
    {pw₁ : var₁ (.array (.array .nat))} {pw₂ : var₂ (.array (.array .nat))}
    (hVA : ⟨.array .nat, VA₁, VA₂⟩ ∈ Γ) (hW : ⟨.array .nat, W₁, W₂⟩ ∈ Γ)
    (hpw : ⟨.array (.array .nat), pw₁, pw₂⟩ ∈ Γ) (hrk : ⟨.list .nat, rk₁, rk₂⟩ ∈ Γ)
    (hrm : ⟨.list .nat, rm₁, rm₂⟩ ∈ Γ) (ht : ⟨.nat, t₁, t₂⟩ ∈ Γ)
    (hz : ⟨.list .nat, z₁, z₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (c3ClsProg VA₁ W₁ pw₁ rk₁ rm₁ t₁ z₁)
      (c3ClsProg VA₂ W₂ pw₂ rk₂ rm₂ t₂ z₂) := by
  unfold c3ClsProg
  exact .bind (.prim _ (.cons hz .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp [hz]) .nil)) fun _ _ =>
    .bind (Coherent.wf_col1Prog (by simp [hW]) (by simp [hpw]) (by simp [hrk]) (by simp [hrm])
      (by simp) (by simp)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (Coherent.wf_domProg (by simp) (by simp) (by simp [hrm]) (by simp [ht])) fun _ _ =>
    .caseOption (by simp) (.prim _ .nil) fun _ _ =>
      .bind (Coherent.wf_classProg (by simp) (by simp [hrm]) (by simp)) fun _ _ =>
        wf_mapList (by simp) fun _ hΓ _ _ hi =>
          .prim _ (.cons (hΓ (by simp [hVA])) (.cons hi .nil))

theorem wf_cjOutcome3Prog {S : Signature} {M₁ t₁ : var₁ .nat} {M₂ t₂ : var₂ .nat}
    {V₁ rk₁ rm₁ z₁ : var₁ (.list .nat)} {V₂ rk₂ rm₂ z₂ : var₂ (.list .nat)}
    {VA₁ W₁ : var₁ (.array .nat)} {VA₂ W₂ : var₂ (.array .nat)}
    {pw₁ : var₁ (.array (.array .nat))} {pw₂ : var₂ (.array (.array .nat))}
    (hM : ⟨.nat, M₁, M₂⟩ ∈ Γ) (hV : ⟨.list .nat, V₁, V₂⟩ ∈ Γ)
    (hVA : ⟨.array .nat, VA₁, VA₂⟩ ∈ Γ) (hW : ⟨.array .nat, W₁, W₂⟩ ∈ Γ)
    (hpw : ⟨.array (.array .nat), pw₁, pw₂⟩ ∈ Γ) (hrk : ⟨.list .nat, rk₁, rk₂⟩ ∈ Γ)
    (hrm : ⟨.list .nat, rm₁, rm₂⟩ ∈ Γ) (ht : ⟨.nat, t₁, t₂⟩ ∈ Γ)
    (hz : ⟨.list .nat, z₁, z₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (cjOutcome3Prog M₁ V₁ VA₁ W₁ pw₁ rk₁ rm₁ t₁ z₁)
      (cjOutcome3Prog M₂ V₂ VA₂ W₂ pw₂ rk₂ rm₂ t₂ z₂) := by
  unfold cjOutcome3Prog
  exact .bind (wf_c3ClsProg hVA hW hpw hrk hrm ht hz) fun _ _ =>
    .bind (wf_q3Prog (by simp [hM]) (by simp [hV]) (by simp)) fun _ _ =>
    .bind (Case3.wf_outcomeProg (by simp [hM]) (by simp [hV]) (by simp [hVA]) (by simp [hW])
      (by simp [hpw]) (by simp [hrk]) (by simp [hrm]) (by simp [ht]) (by simp [hz])) fun _ _ =>
    Align.wf_joFlatMap (by simp) fun _ hΓ _ _ ho => wf_cjOfProg (hΓ (by simp)) ho

theorem wf_cjStructs3Prog {S : Signature} {M₁ k₁ : var₁ .nat} {M₂ k₂ : var₂ .nat}
    {V₁ : var₁ (.list .nat)} {V₂ : var₂ (.list .nat)} {col₁ : var₁ (.array .nat)}
    {col₂ : var₂ (.array .nat)} (hM : ⟨.nat, M₁, M₂⟩ ∈ Γ) (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ)
    (hV : ⟨.list .nat, V₁, V₂⟩ ∈ Γ) (hcol : ⟨.array .nat, col₁, col₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (cjStructs3Prog M₁ k₁ V₁ col₁)
      (cjStructs3Prog M₂ k₂ V₂ col₂) := by
  unfold cjStructs3Prog
  exact .bind (.prim _ (.cons hV .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp [hV]) .nil)) fun _ _ =>
    .bind (Case3.wf_wlCProg (by simp [hk]) (by simp) (by simp [hcol])) fun _ _ =>
    .bind (.prim _ (.cons (by simp [hk]) .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (Coherent.wf_pwTabProg (by simp) (by simp) (by simp)) fun _ _ =>
    .bind (Case3.wf_tOfProg (by simp)) fun _ _ =>
    .bind (wf_goodListProg (by simp) (by simp [hk]) (by simp) (by simp)) fun _ _ =>
    Align.wf_joFlatMap (by simp) fun _ hΓ _ _ hz =>
      wf_cjOutcome3Prog (hΓ (by simp [hM])) (hΓ (by simp [hV])) (hΓ (by simp)) (hΓ (by simp))
        (hΓ (by simp)) (hΓ (by simp)) (hΓ (by simp)) (hΓ (by simp)) hz

theorem wf_c3FirstClsProg {S : Signature} {k₁ : var₁ .nat} {k₂ : var₂ .nat}
    {V₁ : var₁ (.list .nat)} {V₂ : var₂ (.list .nat)} {col₁ : var₁ (.array .nat)}
    {col₂ : var₂ (.array .nat)} (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ) (hV : ⟨.list .nat, V₁, V₂⟩ ∈ Γ)
    (hcol : ⟨.array .nat, col₁, col₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (c3FirstClsProg k₁ V₁ col₁) (c3FirstClsProg k₂ V₂ col₂) := by
  unfold c3FirstClsProg
  exact .bind (.prim _ (.cons hV .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp [hV]) .nil)) fun _ _ =>
    .bind (Case3.wf_wlCProg (by simp [hk]) (by simp) (by simp [hcol])) fun _ _ =>
    .bind (.prim _ (.cons (by simp [hk]) .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (Coherent.wf_pwTabProg (by simp) (by simp) (by simp)) fun _ _ =>
    .bind (Case3.wf_tOfProg (by simp)) fun _ _ =>
    .bind (wf_goodListProg (by simp) (by simp [hk]) (by simp) (by simp)) fun _ _ =>
    .bind (.caseList (by simp) (.prim _ .nil) fun _ _ _ _ => .ret (by simp)) fun _ _ =>
    wf_c3ClsProg (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)

theorem wf_c2bJTestProg {n₁ : var₁ .nat} {n₂ : var₂ .nat} {Fx₁ : var₁ (Ty.group D)}
    {Fx₂ : var₂ (Ty.group D)} {Φx₁ : var₁ (.list .nat)} {Φx₂ : var₂ (.list .nat)}
    (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (hFx : ⟨Ty.group D, Fx₁, Fx₂⟩ ∈ Γ)
    (hΦx : ⟨.list .nat, Φx₁, Φx₂⟩ ∈ Γ) :
    Prog.Wf (S := groupSig D) (rec := rec) r Γ (c2bJTestProg n₁ Fx₁ Φx₁)
      (c2bJTestProg n₂ Fx₂ Φx₂) := by
  unfold c2bJTestProg
  refine .bind (.prim _ (.cons hFx .nil)) fun _ _ => ?_
  refine .bind (Case2b.wf_degProg (by simp) (by simp [hn]) (by simp [hFx]) (by simp [hΦx]))
    fun _ _ => ?_
  refine .bind (.prim _ .nil) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ => ?_
  refine .bind (wf_firstLeafProg (by simp) (by simp [hn]) (by simp [hFx]) (by simp [hΦx])
    (by simp)) fun _ _ => ?_
  refine .caseOption (by simp) (.prim _ .nil) fun _ _ => ?_
  prog_wf

theorem wf_c2bCJProg {sub₁ : var₁ (hinstTy D) → Prog (groupSig D) rec var₁ (Ty.answer D)}
    {sub₂ : var₂ (hinstTy D) → Prog (groupSig D) rec var₂ (Ty.answer D)}
    (hsub : WfFun r Γ sub₁ sub₂) {n₀₁ n₁ : var₁ .nat} {n₀₂ n₂ : var₂ .nat}
    {L₁ : var₁ (.array (.list .nat))} {L₂ : var₂ (.array (.list .nat))}
    {xy₁ : var₁ Ty.strs} {xy₂ : var₂ Ty.strs} {w₁ : var₁ Ty.win} {w₂ : var₂ Ty.win}
    {G₁ Fx₁ Fy₁ : var₁ (Ty.group D)} {G₂ Fx₂ Fy₂ : var₂ (Ty.group D)}
    {Φx₁ Φy₁ : var₁ (.list .nat)} {Φx₂ Φy₂ : var₂ (.list .nat)}
    (hn₀ : ⟨.nat, n₀₁, n₀₂⟩ ∈ Γ) (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ)
    (hL : ⟨.array (.list .nat), L₁, L₂⟩ ∈ Γ) (hxy : ⟨Ty.strs, xy₁, xy₂⟩ ∈ Γ)
    (hw : ⟨Ty.win, w₁, w₂⟩ ∈ Γ) (hG : ⟨Ty.group D, G₁, G₂⟩ ∈ Γ)
    (hFx : ⟨Ty.group D, Fx₁, Fx₂⟩ ∈ Γ) (hFy : ⟨Ty.group D, Fy₁, Fy₂⟩ ∈ Γ)
    (hΦx : ⟨.list .nat, Φx₁, Φx₂⟩ ∈ Γ) (hΦy : ⟨.list .nat, Φy₁, Φy₂⟩ ∈ Γ) :
    Prog.Wf r Γ (c2bCJProg sub₁ n₀₁ n₁ L₁ xy₁ w₁ G₁ Fx₁ Fy₁ Φx₁ Φy₁)
      (c2bCJProg sub₂ n₀₂ n₂ L₂ xy₂ w₂ G₂ Fx₂ Fy₂ Φx₂ Φy₂) := by
  unfold c2bCJProg
  refine .bind (.prim _ (.cons hG .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) (.cons (by simp [hn]) .nil))) fun _ _ => ?_
  refine .bind (Case2b.wf_degProg (by simp) (by simp [hn]) (by simp [hFx]) (by simp [hΦx]))
    fun _ _ => ?_
  refine .bind (Case2b.wf_degProg (by simp) (by simp [hn]) (by simp [hFy]) (by simp [hΦy]))
    fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ => ?_
  refine .ite (by simp) ?_ (.prim _ .nil)
  refine .bind (.prim _ .nil) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ => ?_
  refine .bind (wf_firstLeafProg (by simp) (by simp [hn]) (by simp [hFx]) (by simp [hΦx])
    (by simp)) fun _ _ => ?_
  refine .caseOption (by simp) (.prim _ .nil) fun _ _ => ?_
  refine .bind (wf_firstTupleProg (by simp [hΦx]) (by simp)) fun _ _ => ?_
  refine .bind (wf_q2bProg (by simp) (by simp [hΦx]) (by simp)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ => ?_
  refine .bind (wf_cjLeaves2bProg (by simp) (by simp [hn]) (by simp [hFy]) (by simp [hΦy])
    (by simp)) fun _ _ => ?_
  refine .bind (.prim _ .nil) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ => ?_
  exact Align.wf_alignProg
    (wf_rdBranch (hsub.mono fun z hz => by simp [hz]) (by simp [hn₀]) (by simp [hn])
      (by simp [hL]) (by simp))
    (fun Γ' hΓ' z₁ z₂ hz => wf_cjohnGensProg (hΓ' (by simp)) hz)
    (fun Γ' hΓ' z₁ z₂ y₁ y₂ hz hy => wf_cjohnIsoProg (hΓ' (by simp)) hz hy)
    (by simp [hn]) (by simp [hxy]) (by simp [hw]) (by simp [hG]) (by simp) (by simp)

theorem wf_m5Case2bCJProg {sub₁ : var₁ (hinstTy D) → Prog (groupSig D) rec var₁ (Ty.answer D)}
    {sub₂ : var₂ (hinstTy D) → Prog (groupSig D) rec var₂ (Ty.answer D)}
    (hsub : WfFun r Γ sub₁ sub₂) {n₀₁ n₁ : var₁ .nat} {n₀₂ n₂ : var₂ .nat}
    {L₁ : var₁ (.array (.list .nat))} {L₂ : var₂ (.array (.list .nat))} {st₁ : var₁ stTy}
    {st₂ : var₂ stTy} {xy₁ : var₁ Ty.strs} {xy₂ : var₂ Ty.strs} {w₁ : var₁ Ty.win}
    {w₂ : var₂ Ty.win} {G₁ Fx₁ Fy₁ : var₁ (Ty.group D)} {G₂ Fx₂ Fy₂ : var₂ (Ty.group D)}
    {Φx₁ Φy₁ : var₁ (.list .nat)} {Φx₂ Φy₂ : var₂ (.list .nat)}
    (hn₀ : ⟨.nat, n₀₁, n₀₂⟩ ∈ Γ) (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ)
    (hL : ⟨.array (.list .nat), L₁, L₂⟩ ∈ Γ) (hst : ⟨stTy, st₁, st₂⟩ ∈ Γ)
    (hxy : ⟨Ty.strs, xy₁, xy₂⟩ ∈ Γ) (hw : ⟨Ty.win, w₁, w₂⟩ ∈ Γ)
    (hG : ⟨Ty.group D, G₁, G₂⟩ ∈ Γ) (hFx : ⟨Ty.group D, Fx₁, Fx₂⟩ ∈ Γ)
    (hFy : ⟨Ty.group D, Fy₁, Fy₂⟩ ∈ Γ) (hΦx : ⟨.list .nat, Φx₁, Φx₂⟩ ∈ Γ)
    (hΦy : ⟨.list .nat, Φy₁, Φy₂⟩ ∈ Γ) :
    Prog.Wf r Γ (m5Case2bCJProg sub₁ n₀₁ n₁ L₁ st₁ xy₁ w₁ G₁ Fx₁ Fy₁ Φx₁ Φy₁)
      (m5Case2bCJProg sub₂ n₀₂ n₂ L₂ st₂ xy₂ w₂ G₂ Fx₂ Fy₂ Φx₂ Φy₂) := by
  unfold m5Case2bCJProg
  refine .bind (wf_c2bJTestProg hn hFx hΦx) fun _ _ => ?_
  refine .ite (by simp) ?_ ?_
  · exact wf_c2bCJProg (hsub.mono fun z hz => by simp [hz]) (by simp [hn₀]) (by simp [hn])
      (by simp [hL]) (by simp [hxy]) (by simp [hw]) (by simp [hG]) (by simp [hFx])
      (by simp [hFy]) (by simp [hΦx]) (by simp [hΦy])
  · exact wf_m5Case2bProg (hsub.mono fun z hz => by simp [hz]) (by simp [hn₀]) (by simp [hn])
      (by simp [hL]) (by simp [hst]) (by simp [hxy]) (by simp [hw]) (by simp [hG])
      (by simp [hFx]) (by simp [hFy]) (by simp [hΦx]) (by simp [hΦy])

theorem wf_c3CJRouteProg {sub₁ : var₁ (hinstTy D) → Prog (groupSig D) rec var₁ (Ty.answer D)}
    {sub₂ : var₂ (hinstTy D) → Prog (groupSig D) rec var₂ (Ty.answer D)}
    (hsub : WfFun r Γ sub₁ sub₂) {n₀₁ n₁ k₁ : var₁ .nat} {n₀₂ n₂ k₂ : var₂ .nat}
    {L₁ : var₁ (.array (.list .nat))} {L₂ : var₂ (.array (.list .nat))}
    {xy₁ : var₁ Ty.strs} {xy₂ : var₂ Ty.strs} {w₁ : var₁ Ty.win} {w₂ : var₂ Ty.win}
    {G₁ : var₁ (Ty.group D)} {G₂ : var₂ (Ty.group D)} {Vx₁ Vy₁ : var₁ (.list .nat)}
    {Vx₂ Vy₂ : var₂ (.list .nat)} {cX₁ cY₁ : var₁ (.array .nat)} {cX₂ cY₂ : var₂ (.array .nat)}
    {X₁ : var₁ outTy} {X₂ : var₂ outTy}
    (hn₀ : ⟨.nat, n₀₁, n₀₂⟩ ∈ Γ) (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ)
    (hL : ⟨.array (.list .nat), L₁, L₂⟩ ∈ Γ) (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ)
    (hxy : ⟨Ty.strs, xy₁, xy₂⟩ ∈ Γ) (hw : ⟨Ty.win, w₁, w₂⟩ ∈ Γ)
    (hG : ⟨Ty.group D, G₁, G₂⟩ ∈ Γ) (hVx : ⟨.list .nat, Vx₁, Vx₂⟩ ∈ Γ)
    (hVy : ⟨.list .nat, Vy₁, Vy₂⟩ ∈ Γ) (hcX : ⟨.array .nat, cX₁, cX₂⟩ ∈ Γ)
    (hcY : ⟨.array .nat, cY₁, cY₂⟩ ∈ Γ) (hX : ⟨outTy, X₁, X₂⟩ ∈ Γ) :
    Prog.Wf r Γ (c3CJRouteProg sub₁ n₀₁ n₁ L₁ k₁ xy₁ w₁ G₁ Vx₁ Vy₁ cX₁ cY₁ X₁)
      (c3CJRouteProg sub₂ n₀₂ n₂ L₂ k₂ xy₂ w₂ G₂ Vx₂ Vy₂ cX₂ cY₂ X₂) := by
  unfold c3CJRouteProg
  refine .bind (.prim _ (.cons hG .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) (.cons (by simp [hn]) .nil))) fun _ _ => ?_
  refine .bind (wf_c3FirstClsProg (by simp [hk]) (by simp [hVx]) (by simp [hcX])) fun _ _ => ?_
  refine .bind (wf_q3Prog (by simp) (by simp [hVx]) (by simp)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp [hX]) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ => ?_
  refine .bind (wf_cjStructs3Prog (by simp) (by simp [hk]) (by simp [hVy]) (by simp [hcY]))
    fun _ _ => ?_
  refine .bind (.prim _ .nil) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ => ?_
  exact Align.wf_alignProg
    (wf_rdBranch (hsub.mono fun z hz => by simp [hz]) (by simp [hn₀]) (by simp [hn])
      (by simp [hL]) (by simp))
    (fun Γ' hΓ' z₁ z₂ hz => wf_cjohnGensProg (hΓ' (by simp)) hz)
    (fun Γ' hΓ' z₁ z₂ y₁ y₂ hz hy => wf_cjohnIsoProg (hΓ' (by simp)) hz hy)
    (by simp [hn]) (by simp [hxy]) (by simp [hw]) (by simp [hG]) (by simp) (by simp)

theorem wf_m5Case3CJProg {sub₁ : var₁ (hinstTy D) → Prog (groupSig D) rec var₁ (Ty.answer D)}
    {sub₂ : var₂ (hinstTy D) → Prog (groupSig D) rec var₂ (Ty.answer D)}
    (hsub : WfFun r Γ sub₁ sub₂) {I₁ : var₁ (hinstTy D)} {I₂ : var₂ (hinstTy D)}
    {n₀₁ n₁ k₁ : var₁ .nat} {n₀₂ n₂ k₂ : var₂ .nat}
    {L₁ : var₁ (.array (.list .nat))} {L₂ : var₂ (.array (.list .nat))} {st₁ : var₁ stTy}
    {st₂ : var₂ stTy} {xy₁ : var₁ Ty.strs} {xy₂ : var₂ Ty.strs} {w₁ : var₁ Ty.win}
    {w₂ : var₂ Ty.win} {G₁ : var₁ (Ty.group D)} {G₂ : var₂ (Ty.group D)}
    {Vx₁ Vy₁ : var₁ (.list .nat)} {Vx₂ Vy₂ : var₂ (.list .nat)}
    (hI : ⟨hinstTy D, I₁, I₂⟩ ∈ Γ) (hn₀ : ⟨.nat, n₀₁, n₀₂⟩ ∈ Γ) (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ)
    (hL : ⟨.array (.list .nat), L₁, L₂⟩ ∈ Γ) (hst : ⟨stTy, st₁, st₂⟩ ∈ Γ)
    (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ) (hxy : ⟨Ty.strs, xy₁, xy₂⟩ ∈ Γ) (hw : ⟨Ty.win, w₁, w₂⟩ ∈ Γ)
    (hG : ⟨Ty.group D, G₁, G₂⟩ ∈ Γ) (hVx : ⟨.list .nat, Vx₁, Vx₂⟩ ∈ Γ)
    (hVy : ⟨.list .nat, Vy₁, Vy₂⟩ ∈ Γ) :
    Prog.Wf r Γ (m5Case3CJProg sub₁ I₁ n₀₁ n₁ L₁ st₁ k₁ xy₁ w₁ G₁ Vx₁ Vy₁)
      (m5Case3CJProg sub₂ I₂ n₀₂ n₂ L₂ st₂ k₂ xy₂ w₂ G₂ Vx₂ Vy₂) := by
  have hold : ∀ Γ' : WfCtx var₁ var₂, Γ ⊆ Γ' →
      Prog.Wf r Γ' (m5Case3Prog sub₁ I₁ n₀₁ n₁ L₁ st₁ k₁ xy₁ w₁ G₁ Vx₁ Vy₁)
        (m5Case3Prog sub₂ I₂ n₀₂ n₂ L₂ st₂ k₂ xy₂ w₂ G₂ Vx₂ Vy₂) := fun Γ' hΓ' =>
    wf_m5Case3Prog (hsub.mono hΓ') (hΓ' hI) (hΓ' hn₀) (hΓ' hn) (hΓ' hL) (hΓ' hst) (hΓ' hk)
      (hΓ' hxy) (hΓ' hw) (hΓ' hG) (hΓ' hVx) (hΓ' hVy)
  unfold m5Case3CJProg
  refine .bind (.prim _ (.cons hw .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp [hG]) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) (.cons (by simp [hn]) .nil))) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp [hVx]) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp [hVy]) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ => ?_
  refine .ite (by simp) ?_ (.prim _ .nil)
  refine .bind (.prim _ (.cons (by simp [hxy]) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp [hxy]) .nil)) fun _ _ => ?_
  refine .bind (Case3.wf_tupleColProg
    (wf_c3Sub (hsub.mono fun z hz => by simp [hz]) (by simp [hn₀]) (by simp [hn])
      (by simp [hL]) (by simp [hst]) (by simp)) (by simp [hn]) (by simp) (by simp [hk])
    (by simp [hVx]) (by simp [hVy]) (by simp) (by simp) (by simp [hG])) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (Case3.wf_twinsFlagProg (by simp [hk]) (by simp) (by simp)) fun _ _ => ?_
  refine .ite (by simp) (hold _ fun y hy => by simp [hy]) ?_
  refine .bind (Case3.wf_firstStructProg (by simp) (by simp [hk]) (by simp [hVx]) (by simp))
    fun _ _ => ?_
  refine .caseOption (by simp) (hold _ fun y hy => by simp [hy]) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (.prim _ .nil) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ => ?_
  refine .ite (by simp) ?_ (hold _ fun y hy => by simp [hy])
  exact wf_c3CJRouteProg (hsub.mono fun z hz => by simp [hz]) (by simp [hn₀]) (by simp [hn])
    (by simp [hL]) (by simp [hk]) (by simp [hxy]) (by simp [hw]) (by simp [hG]) (by simp [hVx])
    (by simp [hVy]) (by simp) (by simp) (by simp)

theorem wf_m5DispatchCJ {sub₁ : var₁ (hinstTy D) → Prog (groupSig D) rec var₁ (Ty.answer D)}
    {sub₂ : var₂ (hinstTy D) → Prog (groupSig D) rec var₂ (Ty.answer D)}
    (hsub : WfFun r Γ sub₁ sub₂) {I₁ : var₁ (hinstTy D)} {I₂ : var₂ (hinstTy D)}
    {n₀₁ n₁ k₁ : var₁ .nat} {n₀₂ n₂ k₂ : var₂ .nat}
    {L₁ : var₁ (.array (.list .nat))} {L₂ : var₂ (.array (.list .nat))} {st₁ : var₁ stTy}
    {st₂ : var₂ stTy} {xy₁ : var₁ Ty.strs} {xy₂ : var₂ Ty.strs} {w₁ : var₁ Ty.win}
    {w₂ : var₂ Ty.win} {G₁ Fx₁ Fy₁ : var₁ (Ty.group D)} {G₂ Fx₂ Fy₂ : var₂ (Ty.group D)}
    {cx₁ cy₁ : var₁ m5CaseTy} {cx₂ cy₂ : var₂ m5CaseTy}
    (hI : ⟨hinstTy D, I₁, I₂⟩ ∈ Γ) (hn₀ : ⟨.nat, n₀₁, n₀₂⟩ ∈ Γ) (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ)
    (hL : ⟨.array (.list .nat), L₁, L₂⟩ ∈ Γ) (hst : ⟨stTy, st₁, st₂⟩ ∈ Γ)
    (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ) (hxy : ⟨Ty.strs, xy₁, xy₂⟩ ∈ Γ) (hw : ⟨Ty.win, w₁, w₂⟩ ∈ Γ)
    (hG : ⟨Ty.group D, G₁, G₂⟩ ∈ Γ) (hFx : ⟨Ty.group D, Fx₁, Fx₂⟩ ∈ Γ)
    (hFy : ⟨Ty.group D, Fy₁, Fy₂⟩ ∈ Γ) (hcx : ⟨m5CaseTy, cx₁, cx₂⟩ ∈ Γ)
    (hcy : ⟨m5CaseTy, cy₁, cy₂⟩ ∈ Γ) :
    Prog.Wf r Γ (m5DispatchCJ sub₁ I₁ n₀₁ n₁ L₁ st₁ k₁ xy₁ w₁ G₁ Fx₁ Fy₁ cx₁ cy₁)
      (m5DispatchCJ sub₂ I₂ n₀₂ n₂ L₂ st₂ k₂ xy₂ w₂ G₂ Fx₂ Fy₂ cx₂ cy₂) := by
  unfold m5DispatchCJ
  refine .bind (.prim _ (.cons hcx .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by m5_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by m5_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by m5_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by m5_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by m5_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by m5_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by m5_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by m5_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by m5_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by m5_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by m5_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ .nil) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by m5_mem) (.cons (List.Mem.head _) .nil))) fun _ _ => ?_
  refine .ite (List.Mem.head _) ?_ ?_
  · exact wf_m5Case1Prog (hsub.mono fun y hy => by m5_mem) (by m5_mem) (by m5_mem) (by m5_mem)
      (by m5_mem) (by m5_mem) (by m5_mem) (by m5_mem) (by m5_mem) (by m5_mem)
  refine .bind (.prim _ .nil) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by m5_mem) (.cons (List.Mem.head _) .nil))) fun _ _ => ?_
  refine .ite (List.Mem.head _) ?_ ?_
  · refine .bind (.prim _ (.cons (by m5_mem) (.cons (by m5_mem) .nil))) fun _ _ => ?_
    refine .bind (.prim _ (.cons (by m5_mem) (.cons (by m5_mem) .nil))) fun _ _ => ?_
    refine .bind (.prim _ (.cons (by m5_mem) .nil)) fun _ _ => ?_
    refine .bind (.prim _ (.cons (by m5_mem) .nil)) fun _ _ => ?_
    refine .bind (.prim _ (.cons (by m5_mem) (.cons (List.Mem.head _) .nil))) fun _ _ => ?_
    refine .bind (.prim _ (.cons (by m5_mem) (.cons (List.Mem.head _) .nil))) fun _ _ => ?_
    refine .bind (.prim _ (.cons (by m5_mem) (.cons (List.Mem.head _) .nil))) fun _ _ => ?_
    refine .ite (List.Mem.head _) (.ite (by m5_mem) ?_ ?_) (.prim _ .nil)
    · refine .bind (.prim _ (.cons (by m5_mem) .nil)) fun _ _ => ?_
      refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
      exact wf_m5Case2aProg (hsub.mono fun y hy => by m5_mem) (by m5_mem) (by m5_mem)
        (by m5_mem) (by m5_mem) (by m5_mem) (by m5_mem) (by m5_mem) (List.Mem.head _)
    · exact wf_m5Case2bCJProg (hsub.mono fun y hy => by m5_mem) (by m5_mem) (by m5_mem)
        (by m5_mem) (by m5_mem) (by m5_mem) (by m5_mem) (by m5_mem) (by m5_mem) (by m5_mem)
        (by m5_mem) (by m5_mem)
  · refine .bind (wf_fixPtsProg (by m5_mem)) fun _ _ => ?_
    refine .bind (wf_fixPtsProg (by m5_mem)) fun _ _ => ?_
    exact wf_m5Case3CJProg (hsub.mono fun y hy => by m5_mem) (by m5_mem) (by m5_mem)
      (by m5_mem) (by m5_mem) (by m5_mem) (by m5_mem) (by m5_mem) (by m5_mem) (by m5_mem)
      (List.Mem.tail _ (List.Mem.head _)) (List.Mem.head _)

theorem wf_m5CoreCJProg {sub₁ : var₁ (hinstTy D) → Prog (groupSig D) rec var₁ (Ty.answer D)}
    {sub₂ : var₂ (hinstTy D) → Prog (groupSig D) rec var₂ (Ty.answer D)}
    (hsub : WfFun r Γ sub₁ sub₂) {I₁ : var₁ (hinstTy D)} {I₂ : var₂ (hinstTy D)}
    {k₁ : var₁ .nat} {k₂ : var₂ .nat} {st₁ : var₁ stTy} {st₂ : var₂ stTy}
    (hI : ⟨hinstTy D, I₁, I₂⟩ ∈ Γ) (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ) (hst : ⟨stTy, st₁, st₂⟩ ∈ Γ) :
    Prog.Wf r Γ (m5CoreCJProg sub₁ I₁ k₁ st₁) (m5CoreCJProg sub₂ I₂ k₂ st₂) := by
  unfold m5CoreCJProg
  refine .bind (.prim _ (.cons hI .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by m5_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by m5_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by m5_mem) .nil)) fun _ _ => ?_
  refine .caseOption (List.Mem.head _) (.prim _ .nil) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by m5_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by m5_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by m5_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by m5_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by m5_mem) .nil)) fun _ _ => ?_
  refine .bind (wf_m5CertProg (hsub.mono fun y hy => by m5_mem) (by m5_mem) (by m5_mem)
    (by m5_mem) (by m5_mem) (by m5_mem) (by m5_mem)) fun _ _ => ?_
  refine .bind (wf_m5CertProg (hsub.mono fun y hy => by m5_mem) (by m5_mem) (by m5_mem)
    (by m5_mem) (by m5_mem) (by m5_mem) (by m5_mem)) fun _ _ => ?_
  refine .bind (wf_m5CaseProg (by m5_mem) (by m5_mem) (by m5_mem)) fun _ _ => ?_
  refine .bind (wf_m5CaseProg (by m5_mem) (by m5_mem) (by m5_mem)) fun _ _ => ?_
  exact wf_m5DispatchCJ (hsub.mono fun y hy => by m5_mem) (by m5_mem) (by m5_mem) (by m5_mem)
    (by m5_mem) (by m5_mem) (by m5_mem) (by m5_mem) (by m5_mem) (by m5_mem) (by m5_mem)
    (by m5_mem) (List.Mem.tail _ (List.Mem.head _)) (List.Mem.head _)

theorem wf_m5StepCJProg {sub₁ : var₁ (hinstTy D) → Prog (groupSig D) rec var₁ (Ty.answer D)}
    {sub₂ : var₂ (hinstTy D) → Prog (groupSig D) rec var₂ (Ty.answer D)}
    (hsub : WfFun r Γ sub₁ sub₂) {I₁ : var₁ (hinstTy D)} {I₂ : var₂ (hinstTy D)}
    {L₁ : var₁ (.array (.list .nat))} {L₂ : var₂ (.array (.list .nat))}
    {k₁ : var₁ .nat} {k₂ : var₂ .nat} {st₁ : var₁ stTy} {st₂ : var₂ stTy}
    (hI : ⟨hinstTy D, I₁, I₂⟩ ∈ Γ) (hL : ⟨.array (.list .nat), L₁, L₂⟩ ∈ Γ)
    (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ) (hst : ⟨stTy, st₁, st₂⟩ ∈ Γ) :
    Prog.Wf r Γ (m5StepCJProg sub₁ I₁ L₁ k₁ st₁) (m5StepCJProg sub₂ I₂ L₂ k₂ st₂) := by
  unfold m5StepCJProg
  exact wf_restrictBaseProg (fun Γ' hΓ x₁ x₂ hx =>
    wf_m5CoreCJProg (hsub.mono hΓ) hx (hΓ hk) (hΓ hst)) hI hL

end Wf

end GraphIso.Main
