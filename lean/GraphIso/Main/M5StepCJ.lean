module

public import GraphIso.Main.M5Case3CJ
public import GraphIso.Main.M5CasesNs
public import GraphIso.Main.M5Step

/-!
# M5 with coloured Johnson alignment: the dispatcher, M5 on the restricted instance, the step

Stage 14j-4b, item 4 (`PLAN-14.md` §14.5). The variants of 14j-4's `m5Dispatch`, `m5CoreProg`
and `m5StepProg` with Cases 2b and 3 replaced by `m5Case2bCJProg` and `m5Case3CJProg`.

* `RunsWithin.m5DispatchCJ`, `RunsWithin.m5CoreCJProg`, `RunsWithin.m5StepCJProg`: under 14j-4's
  hypotheses (as stated there) and those of the Johnson routes (`RDOrbit` at `st = (2, X₀)`, the
  align charges `Bg1J₂`, `Bg1J₃`, the bound `uB` on the union cells, `Lg` large enough for the
  numbers of candidates): the answer is correct; the children are `StepChild |W| m` with factor
  `m5CFCJ`; the sub-calls without a hint are counted (`m5CKCJ`, Case 3's colourings twice, and
  `m5CH`); the work is `m5WCJ` (`m5CoreWorkCJ`). At the level of the cases
  (`RunsWithin.m5Case2bCJProg`, `RunsWithin.m5Case3CJProg`) the partition routes' hypotheses are
  needed only for a first leaf or structure that is not a Johnson one.
* **No stuck orbit** (`RunsWithin.m5DispatchCJ_ns`, `RunsWithin.m5CoreCJProg_ns`): in every
  case except a partition leaf of Case 2b or a partition structure of Case 3, which keep 14j-4's
  hypothesis (a colored `t`-partition with `4t ≤ 3m`), and with no twins in Case 3 as in 14j-4.
  The factor is `m5CFnsCJ`: `m` or `max(m, uB!)` per candidate, with no `m!`.
* **Case 2b's counts for `y` only in Case 2b** (stage 14j-6b-1, `PLAN-14.md` §14.11 item 5):
  `RunsWithin.m5DispatchCJ_ns_jpC` and `RunsWithin.m5CoreCJProg_ns_jpC` assume `hBgen₂ᵦ` and
  `hLY₂` only for a full group of `y` in Case 2b, where they are used; in Case 2a `y`'s degree
  may be close to `|Φ|`. `RunsWithin.m5DispatchCJ_ns_jp` and `RunsWithin.m5CoreCJProg_ns_jp`
  follow.
-/

@[expose] public section

namespace GraphIso.Main

open Equiv MulAction Pointwise Cost GraphIso GraphIso.Programs GraphIso.Toolkit
  GraphIso.Recursion GraphIso.SplitJohnson GraphIso.Solver GraphIso.Align GraphIso.Certificates
  GraphIso.CertProg

/-! ### The programs -/

section Programs

variable {D : Ty} {rec : Ty × Ty} {var : Ty → Type}

/-- **The dispatch of M5 with coloured Johnson alignment**: `m5Dispatch` with Cases 2b and 3
replaced by `m5Case2bCJProg` and `m5Case3CJProg`. -/
def m5DispatchCJ (sub : var (hinstTy D) → Prog (groupSig D) rec var (Ty.answer D))
    (I : var (hinstTy D)) (n₀ n : var .nat) (L : var (.array (.list .nat))) (st : var stTy)
    (k : var .nat) (xy : var Ty.strs) (w : var Ty.win) (G Fx Fy : var (Ty.group D))
    (cx cy : var m5CaseTy) : Prog (groupSig D) rec var (Ty.answer D) :=
  .bind (.op1 .fst cx) fun rx => .bind (.op1 .snd cx) fun ax =>
  .bind (.op1 .fst rx) fun csx => .bind (.op1 .snd rx) fun bosx =>
  .bind (.op1 .fst csx) fun tag => .bind (.op1 .snd csx) fun Φx =>
  .bind (.op1 .fst cy) fun ry => .bind (.op1 .snd cy) fun ay =>
  .bind (.op1 .fst ry) fun csy => .bind (.op1 .snd ry) fun bosy =>
  .bind (.op1 .fst csy) fun tagy => .bind (.op1 .snd csy) fun Φy =>
  .bind (.op0 (.natLit 1)) fun one => .bind (.op2 .natEq tag one) fun is1 =>
  .ite is1 (m5Case1Prog sub n₀ n L st xy w G Fx Fy)
    (.bind (.op0 (.natLit 2)) fun two => .bind (.op2 .natEq tag two) fun is2 =>
      .ite is2
        (.bind (.op2 .natEq tagy two) fun y2 =>
          .bind (.op2 .and ax ay) fun both => .bind (.op1 .not ax) fun nx =>
          .bind (.op1 .not ay) fun ny => .bind (.op2 .and nx ny) fun neither =>
          .bind (.op2 .or both neither) fun same => .bind (.op2 .and y2 same) fun ok =>
          .ite ok
            (.ite ax
              (.bind (.op1 .snd Fx) fun fd => .bind (.op1 .fst fd) fun fgs =>
                m5Case2aProg sub n₀ n xy w G Φx Φy fgs)
              (m5Case2bCJProg sub n₀ n L st xy w G Fx Fy Φx Φy))
            (.op0 .none))
        (.bind (fixPtsProg bosx) fun Vx => .bind (fixPtsProg bosy) fun Vy =>
          m5Case3CJProg sub I n₀ n L st k xy w G Vx Vy))


/-- **M5 on the restricted instance with coloured Johnson alignment**: `m5CoreProg` with the
dispatch `m5DispatchCJ`. -/
def m5CoreCJProg (sub : var (hinstTy D) → Prog (groupSig D) rec var (Ty.answer D))
    (I : var (hinstTy D)) (k : var .nat) (st : var stTy) :
    Prog (groupSig D) rec var (Ty.answer D) :=
  .bind (.op1 .fst I) fun J => .bind (.op1 .snd I) fun r₁ => .bind (.op1 .fst r₁) fun n₀ =>
  .bind (.op1 .snd r₁) fun r₂ => .bind (.op1 .fst r₂) fun n => .bind (.op1 .snd r₂) fun lab =>
  .caseOption lab (.op0 .none) fun L =>
  .bind (.op1 .fst J) fun xy => .bind (.op1 .snd J) fun wc => .bind (.op1 .fst wc) fun w =>
  .bind (.op1 .snd wc) fun c => .bind (.op1 .snd c) fun G => .bind (.op1 .fst G) fun N =>
  .bind (.op1 .fst xy) fun x => .bind (.op1 .snd xy) fun y =>
  .bind (m5CertProg sub n₀ n N k x G) fun Fx => .bind (m5CertProg sub n₀ n N k y G) fun Fy =>
  .bind (m5CaseProg n N Fx) fun cx => .bind (m5CaseProg n N Fy) fun cy =>
  m5DispatchCJ sub I n₀ n L st k xy w G Fx Fy cx cy

/-- **The step of M5 with coloured Johnson alignment**: the restriction to the window and the
base, with `m5CoreCJProg` as its continuation. -/
def m5StepCJProg (sub : var (hinstTy D) → Prog (groupSig D) rec var (Ty.answer D))
    (I : var (hinstTy D)) (L : var (.array (.list .nat))) (k : var .nat) (st : var stTy) :
    Prog (groupSig D) rec var (Ty.answer D) :=
  restrictBaseProg (fun I' => m5CoreCJProg sub I' k st) I L

end Programs


section DispatchRunCJ

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b}
  {sub : HInstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)}
  {I : HInstData D} {n₀ n k : ℕ} {L : LabelData} {st : ℕ × CJData} {xy : StrData × StrData}
  {w : WinData} {G Fx Fy : GroupData D.denote}
  {cx cy : ((ℕ × List ℕ) × List (List ℕ)) × Bool} {ans : AnswerData D} {c : ℕ}

/-- The dispatch in Case 1. -/
theorem m5Dispatch_run1_cj (h1 : cx.1.1.1 = 1)
    (h : RunsWithin X body (Main.m5Case1Prog sub n₀ n L st xy w G Fx Fy) ans c) :
    RunsWithin X body (Main.m5DispatchCJ sub I n₀ n L st k xy w G Fx Fy cx cy) ans (c + 16) := by
  have he : (cx.1.1.1 == 1) = true := by simp [h1]
  apply RunsWithin.mono
  case h =>
    unfold Main.m5DispatchCJ
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
    run_step (RunsWithin.prim _ _)
    simp only [Prim.eval, he]
    exact RunsWithin.ite_true h
  case hc =>
    simp only [Prim.cost]
    omega

/-- The dispatch in Case 3. -/
theorem m5Dispatch_run3_cj (h1 : cx.1.1.1 ≠ 1) (h2 : cx.1.1.1 ≠ 2) {m : ℕ}
    (hbx : cx.1.2.length ≤ m) (hox : ∀ o ∈ cx.1.2, o.length ≤ m) (hby : cy.1.2.length ≤ m)
    (hoy : ∀ o ∈ cy.1.2, o.length ≤ m)
    (h : RunsWithin X body (Main.m5Case3CJProg sub I n₀ n L st k xy w G (fixPtsD cx.1.2)
      (fixPtsD cy.1.2)) ans c) :
    RunsWithin X body (Main.m5DispatchCJ sub I n₀ n L st k xy w G Fx Fy cx cy) ans
      (c + 2 * fixPtsCost m + 20) := by
  have he1 : (cx.1.1.1 == 1) = false := by simpa using h1
  have he2 : (cx.1.1.1 == 2) = false := by simpa using h2
  apply RunsWithin.mono
  case h =>
    unfold Main.m5DispatchCJ
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
    run_step (RunsWithin.prim _ _)
    simp only [Prim.eval, he1]
    apply RunsWithin.ite_false
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    simp only [Prim.eval, he2]
    apply RunsWithin.ite_false
    run_step (RunsWithin.fixPtsProg hbx hox)
    run_step (RunsWithin.fixPtsProg hby hoy)
    exact h
  case hc =>
    simp only [Prim.cost]
    linarith

/-- The dispatch in Case 2 with `y`'s agreement: the run of the chosen branch. -/
theorem m5Dispatch_run2_cj (h2 : cx.1.1.1 = 2)
    (hrun : RunsWithin X body (.ite (cy.1.1.1 == 2 && (cx.2 && cy.2 || !cx.2 && !cy.2))
      (.ite cx.2
        (.bind (.op1 (Prim.snd (a := .nat) (b := .prod Ty.gens D)) Fx) fun fd =>
          .bind (.op1 .fst fd) fun fgs =>
          Main.m5Case2aProg sub n₀ n xy w G cx.1.1.2 cy.1.1.2 fgs)
        (Main.m5Case2bCJProg sub n₀ n L st xy w G Fx Fy cx.1.1.2 cy.1.1.2))
      (.op0 .none)) ans c) :
    RunsWithin X body (Main.m5DispatchCJ sub I n₀ n L st k xy w G Fx Fy cx cy) ans (c + 26) := by
  have he1 : (cx.1.1.1 == 1) = false := by simp [h2]
  have he2 : (cx.1.1.1 == 2) = true := by simp [h2]
  apply RunsWithin.mono
  case h =>
    unfold Main.m5DispatchCJ
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
    run_step (RunsWithin.prim _ _)
    simp only [Prim.eval, he1]
    apply RunsWithin.ite_false
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    simp only [Prim.eval, he2]
    apply RunsWithin.ite_true
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    simp only [Prim.eval]
    exact hrun
  case hc =>
    simp only [Prim.cost]
    linarith

/-- Case 2 when `y` disagrees: no isomorphism. -/
theorem m5_run2_none_cj (hok : (cy.1.1.1 == 2 && (cx.2 && cy.2 || !cx.2 && !cy.2)) = false) :
    RunsWithin X body (.ite (cy.1.1.1 == 2 && (cx.2 && cy.2 || !cx.2 && !cy.2))
      (.ite cx.2
        (.bind (.op1 (Prim.snd (a := .nat) (b := .prod Ty.gens D)) Fx) fun fd =>
          .bind (.op1 .fst fd) fun fgs =>
          Main.m5Case2aProg sub n₀ n xy w G cx.1.1.2 cy.1.1.2 fgs)
        (Main.m5Case2bCJProg sub n₀ n L st xy w G Fx Fy cx.1.1.2 cy.1.1.2))
      (.op0 .none)) (none : AnswerData D) 2 := by
  rw [hok]
  exact RunsWithin.ite_false (RunsWithin.prim _ _)

/-- Case 2a, when `y` agrees. -/
theorem m5_run2a_cj (hok : (cy.1.1.1 == 2 && (cx.2 && cy.2 || !cx.2 && !cy.2)) = true)
    (hA : cx.2 = true)
    (h : RunsWithin X body (Main.m5Case2aProg sub n₀ n xy w G cx.1.1.2 cy.1.1.2 Fx.2.1) ans c) :
    RunsWithin X body (.ite (cy.1.1.1 == 2 && (cx.2 && cy.2 || !cx.2 && !cy.2))
      (.ite cx.2
        (.bind (.op1 (Prim.snd (a := .nat) (b := .prod Ty.gens D)) Fx) fun fd =>
          .bind (.op1 .fst fd) fun fgs =>
          Main.m5Case2aProg sub n₀ n xy w G cx.1.1.2 cy.1.1.2 fgs)
        (Main.m5Case2bCJProg sub n₀ n L st xy w G Fx Fy cx.1.1.2 cy.1.1.2))
      (.op0 .none)) ans (c + 4) := by
  rw [hok]
  apply RunsWithin.mono
  case h =>
    apply RunsWithin.ite_true
    rw [hA]
    apply RunsWithin.ite_true
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact h
  case hc =>
    simp only [Prim.cost]
    omega

/-- Case 2b, when `y` agrees. -/
theorem m5_run2b_cj (hok : (cy.1.1.1 == 2 && (cx.2 && cy.2 || !cx.2 && !cy.2)) = true)
    (hA : cx.2 = false)
    (h : RunsWithin X body (Main.m5Case2bCJProg sub n₀ n L st xy w G Fx Fy cx.1.1.2 cy.1.1.2)
      ans c) :
    RunsWithin X body (.ite (cy.1.1.1 == 2 && (cx.2 && cy.2 || !cx.2 && !cy.2))
      (.ite cx.2
        (.bind (.op1 (Prim.snd (a := .nat) (b := .prod Ty.gens D)) Fx) fun fd =>
          .bind (.op1 .fst fd) fun fgs =>
          Main.m5Case2aProg sub n₀ n xy w G cx.1.1.2 cy.1.1.2 fgs)
        (Main.m5Case2bCJProg sub n₀ n L st xy w G Fx Fy cx.1.1.2 cy.1.1.2))
      (.op0 .none)) ans (c + 2) := by
  rw [hok]
  apply RunsWithin.mono
  case h =>
    apply RunsWithin.ite_true
    rw [hA]
    exact RunsWithin.ite_false h
  case hc =>
    omega

end DispatchRunCJ

/-! ### The dispatch's work, sub-calls and children -/

section DispatchDefsCJ

variable {D : Ty}

/-- **The work of the dispatch with coloured Johnson alignment** besides its sub-calls, for the
case it runs: as `m5W` in Cases 1 and 2a; in Case 2b the test and the route it takes (the
Johnson route with factor `max(m, uB!)` and no stuck work, or 14j-4's); in Case 3 the prefix
and both routes. -/
def m5WCJ (O : Oracle (groupSig D)) (n N k s sIn Bgen Blift Bo Bk Bcr Bd : ℕ)
    (G Fx Fy : GroupData D.denote) (wl : ℕ) (β : M5Bounds) (Bst Btr Borb Bkg Bko Bks : ℕ)
    (Bo' Bs' Bt' : ℕ → ℕ) (uB Bg1J₂ Bg1J₃ : ℕ) : ℕ :=
  match m5Sel O n N Fx Fy with
  | 1 => Giant.case1Cost n N G.2.1.length
      (partGensD (N - n) (Giant.orbitPartModel O n N Fx)).length β.Box β.Boy β.BgP β.Bmem β.BkA
      β.BlA β.Bg1₁ Bgen (m5Wb N n wl s sIn (N - n) Bd Blift Bgen Bo 0) sIn + 16
  | 2 => c2aWork n N G.2.1.length ((setOps (N - n)).gens (m5Cs O n N Fx).2).length
      (m5Cs O n N Fx).2.length β.BgP β.Bmem β.BkA β.BlA β.Bg1₂ₐ β.Bgen₂ₐ sIn Bst Borb β.Bpb wl s
      β.sK β.Bgm β.Blift β.Bker β.Bgn + 30
  | 3 => c3Work n N sIn G.2.1.length k (fixPtsD (m5Os O n N Fx)).length
      (fixPtsD (m5Os O n N Fy)).length (Case2b.sojZ (N - n)) β.BgP β.Bmem β.BkA β.BlA β.Bg1₃
      β.Bgen₃ Bst Btr Borb Bkg Bko Bks β.Bgk β.Bgs wl
      (m5Wb N n wl s sIn (N - n).factorial Bd Blift Bgen Bo
        (rd6Cost N n wl s sIn Bk Bo Bcr Bgen)) +
      (kerRedCost N n wl (kerReps O n G).length (kerModel O n G).2.1.length s β.Bk3 β.Bo3
        β.Bcr3 β.Bgen3 + 5) + wl + 3 +
      c3PreWork N n sIn k (fixPtsD (m5Os O n N Fx)).length (fixPtsD (m5Os O n N Fy)).length Bst
        Btr Borb Bkg Bko Bks β.Bgk β.BlA β.Bgs wl (Case2b.sojZ (N - n)) +
      c3CJCost n N sIn G.2.1.length k (fixPtsD (m5Os O n N Fx)).length
        (fixPtsD (m5Os O n N Fy)).length (Case2b.sojZ (N - n)) β.BgP β.Bmem β.BkA β.BlA Bg1J₃
        Bgen (m5Wb N n wl s sIn (max (N - n) uB.factorial) Bd Blift Bgen Bo 0) +
      2 * fixPtsCost (N - n) + 20
  | 4 => (match m5Leaf2b O N n Fx (m5Cs O n N Fx).2 with
      | some X₀ => c2bJTestCost N n sIn (m5Cs O n N Fx).2.length
          (Case2b.degD O N n Fx (m5Cs O n N Fx).2 - 1) Bst β.Bg (Case2b.sojZ (N - n)) Bo' Bs'
          Bt' + 1 +
          if c2bJD O N n Fx (m5Cs O n N Fx).2 then
            c2bCJCost n N sIn G.2.1.length (m5Cs O n N Fx).2.length (m5Cs O n N Fy).2.length
              (Case2b.degD O N n Fx (m5Cs O n N Fx).2 - 1)
              (cjohnGensD (N - n) (cjFirst2bD N n (m5Cs O n N Fx).2
                (Case2b.degD O N n Fx (m5Cs O n N Fx).2 - 1) X₀)).length Bst β.Bg
              (Case2b.sojZ (N - n)) β.BgP β.Bmem β.BkA β.BlA Bg1J₂ Bgen
              (m5Wb N n wl s sIn (max (N - n) uB.factorial) Bd Blift Bgen Bo 0) Bo' Bs' Bt'
          else
            Case2b.c2bCost n N sIn G.2.1.length (m5Cs O n N Fx).2.length
              (m5Cs O n N Fy).2.length (Case2b.degD O N n Fx (m5Cs O n N Fx).2 - 1)
              (Case2b.outGensD (N - n) X₀).length Bst β.Bg (Case2b.sojZ (N - n)) β.BgP β.Bmem
              β.BkA β.BlA β.Bg1₂ᵦ β.Bgen₂ᵦ
              (m5Wb N n wl s sIn (N - n).factorial Bd Blift Bgen Bo
                (rd6Cost N n wl s sIn Bk Bo Bcr Bgen)) Bo' Bs' Bt'
      | none => 0) + 28
  | _ => 28

/-- The number of the dispatch's sub-calls on windows of at most `n / k` points: Case 3's
comparisons, at most twice (the colourings are computed again inside `m5Case3Prog`). -/
def m5CKCJ (O : Oracle (groupSig D)) (n N k : ℕ) (Fx Fy : GroupData D.denote) : ℕ :=
  if m5Sel O n N Fx Fy = 3 then 2 * c3Count (fixPtsD (m5Os O n N Fx)).length k n else 0

theorem m5CKCJ_of_ne {O : Oracle (groupSig D)} {n N k : ℕ} {Fx Fy : GroupData D.denote}
    (h : m5Sel O n N Fx Fy ≠ 3) : m5CKCJ O n N k Fx Fy = 0 := by
  unfold m5CKCJ
  rw [if_neg' h]

/-- **The factor of the dispatch's children list**: as `m5CF` in Cases 1 and 2a; in Case 2b
`c2bR · max(m, uB!)` for a Johnson leaf, `c2bR · m!` otherwise; in Case 3 the sum of both
routes' factors. -/
def m5CFCJ (O : Oracle (groupSig D)) (n N k : ℕ) (Fx Fy : GroupData D.denote) (uB : ℕ) : ℕ :=
  match m5Sel O n N Fx Fy with
  | 1 => 1 * (N - n)
  | 3 => Case3.c3R k (fixPtsD (m5Os O n N Fy)).length (Case2b.sojZ (N - n)) *
      max (N - n) uB.factorial +
      (Case3.c3R k (fixPtsD (m5Os O n N Fy)).length (Case2b.sojZ (N - n)) *
        (N - n).factorial + (N - n).factorial)
  | 4 => if c2bJD O N n Fx (m5Cs O n N Fx).2 then
      Case2b.c2bR N n (m5Cs O n N Fy).2.length (Case2b.degD O N n Fx (m5Cs O n N Fx).2 - 1)
        (Case2b.sojZ (N - n)) * max (N - n) uB.factorial
    else
      Case2b.c2bR N n (m5Cs O n N Fy).2.length (Case2b.degD O N n Fx (m5Cs O n N Fx).2 - 1)
        (Case2b.sojZ (N - n)) * (N - n).factorial
  | _ => 0

end DispatchDefsCJ

section DispatchSpecCJ

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}
  {sub : HInstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)}
  {C : ℕ → Option ℕ → ℕ} {s : ℕ} {xy : StrData × StrData} {w : WinData}
  {N : ℕ} {gs : GensData} {d : D.denote} {n₀ n : ℕ} {L : LabelData} {st : ℕ × CJData}
  {sIn Lg Blift Bgen Bo Bk Bcr Bd : ℕ}

/-- **M5's dispatch with coloured Johnson alignment.** Under the hypotheses of
`RunsWithin.m5Dispatch` and, for the Johnson routes of Cases 2b and 3, `RDOrbit` at
`st = (2, X₀)`, the align charges, the bound `uB` on the union cells and `Lg ≥ R · (sIn + 1)`
for the numbers `R` of candidates: the answer is correct for `G` on `W`. The cost is the
children's (`StepChild |W| m`, factor `m5CFCJ`), `m5CKCJ` sub-calls without a hint on windows of
at most `n / k` points, `m5CH` on windows of at most `|W| / 2` points, and the work `m5WCJ`.
The Johnson routes have no stuck work (`RunsWithin.c2bCJProg`, `RunsWithin.c3CJRouteProg`).

Stage 14j-5c (`PLAN-14.md` §14.8 item 4): the hypotheses of Cases 2b and 3 carry the premises
under which their routes use them: `x`'s case (Case 2b: tag `2`, not Case 2a; Case 3: tag neither
`1` nor `2`); for the partition routes (`hBg1₂ᵦ`, `hBg1₃`) a first leaf or structure that is not a
Johnson one (`X₀.1 ≠ 2`); for the Johnson routes (`hBg1J₂`, `hDJ₂`, `hu₂`, `hBg1J₃`, `hDJ₃`,
`hu₃`) a Johnson one (`X₀.1 = 2`) with the facts `CJFacts` of its coloured pair.
`RunsWithin.m5DispatchCJ` follows from this one. -/
theorem RunsWithin.m5DispatchCJ_jp (hO : MeetsContractOn DV m5Ops X.O)
    (hPre : ∀ op x, m5Ops op → GroupPre DV op x → X.Pre op x)
    (hI : HInstValid DV (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D))
    {hC : CertSetting (GensData.denote N gs) n} {φ : strGroup hC →* Perm (Fin (N - n))}
    (hφ : IsPhi hC φ)
    (halt : alternatingGroup (Fin (N - n)) ≤ (baseHom _ n hC.base).range)
    (hwS : ∀ u : Fin N, u.val < n → u ∈ w.denote N)
    {k : ℕ} (h5 : 5 ≤ k) (hk : k + 2 ≤ N - n) (hm12 : 12 ≤ N - n)
    {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N sIn G₀) (hgs : gs.length ≤ sIn)
    (hGG₀ : GensData.denote N gs ≤ G₀) {sk : ℕ} (Bk' : BackendBounds X DV k sk ⊤)
    (hsk : sIn ≤ k * (sk + 1)) {sm : ℕ → ℕ} (Bm : ∀ M, BackendBounds X DV M (sm M) ⊤)
    (hsub : HSubSolves X body DV sub
      (fun J => SizeChild (max sIn (supTo sm (w.1.length / 2)))
          (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D) J ∧
        StepChild w.1.length (N - n) (J.winSize, J.baseOpt)) C s)
    (hCmono : ∀ a b, a ≤ b → C a none ≤ C b none) (hs : s ≤ sIn)
    (hB : RDBounds X DV n N sIn Lg Blift Bgen Bo Bk Bcr)
    (hLg : (N - n).factorial * (sIn + 1) ≤ Lg) (hst : st.1 ≠ 2) (β : M5Bounds)
    -- the full groups
    {fxs fys : GensData} {ex ey : D.denote} (hFxv : GroupValid DV N fxs ex)
    (hFyv : GroupValid DV N fys ey) (hFxs : fxs.length ≤ sIn) (hFys : fys.length ≤ sIn)
    (hFxe : GensData.denote N fxs = m5Fmap hC φ k (xy.1.denote N))
    (hFye : GensData.denote N fys = m5Fmap hC φ k (xy.2.denote N))
    -- charges on `G`
    (hBgP : X.B.call GroupOp.generate (N - n, gs.map (baseD n N))
      (X.O.run GroupOp.generate (N - n, gs.map (baseD n N))) ≤ β.BgP)
    (hBmem : ∀ g : PermData, g.Valid (N - n) → X.B.call GroupOp.mem (pModel X.O n (N, gs, d), g)
      (X.O.run GroupOp.mem (pModel X.O n (N, gs, d), g)) ≤ β.Bmem)
    (hBkA : X.B.call GroupOp.kernel ((N, gs, d), baseWin n N) (kerModel X.O n (N, gs, d)) ≤
      β.BkA)
    (hBlA : ∀ π : PermData, X.B.call GroupOp.lift ((N, gs, d), (baseWin n N, π))
      (liftModel X.O n (N, gs, d) π) ≤ β.BlA)
    (hBg : ∀ M ≤ N - n, ∀ gs' : GensData, GensData.AllValid M gs' → gs'.length ≤ sIn →
      X.B.call GroupOp.generate (M, gs') (X.O.run GroupOp.generate (M, gs')) ≤ β.Bg)
    (hBgk : ∀ gs' : GensData, GensData.AllValid N gs' →
      gs'.length ≤ k.factorial * (sIn + 1) → GensData.denote N gs' ≤ GensData.denote N gs →
        X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.Bgk)
    (hBgs : ∀ al : List ℕ, al.Nodup → al.length = k → (∀ a ∈ al, a < N - n) → ∀ b₁ b₂,
      X.B.call GroupOp.generate (N, giantGens X.O n (N, gs, d) al b₁ b₂)
        (giantSetStabModel X.O n (N, gs, d) al b₁ b₂) ≤ β.Bgs)
    (hBk3 : X.B.call GroupOp.kernel ((N, gs, d), baseWin n N) (kerModel X.O n (N, gs, d)) ≤
      β.Bk3)
    (hBo3 : X.B.call GroupOp.orbits (kerModel X.O n (N, gs, d), w)
      (krOrbits X.O n (N, gs, d) w) ≤ β.Bo3)
    (hBcr3 : X.B.call GroupOp.cosetReps ((N, gs, d), kerModel X.O n (N, gs, d))
      (kerReps X.O n (N, gs, d)) ≤ β.Bcr3)
    (hB3 : ∀ hs : GensData, GensData.AllValid N hs →
      hs.length ≤ (kerReps X.O n (N, gs, d)).length *
        (max s (kerModel X.O n (N, gs, d)).2.1.length + 1) →
      GensData.denote N hs ≤ GensData.denote N gs →
      X.B.call GroupOp.generate (N, hs) (X.O.run GroupOp.generate (N, hs)) ≤ β.Bgen3)
    -- Case 1
    (hBox : X.B.call GroupOp.orbits ((N, fxs, ex), baseWin n N)
      (Giant.baseOrbits X.O n N (N, fxs, ex)) ≤ β.Box)
    (hBoy : X.B.call GroupOp.orbits ((N, fys, ey), baseWin n N)
      (Giant.baseOrbits X.O n N (N, fys, ey)) ≤ β.Boy)
    (hBg1₁ : X.B.call GroupOp.generate
      (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
        (partGensD (N - n) (Giant.orbitPartModel X.O n N (N, fxs, ex))))).map
        (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
      (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
        (partGensD (N - n) (Giant.orbitPartModel X.O n N (N, fxs, ex)))))) ≤ β.Bg1₁)
    (hD₁ : ∀ gs' d' O', RDSet DV n N gs w L (Giant.g1Model X.O n (N, gs, d) (partOps (N - n))
        (Giant.orbitPartModel X.O n N (N, fxs, ex))).2.1 sIn gs' d' O' →
      RDOrbit X body DV n N w L st sIn Bd gs' d' O')
    -- Case 2a
    (hBg1₂ₐ : X.B.call GroupOp.generate
      (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
        ((setOps (N - n)).gens (m5Cs X.O n N (N, fxs, ex)).2))).map
        (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
      (Giant.g1Model X.O n (N, gs, d) (setOps (N - n)) (m5Cs X.O n N (N, fxs, ex)).2) ≤
        β.Bg1₂ₐ)
    (hBgen₂ₐ : ∀ gs' : GensData, GensData.AllValid N gs' → gs'.length ≤ sIn + 1 →
      GensData.denote N gs' ≤ GensData.denote N gs →
      X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.Bgen₂ₐ)
    (hBpb : ∀ gs', GensData.AllValid N gs' →
      gs'.length ≤ (sIn + 1) * (sIn + 1) + sIn + fxs.length → GensData.denote N gs' ≤ G₀ →
      X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.Bpb)
    (hBgm : ∀ (w' : WinData) (σ' : PermData) (gs' : GensData) (d' : D.denote),
      Giant.PbSubP DV G₀ xy w.1.length sIn (xy, w', σ', N, gs', d') →
      X.B.call GroupOp.generate (w'.1.length, GensData.restrictTo (WinData.pos N w') w'.1 gs')
        (X.O.run GroupOp.generate
          (w'.1.length, GensData.restrictTo (WinData.pos N w') w'.1 gs')) ≤ β.Bgm)
    (hBlift : ∀ (w' : WinData) (σ' : PermData) (gs' : GensData) (d' : D.denote),
      Giant.PbSubP DV G₀ xy w.1.length sIn (xy, w', σ', N, gs', d') → ∀ π' : PermData,
      X.B.call GroupOp.lift ((N, gs', d'), (w', π'))
        (X.O.run GroupOp.lift ((N, gs', d'), (w', π'))) ≤ β.Blift)
    (hBker : ∀ (w' : WinData) (σ' : PermData) (gs' : GensData) (d' : D.denote),
      Giant.PbSubP DV G₀ xy w.1.length sIn (xy, w', σ', N, gs', d') →
      X.B.call GroupOp.kernel ((N, gs', d'), w') (X.O.run GroupOp.kernel ((N, gs', d'), w')) ≤
        β.Bker)
    (hsK : ∀ (w' : WinData) (σ' : PermData) (gs' : GensData) (d' : D.denote),
      Giant.PbSubP DV G₀ xy w.1.length sIn (xy, w', σ', N, gs', d') →
      (X.O.run GroupOp.kernel ((N, gs', d'), w')).2.1.length ≤ β.sK)
    (hBgn : ∀ hs : GensData, GensData.AllValid N hs → hs.length ≤ β.sK + s →
      GensData.denote N hs ≤ G₀ →
      X.B.call GroupOp.generate (N, hs) (X.O.run GroupOp.generate (N, hs)) ≤ β.Bgn)
    -- Case 2b
    (hBg1₂ᵦ :
      (m5Cs X.O n N (N, fxs, ex)).1 = 2 → m5IsA X.O n N (N, fxs, ex) = false → ∀ X₀ : SoJTree.OutD,
      m5Leaf2b X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 = some X₀ → X₀.1 ≠ 2 →
      X.B.call GroupOp.generate
        (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (Case2b.outGensD (N - n) X₀))).map
          (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
        (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (Case2b.outGensD (N - n) X₀)))) ≤ β.Bg1₂ᵦ)
    (hBgen₂ᵦ : ∀ gs' : GensData, GensData.AllValid N gs' →
      gs'.length ≤ Case2b.c2bR N n (m5Cs X.O n N (N, fys, ey)).2.length
        (Case2b.degD X.O N n (N, fys, ey) (m5Cs X.O n N (N, fys, ey)).2 - 1)
        (Case2b.sojZ (N - n)) * (sIn + 1) →
      GensData.denote N gs' ≤ GensData.denote N gs →
      X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.Bgen₂ᵦ)
    (hD₂ᵦ : ∀ X₀, m5Leaf2b X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 = some X₀ →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (Case2b.outOps (N - n)) X₀).2.1 sIn gs' d' O' →
      RDOrbit X body DV n N w L st sIn Bd gs' d' O')
    -- Case 3
    (hBg1₃ :
      (m5Cs X.O n N (N, fxs, ex)).1 ≠ 1 → (m5Cs X.O n N (N, fxs, ex)).1 ≠ 2 →
      ∀ X₀ : SoJTree.OutD, Case3.C3First φ (strOn hC.le (xy.1.denote N)) (N - n) k
        (fixPtsD (m5Os X.O n N (N, fxs, ex))) X₀ → X₀.1 ≠ 2 →
      X.B.call GroupOp.generate
        (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (Case2b.outGensD (N - n) X₀))).map
          (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
        (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (Case2b.outGensD (N - n) X₀)))) ≤ β.Bg1₃)
    (hBgen₃ : ∀ gs' : GensData, GensData.AllValid N gs' →
      gs'.length ≤ Case3.c3R k (fixPtsD (m5Os X.O n N (N, fys, ey))).length
        (Case2b.sojZ (N - n)) * (sIn + 1) →
      GensData.denote N gs' ≤ GensData.denote N gs →
      X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.Bgen₃)
    (hD₃ : ∀ X₀, Case3.C3First φ (strOn hC.le (xy.1.denote N)) (N - n) k
        (fixPtsD (m5Os X.O n N (N, fxs, ex))) X₀ →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (Case2b.outOps (N - n)) X₀).2.1 sIn gs' d' O' →
      RDOrbit X body DV n N w L st sIn Bd gs' d' O')
    -- the coloured Johnson routes
    {uB Bg1J₂ Bg1J₃ : ℕ} (hLgJ : max (N - n) uB.factorial * (sIn + 1) ≤ Lg)
    (hBg1J₂ :
      (m5Cs X.O n N (N, fxs, ex)).1 = 2 → m5IsA X.O n N (N, fxs, ex) = false → ∀ X₀ : SoJTree.OutD,
      m5Leaf2b X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 = some X₀ → X₀.1 = 2 →
      CJFacts (N - n) (cjFirst2bD N n (m5Cs X.O n N (N, fxs, ex)).2
          (Case2b.degD X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 - 1) X₀) →
      X.B.call GroupOp.generate
        (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (cjohnGensD (N - n) (cjFirst2bD N n (m5Cs X.O n N (N, fxs, ex)).2
            (Case2b.degD X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 - 1) X₀)))).map
          (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
        (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (cjohnGensD (N - n) (cjFirst2bD N n (m5Cs X.O n N (N, fxs, ex)).2
            (Case2b.degD X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 - 1) X₀))))) ≤
        Bg1J₂)
    (hLY₂ : Case2b.c2bR N n (m5Cs X.O n N (N, fys, ey)).2.length
      (Case2b.degD X.O N n (N, fys, ey) (m5Cs X.O n N (N, fys, ey)).2 - 1)
      (Case2b.sojZ (N - n)) * (sIn + 1) ≤ Lg)
    (hDJ₂ :
      (m5Cs X.O n N (N, fxs, ex)).1 = 2 → m5IsA X.O n N (N, fxs, ex) = false →
      ∀ X₀, m5Leaf2b X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 = some X₀ → X₀.1 = 2 →
      CJFacts (N - n) (cjFirst2bD N n (m5Cs X.O n N (N, fxs, ex)).2
          (Case2b.degD X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 - 1) X₀) →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (cjohnOps (N - n))
          (cjFirst2bD N n (m5Cs X.O n N (N, fxs, ex)).2
            (Case2b.degD X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 - 1) X₀)).2.1 sIn
          gs' d' O' →
      RDOrbit X body DV n N w L (2, cjFirst2bD N n (m5Cs X.O n N (N, fxs, ex)).2
        (Case2b.degD X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 - 1) X₀) sIn Bd gs' d' O')
    (hu₂ :
      (m5Cs X.O n N (N, fxs, ex)).1 = 2 → m5IsA X.O n N (N, fxs, ex) = false →
      ∀ X₀, m5Leaf2b X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 = some X₀ → X₀.1 = 2 →
      CJFacts (N - n) (cjFirst2bD N n (m5Cs X.O n N (N, fxs, ex)).2
          (Case2b.degD X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 - 1) X₀) →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (cjohnOps (N - n))
          (cjFirst2bD N n (m5Cs X.O n N (N, fxs, ex)).2
            (Case2b.degD X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 - 1) X₀)).2.1 sIn
          gs' d' O' →
      ((labJUD X₀.2.2.2.1.length (markArr (N - n) X₀.2.2.1) X₀.2.2.2.2.2 L O').getD
        (O'.headD 0) []).length ≤ uB)
    (hBg1J₃ :
      (m5Cs X.O n N (N, fxs, ex)).1 ≠ 1 → (m5Cs X.O n N (N, fxs, ex)).1 ≠ 2 →
      ∀ cXX X₀, Case3.ColChar φ (strOn hC.le (xy.1.denote N))
        (strOn hC.le (xy.1.denote N)) k (fixPtsD (m5Os X.O n N (N, fxs, ex))).length
        (fixPtsD (m5Os X.O n N (N, fxs, ex))) (fixPtsD (m5Os X.O n N (N, fxs, ex))) cXX →
      Case3.firstStructD (N - n) k (fixPtsD (m5Os X.O n N (N, fxs, ex)))
        (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fxs, ex))).length) = some X₀ → X₀.1 = 2 →
      CJFacts (N - n) (cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fxs, ex)))
          (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fxs, ex))).length) X₀) →
      X.B.call GroupOp.generate
        (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (cjohnGensD (N - n) (cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fxs, ex)))
            (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fxs, ex))).length) X₀)))).map
          (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
        (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (cjohnGensD (N - n) (cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fxs, ex)))
            (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fxs, ex))).length) X₀))))) ≤ Bg1J₃)
    (hLY₃ : Case3.c3R k (fixPtsD (m5Os X.O n N (N, fys, ey))).length (Case2b.sojZ (N - n)) *
      (sIn + 1) ≤ Lg)
    (hDJ₃ :
      (m5Cs X.O n N (N, fxs, ex)).1 ≠ 1 → (m5Cs X.O n N (N, fxs, ex)).1 ≠ 2 →
      ∀ cXX X₀, Case3.ColChar φ (strOn hC.le (xy.1.denote N))
        (strOn hC.le (xy.1.denote N)) k (fixPtsD (m5Os X.O n N (N, fxs, ex))).length
        (fixPtsD (m5Os X.O n N (N, fxs, ex))) (fixPtsD (m5Os X.O n N (N, fxs, ex))) cXX →
      Case3.firstStructD (N - n) k (fixPtsD (m5Os X.O n N (N, fxs, ex)))
        (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fxs, ex))).length) = some X₀ → X₀.1 = 2 →
      CJFacts (N - n) (cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fxs, ex)))
          (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fxs, ex))).length) X₀) →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (cjohnOps (N - n))
          (cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fxs, ex)))
            (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fxs, ex))).length) X₀)).2.1 sIn
          gs' d' O' →
      RDOrbit X body DV n N w L (2, cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fxs, ex)))
        (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fxs, ex))).length) X₀) sIn Bd gs' d' O')
    (hu₃ :
      (m5Cs X.O n N (N, fxs, ex)).1 ≠ 1 → (m5Cs X.O n N (N, fxs, ex)).1 ≠ 2 →
      ∀ cXX X₀, Case3.ColChar φ (strOn hC.le (xy.1.denote N))
        (strOn hC.le (xy.1.denote N)) k (fixPtsD (m5Os X.O n N (N, fxs, ex))).length
        (fixPtsD (m5Os X.O n N (N, fxs, ex))) (fixPtsD (m5Os X.O n N (N, fxs, ex))) cXX →
      Case3.firstStructD (N - n) k (fixPtsD (m5Os X.O n N (N, fxs, ex)))
        (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fxs, ex))).length) = some X₀ → X₀.1 = 2 →
      CJFacts (N - n) (cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fxs, ex)))
          (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fxs, ex))).length) X₀) →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (cjohnOps (N - n))
          (cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fxs, ex)))
            (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fxs, ex))).length) X₀)).2.1 sIn
          gs' d' O' →
      ((labJUD X₀.2.2.2.1.length (markArr (N - n) X₀.2.2.1) X₀.2.2.2.2.2 L O').getD
        (O'.headD 0) []).length ≤ uB) :
    ∃ (ans : AnswerData D) (ch : List (ℕ × Option ℕ)),
      RunsWithin X body (Main.m5DispatchCJ sub
          (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D) n₀ n L st k xy w
          (N, gs, d) (N, fxs, ex) (N, fys, ey) (m5CaseD X.O n N (N, fxs, ex))
          (m5CaseD X.O n N (N, fys, ey))) ans
        ((ch.map fun x => C x.1 x.2).sum +
          m5CKCJ X.O n N k (N, fxs, ex) (N, fys, ey) * C (n / k) none +
          m5CH X.O n N sIn w.1.length (N, fxs, ex) (N, fys, ey) * C (w.1.length / 2) none +
          m5WCJ X.O n N k s sIn Bgen Blift Bo Bk Bcr Bd (N, gs, d) (N, fxs, ex) (N, fys, ey)
            w.1.length β B.Bstab B.Btr B.Borb Bk'.Bgen Bk'.Borb Bk'.Bstab
            (fun M => (Bm M).Borb) (fun M => (Bm M).Bstab) (fun M => (Bm M).Btr) uB Bg1J₂ Bg1J₃) ∧
      AnsOK DV N (w.denote N) 1 (GensData.denote N gs) (xy.1.denote N) (xy.2.denote N) ans ∧
      (∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sIn) ∧
      ChildList w.1.length (m5CFCJ X.O n N k (N, fxs, ex) (N, fys, ey) uB)
        (StepChild w.1.length (N - n)) ch := by
  classical
  -- the sub-solver on the children of every case but 2a, and Case 2a's generator bound
  have hsubI : HSubSolves X body DV sub
      (fun J => SizeChild sIn (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D)
        J ∧ StepChild w.1.length (N - n) (J.winSize, J.baseOpt)) C s :=
    hsub.mono fun J hJ => ⟨hJ.1.mono (le_max_left _ _), hJ.2⟩
  have hgR : ∀ M ≤ w.1.length / 2, ∀ hs : GensData, GensData.AllValid M hs → hs.length ≤ sIn →
      (X.O.run GroupOp.generate (M, hs)).2.1.length ≤ max sIn (supTo sm (w.1.length / 2)) :=
    fun M hM hs hv _ =>
      ((Bm M).genOut hs hv le_top).trans ((le_supTo hM).trans (le_max_right _ _))
  -- the operations
  have hOc1 : MeetsContractOn DV Giant.case1Ops X.O := fun op x h hx => hO op x (Or.inl h) hx
  have hPc1 : ∀ op x, Giant.case1Ops op → GroupPre DV op x → X.Pre op x :=
    fun op x h hx => hPre op x (Or.inl h) hx
  have hO2a : MeetsContractOn DV Giant.c2aOps X.O :=
    fun op x h hx => hO op x (Or.inr (Or.inl h)) hx
  have hP2a : ∀ op x, Giant.c2aOps op → GroupPre DV op x → X.Pre op x :=
    fun op x h hx => hPre op x (Or.inr (Or.inl h)) hx
  have hOr : MeetsContractOn DV restrictOps X.O :=
    fun op x h hx => hO op x (Or.inr (Or.inr (Or.inl h))) hx
  have hPr : ∀ op x, restrictOps op → GroupPre DV op x → X.Pre op x :=
    fun op x h hx => hPre op x (Or.inr (Or.inr (Or.inl h))) hx
  have hO2b : MeetsContractOn DV Case2b.c2bOps X.O :=
    fun op x h hx => hO op x (Or.inr (Or.inr (Or.inr (Or.inl h)))) hx
  have hP2b : ∀ op x, Case2b.c2bOps op → GroupPre DV op x → X.Pre op x :=
    fun op x h hx => hPre op x (Or.inr (Or.inr (Or.inr (Or.inl h)))) hx
  have hO3 : MeetsContractOn DV Case3.c3Ops X.O :=
    fun op x h hx => hO op x (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))) hx
  have hP3 : ∀ op x, Case3.c3Ops op → GroupPre DV op x → X.Pre op x :=
    fun op x h hx => hPre op x (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))) hx
  have hOrd : MeetsContractOn DV rdOps X.O :=
    fun op x h hx => hO op x (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))) hx
  have hPrd : ∀ op x, rdOps op → GroupPre DV op x → X.Pre op x :=
    fun op x h hx => hPre op x (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))) hx
  have hOk : MeetsContractOn DV kerRedOps X.O :=
    fun op x h hx => hO op x (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))) hx
  have hPk : ∀ op x, kerRedOps op → GroupPre DV op x → X.Pre op x := fun op x h hx =>
    hPre op x (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))) hx
  have hOcs : MeetsContractOn DV m5CaseOps X.O := fun op x h hx =>
    hO op x (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))) hx
  have hPcs : ∀ op x, m5CaseOps op → GroupPre DV op x → X.Pre op x := fun op x h hx =>
    hPre op x (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))) hx
  -- the setting
  have hGv : GroupValid DV N gs d := hI.valid.group
  have hG : IsInvariant (GensData.denote N gs) (baseSet n N) := hC.base
  have hWG : IsInvariant (GensData.denote N gs) (w.denote N) := hI.valid.invariant
  have hFxG : GensData.denote N fxs ≤ GensData.denote N gs := hFxe ▸ m5Fmap_le hC φ k _
  have hFyG : GensData.denote N fys ≤ GensData.denote N gs := hFye ▸ m5Fmap_le hC φ k _
  have hFxi : IsInvariant (GensData.denote N fxs) (baseSet n N) := hG.mono hFxG
  have hFyi : IsInvariant (GensData.denote N fys) (baseSet n N) := hG.mono hFyG
  have hFx₀ : GensData.denote N fxs ≤ G₀ := hFxG.trans hGG₀
  have hFy₀ : GensData.denote N fys ≤ G₀ := hFyG.trans hGG₀
  obtain ⟨hosx, hAx, hngx⟩ := m5Case_spec hOcs hPcs B Bm hFxv hFxs hFx₀ hFxi
  obtain ⟨hosy, hAy, hngy⟩ := m5Case_spec hOcs hPcs B Bm hFyv hFys hFy₀ hFyi
  have hcx := Giant.caseD_spec hFxi hosx
  have hcy := Giant.caseD_spec hFyi hosy
  rw [m5Cs_eq] at hcx hcy
  have hLg' : (N - n) * (sIn + 1) ≤ Lg :=
    (Nat.mul_le_mul_right _ (Nat.self_le_factorial _)).trans hLg
  by_cases h1 : (m5Cs X.O n N (N, fxs, ex)).1 = 1
  · -- Case 1
    have hsel : m5Sel X.O n N (N, fxs, ex) (N, fys, ey) = 1 := by simp [m5Sel, h1]
    obtain ⟨hc1a, hc1b⟩ := hcx.2.2.1.1 h1
    obtain ⟨ans, ch, hrun, hok, hg, hch⟩ := RunsWithin.m5Case1Prog_ns hOc1 hPc1 hOrd hPrd hI
      hG halt B hGG₀ le_rfl (m5Fmap_le hC φ k) (m5Fmap_loc hC φ k hwS) (m5Fmap_relabel hC φ k)
      hFxv hFyv hFxe hFye hFxi hc1a hc1b hBox hBoy hBgP hBmem hBkA hBlA hBg1₁ hsubI hB hs hLg'
      (by omega) hst hD₁
    refine ⟨ans, ch, (m5Dispatch_run1_cj h1 hrun).mono ?_, hok, hg, ?_⟩
    · rw [m5CKCJ_of_ne (by rw [hsel]; decide), m5CH_of_ne (by rw [hsel]; decide)]
      have hW : m5WCJ X.O n N k s sIn Bgen Blift Bo Bk Bcr Bd (N, gs, d) (N, fxs, ex) (N, fys, ey)
          w.1.length β B.Bstab B.Btr B.Borb Bk'.Bgen Bk'.Borb Bk'.Bstab
          (fun M => (Bm M).Borb) (fun M => (Bm M).Bstab) (fun M => (Bm M).Btr) uB Bg1J₂
              Bg1J₃ =
          Giant.case1Cost n N gs.length
            (partGensD (N - n) (Giant.orbitPartModel X.O n N (N, fxs, ex))).length β.Box β.Boy
            β.BgP β.Bmem β.BkA β.BlA β.Bg1₁ Bgen
            (m5Wb N n w.1.length s sIn (N - n) Bd Blift Bgen Bo 0) sIn + 16 := by
        unfold m5WCJ
        rw [hsel]
        rfl
      rw [hW]
      simp only [m5Wb]
      omega
    · have hF : m5CFCJ X.O n N k (N, fxs, ex) (N, fys, ey) uB = 1 * (N - n) := by
        unfold m5CFCJ
        rw [hsel]
        rfl
      rw [hF]
      exact hch
  by_cases h2 : (m5Cs X.O n N (N, fxs, ex)).1 = 2
  · obtain ⟨hΦxn, hΦxl, hΦx2, hΦxo⟩ := hcx.2.1 h2
    by_cases hok : ((m5Cs X.O n N (N, fys, ey)).1 == 2 &&
        (m5IsA X.O n N (N, fxs, ex) && m5IsA X.O n N (N, fys, ey) ||
          !m5IsA X.O n N (N, fxs, ex) && !m5IsA X.O n N (N, fys, ey))) = true
    · have h2y : (m5Cs X.O n N (N, fys, ey)).1 = 2 := by
        simp only [Bool.and_eq_true, beq_iff_eq] at hok
        exact hok.1
      obtain ⟨hΦyn, hΦyl, hΦy2, hΦyo⟩ := hcy.2.1 h2y
      by_cases hA : m5IsA X.O n N (N, fxs, ex) = true
      · -- Case 2a
        have hsel : m5Sel X.O n N (N, fxs, ex) (N, fys, ey) = 2 := by
          unfold m5Sel
          rw [if_neg' h1, if_pos' h2, if_pos' hok, if_pos' hA]
        obtain ⟨lab, t, he, ht, ht1, ht2⟩ := m5_labels (hI.hint L rfl).1 hGv.1 hI.valid.win
          hWG (hI.hint L rfl).2 hG
        obtain ⟨ans, hrun, hok', hg⟩ := RunsWithin.m5Case2aProg hO2a hP2a hOr hPr hI B hGG₀ hG
          halt (by omega) he ht ht1 ht2 (m5Fmap_le hC φ k) (m5Fmap_loc hC φ k hwS)
          (m5Fmap_relabel hC φ k) hFxv.1 hFxe
          (fun f hf => m5Fmap_matchesW hC φ k _ (fun u hu => hI.win_lt u.val hu) f (hFxe ▸ hf))
          hFye hFxi hFyi hΦxn hΦxl hΦx2 hΦxo hΦyn hΦyl hΦy2 hΦyo (hAx h2 hA) hBgP hBmem hBkA
          hBlA hBg1₂ₐ hBgen₂ₐ hBpb hgR hsub hCmono hBgm hBlift hBker hsK hBgn
        refine ⟨ans, [], (m5Dispatch_run2_cj h2 (m5_run2a_cj hok hA hrun)).mono ?_, hok',
          hg sIn (fun gs' hv hle => B.genOut gs' hv (hle.trans hGG₀)),
          ⟨by simp, by simp, by simp⟩⟩
        rw [m5CKCJ_of_ne (by rw [hsel]; decide)]
        have hH : m5CH X.O n N sIn w.1.length (N, fxs, ex) (N, fys, ey) =
            (sIn + 1) * w.1.length := by
          unfold m5CH
          rw [if_pos' hsel]
        have hW : m5WCJ X.O n N k s sIn Bgen Blift Bo Bk Bcr Bd (N, gs, d) (N, fxs, ex)
            (N, fys, ey) w.1.length β B.Bstab B.Btr B.Borb Bk'.Bgen Bk'.Borb Bk'.Bstab
            (fun M => (Bm M).Borb) (fun M => (Bm M).Bstab) (fun M => (Bm M).Btr) uB Bg1J₂
              Bg1J₃ =
            c2aWork n N gs.length ((setOps (N - n)).gens (m5Cs X.O n N (N, fxs, ex)).2).length
              (m5Cs X.O n N (N, fxs, ex)).2.length β.BgP β.Bmem β.BkA β.BlA β.Bg1₂ₐ β.Bgen₂ₐ
              sIn B.Bstab B.Borb β.Bpb w.1.length s β.sK β.Bgm β.Blift β.Bker β.Bgn + 30 := by
          unfold m5WCJ
          rw [hsel]
          rfl
        rw [hH, hW]
        simp only [List.map_nil, List.sum_nil]
        omega
      · -- Case 2b
        have hA' : m5IsA X.O n N (N, fxs, ex) = false := by simpa using hA
        have hAy' : m5IsA X.O n N (N, fys, ey) = false := by
          have h' := hok
          rw [hA'] at h'
          simp only [Bool.and_eq_true, beq_iff_eq, Bool.false_and, Bool.not_false, Bool.true_and,
            Bool.false_or, Bool.not_eq_true'] at h'
          exact h'.2
        have hsel : m5Sel X.O n N (N, fxs, ex) (N, fys, ey) = 4 := by
          unfold m5Sel
          rw [if_neg' h1, if_pos' h2, if_pos' hok, if_neg' hA]
        obtain ⟨X₀, hX₀, ans, ch, hrun, hok', hg, hch⟩ := RunsWithin.m5Case2bCJProg_jp
          (F := (N - n).factorial) (W6 := rd6Cost N n w.1.length s sIn Bk Bo Bcr Bgen) hO2b
          hP2b hOrd hPrd hI B hGG₀ Bm hG halt (m5Fmap_loc hC φ k hwS) (m5Fmap_relabel hC φ k)
          hFxv hFyv hFxs hFys hFx₀ hFy₀ hFxe hFye hFxi hFyi hΦxn hΦxl hΦx2 hΦxo hΦyn hΦyl
          hΦy2 hΦyo (hngx h2 hA') (hngy h2y hAy') hBg hBgP hBmem hBkA hBlA (hBg1₂ᵦ h2 hA') hBgen₂ᵦ
          hsubI hB hs hLg (Nat.factorial_pos _) (Nat.self_le_factorial _)
          (fun X₀ hX₀ _ => hD₂ᵦ X₀ hX₀) (fun _ _ _ => Or.inl le_rfl)
          (fun _ _ _ => Or.inr ⟨le_rfl, le_rfl⟩) (hBg1J₂ h2 hA') hLY₂ hLgJ (by omega) (hDJ₂ h2 hA')
          (hu₂ h2 hA')
        refine ⟨ans, ch, (m5Dispatch_run2_cj h2 (m5_run2b_cj hok hA' hrun)).mono ?_, hok', hg, ?_⟩
        · rw [m5CKCJ_of_ne (by rw [hsel]; decide), m5CH_of_ne (by rw [hsel]; decide)]
          unfold m5WCJ
          rw [hsel]
          simp only
          rw [hX₀]
          simp only [m5Wb]
          omega
        · unfold m5CFCJ
          rw [hsel]
          exact hch
    · -- Case 2 for `x`, not in the same way for `y`: no isomorphism
      have hsel : m5Sel X.O n N (N, fxs, ex) (N, fys, ey) = 0 := by
        unfold m5Sel
        rw [if_neg' h1, if_pos' h2, if_neg' hok]
      refine ⟨none, [],
        (m5Dispatch_run2_cj h2 (m5_run2_none_cj (Bool.eq_false_iff.2 hok))).mono ?_, ?_,
        by simp, ⟨by simp, by simp, by simp⟩⟩
      · rw [m5CKCJ_of_ne (by rw [hsel]; decide), m5CH_of_ne (by rw [hsel]; decide)]
        have hW : m5WCJ X.O n N k s sIn Bgen Blift Bo Bk Bcr Bd (N, gs, d) (N, fxs, ex)
            (N, fys, ey) w.1.length β B.Bstab B.Btr B.Borb Bk'.Bgen Bk'.Borb Bk'.Bstab
            (fun M => (Bm M).Borb) (fun M => (Bm M).Bstab) (fun M => (Bm M).Btr) uB Bg1J₂
            Bg1J₃ = 28 := by
          unfold m5WCJ
          rw [hsel]
          rfl
        rw [hW]
        simp
      · show iso (w.denote N) 1 (GensData.denote N gs) (xy.1.denote N) (xy.2.denote N) = ∅
        refine Set.eq_empty_of_forall_notMem fun g hg => hok ?_
        have hly := m5_large_iso hC φ k hwS hWG hg hFxe hFye hFxi hFyi (hcx.1.1 h2)
        have h2y : (m5Cs X.O n N (N, fys, ey)).1 = 2 := hcy.1.2 hly
        obtain ⟨hΦyn, hΦyl, hΦy2, hΦyo⟩ := hcy.2.1 h2y
        have hiffx := m5_isA_iff hOcs hPcs B Bm hFxv hFxs hFx₀ hFxi h2
        have hiffy := m5_isA_iff hOcs hPcs B Bm hFyv hFys hFy₀ hFyi h2y
        have htt := m5_tupTrans_iso hC φ k hwS hWG hg hFxe hFye hFxi hFyi hΦxn hΦxl hΦx2 hΦxo
          hΦyn hΦyl hΦy2 hΦyo
        have hAeq : m5IsA X.O n N (N, fxs, ex) = m5IsA X.O n N (N, fys, ey) := by
          rw [Bool.eq_iff_iff, ← hiffx, ← hiffy]
          exact htt.symm
        rw [hAeq, h2y]
        cases m5IsA X.O n N (N, fys, ey) <;> simp
  · -- Case 3
    have h3 : (m5Cs X.O n N (N, fxs, ex)).1 = 3 := by
      rcases m5_caseD_tag (N - n) (m5Os X.O n N (N, fxs, ex)) with h | h | h
      · exact absurd h h1
      · exact absurd h h2
      · exact h
    have hsel : m5Sel X.O n N (N, fxs, ex) (N, fys, ey) = 3 := by
      unfold m5Sel
      rw [if_neg' h1, if_neg' h2]
    obtain ⟨-, hc3b⟩ := hcx.2.2.2.1 h3
    obtain ⟨hVxn, hVxl, hVxF⟩ := fixPtsD_spec hFxi hosx
    obtain ⟨hVyn, hVyl, hVyF⟩ := fixPtsD_spec hFyi hosy
    rw [m5Os_eq] at hVxn hVxl hVxF hVyn hVyl hVyF
    have hlen := m5_fix_len hVxn hVxl hVxF
    have hm6 : 6 ≤ (fixPtsD (m5Os X.O n N (N, fxs, ex))).length := by
      omega
    have hVx2 : N - n ≤ 2 * (fixPtsD (m5Os X.O n N (N, fxs, ex))).length := by
      omega
    obtain ⟨ans, ch, hrun, hok', hg, hch⟩ := RunsWithin.m5Case3CJProg_jp hO3 hP3 hOrd hPrd hI hφ
      halt hwS (m5Fmap_loc hC φ k hwS) (m5Fmap_relabel hC φ k) hFxe hFye hFxi hFyi hVxl hVxn
      hVyl hVyn hVxF hVyF hm6 hVx2 h5 hk B hgs hGG₀ Bk' hsk hBgk hBlA hBgs hBgP hBmem hBkA hsubI
      hCmono hB hs
      (fun hc => RunsWithin.m5Case3Prog hO3 hP3 hOrd hPrd hOk hPk hI hφ halt hwS
        (m5Fmap_loc hC φ k hwS)
        (m5Fmap_relabel hC φ k) hFxe hFye hFxi hFyi hVxl hVxn hVyl hVyn hVxF hVyF hm6 h5 hk B hgs
        hGG₀ Bk' hsk hBgk hBlA hBgs hBgP hBmem hBkA
        (fun X₀ hX₀ => hBg1₃ h1 h2 X₀ hX₀ (hc X₀ hX₀)) hBgen₃ hsubI hCmono hB hs hLg
        hD₃ hBk3
        hBo3 hBcr3 hB3)
      (hBg1J₃ h1 h2) hLY₃ hLgJ (by omega) (hDJ₃ h1 h2)
      (hu₃ h1 h2)
    obtain ⟨hbx, hox⟩ := m5_os_bounds hosx
    obtain ⟨hby, hoy⟩ := m5_os_bounds hosy
    refine ⟨ans, ch, (m5Dispatch_run3_cj h1 h2 hbx hox hby hoy hrun).mono ?_, hok', hg, ?_⟩
    · rw [m5CH_of_ne (by rw [hsel]; decide)]
      have hK : m5CKCJ X.O n N k (N, fxs, ex) (N, fys, ey) =
          2 * c3Count (fixPtsD (m5Os X.O n N (N, fxs, ex))).length k n := by
        unfold m5CKCJ
        rw [if_pos' hsel]
      rw [hK, Nat.mul_assoc]
      unfold m5WCJ
      rw [hsel]
      simp only [m5Wb]
      omega
    · unfold m5CFCJ
      rw [hsel]
      exact hch

/-- `RunsWithin.m5DispatchCJ_jp` with Case 2b's Johnson-route hypotheses stated for every first
leaf. -/
theorem RunsWithin.m5DispatchCJ (hO : MeetsContractOn DV m5Ops X.O)
    (hPre : ∀ op x, m5Ops op → GroupPre DV op x → X.Pre op x)
    (hI : HInstValid DV (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D))
    {hC : CertSetting (GensData.denote N gs) n} {φ : strGroup hC →* Perm (Fin (N - n))}
    (hφ : IsPhi hC φ)
    (halt : alternatingGroup (Fin (N - n)) ≤ (baseHom _ n hC.base).range)
    (hwS : ∀ u : Fin N, u.val < n → u ∈ w.denote N)
    {k : ℕ} (h5 : 5 ≤ k) (hk : k + 2 ≤ N - n) (hm12 : 12 ≤ N - n)
    {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N sIn G₀) (hgs : gs.length ≤ sIn)
    (hGG₀ : GensData.denote N gs ≤ G₀) {sk : ℕ} (Bk' : BackendBounds X DV k sk ⊤)
    (hsk : sIn ≤ k * (sk + 1)) {sm : ℕ → ℕ} (Bm : ∀ M, BackendBounds X DV M (sm M) ⊤)
    (hsub : HSubSolves X body DV sub
      (fun J => SizeChild (max sIn (supTo sm (w.1.length / 2)))
          (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D) J ∧
        StepChild w.1.length (N - n) (J.winSize, J.baseOpt)) C s)
    (hCmono : ∀ a b, a ≤ b → C a none ≤ C b none) (hs : s ≤ sIn)
    (hB : RDBounds X DV n N sIn Lg Blift Bgen Bo Bk Bcr)
    (hLg : (N - n).factorial * (sIn + 1) ≤ Lg) (hst : st.1 ≠ 2) (β : M5Bounds)
    -- the full groups
    {fxs fys : GensData} {ex ey : D.denote} (hFxv : GroupValid DV N fxs ex)
    (hFyv : GroupValid DV N fys ey) (hFxs : fxs.length ≤ sIn) (hFys : fys.length ≤ sIn)
    (hFxe : GensData.denote N fxs = m5Fmap hC φ k (xy.1.denote N))
    (hFye : GensData.denote N fys = m5Fmap hC φ k (xy.2.denote N))
    -- charges on `G`
    (hBgP : X.B.call GroupOp.generate (N - n, gs.map (baseD n N))
      (X.O.run GroupOp.generate (N - n, gs.map (baseD n N))) ≤ β.BgP)
    (hBmem : ∀ g : PermData, g.Valid (N - n) → X.B.call GroupOp.mem (pModel X.O n (N, gs, d), g)
      (X.O.run GroupOp.mem (pModel X.O n (N, gs, d), g)) ≤ β.Bmem)
    (hBkA : X.B.call GroupOp.kernel ((N, gs, d), baseWin n N) (kerModel X.O n (N, gs, d)) ≤
      β.BkA)
    (hBlA : ∀ π : PermData, X.B.call GroupOp.lift ((N, gs, d), (baseWin n N, π))
      (liftModel X.O n (N, gs, d) π) ≤ β.BlA)
    (hBg : ∀ M ≤ N - n, ∀ gs' : GensData, GensData.AllValid M gs' → gs'.length ≤ sIn →
      X.B.call GroupOp.generate (M, gs') (X.O.run GroupOp.generate (M, gs')) ≤ β.Bg)
    (hBgk : ∀ gs' : GensData, GensData.AllValid N gs' →
      gs'.length ≤ k.factorial * (sIn + 1) → GensData.denote N gs' ≤ GensData.denote N gs →
        X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.Bgk)
    (hBgs : ∀ al : List ℕ, al.Nodup → al.length = k → (∀ a ∈ al, a < N - n) → ∀ b₁ b₂,
      X.B.call GroupOp.generate (N, giantGens X.O n (N, gs, d) al b₁ b₂)
        (giantSetStabModel X.O n (N, gs, d) al b₁ b₂) ≤ β.Bgs)
    (hBk3 : X.B.call GroupOp.kernel ((N, gs, d), baseWin n N) (kerModel X.O n (N, gs, d)) ≤
      β.Bk3)
    (hBo3 : X.B.call GroupOp.orbits (kerModel X.O n (N, gs, d), w)
      (krOrbits X.O n (N, gs, d) w) ≤ β.Bo3)
    (hBcr3 : X.B.call GroupOp.cosetReps ((N, gs, d), kerModel X.O n (N, gs, d))
      (kerReps X.O n (N, gs, d)) ≤ β.Bcr3)
    (hB3 : ∀ hs : GensData, GensData.AllValid N hs →
      hs.length ≤ (kerReps X.O n (N, gs, d)).length *
        (max s (kerModel X.O n (N, gs, d)).2.1.length + 1) →
      GensData.denote N hs ≤ GensData.denote N gs →
      X.B.call GroupOp.generate (N, hs) (X.O.run GroupOp.generate (N, hs)) ≤ β.Bgen3)
    -- Case 1
    (hBox : X.B.call GroupOp.orbits ((N, fxs, ex), baseWin n N)
      (Giant.baseOrbits X.O n N (N, fxs, ex)) ≤ β.Box)
    (hBoy : X.B.call GroupOp.orbits ((N, fys, ey), baseWin n N)
      (Giant.baseOrbits X.O n N (N, fys, ey)) ≤ β.Boy)
    (hBg1₁ : X.B.call GroupOp.generate
      (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
        (partGensD (N - n) (Giant.orbitPartModel X.O n N (N, fxs, ex))))).map
        (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
      (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
        (partGensD (N - n) (Giant.orbitPartModel X.O n N (N, fxs, ex)))))) ≤ β.Bg1₁)
    (hD₁ : ∀ gs' d' O', RDSet DV n N gs w L (Giant.g1Model X.O n (N, gs, d) (partOps (N - n))
        (Giant.orbitPartModel X.O n N (N, fxs, ex))).2.1 sIn gs' d' O' →
      RDOrbit X body DV n N w L st sIn Bd gs' d' O')
    -- Case 2a
    (hBg1₂ₐ : X.B.call GroupOp.generate
      (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
        ((setOps (N - n)).gens (m5Cs X.O n N (N, fxs, ex)).2))).map
        (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
      (Giant.g1Model X.O n (N, gs, d) (setOps (N - n)) (m5Cs X.O n N (N, fxs, ex)).2) ≤
        β.Bg1₂ₐ)
    (hBgen₂ₐ : ∀ gs' : GensData, GensData.AllValid N gs' → gs'.length ≤ sIn + 1 →
      GensData.denote N gs' ≤ GensData.denote N gs →
      X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.Bgen₂ₐ)
    (hBpb : ∀ gs', GensData.AllValid N gs' →
      gs'.length ≤ (sIn + 1) * (sIn + 1) + sIn + fxs.length → GensData.denote N gs' ≤ G₀ →
      X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.Bpb)
    (hBgm : ∀ (w' : WinData) (σ' : PermData) (gs' : GensData) (d' : D.denote),
      Giant.PbSubP DV G₀ xy w.1.length sIn (xy, w', σ', N, gs', d') →
      X.B.call GroupOp.generate (w'.1.length, GensData.restrictTo (WinData.pos N w') w'.1 gs')
        (X.O.run GroupOp.generate
          (w'.1.length, GensData.restrictTo (WinData.pos N w') w'.1 gs')) ≤ β.Bgm)
    (hBlift : ∀ (w' : WinData) (σ' : PermData) (gs' : GensData) (d' : D.denote),
      Giant.PbSubP DV G₀ xy w.1.length sIn (xy, w', σ', N, gs', d') → ∀ π' : PermData,
      X.B.call GroupOp.lift ((N, gs', d'), (w', π'))
        (X.O.run GroupOp.lift ((N, gs', d'), (w', π'))) ≤ β.Blift)
    (hBker : ∀ (w' : WinData) (σ' : PermData) (gs' : GensData) (d' : D.denote),
      Giant.PbSubP DV G₀ xy w.1.length sIn (xy, w', σ', N, gs', d') →
      X.B.call GroupOp.kernel ((N, gs', d'), w') (X.O.run GroupOp.kernel ((N, gs', d'), w')) ≤
        β.Bker)
    (hsK : ∀ (w' : WinData) (σ' : PermData) (gs' : GensData) (d' : D.denote),
      Giant.PbSubP DV G₀ xy w.1.length sIn (xy, w', σ', N, gs', d') →
      (X.O.run GroupOp.kernel ((N, gs', d'), w')).2.1.length ≤ β.sK)
    (hBgn : ∀ hs : GensData, GensData.AllValid N hs → hs.length ≤ β.sK + s →
      GensData.denote N hs ≤ G₀ →
      X.B.call GroupOp.generate (N, hs) (X.O.run GroupOp.generate (N, hs)) ≤ β.Bgn)
    -- Case 2b
    (hBg1₂ᵦ : ∀ X₀ : SoJTree.OutD,
      m5Leaf2b X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 = some X₀ →
      X.B.call GroupOp.generate
        (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (Case2b.outGensD (N - n) X₀))).map
          (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
        (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (Case2b.outGensD (N - n) X₀)))) ≤ β.Bg1₂ᵦ)
    (hBgen₂ᵦ : ∀ gs' : GensData, GensData.AllValid N gs' →
      gs'.length ≤ Case2b.c2bR N n (m5Cs X.O n N (N, fys, ey)).2.length
        (Case2b.degD X.O N n (N, fys, ey) (m5Cs X.O n N (N, fys, ey)).2 - 1)
        (Case2b.sojZ (N - n)) * (sIn + 1) →
      GensData.denote N gs' ≤ GensData.denote N gs →
      X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.Bgen₂ᵦ)
    (hD₂ᵦ : ∀ X₀, m5Leaf2b X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 = some X₀ →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (Case2b.outOps (N - n)) X₀).2.1 sIn gs' d' O' →
      RDOrbit X body DV n N w L st sIn Bd gs' d' O')
    -- Case 3
    (hBg1₃ : ∀ X₀ : SoJTree.OutD, Case3.C3First φ (strOn hC.le (xy.1.denote N)) (N - n) k
        (fixPtsD (m5Os X.O n N (N, fxs, ex))) X₀ →
      X.B.call GroupOp.generate
        (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (Case2b.outGensD (N - n) X₀))).map
          (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
        (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (Case2b.outGensD (N - n) X₀)))) ≤ β.Bg1₃)
    (hBgen₃ : ∀ gs' : GensData, GensData.AllValid N gs' →
      gs'.length ≤ Case3.c3R k (fixPtsD (m5Os X.O n N (N, fys, ey))).length
        (Case2b.sojZ (N - n)) * (sIn + 1) →
      GensData.denote N gs' ≤ GensData.denote N gs →
      X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.Bgen₃)
    (hD₃ : ∀ X₀, Case3.C3First φ (strOn hC.le (xy.1.denote N)) (N - n) k
        (fixPtsD (m5Os X.O n N (N, fxs, ex))) X₀ →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (Case2b.outOps (N - n)) X₀).2.1 sIn gs' d' O' →
      RDOrbit X body DV n N w L st sIn Bd gs' d' O')
    -- the coloured Johnson routes
    {uB Bg1J₂ Bg1J₃ : ℕ} (hLgJ : max (N - n) uB.factorial * (sIn + 1) ≤ Lg)
    (hBg1J₂ : ∀ X₀ : SoJTree.OutD,
      m5Leaf2b X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 = some X₀ →
      X.B.call GroupOp.generate
        (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (cjohnGensD (N - n) (cjFirst2bD N n (m5Cs X.O n N (N, fxs, ex)).2
            (Case2b.degD X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 - 1) X₀)))).map
          (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
        (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (cjohnGensD (N - n) (cjFirst2bD N n (m5Cs X.O n N (N, fxs, ex)).2
            (Case2b.degD X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 - 1) X₀))))) ≤
        Bg1J₂)
    (hLY₂ : Case2b.c2bR N n (m5Cs X.O n N (N, fys, ey)).2.length
      (Case2b.degD X.O N n (N, fys, ey) (m5Cs X.O n N (N, fys, ey)).2 - 1)
      (Case2b.sojZ (N - n)) * (sIn + 1) ≤ Lg)
    (hDJ₂ : ∀ X₀, m5Leaf2b X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 = some X₀ →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (cjohnOps (N - n))
          (cjFirst2bD N n (m5Cs X.O n N (N, fxs, ex)).2
            (Case2b.degD X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 - 1) X₀)).2.1 sIn
          gs' d' O' →
      RDOrbit X body DV n N w L (2, cjFirst2bD N n (m5Cs X.O n N (N, fxs, ex)).2
        (Case2b.degD X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 - 1) X₀) sIn Bd gs' d' O')
    (hu₂ : ∀ X₀, m5Leaf2b X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 = some X₀ →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (cjohnOps (N - n))
          (cjFirst2bD N n (m5Cs X.O n N (N, fxs, ex)).2
            (Case2b.degD X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 - 1) X₀)).2.1 sIn
          gs' d' O' →
      ((labJUD X₀.2.2.2.1.length (markArr (N - n) X₀.2.2.1) X₀.2.2.2.2.2 L O').getD
        (O'.headD 0) []).length ≤ uB)
    (hBg1J₃ : ∀ cXX X₀, Case3.ColChar φ (strOn hC.le (xy.1.denote N))
        (strOn hC.le (xy.1.denote N)) k (fixPtsD (m5Os X.O n N (N, fxs, ex))).length
        (fixPtsD (m5Os X.O n N (N, fxs, ex))) (fixPtsD (m5Os X.O n N (N, fxs, ex))) cXX →
      Case3.firstStructD (N - n) k (fixPtsD (m5Os X.O n N (N, fxs, ex)))
        (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fxs, ex))).length) = some X₀ → X₀.1 = 2 →
      X.B.call GroupOp.generate
        (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (cjohnGensD (N - n) (cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fxs, ex)))
            (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fxs, ex))).length) X₀)))).map
          (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
        (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (cjohnGensD (N - n) (cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fxs, ex)))
            (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fxs, ex))).length) X₀))))) ≤ Bg1J₃)
    (hLY₃ : Case3.c3R k (fixPtsD (m5Os X.O n N (N, fys, ey))).length (Case2b.sojZ (N - n)) *
      (sIn + 1) ≤ Lg)
    (hDJ₃ : ∀ cXX X₀, Case3.ColChar φ (strOn hC.le (xy.1.denote N))
        (strOn hC.le (xy.1.denote N)) k (fixPtsD (m5Os X.O n N (N, fxs, ex))).length
        (fixPtsD (m5Os X.O n N (N, fxs, ex))) (fixPtsD (m5Os X.O n N (N, fxs, ex))) cXX →
      Case3.firstStructD (N - n) k (fixPtsD (m5Os X.O n N (N, fxs, ex)))
        (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fxs, ex))).length) = some X₀ → X₀.1 = 2 →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (cjohnOps (N - n))
          (cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fxs, ex)))
            (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fxs, ex))).length) X₀)).2.1 sIn
          gs' d' O' →
      RDOrbit X body DV n N w L (2, cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fxs, ex)))
        (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fxs, ex))).length) X₀) sIn Bd gs' d' O')
    (hu₃ : ∀ cXX X₀, Case3.ColChar φ (strOn hC.le (xy.1.denote N))
        (strOn hC.le (xy.1.denote N)) k (fixPtsD (m5Os X.O n N (N, fxs, ex))).length
        (fixPtsD (m5Os X.O n N (N, fxs, ex))) (fixPtsD (m5Os X.O n N (N, fxs, ex))) cXX →
      Case3.firstStructD (N - n) k (fixPtsD (m5Os X.O n N (N, fxs, ex)))
        (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fxs, ex))).length) = some X₀ → X₀.1 = 2 →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (cjohnOps (N - n))
          (cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fxs, ex)))
            (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fxs, ex))).length) X₀)).2.1 sIn
          gs' d' O' →
      ((labJUD X₀.2.2.2.1.length (markArr (N - n) X₀.2.2.1) X₀.2.2.2.2.2 L O').getD
        (O'.headD 0) []).length ≤ uB) :
    ∃ (ans : AnswerData D) (ch : List (ℕ × Option ℕ)),
      RunsWithin X body (Main.m5DispatchCJ sub
          (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D) n₀ n L st k xy w
          (N, gs, d) (N, fxs, ex) (N, fys, ey) (m5CaseD X.O n N (N, fxs, ex))
          (m5CaseD X.O n N (N, fys, ey))) ans
        ((ch.map fun x => C x.1 x.2).sum +
          m5CKCJ X.O n N k (N, fxs, ex) (N, fys, ey) * C (n / k) none +
          m5CH X.O n N sIn w.1.length (N, fxs, ex) (N, fys, ey) * C (w.1.length / 2) none +
          m5WCJ X.O n N k s sIn Bgen Blift Bo Bk Bcr Bd (N, gs, d) (N, fxs, ex) (N, fys, ey)
            w.1.length β B.Bstab B.Btr B.Borb Bk'.Bgen Bk'.Borb Bk'.Bstab
            (fun M => (Bm M).Borb) (fun M => (Bm M).Bstab) (fun M => (Bm M).Btr) uB Bg1J₂ Bg1J₃) ∧
      AnsOK DV N (w.denote N) 1 (GensData.denote N gs) (xy.1.denote N) (xy.2.denote N) ans ∧
      (∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sIn) ∧
      ChildList w.1.length (m5CFCJ X.O n N k (N, fxs, ex) (N, fys, ey) uB)
        (StepChild w.1.length (N - n)) ch :=
  RunsWithin.m5DispatchCJ_jp hO hPre hI hφ halt hwS h5 hk hm12 B hgs hGG₀ Bk' hsk Bm hsub hCmono hs
    hB hLg hst β hFxv hFyv hFxs hFys hFxe hFye hBgP hBmem hBkA hBlA hBg hBgk hBgs hBk3 hBo3 hBcr3
    hB3 hBox hBoy hBg1₁ hD₁ hBg1₂ₐ hBgen₂ₐ hBpb hBgm hBlift hBker hsK hBgn
    (fun _ _ X₀ h _ => hBg1₂ᵦ X₀ h) hBgen₂ᵦ hD₂ᵦ (fun _ _ X₀ h _ => hBg1₃ X₀ h) hBgen₃ hD₃ hLgJ
    (fun _ _ X₀ h _ _ => hBg1J₂ X₀ h) hLY₂ (fun _ _ X₀ h _ _ => hDJ₂ X₀ h)
    (fun _ _ X₀ h _ _ => hu₂ X₀ h) (fun _ _ cXX X₀ h₁ h₂ h₃ _ => hBg1J₃ cXX X₀ h₁ h₂ h₃) hLY₃
    (fun _ _ cXX X₀ h₁ h₂ h₃ _ => hDJ₃ cXX X₀ h₁ h₂ h₃)
    (fun _ _ cXX X₀ h₁ h₂ h₃ _ => hu₃ cXX X₀ h₁ h₂ h₃)

end DispatchSpecCJ

/-! ### The dispatch with no stuck orbit -/

section NsDefsCJ

variable {D : Ty}

/-- **The work of the dispatch with coloured Johnson alignment and no stuck orbit**: as `m5Wns`
in Cases 1 and 2a; in Case 2b the test and the route it takes (14j-4's at factor `m`); in Case 3
the prefix and both routes (14j-4's at factor `m`, without the kernel reduction). -/
def m5WnsCJ (O : Oracle (groupSig D)) (n N k s sIn Bgen Blift Bo Bd : ℕ)
    (G Fx Fy : GroupData D.denote) (wl : ℕ) (β : M5Bounds) (Bst Btr Borb Bkg Bko Bks : ℕ)
    (Bo' Bs' Bt' : ℕ → ℕ) (uB Bg1J₂ Bg1J₃ : ℕ) : ℕ :=
  match m5Sel O n N Fx Fy with
  | 1 => Giant.case1Cost n N G.2.1.length
      (partGensD (N - n) (Giant.orbitPartModel O n N Fx)).length β.Box β.Boy β.BgP β.Bmem β.BkA
      β.BlA β.Bg1₁ Bgen (m5Wb N n wl s sIn (N - n) Bd Blift Bgen Bo 0) sIn + 16
  | 2 => c2aWork n N G.2.1.length ((setOps (N - n)).gens (m5Cs O n N Fx).2).length
      (m5Cs O n N Fx).2.length β.BgP β.Bmem β.BkA β.BlA β.Bg1₂ₐ β.Bgen₂ₐ sIn Bst Borb β.Bpb wl s
      β.sK β.Bgm β.Blift β.Bker β.Bgn + 30
  | 3 => c3Work n N sIn G.2.1.length k (fixPtsD (m5Os O n N Fx)).length
      (fixPtsD (m5Os O n N Fy)).length (Case2b.sojZ (N - n)) β.BgP β.Bmem β.BkA β.BlA β.Bg1₃
      β.Bgen₃ Bst Btr Borb Bkg Bko Bks β.Bgk β.Bgs wl
      (m5Wb N n wl s sIn (N - n) Bd Blift Bgen Bo 0) + wl + 3 +
      c3PreWork N n sIn k (fixPtsD (m5Os O n N Fx)).length (fixPtsD (m5Os O n N Fy)).length Bst
        Btr Borb Bkg Bko Bks β.Bgk β.BlA β.Bgs wl (Case2b.sojZ (N - n)) +
      c3CJCost n N sIn G.2.1.length k (fixPtsD (m5Os O n N Fx)).length
        (fixPtsD (m5Os O n N Fy)).length (Case2b.sojZ (N - n)) β.BgP β.Bmem β.BkA β.BlA Bg1J₃
        Bgen (m5Wb N n wl s sIn (max (N - n) uB.factorial) Bd Blift Bgen Bo 0) +
      2 * fixPtsCost (N - n) + 20
  | 4 => (match m5Leaf2b O N n Fx (m5Cs O n N Fx).2 with
      | some X₀ => c2bJTestCost N n sIn (m5Cs O n N Fx).2.length
          (Case2b.degD O N n Fx (m5Cs O n N Fx).2 - 1) Bst β.Bg (Case2b.sojZ (N - n)) Bo' Bs'
          Bt' + 1 +
          if c2bJD O N n Fx (m5Cs O n N Fx).2 then
            c2bCJCost n N sIn G.2.1.length (m5Cs O n N Fx).2.length (m5Cs O n N Fy).2.length
              (Case2b.degD O N n Fx (m5Cs O n N Fx).2 - 1)
              (cjohnGensD (N - n) (cjFirst2bD N n (m5Cs O n N Fx).2
                (Case2b.degD O N n Fx (m5Cs O n N Fx).2 - 1) X₀)).length Bst β.Bg
              (Case2b.sojZ (N - n)) β.BgP β.Bmem β.BkA β.BlA Bg1J₂ Bgen
              (m5Wb N n wl s sIn (max (N - n) uB.factorial) Bd Blift Bgen Bo 0) Bo' Bs' Bt'
          else
            Case2b.c2bCost n N sIn G.2.1.length (m5Cs O n N Fx).2.length
              (m5Cs O n N Fy).2.length (Case2b.degD O N n Fx (m5Cs O n N Fx).2 - 1)
              (Case2b.outGensD (N - n) X₀).length Bst β.Bg (Case2b.sojZ (N - n)) β.BgP β.Bmem
              β.BkA β.BlA β.Bg1₂ᵦ β.Bgen₂ᵦ (m5Wb N n wl s sIn (N - n) Bd Blift Bgen Bo 0) Bo'
              Bs' Bt'
      | none => 0) + 28
  | _ => 28

/-- **The factor of the dispatch's children list with no stuck orbit**: `m` in Case 1; in
Case 2b `c2bR · max(m, uB!)` for a Johnson leaf, `c2bR · m` otherwise; in Case 3
`c3R · max(m, uB!) + c3R · m`; none in Case 2a. -/
def m5CFnsCJ (O : Oracle (groupSig D)) (n N k : ℕ) (Fx Fy : GroupData D.denote) (uB : ℕ) : ℕ :=
  match m5Sel O n N Fx Fy with
  | 1 => 1 * (N - n)
  | 3 => Case3.c3R k (fixPtsD (m5Os O n N Fy)).length (Case2b.sojZ (N - n)) *
      max (N - n) uB.factorial +
      Case3.c3R k (fixPtsD (m5Os O n N Fy)).length (Case2b.sojZ (N - n)) * (N - n)
  | 4 => if c2bJD O N n Fx (m5Cs O n N Fx).2 then
      Case2b.c2bR N n (m5Cs O n N Fy).2.length (Case2b.degD O N n Fx (m5Cs O n N Fx).2 - 1)
        (Case2b.sojZ (N - n)) * max (N - n) uB.factorial
    else
      Case2b.c2bR N n (m5Cs O n N Fy).2.length (Case2b.degD O N n Fx (m5Cs O n N Fx).2 - 1)
        (Case2b.sojZ (N - n)) * (N - n)
  | _ => 0

end NsDefsCJ

section DispatchNsCJ

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}
  {sub : HInstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)}
  {C : ℕ → Option ℕ → ℕ} {s : ℕ} {xy : StrData × StrData} {w : WinData}
  {N : ℕ} {gs : GensData} {d : D.denote} {n₀ n : ℕ} {L : LabelData} {st : ℕ × CJData}
  {sIn Lg Blift Bgen Bo Bk Bcr Bd : ℕ}

/-- **The dispatch with no stuck orbit, with Case 2b's counts for `y` assumed only in Case 2b**
(stage 14j-6b-1, `PLAN-14.md` §14.11 item 5): as `RunsWithin.m5DispatchCJ_ns_jp`, with
`hBgen₂ᵦ` and `hLY₂` needed only when `y`'s case is Case 2b (tag `2`, not Case 2a), the only
case in which the dispatch uses them. There `y`'s degree is bounded under `TransitivityBound`
(`degD_le_T`), so the bounds hold at a depth bound; in Case 2a it may be close to `|Φ|`. -/
theorem RunsWithin.m5DispatchCJ_ns_jpC (hO : MeetsContractOn DV m5Ops X.O)
    (hPre : ∀ op x, m5Ops op → GroupPre DV op x → X.Pre op x)
    (hI : HInstValid DV (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D))
    {hC : CertSetting (GensData.denote N gs) n} {φ : strGroup hC →* Perm (Fin (N - n))}
    (hφ : IsPhi hC φ)
    (halt : alternatingGroup (Fin (N - n)) ≤ (baseHom _ n hC.base).range)
    (hwS : ∀ u : Fin N, u.val < n → u ∈ w.denote N)
    {k : ℕ} (h5 : 5 ≤ k) (hk : k + 2 ≤ N - n) (hm12 : 12 ≤ N - n)
    {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N sIn G₀) (hgs : gs.length ≤ sIn)
    (hGG₀ : GensData.denote N gs ≤ G₀) {sk : ℕ} (Bk' : BackendBounds X DV k sk ⊤)
    (hsk : sIn ≤ k * (sk + 1)) {sm : ℕ → ℕ} (Bm : ∀ M, BackendBounds X DV M (sm M) ⊤)
    (hsub : HSubSolves X body DV sub
      (fun J => SizeChild (max sIn (supTo sm (w.1.length / 2)))
          (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D) J ∧
        StepChild w.1.length (N - n) (J.winSize, J.baseOpt)) C s)
    (hCmono : ∀ a b, a ≤ b → C a none ≤ C b none) (hs : s ≤ sIn)
    (hB : RDBounds X DV n N sIn Lg Blift Bgen Bo Bk Bcr)
    (hLg : (N - n) * (sIn + 1) ≤ Lg) (hst : st.1 ≠ 2) (β : M5Bounds)
    -- the full groups
    {fxs fys : GensData} {ex ey : D.denote} (hFxv : GroupValid DV N fxs ex)
    (hFyv : GroupValid DV N fys ey) (hFxs : fxs.length ≤ sIn) (hFys : fys.length ≤ sIn)
    (hFxe : GensData.denote N fxs = m5Fmap hC φ k (xy.1.denote N))
    (hFye : GensData.denote N fys = m5Fmap hC φ k (xy.2.denote N))
    -- charges on `G`
    (hBgP : X.B.call GroupOp.generate (N - n, gs.map (baseD n N))
      (X.O.run GroupOp.generate (N - n, gs.map (baseD n N))) ≤ β.BgP)
    (hBmem : ∀ g : PermData, g.Valid (N - n) → X.B.call GroupOp.mem (pModel X.O n (N, gs, d), g)
      (X.O.run GroupOp.mem (pModel X.O n (N, gs, d), g)) ≤ β.Bmem)
    (hBkA : X.B.call GroupOp.kernel ((N, gs, d), baseWin n N) (kerModel X.O n (N, gs, d)) ≤
      β.BkA)
    (hBlA : ∀ π : PermData, X.B.call GroupOp.lift ((N, gs, d), (baseWin n N, π))
      (liftModel X.O n (N, gs, d) π) ≤ β.BlA)
    (hBg : ∀ M ≤ N - n, ∀ gs' : GensData, GensData.AllValid M gs' → gs'.length ≤ sIn →
      X.B.call GroupOp.generate (M, gs') (X.O.run GroupOp.generate (M, gs')) ≤ β.Bg)
    (hBgk : ∀ gs' : GensData, GensData.AllValid N gs' →
      gs'.length ≤ k.factorial * (sIn + 1) → GensData.denote N gs' ≤ GensData.denote N gs →
        X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.Bgk)
    (hBgs : ∀ al : List ℕ, al.Nodup → al.length = k → (∀ a ∈ al, a < N - n) → ∀ b₁ b₂,
      X.B.call GroupOp.generate (N, giantGens X.O n (N, gs, d) al b₁ b₂)
        (giantSetStabModel X.O n (N, gs, d) al b₁ b₂) ≤ β.Bgs)
    -- Case 1
    (hBox : X.B.call GroupOp.orbits ((N, fxs, ex), baseWin n N)
      (Giant.baseOrbits X.O n N (N, fxs, ex)) ≤ β.Box)
    (hBoy : X.B.call GroupOp.orbits ((N, fys, ey), baseWin n N)
      (Giant.baseOrbits X.O n N (N, fys, ey)) ≤ β.Boy)
    (hBg1₁ : X.B.call GroupOp.generate
      (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
        (partGensD (N - n) (Giant.orbitPartModel X.O n N (N, fxs, ex))))).map
        (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
      (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
        (partGensD (N - n) (Giant.orbitPartModel X.O n N (N, fxs, ex)))))) ≤ β.Bg1₁)
    (hD₁ : ∀ gs' d' O', RDSet DV n N gs w L (Giant.g1Model X.O n (N, gs, d) (partOps (N - n))
        (Giant.orbitPartModel X.O n N (N, fxs, ex))).2.1 sIn gs' d' O' →
      RDOrbit X body DV n N w L st sIn Bd gs' d' O')
    -- Case 2a
    (hBg1₂ₐ : X.B.call GroupOp.generate
      (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
        ((setOps (N - n)).gens (m5Cs X.O n N (N, fxs, ex)).2))).map
        (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
      (Giant.g1Model X.O n (N, gs, d) (setOps (N - n)) (m5Cs X.O n N (N, fxs, ex)).2) ≤
        β.Bg1₂ₐ)
    (hBgen₂ₐ : ∀ gs' : GensData, GensData.AllValid N gs' → gs'.length ≤ sIn + 1 →
      GensData.denote N gs' ≤ GensData.denote N gs →
      X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.Bgen₂ₐ)
    (hBpb : ∀ gs', GensData.AllValid N gs' →
      gs'.length ≤ (sIn + 1) * (sIn + 1) + sIn + fxs.length → GensData.denote N gs' ≤ G₀ →
      X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.Bpb)
    (hBgm : ∀ (w' : WinData) (σ' : PermData) (gs' : GensData) (d' : D.denote),
      Giant.PbSubP DV G₀ xy w.1.length sIn (xy, w', σ', N, gs', d') →
      X.B.call GroupOp.generate (w'.1.length, GensData.restrictTo (WinData.pos N w') w'.1 gs')
        (X.O.run GroupOp.generate
          (w'.1.length, GensData.restrictTo (WinData.pos N w') w'.1 gs')) ≤ β.Bgm)
    (hBlift : ∀ (w' : WinData) (σ' : PermData) (gs' : GensData) (d' : D.denote),
      Giant.PbSubP DV G₀ xy w.1.length sIn (xy, w', σ', N, gs', d') → ∀ π' : PermData,
      X.B.call GroupOp.lift ((N, gs', d'), (w', π'))
        (X.O.run GroupOp.lift ((N, gs', d'), (w', π'))) ≤ β.Blift)
    (hBker : ∀ (w' : WinData) (σ' : PermData) (gs' : GensData) (d' : D.denote),
      Giant.PbSubP DV G₀ xy w.1.length sIn (xy, w', σ', N, gs', d') →
      X.B.call GroupOp.kernel ((N, gs', d'), w') (X.O.run GroupOp.kernel ((N, gs', d'), w')) ≤
        β.Bker)
    (hsK : ∀ (w' : WinData) (σ' : PermData) (gs' : GensData) (d' : D.denote),
      Giant.PbSubP DV G₀ xy w.1.length sIn (xy, w', σ', N, gs', d') →
      (X.O.run GroupOp.kernel ((N, gs', d'), w')).2.1.length ≤ β.sK)
    (hBgn : ∀ hs : GensData, GensData.AllValid N hs → hs.length ≤ β.sK + s →
      GensData.denote N hs ≤ G₀ →
      X.B.call GroupOp.generate (N, hs) (X.O.run GroupOp.generate (N, hs)) ≤ β.Bgn)
    -- Case 2b
    (hBg1₂ᵦ :
      (m5Cs X.O n N (N, fxs, ex)).1 = 2 → m5IsA X.O n N (N, fxs, ex) = false → ∀ X₀ : SoJTree.OutD,
      m5Leaf2b X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 = some X₀ → X₀.1 ≠ 2 →
      X.B.call GroupOp.generate
        (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (Case2b.outGensD (N - n) X₀))).map
          (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
        (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (Case2b.outGensD (N - n) X₀)))) ≤ β.Bg1₂ᵦ)
    (hBgen₂ᵦ : (m5Cs X.O n N (N, fys, ey)).1 = 2 → m5IsA X.O n N (N, fys, ey) = false →
      ∀ gs' : GensData, GensData.AllValid N gs' →
      gs'.length ≤ Case2b.c2bR N n (m5Cs X.O n N (N, fys, ey)).2.length
        (Case2b.degD X.O N n (N, fys, ey) (m5Cs X.O n N (N, fys, ey)).2 - 1)
        (Case2b.sojZ (N - n)) * (sIn + 1) →
      GensData.denote N gs' ≤ GensData.denote N gs →
      X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.Bgen₂ᵦ)
    (hD₂ᵦ : ∀ X₀, m5Leaf2b X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 = some X₀ →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (Case2b.outOps (N - n)) X₀).2.1 sIn gs' d' O' →
      RDOrbit X body DV n N w L st sIn Bd gs' d' O')
    (hpart₂ᵦ : m5Sel X.O n N (N, fxs, ex) (N, fys, ey) = 4 → ∀ X₀,
      m5Leaf2b X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 = some X₀ → X₀.1 ≠ 2 →
      ∃ (p : CPart (Fin (N - n))) (t : ℕ), (Case2b.outOps (N - n)).dec X₀ = some (Sum.inl p) ∧
        IsColPart Finset.univ t p ∧ 4 * t ≤ 3 * (N - n))
    -- Case 3
    (hBg1₃ :
      (m5Cs X.O n N (N, fxs, ex)).1 ≠ 1 → (m5Cs X.O n N (N, fxs, ex)).1 ≠ 2 →
      ∀ X₀ : SoJTree.OutD, Case3.C3First φ (strOn hC.le (xy.1.denote N)) (N - n) k
        (fixPtsD (m5Os X.O n N (N, fxs, ex))) X₀ → X₀.1 ≠ 2 →
      X.B.call GroupOp.generate
        (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (Case2b.outGensD (N - n) X₀))).map
          (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
        (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (Case2b.outGensD (N - n) X₀)))) ≤ β.Bg1₃)
    (hBgen₃ : ∀ gs' : GensData, GensData.AllValid N gs' →
      gs'.length ≤ Case3.c3R k (fixPtsD (m5Os X.O n N (N, fys, ey))).length
        (Case2b.sojZ (N - n)) * (sIn + 1) →
      GensData.denote N gs' ≤ GensData.denote N gs →
      X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.Bgen₃)
    (hD₃ : ∀ X₀, Case3.C3First φ (strOn hC.le (xy.1.denote N)) (N - n) k
        (fixPtsD (m5Os X.O n N (N, fxs, ex))) X₀ →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (Case2b.outOps (N - n)) X₀).2.1 sIn gs' d' O' →
      RDOrbit X body DV n N w L st sIn Bd gs' d' O')
    (hnt₃ : m5Sel X.O n N (N, fxs, ex) (N, fys, ey) = 3 →
      ¬ Case3.C3Twins φ (strOn hC.le (xy.1.denote N)) k (fixPtsD (m5Os X.O n N (N, fxs, ex))))
    (hpart₃ : m5Sel X.O n N (N, fxs, ex) (N, fys, ey) = 3 → ∀ X₀,
      Case3.C3First φ (strOn hC.le (xy.1.denote N)) (N - n) k
        (fixPtsD (m5Os X.O n N (N, fxs, ex))) X₀ → X₀.1 ≠ 2 →
      ∃ (p : CPart (Fin (N - n))) (t : ℕ), (Case2b.outOps (N - n)).dec X₀ = some (Sum.inl p) ∧
        IsColPart Finset.univ t p ∧ 4 * t ≤ 3 * (N - n))
    -- the coloured Johnson routes
    {uB Bg1J₂ Bg1J₃ : ℕ} (hLgJ : max (N - n) uB.factorial * (sIn + 1) ≤ Lg)
    (hBg1J₂ :
      (m5Cs X.O n N (N, fxs, ex)).1 = 2 → m5IsA X.O n N (N, fxs, ex) = false → ∀ X₀ : SoJTree.OutD,
      m5Leaf2b X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 = some X₀ → X₀.1 = 2 →
      CJFacts (N - n) (cjFirst2bD N n (m5Cs X.O n N (N, fxs, ex)).2
          (Case2b.degD X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 - 1) X₀) →
      X.B.call GroupOp.generate
        (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (cjohnGensD (N - n) (cjFirst2bD N n (m5Cs X.O n N (N, fxs, ex)).2
            (Case2b.degD X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 - 1) X₀)))).map
          (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
        (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (cjohnGensD (N - n) (cjFirst2bD N n (m5Cs X.O n N (N, fxs, ex)).2
            (Case2b.degD X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 - 1) X₀))))) ≤
        Bg1J₂)
    (hLY₂ : (m5Cs X.O n N (N, fys, ey)).1 = 2 → m5IsA X.O n N (N, fys, ey) = false →
      Case2b.c2bR N n (m5Cs X.O n N (N, fys, ey)).2.length
      (Case2b.degD X.O N n (N, fys, ey) (m5Cs X.O n N (N, fys, ey)).2 - 1)
      (Case2b.sojZ (N - n)) * (sIn + 1) ≤ Lg)
    (hDJ₂ :
      (m5Cs X.O n N (N, fxs, ex)).1 = 2 → m5IsA X.O n N (N, fxs, ex) = false →
      ∀ X₀, m5Leaf2b X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 = some X₀ → X₀.1 = 2 →
      CJFacts (N - n) (cjFirst2bD N n (m5Cs X.O n N (N, fxs, ex)).2
          (Case2b.degD X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 - 1) X₀) →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (cjohnOps (N - n))
          (cjFirst2bD N n (m5Cs X.O n N (N, fxs, ex)).2
            (Case2b.degD X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 - 1) X₀)).2.1 sIn
          gs' d' O' →
      RDOrbit X body DV n N w L (2, cjFirst2bD N n (m5Cs X.O n N (N, fxs, ex)).2
        (Case2b.degD X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 - 1) X₀) sIn Bd gs' d' O')
    (hu₂ :
      (m5Cs X.O n N (N, fxs, ex)).1 = 2 → m5IsA X.O n N (N, fxs, ex) = false →
      ∀ X₀, m5Leaf2b X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 = some X₀ → X₀.1 = 2 →
      CJFacts (N - n) (cjFirst2bD N n (m5Cs X.O n N (N, fxs, ex)).2
          (Case2b.degD X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 - 1) X₀) →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (cjohnOps (N - n))
          (cjFirst2bD N n (m5Cs X.O n N (N, fxs, ex)).2
            (Case2b.degD X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 - 1) X₀)).2.1 sIn
          gs' d' O' →
      ((labJUD X₀.2.2.2.1.length (markArr (N - n) X₀.2.2.1) X₀.2.2.2.2.2 L O').getD
        (O'.headD 0) []).length ≤ uB)
    (hBg1J₃ :
      (m5Cs X.O n N (N, fxs, ex)).1 ≠ 1 → (m5Cs X.O n N (N, fxs, ex)).1 ≠ 2 →
      ∀ cXX X₀, Case3.ColChar φ (strOn hC.le (xy.1.denote N))
        (strOn hC.le (xy.1.denote N)) k (fixPtsD (m5Os X.O n N (N, fxs, ex))).length
        (fixPtsD (m5Os X.O n N (N, fxs, ex))) (fixPtsD (m5Os X.O n N (N, fxs, ex))) cXX →
      Case3.firstStructD (N - n) k (fixPtsD (m5Os X.O n N (N, fxs, ex)))
        (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fxs, ex))).length) = some X₀ → X₀.1 = 2 →
      CJFacts (N - n) (cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fxs, ex)))
          (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fxs, ex))).length) X₀) →
      X.B.call GroupOp.generate
        (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (cjohnGensD (N - n) (cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fxs, ex)))
            (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fxs, ex))).length) X₀)))).map
          (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
        (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (cjohnGensD (N - n) (cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fxs, ex)))
            (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fxs, ex))).length) X₀))))) ≤ Bg1J₃)
    (hLY₃ : Case3.c3R k (fixPtsD (m5Os X.O n N (N, fys, ey))).length (Case2b.sojZ (N - n)) *
      (sIn + 1) ≤ Lg)
    (hDJ₃ :
      (m5Cs X.O n N (N, fxs, ex)).1 ≠ 1 → (m5Cs X.O n N (N, fxs, ex)).1 ≠ 2 →
      ∀ cXX X₀, Case3.ColChar φ (strOn hC.le (xy.1.denote N))
        (strOn hC.le (xy.1.denote N)) k (fixPtsD (m5Os X.O n N (N, fxs, ex))).length
        (fixPtsD (m5Os X.O n N (N, fxs, ex))) (fixPtsD (m5Os X.O n N (N, fxs, ex))) cXX →
      Case3.firstStructD (N - n) k (fixPtsD (m5Os X.O n N (N, fxs, ex)))
        (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fxs, ex))).length) = some X₀ → X₀.1 = 2 →
      CJFacts (N - n) (cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fxs, ex)))
          (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fxs, ex))).length) X₀) →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (cjohnOps (N - n))
          (cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fxs, ex)))
            (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fxs, ex))).length) X₀)).2.1 sIn
          gs' d' O' →
      RDOrbit X body DV n N w L (2, cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fxs, ex)))
        (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fxs, ex))).length) X₀) sIn Bd gs' d' O')
    (hu₃ :
      (m5Cs X.O n N (N, fxs, ex)).1 ≠ 1 → (m5Cs X.O n N (N, fxs, ex)).1 ≠ 2 →
      ∀ cXX X₀, Case3.ColChar φ (strOn hC.le (xy.1.denote N))
        (strOn hC.le (xy.1.denote N)) k (fixPtsD (m5Os X.O n N (N, fxs, ex))).length
        (fixPtsD (m5Os X.O n N (N, fxs, ex))) (fixPtsD (m5Os X.O n N (N, fxs, ex))) cXX →
      Case3.firstStructD (N - n) k (fixPtsD (m5Os X.O n N (N, fxs, ex)))
        (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fxs, ex))).length) = some X₀ → X₀.1 = 2 →
      CJFacts (N - n) (cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fxs, ex)))
          (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fxs, ex))).length) X₀) →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (cjohnOps (N - n))
          (cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fxs, ex)))
            (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fxs, ex))).length) X₀)).2.1 sIn
          gs' d' O' →
      ((labJUD X₀.2.2.2.1.length (markArr (N - n) X₀.2.2.1) X₀.2.2.2.2.2 L O').getD
        (O'.headD 0) []).length ≤ uB) :
    ∃ (ans : AnswerData D) (ch : List (ℕ × Option ℕ)),
      RunsWithin X body (Main.m5DispatchCJ sub
          (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D) n₀ n L st k xy w
          (N, gs, d) (N, fxs, ex) (N, fys, ey) (m5CaseD X.O n N (N, fxs, ex))
          (m5CaseD X.O n N (N, fys, ey))) ans
        ((ch.map fun x => C x.1 x.2).sum +
          m5CKCJ X.O n N k (N, fxs, ex) (N, fys, ey) * C (n / k) none +
          m5CH X.O n N sIn w.1.length (N, fxs, ex) (N, fys, ey) * C (w.1.length / 2) none +
          m5WnsCJ X.O n N k s sIn Bgen Blift Bo Bd (N, gs, d) (N, fxs, ex) (N, fys, ey)
            w.1.length β B.Bstab B.Btr B.Borb Bk'.Bgen Bk'.Borb Bk'.Bstab
            (fun M => (Bm M).Borb) (fun M => (Bm M).Bstab) (fun M => (Bm M).Btr) uB Bg1J₂
            Bg1J₃) ∧
      AnsOK DV N (w.denote N) 1 (GensData.denote N gs) (xy.1.denote N) (xy.2.denote N) ans ∧
      (∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sIn) ∧
      ChildList w.1.length (m5CFnsCJ X.O n N k (N, fxs, ex) (N, fys, ey) uB)
        (StepChild w.1.length (N - n)) ch := by
  classical
  -- the sub-solver on the children of every case but 2a, and Case 2a's generator bound
  have hsubI : HSubSolves X body DV sub
      (fun J => SizeChild sIn (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D)
        J ∧ StepChild w.1.length (N - n) (J.winSize, J.baseOpt)) C s :=
    hsub.mono fun J hJ => ⟨hJ.1.mono (le_max_left _ _), hJ.2⟩
  have hgR : ∀ M ≤ w.1.length / 2, ∀ hs : GensData, GensData.AllValid M hs → hs.length ≤ sIn →
      (X.O.run GroupOp.generate (M, hs)).2.1.length ≤ max sIn (supTo sm (w.1.length / 2)) :=
    fun M hM hs hv _ =>
      ((Bm M).genOut hs hv le_top).trans ((le_supTo hM).trans (le_max_right _ _))
  -- the operations
  have hOc1 : MeetsContractOn DV Giant.case1Ops X.O := fun op x h hx => hO op x (Or.inl h) hx
  have hPc1 : ∀ op x, Giant.case1Ops op → GroupPre DV op x → X.Pre op x :=
    fun op x h hx => hPre op x (Or.inl h) hx
  have hO2a : MeetsContractOn DV Giant.c2aOps X.O :=
    fun op x h hx => hO op x (Or.inr (Or.inl h)) hx
  have hP2a : ∀ op x, Giant.c2aOps op → GroupPre DV op x → X.Pre op x :=
    fun op x h hx => hPre op x (Or.inr (Or.inl h)) hx
  have hOr : MeetsContractOn DV restrictOps X.O :=
    fun op x h hx => hO op x (Or.inr (Or.inr (Or.inl h))) hx
  have hPr : ∀ op x, restrictOps op → GroupPre DV op x → X.Pre op x :=
    fun op x h hx => hPre op x (Or.inr (Or.inr (Or.inl h))) hx
  have hO2b : MeetsContractOn DV Case2b.c2bOps X.O :=
    fun op x h hx => hO op x (Or.inr (Or.inr (Or.inr (Or.inl h)))) hx
  have hP2b : ∀ op x, Case2b.c2bOps op → GroupPre DV op x → X.Pre op x :=
    fun op x h hx => hPre op x (Or.inr (Or.inr (Or.inr (Or.inl h)))) hx
  have hO3 : MeetsContractOn DV Case3.c3Ops X.O :=
    fun op x h hx => hO op x (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))) hx
  have hP3 : ∀ op x, Case3.c3Ops op → GroupPre DV op x → X.Pre op x :=
    fun op x h hx => hPre op x (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))) hx
  have hOrd : MeetsContractOn DV rdOps X.O :=
    fun op x h hx => hO op x (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))) hx
  have hPrd : ∀ op x, rdOps op → GroupPre DV op x → X.Pre op x :=
    fun op x h hx => hPre op x (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))) hx
  have hOcs : MeetsContractOn DV m5CaseOps X.O := fun op x h hx =>
    hO op x (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))) hx
  have hPcs : ∀ op x, m5CaseOps op → GroupPre DV op x → X.Pre op x := fun op x h hx =>
    hPre op x (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))) hx
  -- the setting
  have hGv : GroupValid DV N gs d := hI.valid.group
  have hG : IsInvariant (GensData.denote N gs) (baseSet n N) := hC.base
  have hWG : IsInvariant (GensData.denote N gs) (w.denote N) := hI.valid.invariant
  have hFxG : GensData.denote N fxs ≤ GensData.denote N gs := hFxe ▸ m5Fmap_le hC φ k _
  have hFyG : GensData.denote N fys ≤ GensData.denote N gs := hFye ▸ m5Fmap_le hC φ k _
  have hFxi : IsInvariant (GensData.denote N fxs) (baseSet n N) := hG.mono hFxG
  have hFyi : IsInvariant (GensData.denote N fys) (baseSet n N) := hG.mono hFyG
  have hFx₀ : GensData.denote N fxs ≤ G₀ := hFxG.trans hGG₀
  have hFy₀ : GensData.denote N fys ≤ G₀ := hFyG.trans hGG₀
  obtain ⟨hosx, hAx, hngx⟩ := m5Case_spec hOcs hPcs B Bm hFxv hFxs hFx₀ hFxi
  obtain ⟨hosy, hAy, hngy⟩ := m5Case_spec hOcs hPcs B Bm hFyv hFys hFy₀ hFyi
  have hcx := Giant.caseD_spec hFxi hosx
  have hcy := Giant.caseD_spec hFyi hosy
  rw [m5Cs_eq] at hcx hcy
  by_cases h1 : (m5Cs X.O n N (N, fxs, ex)).1 = 1
  · -- Case 1
    have hsel : m5Sel X.O n N (N, fxs, ex) (N, fys, ey) = 1 := by simp [m5Sel, h1]
    obtain ⟨hc1a, hc1b⟩ := hcx.2.2.1.1 h1
    obtain ⟨ans, ch, hrun, hok, hg, hch⟩ := RunsWithin.m5Case1Prog_ns hOc1 hPc1 hOrd hPrd hI
      hG halt B hGG₀ le_rfl (m5Fmap_le hC φ k) (m5Fmap_loc hC φ k hwS) (m5Fmap_relabel hC φ k)
      hFxv hFyv hFxe hFye hFxi hc1a hc1b hBox hBoy hBgP hBmem hBkA hBlA hBg1₁ hsubI hB hs hLg
      (by omega) hst hD₁
    refine ⟨ans, ch, (m5Dispatch_run1_cj h1 hrun).mono ?_, hok, hg, ?_⟩
    · rw [m5CKCJ_of_ne (by rw [hsel]; decide), m5CH_of_ne (by rw [hsel]; decide)]
      have hW : m5WnsCJ X.O n N k s sIn Bgen Blift Bo Bd (N, gs, d) (N, fxs, ex) (N, fys, ey)
          w.1.length β B.Bstab B.Btr B.Borb Bk'.Bgen Bk'.Borb Bk'.Bstab
          (fun M => (Bm M).Borb) (fun M => (Bm M).Bstab) (fun M => (Bm M).Btr) uB Bg1J₂
            Bg1J₃ =
          Giant.case1Cost n N gs.length
            (partGensD (N - n) (Giant.orbitPartModel X.O n N (N, fxs, ex))).length β.Box β.Boy
            β.BgP β.Bmem β.BkA β.BlA β.Bg1₁ Bgen
            (m5Wb N n w.1.length s sIn (N - n) Bd Blift Bgen Bo 0) sIn + 16 := by
        unfold m5WnsCJ
        rw [hsel]
        rfl
      rw [hW]
      simp only [m5Wb]
      omega
    · have hF : m5CFnsCJ X.O n N k (N, fxs, ex) (N, fys, ey) uB = 1 * (N - n) := by
        unfold m5CFnsCJ
        rw [hsel]
        rfl
      rw [hF]
      exact hch
  by_cases h2 : (m5Cs X.O n N (N, fxs, ex)).1 = 2
  · obtain ⟨hΦxn, hΦxl, hΦx2, hΦxo⟩ := hcx.2.1 h2
    by_cases hok : ((m5Cs X.O n N (N, fys, ey)).1 == 2 &&
        (m5IsA X.O n N (N, fxs, ex) && m5IsA X.O n N (N, fys, ey) ||
          !m5IsA X.O n N (N, fxs, ex) && !m5IsA X.O n N (N, fys, ey))) = true
    · have h2y : (m5Cs X.O n N (N, fys, ey)).1 = 2 := by
        simp only [Bool.and_eq_true, beq_iff_eq] at hok
        exact hok.1
      obtain ⟨hΦyn, hΦyl, hΦy2, hΦyo⟩ := hcy.2.1 h2y
      by_cases hA : m5IsA X.O n N (N, fxs, ex) = true
      · -- Case 2a
        have hsel : m5Sel X.O n N (N, fxs, ex) (N, fys, ey) = 2 := by
          unfold m5Sel
          rw [if_neg' h1, if_pos' h2, if_pos' hok, if_pos' hA]
        obtain ⟨lab, t, he, ht, ht1, ht2⟩ := m5_labels (hI.hint L rfl).1 hGv.1 hI.valid.win
          hWG (hI.hint L rfl).2 hG
        obtain ⟨ans, hrun, hok', hg⟩ := RunsWithin.m5Case2aProg hO2a hP2a hOr hPr hI B hGG₀ hG
          halt (by omega) he ht ht1 ht2 (m5Fmap_le hC φ k) (m5Fmap_loc hC φ k hwS)
          (m5Fmap_relabel hC φ k) hFxv.1 hFxe
          (fun f hf => m5Fmap_matchesW hC φ k _ (fun u hu => hI.win_lt u.val hu) f (hFxe ▸ hf))
          hFye hFxi hFyi hΦxn hΦxl hΦx2 hΦxo hΦyn hΦyl hΦy2 hΦyo (hAx h2 hA) hBgP hBmem hBkA
          hBlA hBg1₂ₐ hBgen₂ₐ hBpb hgR hsub hCmono hBgm hBlift hBker hsK hBgn
        refine ⟨ans, [], (m5Dispatch_run2_cj h2 (m5_run2a_cj hok hA hrun)).mono ?_, hok',
          hg sIn (fun gs' hv hle => B.genOut gs' hv (hle.trans hGG₀)),
          ⟨by simp, by simp, by simp⟩⟩
        rw [m5CKCJ_of_ne (by rw [hsel]; decide)]
        have hH : m5CH X.O n N sIn w.1.length (N, fxs, ex) (N, fys, ey) =
            (sIn + 1) * w.1.length := by
          unfold m5CH
          rw [if_pos' hsel]
        have hW : m5WnsCJ X.O n N k s sIn Bgen Blift Bo Bd (N, gs, d) (N, fxs, ex)
            (N, fys, ey) w.1.length β B.Bstab B.Btr B.Borb Bk'.Bgen Bk'.Borb Bk'.Bstab
            (fun M => (Bm M).Borb) (fun M => (Bm M).Bstab) (fun M => (Bm M).Btr) uB Bg1J₂
            Bg1J₃ =
            c2aWork n N gs.length ((setOps (N - n)).gens (m5Cs X.O n N (N, fxs, ex)).2).length
              (m5Cs X.O n N (N, fxs, ex)).2.length β.BgP β.Bmem β.BkA β.BlA β.Bg1₂ₐ β.Bgen₂ₐ
              sIn B.Bstab B.Borb β.Bpb w.1.length s β.sK β.Bgm β.Blift β.Bker β.Bgn + 30 := by
          unfold m5WnsCJ
          rw [hsel]
          rfl
        rw [hH, hW]
        simp only [List.map_nil, List.sum_nil]
        omega
      · -- Case 2b
        have hA' : m5IsA X.O n N (N, fxs, ex) = false := by simpa using hA
        have hAy' : m5IsA X.O n N (N, fys, ey) = false := by
          have h' := hok
          rw [hA'] at h'
          simp only [Bool.and_eq_true, beq_iff_eq, Bool.false_and, Bool.not_false, Bool.true_and,
            Bool.false_or, Bool.not_eq_true'] at h'
          exact h'.2
        have hsel : m5Sel X.O n N (N, fxs, ex) (N, fys, ey) = 4 := by
          unfold m5Sel
          rw [if_neg' h1, if_pos' h2, if_pos' hok, if_neg' hA]
        have hOa : MeetsContractOn DV alignOps X.O := fun op x h hx => hO2b op x (Or.inr h) hx
        have hPa : ∀ op x, alignOps op → GroupPre DV op x → X.Pre op x :=
          fun op x h hx => hP2b op x (Or.inr h) hx
        have hO' : MeetsContractOn DV deriveOps X.O := fun op x h hx => hOrd op x (by
          rcases h with h | h | h | h <;> simp [rdOps, h]) hx
        obtain ⟨X₀, hX₀, ans, ch, hrun, hok', hg, hch⟩ := RunsWithin.m5Case2bCJProg_jp
          (F := N - n) (W6 := 0) hO2b hP2b hOrd hPrd hI B hGG₀ Bm hG halt
          (m5Fmap_loc hC φ k hwS) (m5Fmap_relabel hC φ k) hFxv hFyv hFxs hFys hFx₀ hFy₀ hFxe
          hFye hFxi hFyi hΦxn hΦxl hΦx2 hΦxo hΦyn hΦyl hΦy2 hΦyo (hngx h2 hA') (hngy h2y hAy')
          hBg hBgP hBmem hBkA hBlA (hBg1₂ᵦ h2 hA') (hBgen₂ᵦ h2y hAy') hsubI hB hs hLg (by omega)
          le_rfl
          (fun X₀ hX₀ _ => hD₂ᵦ X₀ hX₀)
          (fun _ _ _ => Or.inr fun gs' d' O' _ h5 => absurd h5 (rd_free_ne5 hst))
          (fun X₀ hX₀ hX₀2 => by
            have hXv := m5_leaf2b_valid hO2b hP2b B Bm hFxv hFxs hFx₀ hFxi hΦxn hΦxl hΦxo
              (hngx h2 hA') hX₀
            obtain ⟨p, t, hdec, hp, ht⟩ := hpart₂ᵦ hsel X₀ hX₀ hX₀2
            obtain ⟨-, hKb, hfix⟩ := ar_g1_facts hOa hPa B hI.valid.group hGG₀ hG halt
              (Case2b.outOps_spec (N - n)) hXv hBlA
            refine Or.inl (rd_ns_part hO' hst hKb hp (fun g => ?_) ht (by omega))
            have h := hfix g
            rw [hdec, Option.smul_some, Sum.smul_inl] at h
            exact Sum.inl_injective (Option.some_injective _ h))
          (hBg1J₂ h2 hA') (hLY₂ h2y hAy') hLgJ (by omega) (hDJ₂ h2 hA')
          (hu₂ h2 hA')
        refine ⟨ans, ch, (m5Dispatch_run2_cj h2 (m5_run2b_cj hok hA' hrun)).mono ?_, hok', hg, ?_⟩
        · rw [m5CKCJ_of_ne (by rw [hsel]; decide), m5CH_of_ne (by rw [hsel]; decide)]
          unfold m5WnsCJ
          rw [hsel]
          simp only
          rw [hX₀]
          simp only [m5Wb]
          omega
        · unfold m5CFnsCJ
          rw [hsel]
          exact hch
    · -- Case 2 for `x`, not in the same way for `y`: no isomorphism
      have hsel : m5Sel X.O n N (N, fxs, ex) (N, fys, ey) = 0 := by
        unfold m5Sel
        rw [if_neg' h1, if_pos' h2, if_neg' hok]
      refine ⟨none, [],
        (m5Dispatch_run2_cj h2 (m5_run2_none_cj (Bool.eq_false_iff.2 hok))).mono ?_, ?_,
        by simp, ⟨by simp, by simp, by simp⟩⟩
      · rw [m5CKCJ_of_ne (by rw [hsel]; decide), m5CH_of_ne (by rw [hsel]; decide)]
        have hW : m5WnsCJ X.O n N k s sIn Bgen Blift Bo Bd (N, gs, d) (N, fxs, ex)
            (N, fys, ey) w.1.length β B.Bstab B.Btr B.Borb Bk'.Bgen Bk'.Borb Bk'.Bstab
            (fun M => (Bm M).Borb) (fun M => (Bm M).Bstab) (fun M => (Bm M).Btr) uB Bg1J₂
            Bg1J₃ = 28 := by
          unfold m5WnsCJ
          rw [hsel]
          rfl
        rw [hW]
        simp
      · show iso (w.denote N) 1 (GensData.denote N gs) (xy.1.denote N) (xy.2.denote N) = ∅
        refine Set.eq_empty_of_forall_notMem fun g hg => hok ?_
        have hly := m5_large_iso hC φ k hwS hWG hg hFxe hFye hFxi hFyi (hcx.1.1 h2)
        have h2y : (m5Cs X.O n N (N, fys, ey)).1 = 2 := hcy.1.2 hly
        obtain ⟨hΦyn, hΦyl, hΦy2, hΦyo⟩ := hcy.2.1 h2y
        have hiffx := m5_isA_iff hOcs hPcs B Bm hFxv hFxs hFx₀ hFxi h2
        have hiffy := m5_isA_iff hOcs hPcs B Bm hFyv hFys hFy₀ hFyi h2y
        have htt := m5_tupTrans_iso hC φ k hwS hWG hg hFxe hFye hFxi hFyi hΦxn hΦxl hΦx2 hΦxo
          hΦyn hΦyl hΦy2 hΦyo
        have hAeq : m5IsA X.O n N (N, fxs, ex) = m5IsA X.O n N (N, fys, ey) := by
          rw [Bool.eq_iff_iff, ← hiffx, ← hiffy]
          exact htt.symm
        rw [hAeq, h2y]
        cases m5IsA X.O n N (N, fys, ey) <;> simp
  · -- Case 3
    have h3 : (m5Cs X.O n N (N, fxs, ex)).1 = 3 := by
      rcases m5_caseD_tag (N - n) (m5Os X.O n N (N, fxs, ex)) with h | h | h
      · exact absurd h h1
      · exact absurd h h2
      · exact h
    have hsel : m5Sel X.O n N (N, fxs, ex) (N, fys, ey) = 3 := by
      unfold m5Sel
      rw [if_neg' h1, if_neg' h2]
    obtain ⟨-, hc3b⟩ := hcx.2.2.2.1 h3
    obtain ⟨hVxn, hVxl, hVxF⟩ := fixPtsD_spec hFxi hosx
    obtain ⟨hVyn, hVyl, hVyF⟩ := fixPtsD_spec hFyi hosy
    rw [m5Os_eq] at hVxn hVxl hVxF hVyn hVyl hVyF
    have hlen := m5_fix_len hVxn hVxl hVxF
    have hm6 : 6 ≤ (fixPtsD (m5Os X.O n N (N, fxs, ex))).length := by
      omega
    have hVx2 : N - n ≤ 2 * (fixPtsD (m5Os X.O n N (N, fxs, ex))).length := by
      omega
    obtain ⟨ans, ch, hrun, hok', hg, hch⟩ := RunsWithin.m5Case3CJProg_jp hO3 hP3 hOrd hPrd hI hφ
      halt hwS (m5Fmap_loc hC φ k hwS) (m5Fmap_relabel hC φ k) hFxe hFye hFxi hFyi hVxl hVxn
      hVyl hVyn hVxF hVyF hm6 hVx2 h5 hk B hgs hGG₀ Bk' hsk hBgk hBlA hBgs hBgP hBmem hBkA hsubI
      hCmono hB hs
      (fun hcond => RunsWithin.m5Case3Prog_part hO3 hP3 hOrd hPrd hI hφ halt hwS
        (m5Fmap_loc hC φ k hwS) (m5Fmap_relabel hC φ k) hFxe hFye hFxi hFyi hVxl hVxn hVyl hVyn
        hVxF hVyF hm6 h5 hk B hgs hGG₀ Bk' hsk hBgk hBlA hBgs hBgP hBmem hBkA
        (fun X₀ hX₀ => hBg1₃ h1 h2 X₀ hX₀ (hcond X₀ hX₀)) hBgen₃ hsubI
        hCmono hB hs hLg hst hD₃ (hnt₃ hsel) (fun X₀ hX₀ => hpart₃ hsel X₀ hX₀ (hcond X₀ hX₀)))
      (hBg1J₃ h1 h2) hLY₃ hLgJ (by omega) (hDJ₃ h1 h2)
      (hu₃ h1 h2)
    obtain ⟨hbx, hox⟩ := m5_os_bounds hosx
    obtain ⟨hby, hoy⟩ := m5_os_bounds hosy
    refine ⟨ans, ch, (m5Dispatch_run3_cj h1 h2 hbx hox hby hoy hrun).mono ?_, hok', hg, ?_⟩
    · rw [m5CH_of_ne (by rw [hsel]; decide)]
      have hK : m5CKCJ X.O n N k (N, fxs, ex) (N, fys, ey) =
          2 * c3Count (fixPtsD (m5Os X.O n N (N, fxs, ex))).length k n := by
        unfold m5CKCJ
        rw [if_pos' hsel]
      rw [hK, Nat.mul_assoc]
      unfold m5WnsCJ
      rw [hsel]
      simp only [m5Wb]
      omega
    · unfold m5CFnsCJ
      rw [hsel]
      exact hch

/-- **M5's dispatch with coloured Johnson alignment and no stuck orbit.** Under the hypotheses
of `RunsWithin.m5Dispatch_ns`, with the partition hypotheses of Cases 2b and 3 (`hpart₂ᵦ`,
`hpart₃`) needed only for a first leaf or structure that is not a Johnson one, and the
hypotheses of the Johnson routes as in `RunsWithin.m5DispatchCJ`: no orbit is stuck in any
case. The children's factor is `m5CFnsCJ` and the work `m5WnsCJ`.

Stage 14j-5c (`PLAN-14.md` §14.8 item 4): the hypotheses of Cases 2b and 3 carry the premises
under which their routes use them: `x`'s case (Case 2b: tag `2`, not Case 2a; Case 3: tag neither
`1` nor `2`); for the partition routes (`hBg1₂ᵦ`, `hBg1₃`) a first leaf or structure that is not a
Johnson one (`X₀.1 ≠ 2`); for the Johnson routes (`hBg1J₂`, `hDJ₂`, `hu₂`, `hBg1J₃`, `hDJ₃`,
`hu₃`) a Johnson one (`X₀.1 = 2`) with the facts `CJFacts` of its coloured pair.
`RunsWithin.m5DispatchCJ_ns` follows from this one. -/
theorem RunsWithin.m5DispatchCJ_ns_jp (hO : MeetsContractOn DV m5Ops X.O)
    (hPre : ∀ op x, m5Ops op → GroupPre DV op x → X.Pre op x)
    (hI : HInstValid DV (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D))
    {hC : CertSetting (GensData.denote N gs) n} {φ : strGroup hC →* Perm (Fin (N - n))}
    (hφ : IsPhi hC φ)
    (halt : alternatingGroup (Fin (N - n)) ≤ (baseHom _ n hC.base).range)
    (hwS : ∀ u : Fin N, u.val < n → u ∈ w.denote N)
    {k : ℕ} (h5 : 5 ≤ k) (hk : k + 2 ≤ N - n) (hm12 : 12 ≤ N - n)
    {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N sIn G₀) (hgs : gs.length ≤ sIn)
    (hGG₀ : GensData.denote N gs ≤ G₀) {sk : ℕ} (Bk' : BackendBounds X DV k sk ⊤)
    (hsk : sIn ≤ k * (sk + 1)) {sm : ℕ → ℕ} (Bm : ∀ M, BackendBounds X DV M (sm M) ⊤)
    (hsub : HSubSolves X body DV sub
      (fun J => SizeChild (max sIn (supTo sm (w.1.length / 2)))
          (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D) J ∧
        StepChild w.1.length (N - n) (J.winSize, J.baseOpt)) C s)
    (hCmono : ∀ a b, a ≤ b → C a none ≤ C b none) (hs : s ≤ sIn)
    (hB : RDBounds X DV n N sIn Lg Blift Bgen Bo Bk Bcr)
    (hLg : (N - n) * (sIn + 1) ≤ Lg) (hst : st.1 ≠ 2) (β : M5Bounds)
    -- the full groups
    {fxs fys : GensData} {ex ey : D.denote} (hFxv : GroupValid DV N fxs ex)
    (hFyv : GroupValid DV N fys ey) (hFxs : fxs.length ≤ sIn) (hFys : fys.length ≤ sIn)
    (hFxe : GensData.denote N fxs = m5Fmap hC φ k (xy.1.denote N))
    (hFye : GensData.denote N fys = m5Fmap hC φ k (xy.2.denote N))
    -- charges on `G`
    (hBgP : X.B.call GroupOp.generate (N - n, gs.map (baseD n N))
      (X.O.run GroupOp.generate (N - n, gs.map (baseD n N))) ≤ β.BgP)
    (hBmem : ∀ g : PermData, g.Valid (N - n) → X.B.call GroupOp.mem (pModel X.O n (N, gs, d), g)
      (X.O.run GroupOp.mem (pModel X.O n (N, gs, d), g)) ≤ β.Bmem)
    (hBkA : X.B.call GroupOp.kernel ((N, gs, d), baseWin n N) (kerModel X.O n (N, gs, d)) ≤
      β.BkA)
    (hBlA : ∀ π : PermData, X.B.call GroupOp.lift ((N, gs, d), (baseWin n N, π))
      (liftModel X.O n (N, gs, d) π) ≤ β.BlA)
    (hBg : ∀ M ≤ N - n, ∀ gs' : GensData, GensData.AllValid M gs' → gs'.length ≤ sIn →
      X.B.call GroupOp.generate (M, gs') (X.O.run GroupOp.generate (M, gs')) ≤ β.Bg)
    (hBgk : ∀ gs' : GensData, GensData.AllValid N gs' →
      gs'.length ≤ k.factorial * (sIn + 1) → GensData.denote N gs' ≤ GensData.denote N gs →
        X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.Bgk)
    (hBgs : ∀ al : List ℕ, al.Nodup → al.length = k → (∀ a ∈ al, a < N - n) → ∀ b₁ b₂,
      X.B.call GroupOp.generate (N, giantGens X.O n (N, gs, d) al b₁ b₂)
        (giantSetStabModel X.O n (N, gs, d) al b₁ b₂) ≤ β.Bgs)
    -- Case 1
    (hBox : X.B.call GroupOp.orbits ((N, fxs, ex), baseWin n N)
      (Giant.baseOrbits X.O n N (N, fxs, ex)) ≤ β.Box)
    (hBoy : X.B.call GroupOp.orbits ((N, fys, ey), baseWin n N)
      (Giant.baseOrbits X.O n N (N, fys, ey)) ≤ β.Boy)
    (hBg1₁ : X.B.call GroupOp.generate
      (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
        (partGensD (N - n) (Giant.orbitPartModel X.O n N (N, fxs, ex))))).map
        (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
      (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
        (partGensD (N - n) (Giant.orbitPartModel X.O n N (N, fxs, ex)))))) ≤ β.Bg1₁)
    (hD₁ : ∀ gs' d' O', RDSet DV n N gs w L (Giant.g1Model X.O n (N, gs, d) (partOps (N - n))
        (Giant.orbitPartModel X.O n N (N, fxs, ex))).2.1 sIn gs' d' O' →
      RDOrbit X body DV n N w L st sIn Bd gs' d' O')
    -- Case 2a
    (hBg1₂ₐ : X.B.call GroupOp.generate
      (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
        ((setOps (N - n)).gens (m5Cs X.O n N (N, fxs, ex)).2))).map
        (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
      (Giant.g1Model X.O n (N, gs, d) (setOps (N - n)) (m5Cs X.O n N (N, fxs, ex)).2) ≤
        β.Bg1₂ₐ)
    (hBgen₂ₐ : ∀ gs' : GensData, GensData.AllValid N gs' → gs'.length ≤ sIn + 1 →
      GensData.denote N gs' ≤ GensData.denote N gs →
      X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.Bgen₂ₐ)
    (hBpb : ∀ gs', GensData.AllValid N gs' →
      gs'.length ≤ (sIn + 1) * (sIn + 1) + sIn + fxs.length → GensData.denote N gs' ≤ G₀ →
      X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.Bpb)
    (hBgm : ∀ (w' : WinData) (σ' : PermData) (gs' : GensData) (d' : D.denote),
      Giant.PbSubP DV G₀ xy w.1.length sIn (xy, w', σ', N, gs', d') →
      X.B.call GroupOp.generate (w'.1.length, GensData.restrictTo (WinData.pos N w') w'.1 gs')
        (X.O.run GroupOp.generate
          (w'.1.length, GensData.restrictTo (WinData.pos N w') w'.1 gs')) ≤ β.Bgm)
    (hBlift : ∀ (w' : WinData) (σ' : PermData) (gs' : GensData) (d' : D.denote),
      Giant.PbSubP DV G₀ xy w.1.length sIn (xy, w', σ', N, gs', d') → ∀ π' : PermData,
      X.B.call GroupOp.lift ((N, gs', d'), (w', π'))
        (X.O.run GroupOp.lift ((N, gs', d'), (w', π'))) ≤ β.Blift)
    (hBker : ∀ (w' : WinData) (σ' : PermData) (gs' : GensData) (d' : D.denote),
      Giant.PbSubP DV G₀ xy w.1.length sIn (xy, w', σ', N, gs', d') →
      X.B.call GroupOp.kernel ((N, gs', d'), w') (X.O.run GroupOp.kernel ((N, gs', d'), w')) ≤
        β.Bker)
    (hsK : ∀ (w' : WinData) (σ' : PermData) (gs' : GensData) (d' : D.denote),
      Giant.PbSubP DV G₀ xy w.1.length sIn (xy, w', σ', N, gs', d') →
      (X.O.run GroupOp.kernel ((N, gs', d'), w')).2.1.length ≤ β.sK)
    (hBgn : ∀ hs : GensData, GensData.AllValid N hs → hs.length ≤ β.sK + s →
      GensData.denote N hs ≤ G₀ →
      X.B.call GroupOp.generate (N, hs) (X.O.run GroupOp.generate (N, hs)) ≤ β.Bgn)
    -- Case 2b
    (hBg1₂ᵦ :
      (m5Cs X.O n N (N, fxs, ex)).1 = 2 → m5IsA X.O n N (N, fxs, ex) = false → ∀ X₀ : SoJTree.OutD,
      m5Leaf2b X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 = some X₀ → X₀.1 ≠ 2 →
      X.B.call GroupOp.generate
        (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (Case2b.outGensD (N - n) X₀))).map
          (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
        (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (Case2b.outGensD (N - n) X₀)))) ≤ β.Bg1₂ᵦ)
    (hBgen₂ᵦ : ∀ gs' : GensData, GensData.AllValid N gs' →
      gs'.length ≤ Case2b.c2bR N n (m5Cs X.O n N (N, fys, ey)).2.length
        (Case2b.degD X.O N n (N, fys, ey) (m5Cs X.O n N (N, fys, ey)).2 - 1)
        (Case2b.sojZ (N - n)) * (sIn + 1) →
      GensData.denote N gs' ≤ GensData.denote N gs →
      X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.Bgen₂ᵦ)
    (hD₂ᵦ : ∀ X₀, m5Leaf2b X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 = some X₀ →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (Case2b.outOps (N - n)) X₀).2.1 sIn gs' d' O' →
      RDOrbit X body DV n N w L st sIn Bd gs' d' O')
    (hpart₂ᵦ : m5Sel X.O n N (N, fxs, ex) (N, fys, ey) = 4 → ∀ X₀,
      m5Leaf2b X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 = some X₀ → X₀.1 ≠ 2 →
      ∃ (p : CPart (Fin (N - n))) (t : ℕ), (Case2b.outOps (N - n)).dec X₀ = some (Sum.inl p) ∧
        IsColPart Finset.univ t p ∧ 4 * t ≤ 3 * (N - n))
    -- Case 3
    (hBg1₃ :
      (m5Cs X.O n N (N, fxs, ex)).1 ≠ 1 → (m5Cs X.O n N (N, fxs, ex)).1 ≠ 2 →
      ∀ X₀ : SoJTree.OutD, Case3.C3First φ (strOn hC.le (xy.1.denote N)) (N - n) k
        (fixPtsD (m5Os X.O n N (N, fxs, ex))) X₀ → X₀.1 ≠ 2 →
      X.B.call GroupOp.generate
        (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (Case2b.outGensD (N - n) X₀))).map
          (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
        (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (Case2b.outGensD (N - n) X₀)))) ≤ β.Bg1₃)
    (hBgen₃ : ∀ gs' : GensData, GensData.AllValid N gs' →
      gs'.length ≤ Case3.c3R k (fixPtsD (m5Os X.O n N (N, fys, ey))).length
        (Case2b.sojZ (N - n)) * (sIn + 1) →
      GensData.denote N gs' ≤ GensData.denote N gs →
      X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.Bgen₃)
    (hD₃ : ∀ X₀, Case3.C3First φ (strOn hC.le (xy.1.denote N)) (N - n) k
        (fixPtsD (m5Os X.O n N (N, fxs, ex))) X₀ →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (Case2b.outOps (N - n)) X₀).2.1 sIn gs' d' O' →
      RDOrbit X body DV n N w L st sIn Bd gs' d' O')
    (hnt₃ : m5Sel X.O n N (N, fxs, ex) (N, fys, ey) = 3 →
      ¬ Case3.C3Twins φ (strOn hC.le (xy.1.denote N)) k (fixPtsD (m5Os X.O n N (N, fxs, ex))))
    (hpart₃ : m5Sel X.O n N (N, fxs, ex) (N, fys, ey) = 3 → ∀ X₀,
      Case3.C3First φ (strOn hC.le (xy.1.denote N)) (N - n) k
        (fixPtsD (m5Os X.O n N (N, fxs, ex))) X₀ → X₀.1 ≠ 2 →
      ∃ (p : CPart (Fin (N - n))) (t : ℕ), (Case2b.outOps (N - n)).dec X₀ = some (Sum.inl p) ∧
        IsColPart Finset.univ t p ∧ 4 * t ≤ 3 * (N - n))
    -- the coloured Johnson routes
    {uB Bg1J₂ Bg1J₃ : ℕ} (hLgJ : max (N - n) uB.factorial * (sIn + 1) ≤ Lg)
    (hBg1J₂ :
      (m5Cs X.O n N (N, fxs, ex)).1 = 2 → m5IsA X.O n N (N, fxs, ex) = false → ∀ X₀ : SoJTree.OutD,
      m5Leaf2b X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 = some X₀ → X₀.1 = 2 →
      CJFacts (N - n) (cjFirst2bD N n (m5Cs X.O n N (N, fxs, ex)).2
          (Case2b.degD X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 - 1) X₀) →
      X.B.call GroupOp.generate
        (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (cjohnGensD (N - n) (cjFirst2bD N n (m5Cs X.O n N (N, fxs, ex)).2
            (Case2b.degD X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 - 1) X₀)))).map
          (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
        (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (cjohnGensD (N - n) (cjFirst2bD N n (m5Cs X.O n N (N, fxs, ex)).2
            (Case2b.degD X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 - 1) X₀))))) ≤
        Bg1J₂)
    (hLY₂ : Case2b.c2bR N n (m5Cs X.O n N (N, fys, ey)).2.length
      (Case2b.degD X.O N n (N, fys, ey) (m5Cs X.O n N (N, fys, ey)).2 - 1)
      (Case2b.sojZ (N - n)) * (sIn + 1) ≤ Lg)
    (hDJ₂ :
      (m5Cs X.O n N (N, fxs, ex)).1 = 2 → m5IsA X.O n N (N, fxs, ex) = false →
      ∀ X₀, m5Leaf2b X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 = some X₀ → X₀.1 = 2 →
      CJFacts (N - n) (cjFirst2bD N n (m5Cs X.O n N (N, fxs, ex)).2
          (Case2b.degD X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 - 1) X₀) →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (cjohnOps (N - n))
          (cjFirst2bD N n (m5Cs X.O n N (N, fxs, ex)).2
            (Case2b.degD X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 - 1) X₀)).2.1 sIn
          gs' d' O' →
      RDOrbit X body DV n N w L (2, cjFirst2bD N n (m5Cs X.O n N (N, fxs, ex)).2
        (Case2b.degD X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 - 1) X₀) sIn Bd gs' d' O')
    (hu₂ :
      (m5Cs X.O n N (N, fxs, ex)).1 = 2 → m5IsA X.O n N (N, fxs, ex) = false →
      ∀ X₀, m5Leaf2b X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 = some X₀ → X₀.1 = 2 →
      CJFacts (N - n) (cjFirst2bD N n (m5Cs X.O n N (N, fxs, ex)).2
          (Case2b.degD X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 - 1) X₀) →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (cjohnOps (N - n))
          (cjFirst2bD N n (m5Cs X.O n N (N, fxs, ex)).2
            (Case2b.degD X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 - 1) X₀)).2.1 sIn
          gs' d' O' →
      ((labJUD X₀.2.2.2.1.length (markArr (N - n) X₀.2.2.1) X₀.2.2.2.2.2 L O').getD
        (O'.headD 0) []).length ≤ uB)
    (hBg1J₃ :
      (m5Cs X.O n N (N, fxs, ex)).1 ≠ 1 → (m5Cs X.O n N (N, fxs, ex)).1 ≠ 2 →
      ∀ cXX X₀, Case3.ColChar φ (strOn hC.le (xy.1.denote N))
        (strOn hC.le (xy.1.denote N)) k (fixPtsD (m5Os X.O n N (N, fxs, ex))).length
        (fixPtsD (m5Os X.O n N (N, fxs, ex))) (fixPtsD (m5Os X.O n N (N, fxs, ex))) cXX →
      Case3.firstStructD (N - n) k (fixPtsD (m5Os X.O n N (N, fxs, ex)))
        (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fxs, ex))).length) = some X₀ → X₀.1 = 2 →
      CJFacts (N - n) (cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fxs, ex)))
          (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fxs, ex))).length) X₀) →
      X.B.call GroupOp.generate
        (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (cjohnGensD (N - n) (cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fxs, ex)))
            (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fxs, ex))).length) X₀)))).map
          (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
        (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (cjohnGensD (N - n) (cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fxs, ex)))
            (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fxs, ex))).length) X₀))))) ≤ Bg1J₃)
    (hLY₃ : Case3.c3R k (fixPtsD (m5Os X.O n N (N, fys, ey))).length (Case2b.sojZ (N - n)) *
      (sIn + 1) ≤ Lg)
    (hDJ₃ :
      (m5Cs X.O n N (N, fxs, ex)).1 ≠ 1 → (m5Cs X.O n N (N, fxs, ex)).1 ≠ 2 →
      ∀ cXX X₀, Case3.ColChar φ (strOn hC.le (xy.1.denote N))
        (strOn hC.le (xy.1.denote N)) k (fixPtsD (m5Os X.O n N (N, fxs, ex))).length
        (fixPtsD (m5Os X.O n N (N, fxs, ex))) (fixPtsD (m5Os X.O n N (N, fxs, ex))) cXX →
      Case3.firstStructD (N - n) k (fixPtsD (m5Os X.O n N (N, fxs, ex)))
        (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fxs, ex))).length) = some X₀ → X₀.1 = 2 →
      CJFacts (N - n) (cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fxs, ex)))
          (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fxs, ex))).length) X₀) →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (cjohnOps (N - n))
          (cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fxs, ex)))
            (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fxs, ex))).length) X₀)).2.1 sIn
          gs' d' O' →
      RDOrbit X body DV n N w L (2, cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fxs, ex)))
        (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fxs, ex))).length) X₀) sIn Bd gs' d' O')
    (hu₃ :
      (m5Cs X.O n N (N, fxs, ex)).1 ≠ 1 → (m5Cs X.O n N (N, fxs, ex)).1 ≠ 2 →
      ∀ cXX X₀, Case3.ColChar φ (strOn hC.le (xy.1.denote N))
        (strOn hC.le (xy.1.denote N)) k (fixPtsD (m5Os X.O n N (N, fxs, ex))).length
        (fixPtsD (m5Os X.O n N (N, fxs, ex))) (fixPtsD (m5Os X.O n N (N, fxs, ex))) cXX →
      Case3.firstStructD (N - n) k (fixPtsD (m5Os X.O n N (N, fxs, ex)))
        (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fxs, ex))).length) = some X₀ → X₀.1 = 2 →
      CJFacts (N - n) (cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fxs, ex)))
          (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fxs, ex))).length) X₀) →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (cjohnOps (N - n))
          (cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fxs, ex)))
            (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fxs, ex))).length) X₀)).2.1 sIn
          gs' d' O' →
      ((labJUD X₀.2.2.2.1.length (markArr (N - n) X₀.2.2.1) X₀.2.2.2.2.2 L O').getD
        (O'.headD 0) []).length ≤ uB) :
    ∃ (ans : AnswerData D) (ch : List (ℕ × Option ℕ)),
      RunsWithin X body (Main.m5DispatchCJ sub
          (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D) n₀ n L st k xy w
          (N, gs, d) (N, fxs, ex) (N, fys, ey) (m5CaseD X.O n N (N, fxs, ex))
          (m5CaseD X.O n N (N, fys, ey))) ans
        ((ch.map fun x => C x.1 x.2).sum +
          m5CKCJ X.O n N k (N, fxs, ex) (N, fys, ey) * C (n / k) none +
          m5CH X.O n N sIn w.1.length (N, fxs, ex) (N, fys, ey) * C (w.1.length / 2) none +
          m5WnsCJ X.O n N k s sIn Bgen Blift Bo Bd (N, gs, d) (N, fxs, ex) (N, fys, ey)
            w.1.length β B.Bstab B.Btr B.Borb Bk'.Bgen Bk'.Borb Bk'.Bstab
            (fun M => (Bm M).Borb) (fun M => (Bm M).Bstab) (fun M => (Bm M).Btr) uB Bg1J₂
            Bg1J₃) ∧
      AnsOK DV N (w.denote N) 1 (GensData.denote N gs) (xy.1.denote N) (xy.2.denote N) ans ∧
      (∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sIn) ∧
      ChildList w.1.length (m5CFnsCJ X.O n N k (N, fxs, ex) (N, fys, ey) uB)
        (StepChild w.1.length (N - n)) ch :=
  RunsWithin.m5DispatchCJ_ns_jpC hO hPre hI hφ halt hwS h5 hk hm12 B hgs hGG₀ Bk' hsk Bm hsub hCmono
    hs hB hLg hst β hFxv hFyv hFxs hFys hFxe hFye hBgP hBmem hBkA hBlA hBg hBgk hBgs hBox hBoy hBg1₁
    hD₁ hBg1₂ₐ hBgen₂ₐ hBpb hBgm hBlift hBker hsK hBgn hBg1₂ᵦ (fun _ _ => hBgen₂ᵦ) hD₂ᵦ hpart₂ᵦ
    hBg1₃ hBgen₃ hD₃ hnt₃ hpart₃ hLgJ hBg1J₂ (fun _ _ => hLY₂) hDJ₂ hu₂ hBg1J₃ hLY₃ hDJ₃ hu₃

/-- `RunsWithin.m5DispatchCJ_ns_jp` with Case 2b's Johnson-route hypotheses stated for every first
leaf. -/
theorem RunsWithin.m5DispatchCJ_ns (hO : MeetsContractOn DV m5Ops X.O)
    (hPre : ∀ op x, m5Ops op → GroupPre DV op x → X.Pre op x)
    (hI : HInstValid DV (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D))
    {hC : CertSetting (GensData.denote N gs) n} {φ : strGroup hC →* Perm (Fin (N - n))}
    (hφ : IsPhi hC φ)
    (halt : alternatingGroup (Fin (N - n)) ≤ (baseHom _ n hC.base).range)
    (hwS : ∀ u : Fin N, u.val < n → u ∈ w.denote N)
    {k : ℕ} (h5 : 5 ≤ k) (hk : k + 2 ≤ N - n) (hm12 : 12 ≤ N - n)
    {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N sIn G₀) (hgs : gs.length ≤ sIn)
    (hGG₀ : GensData.denote N gs ≤ G₀) {sk : ℕ} (Bk' : BackendBounds X DV k sk ⊤)
    (hsk : sIn ≤ k * (sk + 1)) {sm : ℕ → ℕ} (Bm : ∀ M, BackendBounds X DV M (sm M) ⊤)
    (hsub : HSubSolves X body DV sub
      (fun J => SizeChild (max sIn (supTo sm (w.1.length / 2)))
          (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D) J ∧
        StepChild w.1.length (N - n) (J.winSize, J.baseOpt)) C s)
    (hCmono : ∀ a b, a ≤ b → C a none ≤ C b none) (hs : s ≤ sIn)
    (hB : RDBounds X DV n N sIn Lg Blift Bgen Bo Bk Bcr)
    (hLg : (N - n) * (sIn + 1) ≤ Lg) (hst : st.1 ≠ 2) (β : M5Bounds)
    -- the full groups
    {fxs fys : GensData} {ex ey : D.denote} (hFxv : GroupValid DV N fxs ex)
    (hFyv : GroupValid DV N fys ey) (hFxs : fxs.length ≤ sIn) (hFys : fys.length ≤ sIn)
    (hFxe : GensData.denote N fxs = m5Fmap hC φ k (xy.1.denote N))
    (hFye : GensData.denote N fys = m5Fmap hC φ k (xy.2.denote N))
    -- charges on `G`
    (hBgP : X.B.call GroupOp.generate (N - n, gs.map (baseD n N))
      (X.O.run GroupOp.generate (N - n, gs.map (baseD n N))) ≤ β.BgP)
    (hBmem : ∀ g : PermData, g.Valid (N - n) → X.B.call GroupOp.mem (pModel X.O n (N, gs, d), g)
      (X.O.run GroupOp.mem (pModel X.O n (N, gs, d), g)) ≤ β.Bmem)
    (hBkA : X.B.call GroupOp.kernel ((N, gs, d), baseWin n N) (kerModel X.O n (N, gs, d)) ≤
      β.BkA)
    (hBlA : ∀ π : PermData, X.B.call GroupOp.lift ((N, gs, d), (baseWin n N, π))
      (liftModel X.O n (N, gs, d) π) ≤ β.BlA)
    (hBg : ∀ M ≤ N - n, ∀ gs' : GensData, GensData.AllValid M gs' → gs'.length ≤ sIn →
      X.B.call GroupOp.generate (M, gs') (X.O.run GroupOp.generate (M, gs')) ≤ β.Bg)
    (hBgk : ∀ gs' : GensData, GensData.AllValid N gs' →
      gs'.length ≤ k.factorial * (sIn + 1) → GensData.denote N gs' ≤ GensData.denote N gs →
        X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.Bgk)
    (hBgs : ∀ al : List ℕ, al.Nodup → al.length = k → (∀ a ∈ al, a < N - n) → ∀ b₁ b₂,
      X.B.call GroupOp.generate (N, giantGens X.O n (N, gs, d) al b₁ b₂)
        (giantSetStabModel X.O n (N, gs, d) al b₁ b₂) ≤ β.Bgs)
    -- Case 1
    (hBox : X.B.call GroupOp.orbits ((N, fxs, ex), baseWin n N)
      (Giant.baseOrbits X.O n N (N, fxs, ex)) ≤ β.Box)
    (hBoy : X.B.call GroupOp.orbits ((N, fys, ey), baseWin n N)
      (Giant.baseOrbits X.O n N (N, fys, ey)) ≤ β.Boy)
    (hBg1₁ : X.B.call GroupOp.generate
      (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
        (partGensD (N - n) (Giant.orbitPartModel X.O n N (N, fxs, ex))))).map
        (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
      (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
        (partGensD (N - n) (Giant.orbitPartModel X.O n N (N, fxs, ex)))))) ≤ β.Bg1₁)
    (hD₁ : ∀ gs' d' O', RDSet DV n N gs w L (Giant.g1Model X.O n (N, gs, d) (partOps (N - n))
        (Giant.orbitPartModel X.O n N (N, fxs, ex))).2.1 sIn gs' d' O' →
      RDOrbit X body DV n N w L st sIn Bd gs' d' O')
    -- Case 2a
    (hBg1₂ₐ : X.B.call GroupOp.generate
      (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
        ((setOps (N - n)).gens (m5Cs X.O n N (N, fxs, ex)).2))).map
        (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
      (Giant.g1Model X.O n (N, gs, d) (setOps (N - n)) (m5Cs X.O n N (N, fxs, ex)).2) ≤
        β.Bg1₂ₐ)
    (hBgen₂ₐ : ∀ gs' : GensData, GensData.AllValid N gs' → gs'.length ≤ sIn + 1 →
      GensData.denote N gs' ≤ GensData.denote N gs →
      X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.Bgen₂ₐ)
    (hBpb : ∀ gs', GensData.AllValid N gs' →
      gs'.length ≤ (sIn + 1) * (sIn + 1) + sIn + fxs.length → GensData.denote N gs' ≤ G₀ →
      X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.Bpb)
    (hBgm : ∀ (w' : WinData) (σ' : PermData) (gs' : GensData) (d' : D.denote),
      Giant.PbSubP DV G₀ xy w.1.length sIn (xy, w', σ', N, gs', d') →
      X.B.call GroupOp.generate (w'.1.length, GensData.restrictTo (WinData.pos N w') w'.1 gs')
        (X.O.run GroupOp.generate
          (w'.1.length, GensData.restrictTo (WinData.pos N w') w'.1 gs')) ≤ β.Bgm)
    (hBlift : ∀ (w' : WinData) (σ' : PermData) (gs' : GensData) (d' : D.denote),
      Giant.PbSubP DV G₀ xy w.1.length sIn (xy, w', σ', N, gs', d') → ∀ π' : PermData,
      X.B.call GroupOp.lift ((N, gs', d'), (w', π'))
        (X.O.run GroupOp.lift ((N, gs', d'), (w', π'))) ≤ β.Blift)
    (hBker : ∀ (w' : WinData) (σ' : PermData) (gs' : GensData) (d' : D.denote),
      Giant.PbSubP DV G₀ xy w.1.length sIn (xy, w', σ', N, gs', d') →
      X.B.call GroupOp.kernel ((N, gs', d'), w') (X.O.run GroupOp.kernel ((N, gs', d'), w')) ≤
        β.Bker)
    (hsK : ∀ (w' : WinData) (σ' : PermData) (gs' : GensData) (d' : D.denote),
      Giant.PbSubP DV G₀ xy w.1.length sIn (xy, w', σ', N, gs', d') →
      (X.O.run GroupOp.kernel ((N, gs', d'), w')).2.1.length ≤ β.sK)
    (hBgn : ∀ hs : GensData, GensData.AllValid N hs → hs.length ≤ β.sK + s →
      GensData.denote N hs ≤ G₀ →
      X.B.call GroupOp.generate (N, hs) (X.O.run GroupOp.generate (N, hs)) ≤ β.Bgn)
    -- Case 2b
    (hBg1₂ᵦ : ∀ X₀ : SoJTree.OutD,
      m5Leaf2b X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 = some X₀ →
      X.B.call GroupOp.generate
        (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (Case2b.outGensD (N - n) X₀))).map
          (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
        (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (Case2b.outGensD (N - n) X₀)))) ≤ β.Bg1₂ᵦ)
    (hBgen₂ᵦ : ∀ gs' : GensData, GensData.AllValid N gs' →
      gs'.length ≤ Case2b.c2bR N n (m5Cs X.O n N (N, fys, ey)).2.length
        (Case2b.degD X.O N n (N, fys, ey) (m5Cs X.O n N (N, fys, ey)).2 - 1)
        (Case2b.sojZ (N - n)) * (sIn + 1) →
      GensData.denote N gs' ≤ GensData.denote N gs →
      X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.Bgen₂ᵦ)
    (hD₂ᵦ : ∀ X₀, m5Leaf2b X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 = some X₀ →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (Case2b.outOps (N - n)) X₀).2.1 sIn gs' d' O' →
      RDOrbit X body DV n N w L st sIn Bd gs' d' O')
    (hpart₂ᵦ : m5Sel X.O n N (N, fxs, ex) (N, fys, ey) = 4 → ∀ X₀,
      m5Leaf2b X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 = some X₀ → X₀.1 ≠ 2 →
      ∃ (p : CPart (Fin (N - n))) (t : ℕ), (Case2b.outOps (N - n)).dec X₀ = some (Sum.inl p) ∧
        IsColPart Finset.univ t p ∧ 4 * t ≤ 3 * (N - n))
    -- Case 3
    (hBg1₃ : ∀ X₀ : SoJTree.OutD, Case3.C3First φ (strOn hC.le (xy.1.denote N)) (N - n) k
        (fixPtsD (m5Os X.O n N (N, fxs, ex))) X₀ →
      X.B.call GroupOp.generate
        (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (Case2b.outGensD (N - n) X₀))).map
          (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
        (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (Case2b.outGensD (N - n) X₀)))) ≤ β.Bg1₃)
    (hBgen₃ : ∀ gs' : GensData, GensData.AllValid N gs' →
      gs'.length ≤ Case3.c3R k (fixPtsD (m5Os X.O n N (N, fys, ey))).length
        (Case2b.sojZ (N - n)) * (sIn + 1) →
      GensData.denote N gs' ≤ GensData.denote N gs →
      X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.Bgen₃)
    (hD₃ : ∀ X₀, Case3.C3First φ (strOn hC.le (xy.1.denote N)) (N - n) k
        (fixPtsD (m5Os X.O n N (N, fxs, ex))) X₀ →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (Case2b.outOps (N - n)) X₀).2.1 sIn gs' d' O' →
      RDOrbit X body DV n N w L st sIn Bd gs' d' O')
    (hnt₃ : m5Sel X.O n N (N, fxs, ex) (N, fys, ey) = 3 →
      ¬ Case3.C3Twins φ (strOn hC.le (xy.1.denote N)) k (fixPtsD (m5Os X.O n N (N, fxs, ex))))
    (hpart₃ : m5Sel X.O n N (N, fxs, ex) (N, fys, ey) = 3 → ∀ X₀,
      Case3.C3First φ (strOn hC.le (xy.1.denote N)) (N - n) k
        (fixPtsD (m5Os X.O n N (N, fxs, ex))) X₀ → X₀.1 ≠ 2 →
      ∃ (p : CPart (Fin (N - n))) (t : ℕ), (Case2b.outOps (N - n)).dec X₀ = some (Sum.inl p) ∧
        IsColPart Finset.univ t p ∧ 4 * t ≤ 3 * (N - n))
    -- the coloured Johnson routes
    {uB Bg1J₂ Bg1J₃ : ℕ} (hLgJ : max (N - n) uB.factorial * (sIn + 1) ≤ Lg)
    (hBg1J₂ : ∀ X₀ : SoJTree.OutD,
      m5Leaf2b X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 = some X₀ →
      X.B.call GroupOp.generate
        (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (cjohnGensD (N - n) (cjFirst2bD N n (m5Cs X.O n N (N, fxs, ex)).2
            (Case2b.degD X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 - 1) X₀)))).map
          (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
        (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (cjohnGensD (N - n) (cjFirst2bD N n (m5Cs X.O n N (N, fxs, ex)).2
            (Case2b.degD X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 - 1) X₀))))) ≤
        Bg1J₂)
    (hLY₂ : Case2b.c2bR N n (m5Cs X.O n N (N, fys, ey)).2.length
      (Case2b.degD X.O N n (N, fys, ey) (m5Cs X.O n N (N, fys, ey)).2 - 1)
      (Case2b.sojZ (N - n)) * (sIn + 1) ≤ Lg)
    (hDJ₂ : ∀ X₀, m5Leaf2b X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 = some X₀ →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (cjohnOps (N - n))
          (cjFirst2bD N n (m5Cs X.O n N (N, fxs, ex)).2
            (Case2b.degD X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 - 1) X₀)).2.1 sIn
          gs' d' O' →
      RDOrbit X body DV n N w L (2, cjFirst2bD N n (m5Cs X.O n N (N, fxs, ex)).2
        (Case2b.degD X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 - 1) X₀) sIn Bd gs' d' O')
    (hu₂ : ∀ X₀, m5Leaf2b X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 = some X₀ →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (cjohnOps (N - n))
          (cjFirst2bD N n (m5Cs X.O n N (N, fxs, ex)).2
            (Case2b.degD X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 - 1) X₀)).2.1 sIn
          gs' d' O' →
      ((labJUD X₀.2.2.2.1.length (markArr (N - n) X₀.2.2.1) X₀.2.2.2.2.2 L O').getD
        (O'.headD 0) []).length ≤ uB)
    (hBg1J₃ : ∀ cXX X₀, Case3.ColChar φ (strOn hC.le (xy.1.denote N))
        (strOn hC.le (xy.1.denote N)) k (fixPtsD (m5Os X.O n N (N, fxs, ex))).length
        (fixPtsD (m5Os X.O n N (N, fxs, ex))) (fixPtsD (m5Os X.O n N (N, fxs, ex))) cXX →
      Case3.firstStructD (N - n) k (fixPtsD (m5Os X.O n N (N, fxs, ex)))
        (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fxs, ex))).length) = some X₀ → X₀.1 = 2 →
      X.B.call GroupOp.generate
        (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (cjohnGensD (N - n) (cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fxs, ex)))
            (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fxs, ex))).length) X₀)))).map
          (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
        (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (cjohnGensD (N - n) (cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fxs, ex)))
            (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fxs, ex))).length) X₀))))) ≤ Bg1J₃)
    (hLY₃ : Case3.c3R k (fixPtsD (m5Os X.O n N (N, fys, ey))).length (Case2b.sojZ (N - n)) *
      (sIn + 1) ≤ Lg)
    (hDJ₃ : ∀ cXX X₀, Case3.ColChar φ (strOn hC.le (xy.1.denote N))
        (strOn hC.le (xy.1.denote N)) k (fixPtsD (m5Os X.O n N (N, fxs, ex))).length
        (fixPtsD (m5Os X.O n N (N, fxs, ex))) (fixPtsD (m5Os X.O n N (N, fxs, ex))) cXX →
      Case3.firstStructD (N - n) k (fixPtsD (m5Os X.O n N (N, fxs, ex)))
        (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fxs, ex))).length) = some X₀ → X₀.1 = 2 →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (cjohnOps (N - n))
          (cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fxs, ex)))
            (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fxs, ex))).length) X₀)).2.1 sIn
          gs' d' O' →
      RDOrbit X body DV n N w L (2, cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fxs, ex)))
        (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fxs, ex))).length) X₀) sIn Bd gs' d' O')
    (hu₃ : ∀ cXX X₀, Case3.ColChar φ (strOn hC.le (xy.1.denote N))
        (strOn hC.le (xy.1.denote N)) k (fixPtsD (m5Os X.O n N (N, fxs, ex))).length
        (fixPtsD (m5Os X.O n N (N, fxs, ex))) (fixPtsD (m5Os X.O n N (N, fxs, ex))) cXX →
      Case3.firstStructD (N - n) k (fixPtsD (m5Os X.O n N (N, fxs, ex)))
        (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fxs, ex))).length) = some X₀ → X₀.1 = 2 →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (cjohnOps (N - n))
          (cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fxs, ex)))
            (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fxs, ex))).length) X₀)).2.1 sIn
          gs' d' O' →
      ((labJUD X₀.2.2.2.1.length (markArr (N - n) X₀.2.2.1) X₀.2.2.2.2.2 L O').getD
        (O'.headD 0) []).length ≤ uB) :
    ∃ (ans : AnswerData D) (ch : List (ℕ × Option ℕ)),
      RunsWithin X body (Main.m5DispatchCJ sub
          (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D) n₀ n L st k xy w
          (N, gs, d) (N, fxs, ex) (N, fys, ey) (m5CaseD X.O n N (N, fxs, ex))
          (m5CaseD X.O n N (N, fys, ey))) ans
        ((ch.map fun x => C x.1 x.2).sum +
          m5CKCJ X.O n N k (N, fxs, ex) (N, fys, ey) * C (n / k) none +
          m5CH X.O n N sIn w.1.length (N, fxs, ex) (N, fys, ey) * C (w.1.length / 2) none +
          m5WnsCJ X.O n N k s sIn Bgen Blift Bo Bd (N, gs, d) (N, fxs, ex) (N, fys, ey)
            w.1.length β B.Bstab B.Btr B.Borb Bk'.Bgen Bk'.Borb Bk'.Bstab
            (fun M => (Bm M).Borb) (fun M => (Bm M).Bstab) (fun M => (Bm M).Btr) uB Bg1J₂
            Bg1J₃) ∧
      AnsOK DV N (w.denote N) 1 (GensData.denote N gs) (xy.1.denote N) (xy.2.denote N) ans ∧
      (∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sIn) ∧
      ChildList w.1.length (m5CFnsCJ X.O n N k (N, fxs, ex) (N, fys, ey) uB)
        (StepChild w.1.length (N - n)) ch :=
  RunsWithin.m5DispatchCJ_ns_jp hO hPre hI hφ halt hwS h5 hk hm12 B hgs hGG₀ Bk' hsk Bm hsub hCmono
    hs hB hLg hst β hFxv hFyv hFxs hFys hFxe hFye hBgP hBmem hBkA hBlA hBg hBgk hBgs hBox hBoy hBg1₁
    hD₁ hBg1₂ₐ hBgen₂ₐ hBpb hBgm hBlift hBker hsK hBgn (fun _ _ X₀ h _ => hBg1₂ᵦ X₀ h) hBgen₂ᵦ hD₂ᵦ
    hpart₂ᵦ (fun _ _ X₀ h _ => hBg1₃ X₀ h) hBgen₃ hD₃ hnt₃ hpart₃ hLgJ
    (fun _ _ X₀ h _ _ => hBg1J₂ X₀ h) hLY₂ (fun _ _ X₀ h _ _ => hDJ₂ X₀ h)
    (fun _ _ X₀ h _ _ => hu₂ X₀ h) (fun _ _ cXX X₀ h₁ h₂ h₃ _ => hBg1J₃ cXX X₀ h₁ h₂ h₃) hLY₃
    (fun _ _ cXX X₀ h₁ h₂ h₃ _ => hDJ₃ cXX X₀ h₁ h₂ h₃)
    (fun _ _ cXX X₀ h₁ h₂ h₃ _ => hu₃ cXX X₀ h₁ h₂ h₃)

end DispatchNsCJ

/-! ### M5 on the restricted instance -/

section CoreDefsCJ

variable {D : Ty}

/-- **The work of M5 with coloured Johnson alignment**: as `m5CoreWork`, with `m5WCJ`. -/
def m5CoreWorkCJ (O : Oracle (groupSig D)) (n N k s sIn Bgen Blift Bo Bk Bcr Bd : ℕ)
    (G Fx Fy : GroupData D.denote) (wl : ℕ) (β : M5Bounds) (Bst Btr Borb Bkg Bko Bks : ℕ)
    (Bo' Bs' Bt' : ℕ → ℕ) (uB Bg1J₂ Bg1J₃ : ℕ) : ℕ :=
  2 * (certCount N n k * 4 +
      certWork N n k sIn Bst Btr Borb Bkg Bko Bks β.Bgk β.BlA β.Bgs β.BF) +
    m5DecCost O n N sIn Bst Borb β.Bg Bo' Bs' Fx + m5DecCost O n N sIn Bst Borb β.Bg Bo' Bs' Fy +
    m5WCJ O n N k s sIn Bgen Blift Bo Bk Bcr Bd G Fx Fy wl β Bst Btr Borb Bkg Bko Bks Bo' Bs' Bt'
      uB Bg1J₂ Bg1J₃ + 15

/-- **The work of M5 with coloured Johnson alignment and no stuck orbit**: as `m5CoreWorkNs`,
with `m5WnsCJ`. -/
def m5CoreWorkNsCJ (O : Oracle (groupSig D)) (n N k s sIn Bgen Blift Bo Bd : ℕ)
    (G Fx Fy : GroupData D.denote) (wl : ℕ) (β : M5Bounds) (Bst Btr Borb Bkg Bko Bks : ℕ)
    (Bo' Bs' Bt' : ℕ → ℕ) (uB Bg1J₂ Bg1J₃ : ℕ) : ℕ :=
  2 * (certCount N n k * 4 +
      certWork N n k sIn Bst Btr Borb Bkg Bko Bks β.Bgk β.BlA β.Bgs β.BF) +
    m5DecCost O n N sIn Bst Borb β.Bg Bo' Bs' Fx + m5DecCost O n N sIn Bst Borb β.Bg Bo' Bs' Fy +
    m5WnsCJ O n N k s sIn Bgen Blift Bo Bd G Fx Fy wl β Bst Btr Borb Bkg Bko Bks Bo' Bs' Bt' uB
      Bg1J₂ Bg1J₃ + 15

end CoreDefsCJ

section CoreRunCJ

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}
  {sub : HInstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)}

/-- M5's run from the runs of its parts: the two certificates, the two case decisions and the
dispatch, plus `15` for the projections and the case on the labels. -/
theorem m5CoreCJProg_run {xy : StrData × StrData} {w : WinData} {σd : PermData} {N : ℕ}
    {gs : GensData} {d : D.denote} {n₀ n k : ℕ} {L : LabelData} {st : ℕ × CJData}
    {Fx Fy : GroupData D.denote} {cx cy : ((ℕ × List ℕ) × List (List ℕ)) × Bool}
    {ans : AnswerData D} {c₁ c₂ c₃ c₄ c₅ : ℕ}
    (h₁ : RunsWithin X body (Main.m5CertProg sub n₀ n N k xy.1 (N, gs, d)) Fx c₁)
    (h₂ : RunsWithin X body (Main.m5CertProg sub n₀ n N k xy.2 (N, gs, d)) Fy c₂)
    (h₃ : RunsWithin X body (Main.m5CaseProg n N Fx) cx c₃)
    (h₄ : RunsWithin X body (Main.m5CaseProg n N Fy) cy c₄)
    (h₅ : RunsWithin X body (Main.m5DispatchCJ sub
      (((xy, w, σd, N, gs, d), n₀, n, some L) : HInstData D) n₀ n L st k xy w (N, gs, d) Fx Fy
      cx cy) ans c₅) :
    RunsWithin X body (Main.m5CoreCJProg sub
        (((xy, w, σd, N, gs, d), n₀, n, some L) : HInstData D) k st) ans
      (c₁ + c₂ + c₃ + c₄ + c₅ + 15) := by
  apply RunsWithin.mono
  case h =>
    unfold Main.m5CoreCJProg
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
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step h₁
    run_step h₂
    run_step h₃
    run_step h₄
    exact h₅
  case hc =>
    simp only [Prim.cost]
    omega

end CoreRunCJ

section CoreSpecCJ

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}
  {sub : HInstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)}
  {C : ℕ → Option ℕ → ℕ} {s : ℕ} {xy : StrData × StrData} {w : WinData}
  {N : ℕ} {gs : GensData} {d : D.denote} {n₀ n : ℕ} {L : LabelData} {st : ℕ × CJData}
  {sIn Lg Blift Bgen Bo Bk Bcr Bd : ℕ}

/-- **M5 on the restricted instance with coloured Johnson alignment.** Under the hypotheses of
`RunsWithin.m5CoreProg` (a hinted instance `I = (x, y, W, 1 • G)` with labels `L`, the string
positions `[0, n)` all in the window `W`, `G` faithful on the strings with a giant base action on
`m = N − n ≥ 12` points) and those of the Johnson routes (`RunsWithin.m5DispatchCJ_jp`), each for
every pair of full groups `M5Full` allows: the answer is
correct for `I`. The cost is the children's (`StepChild |W| m`, factor `m5CFCJ`),
`2 · certCount` certificate sub-calls and `m5CKCJ` comparison sub-calls (Case 3, the colourings
counted twice) without a hint on windows of at most `n / k` points, `m5CH` sub-calls without a
hint on windows of at most `|W| / 2` points (Case 2a's pullback), and the work
`m5CoreWorkCJ`.

Stage 14j-5c (`PLAN-14.md` §14.8 item 4): the hypotheses of Cases 2b and 3 carry the premises
under which their routes use them: `x`'s case (Case 2b: tag `2`, not Case 2a; Case 3: tag neither
`1` nor `2`); for the partition routes (`hBg1₂ᵦ`, `hBg1₃`) a first leaf or structure that is not a
Johnson one (`X₀.1 ≠ 2`); for the Johnson routes (`hBg1J₂`, `hDJ₂`, `hu₂`, `hBg1J₃`, `hDJ₃`,
`hu₃`) a Johnson one (`X₀.1 = 2`) with the facts `CJFacts` of its coloured pair.
`RunsWithin.m5CoreCJProg` follows from this one. -/
theorem RunsWithin.m5CoreCJProg_jp (hO : MeetsContractOn DV m5Ops X.O)
    (hPre : ∀ op x, m5Ops op → GroupPre DV op x → X.Pre op x)
    (hI : HInstValid DV (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D))
    {hC : CertSetting (GensData.denote N gs) n} {φ : strGroup hC →* Perm (Fin (N - n))}
    (hφ : IsPhi hC φ)
    (halt : alternatingGroup (Fin (N - n)) ≤ (baseHom _ n hC.base).range)
    (hwS : ∀ u : Fin N, u.val < n → u ∈ w.denote N)
    {k : ℕ} (h5 : 5 ≤ k) (hk : k + 2 ≤ N - n) (h2k : 2 * k ≤ N - n) (hm12 : 12 ≤ N - n)
    {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N sIn G₀) (hgs : gs.length ≤ sIn)
    (hGG₀ : GensData.denote N gs ≤ G₀) {sk : ℕ} (Bk' : BackendBounds X DV k sk ⊤)
    (hsk : sIn ≤ k * (sk + 1)) {sm : ℕ → ℕ} (Bm : ∀ M, BackendBounds X DV M (sm M) ⊤)
    (hsub : HSubSolves X body DV sub
      (fun J => SizeChild (max sIn (supTo sm (w.1.length / 2)))
          (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D) J ∧
        StepChild w.1.length (N - n) (J.winSize, J.baseOpt)) C s)
    (hCmono : ∀ a b, a ≤ b → C a none ≤ C b none) (hs : s ≤ sIn)
    (hB : RDBounds X DV n N sIn Lg Blift Bgen Bo Bk Bcr)
    (hLg : (N - n).factorial * (sIn + 1) ≤ Lg) (hst : st.1 ≠ 2) (β : M5Bounds)
    -- charges on `G`
    (hBgP : X.B.call GroupOp.generate (N - n, gs.map (baseD n N))
      (X.O.run GroupOp.generate (N - n, gs.map (baseD n N))) ≤ β.BgP)
    (hBmem : ∀ g : PermData, g.Valid (N - n) → X.B.call GroupOp.mem (pModel X.O n (N, gs, d), g)
      (X.O.run GroupOp.mem (pModel X.O n (N, gs, d), g)) ≤ β.Bmem)
    (hBkA : X.B.call GroupOp.kernel ((N, gs, d), baseWin n N) (kerModel X.O n (N, gs, d)) ≤
      β.BkA)
    (hBlA : ∀ π : PermData, X.B.call GroupOp.lift ((N, gs, d), (baseWin n N, π))
      (liftModel X.O n (N, gs, d) π) ≤ β.BlA)
    (hBg : ∀ M ≤ N - n, ∀ gs' : GensData, GensData.AllValid M gs' → gs'.length ≤ sIn →
      X.B.call GroupOp.generate (M, gs') (X.O.run GroupOp.generate (M, gs')) ≤ β.Bg)
    (hBgk : ∀ gs' : GensData, GensData.AllValid N gs' →
      gs'.length ≤ k.factorial * (sIn + 1) → GensData.denote N gs' ≤ GensData.denote N gs →
        X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.Bgk)
    (hBgs : ∀ al : List ℕ, al.Nodup → al.length = k → (∀ a ∈ al, a < N - n) → ∀ b₁ b₂,
      X.B.call GroupOp.generate (N, giantGens X.O n (N, gs, d) al b₁ b₂)
        (giantSetStabModel X.O n (N, gs, d) al b₁ b₂) ≤ β.Bgs)
    (hBF : ∀ gs' : GensData, GensData.AllValid N gs' → gs'.length ≤ 2 * sIn →
      GensData.denote N gs' ≤ GensData.denote N gs →
        X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.BF)
    (hBk3 : X.B.call GroupOp.kernel ((N, gs, d), baseWin n N) (kerModel X.O n (N, gs, d)) ≤
      β.Bk3)
    (hBo3 : X.B.call GroupOp.orbits (kerModel X.O n (N, gs, d), w)
      (krOrbits X.O n (N, gs, d) w) ≤ β.Bo3)
    (hBcr3 : X.B.call GroupOp.cosetReps ((N, gs, d), kerModel X.O n (N, gs, d))
      (kerReps X.O n (N, gs, d)) ≤ β.Bcr3)
    (hB3 : ∀ hs : GensData, GensData.AllValid N hs →
      hs.length ≤ (kerReps X.O n (N, gs, d)).length *
        (max s (kerModel X.O n (N, gs, d)).2.1.length + 1) →
      GensData.denote N hs ≤ GensData.denote N gs →
      X.B.call GroupOp.generate (N, hs) (X.O.run GroupOp.generate (N, hs)) ≤ β.Bgen3)
    -- Case 1
    (hBox : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e →
      X.B.call GroupOp.orbits ((N, fs, e), baseWin n N)
        (Giant.baseOrbits X.O n N (N, fs, e)) ≤ β.Box)
    (hBoy : ∀ fs e, M5Full DV hC φ k sIn xy.2 fs e →
      X.B.call GroupOp.orbits ((N, fs, e), baseWin n N)
        (Giant.baseOrbits X.O n N (N, fs, e)) ≤ β.Boy)
    (hBg1₁ : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e → X.B.call GroupOp.generate
      (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
        (partGensD (N - n) (Giant.orbitPartModel X.O n N (N, fs, e))))).map
        (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
      (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
        (partGensD (N - n) (Giant.orbitPartModel X.O n N (N, fs, e)))))) ≤ β.Bg1₁)
    (hD₁ : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e →
      ∀ gs' d' O', RDSet DV n N gs w L (Giant.g1Model X.O n (N, gs, d) (partOps (N - n))
        (Giant.orbitPartModel X.O n N (N, fs, e))).2.1 sIn gs' d' O' →
      RDOrbit X body DV n N w L st sIn Bd gs' d' O')
    -- Case 2a
    (hBg1₂ₐ : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e → X.B.call GroupOp.generate
      (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
        ((setOps (N - n)).gens (m5Cs X.O n N (N, fs, e)).2))).map
        (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
      (Giant.g1Model X.O n (N, gs, d) (setOps (N - n)) (m5Cs X.O n N (N, fs, e)).2) ≤
        β.Bg1₂ₐ)
    (hBgen₂ₐ : ∀ gs' : GensData, GensData.AllValid N gs' → gs'.length ≤ sIn + 1 →
      GensData.denote N gs' ≤ GensData.denote N gs →
      X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.Bgen₂ₐ)
    (hBpb : ∀ gs', GensData.AllValid N gs' →
      gs'.length ≤ (sIn + 1) * (sIn + 1) + sIn + sIn → GensData.denote N gs' ≤ G₀ →
      X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.Bpb)
    (hBgm : ∀ (w' : WinData) (σ' : PermData) (gs' : GensData) (d' : D.denote),
      Giant.PbSubP DV G₀ xy w.1.length sIn (xy, w', σ', N, gs', d') →
      X.B.call GroupOp.generate (w'.1.length, GensData.restrictTo (WinData.pos N w') w'.1 gs')
        (X.O.run GroupOp.generate
          (w'.1.length, GensData.restrictTo (WinData.pos N w') w'.1 gs')) ≤ β.Bgm)
    (hBlift : ∀ (w' : WinData) (σ' : PermData) (gs' : GensData) (d' : D.denote),
      Giant.PbSubP DV G₀ xy w.1.length sIn (xy, w', σ', N, gs', d') → ∀ π' : PermData,
      X.B.call GroupOp.lift ((N, gs', d'), (w', π'))
        (X.O.run GroupOp.lift ((N, gs', d'), (w', π'))) ≤ β.Blift)
    (hBker : ∀ (w' : WinData) (σ' : PermData) (gs' : GensData) (d' : D.denote),
      Giant.PbSubP DV G₀ xy w.1.length sIn (xy, w', σ', N, gs', d') →
      X.B.call GroupOp.kernel ((N, gs', d'), w') (X.O.run GroupOp.kernel ((N, gs', d'), w')) ≤
        β.Bker)
    (hsK : ∀ (w' : WinData) (σ' : PermData) (gs' : GensData) (d' : D.denote),
      Giant.PbSubP DV G₀ xy w.1.length sIn (xy, w', σ', N, gs', d') →
      (X.O.run GroupOp.kernel ((N, gs', d'), w')).2.1.length ≤ β.sK)
    (hBgn : ∀ hs : GensData, GensData.AllValid N hs → hs.length ≤ β.sK + s →
      GensData.denote N hs ≤ G₀ →
      X.B.call GroupOp.generate (N, hs) (X.O.run GroupOp.generate (N, hs)) ≤ β.Bgn)
    -- Case 2b
    (hBg1₂ᵦ : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e →
      (m5Cs X.O n N (N, fs, e)).1 = 2 → m5IsA X.O n N (N, fs, e) = false → ∀ X₀ : SoJTree.OutD,
      m5Leaf2b X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 = some X₀ → X₀.1 ≠ 2 →
      X.B.call GroupOp.generate
        (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (Case2b.outGensD (N - n) X₀))).map
          (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
        (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (Case2b.outGensD (N - n) X₀)))) ≤ β.Bg1₂ᵦ)
    (hBgen₂ᵦ : ∀ fs e, M5Full DV hC φ k sIn xy.2 fs e → ∀ gs' : GensData,
      GensData.AllValid N gs' →
      gs'.length ≤ Case2b.c2bR N n (m5Cs X.O n N (N, fs, e)).2.length
        (Case2b.degD X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 - 1)
        (Case2b.sojZ (N - n)) * (sIn + 1) →
      GensData.denote N gs' ≤ GensData.denote N gs →
      X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.Bgen₂ᵦ)
    (hD₂ᵦ : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e → ∀ X₀,
      m5Leaf2b X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 = some X₀ →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (Case2b.outOps (N - n)) X₀).2.1 sIn gs' d' O' →
      RDOrbit X body DV n N w L st sIn Bd gs' d' O')
    -- Case 3
    (hBg1₃ : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e →
      (m5Cs X.O n N (N, fs, e)).1 ≠ 1 → (m5Cs X.O n N (N, fs, e)).1 ≠ 2 → ∀ X₀ : SoJTree.OutD,
      Case3.C3First φ (strOn hC.le (xy.1.denote N)) (N - n) k
        (fixPtsD (m5Os X.O n N (N, fs, e))) X₀ → X₀.1 ≠ 2 →
      X.B.call GroupOp.generate
        (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (Case2b.outGensD (N - n) X₀))).map
          (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
        (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (Case2b.outGensD (N - n) X₀)))) ≤ β.Bg1₃)
    (hBgen₃ : ∀ fs e, M5Full DV hC φ k sIn xy.2 fs e → ∀ gs' : GensData,
      GensData.AllValid N gs' →
      gs'.length ≤ Case3.c3R k (fixPtsD (m5Os X.O n N (N, fs, e))).length
        (Case2b.sojZ (N - n)) * (sIn + 1) →
      GensData.denote N gs' ≤ GensData.denote N gs →
      X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.Bgen₃)
    (hD₃ : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e → ∀ X₀,
      Case3.C3First φ (strOn hC.le (xy.1.denote N)) (N - n) k
        (fixPtsD (m5Os X.O n N (N, fs, e))) X₀ →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (Case2b.outOps (N - n)) X₀).2.1 sIn gs' d' O' →
      RDOrbit X body DV n N w L st sIn Bd gs' d' O')
        -- the coloured Johnson routes
    {uB Bg1J₂ Bg1J₃ : ℕ} (hLgJ : max (N - n) uB.factorial * (sIn + 1) ≤ Lg)
    (hBg1J₂ : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e →
      (m5Cs X.O n N (N, fs, e)).1 = 2 → m5IsA X.O n N (N, fs, e) = false →
      ∀ X₀ : SoJTree.OutD,
      m5Leaf2b X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 = some X₀ → X₀.1 = 2 →
      CJFacts (N - n) (cjFirst2bD N n (m5Cs X.O n N (N, fs, e)).2
          (Case2b.degD X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 - 1) X₀) →
      X.B.call GroupOp.generate
        (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (cjohnGensD (N - n) (cjFirst2bD N n (m5Cs X.O n N (N, fs, e)).2
            (Case2b.degD X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 - 1) X₀)))).map
          (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
        (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (cjohnGensD (N - n) (cjFirst2bD N n (m5Cs X.O n N (N, fs, e)).2
            (Case2b.degD X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 - 1) X₀))))) ≤
        Bg1J₂)
    (hLY₂ : ∀ fs e, M5Full DV hC φ k sIn xy.2 fs e →
      Case2b.c2bR N n (m5Cs X.O n N (N, fs, e)).2.length
      (Case2b.degD X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 - 1)
      (Case2b.sojZ (N - n)) * (sIn + 1) ≤ Lg)
    (hDJ₂ : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e →
      (m5Cs X.O n N (N, fs, e)).1 = 2 → m5IsA X.O n N (N, fs, e) = false →
      ∀ X₀, m5Leaf2b X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 = some X₀ → X₀.1 = 2 →
      CJFacts (N - n) (cjFirst2bD N n (m5Cs X.O n N (N, fs, e)).2
          (Case2b.degD X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 - 1) X₀) →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (cjohnOps (N - n))
          (cjFirst2bD N n (m5Cs X.O n N (N, fs, e)).2
            (Case2b.degD X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 - 1) X₀)).2.1 sIn
          gs' d' O' →
      RDOrbit X body DV n N w L (2, cjFirst2bD N n (m5Cs X.O n N (N, fs, e)).2
        (Case2b.degD X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 - 1) X₀) sIn Bd gs' d' O')
    (hu₂ : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e →
      (m5Cs X.O n N (N, fs, e)).1 = 2 → m5IsA X.O n N (N, fs, e) = false →
      ∀ X₀, m5Leaf2b X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 = some X₀ → X₀.1 = 2 →
      CJFacts (N - n) (cjFirst2bD N n (m5Cs X.O n N (N, fs, e)).2
          (Case2b.degD X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 - 1) X₀) →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (cjohnOps (N - n))
          (cjFirst2bD N n (m5Cs X.O n N (N, fs, e)).2
            (Case2b.degD X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 - 1) X₀)).2.1 sIn
          gs' d' O' →
      ((labJUD X₀.2.2.2.1.length (markArr (N - n) X₀.2.2.1) X₀.2.2.2.2.2 L O').getD
        (O'.headD 0) []).length ≤ uB)
    (hBg1J₃ : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e →
      (m5Cs X.O n N (N, fs, e)).1 ≠ 1 → (m5Cs X.O n N (N, fs, e)).1 ≠ 2 →
      ∀ cXX X₀, Case3.ColChar φ (strOn hC.le (xy.1.denote N))
        (strOn hC.le (xy.1.denote N)) k (fixPtsD (m5Os X.O n N (N, fs, e))).length
        (fixPtsD (m5Os X.O n N (N, fs, e))) (fixPtsD (m5Os X.O n N (N, fs, e))) cXX →
      Case3.firstStructD (N - n) k (fixPtsD (m5Os X.O n N (N, fs, e)))
        (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fs, e))).length) = some X₀ → X₀.1 = 2 →
      CJFacts (N - n) (cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fs, e)))
          (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fs, e))).length) X₀) →
      X.B.call GroupOp.generate
        (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (cjohnGensD (N - n) (cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fs, e)))
            (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fs, e))).length) X₀)))).map
          (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
        (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (cjohnGensD (N - n) (cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fs, e)))
            (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fs, e))).length) X₀))))) ≤ Bg1J₃)
    (hLY₃ : ∀ fs e, M5Full DV hC φ k sIn xy.2 fs e →
      Case3.c3R k (fixPtsD (m5Os X.O n N (N, fs, e))).length (Case2b.sojZ (N - n)) *
      (sIn + 1) ≤ Lg)
    (hDJ₃ : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e →
      (m5Cs X.O n N (N, fs, e)).1 ≠ 1 → (m5Cs X.O n N (N, fs, e)).1 ≠ 2 →
      ∀ cXX X₀, Case3.ColChar φ (strOn hC.le (xy.1.denote N))
        (strOn hC.le (xy.1.denote N)) k (fixPtsD (m5Os X.O n N (N, fs, e))).length
        (fixPtsD (m5Os X.O n N (N, fs, e))) (fixPtsD (m5Os X.O n N (N, fs, e))) cXX →
      Case3.firstStructD (N - n) k (fixPtsD (m5Os X.O n N (N, fs, e)))
        (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fs, e))).length) = some X₀ → X₀.1 = 2 →
      CJFacts (N - n) (cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fs, e)))
          (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fs, e))).length) X₀) →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (cjohnOps (N - n))
          (cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fs, e)))
            (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fs, e))).length) X₀)).2.1 sIn
          gs' d' O' →
      RDOrbit X body DV n N w L (2, cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fs, e)))
        (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fs, e))).length) X₀) sIn Bd gs' d' O')
    (hu₃ : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e →
      (m5Cs X.O n N (N, fs, e)).1 ≠ 1 → (m5Cs X.O n N (N, fs, e)).1 ≠ 2 →
      ∀ cXX X₀, Case3.ColChar φ (strOn hC.le (xy.1.denote N))
        (strOn hC.le (xy.1.denote N)) k (fixPtsD (m5Os X.O n N (N, fs, e))).length
        (fixPtsD (m5Os X.O n N (N, fs, e))) (fixPtsD (m5Os X.O n N (N, fs, e))) cXX →
      Case3.firstStructD (N - n) k (fixPtsD (m5Os X.O n N (N, fs, e)))
        (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fs, e))).length) = some X₀ → X₀.1 = 2 →
      CJFacts (N - n) (cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fs, e)))
          (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fs, e))).length) X₀) →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (cjohnOps (N - n))
          (cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fs, e)))
            (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fs, e))).length) X₀)).2.1 sIn
          gs' d' O' →
      ((labJUD X₀.2.2.2.1.length (markArr (N - n) X₀.2.2.1) X₀.2.2.2.2.2 L O').getD
        (O'.headD 0) []).length ≤ uB) :
    ∃ (fxs fys : GensData) (ex ey : D.denote) (ans : AnswerData D) (ch : List (ℕ × Option ℕ)),
      M5Full DV hC φ k sIn xy.1 fxs ex ∧ M5Full DV hC φ k sIn xy.2 fys ey ∧
      RunsWithin X body (Main.m5CoreCJProg sub
          (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D) k st) ans
        ((ch.map fun x => C x.1 x.2).sum + 2 * certCount N n k * C (n / k) none +
          m5CKCJ X.O n N k (N, fxs, ex) (N, fys, ey) * C (n / k) none +
          m5CH X.O n N sIn w.1.length (N, fxs, ex) (N, fys, ey) * C (w.1.length / 2) none +
          m5CoreWorkCJ X.O n N k s sIn Bgen Blift Bo Bk Bcr Bd (N, gs, d) (N, fxs, ex)
            (N, fys, ey) w.1.length β B.Bstab B.Btr B.Borb Bk'.Bgen Bk'.Borb Bk'.Bstab
            (fun M => (Bm M).Borb) (fun M => (Bm M).Bstab) (fun M => (Bm M).Btr)
            uB Bg1J₂ Bg1J₃) ∧
      InstData.OK (D := D) (xy, w, PermData.one N, N, gs, d) DV ans ∧
      (∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sIn) ∧
      ChildList w.1.length (m5CFCJ X.O n N k (N, fxs, ex) (N, fys, ey) uB)
        (StepChild w.1.length (N - n)) ch := by
  have hOc : MeetsContractOn DV certOps X.O := fun op x h hx =>
    hO op x (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))) hx
  have hPc : ∀ op x, certOps op → GroupPre DV op x → X.Pre op x := fun op x h hx =>
    hPre op x (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))) hx
  have hOcs : MeetsContractOn DV m5CaseOps X.O := fun op x h hx =>
    hO op x (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))) hx
  have hPcs : ∀ op x, m5CaseOps op → GroupPre DV op x → X.Pre op x := fun op x h hx =>
    hPre op x (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))) hx
  have hGv : GroupValid DV N gs d := hI.valid.group
  have hG : IsInvariant (GensData.denote N gs) (baseSet n N) := hC.base
  have hnw : n ≤ w.1.length := m5_n_le_win hI.valid.win hI.le hwS
  have hsub' := m5_hsub_mono_s hsub hs
  have hBgs' : ∀ al ∈ Giant.ksubsD (N - n) k, ∀ b₁ b₂,
      X.B.call GroupOp.generate (N, giantGens X.O n (N, gs, d) al b₁ b₂)
        (giantSetStabModel X.O n (N, gs, d) al b₁ b₂) ≤ β.Bgs := fun al hal => by
    obtain ⟨hp, hl, hlt⟩ := Giant.mem_ksubsD.1 hal
    exact hBgs al (hp.imp Nat.ne_of_lt) hl hlt
  -- the certificates
  obtain ⟨⟨N₁, fxs, ex⟩, hrx, hNx, hvx, hlx, hdx⟩ := RunsWithin.m5CertProg (body := body) hOc
    hPc hφ hGv halt h5 hk h2k xy.1 B hgs hGG₀ Bk' hsk hBgk hBlA hBgs' hBF hsub' hCmono n₀
    (fun J hJ => (m5_stepSub_child h5 hnw hJ).imp_left (·.mono (le_max_left _ _)))
  obtain ⟨⟨N₂, fys, ey⟩, hry, hNy, hvy, hly, hdy⟩ := RunsWithin.m5CertProg (body := body) hOc
    hPc hφ hGv halt h5 hk h2k xy.2 B hgs hGG₀ Bk' hsk hBgk hBlA hBgs' hBF hsub' hCmono n₀
    (fun J hJ => (m5_stepSub_child h5 hnw hJ).imp_left (·.mono (le_max_left _ _)))
  simp only at hNx hNy
  subst N₁ N₂
  have hFx : M5Full DV hC φ k sIn xy.1 fxs ex := ⟨hvx, hlx, hdx⟩
  have hFy : M5Full DV hC φ k sIn xy.2 fys ey := ⟨hvy, hly, hdy⟩
  -- the case decisions
  have hFxG : GensData.denote N fxs ≤ GensData.denote N gs := hFx.2.2 ▸ m5Fmap_le hC φ k _
  have hFyG : GensData.denote N fys ≤ GensData.denote N gs := hFy.2.2 ▸ m5Fmap_le hC φ k _
  have hcx : RunsWithin X body (Main.m5CaseProg n N (N, fxs, ex)) (m5CaseD X.O n N (N, fxs, ex))
      (m5DecCost X.O n N sIn B.Bstab B.Borb β.Bg (fun M => (Bm M).Borb)
        (fun M => (Bm M).Bstab) (N, fxs, ex)) :=
    RunsWithin.m5CaseProg hOcs hPcs B Bm hFx.1 hFx.2.1 (hFxG.trans hGG₀) (hG.mono hFxG) hBg
  have hcy : RunsWithin X body (Main.m5CaseProg n N (N, fys, ey)) (m5CaseD X.O n N (N, fys, ey))
      (m5DecCost X.O n N sIn B.Bstab B.Borb β.Bg (fun M => (Bm M).Borb)
        (fun M => (Bm M).Bstab) (N, fys, ey)) :=
    RunsWithin.m5CaseProg hOcs hPcs B Bm hFy.1 hFy.2.1 (hFyG.trans hGG₀) (hG.mono hFyG) hBg
  -- the dispatch
  obtain ⟨ans, ch, hrun, hok, hg, hch⟩ := RunsWithin.m5DispatchCJ_jp hO hPre hI hφ halt hwS h5 hk
    hm12 B hgs hGG₀ Bk' hsk Bm hsub hCmono hs hB hLg hst β hFx.1 hFy.1 hFx.2.1 hFy.2.1 hFx.2.2
    hFy.2.2 hBgP hBmem hBkA hBlA hBg hBgk hBgs hBk3 hBo3 hBcr3 hB3 (hBox _ _ hFx)
    (hBoy _ _ hFy) (hBg1₁ _ _ hFx) (hD₁ _ _ hFx) (hBg1₂ₐ _ _ hFx) hBgen₂ₐ
    (fun gs' hv hl h0 => hBpb gs' hv (hl.trans (Nat.add_le_add_left hFx.2.1 _)) h0) hBgm hBlift
    hBker hsK hBgn (hBg1₂ᵦ _ _ hFx) (hBgen₂ᵦ _ _ hFy) (hD₂ᵦ _ _ hFx) (hBg1₃ _ _ hFx)
    (hBgen₃ _ _ hFy) (hD₃ _ _ hFx) hLgJ (hBg1J₂ _ _ hFx) (hLY₂ _ _ hFy) (hDJ₂ _ _ hFx)
    (hu₂ _ _ hFx) (hBg1J₃ _ _ hFx) (hLY₃ _ _ hFy) (hDJ₃ _ _ hFx) (hu₃ _ _ hFx)
  refine ⟨fxs, fys, ex, ey, ans, ch, hFx, hFy,
    (m5CoreCJProg_run hrx hry hcx hcy hrun).mono ?_, ?_, hg, hch⟩
  · have e1 := fullCost_le_count N n k sIn B.Bstab B.Btr B.Borb Bk'.Bgen Bk'.Borb Bk'.Bstab
      β.Bgk (C (n / k) none + 4) β.BlA β.Bgs β.BF
    unfold m5CoreWorkCJ
    linarith
  · show AnsOK DV N (w.denote N) (PermData.denote N (PermData.one N)) (GensData.denote N gs)
      (xy.1.denote N) (xy.2.denote N) ans
    rw [PermData.denote_one]
    exact hok

/-- `RunsWithin.m5CoreCJProg_jp` with Case 2b's Johnson-route hypotheses stated for every first
leaf. -/
theorem RunsWithin.m5CoreCJProg (hO : MeetsContractOn DV m5Ops X.O)
    (hPre : ∀ op x, m5Ops op → GroupPre DV op x → X.Pre op x)
    (hI : HInstValid DV (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D))
    {hC : CertSetting (GensData.denote N gs) n} {φ : strGroup hC →* Perm (Fin (N - n))}
    (hφ : IsPhi hC φ)
    (halt : alternatingGroup (Fin (N - n)) ≤ (baseHom _ n hC.base).range)
    (hwS : ∀ u : Fin N, u.val < n → u ∈ w.denote N)
    {k : ℕ} (h5 : 5 ≤ k) (hk : k + 2 ≤ N - n) (h2k : 2 * k ≤ N - n) (hm12 : 12 ≤ N - n)
    {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N sIn G₀) (hgs : gs.length ≤ sIn)
    (hGG₀ : GensData.denote N gs ≤ G₀) {sk : ℕ} (Bk' : BackendBounds X DV k sk ⊤)
    (hsk : sIn ≤ k * (sk + 1)) {sm : ℕ → ℕ} (Bm : ∀ M, BackendBounds X DV M (sm M) ⊤)
    (hsub : HSubSolves X body DV sub
      (fun J => SizeChild (max sIn (supTo sm (w.1.length / 2)))
          (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D) J ∧
        StepChild w.1.length (N - n) (J.winSize, J.baseOpt)) C s)
    (hCmono : ∀ a b, a ≤ b → C a none ≤ C b none) (hs : s ≤ sIn)
    (hB : RDBounds X DV n N sIn Lg Blift Bgen Bo Bk Bcr)
    (hLg : (N - n).factorial * (sIn + 1) ≤ Lg) (hst : st.1 ≠ 2) (β : M5Bounds)
    -- charges on `G`
    (hBgP : X.B.call GroupOp.generate (N - n, gs.map (baseD n N))
      (X.O.run GroupOp.generate (N - n, gs.map (baseD n N))) ≤ β.BgP)
    (hBmem : ∀ g : PermData, g.Valid (N - n) → X.B.call GroupOp.mem (pModel X.O n (N, gs, d), g)
      (X.O.run GroupOp.mem (pModel X.O n (N, gs, d), g)) ≤ β.Bmem)
    (hBkA : X.B.call GroupOp.kernel ((N, gs, d), baseWin n N) (kerModel X.O n (N, gs, d)) ≤
      β.BkA)
    (hBlA : ∀ π : PermData, X.B.call GroupOp.lift ((N, gs, d), (baseWin n N, π))
      (liftModel X.O n (N, gs, d) π) ≤ β.BlA)
    (hBg : ∀ M ≤ N - n, ∀ gs' : GensData, GensData.AllValid M gs' → gs'.length ≤ sIn →
      X.B.call GroupOp.generate (M, gs') (X.O.run GroupOp.generate (M, gs')) ≤ β.Bg)
    (hBgk : ∀ gs' : GensData, GensData.AllValid N gs' →
      gs'.length ≤ k.factorial * (sIn + 1) → GensData.denote N gs' ≤ GensData.denote N gs →
        X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.Bgk)
    (hBgs : ∀ al : List ℕ, al.Nodup → al.length = k → (∀ a ∈ al, a < N - n) → ∀ b₁ b₂,
      X.B.call GroupOp.generate (N, giantGens X.O n (N, gs, d) al b₁ b₂)
        (giantSetStabModel X.O n (N, gs, d) al b₁ b₂) ≤ β.Bgs)
    (hBF : ∀ gs' : GensData, GensData.AllValid N gs' → gs'.length ≤ 2 * sIn →
      GensData.denote N gs' ≤ GensData.denote N gs →
        X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.BF)
    (hBk3 : X.B.call GroupOp.kernel ((N, gs, d), baseWin n N) (kerModel X.O n (N, gs, d)) ≤
      β.Bk3)
    (hBo3 : X.B.call GroupOp.orbits (kerModel X.O n (N, gs, d), w)
      (krOrbits X.O n (N, gs, d) w) ≤ β.Bo3)
    (hBcr3 : X.B.call GroupOp.cosetReps ((N, gs, d), kerModel X.O n (N, gs, d))
      (kerReps X.O n (N, gs, d)) ≤ β.Bcr3)
    (hB3 : ∀ hs : GensData, GensData.AllValid N hs →
      hs.length ≤ (kerReps X.O n (N, gs, d)).length *
        (max s (kerModel X.O n (N, gs, d)).2.1.length + 1) →
      GensData.denote N hs ≤ GensData.denote N gs →
      X.B.call GroupOp.generate (N, hs) (X.O.run GroupOp.generate (N, hs)) ≤ β.Bgen3)
    -- Case 1
    (hBox : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e →
      X.B.call GroupOp.orbits ((N, fs, e), baseWin n N)
        (Giant.baseOrbits X.O n N (N, fs, e)) ≤ β.Box)
    (hBoy : ∀ fs e, M5Full DV hC φ k sIn xy.2 fs e →
      X.B.call GroupOp.orbits ((N, fs, e), baseWin n N)
        (Giant.baseOrbits X.O n N (N, fs, e)) ≤ β.Boy)
    (hBg1₁ : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e → X.B.call GroupOp.generate
      (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
        (partGensD (N - n) (Giant.orbitPartModel X.O n N (N, fs, e))))).map
        (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
      (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
        (partGensD (N - n) (Giant.orbitPartModel X.O n N (N, fs, e)))))) ≤ β.Bg1₁)
    (hD₁ : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e →
      ∀ gs' d' O', RDSet DV n N gs w L (Giant.g1Model X.O n (N, gs, d) (partOps (N - n))
        (Giant.orbitPartModel X.O n N (N, fs, e))).2.1 sIn gs' d' O' →
      RDOrbit X body DV n N w L st sIn Bd gs' d' O')
    -- Case 2a
    (hBg1₂ₐ : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e → X.B.call GroupOp.generate
      (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
        ((setOps (N - n)).gens (m5Cs X.O n N (N, fs, e)).2))).map
        (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
      (Giant.g1Model X.O n (N, gs, d) (setOps (N - n)) (m5Cs X.O n N (N, fs, e)).2) ≤
        β.Bg1₂ₐ)
    (hBgen₂ₐ : ∀ gs' : GensData, GensData.AllValid N gs' → gs'.length ≤ sIn + 1 →
      GensData.denote N gs' ≤ GensData.denote N gs →
      X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.Bgen₂ₐ)
    (hBpb : ∀ gs', GensData.AllValid N gs' →
      gs'.length ≤ (sIn + 1) * (sIn + 1) + sIn + sIn → GensData.denote N gs' ≤ G₀ →
      X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.Bpb)
    (hBgm : ∀ (w' : WinData) (σ' : PermData) (gs' : GensData) (d' : D.denote),
      Giant.PbSubP DV G₀ xy w.1.length sIn (xy, w', σ', N, gs', d') →
      X.B.call GroupOp.generate (w'.1.length, GensData.restrictTo (WinData.pos N w') w'.1 gs')
        (X.O.run GroupOp.generate
          (w'.1.length, GensData.restrictTo (WinData.pos N w') w'.1 gs')) ≤ β.Bgm)
    (hBlift : ∀ (w' : WinData) (σ' : PermData) (gs' : GensData) (d' : D.denote),
      Giant.PbSubP DV G₀ xy w.1.length sIn (xy, w', σ', N, gs', d') → ∀ π' : PermData,
      X.B.call GroupOp.lift ((N, gs', d'), (w', π'))
        (X.O.run GroupOp.lift ((N, gs', d'), (w', π'))) ≤ β.Blift)
    (hBker : ∀ (w' : WinData) (σ' : PermData) (gs' : GensData) (d' : D.denote),
      Giant.PbSubP DV G₀ xy w.1.length sIn (xy, w', σ', N, gs', d') →
      X.B.call GroupOp.kernel ((N, gs', d'), w') (X.O.run GroupOp.kernel ((N, gs', d'), w')) ≤
        β.Bker)
    (hsK : ∀ (w' : WinData) (σ' : PermData) (gs' : GensData) (d' : D.denote),
      Giant.PbSubP DV G₀ xy w.1.length sIn (xy, w', σ', N, gs', d') →
      (X.O.run GroupOp.kernel ((N, gs', d'), w')).2.1.length ≤ β.sK)
    (hBgn : ∀ hs : GensData, GensData.AllValid N hs → hs.length ≤ β.sK + s →
      GensData.denote N hs ≤ G₀ →
      X.B.call GroupOp.generate (N, hs) (X.O.run GroupOp.generate (N, hs)) ≤ β.Bgn)
    -- Case 2b
    (hBg1₂ᵦ : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e → ∀ X₀ : SoJTree.OutD,
      m5Leaf2b X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 = some X₀ →
      X.B.call GroupOp.generate
        (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (Case2b.outGensD (N - n) X₀))).map
          (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
        (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (Case2b.outGensD (N - n) X₀)))) ≤ β.Bg1₂ᵦ)
    (hBgen₂ᵦ : ∀ fs e, M5Full DV hC φ k sIn xy.2 fs e → ∀ gs' : GensData,
      GensData.AllValid N gs' →
      gs'.length ≤ Case2b.c2bR N n (m5Cs X.O n N (N, fs, e)).2.length
        (Case2b.degD X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 - 1)
        (Case2b.sojZ (N - n)) * (sIn + 1) →
      GensData.denote N gs' ≤ GensData.denote N gs →
      X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.Bgen₂ᵦ)
    (hD₂ᵦ : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e → ∀ X₀,
      m5Leaf2b X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 = some X₀ →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (Case2b.outOps (N - n)) X₀).2.1 sIn gs' d' O' →
      RDOrbit X body DV n N w L st sIn Bd gs' d' O')
    -- Case 3
    (hBg1₃ : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e → ∀ X₀ : SoJTree.OutD,
      Case3.C3First φ (strOn hC.le (xy.1.denote N)) (N - n) k
        (fixPtsD (m5Os X.O n N (N, fs, e))) X₀ →
      X.B.call GroupOp.generate
        (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (Case2b.outGensD (N - n) X₀))).map
          (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
        (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (Case2b.outGensD (N - n) X₀)))) ≤ β.Bg1₃)
    (hBgen₃ : ∀ fs e, M5Full DV hC φ k sIn xy.2 fs e → ∀ gs' : GensData,
      GensData.AllValid N gs' →
      gs'.length ≤ Case3.c3R k (fixPtsD (m5Os X.O n N (N, fs, e))).length
        (Case2b.sojZ (N - n)) * (sIn + 1) →
      GensData.denote N gs' ≤ GensData.denote N gs →
      X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.Bgen₃)
    (hD₃ : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e → ∀ X₀,
      Case3.C3First φ (strOn hC.le (xy.1.denote N)) (N - n) k
        (fixPtsD (m5Os X.O n N (N, fs, e))) X₀ →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (Case2b.outOps (N - n)) X₀).2.1 sIn gs' d' O' →
      RDOrbit X body DV n N w L st sIn Bd gs' d' O')
        -- the coloured Johnson routes
    {uB Bg1J₂ Bg1J₃ : ℕ} (hLgJ : max (N - n) uB.factorial * (sIn + 1) ≤ Lg)
    (hBg1J₂ : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e →
      ∀ X₀ : SoJTree.OutD,
      m5Leaf2b X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 = some X₀ →
      X.B.call GroupOp.generate
        (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (cjohnGensD (N - n) (cjFirst2bD N n (m5Cs X.O n N (N, fs, e)).2
            (Case2b.degD X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 - 1) X₀)))).map
          (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
        (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (cjohnGensD (N - n) (cjFirst2bD N n (m5Cs X.O n N (N, fs, e)).2
            (Case2b.degD X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 - 1) X₀))))) ≤
        Bg1J₂)
    (hLY₂ : ∀ fs e, M5Full DV hC φ k sIn xy.2 fs e →
      Case2b.c2bR N n (m5Cs X.O n N (N, fs, e)).2.length
      (Case2b.degD X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 - 1)
      (Case2b.sojZ (N - n)) * (sIn + 1) ≤ Lg)
    (hDJ₂ : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e →
      ∀ X₀, m5Leaf2b X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 = some X₀ →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (cjohnOps (N - n))
          (cjFirst2bD N n (m5Cs X.O n N (N, fs, e)).2
            (Case2b.degD X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 - 1) X₀)).2.1 sIn
          gs' d' O' →
      RDOrbit X body DV n N w L (2, cjFirst2bD N n (m5Cs X.O n N (N, fs, e)).2
        (Case2b.degD X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 - 1) X₀) sIn Bd gs' d' O')
    (hu₂ : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e →
      ∀ X₀, m5Leaf2b X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 = some X₀ →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (cjohnOps (N - n))
          (cjFirst2bD N n (m5Cs X.O n N (N, fs, e)).2
            (Case2b.degD X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 - 1) X₀)).2.1 sIn
          gs' d' O' →
      ((labJUD X₀.2.2.2.1.length (markArr (N - n) X₀.2.2.1) X₀.2.2.2.2.2 L O').getD
        (O'.headD 0) []).length ≤ uB)
    (hBg1J₃ : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e →
      ∀ cXX X₀, Case3.ColChar φ (strOn hC.le (xy.1.denote N))
        (strOn hC.le (xy.1.denote N)) k (fixPtsD (m5Os X.O n N (N, fs, e))).length
        (fixPtsD (m5Os X.O n N (N, fs, e))) (fixPtsD (m5Os X.O n N (N, fs, e))) cXX →
      Case3.firstStructD (N - n) k (fixPtsD (m5Os X.O n N (N, fs, e)))
        (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fs, e))).length) = some X₀ → X₀.1 = 2 →
      X.B.call GroupOp.generate
        (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (cjohnGensD (N - n) (cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fs, e)))
            (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fs, e))).length) X₀)))).map
          (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
        (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (cjohnGensD (N - n) (cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fs, e)))
            (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fs, e))).length) X₀))))) ≤ Bg1J₃)
    (hLY₃ : ∀ fs e, M5Full DV hC φ k sIn xy.2 fs e →
      Case3.c3R k (fixPtsD (m5Os X.O n N (N, fs, e))).length (Case2b.sojZ (N - n)) *
      (sIn + 1) ≤ Lg)
    (hDJ₃ : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e →
      ∀ cXX X₀, Case3.ColChar φ (strOn hC.le (xy.1.denote N))
        (strOn hC.le (xy.1.denote N)) k (fixPtsD (m5Os X.O n N (N, fs, e))).length
        (fixPtsD (m5Os X.O n N (N, fs, e))) (fixPtsD (m5Os X.O n N (N, fs, e))) cXX →
      Case3.firstStructD (N - n) k (fixPtsD (m5Os X.O n N (N, fs, e)))
        (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fs, e))).length) = some X₀ → X₀.1 = 2 →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (cjohnOps (N - n))
          (cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fs, e)))
            (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fs, e))).length) X₀)).2.1 sIn
          gs' d' O' →
      RDOrbit X body DV n N w L (2, cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fs, e)))
        (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fs, e))).length) X₀) sIn Bd gs' d' O')
    (hu₃ : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e →
      ∀ cXX X₀, Case3.ColChar φ (strOn hC.le (xy.1.denote N))
        (strOn hC.le (xy.1.denote N)) k (fixPtsD (m5Os X.O n N (N, fs, e))).length
        (fixPtsD (m5Os X.O n N (N, fs, e))) (fixPtsD (m5Os X.O n N (N, fs, e))) cXX →
      Case3.firstStructD (N - n) k (fixPtsD (m5Os X.O n N (N, fs, e)))
        (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fs, e))).length) = some X₀ → X₀.1 = 2 →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (cjohnOps (N - n))
          (cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fs, e)))
            (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fs, e))).length) X₀)).2.1 sIn
          gs' d' O' →
      ((labJUD X₀.2.2.2.1.length (markArr (N - n) X₀.2.2.1) X₀.2.2.2.2.2 L O').getD
        (O'.headD 0) []).length ≤ uB) :
    ∃ (fxs fys : GensData) (ex ey : D.denote) (ans : AnswerData D) (ch : List (ℕ × Option ℕ)),
      M5Full DV hC φ k sIn xy.1 fxs ex ∧ M5Full DV hC φ k sIn xy.2 fys ey ∧
      RunsWithin X body (Main.m5CoreCJProg sub
          (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D) k st) ans
        ((ch.map fun x => C x.1 x.2).sum + 2 * certCount N n k * C (n / k) none +
          m5CKCJ X.O n N k (N, fxs, ex) (N, fys, ey) * C (n / k) none +
          m5CH X.O n N sIn w.1.length (N, fxs, ex) (N, fys, ey) * C (w.1.length / 2) none +
          m5CoreWorkCJ X.O n N k s sIn Bgen Blift Bo Bk Bcr Bd (N, gs, d) (N, fxs, ex)
            (N, fys, ey) w.1.length β B.Bstab B.Btr B.Borb Bk'.Bgen Bk'.Borb Bk'.Bstab
            (fun M => (Bm M).Borb) (fun M => (Bm M).Bstab) (fun M => (Bm M).Btr)
            uB Bg1J₂ Bg1J₃) ∧
      InstData.OK (D := D) (xy, w, PermData.one N, N, gs, d) DV ans ∧
      (∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sIn) ∧
      ChildList w.1.length (m5CFCJ X.O n N k (N, fxs, ex) (N, fys, ey) uB)
        (StepChild w.1.length (N - n)) ch :=
  RunsWithin.m5CoreCJProg_jp hO hPre hI hφ halt hwS h5 hk h2k hm12 B hgs hGG₀ Bk' hsk Bm hsub hCmono
    hs hB hLg hst β hBgP hBmem hBkA hBlA hBg hBgk hBgs hBF hBk3 hBo3 hBcr3 hB3 hBox hBoy hBg1₁ hD₁
    hBg1₂ₐ hBgen₂ₐ hBpb hBgm hBlift hBker hsK hBgn (fun fs e hF _ _ X₀ h _ => hBg1₂ᵦ fs e hF X₀ h)
    hBgen₂ᵦ hD₂ᵦ (fun fs e hF _ _ X₀ h _ => hBg1₃ fs e hF X₀ h) hBgen₃ hD₃ hLgJ
    (fun fs e hF _ _ X₀ h _ _ => hBg1J₂ fs e hF X₀ h) hLY₂
    (fun fs e hF _ _ X₀ h _ _ => hDJ₂ fs e hF X₀ h) (fun fs e hF _ _ X₀ h _ _ => hu₂ fs e hF X₀ h)
    (fun fs e hF _ _ cXX X₀ h₁ h₂ h₃ _ => hBg1J₃ fs e hF cXX X₀ h₁ h₂ h₃) hLY₃
    (fun fs e hF _ _ cXX X₀ h₁ h₂ h₃ _ => hDJ₃ fs e hF cXX X₀ h₁ h₂ h₃)
    (fun fs e hF _ _ cXX X₀ h₁ h₂ h₃ _ => hu₃ fs e hF cXX X₀ h₁ h₂ h₃)

end CoreSpecCJ

section CoreNsCJ

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}
  {sub : HInstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)}
  {C : ℕ → Option ℕ → ℕ} {s : ℕ} {xy : StrData × StrData} {w : WinData}
  {N : ℕ} {gs : GensData} {d : D.denote} {n₀ n : ℕ} {L : LabelData} {st : ℕ × CJData}
  {sIn Lg Blift Bgen Bo Bk Bcr Bd : ℕ}

/-- **M5 on the restricted instance with no stuck orbit, with Case 2b's counts for `y` assumed
only in Case 2b** (stage 14j-6b-1, `PLAN-14.md` §14.11 item 5): as
`RunsWithin.m5CoreCJProg_ns_jp`, with `hBgen₂ᵦ` and `hLY₂` needed only for a full group of `y`
in Case 2b (`RunsWithin.m5DispatchCJ_ns_jpC`). -/
theorem RunsWithin.m5CoreCJProg_ns_jpC (hO : MeetsContractOn DV m5Ops X.O)
    (hPre : ∀ op x, m5Ops op → GroupPre DV op x → X.Pre op x)
    (hI : HInstValid DV (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D))
    {hC : CertSetting (GensData.denote N gs) n} {φ : strGroup hC →* Perm (Fin (N - n))}
    (hφ : IsPhi hC φ)
    (halt : alternatingGroup (Fin (N - n)) ≤ (baseHom _ n hC.base).range)
    (hwS : ∀ u : Fin N, u.val < n → u ∈ w.denote N)
    {k : ℕ} (h5 : 5 ≤ k) (hk : k + 2 ≤ N - n) (h2k : 2 * k ≤ N - n) (hm12 : 12 ≤ N - n)
    {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N sIn G₀) (hgs : gs.length ≤ sIn)
    (hGG₀ : GensData.denote N gs ≤ G₀) {sk : ℕ} (Bk' : BackendBounds X DV k sk ⊤)
    (hsk : sIn ≤ k * (sk + 1)) {sm : ℕ → ℕ} (Bm : ∀ M, BackendBounds X DV M (sm M) ⊤)
    (hsub : HSubSolves X body DV sub
      (fun J => SizeChild (max sIn (supTo sm (w.1.length / 2)))
          (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D) J ∧
        StepChild w.1.length (N - n) (J.winSize, J.baseOpt)) C s)
    (hCmono : ∀ a b, a ≤ b → C a none ≤ C b none) (hs : s ≤ sIn)
    (hB : RDBounds X DV n N sIn Lg Blift Bgen Bo Bk Bcr)
    (hLg : (N - n) * (sIn + 1) ≤ Lg) (hst : st.1 ≠ 2) (β : M5Bounds)
    -- charges on `G`
    (hBgP : X.B.call GroupOp.generate (N - n, gs.map (baseD n N))
      (X.O.run GroupOp.generate (N - n, gs.map (baseD n N))) ≤ β.BgP)
    (hBmem : ∀ g : PermData, g.Valid (N - n) → X.B.call GroupOp.mem (pModel X.O n (N, gs, d), g)
      (X.O.run GroupOp.mem (pModel X.O n (N, gs, d), g)) ≤ β.Bmem)
    (hBkA : X.B.call GroupOp.kernel ((N, gs, d), baseWin n N) (kerModel X.O n (N, gs, d)) ≤
      β.BkA)
    (hBlA : ∀ π : PermData, X.B.call GroupOp.lift ((N, gs, d), (baseWin n N, π))
      (liftModel X.O n (N, gs, d) π) ≤ β.BlA)
    (hBg : ∀ M ≤ N - n, ∀ gs' : GensData, GensData.AllValid M gs' → gs'.length ≤ sIn →
      X.B.call GroupOp.generate (M, gs') (X.O.run GroupOp.generate (M, gs')) ≤ β.Bg)
    (hBgk : ∀ gs' : GensData, GensData.AllValid N gs' →
      gs'.length ≤ k.factorial * (sIn + 1) → GensData.denote N gs' ≤ GensData.denote N gs →
        X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.Bgk)
    (hBgs : ∀ al : List ℕ, al.Nodup → al.length = k → (∀ a ∈ al, a < N - n) → ∀ b₁ b₂,
      X.B.call GroupOp.generate (N, giantGens X.O n (N, gs, d) al b₁ b₂)
        (giantSetStabModel X.O n (N, gs, d) al b₁ b₂) ≤ β.Bgs)
    (hBF : ∀ gs' : GensData, GensData.AllValid N gs' → gs'.length ≤ 2 * sIn →
      GensData.denote N gs' ≤ GensData.denote N gs →
        X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.BF)
    -- Case 1
    (hBox : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e →
      X.B.call GroupOp.orbits ((N, fs, e), baseWin n N)
        (Giant.baseOrbits X.O n N (N, fs, e)) ≤ β.Box)
    (hBoy : ∀ fs e, M5Full DV hC φ k sIn xy.2 fs e →
      X.B.call GroupOp.orbits ((N, fs, e), baseWin n N)
        (Giant.baseOrbits X.O n N (N, fs, e)) ≤ β.Boy)
    (hBg1₁ : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e → X.B.call GroupOp.generate
      (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
        (partGensD (N - n) (Giant.orbitPartModel X.O n N (N, fs, e))))).map
        (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
      (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
        (partGensD (N - n) (Giant.orbitPartModel X.O n N (N, fs, e)))))) ≤ β.Bg1₁)
    (hD₁ : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e →
      ∀ gs' d' O', RDSet DV n N gs w L (Giant.g1Model X.O n (N, gs, d) (partOps (N - n))
        (Giant.orbitPartModel X.O n N (N, fs, e))).2.1 sIn gs' d' O' →
      RDOrbit X body DV n N w L st sIn Bd gs' d' O')
    -- Case 2a
    (hBg1₂ₐ : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e → X.B.call GroupOp.generate
      (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
        ((setOps (N - n)).gens (m5Cs X.O n N (N, fs, e)).2))).map
        (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
      (Giant.g1Model X.O n (N, gs, d) (setOps (N - n)) (m5Cs X.O n N (N, fs, e)).2) ≤
        β.Bg1₂ₐ)
    (hBgen₂ₐ : ∀ gs' : GensData, GensData.AllValid N gs' → gs'.length ≤ sIn + 1 →
      GensData.denote N gs' ≤ GensData.denote N gs →
      X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.Bgen₂ₐ)
    (hBpb : ∀ gs', GensData.AllValid N gs' →
      gs'.length ≤ (sIn + 1) * (sIn + 1) + sIn + sIn → GensData.denote N gs' ≤ G₀ →
      X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.Bpb)
    (hBgm : ∀ (w' : WinData) (σ' : PermData) (gs' : GensData) (d' : D.denote),
      Giant.PbSubP DV G₀ xy w.1.length sIn (xy, w', σ', N, gs', d') →
      X.B.call GroupOp.generate (w'.1.length, GensData.restrictTo (WinData.pos N w') w'.1 gs')
        (X.O.run GroupOp.generate
          (w'.1.length, GensData.restrictTo (WinData.pos N w') w'.1 gs')) ≤ β.Bgm)
    (hBlift : ∀ (w' : WinData) (σ' : PermData) (gs' : GensData) (d' : D.denote),
      Giant.PbSubP DV G₀ xy w.1.length sIn (xy, w', σ', N, gs', d') → ∀ π' : PermData,
      X.B.call GroupOp.lift ((N, gs', d'), (w', π'))
        (X.O.run GroupOp.lift ((N, gs', d'), (w', π'))) ≤ β.Blift)
    (hBker : ∀ (w' : WinData) (σ' : PermData) (gs' : GensData) (d' : D.denote),
      Giant.PbSubP DV G₀ xy w.1.length sIn (xy, w', σ', N, gs', d') →
      X.B.call GroupOp.kernel ((N, gs', d'), w') (X.O.run GroupOp.kernel ((N, gs', d'), w')) ≤
        β.Bker)
    (hsK : ∀ (w' : WinData) (σ' : PermData) (gs' : GensData) (d' : D.denote),
      Giant.PbSubP DV G₀ xy w.1.length sIn (xy, w', σ', N, gs', d') →
      (X.O.run GroupOp.kernel ((N, gs', d'), w')).2.1.length ≤ β.sK)
    (hBgn : ∀ hs : GensData, GensData.AllValid N hs → hs.length ≤ β.sK + s →
      GensData.denote N hs ≤ G₀ →
      X.B.call GroupOp.generate (N, hs) (X.O.run GroupOp.generate (N, hs)) ≤ β.Bgn)
    -- Case 2b
    (hBg1₂ᵦ : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e →
      (m5Cs X.O n N (N, fs, e)).1 = 2 → m5IsA X.O n N (N, fs, e) = false → ∀ X₀ : SoJTree.OutD,
      m5Leaf2b X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 = some X₀ → X₀.1 ≠ 2 →
      X.B.call GroupOp.generate
        (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (Case2b.outGensD (N - n) X₀))).map
          (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
        (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (Case2b.outGensD (N - n) X₀)))) ≤ β.Bg1₂ᵦ)
    (hBgen₂ᵦ : ∀ fs e, M5Full DV hC φ k sIn xy.2 fs e →
      (m5Cs X.O n N (N, fs, e)).1 = 2 → m5IsA X.O n N (N, fs, e) = false → ∀ gs' : GensData,
      GensData.AllValid N gs' →
      gs'.length ≤ Case2b.c2bR N n (m5Cs X.O n N (N, fs, e)).2.length
        (Case2b.degD X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 - 1)
        (Case2b.sojZ (N - n)) * (sIn + 1) →
      GensData.denote N gs' ≤ GensData.denote N gs →
      X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.Bgen₂ᵦ)
    (hD₂ᵦ : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e → ∀ X₀,
      m5Leaf2b X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 = some X₀ →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (Case2b.outOps (N - n)) X₀).2.1 sIn gs' d' O' →
      RDOrbit X body DV n N w L st sIn Bd gs' d' O')
    (hpart₂ᵦ : ∀ fxs ex fys ey, M5Full DV hC φ k sIn xy.1 fxs ex →
      M5Full DV hC φ k sIn xy.2 fys ey → m5Sel X.O n N (N, fxs, ex) (N, fys, ey) = 4 → ∀ X₀,
      m5Leaf2b X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 = some X₀ → X₀.1 ≠ 2 →
      ∃ (p : CPart (Fin (N - n))) (t : ℕ), (Case2b.outOps (N - n)).dec X₀ = some (Sum.inl p) ∧
        IsColPart Finset.univ t p ∧ 4 * t ≤ 3 * (N - n))
    -- Case 3
    (hBg1₃ : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e →
      (m5Cs X.O n N (N, fs, e)).1 ≠ 1 → (m5Cs X.O n N (N, fs, e)).1 ≠ 2 → ∀ X₀ : SoJTree.OutD,
      Case3.C3First φ (strOn hC.le (xy.1.denote N)) (N - n) k
        (fixPtsD (m5Os X.O n N (N, fs, e))) X₀ → X₀.1 ≠ 2 →
      X.B.call GroupOp.generate
        (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (Case2b.outGensD (N - n) X₀))).map
          (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
        (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (Case2b.outGensD (N - n) X₀)))) ≤ β.Bg1₃)
    (hBgen₃ : ∀ fs e, M5Full DV hC φ k sIn xy.2 fs e → ∀ gs' : GensData,
      GensData.AllValid N gs' →
      gs'.length ≤ Case3.c3R k (fixPtsD (m5Os X.O n N (N, fs, e))).length
        (Case2b.sojZ (N - n)) * (sIn + 1) →
      GensData.denote N gs' ≤ GensData.denote N gs →
      X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.Bgen₃)
    (hD₃ : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e → ∀ X₀,
      Case3.C3First φ (strOn hC.le (xy.1.denote N)) (N - n) k
        (fixPtsD (m5Os X.O n N (N, fs, e))) X₀ →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (Case2b.outOps (N - n)) X₀).2.1 sIn gs' d' O' →
      RDOrbit X body DV n N w L st sIn Bd gs' d' O')
    (hnt₃ : ∀ fxs ex fys ey, M5Full DV hC φ k sIn xy.1 fxs ex →
      M5Full DV hC φ k sIn xy.2 fys ey → m5Sel X.O n N (N, fxs, ex) (N, fys, ey) = 3 →
      ¬ Case3.C3Twins φ (strOn hC.le (xy.1.denote N)) k (fixPtsD (m5Os X.O n N (N, fxs, ex))))
    (hpart₃ : ∀ fxs ex fys ey, M5Full DV hC φ k sIn xy.1 fxs ex →
      M5Full DV hC φ k sIn xy.2 fys ey → m5Sel X.O n N (N, fxs, ex) (N, fys, ey) = 3 → ∀ X₀,
      Case3.C3First φ (strOn hC.le (xy.1.denote N)) (N - n) k
        (fixPtsD (m5Os X.O n N (N, fxs, ex))) X₀ → X₀.1 ≠ 2 →
      ∃ (p : CPart (Fin (N - n))) (t : ℕ), (Case2b.outOps (N - n)).dec X₀ = some (Sum.inl p) ∧
        IsColPart Finset.univ t p ∧ 4 * t ≤ 3 * (N - n))
        -- the coloured Johnson routes
    {uB Bg1J₂ Bg1J₃ : ℕ} (hLgJ : max (N - n) uB.factorial * (sIn + 1) ≤ Lg)
    (hBg1J₂ : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e →
      (m5Cs X.O n N (N, fs, e)).1 = 2 → m5IsA X.O n N (N, fs, e) = false →
      ∀ X₀ : SoJTree.OutD,
      m5Leaf2b X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 = some X₀ → X₀.1 = 2 →
      CJFacts (N - n) (cjFirst2bD N n (m5Cs X.O n N (N, fs, e)).2
          (Case2b.degD X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 - 1) X₀) →
      X.B.call GroupOp.generate
        (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (cjohnGensD (N - n) (cjFirst2bD N n (m5Cs X.O n N (N, fs, e)).2
            (Case2b.degD X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 - 1) X₀)))).map
          (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
        (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (cjohnGensD (N - n) (cjFirst2bD N n (m5Cs X.O n N (N, fs, e)).2
            (Case2b.degD X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 - 1) X₀))))) ≤
        Bg1J₂)
    (hLY₂ : ∀ fs e, M5Full DV hC φ k sIn xy.2 fs e →
      (m5Cs X.O n N (N, fs, e)).1 = 2 → m5IsA X.O n N (N, fs, e) = false →
      Case2b.c2bR N n (m5Cs X.O n N (N, fs, e)).2.length
      (Case2b.degD X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 - 1)
      (Case2b.sojZ (N - n)) * (sIn + 1) ≤ Lg)
    (hDJ₂ : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e →
      (m5Cs X.O n N (N, fs, e)).1 = 2 → m5IsA X.O n N (N, fs, e) = false →
      ∀ X₀, m5Leaf2b X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 = some X₀ → X₀.1 = 2 →
      CJFacts (N - n) (cjFirst2bD N n (m5Cs X.O n N (N, fs, e)).2
          (Case2b.degD X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 - 1) X₀) →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (cjohnOps (N - n))
          (cjFirst2bD N n (m5Cs X.O n N (N, fs, e)).2
            (Case2b.degD X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 - 1) X₀)).2.1 sIn
          gs' d' O' →
      RDOrbit X body DV n N w L (2, cjFirst2bD N n (m5Cs X.O n N (N, fs, e)).2
        (Case2b.degD X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 - 1) X₀) sIn Bd gs' d' O')
    (hu₂ : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e →
      (m5Cs X.O n N (N, fs, e)).1 = 2 → m5IsA X.O n N (N, fs, e) = false →
      ∀ X₀, m5Leaf2b X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 = some X₀ → X₀.1 = 2 →
      CJFacts (N - n) (cjFirst2bD N n (m5Cs X.O n N (N, fs, e)).2
          (Case2b.degD X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 - 1) X₀) →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (cjohnOps (N - n))
          (cjFirst2bD N n (m5Cs X.O n N (N, fs, e)).2
            (Case2b.degD X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 - 1) X₀)).2.1 sIn
          gs' d' O' →
      ((labJUD X₀.2.2.2.1.length (markArr (N - n) X₀.2.2.1) X₀.2.2.2.2.2 L O').getD
        (O'.headD 0) []).length ≤ uB)
    (hBg1J₃ : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e →
      (m5Cs X.O n N (N, fs, e)).1 ≠ 1 → (m5Cs X.O n N (N, fs, e)).1 ≠ 2 →
      ∀ cXX X₀, Case3.ColChar φ (strOn hC.le (xy.1.denote N))
        (strOn hC.le (xy.1.denote N)) k (fixPtsD (m5Os X.O n N (N, fs, e))).length
        (fixPtsD (m5Os X.O n N (N, fs, e))) (fixPtsD (m5Os X.O n N (N, fs, e))) cXX →
      Case3.firstStructD (N - n) k (fixPtsD (m5Os X.O n N (N, fs, e)))
        (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fs, e))).length) = some X₀ → X₀.1 = 2 →
      CJFacts (N - n) (cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fs, e)))
          (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fs, e))).length) X₀) →
      X.B.call GroupOp.generate
        (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (cjohnGensD (N - n) (cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fs, e)))
            (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fs, e))).length) X₀)))).map
          (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
        (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (cjohnGensD (N - n) (cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fs, e)))
            (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fs, e))).length) X₀))))) ≤ Bg1J₃)
    (hLY₃ : ∀ fs e, M5Full DV hC φ k sIn xy.2 fs e →
      Case3.c3R k (fixPtsD (m5Os X.O n N (N, fs, e))).length (Case2b.sojZ (N - n)) *
      (sIn + 1) ≤ Lg)
    (hDJ₃ : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e →
      (m5Cs X.O n N (N, fs, e)).1 ≠ 1 → (m5Cs X.O n N (N, fs, e)).1 ≠ 2 →
      ∀ cXX X₀, Case3.ColChar φ (strOn hC.le (xy.1.denote N))
        (strOn hC.le (xy.1.denote N)) k (fixPtsD (m5Os X.O n N (N, fs, e))).length
        (fixPtsD (m5Os X.O n N (N, fs, e))) (fixPtsD (m5Os X.O n N (N, fs, e))) cXX →
      Case3.firstStructD (N - n) k (fixPtsD (m5Os X.O n N (N, fs, e)))
        (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fs, e))).length) = some X₀ → X₀.1 = 2 →
      CJFacts (N - n) (cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fs, e)))
          (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fs, e))).length) X₀) →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (cjohnOps (N - n))
          (cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fs, e)))
            (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fs, e))).length) X₀)).2.1 sIn
          gs' d' O' →
      RDOrbit X body DV n N w L (2, cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fs, e)))
        (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fs, e))).length) X₀) sIn Bd gs' d' O')
    (hu₃ : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e →
      (m5Cs X.O n N (N, fs, e)).1 ≠ 1 → (m5Cs X.O n N (N, fs, e)).1 ≠ 2 →
      ∀ cXX X₀, Case3.ColChar φ (strOn hC.le (xy.1.denote N))
        (strOn hC.le (xy.1.denote N)) k (fixPtsD (m5Os X.O n N (N, fs, e))).length
        (fixPtsD (m5Os X.O n N (N, fs, e))) (fixPtsD (m5Os X.O n N (N, fs, e))) cXX →
      Case3.firstStructD (N - n) k (fixPtsD (m5Os X.O n N (N, fs, e)))
        (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fs, e))).length) = some X₀ → X₀.1 = 2 →
      CJFacts (N - n) (cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fs, e)))
          (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fs, e))).length) X₀) →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (cjohnOps (N - n))
          (cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fs, e)))
            (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fs, e))).length) X₀)).2.1 sIn
          gs' d' O' →
      ((labJUD X₀.2.2.2.1.length (markArr (N - n) X₀.2.2.1) X₀.2.2.2.2.2 L O').getD
        (O'.headD 0) []).length ≤ uB) :
    ∃ (fxs fys : GensData) (ex ey : D.denote) (ans : AnswerData D) (ch : List (ℕ × Option ℕ)),
      M5Full DV hC φ k sIn xy.1 fxs ex ∧ M5Full DV hC φ k sIn xy.2 fys ey ∧
      RunsWithin X body (Main.m5CoreCJProg sub
          (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D) k st) ans
        ((ch.map fun x => C x.1 x.2).sum + 2 * certCount N n k * C (n / k) none +
          m5CKCJ X.O n N k (N, fxs, ex) (N, fys, ey) * C (n / k) none +
          m5CH X.O n N sIn w.1.length (N, fxs, ex) (N, fys, ey) * C (w.1.length / 2) none +
          m5CoreWorkNsCJ X.O n N k s sIn Bgen Blift Bo Bd (N, gs, d) (N, fxs, ex)
            (N, fys, ey) w.1.length β B.Bstab B.Btr B.Borb Bk'.Bgen Bk'.Borb Bk'.Bstab
            (fun M => (Bm M).Borb) (fun M => (Bm M).Bstab) (fun M => (Bm M).Btr)
            uB Bg1J₂ Bg1J₃) ∧
      InstData.OK (D := D) (xy, w, PermData.one N, N, gs, d) DV ans ∧
      (∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sIn) ∧
      ChildList w.1.length (m5CFnsCJ X.O n N k (N, fxs, ex) (N, fys, ey) uB)
        (StepChild w.1.length (N - n)) ch := by
  have hOc : MeetsContractOn DV certOps X.O := fun op x h hx =>
    hO op x (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))) hx
  have hPc : ∀ op x, certOps op → GroupPre DV op x → X.Pre op x := fun op x h hx =>
    hPre op x (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))) hx
  have hOcs : MeetsContractOn DV m5CaseOps X.O := fun op x h hx =>
    hO op x (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))) hx
  have hPcs : ∀ op x, m5CaseOps op → GroupPre DV op x → X.Pre op x := fun op x h hx =>
    hPre op x (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))) hx
  have hGv : GroupValid DV N gs d := hI.valid.group
  have hG : IsInvariant (GensData.denote N gs) (baseSet n N) := hC.base
  have hnw : n ≤ w.1.length := m5_n_le_win hI.valid.win hI.le hwS
  have hsub' := m5_hsub_mono_s hsub hs
  have hBgs' : ∀ al ∈ Giant.ksubsD (N - n) k, ∀ b₁ b₂,
      X.B.call GroupOp.generate (N, giantGens X.O n (N, gs, d) al b₁ b₂)
        (giantSetStabModel X.O n (N, gs, d) al b₁ b₂) ≤ β.Bgs := fun al hal => by
    obtain ⟨hp, hl, hlt⟩ := Giant.mem_ksubsD.1 hal
    exact hBgs al (hp.imp Nat.ne_of_lt) hl hlt
  -- the certificates
  obtain ⟨⟨N₁, fxs, ex⟩, hrx, hNx, hvx, hlx, hdx⟩ := RunsWithin.m5CertProg (body := body) hOc
    hPc hφ hGv halt h5 hk h2k xy.1 B hgs hGG₀ Bk' hsk hBgk hBlA hBgs' hBF hsub' hCmono n₀
    (fun J hJ => (m5_stepSub_child h5 hnw hJ).imp_left (·.mono (le_max_left _ _)))
  obtain ⟨⟨N₂, fys, ey⟩, hry, hNy, hvy, hly, hdy⟩ := RunsWithin.m5CertProg (body := body) hOc
    hPc hφ hGv halt h5 hk h2k xy.2 B hgs hGG₀ Bk' hsk hBgk hBlA hBgs' hBF hsub' hCmono n₀
    (fun J hJ => (m5_stepSub_child h5 hnw hJ).imp_left (·.mono (le_max_left _ _)))
  simp only at hNx hNy
  subst N₁ N₂
  have hFx : M5Full DV hC φ k sIn xy.1 fxs ex := ⟨hvx, hlx, hdx⟩
  have hFy : M5Full DV hC φ k sIn xy.2 fys ey := ⟨hvy, hly, hdy⟩
  -- the case decisions
  have hFxG : GensData.denote N fxs ≤ GensData.denote N gs := hFx.2.2 ▸ m5Fmap_le hC φ k _
  have hFyG : GensData.denote N fys ≤ GensData.denote N gs := hFy.2.2 ▸ m5Fmap_le hC φ k _
  have hcx : RunsWithin X body (Main.m5CaseProg n N (N, fxs, ex)) (m5CaseD X.O n N (N, fxs, ex))
      (m5DecCost X.O n N sIn B.Bstab B.Borb β.Bg (fun M => (Bm M).Borb)
        (fun M => (Bm M).Bstab) (N, fxs, ex)) :=
    RunsWithin.m5CaseProg hOcs hPcs B Bm hFx.1 hFx.2.1 (hFxG.trans hGG₀) (hG.mono hFxG) hBg
  have hcy : RunsWithin X body (Main.m5CaseProg n N (N, fys, ey)) (m5CaseD X.O n N (N, fys, ey))
      (m5DecCost X.O n N sIn B.Bstab B.Borb β.Bg (fun M => (Bm M).Borb)
        (fun M => (Bm M).Bstab) (N, fys, ey)) :=
    RunsWithin.m5CaseProg hOcs hPcs B Bm hFy.1 hFy.2.1 (hFyG.trans hGG₀) (hG.mono hFyG) hBg
  -- the dispatch
  obtain ⟨ans, ch, hrun, hok, hg, hch⟩ := RunsWithin.m5DispatchCJ_ns_jpC hO hPre hI hφ halt hwS h5
    hk hm12 B hgs hGG₀ Bk' hsk Bm hsub hCmono hs hB hLg hst β hFx.1 hFy.1 hFx.2.1 hFy.2.1 hFx.2.2
    hFy.2.2 hBgP hBmem hBkA hBlA hBg hBgk hBgs (hBox _ _ hFx)
    (hBoy _ _ hFy) (hBg1₁ _ _ hFx) (hD₁ _ _ hFx) (hBg1₂ₐ _ _ hFx) hBgen₂ₐ
    (fun gs' hv hl h0 => hBpb gs' hv (hl.trans (Nat.add_le_add_left hFx.2.1 _)) h0) hBgm hBlift
    hBker hsK hBgn (hBg1₂ᵦ _ _ hFx) (hBgen₂ᵦ _ _ hFy) (hD₂ᵦ _ _ hFx)
    (hpart₂ᵦ _ _ _ _ hFx hFy) (hBg1₃ _ _ hFx) (hBgen₃ _ _ hFy) (hD₃ _ _ hFx)
    (hnt₃ _ _ _ _ hFx hFy) (hpart₃ _ _ _ _ hFx hFy) hLgJ (hBg1J₂ _ _ hFx) (hLY₂ _ _ hFy)
    (hDJ₂ _ _ hFx) (hu₂ _ _ hFx) (hBg1J₃ _ _ hFx) (hLY₃ _ _ hFy) (hDJ₃ _ _ hFx) (hu₃ _ _ hFx)
  refine ⟨fxs, fys, ex, ey, ans, ch, hFx, hFy,
    (m5CoreCJProg_run hrx hry hcx hcy hrun).mono ?_, ?_, hg, hch⟩
  · have e1 := fullCost_le_count N n k sIn B.Bstab B.Btr B.Borb Bk'.Bgen Bk'.Borb Bk'.Bstab
      β.Bgk (C (n / k) none + 4) β.BlA β.Bgs β.BF
    unfold m5CoreWorkNsCJ
    linarith
  · show AnsOK DV N (w.denote N) (PermData.denote N (PermData.one N)) (GensData.denote N gs)
      (xy.1.denote N) (xy.2.denote N) ans
    rw [PermData.denote_one]
    exact hok

/-- **M5 on the restricted instance with coloured Johnson alignment and no stuck orbit.** Under
the hypotheses of `RunsWithin.m5CoreProg_ns` (with `m · (sIn + 1) ≤ Lg`, `st` not a coloured
Johnson structure, and for every pair of full groups `M5Full` allows, no twins in Case 3), where
the partition hypotheses (a colored `t`-partition with `4t ≤ 3m`) are needed only for a first
leaf of Case 2b or a first structure of Case 3 that is not a Johnson one, and with the
hypotheses of the Johnson routes: the answer is correct for `I`, no orbit is stuck and Case 3
never runs the kernel reduction. The children's factor is `m5CFnsCJ` and the work
`m5CoreWorkNsCJ`.

Stage 14j-5c (`PLAN-14.md` §14.8 item 4): the hypotheses of Cases 2b and 3 carry the premises
under which their routes use them: `x`'s case (Case 2b: tag `2`, not Case 2a; Case 3: tag neither
`1` nor `2`); for the partition routes (`hBg1₂ᵦ`, `hBg1₃`) a first leaf or structure that is not a
Johnson one (`X₀.1 ≠ 2`); for the Johnson routes (`hBg1J₂`, `hDJ₂`, `hu₂`, `hBg1J₃`, `hDJ₃`,
`hu₃`) a Johnson one (`X₀.1 = 2`) with the facts `CJFacts` of its coloured pair.
`RunsWithin.m5CoreCJProg_ns` follows from this one. -/
theorem RunsWithin.m5CoreCJProg_ns_jp (hO : MeetsContractOn DV m5Ops X.O)
    (hPre : ∀ op x, m5Ops op → GroupPre DV op x → X.Pre op x)
    (hI : HInstValid DV (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D))
    {hC : CertSetting (GensData.denote N gs) n} {φ : strGroup hC →* Perm (Fin (N - n))}
    (hφ : IsPhi hC φ)
    (halt : alternatingGroup (Fin (N - n)) ≤ (baseHom _ n hC.base).range)
    (hwS : ∀ u : Fin N, u.val < n → u ∈ w.denote N)
    {k : ℕ} (h5 : 5 ≤ k) (hk : k + 2 ≤ N - n) (h2k : 2 * k ≤ N - n) (hm12 : 12 ≤ N - n)
    {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N sIn G₀) (hgs : gs.length ≤ sIn)
    (hGG₀ : GensData.denote N gs ≤ G₀) {sk : ℕ} (Bk' : BackendBounds X DV k sk ⊤)
    (hsk : sIn ≤ k * (sk + 1)) {sm : ℕ → ℕ} (Bm : ∀ M, BackendBounds X DV M (sm M) ⊤)
    (hsub : HSubSolves X body DV sub
      (fun J => SizeChild (max sIn (supTo sm (w.1.length / 2)))
          (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D) J ∧
        StepChild w.1.length (N - n) (J.winSize, J.baseOpt)) C s)
    (hCmono : ∀ a b, a ≤ b → C a none ≤ C b none) (hs : s ≤ sIn)
    (hB : RDBounds X DV n N sIn Lg Blift Bgen Bo Bk Bcr)
    (hLg : (N - n) * (sIn + 1) ≤ Lg) (hst : st.1 ≠ 2) (β : M5Bounds)
    -- charges on `G`
    (hBgP : X.B.call GroupOp.generate (N - n, gs.map (baseD n N))
      (X.O.run GroupOp.generate (N - n, gs.map (baseD n N))) ≤ β.BgP)
    (hBmem : ∀ g : PermData, g.Valid (N - n) → X.B.call GroupOp.mem (pModel X.O n (N, gs, d), g)
      (X.O.run GroupOp.mem (pModel X.O n (N, gs, d), g)) ≤ β.Bmem)
    (hBkA : X.B.call GroupOp.kernel ((N, gs, d), baseWin n N) (kerModel X.O n (N, gs, d)) ≤
      β.BkA)
    (hBlA : ∀ π : PermData, X.B.call GroupOp.lift ((N, gs, d), (baseWin n N, π))
      (liftModel X.O n (N, gs, d) π) ≤ β.BlA)
    (hBg : ∀ M ≤ N - n, ∀ gs' : GensData, GensData.AllValid M gs' → gs'.length ≤ sIn →
      X.B.call GroupOp.generate (M, gs') (X.O.run GroupOp.generate (M, gs')) ≤ β.Bg)
    (hBgk : ∀ gs' : GensData, GensData.AllValid N gs' →
      gs'.length ≤ k.factorial * (sIn + 1) → GensData.denote N gs' ≤ GensData.denote N gs →
        X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.Bgk)
    (hBgs : ∀ al : List ℕ, al.Nodup → al.length = k → (∀ a ∈ al, a < N - n) → ∀ b₁ b₂,
      X.B.call GroupOp.generate (N, giantGens X.O n (N, gs, d) al b₁ b₂)
        (giantSetStabModel X.O n (N, gs, d) al b₁ b₂) ≤ β.Bgs)
    (hBF : ∀ gs' : GensData, GensData.AllValid N gs' → gs'.length ≤ 2 * sIn →
      GensData.denote N gs' ≤ GensData.denote N gs →
        X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.BF)
    -- Case 1
    (hBox : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e →
      X.B.call GroupOp.orbits ((N, fs, e), baseWin n N)
        (Giant.baseOrbits X.O n N (N, fs, e)) ≤ β.Box)
    (hBoy : ∀ fs e, M5Full DV hC φ k sIn xy.2 fs e →
      X.B.call GroupOp.orbits ((N, fs, e), baseWin n N)
        (Giant.baseOrbits X.O n N (N, fs, e)) ≤ β.Boy)
    (hBg1₁ : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e → X.B.call GroupOp.generate
      (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
        (partGensD (N - n) (Giant.orbitPartModel X.O n N (N, fs, e))))).map
        (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
      (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
        (partGensD (N - n) (Giant.orbitPartModel X.O n N (N, fs, e)))))) ≤ β.Bg1₁)
    (hD₁ : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e →
      ∀ gs' d' O', RDSet DV n N gs w L (Giant.g1Model X.O n (N, gs, d) (partOps (N - n))
        (Giant.orbitPartModel X.O n N (N, fs, e))).2.1 sIn gs' d' O' →
      RDOrbit X body DV n N w L st sIn Bd gs' d' O')
    -- Case 2a
    (hBg1₂ₐ : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e → X.B.call GroupOp.generate
      (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
        ((setOps (N - n)).gens (m5Cs X.O n N (N, fs, e)).2))).map
        (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
      (Giant.g1Model X.O n (N, gs, d) (setOps (N - n)) (m5Cs X.O n N (N, fs, e)).2) ≤
        β.Bg1₂ₐ)
    (hBgen₂ₐ : ∀ gs' : GensData, GensData.AllValid N gs' → gs'.length ≤ sIn + 1 →
      GensData.denote N gs' ≤ GensData.denote N gs →
      X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.Bgen₂ₐ)
    (hBpb : ∀ gs', GensData.AllValid N gs' →
      gs'.length ≤ (sIn + 1) * (sIn + 1) + sIn + sIn → GensData.denote N gs' ≤ G₀ →
      X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.Bpb)
    (hBgm : ∀ (w' : WinData) (σ' : PermData) (gs' : GensData) (d' : D.denote),
      Giant.PbSubP DV G₀ xy w.1.length sIn (xy, w', σ', N, gs', d') →
      X.B.call GroupOp.generate (w'.1.length, GensData.restrictTo (WinData.pos N w') w'.1 gs')
        (X.O.run GroupOp.generate
          (w'.1.length, GensData.restrictTo (WinData.pos N w') w'.1 gs')) ≤ β.Bgm)
    (hBlift : ∀ (w' : WinData) (σ' : PermData) (gs' : GensData) (d' : D.denote),
      Giant.PbSubP DV G₀ xy w.1.length sIn (xy, w', σ', N, gs', d') → ∀ π' : PermData,
      X.B.call GroupOp.lift ((N, gs', d'), (w', π'))
        (X.O.run GroupOp.lift ((N, gs', d'), (w', π'))) ≤ β.Blift)
    (hBker : ∀ (w' : WinData) (σ' : PermData) (gs' : GensData) (d' : D.denote),
      Giant.PbSubP DV G₀ xy w.1.length sIn (xy, w', σ', N, gs', d') →
      X.B.call GroupOp.kernel ((N, gs', d'), w') (X.O.run GroupOp.kernel ((N, gs', d'), w')) ≤
        β.Bker)
    (hsK : ∀ (w' : WinData) (σ' : PermData) (gs' : GensData) (d' : D.denote),
      Giant.PbSubP DV G₀ xy w.1.length sIn (xy, w', σ', N, gs', d') →
      (X.O.run GroupOp.kernel ((N, gs', d'), w')).2.1.length ≤ β.sK)
    (hBgn : ∀ hs : GensData, GensData.AllValid N hs → hs.length ≤ β.sK + s →
      GensData.denote N hs ≤ G₀ →
      X.B.call GroupOp.generate (N, hs) (X.O.run GroupOp.generate (N, hs)) ≤ β.Bgn)
    -- Case 2b
    (hBg1₂ᵦ : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e →
      (m5Cs X.O n N (N, fs, e)).1 = 2 → m5IsA X.O n N (N, fs, e) = false → ∀ X₀ : SoJTree.OutD,
      m5Leaf2b X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 = some X₀ → X₀.1 ≠ 2 →
      X.B.call GroupOp.generate
        (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (Case2b.outGensD (N - n) X₀))).map
          (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
        (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (Case2b.outGensD (N - n) X₀)))) ≤ β.Bg1₂ᵦ)
    (hBgen₂ᵦ : ∀ fs e, M5Full DV hC φ k sIn xy.2 fs e → ∀ gs' : GensData,
      GensData.AllValid N gs' →
      gs'.length ≤ Case2b.c2bR N n (m5Cs X.O n N (N, fs, e)).2.length
        (Case2b.degD X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 - 1)
        (Case2b.sojZ (N - n)) * (sIn + 1) →
      GensData.denote N gs' ≤ GensData.denote N gs →
      X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.Bgen₂ᵦ)
    (hD₂ᵦ : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e → ∀ X₀,
      m5Leaf2b X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 = some X₀ →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (Case2b.outOps (N - n)) X₀).2.1 sIn gs' d' O' →
      RDOrbit X body DV n N w L st sIn Bd gs' d' O')
    (hpart₂ᵦ : ∀ fxs ex fys ey, M5Full DV hC φ k sIn xy.1 fxs ex →
      M5Full DV hC φ k sIn xy.2 fys ey → m5Sel X.O n N (N, fxs, ex) (N, fys, ey) = 4 → ∀ X₀,
      m5Leaf2b X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 = some X₀ → X₀.1 ≠ 2 →
      ∃ (p : CPart (Fin (N - n))) (t : ℕ), (Case2b.outOps (N - n)).dec X₀ = some (Sum.inl p) ∧
        IsColPart Finset.univ t p ∧ 4 * t ≤ 3 * (N - n))
    -- Case 3
    (hBg1₃ : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e →
      (m5Cs X.O n N (N, fs, e)).1 ≠ 1 → (m5Cs X.O n N (N, fs, e)).1 ≠ 2 → ∀ X₀ : SoJTree.OutD,
      Case3.C3First φ (strOn hC.le (xy.1.denote N)) (N - n) k
        (fixPtsD (m5Os X.O n N (N, fs, e))) X₀ → X₀.1 ≠ 2 →
      X.B.call GroupOp.generate
        (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (Case2b.outGensD (N - n) X₀))).map
          (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
        (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (Case2b.outGensD (N - n) X₀)))) ≤ β.Bg1₃)
    (hBgen₃ : ∀ fs e, M5Full DV hC φ k sIn xy.2 fs e → ∀ gs' : GensData,
      GensData.AllValid N gs' →
      gs'.length ≤ Case3.c3R k (fixPtsD (m5Os X.O n N (N, fs, e))).length
        (Case2b.sojZ (N - n)) * (sIn + 1) →
      GensData.denote N gs' ≤ GensData.denote N gs →
      X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.Bgen₃)
    (hD₃ : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e → ∀ X₀,
      Case3.C3First φ (strOn hC.le (xy.1.denote N)) (N - n) k
        (fixPtsD (m5Os X.O n N (N, fs, e))) X₀ →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (Case2b.outOps (N - n)) X₀).2.1 sIn gs' d' O' →
      RDOrbit X body DV n N w L st sIn Bd gs' d' O')
    (hnt₃ : ∀ fxs ex fys ey, M5Full DV hC φ k sIn xy.1 fxs ex →
      M5Full DV hC φ k sIn xy.2 fys ey → m5Sel X.O n N (N, fxs, ex) (N, fys, ey) = 3 →
      ¬ Case3.C3Twins φ (strOn hC.le (xy.1.denote N)) k (fixPtsD (m5Os X.O n N (N, fxs, ex))))
    (hpart₃ : ∀ fxs ex fys ey, M5Full DV hC φ k sIn xy.1 fxs ex →
      M5Full DV hC φ k sIn xy.2 fys ey → m5Sel X.O n N (N, fxs, ex) (N, fys, ey) = 3 → ∀ X₀,
      Case3.C3First φ (strOn hC.le (xy.1.denote N)) (N - n) k
        (fixPtsD (m5Os X.O n N (N, fxs, ex))) X₀ → X₀.1 ≠ 2 →
      ∃ (p : CPart (Fin (N - n))) (t : ℕ), (Case2b.outOps (N - n)).dec X₀ = some (Sum.inl p) ∧
        IsColPart Finset.univ t p ∧ 4 * t ≤ 3 * (N - n))
        -- the coloured Johnson routes
    {uB Bg1J₂ Bg1J₃ : ℕ} (hLgJ : max (N - n) uB.factorial * (sIn + 1) ≤ Lg)
    (hBg1J₂ : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e →
      (m5Cs X.O n N (N, fs, e)).1 = 2 → m5IsA X.O n N (N, fs, e) = false →
      ∀ X₀ : SoJTree.OutD,
      m5Leaf2b X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 = some X₀ → X₀.1 = 2 →
      CJFacts (N - n) (cjFirst2bD N n (m5Cs X.O n N (N, fs, e)).2
          (Case2b.degD X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 - 1) X₀) →
      X.B.call GroupOp.generate
        (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (cjohnGensD (N - n) (cjFirst2bD N n (m5Cs X.O n N (N, fs, e)).2
            (Case2b.degD X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 - 1) X₀)))).map
          (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
        (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (cjohnGensD (N - n) (cjFirst2bD N n (m5Cs X.O n N (N, fs, e)).2
            (Case2b.degD X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 - 1) X₀))))) ≤
        Bg1J₂)
    (hLY₂ : ∀ fs e, M5Full DV hC φ k sIn xy.2 fs e →
      Case2b.c2bR N n (m5Cs X.O n N (N, fs, e)).2.length
      (Case2b.degD X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 - 1)
      (Case2b.sojZ (N - n)) * (sIn + 1) ≤ Lg)
    (hDJ₂ : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e →
      (m5Cs X.O n N (N, fs, e)).1 = 2 → m5IsA X.O n N (N, fs, e) = false →
      ∀ X₀, m5Leaf2b X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 = some X₀ → X₀.1 = 2 →
      CJFacts (N - n) (cjFirst2bD N n (m5Cs X.O n N (N, fs, e)).2
          (Case2b.degD X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 - 1) X₀) →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (cjohnOps (N - n))
          (cjFirst2bD N n (m5Cs X.O n N (N, fs, e)).2
            (Case2b.degD X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 - 1) X₀)).2.1 sIn
          gs' d' O' →
      RDOrbit X body DV n N w L (2, cjFirst2bD N n (m5Cs X.O n N (N, fs, e)).2
        (Case2b.degD X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 - 1) X₀) sIn Bd gs' d' O')
    (hu₂ : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e →
      (m5Cs X.O n N (N, fs, e)).1 = 2 → m5IsA X.O n N (N, fs, e) = false →
      ∀ X₀, m5Leaf2b X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 = some X₀ → X₀.1 = 2 →
      CJFacts (N - n) (cjFirst2bD N n (m5Cs X.O n N (N, fs, e)).2
          (Case2b.degD X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 - 1) X₀) →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (cjohnOps (N - n))
          (cjFirst2bD N n (m5Cs X.O n N (N, fs, e)).2
            (Case2b.degD X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 - 1) X₀)).2.1 sIn
          gs' d' O' →
      ((labJUD X₀.2.2.2.1.length (markArr (N - n) X₀.2.2.1) X₀.2.2.2.2.2 L O').getD
        (O'.headD 0) []).length ≤ uB)
    (hBg1J₃ : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e →
      (m5Cs X.O n N (N, fs, e)).1 ≠ 1 → (m5Cs X.O n N (N, fs, e)).1 ≠ 2 →
      ∀ cXX X₀, Case3.ColChar φ (strOn hC.le (xy.1.denote N))
        (strOn hC.le (xy.1.denote N)) k (fixPtsD (m5Os X.O n N (N, fs, e))).length
        (fixPtsD (m5Os X.O n N (N, fs, e))) (fixPtsD (m5Os X.O n N (N, fs, e))) cXX →
      Case3.firstStructD (N - n) k (fixPtsD (m5Os X.O n N (N, fs, e)))
        (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fs, e))).length) = some X₀ → X₀.1 = 2 →
      CJFacts (N - n) (cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fs, e)))
          (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fs, e))).length) X₀) →
      X.B.call GroupOp.generate
        (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (cjohnGensD (N - n) (cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fs, e)))
            (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fs, e))).length) X₀)))).map
          (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
        (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (cjohnGensD (N - n) (cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fs, e)))
            (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fs, e))).length) X₀))))) ≤ Bg1J₃)
    (hLY₃ : ∀ fs e, M5Full DV hC φ k sIn xy.2 fs e →
      Case3.c3R k (fixPtsD (m5Os X.O n N (N, fs, e))).length (Case2b.sojZ (N - n)) *
      (sIn + 1) ≤ Lg)
    (hDJ₃ : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e →
      (m5Cs X.O n N (N, fs, e)).1 ≠ 1 → (m5Cs X.O n N (N, fs, e)).1 ≠ 2 →
      ∀ cXX X₀, Case3.ColChar φ (strOn hC.le (xy.1.denote N))
        (strOn hC.le (xy.1.denote N)) k (fixPtsD (m5Os X.O n N (N, fs, e))).length
        (fixPtsD (m5Os X.O n N (N, fs, e))) (fixPtsD (m5Os X.O n N (N, fs, e))) cXX →
      Case3.firstStructD (N - n) k (fixPtsD (m5Os X.O n N (N, fs, e)))
        (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fs, e))).length) = some X₀ → X₀.1 = 2 →
      CJFacts (N - n) (cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fs, e)))
          (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fs, e))).length) X₀) →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (cjohnOps (N - n))
          (cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fs, e)))
            (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fs, e))).length) X₀)).2.1 sIn
          gs' d' O' →
      RDOrbit X body DV n N w L (2, cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fs, e)))
        (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fs, e))).length) X₀) sIn Bd gs' d' O')
    (hu₃ : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e →
      (m5Cs X.O n N (N, fs, e)).1 ≠ 1 → (m5Cs X.O n N (N, fs, e)).1 ≠ 2 →
      ∀ cXX X₀, Case3.ColChar φ (strOn hC.le (xy.1.denote N))
        (strOn hC.le (xy.1.denote N)) k (fixPtsD (m5Os X.O n N (N, fs, e))).length
        (fixPtsD (m5Os X.O n N (N, fs, e))) (fixPtsD (m5Os X.O n N (N, fs, e))) cXX →
      Case3.firstStructD (N - n) k (fixPtsD (m5Os X.O n N (N, fs, e)))
        (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fs, e))).length) = some X₀ → X₀.1 = 2 →
      CJFacts (N - n) (cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fs, e)))
          (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fs, e))).length) X₀) →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (cjohnOps (N - n))
          (cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fs, e)))
            (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fs, e))).length) X₀)).2.1 sIn
          gs' d' O' →
      ((labJUD X₀.2.2.2.1.length (markArr (N - n) X₀.2.2.1) X₀.2.2.2.2.2 L O').getD
        (O'.headD 0) []).length ≤ uB) :
    ∃ (fxs fys : GensData) (ex ey : D.denote) (ans : AnswerData D) (ch : List (ℕ × Option ℕ)),
      M5Full DV hC φ k sIn xy.1 fxs ex ∧ M5Full DV hC φ k sIn xy.2 fys ey ∧
      RunsWithin X body (Main.m5CoreCJProg sub
          (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D) k st) ans
        ((ch.map fun x => C x.1 x.2).sum + 2 * certCount N n k * C (n / k) none +
          m5CKCJ X.O n N k (N, fxs, ex) (N, fys, ey) * C (n / k) none +
          m5CH X.O n N sIn w.1.length (N, fxs, ex) (N, fys, ey) * C (w.1.length / 2) none +
          m5CoreWorkNsCJ X.O n N k s sIn Bgen Blift Bo Bd (N, gs, d) (N, fxs, ex)
            (N, fys, ey) w.1.length β B.Bstab B.Btr B.Borb Bk'.Bgen Bk'.Borb Bk'.Bstab
            (fun M => (Bm M).Borb) (fun M => (Bm M).Bstab) (fun M => (Bm M).Btr)
            uB Bg1J₂ Bg1J₃) ∧
      InstData.OK (D := D) (xy, w, PermData.one N, N, gs, d) DV ans ∧
      (∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sIn) ∧
      ChildList w.1.length (m5CFnsCJ X.O n N k (N, fxs, ex) (N, fys, ey) uB)
        (StepChild w.1.length (N - n)) ch :=
  RunsWithin.m5CoreCJProg_ns_jpC hO hPre hI hφ halt hwS h5 hk h2k hm12 B hgs hGG₀ Bk' hsk Bm hsub
    hCmono hs hB hLg hst β hBgP hBmem hBkA hBlA hBg hBgk hBgs hBF hBox hBoy hBg1₁ hD₁ hBg1₂ₐ hBgen₂ₐ
    hBpb hBgm hBlift hBker hsK hBgn hBg1₂ᵦ (fun fs e hF _ _ => hBgen₂ᵦ fs e hF) hD₂ᵦ hpart₂ᵦ hBg1₃
    hBgen₃ hD₃ hnt₃ hpart₃ hLgJ hBg1J₂ (fun fs e hF _ _ => hLY₂ fs e hF) hDJ₂ hu₂ hBg1J₃ hLY₃ hDJ₃
    hu₃

/-- `RunsWithin.m5CoreCJProg_ns_jp` with Case 2b's Johnson-route hypotheses stated for every first
leaf. -/
theorem RunsWithin.m5CoreCJProg_ns (hO : MeetsContractOn DV m5Ops X.O)
    (hPre : ∀ op x, m5Ops op → GroupPre DV op x → X.Pre op x)
    (hI : HInstValid DV (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D))
    {hC : CertSetting (GensData.denote N gs) n} {φ : strGroup hC →* Perm (Fin (N - n))}
    (hφ : IsPhi hC φ)
    (halt : alternatingGroup (Fin (N - n)) ≤ (baseHom _ n hC.base).range)
    (hwS : ∀ u : Fin N, u.val < n → u ∈ w.denote N)
    {k : ℕ} (h5 : 5 ≤ k) (hk : k + 2 ≤ N - n) (h2k : 2 * k ≤ N - n) (hm12 : 12 ≤ N - n)
    {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N sIn G₀) (hgs : gs.length ≤ sIn)
    (hGG₀ : GensData.denote N gs ≤ G₀) {sk : ℕ} (Bk' : BackendBounds X DV k sk ⊤)
    (hsk : sIn ≤ k * (sk + 1)) {sm : ℕ → ℕ} (Bm : ∀ M, BackendBounds X DV M (sm M) ⊤)
    (hsub : HSubSolves X body DV sub
      (fun J => SizeChild (max sIn (supTo sm (w.1.length / 2)))
          (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D) J ∧
        StepChild w.1.length (N - n) (J.winSize, J.baseOpt)) C s)
    (hCmono : ∀ a b, a ≤ b → C a none ≤ C b none) (hs : s ≤ sIn)
    (hB : RDBounds X DV n N sIn Lg Blift Bgen Bo Bk Bcr)
    (hLg : (N - n) * (sIn + 1) ≤ Lg) (hst : st.1 ≠ 2) (β : M5Bounds)
    -- charges on `G`
    (hBgP : X.B.call GroupOp.generate (N - n, gs.map (baseD n N))
      (X.O.run GroupOp.generate (N - n, gs.map (baseD n N))) ≤ β.BgP)
    (hBmem : ∀ g : PermData, g.Valid (N - n) → X.B.call GroupOp.mem (pModel X.O n (N, gs, d), g)
      (X.O.run GroupOp.mem (pModel X.O n (N, gs, d), g)) ≤ β.Bmem)
    (hBkA : X.B.call GroupOp.kernel ((N, gs, d), baseWin n N) (kerModel X.O n (N, gs, d)) ≤
      β.BkA)
    (hBlA : ∀ π : PermData, X.B.call GroupOp.lift ((N, gs, d), (baseWin n N, π))
      (liftModel X.O n (N, gs, d) π) ≤ β.BlA)
    (hBg : ∀ M ≤ N - n, ∀ gs' : GensData, GensData.AllValid M gs' → gs'.length ≤ sIn →
      X.B.call GroupOp.generate (M, gs') (X.O.run GroupOp.generate (M, gs')) ≤ β.Bg)
    (hBgk : ∀ gs' : GensData, GensData.AllValid N gs' →
      gs'.length ≤ k.factorial * (sIn + 1) → GensData.denote N gs' ≤ GensData.denote N gs →
        X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.Bgk)
    (hBgs : ∀ al : List ℕ, al.Nodup → al.length = k → (∀ a ∈ al, a < N - n) → ∀ b₁ b₂,
      X.B.call GroupOp.generate (N, giantGens X.O n (N, gs, d) al b₁ b₂)
        (giantSetStabModel X.O n (N, gs, d) al b₁ b₂) ≤ β.Bgs)
    (hBF : ∀ gs' : GensData, GensData.AllValid N gs' → gs'.length ≤ 2 * sIn →
      GensData.denote N gs' ≤ GensData.denote N gs →
        X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.BF)
    -- Case 1
    (hBox : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e →
      X.B.call GroupOp.orbits ((N, fs, e), baseWin n N)
        (Giant.baseOrbits X.O n N (N, fs, e)) ≤ β.Box)
    (hBoy : ∀ fs e, M5Full DV hC φ k sIn xy.2 fs e →
      X.B.call GroupOp.orbits ((N, fs, e), baseWin n N)
        (Giant.baseOrbits X.O n N (N, fs, e)) ≤ β.Boy)
    (hBg1₁ : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e → X.B.call GroupOp.generate
      (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
        (partGensD (N - n) (Giant.orbitPartModel X.O n N (N, fs, e))))).map
        (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
      (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
        (partGensD (N - n) (Giant.orbitPartModel X.O n N (N, fs, e)))))) ≤ β.Bg1₁)
    (hD₁ : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e →
      ∀ gs' d' O', RDSet DV n N gs w L (Giant.g1Model X.O n (N, gs, d) (partOps (N - n))
        (Giant.orbitPartModel X.O n N (N, fs, e))).2.1 sIn gs' d' O' →
      RDOrbit X body DV n N w L st sIn Bd gs' d' O')
    -- Case 2a
    (hBg1₂ₐ : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e → X.B.call GroupOp.generate
      (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
        ((setOps (N - n)).gens (m5Cs X.O n N (N, fs, e)).2))).map
        (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
      (Giant.g1Model X.O n (N, gs, d) (setOps (N - n)) (m5Cs X.O n N (N, fs, e)).2) ≤
        β.Bg1₂ₐ)
    (hBgen₂ₐ : ∀ gs' : GensData, GensData.AllValid N gs' → gs'.length ≤ sIn + 1 →
      GensData.denote N gs' ≤ GensData.denote N gs →
      X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.Bgen₂ₐ)
    (hBpb : ∀ gs', GensData.AllValid N gs' →
      gs'.length ≤ (sIn + 1) * (sIn + 1) + sIn + sIn → GensData.denote N gs' ≤ G₀ →
      X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.Bpb)
    (hBgm : ∀ (w' : WinData) (σ' : PermData) (gs' : GensData) (d' : D.denote),
      Giant.PbSubP DV G₀ xy w.1.length sIn (xy, w', σ', N, gs', d') →
      X.B.call GroupOp.generate (w'.1.length, GensData.restrictTo (WinData.pos N w') w'.1 gs')
        (X.O.run GroupOp.generate
          (w'.1.length, GensData.restrictTo (WinData.pos N w') w'.1 gs')) ≤ β.Bgm)
    (hBlift : ∀ (w' : WinData) (σ' : PermData) (gs' : GensData) (d' : D.denote),
      Giant.PbSubP DV G₀ xy w.1.length sIn (xy, w', σ', N, gs', d') → ∀ π' : PermData,
      X.B.call GroupOp.lift ((N, gs', d'), (w', π'))
        (X.O.run GroupOp.lift ((N, gs', d'), (w', π'))) ≤ β.Blift)
    (hBker : ∀ (w' : WinData) (σ' : PermData) (gs' : GensData) (d' : D.denote),
      Giant.PbSubP DV G₀ xy w.1.length sIn (xy, w', σ', N, gs', d') →
      X.B.call GroupOp.kernel ((N, gs', d'), w') (X.O.run GroupOp.kernel ((N, gs', d'), w')) ≤
        β.Bker)
    (hsK : ∀ (w' : WinData) (σ' : PermData) (gs' : GensData) (d' : D.denote),
      Giant.PbSubP DV G₀ xy w.1.length sIn (xy, w', σ', N, gs', d') →
      (X.O.run GroupOp.kernel ((N, gs', d'), w')).2.1.length ≤ β.sK)
    (hBgn : ∀ hs : GensData, GensData.AllValid N hs → hs.length ≤ β.sK + s →
      GensData.denote N hs ≤ G₀ →
      X.B.call GroupOp.generate (N, hs) (X.O.run GroupOp.generate (N, hs)) ≤ β.Bgn)
    -- Case 2b
    (hBg1₂ᵦ : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e → ∀ X₀ : SoJTree.OutD,
      m5Leaf2b X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 = some X₀ →
      X.B.call GroupOp.generate
        (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (Case2b.outGensD (N - n) X₀))).map
          (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
        (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (Case2b.outGensD (N - n) X₀)))) ≤ β.Bg1₂ᵦ)
    (hBgen₂ᵦ : ∀ fs e, M5Full DV hC φ k sIn xy.2 fs e → ∀ gs' : GensData,
      GensData.AllValid N gs' →
      gs'.length ≤ Case2b.c2bR N n (m5Cs X.O n N (N, fs, e)).2.length
        (Case2b.degD X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 - 1)
        (Case2b.sojZ (N - n)) * (sIn + 1) →
      GensData.denote N gs' ≤ GensData.denote N gs →
      X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.Bgen₂ᵦ)
    (hD₂ᵦ : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e → ∀ X₀,
      m5Leaf2b X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 = some X₀ →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (Case2b.outOps (N - n)) X₀).2.1 sIn gs' d' O' →
      RDOrbit X body DV n N w L st sIn Bd gs' d' O')
    (hpart₂ᵦ : ∀ fxs ex fys ey, M5Full DV hC φ k sIn xy.1 fxs ex →
      M5Full DV hC φ k sIn xy.2 fys ey → m5Sel X.O n N (N, fxs, ex) (N, fys, ey) = 4 → ∀ X₀,
      m5Leaf2b X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 = some X₀ → X₀.1 ≠ 2 →
      ∃ (p : CPart (Fin (N - n))) (t : ℕ), (Case2b.outOps (N - n)).dec X₀ = some (Sum.inl p) ∧
        IsColPart Finset.univ t p ∧ 4 * t ≤ 3 * (N - n))
    -- Case 3
    (hBg1₃ : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e → ∀ X₀ : SoJTree.OutD,
      Case3.C3First φ (strOn hC.le (xy.1.denote N)) (N - n) k
        (fixPtsD (m5Os X.O n N (N, fs, e))) X₀ →
      X.B.call GroupOp.generate
        (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (Case2b.outGensD (N - n) X₀))).map
          (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
        (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (Case2b.outGensD (N - n) X₀)))) ≤ β.Bg1₃)
    (hBgen₃ : ∀ fs e, M5Full DV hC φ k sIn xy.2 fs e → ∀ gs' : GensData,
      GensData.AllValid N gs' →
      gs'.length ≤ Case3.c3R k (fixPtsD (m5Os X.O n N (N, fs, e))).length
        (Case2b.sojZ (N - n)) * (sIn + 1) →
      GensData.denote N gs' ≤ GensData.denote N gs →
      X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.Bgen₃)
    (hD₃ : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e → ∀ X₀,
      Case3.C3First φ (strOn hC.le (xy.1.denote N)) (N - n) k
        (fixPtsD (m5Os X.O n N (N, fs, e))) X₀ →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (Case2b.outOps (N - n)) X₀).2.1 sIn gs' d' O' →
      RDOrbit X body DV n N w L st sIn Bd gs' d' O')
    (hnt₃ : ∀ fxs ex fys ey, M5Full DV hC φ k sIn xy.1 fxs ex →
      M5Full DV hC φ k sIn xy.2 fys ey → m5Sel X.O n N (N, fxs, ex) (N, fys, ey) = 3 →
      ¬ Case3.C3Twins φ (strOn hC.le (xy.1.denote N)) k (fixPtsD (m5Os X.O n N (N, fxs, ex))))
    (hpart₃ : ∀ fxs ex fys ey, M5Full DV hC φ k sIn xy.1 fxs ex →
      M5Full DV hC φ k sIn xy.2 fys ey → m5Sel X.O n N (N, fxs, ex) (N, fys, ey) = 3 → ∀ X₀,
      Case3.C3First φ (strOn hC.le (xy.1.denote N)) (N - n) k
        (fixPtsD (m5Os X.O n N (N, fxs, ex))) X₀ → X₀.1 ≠ 2 →
      ∃ (p : CPart (Fin (N - n))) (t : ℕ), (Case2b.outOps (N - n)).dec X₀ = some (Sum.inl p) ∧
        IsColPart Finset.univ t p ∧ 4 * t ≤ 3 * (N - n))
        -- the coloured Johnson routes
    {uB Bg1J₂ Bg1J₃ : ℕ} (hLgJ : max (N - n) uB.factorial * (sIn + 1) ≤ Lg)
    (hBg1J₂ : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e →
      ∀ X₀ : SoJTree.OutD,
      m5Leaf2b X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 = some X₀ →
      X.B.call GroupOp.generate
        (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (cjohnGensD (N - n) (cjFirst2bD N n (m5Cs X.O n N (N, fs, e)).2
            (Case2b.degD X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 - 1) X₀)))).map
          (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
        (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (cjohnGensD (N - n) (cjFirst2bD N n (m5Cs X.O n N (N, fs, e)).2
            (Case2b.degD X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 - 1) X₀))))) ≤
        Bg1J₂)
    (hLY₂ : ∀ fs e, M5Full DV hC φ k sIn xy.2 fs e →
      Case2b.c2bR N n (m5Cs X.O n N (N, fs, e)).2.length
      (Case2b.degD X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 - 1)
      (Case2b.sojZ (N - n)) * (sIn + 1) ≤ Lg)
    (hDJ₂ : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e →
      ∀ X₀, m5Leaf2b X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 = some X₀ →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (cjohnOps (N - n))
          (cjFirst2bD N n (m5Cs X.O n N (N, fs, e)).2
            (Case2b.degD X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 - 1) X₀)).2.1 sIn
          gs' d' O' →
      RDOrbit X body DV n N w L (2, cjFirst2bD N n (m5Cs X.O n N (N, fs, e)).2
        (Case2b.degD X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 - 1) X₀) sIn Bd gs' d' O')
    (hu₂ : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e →
      ∀ X₀, m5Leaf2b X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 = some X₀ →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (cjohnOps (N - n))
          (cjFirst2bD N n (m5Cs X.O n N (N, fs, e)).2
            (Case2b.degD X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 - 1) X₀)).2.1 sIn
          gs' d' O' →
      ((labJUD X₀.2.2.2.1.length (markArr (N - n) X₀.2.2.1) X₀.2.2.2.2.2 L O').getD
        (O'.headD 0) []).length ≤ uB)
    (hBg1J₃ : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e →
      ∀ cXX X₀, Case3.ColChar φ (strOn hC.le (xy.1.denote N))
        (strOn hC.le (xy.1.denote N)) k (fixPtsD (m5Os X.O n N (N, fs, e))).length
        (fixPtsD (m5Os X.O n N (N, fs, e))) (fixPtsD (m5Os X.O n N (N, fs, e))) cXX →
      Case3.firstStructD (N - n) k (fixPtsD (m5Os X.O n N (N, fs, e)))
        (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fs, e))).length) = some X₀ → X₀.1 = 2 →
      X.B.call GroupOp.generate
        (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (cjohnGensD (N - n) (cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fs, e)))
            (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fs, e))).length) X₀)))).map
          (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
        (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (cjohnGensD (N - n) (cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fs, e)))
            (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fs, e))).length) X₀))))) ≤ Bg1J₃)
    (hLY₃ : ∀ fs e, M5Full DV hC φ k sIn xy.2 fs e →
      Case3.c3R k (fixPtsD (m5Os X.O n N (N, fs, e))).length (Case2b.sojZ (N - n)) *
      (sIn + 1) ≤ Lg)
    (hDJ₃ : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e →
      ∀ cXX X₀, Case3.ColChar φ (strOn hC.le (xy.1.denote N))
        (strOn hC.le (xy.1.denote N)) k (fixPtsD (m5Os X.O n N (N, fs, e))).length
        (fixPtsD (m5Os X.O n N (N, fs, e))) (fixPtsD (m5Os X.O n N (N, fs, e))) cXX →
      Case3.firstStructD (N - n) k (fixPtsD (m5Os X.O n N (N, fs, e)))
        (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fs, e))).length) = some X₀ → X₀.1 = 2 →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (cjohnOps (N - n))
          (cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fs, e)))
            (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fs, e))).length) X₀)).2.1 sIn
          gs' d' O' →
      RDOrbit X body DV n N w L (2, cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fs, e)))
        (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fs, e))).length) X₀) sIn Bd gs' d' O')
    (hu₃ : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e →
      ∀ cXX X₀, Case3.ColChar φ (strOn hC.le (xy.1.denote N))
        (strOn hC.le (xy.1.denote N)) k (fixPtsD (m5Os X.O n N (N, fs, e))).length
        (fixPtsD (m5Os X.O n N (N, fs, e))) (fixPtsD (m5Os X.O n N (N, fs, e))) cXX →
      Case3.firstStructD (N - n) k (fixPtsD (m5Os X.O n N (N, fs, e)))
        (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fs, e))).length) = some X₀ → X₀.1 = 2 →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (cjohnOps (N - n))
          (cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fs, e)))
            (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fs, e))).length) X₀)).2.1 sIn
          gs' d' O' →
      ((labJUD X₀.2.2.2.1.length (markArr (N - n) X₀.2.2.1) X₀.2.2.2.2.2 L O').getD
        (O'.headD 0) []).length ≤ uB) :
    ∃ (fxs fys : GensData) (ex ey : D.denote) (ans : AnswerData D) (ch : List (ℕ × Option ℕ)),
      M5Full DV hC φ k sIn xy.1 fxs ex ∧ M5Full DV hC φ k sIn xy.2 fys ey ∧
      RunsWithin X body (Main.m5CoreCJProg sub
          (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D) k st) ans
        ((ch.map fun x => C x.1 x.2).sum + 2 * certCount N n k * C (n / k) none +
          m5CKCJ X.O n N k (N, fxs, ex) (N, fys, ey) * C (n / k) none +
          m5CH X.O n N sIn w.1.length (N, fxs, ex) (N, fys, ey) * C (w.1.length / 2) none +
          m5CoreWorkNsCJ X.O n N k s sIn Bgen Blift Bo Bd (N, gs, d) (N, fxs, ex)
            (N, fys, ey) w.1.length β B.Bstab B.Btr B.Borb Bk'.Bgen Bk'.Borb Bk'.Bstab
            (fun M => (Bm M).Borb) (fun M => (Bm M).Bstab) (fun M => (Bm M).Btr)
            uB Bg1J₂ Bg1J₃) ∧
      InstData.OK (D := D) (xy, w, PermData.one N, N, gs, d) DV ans ∧
      (∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sIn) ∧
      ChildList w.1.length (m5CFnsCJ X.O n N k (N, fxs, ex) (N, fys, ey) uB)
        (StepChild w.1.length (N - n)) ch :=
  RunsWithin.m5CoreCJProg_ns_jp hO hPre hI hφ halt hwS h5 hk h2k hm12 B hgs hGG₀ Bk' hsk Bm hsub
    hCmono hs hB hLg hst β hBgP hBmem hBkA hBlA hBg hBgk hBgs hBF hBox hBoy hBg1₁ hD₁ hBg1₂ₐ hBgen₂ₐ
    hBpb hBgm hBlift hBker hsK hBgn (fun fs e hF _ _ X₀ h _ => hBg1₂ᵦ fs e hF X₀ h) hBgen₂ᵦ hD₂ᵦ
    hpart₂ᵦ (fun fs e hF _ _ X₀ h _ => hBg1₃ fs e hF X₀ h) hBgen₃ hD₃ hnt₃ hpart₃ hLgJ
    (fun fs e hF _ _ X₀ h _ _ => hBg1J₂ fs e hF X₀ h) hLY₂
    (fun fs e hF _ _ X₀ h _ _ => hDJ₂ fs e hF X₀ h) (fun fs e hF _ _ X₀ h _ _ => hu₂ fs e hF X₀ h)
    (fun fs e hF _ _ cXX X₀ h₁ h₂ h₃ _ => hBg1J₃ fs e hF cXX X₀ h₁ h₂ h₃) hLY₃
    (fun fs e hF _ _ cXX X₀ h₁ h₂ h₃ _ => hDJ₃ fs e hF cXX X₀ h₁ h₂ h₃)
    (fun fs e hF _ _ cXX X₀ h₁ h₂ h₃ _ => hu₃ fs e hF cXX X₀ h₁ h₂ h₃)

end CoreNsCJ

section StepSpecCJ

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}
  {sub : HInstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)}
  {C : ℕ → Option ℕ → ℕ} {s : ℕ} {xy : StrData × StrData} {w : WinData}
  {N : ℕ} {gs : GensData} {d : D.denote} {n₀ n : ℕ} {L : LabelData} {st : ℕ × CJData}
  {sIn Lg Blift Bgen Bo Bk Bcr Bd : ℕ}
  {xyP : StrData × StrData} {wP : WinData} {σP : PermData} {NP : ℕ} {gsP : GensData}
  {dP : D.denote} {nP : ℕ} {LP : LabelData}

/-- **M5 with coloured Johnson alignment as a step.** As `RunsWithin.m5StepProg`, with
`m5CoreCJProg` on the restricted instance: under the hypotheses of `RunsWithin.m5StepProg` and
those of the Johnson routes (`RunsWithin.m5CoreCJProg_jp`, for every certificate setting and every
`φ`), the answer is correct for `(wP, σP • GP, xP, yP)`; the cost is `rbCost` around M5's; the
children of the step are `StepChild |wP| m` with factor `m5CFCJ`, and M5's sub-calls without a
hint are counted (`2 · certCount + m5CKCJ` on windows of at most `|wP| / k` points, `m5CH` on
windows of at most `|wP| / 2`).

Stage 14j-5c (`PLAN-14.md` §14.8 item 4): the hypotheses of Cases 2b and 3 carry the premises
under which their routes use them: `x`'s case (Case 2b: tag `2`, not Case 2a; Case 3: tag neither
`1` nor `2`); for the partition routes (`hBg1₂ᵦ`, `hBg1₃`) a first leaf or structure that is not a
Johnson one (`X₀.1 ≠ 2`); for the Johnson routes (`hBg1J₂`, `hDJ₂`, `hu₂`, `hBg1J₃`, `hDJ₃`,
`hu₃`) a Johnson one (`X₀.1 = 2`) with the facts `CJFacts` of its coloured pair.
`RunsWithin.m5StepCJProg` follows from this one. -/
theorem RunsWithin.m5StepCJProg_jp (hO : MeetsContractOn DV m5Ops X.O)
    (hPre : ∀ op x, m5Ops op → GroupPre DV op x → X.Pre op x)
    -- the parent
    (hIP : HInstValid DV
      (((xyP, (wP, (σP, (NP, gsP, dP)))), (n₀, (nP, some LP))) : HInstData D))
    {hBP : IsInvariant (GensData.denote NP gsP) (baseSet nP NP)}
    (haltP : alternatingGroup (Fin (NP - nP)) ≤ (baseHom (GensData.denote NP gsP) nP hBP).range)
    {sm : ℕ → ℕ}
    (hsubP : HSubSolves X body DV sub
      (fun J => SizeChild (max sIn (supTo sm (wP.1.length / 2)))
        (((xyP, (wP, (σP, (NP, gsP, dP)))), (n₀, (nP, some LP))) : HInstData D) J ∧
        StepChild wP.1.length (NP - nP) (J.winSize, J.baseOpt)) C s)
    -- the restricted instance
    (hG' : X.O.run GroupOp.generate ((rbPts nP NP wP).length, rbGens nP NP wP gsP) =
      (N, gs, d))
    (hxy : xy = (StrData.restrictTo (rbPts nP NP wP) xyP.1,
      StrData.restrictComp (rbPts nP NP wP) xyP.2 σP))
    (hw : w = WinData.ofPoints N (List.range wP.1.length)) (hn : n = wP.1.length)
    (hL : L = rbLabels wP LP)
    -- the certificates, the backends and the numbers
    {k : ℕ} (h5 : 5 ≤ k) (hk : k + 2 ≤ NP - nP) (h2k : 2 * k ≤ NP - nP)
    (hm12 : 12 ≤ NP - nP)
    {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N sIn G₀) (hgs : gs.length ≤ sIn)
    (hGG₀ : GensData.denote N gs ≤ G₀) {sk : ℕ} (Bk' : BackendBounds X DV k sk ⊤)
    (hsk : sIn ≤ k * (sk + 1)) (Bm : ∀ M, BackendBounds X DV M (sm M) ⊤)
    (hCmono : ∀ a b, a ≤ b → C a none ≤ C b none) (hs : s ≤ sIn)
    (hB : RDBounds X DV n N sIn Lg Blift Bgen Bo Bk Bcr)
    (hLg : (NP - nP).factorial * (sIn + 1) ≤ Lg) (hst : st.1 ≠ 2) (β : M5Bounds)
    -- M5's charges on the restricted instance
    (hBgP : X.B.call GroupOp.generate (N - n, gs.map (baseD n N))
      (X.O.run GroupOp.generate (N - n, gs.map (baseD n N))) ≤ β.BgP)
    (hBmem : ∀ g : PermData, g.Valid (N - n) → X.B.call GroupOp.mem (pModel X.O n (N, gs, d), g)
      (X.O.run GroupOp.mem (pModel X.O n (N, gs, d), g)) ≤ β.Bmem)
    (hBkA : X.B.call GroupOp.kernel ((N, gs, d), baseWin n N) (kerModel X.O n (N, gs, d)) ≤
      β.BkA)
    (hBlA : ∀ π : PermData, X.B.call GroupOp.lift ((N, gs, d), (baseWin n N, π))
      (liftModel X.O n (N, gs, d) π) ≤ β.BlA)
    (hBg : ∀ M ≤ N - n, ∀ gs' : GensData, GensData.AllValid M gs' → gs'.length ≤ sIn →
      X.B.call GroupOp.generate (M, gs') (X.O.run GroupOp.generate (M, gs')) ≤ β.Bg)
    (hBgk : ∀ gs' : GensData, GensData.AllValid N gs' →
      gs'.length ≤ k.factorial * (sIn + 1) → GensData.denote N gs' ≤ GensData.denote N gs →
        X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.Bgk)
    (hBgs : ∀ al : List ℕ, al.Nodup → al.length = k → (∀ a ∈ al, a < N - n) → ∀ b₁ b₂,
      X.B.call GroupOp.generate (N, giantGens X.O n (N, gs, d) al b₁ b₂)
        (giantSetStabModel X.O n (N, gs, d) al b₁ b₂) ≤ β.Bgs)
    (hBF : ∀ gs' : GensData, GensData.AllValid N gs' → gs'.length ≤ 2 * sIn →
      GensData.denote N gs' ≤ GensData.denote N gs →
        X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.BF)
    (hBk3 : X.B.call GroupOp.kernel ((N, gs, d), baseWin n N) (kerModel X.O n (N, gs, d)) ≤
      β.Bk3)
    (hBo3 : X.B.call GroupOp.orbits (kerModel X.O n (N, gs, d), w)
      (krOrbits X.O n (N, gs, d) w) ≤ β.Bo3)
    (hBcr3 : X.B.call GroupOp.cosetReps ((N, gs, d), kerModel X.O n (N, gs, d))
      (kerReps X.O n (N, gs, d)) ≤ β.Bcr3)
    (hB3 : ∀ hs : GensData, GensData.AllValid N hs →
      hs.length ≤ (kerReps X.O n (N, gs, d)).length *
        (max s (kerModel X.O n (N, gs, d)).2.1.length + 1) →
      GensData.denote N hs ≤ GensData.denote N gs →
      X.B.call GroupOp.generate (N, hs) (X.O.run GroupOp.generate (N, hs)) ≤ β.Bgen3)
    -- Case 1
    (hBox : ∀ (hC : CertSetting (GensData.denote N gs) n)
      (φ : strGroup hC →* Perm (Fin (N - n))), IsPhi hC φ →
      ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e →
      X.B.call GroupOp.orbits ((N, fs, e), baseWin n N)
        (Giant.baseOrbits X.O n N (N, fs, e)) ≤ β.Box)
    (hBoy : ∀ (hC : CertSetting (GensData.denote N gs) n)
      (φ : strGroup hC →* Perm (Fin (N - n))), IsPhi hC φ →
      ∀ fs e, M5Full DV hC φ k sIn xy.2 fs e →
      X.B.call GroupOp.orbits ((N, fs, e), baseWin n N)
        (Giant.baseOrbits X.O n N (N, fs, e)) ≤ β.Boy)
    (hBg1₁ : ∀ (hC : CertSetting (GensData.denote N gs) n)
      (φ : strGroup hC →* Perm (Fin (N - n))), IsPhi hC φ →
      ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e → X.B.call GroupOp.generate
      (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
        (partGensD (N - n) (Giant.orbitPartModel X.O n N (N, fs, e))))).map
        (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
      (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
        (partGensD (N - n) (Giant.orbitPartModel X.O n N (N, fs, e)))))) ≤ β.Bg1₁)
    (hD₁ : ∀ (hC : CertSetting (GensData.denote N gs) n)
      (φ : strGroup hC →* Perm (Fin (N - n))), IsPhi hC φ →
      ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e →
      ∀ gs' d' O', RDSet DV n N gs w L (Giant.g1Model X.O n (N, gs, d) (partOps (N - n))
        (Giant.orbitPartModel X.O n N (N, fs, e))).2.1 sIn gs' d' O' →
      RDOrbit X body DV n N w L st sIn Bd gs' d' O')
    -- Case 2a
    (hBg1₂ₐ : ∀ (hC : CertSetting (GensData.denote N gs) n)
      (φ : strGroup hC →* Perm (Fin (N - n))), IsPhi hC φ →
      ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e → X.B.call GroupOp.generate
      (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
        ((setOps (N - n)).gens (m5Cs X.O n N (N, fs, e)).2))).map
        (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
      (Giant.g1Model X.O n (N, gs, d) (setOps (N - n)) (m5Cs X.O n N (N, fs, e)).2) ≤
        β.Bg1₂ₐ)
    (hBgen₂ₐ : ∀ gs' : GensData, GensData.AllValid N gs' → gs'.length ≤ sIn + 1 →
      GensData.denote N gs' ≤ GensData.denote N gs →
      X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.Bgen₂ₐ)
    (hBpb : ∀ gs', GensData.AllValid N gs' →
      gs'.length ≤ (sIn + 1) * (sIn + 1) + sIn + sIn → GensData.denote N gs' ≤ G₀ →
      X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.Bpb)
    (hBgm : ∀ (w' : WinData) (σ' : PermData) (gs' : GensData) (d' : D.denote),
      Giant.PbSubP DV G₀ xy w.1.length sIn (xy, w', σ', N, gs', d') →
      X.B.call GroupOp.generate (w'.1.length, GensData.restrictTo (WinData.pos N w') w'.1 gs')
        (X.O.run GroupOp.generate
          (w'.1.length, GensData.restrictTo (WinData.pos N w') w'.1 gs')) ≤ β.Bgm)
    (hBlift : ∀ (w' : WinData) (σ' : PermData) (gs' : GensData) (d' : D.denote),
      Giant.PbSubP DV G₀ xy w.1.length sIn (xy, w', σ', N, gs', d') → ∀ π' : PermData,
      X.B.call GroupOp.lift ((N, gs', d'), (w', π'))
        (X.O.run GroupOp.lift ((N, gs', d'), (w', π'))) ≤ β.Blift)
    (hBker : ∀ (w' : WinData) (σ' : PermData) (gs' : GensData) (d' : D.denote),
      Giant.PbSubP DV G₀ xy w.1.length sIn (xy, w', σ', N, gs', d') →
      X.B.call GroupOp.kernel ((N, gs', d'), w') (X.O.run GroupOp.kernel ((N, gs', d'), w')) ≤
        β.Bker)
    (hsK : ∀ (w' : WinData) (σ' : PermData) (gs' : GensData) (d' : D.denote),
      Giant.PbSubP DV G₀ xy w.1.length sIn (xy, w', σ', N, gs', d') →
      (X.O.run GroupOp.kernel ((N, gs', d'), w')).2.1.length ≤ β.sK)
    (hBgn : ∀ hs : GensData, GensData.AllValid N hs → hs.length ≤ β.sK + s →
      GensData.denote N hs ≤ G₀ →
      X.B.call GroupOp.generate (N, hs) (X.O.run GroupOp.generate (N, hs)) ≤ β.Bgn)
    -- Case 2b
    (hBg1₂ᵦ : ∀ (hC : CertSetting (GensData.denote N gs) n)
      (φ : strGroup hC →* Perm (Fin (N - n))), IsPhi hC φ →
      ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e →
      (m5Cs X.O n N (N, fs, e)).1 = 2 → m5IsA X.O n N (N, fs, e) = false → ∀ X₀ : SoJTree.OutD,
      m5Leaf2b X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 = some X₀ → X₀.1 ≠ 2 →
      X.B.call GroupOp.generate
        (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (Case2b.outGensD (N - n) X₀))).map
          (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
        (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (Case2b.outGensD (N - n) X₀)))) ≤ β.Bg1₂ᵦ)
    (hBgen₂ᵦ : ∀ (hC : CertSetting (GensData.denote N gs) n)
      (φ : strGroup hC →* Perm (Fin (N - n))), IsPhi hC φ →
      ∀ fs e, M5Full DV hC φ k sIn xy.2 fs e → ∀ gs' : GensData,
      GensData.AllValid N gs' →
      gs'.length ≤ Case2b.c2bR N n (m5Cs X.O n N (N, fs, e)).2.length
        (Case2b.degD X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 - 1)
        (Case2b.sojZ (N - n)) * (sIn + 1) →
      GensData.denote N gs' ≤ GensData.denote N gs →
      X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.Bgen₂ᵦ)
    (hD₂ᵦ : ∀ (hC : CertSetting (GensData.denote N gs) n)
      (φ : strGroup hC →* Perm (Fin (N - n))), IsPhi hC φ →
      ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e → ∀ X₀,
      m5Leaf2b X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 = some X₀ →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (Case2b.outOps (N - n)) X₀).2.1 sIn gs' d' O' →
      RDOrbit X body DV n N w L st sIn Bd gs' d' O')
    -- Case 3
    (hBg1₃ : ∀ (hC : CertSetting (GensData.denote N gs) n)
      (φ : strGroup hC →* Perm (Fin (N - n))), IsPhi hC φ →
      ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e →
      (m5Cs X.O n N (N, fs, e)).1 ≠ 1 → (m5Cs X.O n N (N, fs, e)).1 ≠ 2 → ∀ X₀ : SoJTree.OutD,
      Case3.C3First φ (strOn hC.le (xy.1.denote N)) (N - n) k
        (fixPtsD (m5Os X.O n N (N, fs, e))) X₀ → X₀.1 ≠ 2 →
      X.B.call GroupOp.generate
        (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (Case2b.outGensD (N - n) X₀))).map
          (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
        (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (Case2b.outGensD (N - n) X₀)))) ≤ β.Bg1₃)
    (hBgen₃ : ∀ (hC : CertSetting (GensData.denote N gs) n)
      (φ : strGroup hC →* Perm (Fin (N - n))), IsPhi hC φ →
      ∀ fs e, M5Full DV hC φ k sIn xy.2 fs e → ∀ gs' : GensData,
      GensData.AllValid N gs' →
      gs'.length ≤ Case3.c3R k (fixPtsD (m5Os X.O n N (N, fs, e))).length
        (Case2b.sojZ (N - n)) * (sIn + 1) →
      GensData.denote N gs' ≤ GensData.denote N gs →
      X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.Bgen₃)
    (hD₃ : ∀ (hC : CertSetting (GensData.denote N gs) n)
      (φ : strGroup hC →* Perm (Fin (N - n))), IsPhi hC φ →
      ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e → ∀ X₀,
      Case3.C3First φ (strOn hC.le (xy.1.denote N)) (N - n) k
        (fixPtsD (m5Os X.O n N (N, fs, e))) X₀ →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (Case2b.outOps (N - n)) X₀).2.1 sIn gs' d' O' →
      RDOrbit X body DV n N w L st sIn Bd gs' d' O')
        -- the coloured Johnson routes
    {uB Bg1J₂ Bg1J₃ : ℕ} (hLgJ : max (NP - nP) uB.factorial * (sIn + 1) ≤ Lg)
    (hBg1J₂ : ∀ (hC : CertSetting (GensData.denote N gs) n)
      (φ : strGroup hC →* Perm (Fin (N - n))), IsPhi hC φ →
      ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e →
      (m5Cs X.O n N (N, fs, e)).1 = 2 → m5IsA X.O n N (N, fs, e) = false →
      ∀ X₀ : SoJTree.OutD,
      m5Leaf2b X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 = some X₀ → X₀.1 = 2 →
      CJFacts (N - n) (cjFirst2bD N n (m5Cs X.O n N (N, fs, e)).2
          (Case2b.degD X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 - 1) X₀) →
      X.B.call GroupOp.generate
        (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (cjohnGensD (N - n) (cjFirst2bD N n (m5Cs X.O n N (N, fs, e)).2
            (Case2b.degD X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 - 1) X₀)))).map
          (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
        (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (cjohnGensD (N - n) (cjFirst2bD N n (m5Cs X.O n N (N, fs, e)).2
            (Case2b.degD X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 - 1) X₀))))) ≤
        Bg1J₂)
    (hLY₂ : ∀ (hC : CertSetting (GensData.denote N gs) n)
      (φ : strGroup hC →* Perm (Fin (N - n))), IsPhi hC φ →
      ∀ fs e, M5Full DV hC φ k sIn xy.2 fs e →
      Case2b.c2bR N n (m5Cs X.O n N (N, fs, e)).2.length
      (Case2b.degD X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 - 1)
      (Case2b.sojZ (N - n)) * (sIn + 1) ≤ Lg)
    (hDJ₂ : ∀ (hC : CertSetting (GensData.denote N gs) n)
      (φ : strGroup hC →* Perm (Fin (N - n))), IsPhi hC φ →
      ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e →
      (m5Cs X.O n N (N, fs, e)).1 = 2 → m5IsA X.O n N (N, fs, e) = false →
      ∀ X₀, m5Leaf2b X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 = some X₀ → X₀.1 = 2 →
      CJFacts (N - n) (cjFirst2bD N n (m5Cs X.O n N (N, fs, e)).2
          (Case2b.degD X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 - 1) X₀) →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (cjohnOps (N - n))
          (cjFirst2bD N n (m5Cs X.O n N (N, fs, e)).2
            (Case2b.degD X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 - 1) X₀)).2.1 sIn
          gs' d' O' →
      RDOrbit X body DV n N w L (2, cjFirst2bD N n (m5Cs X.O n N (N, fs, e)).2
        (Case2b.degD X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 - 1) X₀) sIn Bd gs' d' O')
    (hu₂ : ∀ (hC : CertSetting (GensData.denote N gs) n)
      (φ : strGroup hC →* Perm (Fin (N - n))), IsPhi hC φ →
      ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e →
      (m5Cs X.O n N (N, fs, e)).1 = 2 → m5IsA X.O n N (N, fs, e) = false →
      ∀ X₀, m5Leaf2b X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 = some X₀ → X₀.1 = 2 →
      CJFacts (N - n) (cjFirst2bD N n (m5Cs X.O n N (N, fs, e)).2
          (Case2b.degD X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 - 1) X₀) →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (cjohnOps (N - n))
          (cjFirst2bD N n (m5Cs X.O n N (N, fs, e)).2
            (Case2b.degD X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 - 1) X₀)).2.1 sIn
          gs' d' O' →
      ((labJUD X₀.2.2.2.1.length (markArr (N - n) X₀.2.2.1) X₀.2.2.2.2.2 L O').getD
        (O'.headD 0) []).length ≤ uB)
    (hBg1J₃ : ∀ (hC : CertSetting (GensData.denote N gs) n)
      (φ : strGroup hC →* Perm (Fin (N - n))), IsPhi hC φ →
      ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e →
      (m5Cs X.O n N (N, fs, e)).1 ≠ 1 → (m5Cs X.O n N (N, fs, e)).1 ≠ 2 →
      ∀ cXX X₀, Case3.ColChar φ (strOn hC.le (xy.1.denote N))
        (strOn hC.le (xy.1.denote N)) k (fixPtsD (m5Os X.O n N (N, fs, e))).length
        (fixPtsD (m5Os X.O n N (N, fs, e))) (fixPtsD (m5Os X.O n N (N, fs, e))) cXX →
      Case3.firstStructD (N - n) k (fixPtsD (m5Os X.O n N (N, fs, e)))
        (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fs, e))).length) = some X₀ → X₀.1 = 2 →
      CJFacts (N - n) (cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fs, e)))
          (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fs, e))).length) X₀) →
      X.B.call GroupOp.generate
        (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (cjohnGensD (N - n) (cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fs, e)))
            (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fs, e))).length) X₀)))).map
          (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
        (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (cjohnGensD (N - n) (cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fs, e)))
            (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fs, e))).length) X₀))))) ≤ Bg1J₃)
    (hLY₃ : ∀ (hC : CertSetting (GensData.denote N gs) n)
      (φ : strGroup hC →* Perm (Fin (N - n))), IsPhi hC φ →
      ∀ fs e, M5Full DV hC φ k sIn xy.2 fs e →
      Case3.c3R k (fixPtsD (m5Os X.O n N (N, fs, e))).length (Case2b.sojZ (N - n)) *
      (sIn + 1) ≤ Lg)
    (hDJ₃ : ∀ (hC : CertSetting (GensData.denote N gs) n)
      (φ : strGroup hC →* Perm (Fin (N - n))), IsPhi hC φ →
      ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e →
      (m5Cs X.O n N (N, fs, e)).1 ≠ 1 → (m5Cs X.O n N (N, fs, e)).1 ≠ 2 →
      ∀ cXX X₀, Case3.ColChar φ (strOn hC.le (xy.1.denote N))
        (strOn hC.le (xy.1.denote N)) k (fixPtsD (m5Os X.O n N (N, fs, e))).length
        (fixPtsD (m5Os X.O n N (N, fs, e))) (fixPtsD (m5Os X.O n N (N, fs, e))) cXX →
      Case3.firstStructD (N - n) k (fixPtsD (m5Os X.O n N (N, fs, e)))
        (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fs, e))).length) = some X₀ → X₀.1 = 2 →
      CJFacts (N - n) (cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fs, e)))
          (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fs, e))).length) X₀) →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (cjohnOps (N - n))
          (cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fs, e)))
            (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fs, e))).length) X₀)).2.1 sIn
          gs' d' O' →
      RDOrbit X body DV n N w L (2, cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fs, e)))
        (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fs, e))).length) X₀) sIn Bd gs' d' O')
    (hu₃ : ∀ (hC : CertSetting (GensData.denote N gs) n)
      (φ : strGroup hC →* Perm (Fin (N - n))), IsPhi hC φ →
      ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e →
      (m5Cs X.O n N (N, fs, e)).1 ≠ 1 → (m5Cs X.O n N (N, fs, e)).1 ≠ 2 →
      ∀ cXX X₀, Case3.ColChar φ (strOn hC.le (xy.1.denote N))
        (strOn hC.le (xy.1.denote N)) k (fixPtsD (m5Os X.O n N (N, fs, e))).length
        (fixPtsD (m5Os X.O n N (N, fs, e))) (fixPtsD (m5Os X.O n N (N, fs, e))) cXX →
      Case3.firstStructD (N - n) k (fixPtsD (m5Os X.O n N (N, fs, e)))
        (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fs, e))).length) = some X₀ → X₀.1 = 2 →
      CJFacts (N - n) (cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fs, e)))
          (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fs, e))).length) X₀) →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (cjohnOps (N - n))
          (cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fs, e)))
            (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fs, e))).length) X₀)).2.1 sIn
          gs' d' O' →
      ((labJUD X₀.2.2.2.1.length (markArr (N - n) X₀.2.2.1) X₀.2.2.2.2.2 L O').getD
        (O'.headD 0) []).length ≤ uB)
    -- the restriction's charges
    {sKR BgmR BliftR BkerR BgnR : ℕ}
    (hBgmR : X.B.call GroupOp.generate ((rbPts nP NP wP).length, rbGens nP NP wP gsP)
      (X.O.run GroupOp.generate ((rbPts nP NP wP).length, rbGens nP NP wP gsP)) ≤ BgmR)
    (hBliftR : ∀ π' : PermData, X.B.call GroupOp.lift ((NP, gsP, dP), (rbU nP NP wP, π'))
      (X.O.run GroupOp.lift ((NP, gsP, dP), (rbU nP NP wP, π'))) ≤ BliftR)
    (hBkerR : X.B.call GroupOp.kernel ((NP, gsP, dP), rbU nP NP wP)
      (X.O.run GroupOp.kernel ((NP, gsP, dP), rbU nP NP wP)) ≤ BkerR)
    (hsKR : (X.O.run GroupOp.kernel ((NP, gsP, dP), rbU nP NP wP)).2.1.length ≤ sKR)
    (hBgnR : ∀ hs : GensData, GensData.AllValid NP hs → hs.length ≤ sKR + sIn →
      GensData.denote NP hs ≤ GensData.denote NP gsP →
      X.B.call GroupOp.generate (NP, hs) (X.O.run GroupOp.generate (NP, hs)) ≤ BgnR) :
    ∃ (fxs fys : GensData) (ex ey : D.denote) (ans : AnswerData D) (ch : List (ℕ × Option ℕ)),
      (∃ (hC : CertSetting (GensData.denote N gs) n) (φ : strGroup hC →* Perm (Fin (N - n))),
        IsPhi hC φ ∧ M5Full DV hC φ k sIn xy.1 fxs ex ∧ M5Full DV hC φ k sIn xy.2 fys ey) ∧
      RunsWithin X body (Main.m5StepCJProg sub
          (((xyP, (wP, (σP, (NP, gsP, dP)))), (n₀, (nP, some LP))) : HInstData D) LP k st) ans
        (rbCost NP wP.1.length (NP - nP) gsP.length
          ((ch.map fun x => C x.1 x.2).sum + 2 * certCount N n k * C (n / k) none +
            m5CKCJ X.O n N k (N, fxs, ex) (N, fys, ey) * C (n / k) none +
            m5CH X.O n N sIn w.1.length (N, fxs, ex) (N, fys, ey) * C (w.1.length / 2) none +
            m5CoreWorkCJ X.O n N k s sIn Bgen Blift Bo Bk Bcr Bd (N, gs, d) (N, fxs, ex)
              (N, fys, ey) w.1.length β B.Bstab B.Btr B.Borb Bk'.Bgen Bk'.Borb Bk'.Bstab
              (fun M => (Bm M).Borb) (fun M => (Bm M).Bstab) (fun M => (Bm M).Btr)
              uB Bg1J₂ Bg1J₃)
          sIn sKR BgmR BliftR BkerR BgnR) ∧
      AnsOK DV NP (wP.denote NP) (PermData.denote NP σP) (GensData.denote NP gsP)
        (xyP.1.denote NP) (xyP.2.denote NP) ans ∧
      (∀ sGen, (∀ hs, GensData.AllValid NP hs →
          GensData.denote NP hs ≤ GensData.denote NP gsP →
          (X.O.run GroupOp.generate (NP, hs)).2.1.length ≤ sGen) →
        ∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sGen) ∧
      ChildList wP.1.length (m5CFCJ X.O n N k (N, fxs, ex) (N, fys, ey) uB)
        (StepChild wP.1.length (NP - nP)) ch := by
  subst hxy hw hn hL
  -- the parent's facts
  obtain ⟨⟨hwP, hσP, hgvP, hWP⟩, hleP, hBP', hwinP, -, -⟩ := id hIP
  change WinData.Valid NP wP at hwP
  change GroupValid DV NP gsP dP at hgvP
  change IsInvariant (GensData.denote NP gsP) (wP.denote NP) at hWP
  change nP ≤ NP at hleP
  change IsInvariant (GensData.denote NP gsP) (baseSet nP NP) at hBP'
  change ∀ i ∈ wP.1, i < nP at hwinP
  have hwlen : wP.1.length ≤ nP := mf_length_le_of_nodup hwP.nodup hwinP
  have hlen : (rbPts nP NP wP).length = wP.1.length + (NP - nP) := rb_length
  -- the restricted group
  have hOg : MeetsContractOn DV (· = .generate) X.O := fun op x h hx =>
    hO op x (by subst h; exact Or.inr (Or.inr (Or.inl (Or.inl rfl)))) hx
  have hOr : MeetsContractOn DV restrictOps X.O := fun op x h hx =>
    hO op x (Or.inr (Or.inr (Or.inl h))) hx
  have hPr : ∀ op x, restrictOps op → GroupPre DV op x → X.Pre op x := fun op x h hx =>
    hPre op x (Or.inr (Or.inr (Or.inl h))) hx
  have hUv := rb_valid (n := nP) hwP hwinP
  have hU := rb_inv (n := nP) hWP hBP'
  have hg'v := GensData.allValid_restrictTo hU hUv hgvP.1
  have hg'den := GensData.denote_restrictTo hU hUv hgvP.1
  have hpost := hOg .generate ((rbPts nP NP wP).length, rbGens nP NP wP gsP) rfl hg'v
  rw [hG'] at hpost
  obtain ⟨hNeq, hgv, hden0⟩ := hpost
  subst hNeq
  have hden : GensData.denote (rbU nP NP wP).1.length gs =
      (restrictHom hU (WinData.reindex hUv)).range := hden0.trans hg'den
  have hm : (rbPts nP NP wP).length - wP.1.length = NP - nP := by omega
  -- the restricted instance
  have hIeq : rbHInst X.O xyP wP σP NP gsP n₀ nP LP =
      ((((StrData.restrictTo (rbPts nP NP wP) xyP.1,
          StrData.restrictComp (rbPts nP NP wP) xyP.2 σP),
        (WinData.ofPoints (rbPts nP NP wP).length (List.range wP.1.length),
          (PermData.one (rbPts nP NP wP).length, ((rbPts nP NP wP).length, gs, d)))),
        (n₀, (wP.1.length, some (rbLabels wP LP)))) : HInstData D) := by
    simp only [rbHInst]
    rw [hG']
  have hI' := rbHInst_valid (hB := hBP) hOg hIP haltP (by omega)
  rw [hIeq] at hI'
  have hC : CertSetting (GensData.denote (rbPts nP NP wP).length gs) wP.1.length :=
    ⟨hI'.le, hI'.base_inv, hI'.faithful⟩
  obtain ⟨φ, hφ⟩ := exists_phi hC
  have halt' : alternatingGroup (Fin ((rbPts nP NP wP).length - wP.1.length)) ≤
      (baseHom _ wP.1.length hC.base).range :=
    m5s_giant hUv hU hwinP hBP' haltP hden hC.base
  have hwS : ∀ u : Fin (rbPts nP NP wP).length, u.val < wP.1.length →
      u ∈ (WinData.ofPoints (rbPts nP NP wP).length (List.range wP.1.length)).denote
        (rbPts nP NP wP).length := fun u hu => List.mem_range.2 hu
  -- the sub-solver of the restricted instance
  have e1 : (WinData.ofPoints (rbPts nP NP wP).length
      (List.range wP.1.length)).1.length = wP.1.length := List.length_range
  have hsubR := hsubP.mono (Q := fun J => SizeChild (max sIn (supTo sm
      ((WinData.ofPoints (rbPts nP NP wP).length (List.range wP.1.length)).1.length / 2)))
      ((((StrData.restrictTo (rbPts nP NP wP) xyP.1, StrData.restrictComp (rbPts nP NP wP)
        xyP.2 σP),
        (WinData.ofPoints (rbPts nP NP wP).length (List.range wP.1.length),
          (PermData.one (rbPts nP NP wP).length, ((rbPts nP NP wP).length, gs, d)))),
        (n₀, (wP.1.length, some (rbLabels wP LP)))) : HInstData D) J ∧
      StepChild (WinData.ofPoints (rbPts nP NP wP).length (List.range wP.1.length)).1.length
        ((rbPts nP NP wP).length - wP.1.length) (J.winSize, J.baseOpt)) (by
    rintro J ⟨hS, hSt⟩
    refine ⟨⟨hS.n₀, le_trans hS.n_le hwlen, ?_, by have := hS.gens_le; rwa [e1] at this,
      fun hIL => hS.lab ⟨le_trans hwlen hIL.n_le, fun L' hL' => by
        obtain rfl := Option.some.inj hL'
        change LabInvAt n₀ ((rbPts nP NP wP).length - wP.1.length) (labLen (rbLabels wP LP))
        rw [hm]
        exact (hIL.hint LP rfl).mono le_rfl (labLen_rbLabels_le wP LP)⟩⟩, ?_⟩
    · have := hS.degree_le
      change J.inst.degree ≤ max (rbPts nP NP wP).length (2 * wP.1.length) at this
      change J.inst.degree ≤ max NP (2 * nP)
      omega
    · rw [e1, hm] at hSt
      exact hSt)
  -- M5 on the restricted instance
  obtain ⟨fxs, fys, ex, ey, ans', ch, hFx, hFy, hrun', hok', hg', hch⟩ :=
    RunsWithin.m5CoreCJProg_jp (X := X) (body := body) (sub := sub) (hC := hC) hO hPre hI' hφ halt'
      hwS h5 (by omega) (by omega) (by omega) B hgs hGG₀ Bk' hsk Bm hsubR hCmono hs hB
      (by rw [hm]; exact hLg) hst β hBgP hBmem hBkA hBlA hBg hBgk hBgs hBF hBk3 hBo3 hBcr3 hB3
      (hBox hC φ hφ) (hBoy hC φ hφ) (hBg1₁ hC φ hφ) (hD₁ hC φ hφ) (hBg1₂ₐ hC φ hφ) hBgen₂ₐ
      hBpb hBgm hBlift hBker hsK hBgn (hBg1₂ᵦ hC φ hφ) (hBgen₂ᵦ hC φ hφ) (hD₂ᵦ hC φ hφ)
      (hBg1₃ hC φ hφ) (hBgen₃ hC φ hφ) (hD₃ hC φ hφ) (by rw [hm]; exact hLgJ)
      (hBg1J₂ hC φ hφ) (hLY₂ hC φ hφ) (hDJ₂ hC φ hφ) (hu₂ hC φ hφ) (hBg1J₃ hC φ hφ)
      (hLY₃ hC φ hφ) (hDJ₃ hC φ hφ) (hu₃ hC φ hφ)
  -- the restriction around it
  obtain ⟨ans, hrun, hok, hgen⟩ := RunsWithin.restrictBaseProg (X := X) (body := body)
    (cont := fun I => Main.m5CoreCJProg sub I k st) hOr hPr hIP (s' := sIn)
    ⟨ans', by rw [hIeq]; exact hrun', by rw [hIeq]; exact hok', hg'⟩
    hBgmR hBliftR hBkerR hsKR hBgnR
  refine ⟨fxs, fys, ex, ey, ans, ch, ⟨hC, φ, hφ, hFx, hFy⟩, hrun, hok, hgen, ?_⟩
  rw [e1, hm] at hch
  exact hch

/-- `RunsWithin.m5StepCJProg_jp` with Case 2b's Johnson-route hypotheses stated for every first
leaf. -/
theorem RunsWithin.m5StepCJProg (hO : MeetsContractOn DV m5Ops X.O)
    (hPre : ∀ op x, m5Ops op → GroupPre DV op x → X.Pre op x)
    -- the parent
    (hIP : HInstValid DV
      (((xyP, (wP, (σP, (NP, gsP, dP)))), (n₀, (nP, some LP))) : HInstData D))
    {hBP : IsInvariant (GensData.denote NP gsP) (baseSet nP NP)}
    (haltP : alternatingGroup (Fin (NP - nP)) ≤ (baseHom (GensData.denote NP gsP) nP hBP).range)
    {sm : ℕ → ℕ}
    (hsubP : HSubSolves X body DV sub
      (fun J => SizeChild (max sIn (supTo sm (wP.1.length / 2)))
        (((xyP, (wP, (σP, (NP, gsP, dP)))), (n₀, (nP, some LP))) : HInstData D) J ∧
        StepChild wP.1.length (NP - nP) (J.winSize, J.baseOpt)) C s)
    -- the restricted instance
    (hG' : X.O.run GroupOp.generate ((rbPts nP NP wP).length, rbGens nP NP wP gsP) =
      (N, gs, d))
    (hxy : xy = (StrData.restrictTo (rbPts nP NP wP) xyP.1,
      StrData.restrictComp (rbPts nP NP wP) xyP.2 σP))
    (hw : w = WinData.ofPoints N (List.range wP.1.length)) (hn : n = wP.1.length)
    (hL : L = rbLabels wP LP)
    -- the certificates, the backends and the numbers
    {k : ℕ} (h5 : 5 ≤ k) (hk : k + 2 ≤ NP - nP) (h2k : 2 * k ≤ NP - nP)
    (hm12 : 12 ≤ NP - nP)
    {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N sIn G₀) (hgs : gs.length ≤ sIn)
    (hGG₀ : GensData.denote N gs ≤ G₀) {sk : ℕ} (Bk' : BackendBounds X DV k sk ⊤)
    (hsk : sIn ≤ k * (sk + 1)) (Bm : ∀ M, BackendBounds X DV M (sm M) ⊤)
    (hCmono : ∀ a b, a ≤ b → C a none ≤ C b none) (hs : s ≤ sIn)
    (hB : RDBounds X DV n N sIn Lg Blift Bgen Bo Bk Bcr)
    (hLg : (NP - nP).factorial * (sIn + 1) ≤ Lg) (hst : st.1 ≠ 2) (β : M5Bounds)
    -- M5's charges on the restricted instance
    (hBgP : X.B.call GroupOp.generate (N - n, gs.map (baseD n N))
      (X.O.run GroupOp.generate (N - n, gs.map (baseD n N))) ≤ β.BgP)
    (hBmem : ∀ g : PermData, g.Valid (N - n) → X.B.call GroupOp.mem (pModel X.O n (N, gs, d), g)
      (X.O.run GroupOp.mem (pModel X.O n (N, gs, d), g)) ≤ β.Bmem)
    (hBkA : X.B.call GroupOp.kernel ((N, gs, d), baseWin n N) (kerModel X.O n (N, gs, d)) ≤
      β.BkA)
    (hBlA : ∀ π : PermData, X.B.call GroupOp.lift ((N, gs, d), (baseWin n N, π))
      (liftModel X.O n (N, gs, d) π) ≤ β.BlA)
    (hBg : ∀ M ≤ N - n, ∀ gs' : GensData, GensData.AllValid M gs' → gs'.length ≤ sIn →
      X.B.call GroupOp.generate (M, gs') (X.O.run GroupOp.generate (M, gs')) ≤ β.Bg)
    (hBgk : ∀ gs' : GensData, GensData.AllValid N gs' →
      gs'.length ≤ k.factorial * (sIn + 1) → GensData.denote N gs' ≤ GensData.denote N gs →
        X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.Bgk)
    (hBgs : ∀ al : List ℕ, al.Nodup → al.length = k → (∀ a ∈ al, a < N - n) → ∀ b₁ b₂,
      X.B.call GroupOp.generate (N, giantGens X.O n (N, gs, d) al b₁ b₂)
        (giantSetStabModel X.O n (N, gs, d) al b₁ b₂) ≤ β.Bgs)
    (hBF : ∀ gs' : GensData, GensData.AllValid N gs' → gs'.length ≤ 2 * sIn →
      GensData.denote N gs' ≤ GensData.denote N gs →
        X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.BF)
    (hBk3 : X.B.call GroupOp.kernel ((N, gs, d), baseWin n N) (kerModel X.O n (N, gs, d)) ≤
      β.Bk3)
    (hBo3 : X.B.call GroupOp.orbits (kerModel X.O n (N, gs, d), w)
      (krOrbits X.O n (N, gs, d) w) ≤ β.Bo3)
    (hBcr3 : X.B.call GroupOp.cosetReps ((N, gs, d), kerModel X.O n (N, gs, d))
      (kerReps X.O n (N, gs, d)) ≤ β.Bcr3)
    (hB3 : ∀ hs : GensData, GensData.AllValid N hs →
      hs.length ≤ (kerReps X.O n (N, gs, d)).length *
        (max s (kerModel X.O n (N, gs, d)).2.1.length + 1) →
      GensData.denote N hs ≤ GensData.denote N gs →
      X.B.call GroupOp.generate (N, hs) (X.O.run GroupOp.generate (N, hs)) ≤ β.Bgen3)
    -- Case 1
    (hBox : ∀ (hC : CertSetting (GensData.denote N gs) n)
      (φ : strGroup hC →* Perm (Fin (N - n))), IsPhi hC φ →
      ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e →
      X.B.call GroupOp.orbits ((N, fs, e), baseWin n N)
        (Giant.baseOrbits X.O n N (N, fs, e)) ≤ β.Box)
    (hBoy : ∀ (hC : CertSetting (GensData.denote N gs) n)
      (φ : strGroup hC →* Perm (Fin (N - n))), IsPhi hC φ →
      ∀ fs e, M5Full DV hC φ k sIn xy.2 fs e →
      X.B.call GroupOp.orbits ((N, fs, e), baseWin n N)
        (Giant.baseOrbits X.O n N (N, fs, e)) ≤ β.Boy)
    (hBg1₁ : ∀ (hC : CertSetting (GensData.denote N gs) n)
      (φ : strGroup hC →* Perm (Fin (N - n))), IsPhi hC φ →
      ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e → X.B.call GroupOp.generate
      (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
        (partGensD (N - n) (Giant.orbitPartModel X.O n N (N, fs, e))))).map
        (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
      (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
        (partGensD (N - n) (Giant.orbitPartModel X.O n N (N, fs, e)))))) ≤ β.Bg1₁)
    (hD₁ : ∀ (hC : CertSetting (GensData.denote N gs) n)
      (φ : strGroup hC →* Perm (Fin (N - n))), IsPhi hC φ →
      ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e →
      ∀ gs' d' O', RDSet DV n N gs w L (Giant.g1Model X.O n (N, gs, d) (partOps (N - n))
        (Giant.orbitPartModel X.O n N (N, fs, e))).2.1 sIn gs' d' O' →
      RDOrbit X body DV n N w L st sIn Bd gs' d' O')
    -- Case 2a
    (hBg1₂ₐ : ∀ (hC : CertSetting (GensData.denote N gs) n)
      (φ : strGroup hC →* Perm (Fin (N - n))), IsPhi hC φ →
      ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e → X.B.call GroupOp.generate
      (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
        ((setOps (N - n)).gens (m5Cs X.O n N (N, fs, e)).2))).map
        (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
      (Giant.g1Model X.O n (N, gs, d) (setOps (N - n)) (m5Cs X.O n N (N, fs, e)).2) ≤
        β.Bg1₂ₐ)
    (hBgen₂ₐ : ∀ gs' : GensData, GensData.AllValid N gs' → gs'.length ≤ sIn + 1 →
      GensData.denote N gs' ≤ GensData.denote N gs →
      X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.Bgen₂ₐ)
    (hBpb : ∀ gs', GensData.AllValid N gs' →
      gs'.length ≤ (sIn + 1) * (sIn + 1) + sIn + sIn → GensData.denote N gs' ≤ G₀ →
      X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.Bpb)
    (hBgm : ∀ (w' : WinData) (σ' : PermData) (gs' : GensData) (d' : D.denote),
      Giant.PbSubP DV G₀ xy w.1.length sIn (xy, w', σ', N, gs', d') →
      X.B.call GroupOp.generate (w'.1.length, GensData.restrictTo (WinData.pos N w') w'.1 gs')
        (X.O.run GroupOp.generate
          (w'.1.length, GensData.restrictTo (WinData.pos N w') w'.1 gs')) ≤ β.Bgm)
    (hBlift : ∀ (w' : WinData) (σ' : PermData) (gs' : GensData) (d' : D.denote),
      Giant.PbSubP DV G₀ xy w.1.length sIn (xy, w', σ', N, gs', d') → ∀ π' : PermData,
      X.B.call GroupOp.lift ((N, gs', d'), (w', π'))
        (X.O.run GroupOp.lift ((N, gs', d'), (w', π'))) ≤ β.Blift)
    (hBker : ∀ (w' : WinData) (σ' : PermData) (gs' : GensData) (d' : D.denote),
      Giant.PbSubP DV G₀ xy w.1.length sIn (xy, w', σ', N, gs', d') →
      X.B.call GroupOp.kernel ((N, gs', d'), w') (X.O.run GroupOp.kernel ((N, gs', d'), w')) ≤
        β.Bker)
    (hsK : ∀ (w' : WinData) (σ' : PermData) (gs' : GensData) (d' : D.denote),
      Giant.PbSubP DV G₀ xy w.1.length sIn (xy, w', σ', N, gs', d') →
      (X.O.run GroupOp.kernel ((N, gs', d'), w')).2.1.length ≤ β.sK)
    (hBgn : ∀ hs : GensData, GensData.AllValid N hs → hs.length ≤ β.sK + s →
      GensData.denote N hs ≤ G₀ →
      X.B.call GroupOp.generate (N, hs) (X.O.run GroupOp.generate (N, hs)) ≤ β.Bgn)
    -- Case 2b
    (hBg1₂ᵦ : ∀ (hC : CertSetting (GensData.denote N gs) n)
      (φ : strGroup hC →* Perm (Fin (N - n))), IsPhi hC φ →
      ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e → ∀ X₀ : SoJTree.OutD,
      m5Leaf2b X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 = some X₀ →
      X.B.call GroupOp.generate
        (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (Case2b.outGensD (N - n) X₀))).map
          (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
        (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (Case2b.outGensD (N - n) X₀)))) ≤ β.Bg1₂ᵦ)
    (hBgen₂ᵦ : ∀ (hC : CertSetting (GensData.denote N gs) n)
      (φ : strGroup hC →* Perm (Fin (N - n))), IsPhi hC φ →
      ∀ fs e, M5Full DV hC φ k sIn xy.2 fs e → ∀ gs' : GensData,
      GensData.AllValid N gs' →
      gs'.length ≤ Case2b.c2bR N n (m5Cs X.O n N (N, fs, e)).2.length
        (Case2b.degD X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 - 1)
        (Case2b.sojZ (N - n)) * (sIn + 1) →
      GensData.denote N gs' ≤ GensData.denote N gs →
      X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.Bgen₂ᵦ)
    (hD₂ᵦ : ∀ (hC : CertSetting (GensData.denote N gs) n)
      (φ : strGroup hC →* Perm (Fin (N - n))), IsPhi hC φ →
      ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e → ∀ X₀,
      m5Leaf2b X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 = some X₀ →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (Case2b.outOps (N - n)) X₀).2.1 sIn gs' d' O' →
      RDOrbit X body DV n N w L st sIn Bd gs' d' O')
    -- Case 3
    (hBg1₃ : ∀ (hC : CertSetting (GensData.denote N gs) n)
      (φ : strGroup hC →* Perm (Fin (N - n))), IsPhi hC φ →
      ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e → ∀ X₀ : SoJTree.OutD,
      Case3.C3First φ (strOn hC.le (xy.1.denote N)) (N - n) k
        (fixPtsD (m5Os X.O n N (N, fs, e))) X₀ →
      X.B.call GroupOp.generate
        (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (Case2b.outGensD (N - n) X₀))).map
          (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
        (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (Case2b.outGensD (N - n) X₀)))) ≤ β.Bg1₃)
    (hBgen₃ : ∀ (hC : CertSetting (GensData.denote N gs) n)
      (φ : strGroup hC →* Perm (Fin (N - n))), IsPhi hC φ →
      ∀ fs e, M5Full DV hC φ k sIn xy.2 fs e → ∀ gs' : GensData,
      GensData.AllValid N gs' →
      gs'.length ≤ Case3.c3R k (fixPtsD (m5Os X.O n N (N, fs, e))).length
        (Case2b.sojZ (N - n)) * (sIn + 1) →
      GensData.denote N gs' ≤ GensData.denote N gs →
      X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.Bgen₃)
    (hD₃ : ∀ (hC : CertSetting (GensData.denote N gs) n)
      (φ : strGroup hC →* Perm (Fin (N - n))), IsPhi hC φ →
      ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e → ∀ X₀,
      Case3.C3First φ (strOn hC.le (xy.1.denote N)) (N - n) k
        (fixPtsD (m5Os X.O n N (N, fs, e))) X₀ →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (Case2b.outOps (N - n)) X₀).2.1 sIn gs' d' O' →
      RDOrbit X body DV n N w L st sIn Bd gs' d' O')
        -- the coloured Johnson routes
    {uB Bg1J₂ Bg1J₃ : ℕ} (hLgJ : max (NP - nP) uB.factorial * (sIn + 1) ≤ Lg)
    (hBg1J₂ : ∀ (hC : CertSetting (GensData.denote N gs) n)
      (φ : strGroup hC →* Perm (Fin (N - n))), IsPhi hC φ →
      ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e →
      ∀ X₀ : SoJTree.OutD,
      m5Leaf2b X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 = some X₀ →
      X.B.call GroupOp.generate
        (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (cjohnGensD (N - n) (cjFirst2bD N n (m5Cs X.O n N (N, fs, e)).2
            (Case2b.degD X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 - 1) X₀)))).map
          (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
        (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (cjohnGensD (N - n) (cjFirst2bD N n (m5Cs X.O n N (N, fs, e)).2
            (Case2b.degD X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 - 1) X₀))))) ≤
        Bg1J₂)
    (hLY₂ : ∀ (hC : CertSetting (GensData.denote N gs) n)
      (φ : strGroup hC →* Perm (Fin (N - n))), IsPhi hC φ →
      ∀ fs e, M5Full DV hC φ k sIn xy.2 fs e →
      Case2b.c2bR N n (m5Cs X.O n N (N, fs, e)).2.length
      (Case2b.degD X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 - 1)
      (Case2b.sojZ (N - n)) * (sIn + 1) ≤ Lg)
    (hDJ₂ : ∀ (hC : CertSetting (GensData.denote N gs) n)
      (φ : strGroup hC →* Perm (Fin (N - n))), IsPhi hC φ →
      ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e →
      ∀ X₀, m5Leaf2b X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 = some X₀ →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (cjohnOps (N - n))
          (cjFirst2bD N n (m5Cs X.O n N (N, fs, e)).2
            (Case2b.degD X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 - 1) X₀)).2.1 sIn
          gs' d' O' →
      RDOrbit X body DV n N w L (2, cjFirst2bD N n (m5Cs X.O n N (N, fs, e)).2
        (Case2b.degD X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 - 1) X₀) sIn Bd gs' d' O')
    (hu₂ : ∀ (hC : CertSetting (GensData.denote N gs) n)
      (φ : strGroup hC →* Perm (Fin (N - n))), IsPhi hC φ →
      ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e →
      ∀ X₀, m5Leaf2b X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 = some X₀ →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (cjohnOps (N - n))
          (cjFirst2bD N n (m5Cs X.O n N (N, fs, e)).2
            (Case2b.degD X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 - 1) X₀)).2.1 sIn
          gs' d' O' →
      ((labJUD X₀.2.2.2.1.length (markArr (N - n) X₀.2.2.1) X₀.2.2.2.2.2 L O').getD
        (O'.headD 0) []).length ≤ uB)
    (hBg1J₃ : ∀ (hC : CertSetting (GensData.denote N gs) n)
      (φ : strGroup hC →* Perm (Fin (N - n))), IsPhi hC φ →
      ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e →
      ∀ cXX X₀, Case3.ColChar φ (strOn hC.le (xy.1.denote N))
        (strOn hC.le (xy.1.denote N)) k (fixPtsD (m5Os X.O n N (N, fs, e))).length
        (fixPtsD (m5Os X.O n N (N, fs, e))) (fixPtsD (m5Os X.O n N (N, fs, e))) cXX →
      Case3.firstStructD (N - n) k (fixPtsD (m5Os X.O n N (N, fs, e)))
        (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fs, e))).length) = some X₀ → X₀.1 = 2 →
      X.B.call GroupOp.generate
        (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (cjohnGensD (N - n) (cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fs, e)))
            (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fs, e))).length) X₀)))).map
          (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
        (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (cjohnGensD (N - n) (cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fs, e)))
            (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fs, e))).length) X₀))))) ≤ Bg1J₃)
    (hLY₃ : ∀ (hC : CertSetting (GensData.denote N gs) n)
      (φ : strGroup hC →* Perm (Fin (N - n))), IsPhi hC φ →
      ∀ fs e, M5Full DV hC φ k sIn xy.2 fs e →
      Case3.c3R k (fixPtsD (m5Os X.O n N (N, fs, e))).length (Case2b.sojZ (N - n)) *
      (sIn + 1) ≤ Lg)
    (hDJ₃ : ∀ (hC : CertSetting (GensData.denote N gs) n)
      (φ : strGroup hC →* Perm (Fin (N - n))), IsPhi hC φ →
      ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e →
      ∀ cXX X₀, Case3.ColChar φ (strOn hC.le (xy.1.denote N))
        (strOn hC.le (xy.1.denote N)) k (fixPtsD (m5Os X.O n N (N, fs, e))).length
        (fixPtsD (m5Os X.O n N (N, fs, e))) (fixPtsD (m5Os X.O n N (N, fs, e))) cXX →
      Case3.firstStructD (N - n) k (fixPtsD (m5Os X.O n N (N, fs, e)))
        (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fs, e))).length) = some X₀ → X₀.1 = 2 →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (cjohnOps (N - n))
          (cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fs, e)))
            (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fs, e))).length) X₀)).2.1 sIn
          gs' d' O' →
      RDOrbit X body DV n N w L (2, cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fs, e)))
        (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fs, e))).length) X₀) sIn Bd gs' d' O')
    (hu₃ : ∀ (hC : CertSetting (GensData.denote N gs) n)
      (φ : strGroup hC →* Perm (Fin (N - n))), IsPhi hC φ →
      ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e →
      ∀ cXX X₀, Case3.ColChar φ (strOn hC.le (xy.1.denote N))
        (strOn hC.le (xy.1.denote N)) k (fixPtsD (m5Os X.O n N (N, fs, e))).length
        (fixPtsD (m5Os X.O n N (N, fs, e))) (fixPtsD (m5Os X.O n N (N, fs, e))) cXX →
      Case3.firstStructD (N - n) k (fixPtsD (m5Os X.O n N (N, fs, e)))
        (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fs, e))).length) = some X₀ → X₀.1 = 2 →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (cjohnOps (N - n))
          (cjFirst3D (N - n) k (fixPtsD (m5Os X.O n N (N, fs, e)))
            (Case3.colXD cXX k (fixPtsD (m5Os X.O n N (N, fs, e))).length) X₀)).2.1 sIn
          gs' d' O' →
      ((labJUD X₀.2.2.2.1.length (markArr (N - n) X₀.2.2.1) X₀.2.2.2.2.2 L O').getD
        (O'.headD 0) []).length ≤ uB)
    -- the restriction's charges
    {sKR BgmR BliftR BkerR BgnR : ℕ}
    (hBgmR : X.B.call GroupOp.generate ((rbPts nP NP wP).length, rbGens nP NP wP gsP)
      (X.O.run GroupOp.generate ((rbPts nP NP wP).length, rbGens nP NP wP gsP)) ≤ BgmR)
    (hBliftR : ∀ π' : PermData, X.B.call GroupOp.lift ((NP, gsP, dP), (rbU nP NP wP, π'))
      (X.O.run GroupOp.lift ((NP, gsP, dP), (rbU nP NP wP, π'))) ≤ BliftR)
    (hBkerR : X.B.call GroupOp.kernel ((NP, gsP, dP), rbU nP NP wP)
      (X.O.run GroupOp.kernel ((NP, gsP, dP), rbU nP NP wP)) ≤ BkerR)
    (hsKR : (X.O.run GroupOp.kernel ((NP, gsP, dP), rbU nP NP wP)).2.1.length ≤ sKR)
    (hBgnR : ∀ hs : GensData, GensData.AllValid NP hs → hs.length ≤ sKR + sIn →
      GensData.denote NP hs ≤ GensData.denote NP gsP →
      X.B.call GroupOp.generate (NP, hs) (X.O.run GroupOp.generate (NP, hs)) ≤ BgnR) :
    ∃ (fxs fys : GensData) (ex ey : D.denote) (ans : AnswerData D) (ch : List (ℕ × Option ℕ)),
      (∃ (hC : CertSetting (GensData.denote N gs) n) (φ : strGroup hC →* Perm (Fin (N - n))),
        IsPhi hC φ ∧ M5Full DV hC φ k sIn xy.1 fxs ex ∧ M5Full DV hC φ k sIn xy.2 fys ey) ∧
      RunsWithin X body (Main.m5StepCJProg sub
          (((xyP, (wP, (σP, (NP, gsP, dP)))), (n₀, (nP, some LP))) : HInstData D) LP k st) ans
        (rbCost NP wP.1.length (NP - nP) gsP.length
          ((ch.map fun x => C x.1 x.2).sum + 2 * certCount N n k * C (n / k) none +
            m5CKCJ X.O n N k (N, fxs, ex) (N, fys, ey) * C (n / k) none +
            m5CH X.O n N sIn w.1.length (N, fxs, ex) (N, fys, ey) * C (w.1.length / 2) none +
            m5CoreWorkCJ X.O n N k s sIn Bgen Blift Bo Bk Bcr Bd (N, gs, d) (N, fxs, ex)
              (N, fys, ey) w.1.length β B.Bstab B.Btr B.Borb Bk'.Bgen Bk'.Borb Bk'.Bstab
              (fun M => (Bm M).Borb) (fun M => (Bm M).Bstab) (fun M => (Bm M).Btr)
              uB Bg1J₂ Bg1J₃)
          sIn sKR BgmR BliftR BkerR BgnR) ∧
      AnsOK DV NP (wP.denote NP) (PermData.denote NP σP) (GensData.denote NP gsP)
        (xyP.1.denote NP) (xyP.2.denote NP) ans ∧
      (∀ sGen, (∀ hs, GensData.AllValid NP hs →
          GensData.denote NP hs ≤ GensData.denote NP gsP →
          (X.O.run GroupOp.generate (NP, hs)).2.1.length ≤ sGen) →
        ∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sGen) ∧
      ChildList wP.1.length (m5CFCJ X.O n N k (N, fxs, ex) (N, fys, ey) uB)
        (StepChild wP.1.length (NP - nP)) ch :=
  RunsWithin.m5StepCJProg_jp hO hPre hIP haltP hsubP hG' hxy hw hn hL h5 hk h2k hm12 B hgs hGG₀ Bk'
    hsk Bm hCmono hs hB hLg hst β hBgP hBmem hBkA hBlA hBg hBgk hBgs hBF hBk3 hBo3 hBcr3 hB3 hBox
    hBoy hBg1₁ hD₁ hBg1₂ₐ hBgen₂ₐ hBpb hBgm hBlift hBker hsK hBgn
    (fun hC φ hφ fs e hF _ _ X₀ h _ => hBg1₂ᵦ hC φ hφ fs e hF X₀ h) hBgen₂ᵦ hD₂ᵦ
    (fun hC φ hφ fs e hF _ _ X₀ h _ => hBg1₃ hC φ hφ fs e hF X₀ h) hBgen₃ hD₃ hLgJ
    (fun hC φ hφ fs e hF _ _ X₀ h _ _ => hBg1J₂ hC φ hφ fs e hF X₀ h) hLY₂
    (fun hC φ hφ fs e hF _ _ X₀ h _ _ => hDJ₂ hC φ hφ fs e hF X₀ h)
    (fun hC φ hφ fs e hF _ _ X₀ h _ _ => hu₂ hC φ hφ fs e hF X₀ h)
    (fun hC φ hφ fs e hF _ _ cXX X₀ h₁ h₂ h₃ _ => hBg1J₃ hC φ hφ fs e hF cXX X₀ h₁ h₂ h₃) hLY₃
    (fun hC φ hφ fs e hF _ _ cXX X₀ h₁ h₂ h₃ _ => hDJ₃ hC φ hφ fs e hF cXX X₀ h₁ h₂ h₃)
    (fun hC φ hφ fs e hF _ _ cXX X₀ h₁ h₂ h₃ _ => hu₃ hC φ hφ fs e hF cXX X₀ h₁ h₂ h₃) hBgmR hBliftR
    hBkerR hsKR hBgnR

end StepSpecCJ

end GraphIso.Main
