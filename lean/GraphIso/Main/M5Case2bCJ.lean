module

public import GraphIso.Main.M5CJProg
public import GraphIso.Main.M5Cases

/-!
# M5, Case 2b with coloured Johnson alignment

Stage 14j-4b, item 3 (`PLAN-14.md` §14.5). When `x`'s first leaf in Case 2b is a Johnson leaf,
Align compares it as a coloured pair (`cjohnOps`, colouring `q2bD`) with `y`'s coloured Johnson
leaves, and reduce-and-derive runs on the aligned cosets with `st = (2, X₀)`, so no orbit is
stuck (`rd_ns_cj`). Otherwise 14j-4's `m5Case2bProg` runs.

* **The test** `c2bJTestProg` (`c2bJD`): `x`'s first leaf is a Johnson leaf.
* **The Johnson route** `c2bCJProg`: both degrees (if they differ, no isomorphism), `x`'s first
  leaf, the first tuple's colouring, `y`'s coloured Johnson leaves (`cjLeaves2bProg`), and Align
  with `cjohnOps` and `rdBranch` at `st = (2, X₀)`.
  `RunsWithin.c2bCJProg`: under Case 2b's hypotheses and `c2bJD = true`, the answer is correct
  and the children are `StepChild |W| m`, `c2bR` copies of one list with factor
  `max(m, uB!)`: no stuck orbit (`alignRd_cj_ns`). The colour bound (`cj2b_hq`), the alignment
  (`cj2b_reach`) and the validity (`cj2b_valid`) of the coloured pairs are proved, not assumed.
* **The variant** `m5Case2bCJProg`: the test, then the Johnson route or `m5Case2bProg`.
  `RunsWithin.m5Case2bCJProg`: the answer is correct in both branches; the cost is the test's
  plus the branch's, and the children's factor is `c2bR · max(m, uB!)` for a Johnson leaf,
  `c2bR · F` otherwise (14j-4's `RunsWithin.m5Case2bProg`, whose reduce-and-derive hypotheses
  are then needed only for a leaf that is not a Johnson leaf).
-/

@[expose] public section

namespace GraphIso.Main

open Equiv Finset Pointwise Cost GraphIso GraphIso.Programs GraphIso.Toolkit GraphIso.SoJProg
  GraphIso.SoJTree GraphIso.Case2b GraphIso.Align GraphIso.Recursion GraphIso.SplitJohnson
  GraphIso.Solver

/-! ### The programs -/

section Programs

variable {D : Ty} {rec : Ty × Ty} {var : Ty → Type}

/-- **The test of Case 2b's Johnson route** (`c2bJD`): `x`'s first leaf is a Johnson leaf. -/
def c2bJTestProg (n : var .nat) (Fx : var (Ty.group D)) (Φx : var (.list .nat)) :
    Prog (groupSig D) rec var .bool :=
  .bind (.op1 .fst Fx) fun N =>
  .bind (Case2b.degProg N n Fx Φx) fun dx =>
  .bind (.op0 (.natLit 1)) fun one => .bind (.op2 .sub dx one) fun j =>
  .bind (Case2b.firstLeafProg N n Fx Φx j) fun ox =>
  .caseOption ox (.op0 (.boolLit false)) fun X₀ =>
    .bind (.op1 .fst X₀) fun tag => .bind (.op0 (.natLit 2)) fun two => .op2 .natEq tag two

/-- **Case 2b's Johnson route**: if the degrees differ, no isomorphism; otherwise `x`'s first leaf
with the colouring of its tuple, `y`'s coloured Johnson leaves, and Align with `cjohnOps`; on
each aligned coset, reduce-and-derive with `st = (2, X₀)`. -/
def c2bCJProg (sub : var (hinstTy D) → Prog (groupSig D) rec var (Ty.answer D))
    (n₀ n : var .nat) (L : var (.array (.list .nat))) (xy : var Ty.strs) (w : var Ty.win)
    (G Fx Fy : var (Ty.group D)) (Φx Φy : var (.list .nat)) :
    Prog (groupSig D) rec var (Ty.answer D) :=
  .bind (.op1 .fst G) fun N => .bind (.op2 .sub N n) fun m =>
  .bind (Case2b.degProg N n Fx Φx) fun dx => .bind (Case2b.degProg N n Fy Φy) fun dy =>
  .bind (.op2 .natEq dx dy) fun same =>
  .ite same
    (.bind (.op0 (.natLit 1)) fun one => .bind (.op2 .sub dx one) fun j =>
      .bind (Case2b.firstLeafProg N n Fx Φx j) fun ox =>
      .caseOption ox (.op0 .none) fun X₀ =>
      .bind (firstTupleProg Φx j) fun S₀ => .bind (q2bProg m Φx S₀) fun qx =>
      .bind (.op1 .snd X₀) fun r => .bind (.op1 .snd r) fun jd =>
      .bind (.op2 .pair jd qx) fun X₀c =>
      .bind (cjLeaves2bProg N n Fy Φy j) fun Ys =>
      .bind (.op0 (.natLit 2)) fun two => .bind (.op2 .pair two X₀c) fun st' =>
      Align.alignProg (fun J => Main.rdBranch sub n₀ n L st' J) (fun e => cjohnGensProg m e)
        (fun e e' => cjohnIsoProg m e e') n xy w G X₀c Ys)
    (.op0 .none)

/-- **Case 2b of M5 with coloured Johnson alignment**: the Johnson route when the test holds,
14j-4's `m5Case2bProg` otherwise. -/
def m5Case2bCJProg (sub : var (hinstTy D) → Prog (groupSig D) rec var (Ty.answer D))
    (n₀ n : var .nat) (L : var (.array (.list .nat))) (st : var stTy) (xy : var Ty.strs)
    (w : var Ty.win) (G Fx Fy : var (Ty.group D)) (Φx Φy : var (.list .nat)) :
    Prog (groupSig D) rec var (Ty.answer D) :=
  .bind (c2bJTestProg n Fx Φx) fun isJ =>
  .ite isJ (c2bCJProg sub n₀ n L xy w G Fx Fy Φx Φy)
    (m5Case2bProg sub n₀ n L st xy w G Fx Fy Φx Φy)

end Programs

/-! ### The test on data -/

section TestData

variable {D : Ty}

/-- **The test of Case 2b's Johnson route**, on data: `x`'s first leaf is a Johnson leaf. -/
def c2bJD (O : Oracle (groupSig D)) (N n : ℕ) (Fx : GroupData D.denote) (Φx : List ℕ) : Bool :=
  match firstLeafD O N n Fx Φx (degD O N n Fx Φx - 1) with
  | some X₀ => X₀.1 == 2
  | none => false

theorem c2bJD_true {O : Oracle (groupSig D)} {N n : ℕ} {Fx : GroupData D.denote}
    {Φx : List ℕ} (h : c2bJD O N n Fx Φx = true) :
    ∃ X₀, m5Leaf2b O N n Fx Φx = some X₀ ∧ X₀.1 = 2 := by
  unfold c2bJD at h
  unfold m5Leaf2b
  rcases hf : firstLeafD O N n Fx Φx (degD O N n Fx Φx - 1) with _ | X₀
  · rw [hf] at h
    exact absurd h (by simp)
  · rw [hf] at h
    exact ⟨X₀, rfl, by simpa using h⟩

theorem c2bJD_false {O : Oracle (groupSig D)} {N n : ℕ} {Fx : GroupData D.denote}
    {Φx : List ℕ} (h : c2bJD O N n Fx Φx = false) {X₀ : OutD}
    (hX₀ : m5Leaf2b O N n Fx Φx = some X₀) : X₀.1 ≠ 2 := by
  unfold c2bJD at h
  unfold m5Leaf2b at hX₀
  rw [hX₀] at h
  simpa using h

/-- **The facts of a coloured Johnson pair that the Johnson routes establish** before aligning
it: the pair is valid, and its structure is a Johnson structure. -/
def CJFacts (m : ℕ) (Y : CJData) : Prop :=
  CJValid m Y ∧ ∃ t, IsJohnson Finset.univ t (Align.jdec m Y.1)

/-- When the test holds, the first leaf is a Johnson leaf. -/
theorem c2bJD_tag {O : Oracle (groupSig D)} {N n : ℕ} {Fx : GroupData D.denote}
    {Φx : List ℕ} (h : c2bJD O N n Fx Φx = true) {X₀ : OutD}
    (hX₀ : m5Leaf2b O N n Fx Φx = some X₀) : X₀.1 = 2 := by
  obtain ⟨X₁, h₁, h₂⟩ := c2bJD_true h
  rw [hX₀, Option.some.injEq] at h₁
  rw [h₁]
  exact h₂

end TestData

/-! ### The pieces' specifications -/

section PieceSpecs

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}

/-- The cost of the test: `x`'s degree and first leaf. -/
def c2bJTestCost (N n s nx j Bstab Bg Z : ℕ) (Bo Bs Bt : ℕ → ℕ) : ℕ :=
  1 + degCost N n nx nx s Bstab Bg (Bo nx) (Bs nx) + 1 + 1 +
    (tuplesCost nx j + chCost N n s nx j Bstab Bg (Bt (nx - j)) (Bs (nx - j)) (Bo (nx - j)) Z +
      8) + 1 + 3

/-- **The test, as a program.** -/
theorem RunsWithin.c2bJTestProg (hO : MeetsContractOn DV c2bOps X.O)
    (hPre : ∀ op x, c2bOps op → GroupPre DV op x → X.Pre op x)
    {N n s : ℕ} {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N s G₀)
    {sm : ℕ → ℕ} (Bm : ∀ M, BackendBounds X DV M (sm M) ⊤)
    {fxs : GensData} {ex : D.denote} (hFxv : GroupValid DV N fxs ex) (hFxs : fxs.length ≤ s)
    (hFx₀ : GensData.denote N fxs ≤ G₀)
    {Φx : List ℕ} (hΦxn : Φx.Nodup) (hΦxl : ∀ i ∈ Φx, i < N - n)
    (hΦx : IsInvariant (GensData.denote N fxs) {u | u.val ∈ ptsD n Φx})
    (hjx : degD X.O N n (N, fxs, ex) Φx - 1 + 2 ≤ Φx.length) {Bg : ℕ}
    (hBg : ∀ M ≤ N - n, ∀ gs' : GensData, GensData.AllValid M gs' → gs'.length ≤ s →
      X.B.call GroupOp.generate (M, gs') (X.O.run GroupOp.generate (M, gs')) ≤ Bg) {Z : ℕ}
    (hZx : ∀ Sl ∈ tuplesD Φx (degD X.O N n (N, fxs, ex) Φx - 1),
      ∀ ab ∈ pairsD (phiSD (N - n) Φx Sl).length,
        sojSz (phiSD (N - n) Φx Sl).length (wlColOf X.O N n (N, fxs, ex) Φx Sl ab.1 ab.2) ≤ Z) :
    RunsWithin X body (Main.c2bJTestProg n (N, fxs, ex) Φx) (c2bJD X.O N n (N, fxs, ex) Φx)
      (c2bJTestCost N n s Φx.length (degD X.O N n (N, fxs, ex) Φx - 1) B.Bstab Bg Z
        (fun M => (Bm M).Borb) (fun M => (Bm M).Bstab) (fun M => (Bm M).Btr)) := by
  have hOd : MeetsContractOn DV degOps X.O := fun op x h hp => hO op x (Or.inl h) hp
  have hPd : ∀ op x, degOps op → GroupPre DV op x → X.Pre op x := fun op x h hp =>
    hPre op x (Or.inl h) hp
  have hOc := cp2_choiceOps_of_deg hOd
  have hPc : ∀ op x, choiceOps op → GroupPre DV op x → X.Pre op x := fun op x h hp =>
    hPre op x (Or.inl (Or.inl h)) hp
  have hdx := RunsWithin.degProg_le (body := body) hOd hPd B Bm hFxv hFxs hFx₀ hΦxn hΦxl hΦx hBg
  have hfl := RunsWithin.firstLeafProg_le (body := body) hOc hPc B Bm hFxv hFxs hFx₀ hΦxn hΦxl
    hΦx (j := degD X.O N n (N, fxs, ex) Φx - 1) hjx hBg hZx
  rcases hf : firstLeafD X.O N n (N, fxs, ex) Φx (degD X.O N n (N, fxs, ex) Φx - 1) with _ | X₀
  · rw [hf] at hfl
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step hdx
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step hfl
      run_with RunsWithin.caseOption_none _
      exact (RunsWithin.prim _ _).of_eq (by rw [c2bJD, hf]; rfl)
    case hc =>
      simp only [Prim.cost, c2bJTestCost]
      omega
  · rw [hf] at hfl
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step hdx
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step hfl
      run_with RunsWithin.caseOption_some _
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      exact (RunsWithin.prim _ _).of_eq (by rw [c2bJD, hf]; rfl)
    case hc =>
      simp only [Prim.cost, c2bJTestCost]
      omega

/-- **`y`'s coloured Johnson leaves, at the uniform cost**: at most `|Φ|^j` tuples, `(N − n)²`
pairs, and `Z + 1` leaves per choice. -/
theorem RunsWithin.cjLeaves2bProg_le (hO : MeetsContractOn DV choiceOps X.O)
    (hPre : ∀ op x, choiceOps op → GroupPre DV op x → X.Pre op x)
    {N n s : ℕ} {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N s G₀)
    {sm : ℕ → ℕ} (Bm : ∀ M, BackendBounds X DV M (sm M) ⊤)
    {gs : GensData} {d : D.denote} (hGv : GroupValid DV N gs d) (hs : gs.length ≤ s)
    (hG₀ : GensData.denote N gs ≤ G₀) {Φ : List ℕ} (hΦn : Φ.Nodup) (hΦl : ∀ i ∈ Φ, i < N - n)
    (hΦ : IsInvariant (GensData.denote N gs) {u | u.val ∈ ptsD n Φ}) {j : ℕ}
    (hj : j < Φ.length) {Bg : ℕ}
    (hBg : ∀ M ≤ N - n, ∀ gs' : GensData, GensData.AllValid M gs' → gs'.length ≤ s →
      X.B.call GroupOp.generate (M, gs') (X.O.run GroupOp.generate (M, gs')) ≤ Bg) {Z : ℕ}
    (hZ : ∀ Sl ∈ tuplesD Φ j, ∀ ab ∈ pairsD (phiSD (N - n) Φ Sl).length,
      sojSz (phiSD (N - n) Φ Sl).length (wlColOf X.O N n (N, gs, d) Φ Sl ab.1 ab.2) ≤ Z) :
    RunsWithin X body (Main.cjLeaves2bProg N n (N, gs, d) Φ j)
      (cjLeaves2bD X.O N n (N, gs, d) Φ j)
      (cjAllCost (N - n) Φ.length j (chCost N n s Φ.length j B.Bstab Bg (Bm (Φ.length - j)).Btr
        (Bm (Φ.length - j)).Bstab (Bm (Φ.length - j)).Borb Z) (Z + 1)) := by
  refine RunsWithin.cjLeaves2bProg (fun Sl hSl ab hab => ?_) fun Sl hSl ab hab => ?_
  · obtain ⟨hSlen, hSn, hSΦ⟩ := (mem_tuplesD Φ j).1 hSl
    have ha := (Case2b.mem_pairsD.1 (show (ab.1, ab.2) ∈ _ from hab)).1
    rw [length_phiSD hΦn hΦl hSn hSΦ, hSlen] at ha
    exact RunsWithin.choiceProg_le hO hPre B Bm hGv hs hG₀ hΦn hΦl hΦ hj hBg hSl ha.le
      (hZ Sl hSl ab hab)
  · unfold choiceLeavesD
    rw [List.length_map]
    exact (length_leavesOfD_le _ _).trans (Nat.add_le_add_right (hZ Sl hSl ab hab) 1)

/-- At most one coloured datum per leaf. -/
theorem length_flatMap_cjOfD_le (q : Array ℕ) (l : List OutD) :
    (l.flatMap (cjOfD q)).length ≤ l.length := by
  rw [List.length_flatMap]
  calc (l.map fun o => (cjOfD q o).length).sum ≤ (l.map fun _ => 1).sum :=
        List.sum_le_sum fun o _ => by unfold cjOfD; split_ifs <;> simp
    _ = l.length := by simp

/-- **`y`'s coloured Johnson leaves are at most `c2bR`.** -/
theorem length_cjLeaves2bD_le {O : Oracle (groupSig D)} {N n : ℕ} {F : GroupData D.denote}
    {Φ : List ℕ} {j Lc : ℕ}
    (hL : ∀ Sl ∈ tuplesD Φ j, ∀ ab ∈ pairsD (phiSD (N - n) Φ Sl).length,
      (choiceLeavesD O N n F Φ Sl ab.1 ab.2).length ≤ Lc) :
    (cjLeaves2bD O N n F Φ j).length ≤ Φ.length ^ j * ((N - n) * (N - n) * Lc) := by
  refine (po_length_flatMap_le _ fun Sl hSl => ?_).trans
    (Nat.mul_le_mul_right _ (length_tuplesD_le Φ j))
  have hm := length_phiSD_le (N - n) Φ Sl
  refine (po_length_flatMap_le _ fun ab hab =>
    (length_flatMap_cjOfD_le _ _).trans (hL Sl hSl ab hab)).trans ?_
  exact Nat.mul_le_mul_right _ ((Case2b.length_pairsD_le _).trans (Nat.mul_le_mul hm hm))

end PieceSpecs

/-! ### The Johnson route -/

/-- **The cost of Case 2b's Johnson route**: both degrees, `x`'s first leaf, the first tuple and
its colouring, `y`'s coloured Johnson leaves, and Align with `cjohnOps` (`k` stabilizer generators,
`c2bR` candidates, branch cost `Cb`). -/
def c2bCJCost (n N s g nx ny j k Bstab Bg Z BgP Bmem Bk Bl Bg1 Bgen Cb : ℕ)
    (Bo Bs Bt : ℕ → ℕ) : ℕ :=
  1 + 1 + degCost N n nx nx s Bstab Bg (Bo nx) (Bs nx) +
    degCost N n ny ny s Bstab Bg (Bo ny) (Bs ny) + 1 + 1 + 1 + 1 +
    (tuplesCost nx j + chCost N n s nx j Bstab Bg (Bt (nx - j)) (Bs (nx - j)) (Bo (nx - j)) Z +
      8) +
    (1 + (tuplesCost nx j + 2 + q2bCost (N - n) nx j + 1 + 1 + 1 +
      cjAllCost (N - n) ny j
        (chCost N n s ny j Bstab Bg (Bt (ny - j)) (Bs (ny - j)) (Bo (ny - j)) Z) (Z + 1) + 1 + 1 +
      alignCost n N g k (c2bR N n ny j Z) (cjohnGensCost (leafB (N - n)))
        (cjohnIsoCost (leafB (N - n))) BgP Bmem Bk Bl Bg1 Bgen Cb s))

section JohnsonRoute

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}
  {sub : HInstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)}
  {C : ℕ → Option ℕ → ℕ} {s : ℕ} {xy : StrData × StrData} {w : WinData}
  {N : ℕ} {gs : GensData} {d : D.denote} {n₀ n : ℕ} {L : LabelData}
  {sIn Lg Blift Bgen Bo Bk Bcr Bd : ℕ}

/-- **Case 2b's Johnson route.** Under Case 2b's hypotheses (as in `RunsWithin.m5Case2bProg`)
and the test (`c2bJD = true`: `x`'s first leaf `X₀` is a Johnson leaf): the answer is correct
for `G` on `W` (no isomorphism when the degrees differ, `cp2_degD_eq`), and the children are
`StepChild |W| m`, `c2bR` copies of one list with windows summing to at most
`max(m, uB!) · |W|`. No orbit is stuck
(`alignRd_cj_ns`): the coloured pair of `X₀` is aligned (`cj2b_reach`), valid (`cj2b_valid`),
Johnson (`choiceLeavesD_along`) and has small colour classes (`cj2b_hq`). Assumed: the
backend's charges, `RDBounds`, the per-orbit `RDOrbit` for `st = (2, X₀)`, and the bound `uB`
on the union cells.

Its Johnson-route hypotheses (`hBg1`, `hD`, `hu`) are needed only with the facts `CJFacts` of the
first coloured pair, which the proof establishes before aligning (stage 14j-5c, `PLAN-14.md` §14.8
item 4); `RunsWithin.c2bCJProg` states them without these facts. -/
theorem RunsWithin.c2bCJProg_jp (hOc : MeetsContractOn DV Case2b.c2bOps X.O)
    (hPc : ∀ op x, Case2b.c2bOps op → GroupPre DV op x → X.Pre op x)
    (hO : MeetsContractOn DV rdOps X.O)
    (hPre : ∀ op x, rdOps op → GroupPre DV op x → X.Pre op x)
    (hI : HInstValid DV (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D))
    {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N sIn G₀)
    (hGG₀ : GensData.denote N gs ≤ G₀)
    {sm : ℕ → ℕ} (Bm : ∀ M, BackendBounds X DV M (sm M) ⊤)
    (hG : IsInvariant (GensData.denote N gs) (baseSet n N))
    (halt : alternatingGroup (Fin (N - n)) ≤ (baseHom _ n hG).range)
    {Fmap : (Fin N → ℕ) → Subgroup (Perm (Fin N))}
    (hloc : ∀ x x', (∀ u ∈ w.denote N, x u = x' u) → Fmap x = Fmap x')
    (heq : ∀ g ∈ GensData.denote N gs, ∀ x,
      Fmap (relabel g x) = (Fmap x).map (MulAut.conj g).toMonoidHom)
    {fxs fys : GensData} {ex ey : D.denote} (hFxv : GroupValid DV N fxs ex)
    (hFyv : GroupValid DV N fys ey) (hFxs : fxs.length ≤ sIn) (hFys : fys.length ≤ sIn)
    (hFx₀ : GensData.denote N fxs ≤ G₀) (hFy₀ : GensData.denote N fys ≤ G₀)
    (hFxe : GensData.denote N fxs = Fmap (xy.1.denote N))
    (hFye : GensData.denote N fys = Fmap (xy.2.denote N))
    (hFxi : IsInvariant (GensData.denote N fxs) (baseSet n N))
    (hFyi : IsInvariant (GensData.denote N fys) (baseSet n N))
    {Φx Φy : List ℕ} (hΦxn : Φx.Nodup) (hΦxl : ∀ i ∈ Φx, i < N - n)
    (hΦx2 : N - n < 2 * Φx.length)
    (hΦxo : ∃ γ : Fin (N - n), γ.val ∈ Φx ∧ ∀ δ : Fin (N - n),
      δ.val ∈ Φx ↔ δ ∈ MulAction.orbit (baseHom _ n hFxi).range γ)
    (hΦyn : Φy.Nodup) (hΦyl : ∀ i ∈ Φy, i < N - n) (hΦy2 : N - n < 2 * Φy.length)
    (hΦyo : ∃ γ : Fin (N - n), γ.val ∈ Φy ∧ ∀ δ : Fin (N - n),
      δ.val ∈ Φy ↔ δ ∈ MulAction.orbit (baseHom _ n hFyi).range γ)
    (hngx : ¬ Case2b.TupTrans (baseHom _ n hFxi).range (SoJProg.setOf (N - n) Φx) (Φx.length - 2))
    (hngy : ¬ Case2b.TupTrans (baseHom _ n hFyi).range (SoJProg.setOf (N - n) Φy) (Φy.length - 2))
    (hJ : c2bJD X.O N n (N, fxs, ex) Φx = true)
    {Bg BgP Bmem BkA BlA Bg1 uB : ℕ}
    (hBg : ∀ M ≤ N - n, ∀ gs' : GensData, GensData.AllValid M gs' → gs'.length ≤ sIn →
      X.B.call GroupOp.generate (M, gs') (X.O.run GroupOp.generate (M, gs')) ≤ Bg)
    (hBgP : X.B.call GroupOp.generate (N - n, gs.map (baseD n N))
      (X.O.run GroupOp.generate (N - n, gs.map (baseD n N))) ≤ BgP)
    (hBmem : ∀ g : PermData, g.Valid (N - n) → X.B.call GroupOp.mem (pModel X.O n (N, gs, d), g)
      (X.O.run GroupOp.mem (pModel X.O n (N, gs, d), g)) ≤ Bmem)
    (hBkA : X.B.call GroupOp.kernel ((N, gs, d), baseWin n N) (kerModel X.O n (N, gs, d)) ≤ BkA)
    (hBlA : ∀ π : PermData, X.B.call GroupOp.lift ((N, gs, d), (baseWin n N, π))
      (liftModel X.O n (N, gs, d) π) ≤ BlA)
    (hBg1 : ∀ X₀ : OutD, m5Leaf2b X.O N n (N, fxs, ex) Φx = some X₀ →
      CJFacts (N - n) (cjFirst2bD N n Φx (degD X.O N n (N, fxs, ex) Φx - 1) X₀) →
      X.B.call GroupOp.generate
        (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (cjohnGensD (N - n) (cjFirst2bD N n Φx (degD X.O N n (N, fxs, ex) Φx - 1) X₀)))).map
          (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
        (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (cjohnGensD (N - n) (cjFirst2bD N n Φx (degD X.O N n (N, fxs, ex) Φx - 1) X₀))))) ≤
        Bg1)
    (hsub : HSubSolves X body DV sub
      (fun J => SizeChild sIn (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D)
        J ∧ StepChild w.1.length (N - n) (J.winSize, J.baseOpt)) C s)
    (hB : RDBounds X DV n N sIn Lg Blift Bgen Bo Bk Bcr) (hs : s ≤ sIn)
    (hLY : c2bR N n Φy.length (degD X.O N n (N, fys, ey) Φy - 1) (sojZ (N - n)) * (sIn + 1) ≤
      Lg)
    (hLg : max (N - n) uB.factorial * (sIn + 1) ≤ Lg) (hm5 : 5 ≤ N - n)
    (hD : ∀ X₀, m5Leaf2b X.O N n (N, fxs, ex) Φx = some X₀ →
      CJFacts (N - n) (cjFirst2bD N n Φx (degD X.O N n (N, fxs, ex) Φx - 1) X₀) →
      ∀ gs' d' O', RDSet DV n N gs w L
      (Giant.g1Model X.O n (N, gs, d) (cjohnOps (N - n))
        (cjFirst2bD N n Φx (degD X.O N n (N, fxs, ex) Φx - 1) X₀)).2.1 sIn gs' d' O' →
      RDOrbit X body DV n N w L (2, cjFirst2bD N n Φx (degD X.O N n (N, fxs, ex) Φx - 1) X₀) sIn
        Bd gs' d' O')
    (hu : ∀ X₀, m5Leaf2b X.O N n (N, fxs, ex) Φx = some X₀ →
      CJFacts (N - n) (cjFirst2bD N n Φx (degD X.O N n (N, fxs, ex) Φx - 1) X₀) →
      ∀ gs' d' O', RDSet DV n N gs w L
      (Giant.g1Model X.O n (N, gs, d) (cjohnOps (N - n))
        (cjFirst2bD N n Φx (degD X.O N n (N, fxs, ex) Φx - 1) X₀)).2.1 sIn gs' d' O' →
      ((labJUD X₀.2.2.2.1.length (markArr (N - n) X₀.2.2.1) X₀.2.2.2.2.2 L O').getD
        (O'.headD 0) []).length ≤ uB) :
    ∃ X₀ : OutD, m5Leaf2b X.O N n (N, fxs, ex) Φx = some X₀ ∧ X₀.1 = 2 ∧
      ∃ (ans : AnswerData D) (ch : List (ℕ × Option ℕ)),
        RunsWithin X body
          (Main.c2bCJProg sub n₀ n L xy w (N, gs, d) (N, fxs, ex) (N, fys, ey) Φx Φy) ans
          ((ch.map fun x => C x.1 x.2).sum +
            c2bCJCost n N sIn gs.length Φx.length Φy.length
              (degD X.O N n (N, fxs, ex) Φx - 1)
              (cjohnGensD (N - n) (cjFirst2bD N n Φx (degD X.O N n (N, fxs, ex) Φx - 1) X₀)).length
              B.Bstab Bg (sojZ (N - n)) BgP Bmem BkA BlA Bg1 Bgen
              (w.1.length * rdOrbitWork N n w.1.length s sIn (max (N - n) uB.factorial) Bd Blift
                Bgen Bo 0 + dynSeqCost N w.1.length Bo + 5)
              (fun M => (Bm M).Borb) (fun M => (Bm M).Bstab) (fun M => (Bm M).Btr)) ∧
        AnsOK DV N (w.denote N) 1 (GensData.denote N gs) (xy.1.denote N) (xy.2.denote N) ans ∧
        (∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sIn) ∧
        ChildList w.1.length
          (c2bR N n Φy.length (degD X.O N n (N, fxs, ex) Φx - 1) (sojZ (N - n)) *
            max (N - n) uB.factorial) (StepChild w.1.length (N - n)) ch := by
  classical
  have hGv : GroupValid DV N gs d := hI.valid.group
  have hw : w.Valid N := hI.valid.win
  have hWG : IsInvariant (GensData.denote N gs) (w.denote N) := hI.valid.invariant
  have hOa : MeetsContractOn DV alignOps X.O := fun op x h hx => hOc op x (Or.inr h) hx
  have hPa : ∀ op x, alignOps op → GroupPre DV op x → X.Pre op x :=
    fun op x h hx => hPc op x (Or.inr h) hx
  have hOd : MeetsContractOn DV degOps X.O := fun op x h hp => hOc op x (Or.inl h) hp
  have hPd : ∀ op x, degOps op → GroupPre DV op x → X.Pre op x := fun op x h hp =>
    hPc op x (Or.inl h) hp
  have hOch := cp2_choiceOps_of_deg hOd
  have hPch : ∀ op x, choiceOps op → GroupPre DV op x → X.Pre op x := fun op x h hp =>
    hPc op x (Or.inl (Or.inl h)) hp
  -- the hypotheses of the choice trees
  obtain ⟨γx, hγxm, hγx⟩ := hΦxo
  obtain ⟨γy, hγym, hγy⟩ := hΦyo
  have hΦx := cp2_inv_of_orbit hFxi hΦxl ⟨γx, hγx⟩
  have hΦy := cp2_inv_of_orbit hFyi hΦyl ⟨γy, hγy⟩
  obtain ⟨h1x, Hx⟩ := case2bHyp_degD hOd hPd B hFxv hFxs hFx₀ hFxi hΦxn hΦxl hΦx (Bm _)
    ⟨γx, hγx⟩ hngx
  obtain ⟨h1y, Hy⟩ := case2bHyp_degD hOd hPd B hFyv hFys hFy₀ hFyi hΦyn hΦyl hΦy (Bm _)
    ⟨γy, hγy⟩ hngy
  obtain ⟨X₀, hfirst, h2⟩ := c2bJD_true hJ
  unfold m5Leaf2b at hfirst
  -- an isomorphism conjugates `ψ(F)` and translates `Φ`
  have hconj : ∀ g ∈ iso (w.denote N) 1 (GensData.denote N gs) (xy.1.denote N) (xy.2.denote N),
      ∃ hgG : g ∈ GensData.denote N gs,
        (∀ h, h ∈ (baseHom _ n hFyi).range ↔ (baseHom _ n hG ⟨g, hgG⟩)⁻¹ * h *
          baseHom _ n hG ⟨g, hgG⟩ ∈ (baseHom _ n hFxi).range) ∧
        baseHom _ n hG ⟨g, hgG⟩ • SoJProg.setOf (N - n) Φx = SoJProg.setOf (N - n) Φy := by
    intro g hg
    have hgG : g ∈ GensData.denote N gs := (mem_iso_one.1 hg).1
    have hy : GensData.denote N fys =
        (GensData.denote N fxs).map (MulAut.conj g).toMonoidHom := by
      rw [hFye, hFxe, ← heq g hgG _]
      exact (hloc _ _ (Recursion.relabel_eq_on_of_mem_iso hWG hg)).symm
    exact ⟨hgG, cp2_range_conj hG hFxi hFyi hgG hy, Giant.largeOrbit_canonical hG hWG hloc heq
      hFxe hFye hFxi hFyi hg hΦxn hΦxl hΦx2 ⟨γx, hγxm, hγx⟩ hΦyn hΦyl hΦy2 ⟨γy, hγym, hγy⟩⟩
  have hdx := RunsWithin.degProg_le (body := body) hOd hPd B Bm hFxv hFxs hFx₀ hΦxn hΦxl hΦx hBg
  have hdy := RunsWithin.degProg_le (body := body) hOd hPd B Bm hFyv hFys hFy₀ hΦyn hΦyl hΦy hBg
  by_cases hdeg : degD X.O N n (N, fxs, ex) Φx = degD X.O N n (N, fys, ey) Φy
  swap
  · -- different degrees: no isomorphism
    refine ⟨X₀, hfirst, h2, none, [], ?_, ?_, ?_, ?_⟩
    rotate_left 2
    · intro c hc
      cases hc
    · exact ⟨by simp, by simp, by simp⟩
    · apply RunsWithin.mono
      case h =>
        unfold Main.c2bCJProg
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step hdx
        run_step hdy
        run_step (RunsWithin.prim _ _)
        run_with Sims.RunsWithin.ite_neg (show (degD X.O N n (N, fxs, ex) Φx ==
          degD X.O N n (N, fys, ey) Φy) = false by simp [hdeg]) _
        exact RunsWithin.prim _ _
      case hc =>
        simp only [Prim.cost, c2bCJCost]
        omega
    · show iso (w.denote N) 1 (GensData.denote N gs) (xy.1.denote N) (xy.2.denote N) = ∅
      by_contra hiso
      obtain ⟨g, hg⟩ := Set.nonempty_iff_ne_empty.2 hiso
      obtain ⟨hgG, hP, hΦσ⟩ := hconj g hg
      exact hdeg (cp2_degD_eq hOd hPd B Bm hFxv hFyv hFxs hFys hFx₀ hFy₀ hFxi hFyi hΦxn hΦxl
        hΦyn hΦyl ⟨γx, hγx⟩ ⟨γy, hγy⟩ _ hP hΦσ)
  set j := degD X.O N n (N, fxs, ex) Φx - 1 with hj
  have Hx' : Case2bHyp (baseHom _ n hFxi).range (SoJProg.setOf (N - n) Φx) (j + 1) := by
    rw [hj, Nat.sub_add_cancel h1x]
    exact Hx
  have Hy' : Case2bHyp (baseHom _ n hFyi).range (SoJProg.setOf (N - n) Φy) (j + 1) := by
    rw [hj, hdeg, Nat.sub_add_cancel h1y]
    exact Hy
  have hjy : j = degD X.O N n (N, fys, ey) Φy - 1 := by rw [hj, hdeg]
  have hjx : j + 2 ≤ Φx.length := by
    have := Hx'.size
    rw [card_setOf hΦxn hΦxl] at this
    omega
  have hjy' : j < Φy.length := by
    have := Hy'.size
    rw [card_setOf hΦyn hΦyl] at this
    omega
  -- the runs of the pieces
  have hfl := RunsWithin.firstLeafProg_le (body := body) hOch hPch B Bm hFxv hFxs hFx₀ hΦxn hΦxl
    hΦx (j := j) hjx hBg
    (fun Sl hSl ab hab => sojSz_le (F := (N, fxs, ex)) hOch rfl hFxv hFxi hΦxl Hx' hSl hab)
  rw [hfirst] at hfl
  have hYrun := RunsWithin.cjLeaves2bProg_le (body := body) hOch hPch B Bm hFyv hFys hFy₀ hΦyn
    hΦyl hΦy hjy' hBg
    (fun Sl hSl ab hab => sojSz_le (F := (N, fys, ey)) hOch rfl hFyv hFyi hΦyl Hy' hSl hab)
  obtain ⟨hS₀, hX₀mem⟩ := firstLeafD_firstTuple hfirst
  have hS₀len : (firstTupleD Φx j).length = j := mem_tuplesD_length hS₀
  have hft := RunsWithin.firstTupleProg (X := X) (body := body) Φx j
  have hq := RunsWithin.q2bProg (X := X) (body := body) (N - n) Φx (firstTupleD Φx j)
  rw [hS₀len] at hq
  -- the coloured pair of `x`
  set X₀c := cjFirst2bD N n Φx j X₀ with hX₀c
  set Ys := cjLeaves2bD X.O N n (N, fys, ey) Φy j with hYs
  have hmL : N - n ≤ leafB (N - n) := by
    rw [leafB]
    omega
  have h01 : ((0, 1) : ℕ × ℕ) ∈ pairsD (phiSD (N - n) Φx (firstTupleD Φx j)).length :=
    Case2b.mem_pairsD.2 ⟨by have := lk_four hΦxl Hx' hS₀; omega,
      by have := lk_four hΦxl Hx' hS₀; omega, Nat.zero_ne_one⟩
  have hal := choiceLeavesD_along hOch hFxv hFxi hΦxl Hx' hS₀ h01 hX₀mem h2
  obtain ⟨t, hJt⟩ := isJohnson_of_along hal
  have hXv : CJValid (N - n) X₀c ∧ JBound (leafB (N - n)) X₀c.1 := by
    refine ⟨?_, cp2_jbound_le (outSize_firstLeafD hfirst)⟩
    rcases firstLeafD_valid (F := (N, fxs, ex)) hOch rfl hFxv hFxi hΦxn hΦxl Hx' hfirst with
      ⟨h1, -⟩ | ⟨-, hv⟩
    · omega
    · exact hv
  have hYv : ∀ Y ∈ Ys, CJValid (N - n) Y ∧ JBound (leafB (N - n)) Y.1 := by
    intro Y hY
    refine ⟨cj2b_valid hOch hFyv hFyi hΦyn hΦyl Hy' Y hY, ?_⟩
    obtain ⟨S, -, ab, -, o, ho, -, rfl⟩ := mem_cjLeaves2bD.1 hY
    exact cp2_jbound_le (outSize_choiceLeavesD o ho)
  have hYlen : Ys.length ≤ c2bR N n Φy.length j (sojZ (N - n)) := by
    refine length_cjLeaves2bD_le fun Sl hSl ab hab => ?_
    unfold choiceLeavesD
    rw [List.length_map]
    exact (length_leavesOfD_le _ _).trans (Nat.add_le_add_right
      (sojSz_le (F := (N, fys, ey)) hOch rfl hFyv hFyi hΦyl Hy' hSl hab) 1)
  -- the alignment
  have halign : ∀ g ∈ iso (w.denote N) 1 (GensData.denote N gs) (xy.1.denote N) (xy.2.denote N),
      ∃ Y ∈ Ys, ∃ h : g ∈ GensData.denote N gs,
        baseHom _ n hG ⟨g, h⟩ • (cjohnOps (N - n)).dec X₀c = (cjohnOps (N - n)).dec Y := by
    intro g hg
    obtain ⟨hgG, hP, hΦσ⟩ := hconj g hg
    obtain ⟨Y, hY, hYe⟩ := cj2b_reach hOch hFxv hFyv hFxi hFyi hΦxl hΦyl Hx' Hy' _ hP hΦσ
      hfirst h2
    exact ⟨Y, hY, hgG, hYe⟩
  -- the colour bound
  have hq' : ∀ c, 2 * (Finset.univ.filter fun γ =>
      γ ∉ (Align.jdec (N - n) X₀c.1).V0 ∧ cjcol (N - n) X₀c γ = c).card ≤ N - n :=
    fun c => cj2b_hq hOch hFxv hFxi hΦxn hΦxl hΦx2 Hx' hS₀ h01 hX₀mem h2 c
  have hspec : (cjohnOps (N - n)).Spec fun e => CJValid (N - n) e ∧ JBound (leafB (N - n)) e.1 :=
    cp2_spec_mono (cjohnOps_spec (N - n)) fun _ h => h.1
  obtain ⟨ans, ch, hrun, hok, hg, hch⟩ := RunsWithin.alignRd_cj_ns (τ := cjTy)
    (st := ((2 : ℕ), X₀c)) hOa hPa hO hPre hI hG halt B hGG₀ le_rfl hspec
    (gensP := fun e => Main.cjohnGensProg (N - n) e)
    (fun e he => RunsWithin.cjohnGensProg hmL e he.2)
    (isoP := fun e e' => Main.cjohnIsoProg (N - n) e e')
    (fun e e' he he' => RunsWithin.cjohnIsoProg hmL e e' he.2 he'.2) hXv hYv halign hBgP hBmem
    hBkA hBlA (hBg1 X₀ hfirst ⟨hXv.1, t, hJt⟩) hsub hB hs
    ((Nat.mul_le_mul_right _ (hYlen.trans (le_of_eq (by rw [hjy])))).trans hLY)
    (hD X₀ hfirst ⟨hXv.1, t, hJt⟩) hLg rfl hXv.1 hJt (fun _ h => h) hq' hm5
    (hu X₀ hfirst ⟨hXv.1, t, hJt⟩)
  refine ⟨X₀, hfirst, h2, ans, ch, ?_, hok, hg, hch.mono_factor (Nat.mul_le_mul_right _ hYlen)⟩
  apply RunsWithin.mono
  case h =>
    unfold Main.c2bCJProg
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step hdx
    run_step hdy
    run_step (RunsWithin.prim _ _)
    run_with Sims.RunsWithin.ite_pos (show (degD X.O N n (N, fxs, ex) Φx ==
      degD X.O N n (N, fys, ey) Φy) = true by simp [hdeg]) _
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step hfl
    run_with RunsWithin.caseOption_some _
    run_step hft
    run_step hq
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step hYrun
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact hrun
  case hc =>
    have hal' := cp2_alignCost_mono (n := n) (N := N) (g := gs.length)
      (k := (cjohnGensD (N - n) X₀c).length) (cG := cjohnGensCost (leafB (N - n)))
      (cI := cjohnIsoCost (leafB (N - n))) (BgP := BgP) (Bmem := Bmem) (Bk := BkA) (Bl := BlA)
      (Bg1 := Bg1) (Bgen := Bgen)
      (Cb := w.1.length * rdOrbitWork N n w.1.length s sIn (max (N - n) uB.factorial) Bd Blift
        Bgen Bo 0 + dynSeqCost N w.1.length Bo + 5) (s := sIn) hYlen
    have hgk : ((cjohnOps (N - n)).gens X₀c).length = (cjohnGensD (N - n) X₀c).length := rfl
    simp only [Prim.cost, c2bCJCost, ← hX₀c, hgk] at hal' ⊢
    clear_value X₀c Ys j
    clear * - hal'
    omega

/-- `RunsWithin.c2bCJProg_jp` with the Johnson-route hypotheses stated without the pair's
facts. -/
theorem RunsWithin.c2bCJProg (hOc : MeetsContractOn DV Case2b.c2bOps X.O)
    (hPc : ∀ op x, Case2b.c2bOps op → GroupPre DV op x → X.Pre op x)
    (hO : MeetsContractOn DV rdOps X.O)
    (hPre : ∀ op x, rdOps op → GroupPre DV op x → X.Pre op x)
    (hI : HInstValid DV (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D))
    {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N sIn G₀)
    (hGG₀ : GensData.denote N gs ≤ G₀)
    {sm : ℕ → ℕ} (Bm : ∀ M, BackendBounds X DV M (sm M) ⊤)
    (hG : IsInvariant (GensData.denote N gs) (baseSet n N))
    (halt : alternatingGroup (Fin (N - n)) ≤ (baseHom _ n hG).range)
    {Fmap : (Fin N → ℕ) → Subgroup (Perm (Fin N))}
    (hloc : ∀ x x', (∀ u ∈ w.denote N, x u = x' u) → Fmap x = Fmap x')
    (heq : ∀ g ∈ GensData.denote N gs, ∀ x,
      Fmap (relabel g x) = (Fmap x).map (MulAut.conj g).toMonoidHom)
    {fxs fys : GensData} {ex ey : D.denote} (hFxv : GroupValid DV N fxs ex)
    (hFyv : GroupValid DV N fys ey) (hFxs : fxs.length ≤ sIn) (hFys : fys.length ≤ sIn)
    (hFx₀ : GensData.denote N fxs ≤ G₀) (hFy₀ : GensData.denote N fys ≤ G₀)
    (hFxe : GensData.denote N fxs = Fmap (xy.1.denote N))
    (hFye : GensData.denote N fys = Fmap (xy.2.denote N))
    (hFxi : IsInvariant (GensData.denote N fxs) (baseSet n N))
    (hFyi : IsInvariant (GensData.denote N fys) (baseSet n N))
    {Φx Φy : List ℕ} (hΦxn : Φx.Nodup) (hΦxl : ∀ i ∈ Φx, i < N - n)
    (hΦx2 : N - n < 2 * Φx.length)
    (hΦxo : ∃ γ : Fin (N - n), γ.val ∈ Φx ∧ ∀ δ : Fin (N - n),
      δ.val ∈ Φx ↔ δ ∈ MulAction.orbit (baseHom _ n hFxi).range γ)
    (hΦyn : Φy.Nodup) (hΦyl : ∀ i ∈ Φy, i < N - n) (hΦy2 : N - n < 2 * Φy.length)
    (hΦyo : ∃ γ : Fin (N - n), γ.val ∈ Φy ∧ ∀ δ : Fin (N - n),
      δ.val ∈ Φy ↔ δ ∈ MulAction.orbit (baseHom _ n hFyi).range γ)
    (hngx : ¬ Case2b.TupTrans (baseHom _ n hFxi).range (SoJProg.setOf (N - n) Φx) (Φx.length - 2))
    (hngy : ¬ Case2b.TupTrans (baseHom _ n hFyi).range (SoJProg.setOf (N - n) Φy) (Φy.length - 2))
    (hJ : c2bJD X.O N n (N, fxs, ex) Φx = true)
    {Bg BgP Bmem BkA BlA Bg1 uB : ℕ}
    (hBg : ∀ M ≤ N - n, ∀ gs' : GensData, GensData.AllValid M gs' → gs'.length ≤ sIn →
      X.B.call GroupOp.generate (M, gs') (X.O.run GroupOp.generate (M, gs')) ≤ Bg)
    (hBgP : X.B.call GroupOp.generate (N - n, gs.map (baseD n N))
      (X.O.run GroupOp.generate (N - n, gs.map (baseD n N))) ≤ BgP)
    (hBmem : ∀ g : PermData, g.Valid (N - n) → X.B.call GroupOp.mem (pModel X.O n (N, gs, d), g)
      (X.O.run GroupOp.mem (pModel X.O n (N, gs, d), g)) ≤ Bmem)
    (hBkA : X.B.call GroupOp.kernel ((N, gs, d), baseWin n N) (kerModel X.O n (N, gs, d)) ≤ BkA)
    (hBlA : ∀ π : PermData, X.B.call GroupOp.lift ((N, gs, d), (baseWin n N, π))
      (liftModel X.O n (N, gs, d) π) ≤ BlA)
    (hBg1 : ∀ X₀ : OutD, m5Leaf2b X.O N n (N, fxs, ex) Φx = some X₀ →
      X.B.call GroupOp.generate
        (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (cjohnGensD (N - n) (cjFirst2bD N n Φx (degD X.O N n (N, fxs, ex) Φx - 1) X₀)))).map
          (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
        (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (cjohnGensD (N - n) (cjFirst2bD N n Φx (degD X.O N n (N, fxs, ex) Φx - 1) X₀))))) ≤
        Bg1)
    (hsub : HSubSolves X body DV sub
      (fun J => SizeChild sIn (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D)
        J ∧ StepChild w.1.length (N - n) (J.winSize, J.baseOpt)) C s)
    (hB : RDBounds X DV n N sIn Lg Blift Bgen Bo Bk Bcr) (hs : s ≤ sIn)
    (hLY : c2bR N n Φy.length (degD X.O N n (N, fys, ey) Φy - 1) (sojZ (N - n)) * (sIn + 1) ≤
      Lg)
    (hLg : max (N - n) uB.factorial * (sIn + 1) ≤ Lg) (hm5 : 5 ≤ N - n)
    (hD : ∀ X₀, m5Leaf2b X.O N n (N, fxs, ex) Φx = some X₀ → ∀ gs' d' O', RDSet DV n N gs w L
      (Giant.g1Model X.O n (N, gs, d) (cjohnOps (N - n))
        (cjFirst2bD N n Φx (degD X.O N n (N, fxs, ex) Φx - 1) X₀)).2.1 sIn gs' d' O' →
      RDOrbit X body DV n N w L (2, cjFirst2bD N n Φx (degD X.O N n (N, fxs, ex) Φx - 1) X₀) sIn
        Bd gs' d' O')
    (hu : ∀ X₀, m5Leaf2b X.O N n (N, fxs, ex) Φx = some X₀ → ∀ gs' d' O', RDSet DV n N gs w L
      (Giant.g1Model X.O n (N, gs, d) (cjohnOps (N - n))
        (cjFirst2bD N n Φx (degD X.O N n (N, fxs, ex) Φx - 1) X₀)).2.1 sIn gs' d' O' →
      ((labJUD X₀.2.2.2.1.length (markArr (N - n) X₀.2.2.1) X₀.2.2.2.2.2 L O').getD
        (O'.headD 0) []).length ≤ uB) :
    ∃ X₀ : OutD, m5Leaf2b X.O N n (N, fxs, ex) Φx = some X₀ ∧ X₀.1 = 2 ∧
      ∃ (ans : AnswerData D) (ch : List (ℕ × Option ℕ)),
        RunsWithin X body
          (Main.c2bCJProg sub n₀ n L xy w (N, gs, d) (N, fxs, ex) (N, fys, ey) Φx Φy) ans
          ((ch.map fun x => C x.1 x.2).sum +
            c2bCJCost n N sIn gs.length Φx.length Φy.length
              (degD X.O N n (N, fxs, ex) Φx - 1)
              (cjohnGensD (N - n) (cjFirst2bD N n Φx (degD X.O N n (N, fxs, ex) Φx - 1) X₀)).length
              B.Bstab Bg (sojZ (N - n)) BgP Bmem BkA BlA Bg1 Bgen
              (w.1.length * rdOrbitWork N n w.1.length s sIn (max (N - n) uB.factorial) Bd Blift
                Bgen Bo 0 + dynSeqCost N w.1.length Bo + 5)
              (fun M => (Bm M).Borb) (fun M => (Bm M).Bstab) (fun M => (Bm M).Btr)) ∧
        AnsOK DV N (w.denote N) 1 (GensData.denote N gs) (xy.1.denote N) (xy.2.denote N) ans ∧
        (∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sIn) ∧
        ChildList w.1.length
          (c2bR N n Φy.length (degD X.O N n (N, fxs, ex) Φx - 1) (sojZ (N - n)) *
            max (N - n) uB.factorial) (StepChild w.1.length (N - n)) ch := by
  apply RunsWithin.c2bCJProg_jp (hBg1 := fun X₀ h _ => hBg1 X₀ h) (hD := fun X₀ h _ => hD X₀ h)
    (hu := fun X₀ h _ => hu X₀ h)
  all_goals assumption

end JohnsonRoute

/-! ### The variant -/

section Variant

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}
  {sub : HInstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)}
  {C : ℕ → Option ℕ → ℕ} {s : ℕ} {xy : StrData × StrData} {w : WinData}
  {N : ℕ} {gs : GensData} {d : D.denote} {n₀ n : ℕ} {L : LabelData} {st : ℕ × CJData}
  {sIn Lg F Blift Bgen Bo Bk Bcr Bd W6 : ℕ}

/-- **Case 2b of M5 with coloured Johnson alignment.** Under the hypotheses of 14j-4's
`RunsWithin.m5Case2bProg` (for a partition leaf, with factor `F` and stuck work `W6`) and of
`RunsWithin.c2bCJProg` (for a Johnson leaf): the answer is correct for `G` on `W`. The cost is
the test's plus the branch's: `c2bCJCost` (no stuck work) when `c2bJD` holds, else 14j-4's
`c2bCost`. The children are `StepChild |W| m` with factor `c2bR · max(m, uB!)` when `c2bJD`
holds, else `c2bR · F`.

Each route's hypotheses carry the premise under which the route uses them (stage 14j-5c,
`PLAN-14.md` §14.8 item 4): the partition route's charge `hBg1` a first leaf that is not a
Johnson leaf (`X₀.1 ≠ 2`); the Johnson route's `hBg1'`, `hD'` and `hu` a Johnson first leaf
(`X₀.1 = 2`) and the facts `CJFacts` of its coloured pair, which `RunsWithin.c2bCJProg_jp`
establishes. `RunsWithin.m5Case2bCJProg` states them for every first leaf and follows from this
one. -/
theorem RunsWithin.m5Case2bCJProg_jp (hOc : MeetsContractOn DV Case2b.c2bOps X.O)
    (hPc : ∀ op x, Case2b.c2bOps op → GroupPre DV op x → X.Pre op x)
    (hO : MeetsContractOn DV rdOps X.O)
    (hPre : ∀ op x, rdOps op → GroupPre DV op x → X.Pre op x)
    (hI : HInstValid DV (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D))
    {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N sIn G₀)
    (hGG₀ : GensData.denote N gs ≤ G₀)
    {sm : ℕ → ℕ} (Bm : ∀ M, BackendBounds X DV M (sm M) ⊤)
    (hG : IsInvariant (GensData.denote N gs) (baseSet n N))
    (halt : alternatingGroup (Fin (N - n)) ≤ (baseHom _ n hG).range)
    {Fmap : (Fin N → ℕ) → Subgroup (Perm (Fin N))}
    (hloc : ∀ x x', (∀ u ∈ w.denote N, x u = x' u) → Fmap x = Fmap x')
    (heq : ∀ g ∈ GensData.denote N gs, ∀ x,
      Fmap (relabel g x) = (Fmap x).map (MulAut.conj g).toMonoidHom)
    {fxs fys : GensData} {ex ey : D.denote} (hFxv : GroupValid DV N fxs ex)
    (hFyv : GroupValid DV N fys ey) (hFxs : fxs.length ≤ sIn) (hFys : fys.length ≤ sIn)
    (hFx₀ : GensData.denote N fxs ≤ G₀) (hFy₀ : GensData.denote N fys ≤ G₀)
    (hFxe : GensData.denote N fxs = Fmap (xy.1.denote N))
    (hFye : GensData.denote N fys = Fmap (xy.2.denote N))
    (hFxi : IsInvariant (GensData.denote N fxs) (baseSet n N))
    (hFyi : IsInvariant (GensData.denote N fys) (baseSet n N))
    {Φx Φy : List ℕ} (hΦxn : Φx.Nodup) (hΦxl : ∀ i ∈ Φx, i < N - n)
    (hΦx2 : N - n < 2 * Φx.length)
    (hΦxo : ∃ γ : Fin (N - n), γ.val ∈ Φx ∧ ∀ δ : Fin (N - n),
      δ.val ∈ Φx ↔ δ ∈ MulAction.orbit (baseHom _ n hFxi).range γ)
    (hΦyn : Φy.Nodup) (hΦyl : ∀ i ∈ Φy, i < N - n) (hΦy2 : N - n < 2 * Φy.length)
    (hΦyo : ∃ γ : Fin (N - n), γ.val ∈ Φy ∧ ∀ δ : Fin (N - n),
      δ.val ∈ Φy ↔ δ ∈ MulAction.orbit (baseHom _ n hFyi).range γ)
    (hngx : ¬ Case2b.TupTrans (baseHom _ n hFxi).range (SoJProg.setOf (N - n) Φx) (Φx.length - 2))
    (hngy : ¬ Case2b.TupTrans (baseHom _ n hFyi).range (SoJProg.setOf (N - n) Φy) (Φy.length - 2))
    {Bg BgP Bmem BkA BlA Bg1 Bg1' Bgen' uB : ℕ}
    (hBg : ∀ M ≤ N - n, ∀ gs' : GensData, GensData.AllValid M gs' → gs'.length ≤ sIn →
      X.B.call GroupOp.generate (M, gs') (X.O.run GroupOp.generate (M, gs')) ≤ Bg)
    (hBgP : X.B.call GroupOp.generate (N - n, gs.map (baseD n N))
      (X.O.run GroupOp.generate (N - n, gs.map (baseD n N))) ≤ BgP)
    (hBmem : ∀ g : PermData, g.Valid (N - n) → X.B.call GroupOp.mem (pModel X.O n (N, gs, d), g)
      (X.O.run GroupOp.mem (pModel X.O n (N, gs, d), g)) ≤ Bmem)
    (hBkA : X.B.call GroupOp.kernel ((N, gs, d), baseWin n N) (kerModel X.O n (N, gs, d)) ≤ BkA)
    (hBlA : ∀ π : PermData, X.B.call GroupOp.lift ((N, gs, d), (baseWin n N, π))
      (liftModel X.O n (N, gs, d) π) ≤ BlA)
    -- the partition route (14j-4)
    (hBg1 : ∀ X₀ : SoJTree.OutD, m5Leaf2b X.O N n (N, fxs, ex) Φx = some X₀ → X₀.1 ≠ 2 →
      X.B.call GroupOp.generate
        (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (Case2b.outGensD (N - n) X₀))).map
          (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
        (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (Case2b.outGensD (N - n) X₀)))) ≤ Bg1)
    (hBgen : ∀ gs' : GensData, GensData.AllValid N gs' →
      gs'.length ≤ Case2b.c2bR N n Φy.length (Case2b.degD X.O N n (N, fys, ey) Φy - 1)
        (Case2b.sojZ (N - n)) * (sIn + 1) →
      GensData.denote N gs' ≤ GensData.denote N gs →
      X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ Bgen')
    (hsub : HSubSolves X body DV sub
      (fun J => SizeChild sIn (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D)
        J ∧ StepChild w.1.length (N - n) (J.winSize, J.baseOpt)) C s)
    (hB : RDBounds X DV n N sIn Lg Blift Bgen Bo Bk Bcr) (hs : s ≤ sIn)
    (hLg : F * (sIn + 1) ≤ Lg) (hF1 : 1 ≤ F) (hFm : N - n ≤ F)
    (hD : ∀ X₀, m5Leaf2b X.O N n (N, fxs, ex) Φx = some X₀ → X₀.1 ≠ 2 → ∀ gs' d' O',
      RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (Case2b.outOps (N - n)) X₀).2.1 sIn gs' d' O' →
      RDOrbit X body DV n N w L st sIn Bd gs' d' O')
    (h5 : ∀ X₀, m5Leaf2b X.O N n (N, fxs, ex) Φx = some X₀ → X₀.1 ≠ 2 →
      (N - n).factorial ≤ F ∨ ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (Case2b.outOps (N - n)) X₀).2.1 sIn gs' d' O' →
      (deriveModel X.O n N (N, gs', d') O' L st).1 = 5 →
        (deriveModel X.O n N (N, gs', d') O' L st).2.1.2.2.length ≤ F)
    (h6 : ∀ X₀, m5Leaf2b X.O N n (N, fxs, ex) Φx = some X₀ → X₀.1 ≠ 2 →
      (∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (Case2b.outOps (N - n)) X₀).2.1 sIn gs' d' O' →
        (deriveModel X.O n N (N, gs', d') O' L st).1 ≠ 6) ∨
      ((N - n).factorial ≤ F ∧ rd6Cost N n w.1.length s sIn Bk Bo Bcr Bgen ≤ W6))
    -- the Johnson route
    (hBg1' : ∀ X₀ : OutD, m5Leaf2b X.O N n (N, fxs, ex) Φx = some X₀ → X₀.1 = 2 →
      CJFacts (N - n) (cjFirst2bD N n Φx (degD X.O N n (N, fxs, ex) Φx - 1) X₀) →
      X.B.call GroupOp.generate
        (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (cjohnGensD (N - n) (cjFirst2bD N n Φx (degD X.O N n (N, fxs, ex) Φx - 1) X₀)))).map
          (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
        (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (cjohnGensD (N - n) (cjFirst2bD N n Φx (degD X.O N n (N, fxs, ex) Φx - 1) X₀))))) ≤
        Bg1')
    (hLY : c2bR N n Φy.length (degD X.O N n (N, fys, ey) Φy - 1) (sojZ (N - n)) * (sIn + 1) ≤
      Lg)
    (hLg' : max (N - n) uB.factorial * (sIn + 1) ≤ Lg) (hm5 : 5 ≤ N - n)
    (hD' : ∀ X₀, m5Leaf2b X.O N n (N, fxs, ex) Φx = some X₀ → X₀.1 = 2 →
      CJFacts (N - n) (cjFirst2bD N n Φx (degD X.O N n (N, fxs, ex) Φx - 1) X₀) → ∀ gs' d' O',
      RDSet DV n N gs w L
      (Giant.g1Model X.O n (N, gs, d) (cjohnOps (N - n))
        (cjFirst2bD N n Φx (degD X.O N n (N, fxs, ex) Φx - 1) X₀)).2.1 sIn gs' d' O' →
      RDOrbit X body DV n N w L (2, cjFirst2bD N n Φx (degD X.O N n (N, fxs, ex) Φx - 1) X₀) sIn
        Bd gs' d' O')
    (hu : ∀ X₀, m5Leaf2b X.O N n (N, fxs, ex) Φx = some X₀ → X₀.1 = 2 →
      CJFacts (N - n) (cjFirst2bD N n Φx (degD X.O N n (N, fxs, ex) Φx - 1) X₀) → ∀ gs' d' O',
      RDSet DV n N gs w L
      (Giant.g1Model X.O n (N, gs, d) (cjohnOps (N - n))
        (cjFirst2bD N n Φx (degD X.O N n (N, fxs, ex) Φx - 1) X₀)).2.1 sIn gs' d' O' →
      ((labJUD X₀.2.2.2.1.length (markArr (N - n) X₀.2.2.1) X₀.2.2.2.2.2 L O').getD
        (O'.headD 0) []).length ≤ uB) :
    ∃ X₀ : SoJTree.OutD, m5Leaf2b X.O N n (N, fxs, ex) Φx = some X₀ ∧
      ∃ (ans : AnswerData D) (ch : List (ℕ × Option ℕ)),
        RunsWithin X body
          (Main.m5Case2bCJProg sub n₀ n L st xy w (N, gs, d) (N, fxs, ex) (N, fys, ey) Φx Φy) ans
          ((ch.map fun x => C x.1 x.2).sum +
            (c2bJTestCost N n sIn Φx.length (degD X.O N n (N, fxs, ex) Φx - 1) B.Bstab
              Bg (sojZ (N - n)) (fun M => (Bm M).Borb) (fun M => (Bm M).Bstab)
              (fun M => (Bm M).Btr) + 1 +
            if c2bJD X.O N n (N, fxs, ex) Φx then
              c2bCJCost n N sIn gs.length Φx.length Φy.length (degD X.O N n (N, fxs, ex) Φx - 1)
                (cjohnGensD (N - n)
                  (cjFirst2bD N n Φx (degD X.O N n (N, fxs, ex) Φx - 1) X₀)).length
                B.Bstab Bg (sojZ (N - n)) BgP Bmem BkA BlA Bg1' Bgen
                (w.1.length * rdOrbitWork N n w.1.length s sIn (max (N - n) uB.factorial) Bd
                  Blift Bgen Bo 0 + dynSeqCost N w.1.length Bo + 5)
                (fun M => (Bm M).Borb) (fun M => (Bm M).Bstab) (fun M => (Bm M).Btr)
            else
              Case2b.c2bCost n N sIn gs.length Φx.length Φy.length
                (Case2b.degD X.O N n (N, fxs, ex) Φx - 1) (Case2b.outGensD (N - n) X₀).length
                B.Bstab Bg (Case2b.sojZ (N - n)) BgP Bmem BkA BlA Bg1 Bgen'
                (w.1.length * rdOrbitWork N n w.1.length s sIn F Bd Blift Bgen Bo W6 +
                  dynSeqCost N w.1.length Bo + 5)
                (fun M => (Bm M).Borb) (fun M => (Bm M).Bstab) (fun M => (Bm M).Btr))) ∧
        AnsOK DV N (w.denote N) 1 (GensData.denote N gs) (xy.1.denote N) (xy.2.denote N) ans ∧
        (∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sIn) ∧
        ChildList w.1.length
          (if c2bJD X.O N n (N, fxs, ex) Φx then
            c2bR N n Φy.length (degD X.O N n (N, fxs, ex) Φx - 1) (sojZ (N - n)) *
              max (N - n) uB.factorial
          else
            Case2b.c2bR N n Φy.length (Case2b.degD X.O N n (N, fxs, ex) Φx - 1)
              (Case2b.sojZ (N - n)) * F) (StepChild w.1.length (N - n)) ch := by
  classical
  have hOd : MeetsContractOn DV degOps X.O := fun op x h hp => hOc op x (Or.inl h) hp
  have hPd : ∀ op x, degOps op → GroupPre DV op x → X.Pre op x := fun op x h hp =>
    hPc op x (Or.inl h) hp
  have hOch := cp2_choiceOps_of_deg hOd
  have ⟨γx, _, hγx⟩ := hΦxo
  have ⟨γy, _, hγy⟩ := hΦyo
  have hΦx := cp2_inv_of_orbit hFxi hΦxl ⟨γx, hγx⟩
  have hΦy := cp2_inv_of_orbit hFyi hΦyl ⟨γy, hγy⟩
  obtain ⟨h1x, Hx⟩ := case2bHyp_degD hOd hPd B hFxv hFxs hFx₀ hFxi hΦxn hΦxl hΦx (Bm _)
    ⟨γx, hγx⟩ hngx
  have Hx' : Case2bHyp (baseHom _ n hFxi).range (SoJProg.setOf (N - n) Φx)
      (degD X.O N n (N, fxs, ex) Φx - 1 + 1) := by
    rw [Nat.sub_add_cancel h1x]
    exact Hx
  have hjx : degD X.O N n (N, fxs, ex) Φx - 1 + 2 ≤ Φx.length := by
    have := Hx'.size
    rw [card_setOf hΦxn hΦxl] at this
    omega
  have htest := RunsWithin.c2bJTestProg (body := body) hOc hPc B Bm hFxv hFxs hFx₀
    hΦxn hΦxl hΦx hjx hBg (Z := sojZ (N - n))
    (fun Sl hSl ab hab => sojSz_le (F := (N, fxs, ex)) hOch rfl hFxv hFxi hΦxl Hx' hSl hab)
  by_cases hJ : c2bJD X.O N n (N, fxs, ex) Φx = true
  · obtain ⟨X₀, hX₀, -, ans, ch, hrun, hok, hg, hch⟩ := RunsWithin.c2bCJProg_jp (body := body)
      hOc hPc hO hPre hI B hGG₀ Bm hG halt hloc heq hFxv hFyv hFxs hFys hFx₀ hFy₀ hFxe hFye
      hFxi hFyi hΦxn hΦxl hΦx2 hΦxo hΦyn hΦyl hΦy2 hΦyo hngx hngy hJ hBg hBgP hBmem hBkA hBlA
      (fun X₀ h => hBg1' X₀ h (c2bJD_tag hJ h)) hsub hB hs hLY hLg' hm5
      (fun X₀ h => hD' X₀ h (c2bJD_tag hJ h)) (fun X₀ h => hu X₀ h (c2bJD_tag hJ h))
    refine ⟨X₀, hX₀, ans, ch, ?_, hok, hg, by rw [Recursion.if_pos' hJ]; exact hch⟩
    apply RunsWithin.mono
    case h =>
      unfold Main.m5Case2bCJProg
      run_step htest
      run_with Sims.RunsWithin.ite_pos hJ _
      exact hrun
    case hc =>
      rw [Recursion.if_pos' hJ]
      omega
  · have hJf : c2bJD X.O N n (N, fxs, ex) Φx = false := by simpa using hJ
    obtain ⟨X₀, hX₀, ans, ch, hrun, hok, hg, hch⟩ := RunsWithin.m5Case2bProg (body := body)
      hOc hPc hO hPre hI B hGG₀ Bm hG halt hloc heq hFxv hFyv hFxs hFys hFx₀ hFy₀ hFxe hFye hFxi
      hFyi hΦxn hΦxl hΦx2 hΦxo hΦyn hΦyl hΦy2 hΦyo hngx hngy hBg hBgP hBmem hBkA hBlA
      (fun X₀ hX₀ => hBg1 X₀ hX₀ (c2bJD_false hJf hX₀)) hBgen hsub hB hs hLg hF1 hFm
      (fun X₀ hX₀ => hD X₀ hX₀ (c2bJD_false hJf hX₀))
      (fun X₀ hX₀ => h5 X₀ hX₀ (c2bJD_false hJf hX₀))
      (fun X₀ hX₀ => h6 X₀ hX₀ (c2bJD_false hJf hX₀))
    refine ⟨X₀, hX₀, ans, ch, ?_, hok, hg, by rw [Recursion.if_neg' hJ]; exact hch⟩
    apply RunsWithin.mono
    case h =>
      unfold Main.m5Case2bCJProg
      run_step htest
      run_with Sims.RunsWithin.ite_neg hJf _
      exact hrun
    case hc =>
      rw [Recursion.if_neg' hJ]
      omega

/-- **Case 2b of M5 with coloured Johnson alignment**, with the Johnson route's hypotheses for
every first leaf: `RunsWithin.m5Case2bCJProg_jp`, whose premise `X₀.1 = 2` is dropped. -/
theorem RunsWithin.m5Case2bCJProg (hOc : MeetsContractOn DV Case2b.c2bOps X.O)
    (hPc : ∀ op x, Case2b.c2bOps op → GroupPre DV op x → X.Pre op x)
    (hO : MeetsContractOn DV rdOps X.O)
    (hPre : ∀ op x, rdOps op → GroupPre DV op x → X.Pre op x)
    (hI : HInstValid DV (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D))
    {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N sIn G₀)
    (hGG₀ : GensData.denote N gs ≤ G₀)
    {sm : ℕ → ℕ} (Bm : ∀ M, BackendBounds X DV M (sm M) ⊤)
    (hG : IsInvariant (GensData.denote N gs) (baseSet n N))
    (halt : alternatingGroup (Fin (N - n)) ≤ (baseHom _ n hG).range)
    {Fmap : (Fin N → ℕ) → Subgroup (Perm (Fin N))}
    (hloc : ∀ x x', (∀ u ∈ w.denote N, x u = x' u) → Fmap x = Fmap x')
    (heq : ∀ g ∈ GensData.denote N gs, ∀ x,
      Fmap (relabel g x) = (Fmap x).map (MulAut.conj g).toMonoidHom)
    {fxs fys : GensData} {ex ey : D.denote} (hFxv : GroupValid DV N fxs ex)
    (hFyv : GroupValid DV N fys ey) (hFxs : fxs.length ≤ sIn) (hFys : fys.length ≤ sIn)
    (hFx₀ : GensData.denote N fxs ≤ G₀) (hFy₀ : GensData.denote N fys ≤ G₀)
    (hFxe : GensData.denote N fxs = Fmap (xy.1.denote N))
    (hFye : GensData.denote N fys = Fmap (xy.2.denote N))
    (hFxi : IsInvariant (GensData.denote N fxs) (baseSet n N))
    (hFyi : IsInvariant (GensData.denote N fys) (baseSet n N))
    {Φx Φy : List ℕ} (hΦxn : Φx.Nodup) (hΦxl : ∀ i ∈ Φx, i < N - n)
    (hΦx2 : N - n < 2 * Φx.length)
    (hΦxo : ∃ γ : Fin (N - n), γ.val ∈ Φx ∧ ∀ δ : Fin (N - n),
      δ.val ∈ Φx ↔ δ ∈ MulAction.orbit (baseHom _ n hFxi).range γ)
    (hΦyn : Φy.Nodup) (hΦyl : ∀ i ∈ Φy, i < N - n) (hΦy2 : N - n < 2 * Φy.length)
    (hΦyo : ∃ γ : Fin (N - n), γ.val ∈ Φy ∧ ∀ δ : Fin (N - n),
      δ.val ∈ Φy ↔ δ ∈ MulAction.orbit (baseHom _ n hFyi).range γ)
    (hngx : ¬ Case2b.TupTrans (baseHom _ n hFxi).range (SoJProg.setOf (N - n) Φx) (Φx.length - 2))
    (hngy : ¬ Case2b.TupTrans (baseHom _ n hFyi).range (SoJProg.setOf (N - n) Φy) (Φy.length - 2))
    {Bg BgP Bmem BkA BlA Bg1 Bg1' Bgen' uB : ℕ}
    (hBg : ∀ M ≤ N - n, ∀ gs' : GensData, GensData.AllValid M gs' → gs'.length ≤ sIn →
      X.B.call GroupOp.generate (M, gs') (X.O.run GroupOp.generate (M, gs')) ≤ Bg)
    (hBgP : X.B.call GroupOp.generate (N - n, gs.map (baseD n N))
      (X.O.run GroupOp.generate (N - n, gs.map (baseD n N))) ≤ BgP)
    (hBmem : ∀ g : PermData, g.Valid (N - n) → X.B.call GroupOp.mem (pModel X.O n (N, gs, d), g)
      (X.O.run GroupOp.mem (pModel X.O n (N, gs, d), g)) ≤ Bmem)
    (hBkA : X.B.call GroupOp.kernel ((N, gs, d), baseWin n N) (kerModel X.O n (N, gs, d)) ≤ BkA)
    (hBlA : ∀ π : PermData, X.B.call GroupOp.lift ((N, gs, d), (baseWin n N, π))
      (liftModel X.O n (N, gs, d) π) ≤ BlA)
    -- the partition route (14j-4)
    (hBg1 : ∀ X₀ : SoJTree.OutD, m5Leaf2b X.O N n (N, fxs, ex) Φx = some X₀ →
      X.B.call GroupOp.generate
        (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (Case2b.outGensD (N - n) X₀))).map
          (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
        (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (Case2b.outGensD (N - n) X₀)))) ≤ Bg1)
    (hBgen : ∀ gs' : GensData, GensData.AllValid N gs' →
      gs'.length ≤ Case2b.c2bR N n Φy.length (Case2b.degD X.O N n (N, fys, ey) Φy - 1)
        (Case2b.sojZ (N - n)) * (sIn + 1) →
      GensData.denote N gs' ≤ GensData.denote N gs →
      X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ Bgen')
    (hsub : HSubSolves X body DV sub
      (fun J => SizeChild sIn (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D)
        J ∧ StepChild w.1.length (N - n) (J.winSize, J.baseOpt)) C s)
    (hB : RDBounds X DV n N sIn Lg Blift Bgen Bo Bk Bcr) (hs : s ≤ sIn)
    (hLg : F * (sIn + 1) ≤ Lg) (hF1 : 1 ≤ F) (hFm : N - n ≤ F)
    (hD : ∀ X₀, m5Leaf2b X.O N n (N, fxs, ex) Φx = some X₀ → X₀.1 ≠ 2 → ∀ gs' d' O',
      RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (Case2b.outOps (N - n)) X₀).2.1 sIn gs' d' O' →
      RDOrbit X body DV n N w L st sIn Bd gs' d' O')
    (h5 : ∀ X₀, m5Leaf2b X.O N n (N, fxs, ex) Φx = some X₀ → X₀.1 ≠ 2 →
      (N - n).factorial ≤ F ∨ ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (Case2b.outOps (N - n)) X₀).2.1 sIn gs' d' O' →
      (deriveModel X.O n N (N, gs', d') O' L st).1 = 5 →
        (deriveModel X.O n N (N, gs', d') O' L st).2.1.2.2.length ≤ F)
    (h6 : ∀ X₀, m5Leaf2b X.O N n (N, fxs, ex) Φx = some X₀ → X₀.1 ≠ 2 →
      (∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (Case2b.outOps (N - n)) X₀).2.1 sIn gs' d' O' →
        (deriveModel X.O n N (N, gs', d') O' L st).1 ≠ 6) ∨
      ((N - n).factorial ≤ F ∧ rd6Cost N n w.1.length s sIn Bk Bo Bcr Bgen ≤ W6))
    -- the Johnson route
    (hBg1' : ∀ X₀ : OutD, m5Leaf2b X.O N n (N, fxs, ex) Φx = some X₀ →
      X.B.call GroupOp.generate
        (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (cjohnGensD (N - n) (cjFirst2bD N n Φx (degD X.O N n (N, fxs, ex) Φx - 1) X₀)))).map
          (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
        (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (cjohnGensD (N - n) (cjFirst2bD N n Φx (degD X.O N n (N, fxs, ex) Φx - 1) X₀))))) ≤
        Bg1')
    (hLY : c2bR N n Φy.length (degD X.O N n (N, fys, ey) Φy - 1) (sojZ (N - n)) * (sIn + 1) ≤
      Lg)
    (hLg' : max (N - n) uB.factorial * (sIn + 1) ≤ Lg) (hm5 : 5 ≤ N - n)
    (hD' : ∀ X₀, m5Leaf2b X.O N n (N, fxs, ex) Φx = some X₀ → ∀ gs' d' O', RDSet DV n N gs w L
      (Giant.g1Model X.O n (N, gs, d) (cjohnOps (N - n))
        (cjFirst2bD N n Φx (degD X.O N n (N, fxs, ex) Φx - 1) X₀)).2.1 sIn gs' d' O' →
      RDOrbit X body DV n N w L (2, cjFirst2bD N n Φx (degD X.O N n (N, fxs, ex) Φx - 1) X₀) sIn
        Bd gs' d' O')
    (hu : ∀ X₀, m5Leaf2b X.O N n (N, fxs, ex) Φx = some X₀ → ∀ gs' d' O', RDSet DV n N gs w L
      (Giant.g1Model X.O n (N, gs, d) (cjohnOps (N - n))
        (cjFirst2bD N n Φx (degD X.O N n (N, fxs, ex) Φx - 1) X₀)).2.1 sIn gs' d' O' →
      ((labJUD X₀.2.2.2.1.length (markArr (N - n) X₀.2.2.1) X₀.2.2.2.2.2 L O').getD
        (O'.headD 0) []).length ≤ uB) :
    ∃ X₀ : SoJTree.OutD, m5Leaf2b X.O N n (N, fxs, ex) Φx = some X₀ ∧
      ∃ (ans : AnswerData D) (ch : List (ℕ × Option ℕ)),
        RunsWithin X body
          (Main.m5Case2bCJProg sub n₀ n L st xy w (N, gs, d) (N, fxs, ex) (N, fys, ey) Φx Φy) ans
          ((ch.map fun x => C x.1 x.2).sum +
            (c2bJTestCost N n sIn Φx.length (degD X.O N n (N, fxs, ex) Φx - 1) B.Bstab
              Bg (sojZ (N - n)) (fun M => (Bm M).Borb) (fun M => (Bm M).Bstab)
              (fun M => (Bm M).Btr) + 1 +
            if c2bJD X.O N n (N, fxs, ex) Φx then
              c2bCJCost n N sIn gs.length Φx.length Φy.length (degD X.O N n (N, fxs, ex) Φx - 1)
                (cjohnGensD (N - n)
                  (cjFirst2bD N n Φx (degD X.O N n (N, fxs, ex) Φx - 1) X₀)).length
                B.Bstab Bg (sojZ (N - n)) BgP Bmem BkA BlA Bg1' Bgen
                (w.1.length * rdOrbitWork N n w.1.length s sIn (max (N - n) uB.factorial) Bd
                  Blift Bgen Bo 0 + dynSeqCost N w.1.length Bo + 5)
                (fun M => (Bm M).Borb) (fun M => (Bm M).Bstab) (fun M => (Bm M).Btr)
            else
              Case2b.c2bCost n N sIn gs.length Φx.length Φy.length
                (Case2b.degD X.O N n (N, fxs, ex) Φx - 1) (Case2b.outGensD (N - n) X₀).length
                B.Bstab Bg (Case2b.sojZ (N - n)) BgP Bmem BkA BlA Bg1 Bgen'
                (w.1.length * rdOrbitWork N n w.1.length s sIn F Bd Blift Bgen Bo W6 +
                  dynSeqCost N w.1.length Bo + 5)
                (fun M => (Bm M).Borb) (fun M => (Bm M).Bstab) (fun M => (Bm M).Btr))) ∧
        AnsOK DV N (w.denote N) 1 (GensData.denote N gs) (xy.1.denote N) (xy.2.denote N) ans ∧
        (∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sIn) ∧
        ChildList w.1.length
          (if c2bJD X.O N n (N, fxs, ex) Φx then
            c2bR N n Φy.length (degD X.O N n (N, fxs, ex) Φx - 1) (sojZ (N - n)) *
              max (N - n) uB.factorial
          else
            Case2b.c2bR N n Φy.length (Case2b.degD X.O N n (N, fxs, ex) Φx - 1)
              (Case2b.sojZ (N - n)) * F) (StepChild w.1.length (N - n)) ch := by
  apply RunsWithin.m5Case2bCJProg_jp (hBg1 := fun X₀ h _ => hBg1 X₀ h)
    (hBg1' := fun X₀ h _ _ => hBg1' X₀ h) (hD' := fun X₀ h _ _ => hD' X₀ h)
    (hu := fun X₀ h _ _ => hu X₀ h)
  all_goals assumption

end Variant

end GraphIso.Main
