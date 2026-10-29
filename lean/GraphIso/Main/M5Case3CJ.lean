module

public import GraphIso.Main.M5Case2bCJ

/-!
# M5, Case 3 with coloured Johnson alignment

Stage 14j-4b, item 3 (`PLAN-14.md` §14.5). Case 3 computes the colourings of the `k`-tuples of
the fixed points once; when `x`'s first structure is a Johnson structure, Align compares it as a
coloured pair (`cjohnOps`, colouring `q3D`: the support, the dominant class of the first good
list, the rest) with `y`'s coloured Johnson structures, and reduce-and-derive runs on the
aligned cosets with `st = (2, X₀)`, so no orbit is stuck. Otherwise (different numbers of fixed
points, twins, no structure, or a partition structure) 14j-4's `m5Case3Prog` runs.

* **The Johnson route** `c3CJRouteProg`, from the colourings and `X₀`: the first good list's
  dominant class (`c3FirstClsProg`), its colouring, `y`'s coloured Johnson structures
  (`cjStructs3Prog`), and Align with `cjohnOps` and `rdBranch` at `st = (2, X₀)`.
  `RunsWithin.c3CJRouteProg`: if the colourings are those of certificate equivalence (stage
  14i's `ColChar`) and `X₀` is `x`'s first structure, a Johnson structure, the answer is correct
  and the children are `StepChild |W| m`, `c3R` copies of one list with factor `max(m, uB!)`: no
  stuck orbit (`alignRd_cj_ns`), with the alignment `cj3_reach` (through `tupleCol_iso`), the
  validity `cj3_valid` and the colour bound `cj3_hq` proved.
* **The variant** `m5Case3CJProg`: no isomorphism if the numbers of fixed points differ;
  otherwise the colourings, the twins flag and the first structure, then the Johnson route or
  `m5Case3Prog`. `RunsWithin.m5Case3CJProg` takes `m5Case3Prog`'s run (14j-4's
  `RunsWithin.m5Case3Prog`, or `RunsWithin.m5Case3Prog_part` for no stuck orbit) as a
  hypothesis, needed only when `x`'s first structure is not a Johnson structure: the answer is
  correct; the comparisons make at most `2 · c3Count` sub-calls on windows of at most `n / k`
  points (the colourings are computed again inside `m5Case3Prog`); the factor is the sum of the
  two routes'.
-/

@[expose] public section

namespace GraphIso.Main

open Equiv Finset Pointwise Cost GraphIso GraphIso.Programs GraphIso.Toolkit GraphIso.SoJProg
  GraphIso.SoJTree GraphIso.Case2b GraphIso.Align GraphIso.Recursion GraphIso.SplitJohnson
  GraphIso.Solver GraphIso.Certificates GraphIso.CertProg

/-! ### The programs -/

section Programs

variable {D : Ty} {rec : Ty × Ty} {var : Ty → Type}

/-- **The dominant class of the first good list** (`c3ClsD … (firstGoodD …)`). -/
def c3FirstClsProg {S : Signature} (k : var .nat) (V : var (.list .nat)) (col : var (.array .nat)) :
    Prog S rec var (.list .nat) :=
  .bind (.op1 .length V) fun m => .bind (.op1 .arrayOfList V) fun VA =>
  .bind (Case3.wlCProg k m col) fun W =>
  .bind (.op1 .range k) fun rk => .bind (.op1 .range m) fun rm =>
  .bind (Coherent.pwTabProg m rk rm) fun pw =>
  .bind (Case3.tOfProg m) fun t =>
  .bind (SoJProg.goodListProg W k m t) fun gl =>
  .bind (.caseList gl (.op0 .nil) fun z _ => .ret z) fun z₀ =>
  c3ClsProg VA W pw rk rm t z₀

/-- **Case 3's Johnson route**, from the colourings `cX`, `cY` and `x`'s first structure `X₀`:
the coloured pair of `X₀`, `y`'s coloured Johnson structures, and Align with `cjohnOps`; on
each aligned coset, reduce-and-derive with `st = (2, X₀)`. -/
def c3CJRouteProg (sub : var (hinstTy D) → Prog (groupSig D) rec var (Ty.answer D))
    (n₀ n : var .nat) (L : var (.array (.list .nat))) (k : var .nat) (xy : var Ty.strs)
    (w : var Ty.win) (G : var (Ty.group D)) (Vx Vy : var (.list .nat))
    (cX cY : var (.array .nat)) (X₀ : var outTy) : Prog (groupSig D) rec var (Ty.answer D) :=
  .bind (.op1 .fst G) fun N => .bind (.op2 .sub N n) fun M =>
  .bind (c3FirstClsProg k Vx cX) fun Cx => .bind (q3Prog M Vx Cx) fun qx =>
  .bind (.op1 .snd X₀) fun r => .bind (.op1 .snd r) fun jd =>
  .bind (.op2 .pair jd qx) fun X₀c =>
  .bind (cjStructs3Prog M k Vy cY) fun Ys =>
  .bind (.op0 (.natLit 2)) fun two => .bind (.op2 .pair two X₀c) fun st' =>
  Align.alignProg (fun J => Main.rdBranch sub n₀ n L st' J) (fun e => cjohnGensProg M e)
    (fun e e' => cjohnIsoProg M e e') n xy w G X₀c Ys

/-- **Case 3 of M5 with coloured Johnson alignment**: no isomorphism if the numbers of fixed
points differ; otherwise the colourings, the twins flag and the first structure, then the Johnson
route for a Johnson structure and 14j-4's `m5Case3Prog` otherwise. -/
def m5Case3CJProg (sub : var (hinstTy D) → Prog (groupSig D) rec var (Ty.answer D))
    (I : var (hinstTy D)) (n₀ n : var .nat) (L : var (.array (.list .nat))) (st : var stTy)
    (k : var .nat) (xy : var Ty.strs) (w : var Ty.win) (G : var (Ty.group D))
    (Vx Vy : var (.list .nat)) : Prog (groupSig D) rec var (Ty.answer D) :=
  .bind (.op1 .fst w) fun pts => .bind (.op1 .length pts) fun wl =>
  .bind (.op1 .fst G) fun N => .bind (.op2 .sub N n) fun M =>
  .bind (.op1 .length Vx) fun mx => .bind (.op1 .length Vy) fun my =>
  .bind (.op2 .natEq mx my) fun same =>
  .ite same
    (.bind (.op1 .fst xy) fun x => .bind (.op1 .snd xy) fun y =>
      .bind (Case3.tupleColProg (fun J => c3Sub sub n₀ n L st wl J) n N k Vx Vy x y G) fun cc =>
      .bind (.op1 .fst cc) fun cX => .bind (.op1 .snd cc) fun cY =>
      .bind (Case3.twinsFlagProg k mx cX) fun tw =>
      .ite tw (m5Case3Prog sub I n₀ n L st k xy w G Vx Vy)
        (.bind (Case3.firstStructProg M k Vx cX) fun ox =>
          .caseOption ox (m5Case3Prog sub I n₀ n L st k xy w G Vx Vy) fun X₀ =>
          .bind (.op1 .fst X₀) fun tag => .bind (.op0 (.natLit 2)) fun two =>
          .bind (.op2 .natEq tag two) fun isJ =>
          .ite isJ (c3CJRouteProg sub n₀ n L k xy w G Vx Vy cX cY X₀)
            (m5Case3Prog sub I n₀ n L st k xy w G Vx Vy)))
    (.op0 .none)

end Programs

/-! ### The pieces -/

section Pieces

open GraphIso.Case3 GraphIso.Coherent

variable {S : Signature} {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

/-- The cost of `c3FirstClsProg` on `m` points. -/
def c3FirstClsCost (k m : ℕ) : ℕ := pipePrefixCost k m + 2 + c3ClsCost k m k

theorem length_firstGoodD_le (k : ℕ) (V : List ℕ) (col : Array ℕ) :
    (firstGoodD k V col).length ≤ k := by
  unfold firstGoodD
  rcases hg : goodListsD k V.length (wlCD k V.length col) with _ | ⟨z, zs⟩
  · simp
  · have hz : z ∈ goodListsD k V.length (wlCD k V.length col) := by
      rw [hg]
      exact List.mem_cons_self
    obtain ⟨x, hx, rfl, -⟩ := mem_goodListsD.1 hz
    simp only [List.headD_cons, List.length_map]
    omega

theorem RunsWithin.c3FirstClsProg (k : ℕ) (V : List ℕ) (col : Array ℕ) :
    RunsWithin X body (Main.c3FirstClsProg k V col)
      (c3ClsD k V (wlCD k V.length col) (firstGoodD k V col)) (c3FirstClsCost k V.length) := by
  have hz : RunsWithin X body
      (Prog.caseList (a := .list .nat) (goodListsD k V.length (wlCD k V.length col))
        (Prog.op0 .nil) fun z _ => Prog.ret z) (firstGoodD k V col) 2 := by
    unfold firstGoodD
    rcases hg : goodListsD k V.length (wlCD k V.length col) with _ | ⟨z, zs⟩
    · apply RunsWithin.mono
      case h =>
        run_with Coherent.RunsWithin.caseList_eq_nil rfl _
        exact RunsWithin.prim _ _
      case hc => simp [Prim.cost]
    · apply RunsWithin.mono
      case h =>
        run_with Coherent.RunsWithin.caseList_eq_cons rfl _
        exact RunsWithin.ret _
      case hc => simp
  have hcl := (RunsWithin.c3ClsProg (X := X) (body := body) k V (wlCD k V.length col)
    (firstGoodD k V col)).mono (c3ClsCost_mono (length_firstGoodD_le k V col))
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.wlCProg k _ col)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.pwTabProg k _)
    run_step (RunsWithin.tOfProg _)
    run_step (SoJProg.RunsWithin.goodListProg _ k _ _)
    run_step hz
    exact hcl
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head_cons, c3FirstClsCost, pipePrefixCost]
    omega

/-- `y`'s coloured Johnson structures are at most `c3R`. -/
theorem length_cjStructs3D_le (M k : ℕ) (V : List ℕ) (col : Array ℕ) {Z : ℕ}
    (hZ : ∀ z ∈ goodListsD k V.length (wlCD k V.length col),
      outSzD k V (wlCD k V.length col) z ≤ Z) :
    (cjStructs3D M k V col).length ≤ c3R k V.length Z := by
  refine (le_trans ?_ (length_allStructsD_le M V col hZ))
  unfold cjStructs3D allStructsD
  rw [List.length_flatMap, List.length_flatMap]
  refine List.sum_le_sum fun z _ => ?_
  exact length_flatMap_cjOfD_le _ _

/-- **The colourings' cost by count**: `tupleColCost` is affine in the cost of one comparison,
with `3 · m^k · m^k` comparisons. -/
theorem tupleColCost_add_CI (N k m A CI : ℕ) :
    tupleColCost N k m (A + CI) = tupleColCost N k m CI + 3 * m ^ k * m ^ k * A := by
  unfold tupleColCost entryXCost entryYCost cmpCost firstIdxCost
  ring

theorem tupleColCost_mono_CI {N k m CI CI' : ℕ} (h : CI ≤ CI') :
    tupleColCost N k m CI ≤ tupleColCost N k m CI' := by
  unfold tupleColCost entryXCost entryYCost cmpCost firstIdxCost
  gcongr

/-- The polynomial part of the colourings in Case 3: everything but the comparisons'
sub-calls. -/
def c3ColWork (N n s k mx Bstab Btr Borb Bgen' Borb' Bstab' Bgk Bl Bgs wl : ℕ) : ℕ :=
  tupleColCost N k mx (k.factorial * certIsoPoly N n k s Bstab Btr Borb Bgen' Borb' Bstab' Bgk Bl
    Bgs + n * (k.factorial * (n * (wl + 10))))

/-- **The colourings by count**: `c3Count` sub-calls at cost `A` each, and `c3ColWork`. -/
theorem tupleColCost_split (N n s k mx Bstab Btr Borb Bgen' Borb' Bstab' Bgk Bl Bgs wl A : ℕ) :
    tupleColCost N k mx
        (certIsoCost N n k s Bstab Btr Borb Bgen' Borb' Bstab' Bgk (A + 4 + wl + 6) Bl Bgs) ≤
      c3Count mx k n * A +
        c3ColWork N n s k mx Bstab Btr Borb Bgen' Borb' Bstab' Bgk Bl Bgs wl := by
  refine (tupleColCost_mono_CI (certIsoCost_le _ _ _ _ _ _ _ _ _ _ _ _ _ _)).trans (le_of_eq ?_)
  rw [show k.factorial * certIsoPoly N n k s Bstab Btr Borb Bgen' Borb' Bstab' Bgk Bl Bgs +
      n * (k.factorial * (n * (A + 4 + wl + 6))) = n * (k.factorial * (n * A)) +
      (k.factorial * certIsoPoly N n k s Bstab Btr Borb Bgen' Borb' Bstab' Bgk Bl Bgs +
        n * (k.factorial * (n * (wl + 10)))) by ring, tupleColCost_add_CI, c3Count, c3ColWork]
  ring

end Pieces

/-! ### The Johnson route -/

/-- **The cost of Case 3's Johnson route**: the dominant class and the colouring, `y`'s coloured
structures, and Align with at most `3 m²` stabilizer generators and `c3R` candidates. -/
def c3CJCost (n N s g k mx my Z BgP Bmem Bk Bl Bg1 Bgen Cb : ℕ) : ℕ :=
  1 + 1 + c3FirstClsCost k mx + q3Cost (N - n) mx mx + 1 + 1 + 1 +
    cjStructs3Cost (N - n) k my (Case3.c3OutCost (N - n) k my Z) Z + 1 + 1 +
    alignCost n N g (3 * ((N - n) * (N - n))) (Case3.c3R k my Z) (cjohnGensCost (leafB (N - n)))
      (cjohnIsoCost (leafB (N - n))) BgP Bmem Bk Bl Bg1 Bgen Cb s

section JohnsonRoute

open GraphIso.Case3

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}
  {sub : HInstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)}
  {C : ℕ → Option ℕ → ℕ} {s : ℕ} {xy : StrData × StrData} {w : WinData}
  {N : ℕ} {gs : GensData} {d : D.denote} {n₀ n : ℕ} {L : LabelData}
  {sIn Lg Blift Bgen Bo Bk Bcr Bd : ℕ}

/-- **Case 3's Johnson route.** If `Vx`, `Vy` are the fixed points of `ψ(F(x))`, `ψ(F(y))`
(`F` canonical), with `m ≤ 2|Vx|` (Case 3), the colourings `cXX`, `cXY` are certificate
equivalence (`ColChar`), and `X₀` is `x`'s first structure, a Johnson structure: the answer is
correct for `G` on `W`, and the children are `StepChild |W| m`, `c3R` copies of one list with
factor `max(m, uB!)`. No orbit is stuck (`alignRd_cj_ns`): the coloured pair of `X₀` is
aligned (`cj3_reach`, with `tupleCol_iso` relating the colourings along an isomorphism), valid
(`cj3_valid`), Johnson (`outcomeD_along`) and has small colour classes (`cj3_hq`). Assumed:
the backend's charges, `RDBounds`, the per-orbit `RDOrbit` for `st = (2, X₀)`, and `uB`.

The hypotheses `hBg1`, `hD` and `hu` are needed only with the facts `CJFacts` of the coloured
pair, which the proof establishes (stage 14j-5c, `PLAN-14.md` §14.8 item 4);
`RunsWithin.c3CJRouteProg` states them without. -/
theorem RunsWithin.c3CJRouteProg_jp (hOa : MeetsContractOn DV alignOps X.O)
    (hPa : ∀ op x, alignOps op → GroupPre DV op x → X.Pre op x)
    (hO : MeetsContractOn DV rdOps X.O)
    (hPre : ∀ op x, rdOps op → GroupPre DV op x → X.Pre op x)
    (hI : HInstValid DV (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D))
    {hC : CertSetting (GensData.denote N gs) n} {φ : strGroup hC →* Perm (Fin (N - n))}
    (hφ : IsPhi hC φ)
    (halt : alternatingGroup (Fin (N - n)) ≤ (baseHom _ n hC.base).range)
    (hwS : ∀ u : Fin N, u.val < n → u ∈ w.denote N)
    {Fmap : (Fin N → ℕ) → Subgroup (Perm (Fin N))}
    (hloc : ∀ x x', (∀ u ∈ w.denote N, x u = x' u) → Fmap x = Fmap x')
    (heq : ∀ g ∈ GensData.denote N gs, ∀ x,
      Fmap (relabel g x) = (Fmap x).map (MulAut.conj g).toMonoidHom)
    {Fx Fy : Subgroup (Perm (Fin N))} (hFxe : Fx = Fmap (xy.1.denote N))
    (hFye : Fy = Fmap (xy.2.denote N)) (hFxi : IsInvariant Fx (baseSet n N))
    (hFyi : IsInvariant Fy (baseSet n N))
    {Vx Vy : List ℕ} (hVx : ∀ v ∈ Vx, v < N - n) (hVxn : Vx.Nodup)
    (hVy : ∀ v ∈ Vy, v < N - n) (hVyn : Vy.Nodup)
    (hVxF : ∀ v : Fin (N - n), v.val ∈ Vx ↔ ∀ f ∈ (baseHom Fx n hFxi).range, f v = v)
    (hVyF : ∀ v : Fin (N - n), v.val ∈ Vy ↔ ∀ f ∈ (baseHom Fy n hFyi).range, f v = v)
    (hm : 6 ≤ Vx.length) (hlen : Vx.length = Vy.length) (hVx2 : N - n ≤ 2 * Vx.length) {k : ℕ}
    {cXX cXY cYY : List ℕ → List ℕ → Bool}
    (hXX : ColChar φ (strOn hC.le (xy.1.denote N)) (strOn hC.le (xy.1.denote N)) k Vx.length
      Vx Vx cXX)
    (hXY : ColChar φ (strOn hC.le (xy.1.denote N)) (strOn hC.le (xy.2.denote N)) k Vx.length
      Vx Vy cXY)
    {X₀ : OutD} (hfirst : firstStructD (N - n) k Vx (colXD cXX k Vx.length) = some X₀)
    (h2 : X₀.1 = 2)
    {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N sIn G₀)
    (hGG₀ : GensData.denote N gs ≤ G₀)
    {BgP Bmem BkA BlA Bg1 uB : ℕ}
    (hBgP : X.B.call GroupOp.generate (N - n, gs.map (baseD n N))
      (X.O.run GroupOp.generate (N - n, gs.map (baseD n N))) ≤ BgP)
    (hBmem : ∀ g : PermData, g.Valid (N - n) → X.B.call GroupOp.mem (pModel X.O n (N, gs, d), g)
      (X.O.run GroupOp.mem (pModel X.O n (N, gs, d), g)) ≤ Bmem)
    (hBkA : X.B.call GroupOp.kernel ((N, gs, d), baseWin n N) (kerModel X.O n (N, gs, d)) ≤ BkA)
    (hBlA : ∀ π : PermData, X.B.call GroupOp.lift ((N, gs, d), (baseWin n N, π))
      (liftModel X.O n (N, gs, d) π) ≤ BlA)
    (hBg1 : CJFacts (N - n) (cjFirst3D (N - n) k Vx (colXD cXX k Vx.length) X₀) →
      X.B.call GroupOp.generate
        (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (cjohnGensD (N - n) (cjFirst3D (N - n) k Vx (colXD cXX k Vx.length) X₀)))).map
          (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
        (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (cjohnGensD (N - n) (cjFirst3D (N - n) k Vx (colXD cXX k Vx.length) X₀))))) ≤ Bg1)
    (hsub : HSubSolves X body DV sub
      (fun J => SizeChild sIn (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D)
        J ∧ StepChild w.1.length (N - n) (J.winSize, J.baseOpt)) C s)
    (hB : RDBounds X DV n N sIn Lg Blift Bgen Bo Bk Bcr) (hs : s ≤ sIn)
    (hLY : c3R k Vy.length (sojZ (N - n)) * (sIn + 1) ≤ Lg)
    (hLg : max (N - n) uB.factorial * (sIn + 1) ≤ Lg) (hm5 : 5 ≤ N - n)
    (hD : CJFacts (N - n) (cjFirst3D (N - n) k Vx (colXD cXX k Vx.length) X₀) →
      ∀ gs' d' O', RDSet DV n N gs w L
      (Giant.g1Model X.O n (N, gs, d) (cjohnOps (N - n))
        (cjFirst3D (N - n) k Vx (colXD cXX k Vx.length) X₀)).2.1 sIn gs' d' O' →
      RDOrbit X body DV n N w L (2, cjFirst3D (N - n) k Vx (colXD cXX k Vx.length) X₀) sIn Bd
        gs' d' O')
    (hu : CJFacts (N - n) (cjFirst3D (N - n) k Vx (colXD cXX k Vx.length) X₀) →
      ∀ gs' d' O', RDSet DV n N gs w L
      (Giant.g1Model X.O n (N, gs, d) (cjohnOps (N - n))
        (cjFirst3D (N - n) k Vx (colXD cXX k Vx.length) X₀)).2.1 sIn gs' d' O' →
      ((labJUD X₀.2.2.2.1.length (markArr (N - n) X₀.2.2.1) X₀.2.2.2.2.2 L O').getD
        (O'.headD 0) []).length ≤ uB) :
    ∃ (ans : AnswerData D) (ch : List (ℕ × Option ℕ)),
      RunsWithin X body
        (Main.c3CJRouteProg sub n₀ n L k xy w (N, gs, d) Vx Vy (colXD cXX k Vx.length)
          (colYD cXY cYY k Vx.length) X₀) ans
        ((ch.map fun x => C x.1 x.2).sum +
          c3CJCost n N sIn gs.length k Vx.length Vy.length (sojZ (N - n)) BgP Bmem BkA BlA Bg1
            Bgen (w.1.length * rdOrbitWork N n w.1.length s sIn (max (N - n) uB.factorial) Bd
              Blift Bgen Bo 0 + dynSeqCost N w.1.length Bo + 5)) ∧
      AnsOK DV N (w.denote N) 1 (GensData.denote N gs) (xy.1.denote N) (xy.2.denote N) ans ∧
      (∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sIn) ∧
      ChildList w.1.length (c3R k Vy.length (sojZ (N - n)) * max (N - n) uB.factorial)
        (StepChild w.1.length (N - n)) ch := by
  classical
  have hGv : GroupValid DV N gs d := hI.valid.group
  have hWG : IsInvariant (GensData.denote N gs) (w.denote N) := hI.valid.invariant
  have hVyl : 6 ≤ Vy.length := hlen ▸ hm
  have hVyM : Vy.length ≤ N - n := c3p_length_le hVy hVyn
  have hVxM : Vx.length ≤ N - n := c3p_length_le hVx hVxn
  have hzlen : ∀ (V : List ℕ) (W : Array ℕ) (z : List ℕ), z ∈ goodListsD k V.length W →
      z.length ≤ k := by
    intro V W z hz
    obtain ⟨x, hx, rfl, -⟩ := mem_goodListsD.1 hz
    rw [List.length_map]
    omega
  set cX := colXD cXX k Vx.length with hcX
  set cY := colYD cXY cYY k Vx.length with hcY
  -- the first good list and the coloured pair of `x`
  obtain ⟨hz₀, hX₀mem⟩ := firstStructD_firstGood hfirst
  set X₀c := cjFirst3D (N - n) k Vx cX X₀ with hX₀c
  set Ys := cjStructs3D (N - n) k Vy cY with hYs
  have hal := outcomeD_along hVx hVxn cX hm hz₀ hX₀mem h2
  obtain ⟨t, hJt⟩ := isJohnson_of_along hal
  have hmL : N - n ≤ leafB (N - n) := by
    rw [leafB]
    omega
  have hX₀all : X₀ ∈ allStructsD (N - n) k Vx cX := firstStructD_mem hfirst
  have hXv : CJValid (N - n) X₀c ∧ JBound (leafB (N - n)) X₀c.1 := by
    refine ⟨?_, cp2_jbound_le (outSize_allStructsD_le hVxM hX₀all)⟩
    rcases c3p_allStructsD_valid hVx hVxn cX hm X₀ hX₀all with ⟨h1, -⟩ | ⟨-, hv⟩
    · omega
    · exact hv
  have hYv : ∀ Y ∈ Ys, CJValid (N - n) Y ∧ JBound (leafB (N - n)) Y.1 := by
    intro Y hY
    refine ⟨cj3_valid hVy hVyn cY hVyl Y hY, ?_⟩
    obtain ⟨z, hz, o, ho, -, rfl⟩ := mem_cjStructs3D.1 hY
    exact cp2_jbound_le (outSize_allStructsD_le hVyM (mem_allStructsD.2 ⟨z, hz, ho⟩))
  have hZy : ∀ z ∈ goodListsD k Vy.length (wlCD k Vy.length cY),
      outSzD k Vy (wlCD k Vy.length cY) z ≤ sojZ (N - n) :=
    fun z hz => outSzD_le hVy hVyn _ hVyl hz
  have hYlen : Ys.length ≤ c3R k Vy.length (sojZ (N - n)) :=
    length_cjStructs3D_le (N - n) k Vy cY hZy
  -- an isomorphism carries the fixed points of `x` onto those of `y`
  have hmove : ∀ g ∈ iso (w.denote N) 1 (GensData.denote N gs) (xy.1.denote N) (xy.2.denote N),
      ∃ hgG : g ∈ GensData.denote N gs, ∀ v : Fin (N - n),
        (baseHom _ n hC.base ⟨g, hgG⟩ v).val ∈ Vy ↔ v.val ∈ Vx := by
    intro g hg
    have hgG : g ∈ GensData.denote N gs := (mem_iso_one.1 hg).1
    have hy : Fy = Fx.map (MulAut.conj g).toMonoidHom := by
      rw [hFye, hFxe, ← heq g hgG _]
      exact (hloc _ _ (Recursion.relabel_eq_on_of_mem_iso hWG hg)).symm
    exact ⟨hgG, fun v => by rw [hVyF, hVxF]; exact c3p_fix_iff hC.base hFxi hFyi hgG hy v⟩
  have halign : ∀ g ∈ iso (w.denote N) 1 (GensData.denote N gs) (xy.1.denote N) (xy.2.denote N),
      ∃ Y ∈ Ys, ∃ h : g ∈ GensData.denote N gs,
        baseHom _ n hC.base ⟨g, h⟩ • (cjohnOps (N - n)).dec X₀c = (cjohnOps (N - n)).dec Y := by
    intro g hg
    obtain ⟨hgG, hσ⟩ := hmove g hg
    obtain ⟨π, hπ⟩ := c3p_renumber hVx hVxn hVy hVyn hlen _ hσ
    have hrel : ∀ T : Fin k → Fin Vx.length, Coherent.toFun cY (⇑π ∘ T) = Coherent.toFun cX T :=
      tupleCol_iso φ rfl hVx hXX hXY (strR hC ⟨g, hgG⟩) (c3p_strOn_iso hC hwS hg) π
        (c3p_hπ hφ hgG hVx hVxn hVy hVyn hlen hπ)
    obtain ⟨Y, hY, hYe⟩ := cj3_reach hVx hVxn hVy hVyn hlen _ hσ π hπ hrel hfirst h2
    exact ⟨Y, hY, hgG, hYe⟩
  have hq' : ∀ c, 2 * (Finset.univ.filter fun γ =>
      γ ∉ (Align.jdec (N - n) X₀c.1).V0 ∧ cjcol (N - n) X₀c γ = c).card ≤ N - n :=
    fun c => cj3_hq hVx hVxn cX hm hVx2 hz₀ hX₀mem h2 c
  have hspec : (cjohnOps (N - n)).Spec fun e => CJValid (N - n) e ∧ JBound (leafB (N - n)) e.1 :=
    cp2_spec_mono (cjohnOps_spec (N - n)) fun _ h => h.1
  obtain ⟨ans, ch, hrun, hok, hg, hch⟩ := RunsWithin.alignRd_cj_ns (τ := cjTy)
    (st := ((2 : ℕ), X₀c)) hOa hPa hO hPre hI hC.base halt B hGG₀ le_rfl hspec
    (gensP := fun e => Main.cjohnGensProg (N - n) e)
    (fun e he => RunsWithin.cjohnGensProg hmL e he.2)
    (isoP := fun e e' => Main.cjohnIsoProg (N - n) e e')
    (fun e e' he he' => RunsWithin.cjohnIsoProg hmL e e' he.2 he'.2) hXv hYv halign hBgP hBmem
    hBkA hBlA (hBg1 ⟨hXv.1, t, hJt⟩) hsub hB hs ((Nat.mul_le_mul_right _ hYlen).trans hLY)
    (hD ⟨hXv.1, t, hJt⟩) hLg rfl hXv.1 hJt (fun _ h => h) hq' hm5 (hu ⟨hXv.1, t, hJt⟩)
  refine ⟨ans, ch, ?_, hok, hg, hch.mono_factor (Nat.mul_le_mul_right _ hYlen)⟩
  -- the run
  have hcls := RunsWithin.c3FirstClsProg (X := X) (body := body) k Vx cX
  have hq := (RunsWithin.q3Prog (X := X) (body := body) (N - n) Vx
    (c3ClsD k Vx (wlCD k Vx.length cX) (firstGoodD k Vx cX))).mono
    (show q3Cost (N - n) Vx.length _ ≤ q3Cost (N - n) Vx.length Vx.length by
      have := length_c3ClsD_le k Vx (wlCD k Vx.length cX) (firstGoodD k Vx cX)
      unfold q3Cost
      omega)
  have hYrun := RunsWithin.cjStructs3Prog (X := X) (body := body) (N - n) k Vy cY
    (Cz := c3OutCost (N - n) k Vy.length (sojZ (N - n))) (Z := sojZ (N - n))
    (fun z hz => outCostD_le _ _ _ _ (hzlen _ _ z hz) (hZy z hz)) hZy
  apply RunsWithin.mono
  case h =>
    unfold Main.c3CJRouteProg
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step hcls
    run_step hq
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step hYrun
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact hrun
  case hc =>
    have hal' := c3p_alignCost_mono (n := n) (N := N) (g := gs.length)
      (cG := cjohnGensCost (leafB (N - n))) (cI := cjohnIsoCost (leafB (N - n))) (BgP := BgP)
      (Bmem := Bmem) (Bk := BkA) (Bl := BlA) (Bg1 := Bg1) (Bgen := Bgen)
      (Cb := w.1.length * rdOrbitWork N n w.1.length s sIn (max (N - n) uB.factorial) Bd Blift
        Bgen Bo 0 + dynSeqCost N w.1.length Bo + 5) (s := sIn)
      (length_cjohnGensD_le hXv.1) hYlen
    have hgk : ((cjohnOps (N - n)).gens X₀c).length = (cjohnGensD (N - n) X₀c).length := rfl
    simp only [Prim.cost, c3CJCost, hgk] at hal' ⊢
    clear_value X₀c Ys cX cY
    clear * - hal'
    omega

/-- `RunsWithin.c3CJRouteProg_jp` with its Johnson-route hypotheses stated without the pair's
facts. -/
theorem RunsWithin.c3CJRouteProg (hOa : MeetsContractOn DV alignOps X.O)
    (hPa : ∀ op x, alignOps op → GroupPre DV op x → X.Pre op x)
    (hO : MeetsContractOn DV rdOps X.O)
    (hPre : ∀ op x, rdOps op → GroupPre DV op x → X.Pre op x)
    (hI : HInstValid DV (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D))
    {hC : CertSetting (GensData.denote N gs) n} {φ : strGroup hC →* Perm (Fin (N - n))}
    (hφ : IsPhi hC φ)
    (halt : alternatingGroup (Fin (N - n)) ≤ (baseHom _ n hC.base).range)
    (hwS : ∀ u : Fin N, u.val < n → u ∈ w.denote N)
    {Fmap : (Fin N → ℕ) → Subgroup (Perm (Fin N))}
    (hloc : ∀ x x', (∀ u ∈ w.denote N, x u = x' u) → Fmap x = Fmap x')
    (heq : ∀ g ∈ GensData.denote N gs, ∀ x,
      Fmap (relabel g x) = (Fmap x).map (MulAut.conj g).toMonoidHom)
    {Fx Fy : Subgroup (Perm (Fin N))} (hFxe : Fx = Fmap (xy.1.denote N))
    (hFye : Fy = Fmap (xy.2.denote N)) (hFxi : IsInvariant Fx (baseSet n N))
    (hFyi : IsInvariant Fy (baseSet n N))
    {Vx Vy : List ℕ} (hVx : ∀ v ∈ Vx, v < N - n) (hVxn : Vx.Nodup)
    (hVy : ∀ v ∈ Vy, v < N - n) (hVyn : Vy.Nodup)
    (hVxF : ∀ v : Fin (N - n), v.val ∈ Vx ↔ ∀ f ∈ (baseHom Fx n hFxi).range, f v = v)
    (hVyF : ∀ v : Fin (N - n), v.val ∈ Vy ↔ ∀ f ∈ (baseHom Fy n hFyi).range, f v = v)
    (hm : 6 ≤ Vx.length) (hlen : Vx.length = Vy.length) (hVx2 : N - n ≤ 2 * Vx.length) {k : ℕ}
    {cXX cXY cYY : List ℕ → List ℕ → Bool}
    (hXX : ColChar φ (strOn hC.le (xy.1.denote N)) (strOn hC.le (xy.1.denote N)) k Vx.length
      Vx Vx cXX)
    (hXY : ColChar φ (strOn hC.le (xy.1.denote N)) (strOn hC.le (xy.2.denote N)) k Vx.length
      Vx Vy cXY)
    {X₀ : OutD} (hfirst : firstStructD (N - n) k Vx (colXD cXX k Vx.length) = some X₀)
    (h2 : X₀.1 = 2)
    {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N sIn G₀)
    (hGG₀ : GensData.denote N gs ≤ G₀)
    {BgP Bmem BkA BlA Bg1 uB : ℕ}
    (hBgP : X.B.call GroupOp.generate (N - n, gs.map (baseD n N))
      (X.O.run GroupOp.generate (N - n, gs.map (baseD n N))) ≤ BgP)
    (hBmem : ∀ g : PermData, g.Valid (N - n) → X.B.call GroupOp.mem (pModel X.O n (N, gs, d), g)
      (X.O.run GroupOp.mem (pModel X.O n (N, gs, d), g)) ≤ Bmem)
    (hBkA : X.B.call GroupOp.kernel ((N, gs, d), baseWin n N) (kerModel X.O n (N, gs, d)) ≤ BkA)
    (hBlA : ∀ π : PermData, X.B.call GroupOp.lift ((N, gs, d), (baseWin n N, π))
      (liftModel X.O n (N, gs, d) π) ≤ BlA)
    (hBg1 : X.B.call GroupOp.generate
        (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (cjohnGensD (N - n) (cjFirst3D (N - n) k Vx (colXD cXX k Vx.length) X₀)))).map
          (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
        (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (cjohnGensD (N - n) (cjFirst3D (N - n) k Vx (colXD cXX k Vx.length) X₀))))) ≤ Bg1)
    (hsub : HSubSolves X body DV sub
      (fun J => SizeChild sIn (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D)
        J ∧ StepChild w.1.length (N - n) (J.winSize, J.baseOpt)) C s)
    (hB : RDBounds X DV n N sIn Lg Blift Bgen Bo Bk Bcr) (hs : s ≤ sIn)
    (hLY : c3R k Vy.length (sojZ (N - n)) * (sIn + 1) ≤ Lg)
    (hLg : max (N - n) uB.factorial * (sIn + 1) ≤ Lg) (hm5 : 5 ≤ N - n)
    (hD : ∀ gs' d' O', RDSet DV n N gs w L
      (Giant.g1Model X.O n (N, gs, d) (cjohnOps (N - n))
        (cjFirst3D (N - n) k Vx (colXD cXX k Vx.length) X₀)).2.1 sIn gs' d' O' →
      RDOrbit X body DV n N w L (2, cjFirst3D (N - n) k Vx (colXD cXX k Vx.length) X₀) sIn Bd
        gs' d' O')
    (hu : ∀ gs' d' O', RDSet DV n N gs w L
      (Giant.g1Model X.O n (N, gs, d) (cjohnOps (N - n))
        (cjFirst3D (N - n) k Vx (colXD cXX k Vx.length) X₀)).2.1 sIn gs' d' O' →
      ((labJUD X₀.2.2.2.1.length (markArr (N - n) X₀.2.2.1) X₀.2.2.2.2.2 L O').getD
        (O'.headD 0) []).length ≤ uB) :
    ∃ (ans : AnswerData D) (ch : List (ℕ × Option ℕ)),
      RunsWithin X body
        (Main.c3CJRouteProg sub n₀ n L k xy w (N, gs, d) Vx Vy (colXD cXX k Vx.length)
          (colYD cXY cYY k Vx.length) X₀) ans
        ((ch.map fun x => C x.1 x.2).sum +
          c3CJCost n N sIn gs.length k Vx.length Vy.length (sojZ (N - n)) BgP Bmem BkA BlA Bg1
            Bgen (w.1.length * rdOrbitWork N n w.1.length s sIn (max (N - n) uB.factorial) Bd
              Blift Bgen Bo 0 + dynSeqCost N w.1.length Bo + 5)) ∧
      AnsOK DV N (w.denote N) 1 (GensData.denote N gs) (xy.1.denote N) (xy.2.denote N) ans ∧
      (∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sIn) ∧
      ChildList w.1.length (c3R k Vy.length (sojZ (N - n)) * max (N - n) uB.factorial)
        (StepChild w.1.length (N - n)) ch := by
  apply RunsWithin.c3CJRouteProg_jp (hBg1 := fun _ => hBg1) (hD := fun _ => hD) (hu := fun _ => hu)
  all_goals assumption

end JohnsonRoute

/-- Any colouring characterized by certificate equivalence gives `x`'s first structure. -/
theorem c3First_of_colChar {N n : ℕ} {G : Subgroup (Perm (Fin N))} {hC : CertSetting G n}
    {φ : strGroup hC →* Perm (Fin (N - n))} {xs : Fin n → ℕ} {M k : ℕ} {Vx : List ℕ}
    {c : List ℕ → List ℕ → Bool} (hc : Case3.ColChar φ xs xs k Vx.length Vx Vx c)
    {X₀ : SoJTree.OutD} (h : Case3.C3First φ xs M k Vx X₀) :
    Case3.firstStructD M k Vx (Case3.colXD c k Vx.length) = some X₀ := by
  obtain ⟨c', hc', hX₀⟩ := h
  have hcol : Case3.colXD c k Vx.length = Case3.colXD c' k Vx.length :=
    m5_colXD_congr fun di hdi dt hdt hn hn' =>
      Bool.eq_iff_iff.2 ((hc di hdi dt hdt hn hn').trans (hc' di hdi dt hdt hn hn').symm)
  rw [hcol]
  exact hX₀

/-- With the twins flag set, there is no first structure. -/
theorem firstStructD_of_twins {M k : ℕ} {V : List ℕ} {col : Array ℕ}
    (h : Case3.twinsD k V.length col = true) : Case3.firstStructD M k V col = none := by
  unfold Case3.twinsD at h
  unfold Case3.firstStructD
  rw [List.isEmpty_iff.1 h]

/-! ### The variant -/

/-- **The work of the variant's prefix**: the colourings' polynomial part (`c3ColWork`), the twins
flag, the first structure, and the dispatch. -/
def c3PreWork (N n s k mx my Bstab Btr Borb Bgen' Borb' Bstab' Bgk Bl Bgs wl Z : ℕ) : ℕ :=
  30 + wl + mx + my + c3ColWork N n s k mx Bstab Btr Borb Bgen' Borb' Bstab' Bgk Bl Bgs wl +
    Case3.twinsFlagCost k mx + (Case3.pipePrefixCost k mx + Case3.c3OutCost (N - n) k mx Z + 4)

section Variant

open GraphIso.Case3

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}
  {sub : HInstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)}
  {C : ℕ → Option ℕ → ℕ} {s : ℕ} {xy : StrData × StrData} {w : WinData}
  {N : ℕ} {gs : GensData} {d : D.denote} {n₀ n : ℕ} {L : LabelData} {st : ℕ × CJData}
  {sIn Lg Blift Bgen Bo Bk Bcr Bd : ℕ}

/-- **Case 3 of M5 with coloured Johnson alignment.** Given the run of 14j-4's `m5Case3Prog`
(`hold`: cost `Wold`, factor `Fold`; from `RunsWithin.m5Case3Prog` or `_part`), needed only when
`x`'s first structure is not a Johnson structure, and the hypotheses of the Johnson route
(`RunsWithin.c3CJRouteProg`) for every characterization of `x`'s colouring: the answer is
correct for `G` on `W` (no isomorphism when the numbers of fixed points differ). The
comparisons make at most `2 · c3Count` sub-calls on windows of at most `n / k` points; the work
is the prefix's (`c3PreWork`) plus both routes'; the children are `StepChild |W| m` with factor
`c3R · max(m, uB!) + Fold`.

The Johnson route's hypotheses (`hBg1'`, `hD'`, `hu`) carry the premise `CJFacts` of the coloured
pair (stage 14j-5c, `PLAN-14.md` §14.8 item 4); `RunsWithin.m5Case3CJProg` states them without. -/
theorem RunsWithin.m5Case3CJProg_jp (hOc : MeetsContractOn DV Case3.c3Ops X.O)
    (hPc : ∀ op x, Case3.c3Ops op → GroupPre DV op x → X.Pre op x)
    (hO : MeetsContractOn DV rdOps X.O)
    (hPre : ∀ op x, rdOps op → GroupPre DV op x → X.Pre op x)
    (hI : HInstValid DV (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D))
    {hC : CertSetting (GensData.denote N gs) n} {φ : strGroup hC →* Perm (Fin (N - n))}
    (hφ : IsPhi hC φ)
    (halt : alternatingGroup (Fin (N - n)) ≤ (baseHom _ n hC.base).range)
    (hwS : ∀ u : Fin N, u.val < n → u ∈ w.denote N)
    {Fmap : (Fin N → ℕ) → Subgroup (Perm (Fin N))}
    (hloc : ∀ x x', (∀ u ∈ w.denote N, x u = x' u) → Fmap x = Fmap x')
    (heq : ∀ g ∈ GensData.denote N gs, ∀ x,
      Fmap (relabel g x) = (Fmap x).map (MulAut.conj g).toMonoidHom)
    {Fx Fy : Subgroup (Perm (Fin N))} (hFxe : Fx = Fmap (xy.1.denote N))
    (hFye : Fy = Fmap (xy.2.denote N)) (hFxi : IsInvariant Fx (baseSet n N))
    (hFyi : IsInvariant Fy (baseSet n N))
    {Vx Vy : List ℕ} (hVx : ∀ v ∈ Vx, v < N - n) (hVxn : Vx.Nodup)
    (hVy : ∀ v ∈ Vy, v < N - n) (hVyn : Vy.Nodup)
    (hVxF : ∀ v : Fin (N - n), v.val ∈ Vx ↔ ∀ f ∈ (baseHom Fx n hFxi).range, f v = v)
    (hVyF : ∀ v : Fin (N - n), v.val ∈ Vy ↔ ∀ f ∈ (baseHom Fy n hFyi).range, f v = v)
    (hm : 6 ≤ Vx.length) (hVx2 : N - n ≤ 2 * Vx.length) {k : ℕ} (h5 : 5 ≤ k)
    (hk : k + 2 ≤ N - n)
    {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N sIn G₀) (hgs : gs.length ≤ sIn)
    (hGG₀ : GensData.denote N gs ≤ G₀) {sk : ℕ} (Bk' : BackendBounds X DV k sk ⊤)
    (hsk : sIn ≤ k * (sk + 1)) {Bgk Bl Bgs : ℕ}
    (hBgk : ∀ gs' : GensData, GensData.AllValid N gs' →
      gs'.length ≤ k.factorial * (sIn + 1) → GensData.denote N gs' ≤ GensData.denote N gs →
        X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ Bgk)
    (hBl : ∀ π : PermData, X.B.call GroupOp.lift ((N, gs, d), (baseWin n N, π))
      (liftModel X.O n (N, gs, d) π) ≤ Bl)
    (hBgs : ∀ al : List ℕ, al.Nodup → al.length = k → (∀ a ∈ al, a < N - n) → ∀ b₁ b₂,
      X.B.call GroupOp.generate (N, giantGens X.O n (N, gs, d) al b₁ b₂)
        (giantSetStabModel X.O n (N, gs, d) al b₁ b₂) ≤ Bgs)
    {BgP Bmem Bker Bg1' uB : ℕ}
    (hBgP : X.B.call GroupOp.generate (N - n, gs.map (baseD n N))
      (X.O.run GroupOp.generate (N - n, gs.map (baseD n N))) ≤ BgP)
    (hBmem : ∀ g : PermData, g.Valid (N - n) → X.B.call GroupOp.mem (pModel X.O n (N, gs, d), g)
      (X.O.run GroupOp.mem (pModel X.O n (N, gs, d), g)) ≤ Bmem)
    (hBker : X.B.call GroupOp.kernel ((N, gs, d), baseWin n N) (kerModel X.O n (N, gs, d)) ≤
      Bker)
    (hsub : HSubSolves X body DV sub
      (fun J => SizeChild sIn (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D)
        J ∧ StepChild w.1.length (N - n) (J.winSize, J.baseOpt)) C s)
    (hCmono : ∀ a b, a ≤ b → C a none ≤ C b none)
    (hB : RDBounds X DV n N sIn Lg Blift Bgen Bo Bk Bcr) (hs : s ≤ sIn)
    -- 14j-4's route
    {Wold Fold : ℕ}
    (hold : (∀ X₀, C3First φ (strOn hC.le (xy.1.denote N)) (N - n) k Vx X₀ → X₀.1 ≠ 2) →
      ∃ (ans : AnswerData D) (ch : List (ℕ × Option ℕ)),
      RunsWithin X body (Main.m5Case3Prog sub
          (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D) n₀ n L st k xy w
          (N, gs, d) Vx Vy) ans
        ((ch.map fun x => C x.1 x.2).sum + c3Count Vx.length k n * C (n / k) none + Wold) ∧
        AnsOK DV N (w.denote N) 1 (GensData.denote N gs) (xy.1.denote N) (xy.2.denote N) ans ∧
        (∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sIn) ∧
        ChildList w.1.length Fold (StepChild w.1.length (N - n)) ch)
    -- the Johnson route
    (hBg1' : ∀ cXX X₀, ColChar φ (strOn hC.le (xy.1.denote N)) (strOn hC.le (xy.1.denote N)) k
        Vx.length Vx Vx cXX → firstStructD (N - n) k Vx (colXD cXX k Vx.length) = some X₀ →
      X₀.1 = 2 → CJFacts (N - n) (cjFirst3D (N - n) k Vx (colXD cXX k Vx.length) X₀) →
      X.B.call GroupOp.generate
        (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (cjohnGensD (N - n) (cjFirst3D (N - n) k Vx (colXD cXX k Vx.length) X₀)))).map
          (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
        (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (cjohnGensD (N - n) (cjFirst3D (N - n) k Vx (colXD cXX k Vx.length) X₀))))) ≤ Bg1')
    (hLY : c3R k Vy.length (sojZ (N - n)) * (sIn + 1) ≤ Lg)
    (hLg' : max (N - n) uB.factorial * (sIn + 1) ≤ Lg) (hm5 : 5 ≤ N - n)
    (hD' : ∀ cXX X₀, ColChar φ (strOn hC.le (xy.1.denote N)) (strOn hC.le (xy.1.denote N)) k
        Vx.length Vx Vx cXX → firstStructD (N - n) k Vx (colXD cXX k Vx.length) = some X₀ →
      X₀.1 = 2 → CJFacts (N - n) (cjFirst3D (N - n) k Vx (colXD cXX k Vx.length) X₀) →
        ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (cjohnOps (N - n))
          (cjFirst3D (N - n) k Vx (colXD cXX k Vx.length) X₀)).2.1 sIn gs' d' O' →
      RDOrbit X body DV n N w L (2, cjFirst3D (N - n) k Vx (colXD cXX k Vx.length) X₀) sIn Bd
        gs' d' O')
    (hu : ∀ cXX X₀, ColChar φ (strOn hC.le (xy.1.denote N)) (strOn hC.le (xy.1.denote N)) k
        Vx.length Vx Vx cXX → firstStructD (N - n) k Vx (colXD cXX k Vx.length) = some X₀ →
      X₀.1 = 2 → CJFacts (N - n) (cjFirst3D (N - n) k Vx (colXD cXX k Vx.length) X₀) →
        ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (cjohnOps (N - n))
          (cjFirst3D (N - n) k Vx (colXD cXX k Vx.length) X₀)).2.1 sIn gs' d' O' →
      ((labJUD X₀.2.2.2.1.length (markArr (N - n) X₀.2.2.1) X₀.2.2.2.2.2 L O').getD
        (O'.headD 0) []).length ≤ uB) :
    ∃ (ans : AnswerData D) (ch : List (ℕ × Option ℕ)),
      RunsWithin X body (Main.m5Case3CJProg sub
          (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D) n₀ n L st k xy w
          (N, gs, d) Vx Vy) ans
        ((ch.map fun x => C x.1 x.2).sum + 2 * (c3Count Vx.length k n * C (n / k) none) +
          (c3PreWork N n sIn k Vx.length Vy.length B.Bstab B.Btr B.Borb Bk'.Bgen Bk'.Borb
              Bk'.Bstab Bgk Bl Bgs w.1.length (sojZ (N - n)) +
            c3CJCost n N sIn gs.length k Vx.length Vy.length (sojZ (N - n)) BgP Bmem Bker Bl Bg1'
              Bgen (w.1.length * rdOrbitWork N n w.1.length s sIn (max (N - n) uB.factorial) Bd
                Blift Bgen Bo 0 + dynSeqCost N w.1.length Bo + 5) +
            Wold)) ∧
      AnsOK DV N (w.denote N) 1 (GensData.denote N gs) (xy.1.denote N) (xy.2.denote N) ans ∧
      (∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sIn) ∧
      ChildList w.1.length (c3R k Vy.length (sojZ (N - n)) * max (N - n) uB.factorial + Fold)
        (StepChild w.1.length (N - n)) ch := by
  classical
  have hGv : GroupValid DV N gs d := hI.valid.group
  have hw : w.Valid N := hI.valid.win
  have hOa : MeetsContractOn DV alignOps X.O := fun op x h hx => hOc op x (Or.inr h) hx
  have hPa : ∀ op x, alignOps op → GroupPre DV op x → X.Pre op x :=
    fun op x h hx => hPc op x (Or.inr h) hx
  have hOcert : MeetsContractOn DV certOps X.O := fun op x h hp => hOc op x (Or.inl h) hp
  have hPcert : ∀ op x, certOps op → GroupPre DV op x → X.Pre op x := fun op x h hp =>
    hPc op x (Or.inl h) hp
  have hnw : n ≤ w.1.length := m5_n_le_win hw hI.le hwS
  have hw1 : 1 ≤ w.1.length := by
    obtain ⟨i, hi, -⟩ := (hI.hint L rfl).1.nonconst
    exact List.length_pos_of_mem hi
  have hWG : IsInvariant (GensData.denote N gs) (w.denote N) := hI.valid.invariant
  -- an isomorphism carries the fixed points of `x` onto those of `y`
  have hmove : ∀ g ∈ iso (w.denote N) 1 (GensData.denote N gs) (xy.1.denote N) (xy.2.denote N),
      ∃ hgG : g ∈ GensData.denote N gs, ∀ v : Fin (N - n),
        (baseHom _ n hC.base ⟨g, hgG⟩ v).val ∈ Vy ↔ v.val ∈ Vx := by
    intro g hg
    have hgG : g ∈ GensData.denote N gs := (mem_iso_one.1 hg).1
    have hy : Fy = Fx.map (MulAut.conj g).toMonoidHom := by
      rw [hFye, hFxe, ← heq g hgG _]
      exact (hloc _ _ (Recursion.relabel_eq_on_of_mem_iso hWG hg)).symm
    exact ⟨hgG, fun v => by rw [hVyF, hVxF]; exact c3p_fix_iff hC.base hFxi hFyi hgG hy v⟩
  set P := c3Count Vx.length k n * C (n / k) none with hP
  have hFold : Fold ≤ c3R k Vy.length (sojZ (N - n)) * max (N - n) uB.factorial + Fold :=
    Nat.le_add_left _ _
  -- the comparisons' sub-solver
  have hPcmp : ∀ (xy' : StrData × StrData) (J : InstData D),
      StepSubP (DV := DV) (GensData.denote N gs) xy' n k sIn J →
      SizeChild sIn (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D)
          ((J, n₀, n, none) : HInstData D) ∧
        StepChild w.1.length (N - n) (HInstData.winSize ((J, n₀, n, none) : HInstData D),
          HInstData.baseOpt ((J, n₀, n, none) : HInstData D)) := by
    intro xy' J hJ
    obtain ⟨-, -, hdeg, -, hkw, -, hgl⟩ := hJ
    have h5w := Nat.mul_le_mul_right J.2.1.1.length h5
    refine ⟨⟨rfl, le_rfl, ?_, hgl, SizeChild.lab_none rfl le_rfl rfl⟩, ?_, Or.inr ⟨rfl, ?_⟩⟩
    · change J.degree ≤ max N (2 * n)
      rw [hdeg]
      exact le_max_left _ _
    · change J.2.1.1.length ≤ w.1.length
      omega
    · change 2 * J.2.1.1.length ≤ w.1.length
      omega
  have hcmp : ∀ xy' : StrData × StrData,
      SubSolves X body DV (fun J => Main.c3Sub sub n₀ n L st w.1.length J)
        (StepSubP (DV := DV) (GensData.denote N gs) xy' n k sIn)
        (fun _ => C (n / k) none + 4 + w.1.length + 6) sIn := fun xy' =>
    m5_subSolves_mono (m5_c3Sub_cmp (m5_stepSub hsub hCmono (by omega) hC xy' (hPcmp xy'))
      (fun J hJ => by
        obtain ⟨-, -, -, -, hkw, -, -⟩ := hJ
        have := Nat.mul_le_mul_right J.2.1.1.length h5
        omega)) hs
  by_cases hlen : Vx.length = Vy.length
  swap
  · -- different numbers of fixed points: no isomorphism
    refine ⟨none, [], ?_, ?_, ?_, ?_⟩
    rotate_left 2
    · intro c hc
      cases hc
    · exact ⟨by simp, by simp, by simp⟩
    · apply RunsWithin.mono
      case h =>
        unfold Main.m5Case3CJProg
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_with Sims.RunsWithin.ite_neg (show (Vx.length == Vy.length) = false by simp [hlen]) _
        exact RunsWithin.prim _ _
      case hc =>
        simp only [Prim.cost, Prim.eval, Args.head, c3PreWork, twinsFlagCost]
        clear_value P
        clear * -
        omega
    · show iso (w.denote N) 1 (GensData.denote N gs) (xy.1.denote N) (xy.2.denote N) = ∅
      by_contra hne
      obtain ⟨g, hg⟩ := Set.nonempty_iff_ne_empty.2 hne
      obtain ⟨hgG, hσ⟩ := hmove g hg
      exact hlen (c3p_length_eq hVx hVxn hVy hVyn _ hσ)
  -- the colourings
  have hVyl : 6 ≤ Vy.length := hlen ▸ hm
  obtain ⟨cXX, cXY, cYY, hXX, hXY, -, hcol⟩ := Case3.RunsWithin.tupleColProg (X := X)
    (body := body) (φ := φ) (x := xy.1) (y := xy.2) hOcert hPcert hφ hGv halt hVxn hVyn
    hlen.symm hVx hVy h5 hk B hgs hGG₀ Bk' hsk hBgk hBl hBgs (hcmp _) (hcmp _) (hcmp _)
  have hcolc := hcol.mono (tupleColCost_split N n sIn k Vx.length B.Bstab B.Btr B.Borb Bk'.Bgen
    Bk'.Borb Bk'.Bstab Bgk Bl Bgs w.1.length (C (n / k) none))
  rw [← hP] at hcolc
  set cX := colXD cXX k Vx.length with hcX
  set cY := colYD cXY cYY k Vx.length with hcY
  have htw := Case3.RunsWithin.twinsFlagProg (X := X) (body := body) k Vx.length cX
  have hzlen : ∀ (V : List ℕ) (W : Array ℕ) (z : List ℕ), z ∈ goodListsD k V.length W →
      z.length ≤ k := by
    intro V W z hz
    obtain ⟨x, hx, rfl, -⟩ := mem_goodListsD.1 hz
    rw [List.length_map]
    omega
  have hfs := Case3.RunsWithin.firstStructProg (X := X) (body := body) (N - n) k Vx cX
    (Cz := c3OutCost (N - n) k Vx.length (sojZ (N - n)))
    (fun z hz => outCostD_le _ _ _ _ (hzlen _ _ z hz) (outSzD_le hVx hVxn _ hm hz))
  by_cases htwb : twinsD k Vx.length cX = true
  · obtain ⟨ansO, chO, hrunO, hokO, hgO, hchO⟩ := hold fun X₀ hX₀ => by
      have h := c3First_of_colChar hXX hX₀
      rw [← hcX, firstStructD_of_twins htwb] at h
      cases h
    refine ⟨ansO, chO, ?_, hokO, hgO, hchO.mono_factor hFold⟩
    apply RunsWithin.mono
    case h =>
      unfold Main.m5Case3CJProg
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_with Sims.RunsWithin.ite_pos (show (Vx.length == Vy.length) = true by simp [hlen]) _
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step hcolc
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step htw
      run_with Sims.RunsWithin.ite_pos htwb _
      exact hrunO
    case hc =>
      simp only [Prim.cost, Prim.eval, Args.head, c3PreWork, twinsFlagCost]
      clear_value P cX cY
      generalize (chO.map fun x => C x.1 x.2).sum = A
      clear * -
      omega
  have htwf : twinsD k Vx.length cX = false := by simpa using htwb
  rcases hf : firstStructD (N - n) k Vx cX with _ | X₀
  · rw [hf] at hfs
    obtain ⟨ansO, chO, hrunO, hokO, hgO, hchO⟩ := hold fun X₁ hX₁ => by
      have h := c3First_of_colChar hXX hX₁
      rw [← hcX, hf] at h
      cases h
    refine ⟨ansO, chO, ?_, hokO, hgO, hchO.mono_factor hFold⟩
    apply RunsWithin.mono
    case h =>
      unfold Main.m5Case3CJProg
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_with Sims.RunsWithin.ite_pos (show (Vx.length == Vy.length) = true by simp [hlen]) _
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step hcolc
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step htw
      run_with Sims.RunsWithin.ite_neg htwf _
      run_step hfs
      run_with RunsWithin.caseOption_none _
      exact hrunO
    case hc =>
      simp only [Prim.cost, Prim.eval, Args.head, c3PreWork, twinsFlagCost]
      clear_value P cX cY
      generalize (chO.map fun x => C x.1 x.2).sum = A
      clear * -
      omega
  rw [hf] at hfs
  by_cases h2 : X₀.1 = 2
  · obtain ⟨ans, ch, hrun, hok, hg, hch⟩ := RunsWithin.c3CJRouteProg_jp (body := body) (C := C)
      (sub := sub) (cYY := cYY) hOa hPa hO hPre hI hφ halt hwS hloc heq hFxe hFye hFxi hFyi hVx
      hVxn hVy hVyn hVxF hVyF hm hlen hVx2 hXX hXY hf h2 B hGG₀ hBgP hBmem hBker hBl
      (hBg1' cXX X₀ hXX hf h2) hsub hB hs hLY hLg' hm5 (hD' cXX X₀ hXX hf h2) (hu cXX X₀ hXX hf h2)
    refine ⟨ans, ch, ?_, hok, hg, hch.mono_factor (Nat.le_add_right _ _)⟩
    apply RunsWithin.mono
    case h =>
      unfold Main.m5Case3CJProg
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_with Sims.RunsWithin.ite_pos (show (Vx.length == Vy.length) = true by simp [hlen]) _
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step hcolc
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step htw
      run_with Sims.RunsWithin.ite_neg htwf _
      run_step hfs
      run_with RunsWithin.caseOption_some _
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_with Sims.RunsWithin.ite_pos (show (X₀.1 == 2) = true by simp [h2]) _
      exact hrun
    case hc =>
      simp only [Prim.cost, Prim.eval, Args.head, c3PreWork, twinsFlagCost]
      clear_value P cX cY
      generalize (ch.map fun x => C x.1 x.2).sum = A
      clear * -
      omega
  · obtain ⟨ansO, chO, hrunO, hokO, hgO, hchO⟩ := hold fun X₁ hX₁ => by
      have h := c3First_of_colChar hXX hX₁
      rw [← hcX, hf] at h
      obtain rfl := Option.some.inj h
      exact h2
    refine ⟨ansO, chO, ?_, hokO, hgO, hchO.mono_factor hFold⟩
    apply RunsWithin.mono
    case h =>
      unfold Main.m5Case3CJProg
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_with Sims.RunsWithin.ite_pos (show (Vx.length == Vy.length) = true by simp [hlen]) _
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step hcolc
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step htw
      run_with Sims.RunsWithin.ite_neg htwf _
      run_step hfs
      run_with RunsWithin.caseOption_some _
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_with Sims.RunsWithin.ite_neg (show (X₀.1 == 2) = false by simp [h2]) _
      exact hrunO
    case hc =>
      simp only [Prim.cost, Prim.eval, Args.head, c3PreWork, twinsFlagCost]
      clear_value P cX cY
      generalize (chO.map fun x => C x.1 x.2).sum = A
      clear * -
      omega

/-- `RunsWithin.m5Case3CJProg_jp` with the Johnson route's hypotheses stated without the pair's
facts. -/
theorem RunsWithin.m5Case3CJProg (hOc : MeetsContractOn DV Case3.c3Ops X.O)
    (hPc : ∀ op x, Case3.c3Ops op → GroupPre DV op x → X.Pre op x)
    (hO : MeetsContractOn DV rdOps X.O)
    (hPre : ∀ op x, rdOps op → GroupPre DV op x → X.Pre op x)
    (hI : HInstValid DV (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D))
    {hC : CertSetting (GensData.denote N gs) n} {φ : strGroup hC →* Perm (Fin (N - n))}
    (hφ : IsPhi hC φ)
    (halt : alternatingGroup (Fin (N - n)) ≤ (baseHom _ n hC.base).range)
    (hwS : ∀ u : Fin N, u.val < n → u ∈ w.denote N)
    {Fmap : (Fin N → ℕ) → Subgroup (Perm (Fin N))}
    (hloc : ∀ x x', (∀ u ∈ w.denote N, x u = x' u) → Fmap x = Fmap x')
    (heq : ∀ g ∈ GensData.denote N gs, ∀ x,
      Fmap (relabel g x) = (Fmap x).map (MulAut.conj g).toMonoidHom)
    {Fx Fy : Subgroup (Perm (Fin N))} (hFxe : Fx = Fmap (xy.1.denote N))
    (hFye : Fy = Fmap (xy.2.denote N)) (hFxi : IsInvariant Fx (baseSet n N))
    (hFyi : IsInvariant Fy (baseSet n N))
    {Vx Vy : List ℕ} (hVx : ∀ v ∈ Vx, v < N - n) (hVxn : Vx.Nodup)
    (hVy : ∀ v ∈ Vy, v < N - n) (hVyn : Vy.Nodup)
    (hVxF : ∀ v : Fin (N - n), v.val ∈ Vx ↔ ∀ f ∈ (baseHom Fx n hFxi).range, f v = v)
    (hVyF : ∀ v : Fin (N - n), v.val ∈ Vy ↔ ∀ f ∈ (baseHom Fy n hFyi).range, f v = v)
    (hm : 6 ≤ Vx.length) (hVx2 : N - n ≤ 2 * Vx.length) {k : ℕ} (h5 : 5 ≤ k)
    (hk : k + 2 ≤ N - n)
    {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N sIn G₀) (hgs : gs.length ≤ sIn)
    (hGG₀ : GensData.denote N gs ≤ G₀) {sk : ℕ} (Bk' : BackendBounds X DV k sk ⊤)
    (hsk : sIn ≤ k * (sk + 1)) {Bgk Bl Bgs : ℕ}
    (hBgk : ∀ gs' : GensData, GensData.AllValid N gs' →
      gs'.length ≤ k.factorial * (sIn + 1) → GensData.denote N gs' ≤ GensData.denote N gs →
        X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ Bgk)
    (hBl : ∀ π : PermData, X.B.call GroupOp.lift ((N, gs, d), (baseWin n N, π))
      (liftModel X.O n (N, gs, d) π) ≤ Bl)
    (hBgs : ∀ al : List ℕ, al.Nodup → al.length = k → (∀ a ∈ al, a < N - n) → ∀ b₁ b₂,
      X.B.call GroupOp.generate (N, giantGens X.O n (N, gs, d) al b₁ b₂)
        (giantSetStabModel X.O n (N, gs, d) al b₁ b₂) ≤ Bgs)
    {BgP Bmem Bker Bg1' uB : ℕ}
    (hBgP : X.B.call GroupOp.generate (N - n, gs.map (baseD n N))
      (X.O.run GroupOp.generate (N - n, gs.map (baseD n N))) ≤ BgP)
    (hBmem : ∀ g : PermData, g.Valid (N - n) → X.B.call GroupOp.mem (pModel X.O n (N, gs, d), g)
      (X.O.run GroupOp.mem (pModel X.O n (N, gs, d), g)) ≤ Bmem)
    (hBker : X.B.call GroupOp.kernel ((N, gs, d), baseWin n N) (kerModel X.O n (N, gs, d)) ≤
      Bker)
    (hsub : HSubSolves X body DV sub
      (fun J => SizeChild sIn (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D)
        J ∧ StepChild w.1.length (N - n) (J.winSize, J.baseOpt)) C s)
    (hCmono : ∀ a b, a ≤ b → C a none ≤ C b none)
    (hB : RDBounds X DV n N sIn Lg Blift Bgen Bo Bk Bcr) (hs : s ≤ sIn)
    -- 14j-4's route
    {Wold Fold : ℕ}
    (hold : (∀ X₀, C3First φ (strOn hC.le (xy.1.denote N)) (N - n) k Vx X₀ → X₀.1 ≠ 2) →
      ∃ (ans : AnswerData D) (ch : List (ℕ × Option ℕ)),
      RunsWithin X body (Main.m5Case3Prog sub
          (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D) n₀ n L st k xy w
          (N, gs, d) Vx Vy) ans
        ((ch.map fun x => C x.1 x.2).sum + c3Count Vx.length k n * C (n / k) none + Wold) ∧
        AnsOK DV N (w.denote N) 1 (GensData.denote N gs) (xy.1.denote N) (xy.2.denote N) ans ∧
        (∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sIn) ∧
        ChildList w.1.length Fold (StepChild w.1.length (N - n)) ch)
    -- the Johnson route
    (hBg1' : ∀ cXX X₀, ColChar φ (strOn hC.le (xy.1.denote N)) (strOn hC.le (xy.1.denote N)) k
        Vx.length Vx Vx cXX → firstStructD (N - n) k Vx (colXD cXX k Vx.length) = some X₀ →
      X₀.1 = 2 →
      X.B.call GroupOp.generate
        (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (cjohnGensD (N - n) (cjFirst3D (N - n) k Vx (colXD cXX k Vx.length) X₀)))).map
          (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
        (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (cjohnGensD (N - n) (cjFirst3D (N - n) k Vx (colXD cXX k Vx.length) X₀))))) ≤ Bg1')
    (hLY : c3R k Vy.length (sojZ (N - n)) * (sIn + 1) ≤ Lg)
    (hLg' : max (N - n) uB.factorial * (sIn + 1) ≤ Lg) (hm5 : 5 ≤ N - n)
    (hD' : ∀ cXX X₀, ColChar φ (strOn hC.le (xy.1.denote N)) (strOn hC.le (xy.1.denote N)) k
        Vx.length Vx Vx cXX → firstStructD (N - n) k Vx (colXD cXX k Vx.length) = some X₀ →
      X₀.1 = 2 → ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (cjohnOps (N - n))
          (cjFirst3D (N - n) k Vx (colXD cXX k Vx.length) X₀)).2.1 sIn gs' d' O' →
      RDOrbit X body DV n N w L (2, cjFirst3D (N - n) k Vx (colXD cXX k Vx.length) X₀) sIn Bd
        gs' d' O')
    (hu : ∀ cXX X₀, ColChar φ (strOn hC.le (xy.1.denote N)) (strOn hC.le (xy.1.denote N)) k
        Vx.length Vx Vx cXX → firstStructD (N - n) k Vx (colXD cXX k Vx.length) = some X₀ →
      X₀.1 = 2 → ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (cjohnOps (N - n))
          (cjFirst3D (N - n) k Vx (colXD cXX k Vx.length) X₀)).2.1 sIn gs' d' O' →
      ((labJUD X₀.2.2.2.1.length (markArr (N - n) X₀.2.2.1) X₀.2.2.2.2.2 L O').getD
        (O'.headD 0) []).length ≤ uB) :
    ∃ (ans : AnswerData D) (ch : List (ℕ × Option ℕ)),
      RunsWithin X body (Main.m5Case3CJProg sub
          (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D) n₀ n L st k xy w
          (N, gs, d) Vx Vy) ans
        ((ch.map fun x => C x.1 x.2).sum + 2 * (c3Count Vx.length k n * C (n / k) none) +
          (c3PreWork N n sIn k Vx.length Vy.length B.Bstab B.Btr B.Borb Bk'.Bgen Bk'.Borb
              Bk'.Bstab Bgk Bl Bgs w.1.length (sojZ (N - n)) +
            c3CJCost n N sIn gs.length k Vx.length Vy.length (sojZ (N - n)) BgP Bmem Bker Bl Bg1'
              Bgen (w.1.length * rdOrbitWork N n w.1.length s sIn (max (N - n) uB.factorial) Bd
                Blift Bgen Bo 0 + dynSeqCost N w.1.length Bo + 5) +
            Wold)) ∧
      AnsOK DV N (w.denote N) 1 (GensData.denote N gs) (xy.1.denote N) (xy.2.denote N) ans ∧
      (∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sIn) ∧
      ChildList w.1.length (c3R k Vy.length (sojZ (N - n)) * max (N - n) uB.factorial + Fold)
        (StepChild w.1.length (N - n)) ch := by
  apply RunsWithin.m5Case3CJProg_jp (hBg1' := fun cXX X₀ h1 h2 h3 _ => hBg1' cXX X₀ h1 h2 h3)
    (hD' := fun cXX X₀ h1 h2 h3 _ => hD' cXX X₀ h1 h2 h3)
    (hu := fun cXX X₀ h1 h2 h3 _ => hu cXX X₀ h1 h2 h3)
  all_goals assumption

end Variant

end GraphIso.Main
