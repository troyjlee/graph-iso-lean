module

public import GraphIso.Case3.PipelineProg
public import GraphIso.Case3.Colouring
public import GraphIso.Case3.Link

/-!
# Case 3: the program

Stage 14i (`PLAN-14.md` §13, item 4): Case 3 of the giant macro-step, where the support of the
full group has fewer than `m/2` points. `Vx`, `Vy` list the base indices outside the supports
for `x` and for `y`.

* **The program** (`case3Prog`). It returns an `Option` of an answer:
  - `none` is the **fallback signal**: the Design Lemma found no good list for `x`'s colouring
    (the twins flag), and the main recursion must use M3's kernel reduction instead. No good
    list implies more than `t` pairwise twins (`twinsD_spec`), but not conversely: a colouring
    with large twins may still have a good list, and then the program answers;
  - `some ans` is the answer of Case 3.

  If `|Vx| ≠ |Vy|` there is no isomorphism, `some none`. Otherwise:
  - the colourings of the `k`-tuples of `Vx` (for `x`) and of `Vy` (for `y`), with consistent
    names (`tupleColProg`);
  - the twins flag of `x`'s colouring (`twinsFlagProg`); if it is set, `none`;
  - otherwise the first structure of `x` (`firstStructProg`), all structures of `y`
    (`allStructsProg`), and Align (`alignProg` with `outGensProg`, `outIsoProg`).
* `RunsWithin.case3Prog`: the hypothesis form. Given the run of the colourings, the validity of
  the structures, the alignment hypothesis and uniform bounds per good list, the program runs
  within `c3Cost`. It returns `none` only when the twins flag of `x` is set, and every answer is
  correct for `G` (`AnsOK`), under `SubSolves` for the aligned cosets.
* `RunsWithin.case3Prog_canonical`: the canonical form. `F` is a canonical map of the strings
  into subgroups of `G` and `Vx`, `Vy` list the fixed points of `ψ(F(x))`, `ψ(F(y))`. The
  colourings come from `RunsWithin.tupleColProg`, and the hypotheses of the hypothesis form are
  derived:
  - **alignment**: an isomorphism `g` carries the support of `x` to that of `y`
    (`c3p_fix_iff`); its renumbering `π` relates the colourings (`tupleCol_iso`), so `g` carries
    the first structure of `x` to a structure of `y` (`case3_reach`, `allStructsD_leafMs`,
    `firstStructD_reach`);
  - **validity** of every listed structure (`c3p_allStructsD_valid`: no twin hypothesis is
    needed for validity, only for liveness);
  - **sizes**: the `soj` trees have size at most `sojZ (N - n)` (`outSzD_le`), so the cost per
    good list is at most `c3OutCost` (`outCostD_le`), and the first structure has at most
    `outGensB (N - n)` generators (`length_outGensD_le`).

  The cost `c3CostC` is closed. The fallback happens only when the colouring of `x` (certificate
  equivalence, `colX_eq_iff`) has more than `t` pairwise twins (`twinsD_spec`).
* `case3_no_fallback`: under the thresholds of the interface no such twins exist
  (`no_twins_of_thresholds`), so the fallback never happens.
* `c3_ss_charges`: the generation charges for the Schreier–Sims backend, with bounded lists.
-/

@[expose] public section

namespace GraphIso.Case3

open Equiv MulAction Pointwise Finset GraphIso GraphIso.Cost GraphIso.Programs
  GraphIso.SplitJohnson GraphIso.SoJProg GraphIso.SoJTree GraphIso.Coherent GraphIso.Align
  GraphIso.Case2b GraphIso.Toolkit GraphIso.Sims GraphIso.Solver GraphIso.Certificates
  GraphIso.CertProg

/-! ### The program -/

section Program

variable {D : Ty} {rec : Ty × Ty} {var : Ty → Type}

/-- **Case 3.** The result is `none` (fall back to the kernel reduction) when the Design Lemma
finds no good list for the colouring of `x` (which implies more than `t` pairwise twins), and
`some` of the answer otherwise. -/
def case3Prog (sub : var (Ty.inst D) → Prog (groupSig D) rec var (Ty.answer D))
    (n k : var .nat) (xy : var Ty.strs) (w : var Ty.win) (G : var (Ty.group D))
    (Vx Vy : var (.list .nat)) : Prog (groupSig D) rec var (.option (Ty.answer D)) :=
  .bind (.op1 .fst G) fun N => .bind (.op2 .sub N n) fun M =>
  .bind (.op1 .length Vx) fun mx => .bind (.op1 .length Vy) fun my =>
  .bind (.op2 .natEq mx my) fun same =>
  .ite same
    (.bind (.op1 .fst xy) fun x => .bind (.op1 .snd xy) fun y =>
      .bind (tupleColProg sub n N k Vx Vy x y G) fun cc =>
      .bind (.op1 .fst cc) fun cX => .bind (.op1 .snd cc) fun cY =>
      .bind (twinsFlagProg k mx cX) fun tw =>
      .ite tw (.op0 .none)
        (.bind (firstStructProg M k Vx cX) fun ox =>
          .caseOption ox (.op0 .none) fun X₀ =>
          .bind (allStructsProg M k Vy cY) fun Ys =>
          .bind (alignProg sub (fun o => outGensProg M o) (fun o o' => outIsoProg M o o') n xy w
            G X₀ Ys) fun ans =>
          .op1 .some ans))
    (.bind (.op0 .none) fun no => .op1 .some no)

end Program

/-! ### Costs and sizes -/

section Costs

/-- The cost of the twins flag on `m` points. -/
def twinsFlagCost (k m : ℕ) : ℕ := wlCost k m + 1 + (9 * m + 18) + goodListCost k m + 2

/-- The bound on the number of structures for `y`: at most `k (m^k + 1)` good lists, each with
at most `Z + 1` structures. -/
def c3R (k m Z : ℕ) : ℕ := k * (m ^ k + 1) * (Z + 1)

/-- **The cost of Case 3**: `g` generators of `G`, `|Vx| = mx`, `|Vy| = my`, `kX` generators of
the first structure, `Ccol` the cost of the colourings, `Cx`, `Cy` the costs per good list for
`x` and `y`, `soj` trees of size at most `Z`, and Align's charges. -/
def c3Cost (n N s g k mx my kX Ccol Cx Cy Z BgP Bmem Bk Bl Bg1 Bgen Cb : ℕ) : ℕ :=
  mx + my + 6 + (Ccol + 5 + twinsFlagCost k mx + 1 +
    (pipePrefixCost k mx + Cx + 4 + 1 + structsCost k my Cy Z +
      alignCost n N g kX (c3R k my Z) (outGensCost (N - n) (leafB (N - n)) (leafB (N - n)))
        (outIsoCost (N - n) (leafB (N - n)) (leafB (N - n)) (leafB (N - n))) BgP Bmem Bk Bl Bg1
        Bgen Cb s + 1))

/-- The cost of the structures at one good list, uniformly: the prefix, and both outcomes with
the largest class and `soj` trees of size at most `Z`. -/
def c3OutCost (M k m Z : ℕ) : ℕ :=
  outPrefixCost k m k + (smallLeafCost m + Case2b.extCost M m m + 2) + domCost M k m m Z

theorem c3p_alignCost_mono {n N g k k' r r' cG cI BgP Bmem Bk Bl Bg1 Bgen Cb s : ℕ} (hk : k ≤ k')
    (hr : r ≤ r') :
    alignCost n N g k r cG cI BgP Bmem Bk Bl Bg1 Bgen Cb s ≤
      alignCost n N g k' r' cG cI BgP Bmem Bk Bl Bg1 Bgen Cb s := by
  unfold alignCost alignCallCost isoInPCost stabInPCost preCost
  gcongr

theorem domCost_mono {M k m s s' sz sz' : ℕ} (hs : s ≤ s') (hz : sz ≤ sz') :
    domCost M k m s sz ≤ domCost M k m s' sz' := by
  unfold domCost leavesOfCost sojBranchCost disconnCost compPartCost offColsCost compCost
    stepCost stepK opCost extendOutCost exBlkCost addPieceCost trimCost skelCost
    Toolkit.matrixCost Case2b.extCost outB
  gcongr

/-- **The cost per good list is uniform**: for a list of at most `k` points and a `soj` tree of
size at most `Z`. -/
theorem outCostD_le (M k : ℕ) (V : List ℕ) (W : Array ℕ) {z : List ℕ} (hz : z.length ≤ k)
    {Z : ℕ} (hZ : outSzD k V W z ≤ Z) : outCostD M k V W z ≤ c3OutCost M k V.length Z := by
  have hp : outPrefixCost k V.length z.length ≤ outPrefixCost k V.length k := by
    unfold outPrefixCost
    omega
  unfold outCostD c3OutCost
  unfold outSzD at hZ
  split
  · exact Nat.le_add_right_of_le (Nat.add_le_add_right hp _)
  · rename_i u₀ hu
    rw [hu] at hZ
    dsimp only at hZ
    have hs : (classB V (classA (col1D k V.length W z) u₀)).length ≤ V.length := by
      rw [length_classB, classA]
      exact (List.length_filter_le _ _).trans (by simp [length_col1D])
    have := domCost_mono (M := M) (k := k) (m := V.length) hs hZ
    omega

/-- A duplicate-free list of points below `M` has at most `M` points. -/
theorem c3p_length_le {M : ℕ} {V : List ℕ} (hV : ∀ v ∈ V, v < M) (hnd : V.Nodup) :
    V.length ≤ M := by
  have := (List.subperm_of_subset hnd fun v hv => List.mem_range.2 (hV v hv)).length_le
  simpa using this

theorem outSize_allStructsD_le {M k : ℕ} {V : List ℕ} {col : Array ℕ} (hVM : V.length ≤ M)
    {o : OutD} (ho : o ∈ allStructsD M k V col) : outSize o ≤ leafB M := by
  obtain ⟨z, -, hoz⟩ := mem_allStructsD.1 ho
  refine (outSize_outcomeD_le M k V _ z o hoz).trans ?_
  unfold leafB
  have := c3p_outB_mono hVM (Nat.add_le_add_right hVM 2)
  omega

end Costs

/-! ### Validity and liveness without the twin hypothesis -/

section Model

variable {M k : ℕ} {V : List ℕ}

/-- **Every leaf of the model tree is valid**, with no hypothesis on twins: validity holds at
every good list (`outTree_spec`); only liveness needs a good list to exist. -/
theorem c3p_case3Tree_valid {Γ : Type*} [Fintype Γ] [DecidableEq Γ] {m : ℕ}
    (c : (Fin k → Fin m) → ℕ) (e : Fin m ↪ Γ) (hm : 6 ≤ m) :
    (case3Tree c e).AllLeaves ValidLeaf := by
  intro ch hch
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hch
  show (outTree _ e (zOf e (zChoice e z))).AllLeaves ValidLeaf
  rw [zOf_zChoice]
  exact (outTree_spec _ (wl_isCoherent c) e hm (Finset.mem_filter.1 hz).2).2.2

/-- **Every listed structure is valid**, with no hypothesis on twins. -/
theorem c3p_allStructsD_valid (hV : ∀ v ∈ V, v < M) (hnd : V.Nodup) (col : Array ℕ)
    (hm : 6 ≤ V.length) : ∀ o ∈ allStructsD M k V col, OutValid M o := by
  intro o ho
  have hreach : (case3Tree (toFun (k := k) col) (lkE V hV hnd)).Reach (decodeOut M o) := by
    rw [← CTree.mem_leafMs, ← allStructsD_leafMs hV hnd col, Multiset.mem_coe]
    exact List.mem_map_of_mem ho
  exact lk_outValid (CTree.allLeaves_iff_reach.1
    (c3p_case3Tree_valid _ _ hm) _ hreach) (c3l_shape hV hnd col o ho)

/-- **The first structure exists** when the twins flag is not set. -/
theorem c3p_firstStructD_ne_none (hV : ∀ v ∈ V, v < M) (hnd : V.Nodup) (col : Array ℕ)
    (hm : 6 ≤ V.length) (htw : twinsD k V.length col = false) :
    firstStructD M k V col ≠ none := by
  have hne : goodListsD k V.length (wlCD k V.length col) ≠ [] := by
    unfold twinsD at htw
    intro h
    rw [h] at htw
    exact absurd htw (by decide)
  unfold firstStructD
  rcases hg : goodListsD k V.length (wlCD k V.length col) with _ | ⟨zd, rest⟩
  · exact absurd hg hne
  have hzd : zd ∈ goodListsD k V.length (wlCD k V.length col) := by
    rw [hg]
    exact List.mem_cons_self
  obtain ⟨x, -, rfl, hgood⟩ := mem_goodListsD.1 hzd
  have hc := c3l_outcome (M := M) (k := k) hV hnd col x
  have hlive := (outTree_spec (wl k V.length (toFun col)).1 (wl_isCoherent _) (lkE V hV hnd) hm
    (by rw [← toFun_wlCD]; exact hgood)).1
  have hcount := (CTree.meas_size_live hlive).2
  show (outcomeD M k V (wlCD k V.length col) (x.map Fin.val)).head? ≠ none
  rw [Ne, List.head?_eq_none_iff]
  intro hnil
  rw [hnil, List.map_nil] at hc
  have h0 := congrArg Multiset.card hc
  rw [CTree.card_leafMs] at h0
  rw [← h0] at hcount
  simp at hcount

end Model

/-! ### The specification -/

section Spec

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}

/-- **Different numbers of points outside the supports**: no isomorphism, `some none`. -/
theorem RunsWithin.case3Prog_ne
    (sub : InstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)) (n k : ℕ)
    (xy : StrData × StrData) (w : WinData) (G : (Ty.group D).denote) {Vx Vy : List ℕ}
    (hlen : Vx.length ≠ Vy.length) :
    RunsWithin X body (Case3.case3Prog sub n k xy w G Vx Vy) (some none)
      (Vx.length + Vy.length + 8) := by
  apply RunsWithin.mono
  case h =>
    unfold Case3.case3Prog
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_with RunsWithin.ite_neg (show (Vx.length == Vy.length) = false by simp [hlen]) _
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim _ _
  case hc =>
    simp only [Prim.cost, Args.head_cons]
    omega

/-- **Case 3**, with the hypotheses that the colourings and the model provide: the run of the
colourings `cX`, `cY` (when `|Vx| = |Vy|`), no isomorphism when `|Vx| ≠ |Vy|`, the validity of
the structures, the alignment hypothesis of `alignProg` for the first structure of `x`, and
uniform bounds `Cx`, `Cy` on the cost and `Z` on the `soj` size per good list. The result is
`none` (the fallback) only when the twins flag of `x`'s colouring is set, and every answer is
correct for `G`, under `SubSolves` for the aligned cosets. -/
theorem RunsWithin.case3Prog (hO : MeetsContractOn DV alignOps X.O)
    (hPre : ∀ op x, alignOps op → GroupPre DV op x → X.Pre op x)
    {n N : ℕ} {gs : GensData} {d : D.denote} (hGv : GroupValid DV N gs d)
    (hG : IsInvariant (GensData.denote N gs) (baseSet n N))
    (halt : alternatingGroup (Fin (N - n)) ≤ (baseHom _ n hG).range)
    {xy : StrData × StrData} {w : WinData} (hw : w.Valid N)
    (hWG : IsInvariant (GensData.denote N gs) (w.denote N))
    {k : ℕ} {Vx Vy : List ℕ} (hVx : ∀ v ∈ Vx, v < N - n) (hVxn : Vx.Nodup) (hm : 6 ≤ Vx.length)
    (hdiff : Vx.length ≠ Vy.length →
      iso (w.denote N) 1 (GensData.denote N gs) (xy.1.denote N) (xy.2.denote N) = ∅)
    {sub : InstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)}
    {cX cY : Array ℕ} {Ccol : ℕ}
    (hcol : Vx.length = Vy.length →
      RunsWithin X body (Case3.tupleColProg sub n N k Vx Vy xy.1 xy.2 (N, gs, d)) (cX, cY) Ccol)
    {Cx Cy Z : ℕ}
    (hCx : ∀ z ∈ goodListsD k Vx.length (wlCD k Vx.length cX),
      outCostD (N - n) k Vx (wlCD k Vx.length cX) z ≤ Cx)
    (hCy : ∀ z ∈ goodListsD k Vy.length (wlCD k Vy.length cY),
      outCostD (N - n) k Vy (wlCD k Vy.length cY) z ≤ Cy)
    (hZ : ∀ z ∈ goodListsD k Vy.length (wlCD k Vy.length cY),
      outSzD k Vy (wlCD k Vy.length cY) z ≤ Z)
    (hXv : ∀ X₀, firstStructD (N - n) k Vx cX = some X₀ → OutValid (N - n) X₀)
    (hYv : ∀ Y ∈ allStructsD (N - n) k Vy cY, OutValid (N - n) Y)
    (halign : Vx.length = Vy.length → ∀ X₀, firstStructD (N - n) k Vx cX = some X₀ →
      ∀ g ∈ iso (w.denote N) 1 (GensData.denote N gs) (xy.1.denote N) (xy.2.denote N),
        ∃ Y ∈ allStructsD (N - n) k Vy cY, ∃ h : g ∈ GensData.denote N gs,
          baseHom _ n hG ⟨g, h⟩ • decodeOut (N - n) X₀ = decodeOut (N - n) Y)
    {s BgP Bmem Bk Bl Bg1 Bgen Cb : ℕ}
    (hBgP : X.B.call GroupOp.generate (N - n, gs.map (baseD n N))
      (X.O.run GroupOp.generate (N - n, gs.map (baseD n N))) ≤ BgP)
    (hBmem : ∀ g : PermData, g.Valid (N - n) → X.B.call GroupOp.mem (pModel X.O n (N, gs, d), g)
      (X.O.run GroupOp.mem (pModel X.O n (N, gs, d), g)) ≤ Bmem)
    (hBk : X.B.call GroupOp.kernel ((N, gs, d), baseWin n N) (kerModel X.O n (N, gs, d)) ≤ Bk)
    (hBl : ∀ π : PermData, X.B.call GroupOp.lift ((N, gs, d), (baseWin n N, π))
      (liftModel X.O n (N, gs, d) π) ≤ Bl)
    (hBg1 : ∀ X₀ : OutD, firstStructD (N - n) k Vx cX = some X₀ →
      X.B.call GroupOp.generate
        (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d)) (outGensD (N - n) X₀))).map
          (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
        (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (outGensD (N - n) X₀)))) ≤ Bg1)
    (hBgen : ∀ gs' : GensData, GensData.AllValid N gs' →
      gs'.length ≤ c3R k Vy.length Z * (s + 1) →
      GensData.denote N gs' ≤ GensData.denote N gs →
      X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ Bgen)
    (hsub : ∀ X₀ : OutD, firstStructD (N - n) k Vx cX = some X₀ →
      SubSolves X body DV sub (fun I => I.1 = xy ∧ I.2.1 = w ∧
        I.2.2.2 = preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (outGensD (N - n) X₀))) ∧ I.Valid DV) (fun _ => Cb) s) :
    ∃ res : Option (AnswerData D),
      RunsWithin X body (Case3.case3Prog sub n k xy w (N, gs, d) Vx Vy) res
        (c3Cost n N s gs.length k Vx.length Vy.length (outGensB (N - n)) Ccol Cx Cy Z BgP Bmem
          Bk Bl Bg1 Bgen Cb) ∧
      (res = none → Vx.length = Vy.length ∧ twinsD k Vx.length cX = true) ∧
      ∀ ans, res = some ans →
        AnsOK DV N (w.denote N) 1 (GensData.denote N gs) (xy.1.denote N) (xy.2.denote N) ans ∧
        ∀ sGen, (∀ gs', GensData.AllValid N gs' →
            GensData.denote N gs' ≤ GensData.denote N gs →
            (X.O.run GroupOp.generate (N, gs')).2.1.length ≤ sGen) →
          ∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sGen := by
  have hVxM := c3p_length_le hVx hVxn
  by_cases hlen : Vx.length = Vy.length
  swap
  · -- different numbers of points outside the supports: no isomorphism
    refine ⟨some none, (RunsWithin.case3Prog_ne sub n k xy w (N, gs, d) hlen).mono
      (by unfold c3Cost; omega), (fun h => by cases h), fun ans h => ?_⟩
    cases h
    exact ⟨hdiff hlen, fun _ _ c hc => by cases hc⟩
  have hc := hcol hlen
  by_cases htw : twinsD k Vx.length cX = true
  · -- the fallback
    refine ⟨none, ?_, fun _ => ⟨hlen, htw⟩, fun _ h => by cases h⟩
    apply RunsWithin.mono
    case h =>
      unfold Case3.case3Prog
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_with RunsWithin.ite_pos (show (Vx.length == Vy.length) = true by simp [hlen]) _
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step hc
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.twinsFlagProg k Vx.length cX)
      run_with RunsWithin.ite_pos htw _
      exact RunsWithin.prim _ _
    case hc =>
      simp only [Prim.cost, Args.head_cons, c3Cost, twinsFlagCost]
      omega
  -- the aligned branch
  have htw' : twinsD k Vx.length cX = false := by simpa using htw
  obtain ⟨X₀, hfirst⟩ := Option.ne_none_iff_exists'.1
    (c3p_firstStructD_ne_none (M := N - n) hVx hVxn cX hm htw')
  have hfs := RunsWithin.firstStructProg (X := X) (body := body) (N - n) k Vx cX hCx
  rw [hfirst] at hfs
  have has := RunsWithin.allStructsProg (X := X) (body := body) (N - n) k Vy cY hCy hZ
  set Ys := allStructsD (N - n) k Vy cY with hYs
  have hmL : N - n ≤ leafB (N - n) := by
    rw [leafB]
    omega
  have hspec : (outOps (N - n)).Spec fun o => OutValid (N - n) o ∧ outSize o ≤ leafB (N - n) :=
    cp2_spec_mono (outOps_spec (N - n)) fun _ h => h.1
  have hgensP : ∀ o, OutValid (N - n) o ∧ outSize o ≤ leafB (N - n) →
      RunsWithin X body (Case2b.outGensProg (N - n) o) ((outOps (N - n)).gens o)
        (outGensCost (N - n) (leafB (N - n)) (leafB (N - n))) := fun o ho =>
    RunsWithin.outGensProg (N - n) o (fun _ v => (outSize_blk o v).trans ho.2) hmL
      fun _ => cp2_jbound_le ho.2
  have hisoP : ∀ o o', OutValid (N - n) o ∧ outSize o ≤ leafB (N - n) →
      OutValid (N - n) o' ∧ outSize o' ≤ leafB (N - n) →
      RunsWithin X body (Case2b.outIsoProg (N - n) o o') ((outOps (N - n)).iso o o')
        (outIsoCost (N - n) (leafB (N - n)) (leafB (N - n)) (leafB (N - n))) := fun o o' ho ho' =>
    RunsWithin.outIsoProg (N - n) o o' (fun _ v => (outSize_blk o v).trans ho.2)
      (fun _ v => (outSize_blk o' v).trans ho'.2) hmL (fun _ => cp2_jbound_le ho.2)
      fun _ => cp2_jbound_le ho'.2
  have hX : OutValid (N - n) X₀ ∧ outSize X₀ ≤ leafB (N - n) :=
    ⟨hXv X₀ hfirst, outSize_allStructsD_le hVxM (firstStructD_mem hfirst)⟩
  have hYv' : ∀ Y ∈ Ys, OutValid (N - n) Y ∧ outSize Y ≤ leafB (N - n) := fun Y hY =>
    ⟨hYv Y hY, outSize_allStructsD_le (hlen ▸ hVxM) hY⟩
  have hYlen : Ys.length ≤ c3R k Vy.length Z := length_allStructsD_le (N - n) Vy cY hZ
  have hBgen' : ∀ gs' : GensData, GensData.AllValid N gs' → gs'.length ≤ Ys.length * (s + 1) →
      GensData.denote N gs' ≤ GensData.denote N gs →
      X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ Bgen :=
    fun gs' hv hl hle => hBgen gs' hv (hl.trans (Nat.mul_le_mul_right _ hYlen)) hle
  obtain ⟨ans, hrun, hok, hgen⟩ := RunsWithin.alignProg (body := body) (τ := outTy)
    (O := Option (Out (Fin (N - n)))) hO hPre hGv hG halt (S := outOps (N - n)) hspec hgensP
    hisoP hX hYv' hw hWG (halign hlen X₀ hfirst) hBgP hBmem hBk hBl (hBg1 X₀ hfirst) hBgen'
    (hsub X₀ hfirst)
  refine ⟨some ans, ?_, (fun h => by cases h), fun ans' h => ?_⟩
  · apply RunsWithin.mono
    case h =>
      unfold Case3.case3Prog
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_with RunsWithin.ite_pos (show (Vx.length == Vy.length) = true by simp [hlen]) _
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step hc
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.twinsFlagProg k Vx.length cX)
      run_with RunsWithin.ite_neg htw' _
      run_step hfs
      run_with RunsWithin.caseOption_some _
      run_step has
      run_step hrun
      exact RunsWithin.prim _ _
    case hc =>
      have hk := length_outGensD_le (hXv X₀ hfirst)
      have := c3p_alignCost_mono (n := n) (N := N) (g := gs.length)
        (cG := outGensCost (N - n) (leafB (N - n)) (leafB (N - n)))
        (cI := outIsoCost (N - n) (leafB (N - n)) (leafB (N - n)) (leafB (N - n))) (BgP := BgP)
        (Bmem := Bmem) (Bk := Bk) (Bl := Bl) (Bg1 := Bg1) (Bgen := Bgen) (Cb := Cb) (s := s) hk
        hYlen
      have e : ((outOps (N - n)).gens X₀).length = (outGensD (N - n) X₀).length := rfl
      simp only [Prim.cost, Args.head_cons, c3Cost, twinsFlagCost] at this ⊢
      rw [e]
      clear_value Ys
      clear * - this
      omega
  · cases h
    exact ⟨hok, hgen⟩

end Spec

/-! ### Canonicity: the supports and the renumbering -/

section Canonical

variable {N n : ℕ}

/-- **The fixed points of the base actions move with an isomorphism**: if `F(y)` is `F(x)`
conjugated by `g`, then `σ v` is fixed by `ψ(F(y))` exactly when `v` is fixed by `ψ(F(x))`, for
the base action `σ` of `g`. -/
theorem c3p_fix_iff {G Fx Fy : Subgroup (Perm (Fin N))} (hG : IsInvariant G (baseSet n N))
    (hFx : IsInvariant Fx (baseSet n N)) (hFy : IsInvariant Fy (baseSet n N))
    {g : Perm (Fin N)} (hgG : g ∈ G) (hy : Fy = Fx.map (MulAut.conj g).toMonoidHom)
    (v : Fin (N - n)) :
    (∀ f ∈ (baseHom Fy n hFy).range,
        f (baseHom G n hG ⟨g, hgG⟩ v) = baseHom G n hG ⟨g, hgG⟩ v) ↔
      ∀ f ∈ (baseHom Fx n hFx).range, f v = v := by
  have hP := cp2_range_conj hG hFx hFy hgG hy
  set σ := baseHom G n hG ⟨g, hgG⟩
  constructor
  · intro h f hf
    have e : σ⁻¹ * (σ * f * σ⁻¹) * σ = f := by group
    have hf' : σ * f * σ⁻¹ ∈ (baseHom Fy n hFy).range := by
      rw [hP, e]
      exact hf
    have := h _ hf'
    simp only [Perm.mul_apply, perm_inv_apply_self] at this
    exact σ.injective this
  · intro h f hf
    have := h _ ((hP f).1 hf)
    simp only [Perm.mul_apply] at this
    exact (Perm.inv_eq_iff_eq).1 this

/-- Lists of points related by a permutation have the same length. -/
theorem c3p_length_eq {M : ℕ} {Vx Vy : List ℕ} (hVx : ∀ v ∈ Vx, v < M) (hVxn : Vx.Nodup)
    (hVy : ∀ v ∈ Vy, v < M) (hVyn : Vy.Nodup) (σ : Perm (Fin M))
    (hσ : ∀ v : Fin M, (σ v).val ∈ Vy ↔ v.val ∈ Vx) : Vx.length = Vy.length := by
  rw [← card_setOf hVxn hVx, ← card_setOf hVyn hVy]
  have e : setOf M Vy = (setOf M Vx).map σ.toEmbedding := by
    ext v
    rw [mem_setOf, Finset.mem_map]
    constructor
    · intro hv
      refine ⟨σ⁻¹ v, mem_setOf.2 ((hσ _).1 ?_), ?_⟩
      · rwa [perm_apply_inv_self]
      · simp
    · rintro ⟨u, hu, rfl⟩
      exact (hσ u).2 (mem_setOf.1 hu)
  rw [e, Finset.card_map]

/-- **The renumbering induced by a permutation** carrying the points of `Vx` onto those of
`Vy`. -/
theorem c3p_renumber {M : ℕ} {Vx Vy : List ℕ} (hVx : ∀ v ∈ Vx, v < M) (hVxn : Vx.Nodup)
    (hVy : ∀ v ∈ Vy, v < M) (hVyn : Vy.Nodup) (hlen : Vx.length = Vy.length)
    (σ : Perm (Fin M)) (hσ : ∀ v : Fin M, (σ v).val ∈ Vy ↔ v.val ∈ Vx) :
    ∃ π : Perm (Fin Vx.length),
      ∀ a, lkE Vy hVy hVyn (Fin.cast hlen (π a)) = σ (lkE Vx hVx hVxn a) := by
  have hex : ∀ a : Fin Vx.length, ∃ j, lkE Vy hVy hVyn j = σ (lkE Vx hVx hVxn a) := fun a =>
    (lkE_range Vy hVy hVyn _).2 ((hσ _).2 ((lkE_range Vx hVx hVxn _).1 ⟨a, rfl⟩))
  choose f hf using hex
  have hinj : Function.Injective fun a => Fin.cast hlen.symm (f a) := by
    intro a₁ a₂ h
    have h' : f a₁ = f a₂ := Fin.cast_injective _ h
    have := congrArg (lkE Vy hVy hVyn) h'
    rw [hf, hf] at this
    exact (lkE Vx hVx hVxn).injective (σ.injective this)
  refine ⟨Equiv.ofBijective _ (Finite.injective_iff_bijective.1 hinj), fun a => ?_⟩
  simp [hf]

theorem c3p_toFun_cast {k m m' : ℕ} (h : m' = m) (col : Array ℕ) (T : Fin k → Fin m') :
    toFun col T = toFun col (Fin.cast h ∘ T) := by
  subst h
  rfl

/-- **Alignment on data.** If `σ` carries the points of `Vx` onto those of `Vy`, with
renumbering `π`, and the colourings are related by `π`, then `σ` carries the first structure
of `x` to a structure of `y` (`case3_reach`, `allStructsD_leafMs`, `firstStructD_reach`). -/
theorem c3p_align {M k : ℕ} {Vx Vy : List ℕ} (hVx : ∀ v ∈ Vx, v < M) (hVxn : Vx.Nodup)
    (hVy : ∀ v ∈ Vy, v < M) (hVyn : Vy.Nodup) (hlen : Vx.length = Vy.length)
    (σ : Perm (Fin M)) (hσ : ∀ v : Fin M, (σ v).val ∈ Vy ↔ v.val ∈ Vx)
    (π : Perm (Fin Vx.length))
    (hπ : ∀ a, lkE Vy hVy hVyn (Fin.cast hlen (π a)) = σ (lkE Vx hVx hVxn a))
    {cX cY : Array ℕ} (hcol : ∀ T : Fin k → Fin Vx.length, toFun cY (⇑π ∘ T) = toFun cX T)
    {X₀ : OutD} (hfirst : firstStructD M k Vx cX = some X₀) :
    ∃ Y ∈ allStructsD M k Vy cY, σ • decodeOut M X₀ = decodeOut M Y := by
  have hreach := firstStructD_reach hVx hVxn cX hfirst
  have hreach' := case3_reach σ hlen.symm (toFun (k := k) cX) (toFun (k := k) cY)
    (lkE Vx hVx hVxn) (lkE Vy hVy hVyn) (fun v => ?_) (fun T T' hT => ?_) hreach
  · rw [← CTree.mem_leafMs, ← allStructsD_leafMs hVy hVyn cY, Multiset.mem_coe] at hreach'
    obtain ⟨Y, hY, hYe⟩ := List.mem_map.1 hreach'
    exact ⟨Y, hY, hYe.symm⟩
  · rw [lkE_range, lkE_range]
    have := hσ (σ⁻¹ v)
    rwa [perm_apply_inv_self] at this
  · have hT' : Fin.cast hlen.symm ∘ T' = ⇑π ∘ T := funext fun i => by
      have h1 := (lkE Vy hVy hVyn).injective ((hT i).trans (hπ (T i)).symm)
      simp [h1]
    rw [c3p_toFun_cast hlen.symm cY T', hT', hcol]

end Canonical

/-! ### The colourings of certificate equivalence -/

section Colourings

variable {N n : ℕ} {G : Subgroup (Perm (Fin N))} {hC : CertSetting G n}

/-- The comparisons `c` decide certificate equivalence on the repetition-free digit lists, for
the tuples of `l` (for `xs`) and of `l'` (for `xs'`). -/
def ColChar (φ : strGroup hC →* Perm (Fin (N - n))) (xs xs' : Fin n → ℕ) (k m : ℕ)
    (l l' : List ℕ) (c : List ℕ → List ℕ → Bool) : Prop :=
  ∀ di ∈ Coherent.tupList k m, ∀ dt ∈ Coherent.tupList k m, di.Nodup → dt.Nodup →
    (c di dt = true ↔ CertIsoL φ xs xs' k (tupD l di) (tupD l' dt))

/-- `X₀` is the first structure of `x` for a colouring of the `k`-tuples of `Vx` by certificate
equivalence. -/
def C3First (φ : strGroup hC →* Perm (Fin (N - n))) (xs : Fin n → ℕ) (M k : ℕ) (Vx : List ℕ)
    (X₀ : OutD) : Prop :=
  ∃ cXX, ColChar φ xs xs k Vx.length Vx Vx cXX ∧
    firstStructD M k Vx (colXD cXX k Vx.length) = some X₀

/-- **The fallback condition**: the colouring of the `k`-tuples of `Vx` by certificate
equivalence has more than `t` pairwise twins. -/
def C3Twins (φ : strGroup hC →* Perm (Fin (N - n))) (xs : Fin n → ℕ) (k : ℕ) (Vx : List ℕ) :
    Prop :=
  ∃ cXX, ColChar φ xs xs k Vx.length Vx Vx cXX ∧
    ∃ T : Finset (Fin Vx.length), tOf Vx.length < T.card ∧
      ∀ u ∈ T, ∀ v ∈ T, IsTwin (toFun (k := k) (colXD cXX k Vx.length)) u v

/-- An isomorphism carries `x` to `y` on the string positions, when they lie in the window. -/
theorem c3p_strOn_iso (hC : CertSetting G n) {W : Set (Fin N)}
    (hwS : ∀ u : Fin N, u.val < n → u ∈ W) {x y : Fin N → ℕ} {g : Perm (Fin N)}
    (hg : g ∈ iso W 1 G x y) (j : Fin n) :
    strOn hC.le y (strR hC ⟨g, (mem_iso_one.1 hg).1⟩ • j) = strOn hC.le x j := by
  have hm := (mem_iso_one.1 hg).2
  have hj : (⟨j.val, by have := hC.le; omega⟩ : Fin N) ∈ W := hwS _ j.2
  have h := hm _ hj
  simp only [strOn]
  rw [h]
  congr 1

/-- The renumbering `π` of `Vx` onto `Vy` as `tupleCol_iso` needs it: the base action of `g`
carries the `a`-th point of `Vx` to the `π a`-th point of `Vy`. -/
theorem c3p_hπ {φ : strGroup hC →* Perm (Fin (N - n))} (hφ : IsPhi hC φ) {g : Perm (Fin N)}
    (hgG : g ∈ G) {Vx Vy : List ℕ} (hVx : ∀ v ∈ Vx, v < N - n) (hVxn : Vx.Nodup)
    (hVy : ∀ v ∈ Vy, v < N - n) (hVyn : Vy.Nodup) (hlen : Vx.length = Vy.length)
    {π : Perm (Fin Vx.length)}
    (hπ : ∀ a, lkE Vy hVy hVyn (Fin.cast hlen (π a)) =
      baseHom G n hC.base ⟨g, hgG⟩ (lkE Vx hVx hVxn a))
    (a : Fin Vx.length) (h : Vx.getD a 0 < N - n) :
    Vy.getD (π a) 0 = (φ (strR hC ⟨g, hgG⟩) ⟨Vx.getD a 0, h⟩ : ℕ) := by
  have h1 : (⟨Vx.getD a 0, h⟩ : Fin (N - n)) = lkE Vx hVx hVxn a := by
    apply Fin.ext
    show Vx.getD a 0 = (lkE Vx hVx hVxn a).val
    rw [lkE_val, List.getD_eq_getElem _ _ a.2]
    rfl
  have h2 : Vy.getD (π a) 0 = (lkE Vy hVy hVyn (Fin.cast hlen (π a))).val := by
    rw [lkE_val, List.getD_eq_getElem]
    rfl
  rw [hφ, h1, h2, hπ]

/-- **The colouring of `x` is `SameColour` along the numbering of `Vx`.** -/
theorem c3p_sameColour (φ : strGroup hC →* Perm (Fin (N - n))) {xs : Fin n → ℕ} {k : ℕ}
    {Vx : List ℕ} (hVx : ∀ v ∈ Vx, v < N - n) (hVxn : Vx.Nodup) {cXX : List ℕ → List ℕ → Bool}
    (hXX : ColChar φ xs xs k Vx.length Vx Vx cXX) (T T' : Fin k → Fin Vx.length) :
    toFun (colXD cXX k Vx.length) T = toFun (colXD cXX k Vx.length) T' ↔
      SameColour φ xs (⇑(lkE Vx hVx hVxn) ∘ T) (⇑(lkE Vx hVx hVxn) ∘ T') := by
  have he : ∀ U : Fin k → Fin Vx.length, ∀ hU : ∀ i < k,
      (tupD Vx (Coherent.digits U)).getD i 0 < N - n,
      tupleD (N - n) k (tupD Vx (Coherent.digits U)) hU = ⇑(lkE Vx hVx hVxn) ∘ U := by
    intro U hU
    funext i
    apply Fin.ext
    simp only [tupleD, Function.comp_apply, lkE_val]
    rw [getD_tupD_digits U i.2, List.getD_eq_getElem _ _ (U _).2]
    rfl
  have hinj : ∀ U : Fin k → Fin Vx.length,
      Function.Injective (⇑(lkE Vx hVx hVxn) ∘ U) ↔ Function.Injective U := fun U =>
    (lkE Vx hVx hVxn).injective.of_comp_iff U
  rw [colX_eq_iff φ rfl hVx hXX T T', SameColour, hinj, hinj]
  have hT := c3c_tupD_lt rfl hVx T
  have hT' := c3c_tupD_lt rfl hVx T'
  rw [certIsoL_iff φ hT hT', he T hT, he T' hT']

/-- **No fallback under the thresholds.** If the points of `Vx` are exactly those outside the
support of the full group `fullGroupK φ k xs`, the thresholds of the CFSG-free interface leave
fewer than `k` pairwise twins in the colouring by certificate equivalence
(`no_twins_of_thresholds`), so with `k ≤ t` the fallback condition fails. -/
theorem case3_no_fallback (φ : strGroup hC →* Perm (Fin (N - n))) {K : ℕ → ℕ} {k : ℕ}
    (xs : Fin n → ℕ) (hT : Thresholds K n k) {Vx : List ℕ} (hVx : ∀ v ∈ Vx, v < N - n)
    (hVxn : Vx.Nodup) (hsupp : ∀ v : Fin (N - n), v ∉ supp φ (fullGroupK φ k xs) ↔ v.val ∈ Vx)
    (hkt : k ≤ tOf Vx.length) : ¬ C3Twins φ xs k Vx := by
  rintro ⟨cXX, hXX, T, hT₀, htw⟩
  have h := htw_of_thresholds φ xs (by rwa [Fintype.card_fin]) (lkE Vx hVx hVxn)
    (fun v => by rw [hsupp, lkE_range]) (fun T T' => c3p_sameColour φ hVx hVxn hXX T T') hkt T htw
  exact absurd h (not_le.2 hT₀)

end Colourings

/-! ### The canonical specification -/

section CanonicalSpec

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}

/-- The operations of Case 3: the certificate comparisons and Align. -/
def c3Ops (op : GroupOp) : Prop := certOps op ∨ alignOps op

/-- **The cost of Case 3, closed**: `c3Cost` with the colourings at `tupleColCost` (each
comparison of cost `CI`), `outGensB (N - n)` generators for the first structure, and the
uniform cost `c3OutCost` per good list for `soj` trees of size at most `Z`. -/
def c3CostC (n N s g k mx my CI Z BgP Bmem Bk Bl Bg1 Bgen Cb : ℕ) : ℕ :=
  c3Cost n N s g k mx my (outGensB (N - n)) (tupleColCost N k mx CI) (c3OutCost (N - n) k mx Z)
    (c3OutCost (N - n) k my Z) Z BgP Bmem Bk Bl Bg1 Bgen Cb

/-- **Case 3, canonical form.** `F` is a canonical map of the strings into subgroups of `G`
(local on the window, `F (relabel g x) = g F(x) g⁻¹`), `Fx`, `Fy` are `F(x)`, `F(y)`, and `Vx`,
`Vy` list the points of the base fixed by `ψ(F(x))`, `ψ(F(y))`. The string positions lie in the
window. The comparisons run under stage 14e's sub-solver hypotheses (`StepSubP`, cost `Cc`),
Align under `SubSolves` for the aligned cosets of the first structure of `x` (cost `Cb`). Then
the program runs within the closed cost `c3CostC` (with `Z = sojZ (N - n)`); it falls back
(`none`) only when the colouring of `x` by certificate equivalence has more than `t` pairwise
twins (`C3Twins`), and every answer is correct for `G`. -/
theorem RunsWithin.case3Prog_canonical (hO : MeetsContractOn DV c3Ops X.O)
    (hPre : ∀ op x, c3Ops op → GroupPre DV op x → X.Pre op x)
    {n N : ℕ} {gs : GensData} {hC : CertSetting (GensData.denote N gs) n}
    {φ : strGroup hC →* Perm (Fin (N - n))} (hφ : IsPhi hC φ) {d : D.denote}
    (hGv : GroupValid DV N gs d)
    (halt : alternatingGroup (Fin (N - n)) ≤ (baseHom _ n hC.base).range)
    {xy : StrData × StrData} {w : WinData} (hw : w.Valid N)
    (hWG : IsInvariant (GensData.denote N gs) (w.denote N))
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
    (hm : 6 ≤ Vx.length) {k : ℕ} (h5 : 5 ≤ k) (hk : k + 2 ≤ N - n)
    {s : ℕ} {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N s G₀) (hs : gs.length ≤ s)
    (hGG₀ : GensData.denote N gs ≤ G₀) {sk : ℕ} (Bk : BackendBounds X DV k sk ⊤)
    (hsk : s ≤ k * (sk + 1)) {Bgk Bl Bgs : ℕ}
    (hBgk : ∀ gs' : GensData, GensData.AllValid N gs' →
      gs'.length ≤ k.factorial * (s + 1) → GensData.denote N gs' ≤ GensData.denote N gs →
        X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ Bgk)
    (hBl : ∀ π : PermData, X.B.call GroupOp.lift ((N, gs, d), (baseWin n N, π))
      (liftModel X.O n (N, gs, d) π) ≤ Bl)
    (hBgs : ∀ al : List ℕ, al.Nodup → al.length = k → (∀ a ∈ al, a < N - n) → ∀ b₁ b₂,
      X.B.call GroupOp.generate (N, giantGens X.O n (N, gs, d) al b₁ b₂)
        (giantSetStabModel X.O n (N, gs, d) al b₁ b₂) ≤ Bgs)
    {sub : InstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)} {Cc : ℕ}
    (hsubXX : SubSolves X body DV sub
      (StepSubP (DV := DV) (GensData.denote N gs) (xy.1, xy.1) n k s) (fun _ => Cc) s)
    (hsubXY : SubSolves X body DV sub
      (StepSubP (DV := DV) (GensData.denote N gs) (xy.1, xy.2) n k s) (fun _ => Cc) s)
    (hsubYY : SubSolves X body DV sub
      (StepSubP (DV := DV) (GensData.denote N gs) (xy.2, xy.2) n k s) (fun _ => Cc) s)
    {BgP Bmem Bker Bg1 Bgen Cb : ℕ}
    (hBgP : X.B.call GroupOp.generate (N - n, gs.map (baseD n N))
      (X.O.run GroupOp.generate (N - n, gs.map (baseD n N))) ≤ BgP)
    (hBmem : ∀ g : PermData, g.Valid (N - n) → X.B.call GroupOp.mem (pModel X.O n (N, gs, d), g)
      (X.O.run GroupOp.mem (pModel X.O n (N, gs, d), g)) ≤ Bmem)
    (hBker : X.B.call GroupOp.kernel ((N, gs, d), baseWin n N) (kerModel X.O n (N, gs, d)) ≤
      Bker)
    (hBg1 : ∀ X₀ : OutD, C3First φ (strOn hC.le (xy.1.denote N)) (N - n) k Vx X₀ →
      X.B.call GroupOp.generate
        (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d)) (outGensD (N - n) X₀))).map
          (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
        (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (outGensD (N - n) X₀)))) ≤ Bg1)
    (hBgen : ∀ gs' : GensData, GensData.AllValid N gs' →
      gs'.length ≤ c3R k Vy.length (sojZ (N - n)) * (s + 1) →
      GensData.denote N gs' ≤ GensData.denote N gs →
      X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ Bgen)
    (hsub : ∀ X₀ : OutD, C3First φ (strOn hC.le (xy.1.denote N)) (N - n) k Vx X₀ →
      SubSolves X body DV sub (fun I => I.1 = xy ∧ I.2.1 = w ∧
        I.2.2.2 = preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (outGensD (N - n) X₀))) ∧ I.Valid DV) (fun _ => Cb) s) :
    ∃ res : Option (AnswerData D),
      RunsWithin X body (Case3.case3Prog sub n k xy w (N, gs, d) Vx Vy) res
        (c3CostC n N s gs.length k Vx.length Vy.length
          (certIsoCost N n k s B.Bstab B.Btr B.Borb Bk.Bgen Bk.Borb Bk.Bstab Bgk Cc Bl Bgs)
          (sojZ (N - n)) BgP Bmem Bker Bl Bg1 Bgen Cb) ∧
      (res = none → C3Twins φ (strOn hC.le (xy.1.denote N)) k Vx) ∧
      ∀ ans, res = some ans →
        AnsOK DV N (w.denote N) 1 (GensData.denote N gs) (xy.1.denote N) (xy.2.denote N) ans ∧
        ∀ sGen, (∀ gs', GensData.AllValid N gs' →
            GensData.denote N gs' ≤ GensData.denote N gs →
            (X.O.run GroupOp.generate (N, gs')).2.1.length ≤ sGen) →
          ∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sGen := by
  classical
  have hOc : MeetsContractOn DV certOps X.O := fun op x h hp => hO op x (Or.inl h) hp
  have hPc : ∀ op x, certOps op → GroupPre DV op x → X.Pre op x := fun op x h hp =>
    hPre op x (Or.inl h) hp
  have hOa : MeetsContractOn DV alignOps X.O := fun op x h hp => hO op x (Or.inr h) hp
  have hPa : ∀ op x, alignOps op → GroupPre DV op x → X.Pre op x := fun op x h hp =>
    hPre op x (Or.inr h) hp
  -- an isomorphism carries the points outside the support for `x` onto those for `y`
  have hmove : ∀ g ∈ iso (w.denote N) 1 (GensData.denote N gs) (xy.1.denote N) (xy.2.denote N),
      ∃ hgG : g ∈ GensData.denote N gs, ∀ v : Fin (N - n),
        (baseHom _ n hC.base ⟨g, hgG⟩ v).val ∈ Vy ↔ v.val ∈ Vx := by
    intro g hg
    have hgG : g ∈ GensData.denote N gs := (mem_iso_one.1 hg).1
    have hy : Fy = Fx.map (MulAut.conj g).toMonoidHom := by
      rw [hFye, hFxe, ← heq g hgG _]
      exact (hloc _ _ (Recursion.relabel_eq_on_of_mem_iso hWG hg)).symm
    exact ⟨hgG, fun v => by rw [hVyF, hVxF]; exact c3p_fix_iff hC.base hFxi hFyi hgG hy v⟩
  by_cases hlen : Vx.length = Vy.length
  swap
  · -- different numbers of fixed points: no isomorphism
    refine ⟨some none, (RunsWithin.case3Prog_ne sub n k xy w (N, gs, d) hlen).mono
      (by unfold c3CostC c3Cost; omega), (fun h => by cases h), fun ans h => ?_⟩
    cases h
    refine ⟨?_, fun _ _ c hc => by cases hc⟩
    show iso _ _ _ _ _ = ∅
    by_contra hne
    obtain ⟨g, hg⟩ := Set.nonempty_iff_ne_empty.2 hne
    obtain ⟨hgG, hσ⟩ := hmove g hg
    exact hlen (c3p_length_eq hVx hVxn hVy hVyn _ hσ)
  have hVyl : 6 ≤ Vy.length := hlen ▸ hm
  -- the colourings
  obtain ⟨cXX, cXY, cYY, hXX, hXY, -, hcol⟩ := RunsWithin.tupleColProg (X := X) (body := body)
    (φ := φ) (x := xy.1) (y := xy.2) hOc hPc hφ hGv halt hVxn hVyn hlen.symm hVx hVy h5 hk B hs
    hGG₀ Bk hsk hBgk hBl hBgs hsubXX hsubXY hsubYY
  have hzlen : ∀ (V : List ℕ) (W : Array ℕ) (z : List ℕ), z ∈ goodListsD k V.length W →
      z.length ≤ k := by
    intro V W z hz
    obtain ⟨x, hx, rfl, -⟩ := mem_goodListsD.1 hz
    rw [List.length_map]
    omega
  -- the alignment
  have halign : ∀ X₀, firstStructD (N - n) k Vx (colXD cXX k Vx.length) = some X₀ →
      ∀ g ∈ iso (w.denote N) 1 (GensData.denote N gs) (xy.1.denote N) (xy.2.denote N),
        ∃ Y ∈ allStructsD (N - n) k Vy (colYD cXY cYY k Vx.length),
          ∃ h : g ∈ GensData.denote N gs,
            baseHom _ n hC.base ⟨g, h⟩ • decodeOut (N - n) X₀ = decodeOut (N - n) Y := by
    intro X₀ hfirst g hg
    obtain ⟨hgG, hσ⟩ := hmove g hg
    obtain ⟨π, hπ⟩ := c3p_renumber hVx hVxn hVy hVyn hlen _ hσ
    have hrel : ∀ T : Fin k → Fin Vx.length,
        toFun (colYD cXY cYY k Vx.length) (⇑π ∘ T) = toFun (colXD cXX k Vx.length) T :=
      tupleCol_iso φ rfl hVx hXX hXY (strR hC ⟨g, hgG⟩) (c3p_strOn_iso hC hwS hg) π
        (c3p_hπ hφ hgG hVx hVxn hVy hVyn hlen hπ)
    obtain ⟨Y, hY, hYe⟩ := c3p_align hVx hVxn hVy hVyn hlen _ hσ π hπ hrel hfirst
    exact ⟨Y, hY, hgG, hYe⟩
  obtain ⟨res, hrun, hnone, hsome⟩ := RunsWithin.case3Prog (X := X) (body := body) hOa hPa hGv
    hC.base halt hw hWG (k := k) hVx hVxn hm (fun h => absurd hlen h) (sub := sub)
    (cX := colXD cXX k Vx.length) (cY := colYD cXY cYY k Vx.length) (fun _ => hcol)
    (Cx := c3OutCost (N - n) k Vx.length (sojZ (N - n)))
    (Cy := c3OutCost (N - n) k Vy.length (sojZ (N - n))) (Z := sojZ (N - n))
    (fun z hz => outCostD_le _ _ _ _ (hzlen _ _ z hz) (outSzD_le hVx hVxn _ hm hz))
    (fun z hz => outCostD_le _ _ _ _ (hzlen _ _ z hz) (outSzD_le hVy hVyn _ hVyl hz))
    (fun z hz => outSzD_le hVy hVyn _ hVyl hz)
    (fun X₀ h => c3p_allStructsD_valid hVx hVxn _ hm X₀ (firstStructD_mem h))
    (c3p_allStructsD_valid hVy hVyn _ hVyl) (fun _ => halign) hBgP hBmem hBker hBl
    (fun X₀ h => hBg1 X₀ ⟨cXX, hXX, h⟩) hBgen (fun X₀ h => hsub X₀ ⟨cXX, hXX, h⟩)
  refine ⟨res, hrun, fun h => ?_, hsome⟩
  obtain ⟨-, htw⟩ := hnone h
  exact ⟨cXX, hXX, twinsD_spec (by omega) _ htw⟩

end CanonicalSpec

/-! ### The charges of the Schreier–Sims backend -/

section SimsCharges

/-- **The generation charges of Case 3 hold for the Schreier–Sims backend**, with explicit
values: `genCost N (k! (s + 1)) + 2` for the comparisons' combinations of at most `k! (s + 1)`
generators (`hBgk`), and `genCost N (R (s + 1)) + 2` for Align's combination of at most
`R (s + 1)` generators, `R = c3R k m Z` (`hBgen`). Both premises bound the number of
generators. -/
theorem c3_ss_charges {N k s R : ℕ} :
    (∀ gs' : GensData, GensData.AllValid N gs' → gs'.length ≤ k.factorial * (s + 1) →
      ssCtx.B.call GroupOp.generate (N, gs') (ssCtx.O.run GroupOp.generate (N, gs')) ≤
        genCost N (k.factorial * (s + 1)) + 2) ∧
    (∀ gs' : GensData, GensData.AllValid N gs' → gs'.length ≤ R * (s + 1) →
      ssCtx.B.call GroupOp.generate (N, gs') (ssCtx.O.run GroupOp.generate (N, gs')) ≤
        genCost N (R * (s + 1)) + 2) := by
  refine ⟨fun gs' _ hl => ?_, fun gs' _ hl => ?_⟩
  · change genCost N gs'.length + 2 ≤ genCost N (k.factorial * (s + 1)) + 2
    exact Nat.add_le_add_right (genCost_mono hl) 2
  · change genCost N gs'.length + 2 ≤ genCost N (R * (s + 1)) + 2
    exact Nat.add_le_add_right (genCost_mono hl) 2

end SimsCharges

/-! ### Well-formedness -/

section Wf

variable {D : Ty} {rec : Ty × Ty} {var₁ var₂ : Ty → Type} {r : Bool} {Γ : WfCtx var₁ var₂}

theorem wf_case3Prog {sub₁ : var₁ (Ty.inst D) → Prog (groupSig D) rec var₁ (Ty.answer D)}
    {sub₂ : var₂ (Ty.inst D) → Prog (groupSig D) rec var₂ (Ty.answer D)}
    (hsub : WfFun r Γ sub₁ sub₂) {n₁ k₁ : var₁ .nat} {n₂ k₂ : var₂ .nat}
    {xy₁ : var₁ Ty.strs} {xy₂ : var₂ Ty.strs} {w₁ : var₁ Ty.win} {w₂ : var₂ Ty.win}
    {G₁ : var₁ (Ty.group D)} {G₂ : var₂ (Ty.group D)}
    {Vx₁ Vy₁ : var₁ (.list .nat)} {Vx₂ Vy₂ : var₂ (.list .nat)}
    (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ) (hxy : ⟨Ty.strs, xy₁, xy₂⟩ ∈ Γ)
    (hw : ⟨Ty.win, w₁, w₂⟩ ∈ Γ) (hG : ⟨Ty.group D, G₁, G₂⟩ ∈ Γ)
    (hVx : ⟨.list .nat, Vx₁, Vx₂⟩ ∈ Γ) (hVy : ⟨.list .nat, Vy₁, Vy₂⟩ ∈ Γ) :
    Prog.Wf r Γ (case3Prog sub₁ n₁ k₁ xy₁ w₁ G₁ Vx₁ Vy₁)
      (case3Prog sub₂ n₂ k₂ xy₂ w₂ G₂ Vx₂ Vy₂) := by
  unfold case3Prog
  refine .bind (.prim _ (.cons hG .nil)) fun N₁ N₂ => ?_
  refine .bind (.prim _ (.cons (by simp) (.cons (by simp [hn]) .nil))) fun M₁ M₂ => ?_
  refine .bind (.prim _ (.cons (by simp [hVx]) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp [hVy]) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ => ?_
  refine .ite (by simp) ?_ (.bind (.prim _ .nil) fun _ _ => .prim _ (.cons (by simp) .nil))
  refine .bind (.prim _ (.cons (by simp [hxy]) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp [hxy]) .nil)) fun _ _ => ?_
  refine .bind (wf_tupleColProg (hsub.mono fun z hz => by simp [hz]) (by simp [hn]) (by simp)
    (by simp [hk]) (by simp [hVx]) (by simp [hVy]) (by simp) (by simp) (by simp [hG]))
    fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (wf_twinsFlagProg (by simp [hk]) (by simp) (by simp)) fun _ _ => ?_
  refine .ite (by simp) (.prim _ .nil) ?_
  refine .bind (wf_firstStructProg (by simp) (by simp [hk]) (by simp [hVx]) (by simp))
    fun _ _ => ?_
  refine .caseOption (by simp) (.prim _ .nil) fun _ _ => ?_
  refine .bind (wf_allStructsProg (by simp) (by simp [hk]) (by simp [hVy]) (by simp))
    fun _ _ => ?_
  refine .bind (Align.wf_alignProg (hsub.mono fun z hz => by simp [hz])
    (fun Γ' hΓ' z₁ z₂ hz => wf_outGensProg (hΓ' (by simp)) hz)
    (fun Γ' hΓ' z₁ z₂ y₁ y₂ hz hy => wf_outIsoProg (hΓ' (by simp)) hz hy)
    (by simp [hn]) (by simp [hxy]) (by simp [hw]) (by simp [hG]) (by simp) (by simp))
    fun _ _ => ?_
  exact .prim _ (.cons (by simp) .nil)

end Wf

end GraphIso.Case3
