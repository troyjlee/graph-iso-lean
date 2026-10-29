module

public import GraphIso.Main.M5Restrict
public import GraphIso.Main.M5Core

/-!
# M5: the step

Stage 14j-4, item 6 (`PLAN-14.md` §14.4). The giant macro-step on a hinted instance
`I = (x, y, W, σ • G)` of degree `N` (string positions `[0, n)`, base `[n, N)`, labels `L`)
whose base action contains `Alt(m)`, `m = N − n`:

* `m5StepProg sub I L k st`: the restriction to the window and the base (`restrictBaseProg`,
  stage 14j-4 item 1), with M5 on the restricted instance (`m5CoreProg`) as its continuation.
* **The giant survives the restriction** (`m5s_giant`): the restricted group acts on the base
  `[|W|, |W| + m)` as `G` acts on `[n, N)`, so its base action contains `Alt(m)` as well.
* **The step** (`RunsWithin.m5StepProg`). The restricted instance `I'` (degree `|W| + m`, the
  window = all `|W|` string positions, representative `1`) is valid (`rbHInst_valid`); its
  group is faithful on the strings (`CertSetting`), `φ` exists (`exists_phi`), its base action
  is a giant (`m5s_giant`), and the window contains every string position; the parent's
  sub-solver hypothesis (children `SizeChild sC I ∧ StepChild |W| m`, with
  `sC = max sIn (supTo sm (|W| / 2))` as for `RunsWithin.m5CoreProg`) gives the one
  `RunsWithin.m5CoreProg` needs for `I'` (`SizeChild sC I' J` implies `SizeChild sC I J`, as
  `|W| ≤ n` and `|W| + m ≤ N`). The answer is correct for `(W, σ • G, x, y)`; the cost is the
  restriction's (`rbCost`) around M5's: the children (`ChildList |W|`, `StepChild |W| m`,
  factor `m5CF`), `2 · certCount + m5CK` sub-calls without a hint on windows of at most
  `|W| / k` points (the certificates, and Case 3's comparisons), `m5CH` sub-calls on windows
  of at most `|W| / 2` points (Case 2a's pullback), and the work `m5CoreWork`.

  The restricted instance's data (`xy`, `w`, `N`, `gs`, `d`, `n`, `L`) are given by their
  defining equations (`hG'`: the backend's restricted group), so that M5's charges are stated
  verbatim on them; those depending on the full groups or on `φ` are assumed for every
  certificate setting and every `φ` (there is exactly one). M5's charges, reduce-and-derive's
  `RDBounds` and per-orbit `RDOrbit`, the restriction's charges, and the numeric conditions
  `5 ≤ k`, `k + 2 ≤ m`, `2k ≤ m`, `12 ≤ m` are hypotheses.
* Well-formedness: `wf_m5StepProg`.
-/

@[expose] public section

namespace GraphIso.Main

open Equiv Pointwise Cost GraphIso GraphIso.Programs GraphIso.Toolkit GraphIso.Recursion
  GraphIso.Certificates GraphIso.CertProg GraphIso.Align GraphIso.Solver

/-! ### The program -/

section Program

variable {D : Ty} {rec : Ty × Ty} {var : Ty → Type}

/-- **M5**: the restriction to the window and the base, with M5 on the restricted instance as
its continuation. -/
def m5StepProg (sub : var (hinstTy D) → Prog (groupSig D) rec var (Ty.answer D))
    (I : var (hinstTy D)) (L : var (.array (.list .nat))) (k : var .nat) (st : var stTy) :
    Prog (groupSig D) rec var (Ty.answer D) :=
  restrictBaseProg (fun I' => m5CoreProg sub I' k st) I L

end Program

/-! ### The giant survives the restriction -/

section Giant

/-- **The restricted base action is a giant**: the restriction to `w ++ [n, N)` acts on the
base indices `[|w|, |w| + m)` as `G` acts on `[n, N)`, so a giant base action stays a giant. -/
theorem m5s_giant {N n : ℕ} {G : Subgroup (Perm (Fin N))} {w : WinData}
    (hUv : (rbU n N w).Valid N) (hU : IsInvariant G ((rbU n N w).denote N))
    (hwin : ∀ i ∈ w.1, i < n) (hB : IsInvariant G (baseSet n N))
    (halt : alternatingGroup (Fin (N - n)) ≤ (baseHom G n hB).range)
    {H : Subgroup (Perm (Fin (rbU n N w).1.length))}
    (hden : H = (restrictHom hU (WinData.reindex hUv)).range)
    (hB' : IsInvariant H (baseSet w.1.length (rbU n N w).1.length)) :
    alternatingGroup (Fin ((rbU n N w).1.length - w.1.length)) ≤
      (baseHom H w.1.length hB').range := by
  subst hden
  have hlen : (rbU n N w).1.length = w.1.length + (N - n) := rb_length
  have hm : (rbU n N w).1.length - w.1.length = N - n := by omega
  intro c hc
  have hc' : (finCongr hm).permCongr c ∈ alternatingGroup (Fin (N - n)) := by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_permCongr]
    exact Equiv.Perm.mem_alternatingGroup.1 hc
  obtain ⟨g, hg⟩ := halt hc'
  refine ⟨⟨restrictHom hU (WinData.reindex hUv) g, g, rfl⟩, ?_⟩
  ext t
  have ht := t.2
  -- the base position of `t` in the restriction, and its point
  have hj : w.1.length ≤ (basePos (n := w.1.length) t).val := by
    simp only [basePos]
    omega
  have hj' : (basePos (n := w.1.length) t).val < w.1.length + (N - n) := by
    simp only [basePos]
    omega
  obtain ⟨hge, hrb⟩ := rb_base hUv hU hwin hB g (basePos (n := w.1.length) t) hj
  have he : (WinData.reindex hUv (basePos (n := w.1.length) t) : Fin N) =
      basePos (n := n) ((finCongr hm) t) := by
    apply Fin.ext
    rw [rb_e_val, rb_getD_ge hj hj']
    simp only [basePos, finCongr_apply, Fin.val_cast]
    omega
  rw [he] at hrb
  -- the left side
  have h1 : w.1.length + ((baseHom _ w.1.length hB')
      (⟨restrictHom hU (WinData.reindex hUv) g, g, rfl⟩ :
        ↥(restrictHom hU (WinData.reindex hUv)).range) t).val =
      ((restrictHom hU (WinData.reindex hUv) g) (basePos (n := w.1.length) t)).val :=
    congrArg Fin.val (baseHom_apply (hG := hB')
      (⟨restrictHom hU (WinData.reindex hUv) g, g, rfl⟩ :
        ↥(restrictHom hU (WinData.reindex hUv)).range) t)
  -- the right side
  have h2 : n + ((baseHom G n hB g) ((finCongr hm) t)).val =
      ((g : Perm (Fin N)) (basePos (n := n) ((finCongr hm) t))).val :=
    congrArg Fin.val (baseHom_apply (hG := hB) g ((finCongr hm) t))
  have h3 : (baseHom G n hB g) ((finCongr hm) t) = (finCongr hm) (c t) := by
    rw [hg, Equiv.permCongr_apply, Equiv.symm_apply_apply]
  have h4 : ((finCongr hm) (c t)).val = (c t).val := rfl
  rw [h3, h4] at h2
  omega

end Giant

/-! ### The step -/

section StepSpec

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}
  {sub : HInstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)}
  {C : ℕ → Option ℕ → ℕ} {s : ℕ} {xy : StrData × StrData} {w : WinData}
  {N : ℕ} {gs : GensData} {d : D.denote} {n₀ n : ℕ} {L : LabelData} {st : ℕ × CJData}
  {sIn Lg Blift Bgen Bo Bk Bcr Bd : ℕ}
  {xyP : StrData × StrData} {wP : WinData} {σP : PermData} {NP : ℕ} {gsP : GensData}
  {dP : D.denote} {nP : ℕ} {LP : LabelData}

/-- **M5 as a step.** For a valid hinted instance `I = (xyP, wP, σP • GP, LP)` (degree `NP`,
string positions `[0, nP)`) whose base action contains `Alt(m)`, `m = NP − nP ≥ 12`: the
restriction to the window and the base gives the instance `I'` with data `xy`, `w`, `N`, `gs`,
`d`, `n = |wP|`, `L` (their defining equations `hG'`, `hxy`, `hw`, `hn`, `hL`), on which M5
runs (`RunsWithin.m5CoreProg`). The answer is correct for `(wP, σP • GP, xP, yP)`; the cost is
`rbCost` around M5's cost on `I'`; the children of the step are `StepChild |wP| m` with factor
`m5CF`, and M5's sub-calls without a hint are counted (`2 · certCount + m5CK` on windows of at
most `|wP| / k` points, `m5CH` on windows of at most `|wP| / 2`). -/
theorem RunsWithin.m5StepProg (hO : MeetsContractOn DV m5Ops X.O)
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
      RunsWithin X body (Main.m5StepProg sub
          (((xyP, (wP, (σP, (NP, gsP, dP)))), (n₀, (nP, some LP))) : HInstData D) LP k st) ans
        (rbCost NP wP.1.length (NP - nP) gsP.length
          ((ch.map fun x => C x.1 x.2).sum + 2 * certCount N n k * C (n / k) none +
            m5CK X.O n N k (N, fxs, ex) (N, fys, ey) * C (n / k) none +
            m5CH X.O n N sIn w.1.length (N, fxs, ex) (N, fys, ey) * C (w.1.length / 2) none +
            m5CoreWork X.O n N k s sIn Bgen Blift Bo Bk Bcr Bd (N, gs, d) (N, fxs, ex)
              (N, fys, ey) w.1.length β B.Bstab B.Btr B.Borb Bk'.Bgen Bk'.Borb Bk'.Bstab
              (fun M => (Bm M).Borb) (fun M => (Bm M).Bstab) (fun M => (Bm M).Btr))
          sIn sKR BgmR BliftR BkerR BgnR) ∧
      AnsOK DV NP (wP.denote NP) (PermData.denote NP σP) (GensData.denote NP gsP)
        (xyP.1.denote NP) (xyP.2.denote NP) ans ∧
      (∀ sGen, (∀ hs, GensData.AllValid NP hs →
          GensData.denote NP hs ≤ GensData.denote NP gsP →
          (X.O.run GroupOp.generate (NP, hs)).2.1.length ≤ sGen) →
        ∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sGen) ∧
      ChildList wP.1.length (m5CF X.O n N k (N, fxs, ex) (N, fys, ey))
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
    RunsWithin.m5CoreProg (X := X) (body := body) (sub := sub) (hC := hC) hO hPre hI' hφ halt'
      hwS h5 (by omega) (by omega) (by omega) B hgs hGG₀ Bk' hsk Bm hsubR hCmono hs hB
      (by rw [hm]; exact hLg) hst β hBgP hBmem hBkA hBlA hBg hBgk hBgs hBF hBk3 hBo3 hBcr3 hB3
      (hBox hC φ hφ) (hBoy hC φ hφ) (hBg1₁ hC φ hφ) (hD₁ hC φ hφ) (hBg1₂ₐ hC φ hφ) hBgen₂ₐ
      hBpb hBgm hBlift hBker hsK hBgn (hBg1₂ᵦ hC φ hφ) (hBgen₂ᵦ hC φ hφ) (hD₂ᵦ hC φ hφ)
      (hBg1₃ hC φ hφ) (hBgen₃ hC φ hφ) (hD₃ hC φ hφ)
  -- the restriction around it
  obtain ⟨ans, hrun, hok, hgen⟩ := RunsWithin.restrictBaseProg (X := X) (body := body)
    (cont := fun I => Main.m5CoreProg sub I k st) hOr hPr hIP (s' := sIn)
    ⟨ans', by rw [hIeq]; exact hrun', by rw [hIeq]; exact hok', hg'⟩
    hBgmR hBliftR hBkerR hsKR hBgnR
  refine ⟨fxs, fys, ex, ey, ans, ch, ⟨hC, φ, hφ, hFx, hFy⟩, hrun, hok, hgen, ?_⟩
  rw [e1, hm] at hch
  exact hch

end StepSpec

/-! ### Well-formedness -/

section Wf

variable {D : Ty} {rec : Ty × Ty} {var₁ var₂ : Ty → Type} {r : Bool} {Γ : WfCtx var₁ var₂}

theorem wf_m5StepProg {sub₁ : var₁ (hinstTy D) → Prog (groupSig D) rec var₁ (Ty.answer D)}
    {sub₂ : var₂ (hinstTy D) → Prog (groupSig D) rec var₂ (Ty.answer D)}
    (hsub : WfFun r Γ sub₁ sub₂) {I₁ : var₁ (hinstTy D)} {I₂ : var₂ (hinstTy D)}
    {L₁ : var₁ (.array (.list .nat))} {L₂ : var₂ (.array (.list .nat))}
    {k₁ : var₁ .nat} {k₂ : var₂ .nat} {st₁ : var₁ stTy} {st₂ : var₂ stTy}
    (hI : ⟨hinstTy D, I₁, I₂⟩ ∈ Γ) (hL : ⟨.array (.list .nat), L₁, L₂⟩ ∈ Γ)
    (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ) (hst : ⟨stTy, st₁, st₂⟩ ∈ Γ) :
    Prog.Wf r Γ (m5StepProg sub₁ I₁ L₁ k₁ st₁) (m5StepProg sub₂ I₂ L₂ k₂ st₂) := by
  unfold m5StepProg
  exact wf_restrictBaseProg (fun Γ' hΓ x₁ x₂ hx =>
    wf_m5CoreProg (hsub.mono hΓ) hx (hΓ hk) (hΓ hst)) hI hL

end Wf

end GraphIso.Main
