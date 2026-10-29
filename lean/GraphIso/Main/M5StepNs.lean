module

public import GraphIso.Main.M5StepCJ

/-!
# M5 as a step without stuck orbits

Stage 14j-6b-1, item 5 (`PLAN-14.md` §14.11). `RunsWithin.m5StepCJProg_ns`: M5 with coloured
Johnson alignment as a step on the parent instance, with the restricted instance's run given by
`RunsWithin.m5CoreCJProg_ns_jpC` (no stuck orbit, no kernel reduction in Case 3, Case 2b's counts
for `y` assumed only in Case 2b). Its factor is `m5CFnsCJ` and its work `m5CoreWorkNsCJ`, with no
`m!`. The Schreier–Sims form, with every hypothesis but numeric ones and the interfaces
discharged, is `RunsWithin.m5StepCJProg_ns_ss` (`Main/SimsM5Ns.lean`).
-/

@[expose] public section

namespace GraphIso.Main

open Equiv MulAction Pointwise Cost GraphIso GraphIso.Programs GraphIso.Toolkit
  GraphIso.Recursion GraphIso.SplitJohnson GraphIso.Solver GraphIso.Align GraphIso.Certificates
  GraphIso.CertProg

section StepNs

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}
  {sub : HInstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)}
  {C : ℕ → Option ℕ → ℕ} {s : ℕ} {xy : StrData × StrData} {w : WinData}
  {N : ℕ} {gs : GensData} {d : D.denote} {n₀ n : ℕ} {L : LabelData} {st : ℕ × CJData}
  {sIn Lg Blift Bgen Bo Bk Bcr Bd : ℕ}
  {xyP : StrData × StrData} {wP : WinData} {σP : PermData} {NP : ℕ} {gsP : GensData}
  {dP : D.denote} {nP : ℕ} {LP : LabelData}

/-- **M5 with coloured Johnson alignment as a step, without stuck orbits** (stage 14j-6b-1,
`PLAN-14.md` §14.11 item 5). The restriction composed with `RunsWithin.m5CoreCJProg_ns_jpC`, as
`RunsWithin.m5StepCJProg_jp` composes `RunsWithin.m5CoreCJProg_jp`. The hypotheses are those of
`RunsWithin.m5StepCJProg_jp` (for every certificate setting and every `φ`), except:
* the kernel reduction's charges (`hBk3`, `hBo3`, `hBcr3`, `hB3`) are dropped: Case 3 never runs
  it, and no orbit is stuck;
* `Lg` needs only `m · (sIn + 1)`, not `m! · (sIn + 1)`;
* Case 2b's partition leaves and Case 3's partition structures are colored `t`-partitions with
  `4t ≤ 3m` (`hpart₂ᵦ`, `hpart₃`), and Case 3 has no twins (`hnt₃`);
* Case 2b's counts for `y` (`hBgen₂ᵦ`, `hLY₂`) are needed only when `y`'s case is Case 2b.

The answer is correct for the parent; the cost is `rbCost` around M5's, with the work
`m5CoreWorkNsCJ`; the children are `StepChild |wP| m` with factor `m5CFnsCJ` (no `m!`). -/
theorem RunsWithin.m5StepCJProg_ns (hO : MeetsContractOn DV m5Ops X.O)
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
    (hLg : (NP - nP) * (sIn + 1) ≤ Lg) (hst : st.1 ≠ 2) (β : M5Bounds)
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
      ∀ fs e, M5Full DV hC φ k sIn xy.2 fs e →
      (m5Cs X.O n N (N, fs, e)).1 = 2 → m5IsA X.O n N (N, fs, e) = false → ∀ gs' : GensData,
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
    (hpart₂ᵦ : ∀ (hC : CertSetting (GensData.denote N gs) n)
      (φ : strGroup hC →* Perm (Fin (N - n))), IsPhi hC φ →
      ∀ fxs ex fys ey, M5Full DV hC φ k sIn xy.1 fxs ex →
      M5Full DV hC φ k sIn xy.2 fys ey → m5Sel X.O n N (N, fxs, ex) (N, fys, ey) = 4 → ∀ X₀,
      m5Leaf2b X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 = some X₀ → X₀.1 ≠ 2 →
      ∃ (p : CPart (Fin (N - n))) (t : ℕ), (Case2b.outOps (N - n)).dec X₀ = some (Sum.inl p) ∧
        IsColPart Finset.univ t p ∧ 4 * t ≤ 3 * (N - n))
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
    (hnt₃ : ∀ (hC : CertSetting (GensData.denote N gs) n)
      (φ : strGroup hC →* Perm (Fin (N - n))), IsPhi hC φ →
      ∀ fxs ex fys ey, M5Full DV hC φ k sIn xy.1 fxs ex →
      M5Full DV hC φ k sIn xy.2 fys ey → m5Sel X.O n N (N, fxs, ex) (N, fys, ey) = 3 →
      ¬ Case3.C3Twins φ (strOn hC.le (xy.1.denote N)) k (fixPtsD (m5Os X.O n N (N, fxs, ex))))
    (hpart₃ : ∀ (hC : CertSetting (GensData.denote N gs) n)
      (φ : strGroup hC →* Perm (Fin (N - n))), IsPhi hC φ →
      ∀ fxs ex fys ey, M5Full DV hC φ k sIn xy.1 fxs ex →
      M5Full DV hC φ k sIn xy.2 fys ey → m5Sel X.O n N (N, fxs, ex) (N, fys, ey) = 3 → ∀ X₀,
      Case3.C3First φ (strOn hC.le (xy.1.denote N)) (N - n) k
        (fixPtsD (m5Os X.O n N (N, fxs, ex))) X₀ → X₀.1 ≠ 2 →
      ∃ (p : CPart (Fin (N - n))) (t : ℕ), (Case2b.outOps (N - n)).dec X₀ = some (Sum.inl p) ∧
        IsColPart Finset.univ t p ∧ 4 * t ≤ 3 * (N - n))
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
      (m5Cs X.O n N (N, fs, e)).1 = 2 → m5IsA X.O n N (N, fs, e) = false →
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
            m5CoreWorkNsCJ X.O n N k s sIn Bgen Blift Bo Bd (N, gs, d) (N, fxs, ex)
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
      ChildList wP.1.length (m5CFnsCJ X.O n N k (N, fxs, ex) (N, fys, ey) uB)
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
    RunsWithin.m5CoreCJProg_ns_jpC (X := X) (body := body) (sub := sub) (hC := hC) hO hPre hI' hφ
      halt' hwS h5 (by omega) (by omega) (by omega) B hgs hGG₀ Bk' hsk Bm hsubR hCmono hs hB
      (by rw [hm]; exact hLg) hst β hBgP hBmem hBkA hBlA hBg hBgk hBgs hBF
      (hBox hC φ hφ) (hBoy hC φ hφ) (hBg1₁ hC φ hφ) (hD₁ hC φ hφ) (hBg1₂ₐ hC φ hφ) hBgen₂ₐ
      hBpb hBgm hBlift hBker hsK hBgn (hBg1₂ᵦ hC φ hφ) (hBgen₂ᵦ hC φ hφ) (hD₂ᵦ hC φ hφ)
      (hpart₂ᵦ hC φ hφ) (hBg1₃ hC φ hφ) (hBgen₃ hC φ hφ) (hD₃ hC φ hφ) (hnt₃ hC φ hφ)
      (hpart₃ hC φ hφ) (by rw [hm]; exact hLgJ)
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

end StepNs

end GraphIso.Main
