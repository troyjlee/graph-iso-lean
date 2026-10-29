module

public import GraphIso.Main.M5Core

/-!
# M5: Case 3 with a partition leaf

Stage 14j-4, item 6 (`PLAN-14.md` §14.4): the no-stuck form of Case 3 for partition leaves,
next to `RunsWithin.m5Case1Prog_ns` (Case 1) and `RunsWithin.m5Case2bProg_part` (Case 2b).

* **No fallback** (`m5_fix_iff_supp`, `m5_no_twins`): the fixed points of `ψ(F(x))` are the
  points outside the support of `fullGroupK φ k x`, so under the thresholds of the CFSG-free
  interface (`case3_no_fallback`) the colouring of `x` has no more than `t` pairwise twins
  (`¬ C3Twins`).
* **Case 3 with a partition leaf** (`RunsWithin.m5Case3Prog_part`): without twins, `case3Prog`
  answers, so `m5Case3Prog` never runs the kernel reduction `m3Prog`. If `x`'s first structure
  decodes to a colored `t`-partition with `4t ≤ 3m` and `st` is not a coloured Johnson
  structure, every element of the aligned group `K = ψ⁻¹(Stab(X(x)))` preserves it
  (`ar_g1_facts`, i.e. `ar_K_fix`), so no orbit is stuck (`rd_ns_part`), and reduce-and-derive
  runs with factor `m` and no stuck work (`W6 = 0`). The children's factor is `c3R · m`.
* **M5 with no stuck orbit** (`RunsWithin.m5Dispatch_ns`, `RunsWithin.m5CoreProg_ns`): the
  dispatch and M5 on the restricted instance with the no-stuck forms of the cases (Case 1:
  `m5Case1Prog_ns`; Case 2a as before; Case 2b: `m5Case2bProg_part`; Case 3:
  `m5Case3Prog_part`), each case's partition and no-twins hypotheses assumed only when that
  case runs (`m5Sel`). The answer is correct; the children's factor is `m5CFns` (`m`, `c2bR · m`,
  `c3R · m` per case, none in Case 2a) instead of `m5CF`, the work `m5Wns` / `m5CoreWorkNs`
  (no stuck work, no kernel reduction), and `Lg` needs only `m · (sIn + 1)`.

Hypotheses not discharged here: the partition leaves themselves (`hpart`; Johnson leaves are
14j-4b's), `¬ C3Twins` (or the thresholds of `m5_no_twins`), and, as in
`RunsWithin.m5CoreProg`, the backends' charges, `RDBounds`, the per-orbit `RDOrbit` and the
numeric conditions.
-/

@[expose] public section

namespace GraphIso.Main

open Equiv MulAction Pointwise Cost GraphIso GraphIso.Programs GraphIso.Toolkit
  GraphIso.Recursion GraphIso.SplitJohnson GraphIso.Solver GraphIso.Align GraphIso.Certificates
  GraphIso.CertProg

/-! ### No fallback under the thresholds -/

section NoTwins

variable {N n : ℕ} {G : Subgroup (Perm (Fin N))} {hC : CertSetting G n}
  {φ : strGroup hC →* Perm (Fin (N - n))}

/-- **The fixed points of `ψ(F(x))`** are the points outside the support of the full group
`fullGroupK φ k x` of the string. -/
theorem m5_fix_iff_supp (hφ : IsPhi hC φ) (k : ℕ) (x : Fin N → ℕ)
    (hFi : IsInvariant (m5Fmap hC φ k x) (baseSet n N)) (v : Fin (N - n)) :
    (∀ f ∈ (baseHom (m5Fmap hC φ k x) n hFi).range, f v = v) ↔
      v ∉ supp φ (fullGroupK φ k (strOn hC.le x)) := by
  constructor
  · rintro h ⟨c, hc, hne⟩
    obtain ⟨g, rfl⟩ := strR_surjective hC c
    have hgF : g.1 ∈ m5Fmap hC φ k x := Giant.ag_mem_agPre.2 ⟨g.2, hc⟩
    apply hne
    rw [hφ g, m5_baseHom_eq (hH := hFi) g ⟨g.1, hgF⟩ rfl]
    exact h _ ⟨_, rfl⟩
  · rintro h f ⟨⟨g, hgF⟩, rfl⟩
    obtain ⟨hgG, hc⟩ := Giant.ag_mem_agPre.1 hgF
    by_contra hne
    refine h ⟨strR hC ⟨g, hgG⟩, hc, ?_⟩
    rw [hφ, m5_baseHom_eq ⟨g, hgG⟩ ⟨g, hgF⟩ rfl]
    exact hne

/-- **No twins under the thresholds**: if `Vx` lists the fixed points of `ψ(F(x))`, the
thresholds of the CFSG-free interface and `k ≤ t` exclude Case 3's fallback condition
(`case3_no_fallback`). -/
theorem m5_no_twins (hφ : IsPhi hC φ) {K : ℕ → ℕ} {k : ℕ} (hT : Thresholds K n k)
    (x : Fin N → ℕ) (hFi : IsInvariant (m5Fmap hC φ k x) (baseSet n N)) {Vx : List ℕ}
    (hVx : ∀ v ∈ Vx, v < N - n) (hVxn : Vx.Nodup)
    (hVxF : ∀ v : Fin (N - n), v.val ∈ Vx ↔
      ∀ f ∈ (baseHom (m5Fmap hC φ k x) n hFi).range, f v = v)
    (hkt : k ≤ Case3.tOf Vx.length) : ¬ Case3.C3Twins φ (strOn hC.le x) k Vx :=
  Case3.case3_no_fallback φ _ hT hVx hVxn
    (fun v => by rw [hVxF, m5_fix_iff_supp hφ k x hFi v]) hkt

end NoTwins

/-! ### Case 3 with a partition leaf -/

section Case3Part

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}
  {sub : HInstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)}
  {C : ℕ → Option ℕ → ℕ} {s : ℕ} {xy : StrData × StrData} {w : WinData}
  {N : ℕ} {gs : GensData} {d : D.denote} {n₀ n : ℕ} {L : LabelData} {st : ℕ × CJData}
  {sIn Lg Blift Bgen Bo Bk Bcr Bd : ℕ}

/-- **Case 3 of M5 with a partition leaf and no stuck orbit.** Under the hypotheses of
`RunsWithin.m5Case3Prog`, if the colouring of `x` has no more than `t` pairwise twins
(`¬ C3Twins`; `m5_no_twins` under the thresholds), `case3Prog` answers and the kernel reduction
`m3Prog` never runs. If moreover `st` is not a coloured Johnson structure and `x`'s first
structure decodes to a colored `t`-partition with `4t ≤ 3m`, the aligned group preserves it, so
no orbit is stuck (`rd_ns_part`): reduce-and-derive runs with factor `m` and no stuck work, and
the children's windows sum to at most `c3R · m · |W|`. -/
theorem RunsWithin.m5Case3Prog_part (hOc : MeetsContractOn DV Case3.c3Ops X.O)
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
    (hm : 6 ≤ Vx.length) {k : ℕ} (h5 : 5 ≤ k) (hk : k + 2 ≤ N - n)
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
    {BgP Bmem Bker Bg1 Bgen' : ℕ}
    (hBgP : X.B.call GroupOp.generate (N - n, gs.map (baseD n N))
      (X.O.run GroupOp.generate (N - n, gs.map (baseD n N))) ≤ BgP)
    (hBmem : ∀ g : PermData, g.Valid (N - n) → X.B.call GroupOp.mem (pModel X.O n (N, gs, d), g)
      (X.O.run GroupOp.mem (pModel X.O n (N, gs, d), g)) ≤ Bmem)
    (hBker : X.B.call GroupOp.kernel ((N, gs, d), baseWin n N) (kerModel X.O n (N, gs, d)) ≤
      Bker)
    (hBg1 : ∀ X₀ : SoJTree.OutD, Case3.C3First φ (strOn hC.le (xy.1.denote N)) (N - n) k Vx X₀ →
      X.B.call GroupOp.generate
        (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (Case2b.outGensD (N - n) X₀))).map
          (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
        (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (Case2b.outGensD (N - n) X₀)))) ≤ Bg1)
    (hBgen : ∀ gs' : GensData, GensData.AllValid N gs' →
      gs'.length ≤ Case3.c3R k Vy.length (Case2b.sojZ (N - n)) * (sIn + 1) →
      GensData.denote N gs' ≤ GensData.denote N gs →
      X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ Bgen')
    (hsub : HSubSolves X body DV sub
      (fun J => SizeChild sIn (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D)
        J ∧ StepChild w.1.length (N - n) (J.winSize, J.baseOpt)) C s)
    (hCmono : ∀ a b, a ≤ b → C a none ≤ C b none)
    (hB : RDBounds X DV n N sIn Lg Blift Bgen Bo Bk Bcr) (hs : s ≤ sIn)
    (hLg : (N - n) * (sIn + 1) ≤ Lg) (hst : st.1 ≠ 2)
    (hD : ∀ X₀, Case3.C3First φ (strOn hC.le (xy.1.denote N)) (N - n) k Vx X₀ →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (Case2b.outOps (N - n)) X₀).2.1 sIn gs' d' O' →
      RDOrbit X body DV n N w L st sIn Bd gs' d' O')
    (hnt : ¬ Case3.C3Twins φ (strOn hC.le (xy.1.denote N)) k Vx)
    (hpart : ∀ X₀, Case3.C3First φ (strOn hC.le (xy.1.denote N)) (N - n) k Vx X₀ →
      ∃ (p : CPart (Fin (N - n))) (t : ℕ), (Case2b.outOps (N - n)).dec X₀ = some (Sum.inl p) ∧
        IsColPart Finset.univ t p ∧ 4 * t ≤ 3 * (N - n)) :
    ∃ (ans : AnswerData D) (ch : List (ℕ × Option ℕ)),
      RunsWithin X body (Main.m5Case3Prog sub
          (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D) n₀ n L st k xy w
          (N, gs, d) Vx Vy) ans
        ((ch.map fun x => C x.1 x.2).sum + c3Count Vx.length k n * C (n / k) none +
          (c3Work n N sIn gs.length k Vx.length Vy.length (Case2b.sojZ (N - n)) BgP Bmem Bker Bl
            Bg1 Bgen' B.Bstab B.Btr B.Borb Bk'.Bgen Bk'.Borb Bk'.Bstab Bgk Bgs w.1.length
            (w.1.length * rdOrbitWork N n w.1.length s sIn (N - n) Bd Blift Bgen Bo 0 +
              dynSeqCost N w.1.length Bo + 5) + w.1.length + 3)) ∧
      AnsOK DV N (w.denote N) 1 (GensData.denote N gs) (xy.1.denote N) (xy.2.denote N) ans ∧
      (∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sIn) ∧
      ChildList w.1.length (Case3.c3R k Vy.length (Case2b.sojZ (N - n)) * (N - n))
        (StepChild w.1.length (N - n)) ch := by
  have hGv : GroupValid DV N gs d := hI.valid.group
  have hw : w.Valid N := hI.valid.win
  have hWG : IsInvariant (GensData.denote N gs) (w.denote N) := hI.valid.invariant
  have hOa : MeetsContractOn DV alignOps X.O := fun op x h hx => hOc op x (Or.inr h) hx
  have hPa : ∀ op x, alignOps op → GroupPre DV op x → X.Pre op x :=
    fun op x h hx => hPc op x (Or.inr h) hx
  have hO' : MeetsContractOn DV deriveOps X.O := fun op x h hx => hO op x (by
    rcases h with h | h | h | h <;> simp [rdOps, h]) hx
  have hnw : n ≤ w.1.length := m5_n_le_win hw hI.le hwS
  have hm2 : 2 ≤ N - n := by omega
  have hw1 : 1 ≤ w.1.length := by
    obtain ⟨i, hi, -⟩ := (hI.hint L rfl).1.nonconst
    exact List.length_pos_of_mem hi
  set Wb := w.1.length * rdOrbitWork N n w.1.length s sIn (N - n) Bd Blift Bgen Bo 0 +
    dynSeqCost N w.1.length Bo + 5 with hWb
  -- the comparisons' sub-solver
  have hcmp : ∀ xy' : StrData × StrData,
      SubSolves X body DV (fun J => Main.c3Sub sub n₀ n L st w.1.length J)
        (StepSubP (DV := DV) (GensData.denote N gs) xy' n k sIn)
        (fun _ => C (n / k) none + 4 + w.1.length + 6) sIn := fun xy' =>
    m5_subSolves_mono (m5_c3Sub_cmp (m5_stepSub hsub hCmono (by omega) hC xy'
      (fun J hJ => m5_stepSub_child h5 hnw hJ))
      (fun J hJ => by
        obtain ⟨-, -, -, -, hkw, -, -⟩ := hJ
        have := Nat.mul_le_mul_right J.2.1.1.length h5
        omega)) hs
  -- Align's sub-solver, from the unique first structure, with no stuck orbit
  have hpack : ∃ ch₀ : List (ℕ × Option ℕ),
      ((ch₀.map Prod.fst).sum ≤ (N - n) * w.1.length ∧
        (∀ x ∈ ch₀, StepChild w.1.length (N - n) x) ∧ ∀ x ∈ ch₀, 1 ≤ x.1) ∧
      ∀ X₀ : SoJTree.OutD, Case3.C3First φ (strOn hC.le (xy.1.denote N)) (N - n) k Vx X₀ →
        SubSolves X body DV (fun J => Main.c3Sub sub n₀ n L st w.1.length J)
          (fun I => I.1 = xy ∧ I.2.1 = w ∧
            I.2.2.2 = preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O
              (pModel X.O n (N, gs, d)) (Case2b.outGensD (N - n) X₀))) ∧ I.Valid DV)
          (fun _ => (ch₀.map fun x => C x.1 x.2).sum + Wb + w.1.length + 6) sIn := by
    by_cases hex : ∃ X₀₀, Case3.C3First φ (strOn hC.le (xy.1.denote N)) (N - n) k Vx X₀₀
    · obtain ⟨X₀₀, hX₀₀⟩ := hex
      have hXv : Case2b.OutValid (N - n) X₀₀ := by
        obtain ⟨c, -, hfs⟩ := hX₀₀
        exact Case3.c3p_allStructsD_valid hVx hVxn _ hm X₀₀ (Case3.firstStructD_mem hfs)
      obtain ⟨p, t, hdec, hp, ht⟩ := hpart X₀₀ hX₀₀
      obtain ⟨-, hKb, hfix⟩ := ar_g1_facts hOa hPa B hGv hGG₀ hC.base halt
        (Case2b.outOps_spec (N - n)) hXv hBl
      have hpK : ∀ g, baseHom _ n hKb g • p = p := fun g => by
        have h := hfix g
        rw [hdec, Option.smul_some, Sum.smul_inl] at h
        exact Sum.inl_injective (Option.some_injective _ h)
      obtain ⟨ch₀, hgood, hsubA⟩ := m5_alignSub (C := C) (Bk := Bk) (Bcr := Bcr) (W6 := 0) hOa
        hPa hO hPre hI hC.base halt B hGG₀ le_rfl (Case2b.outOps_spec (N - n)) hXv hBl hsub hB
        hs hLg (by omega) le_rfl (hD X₀₀ hX₀₀)
        (Or.inr fun _ _ _ _ h5' => absurd h5' (rd_free_ne5 hst))
        (Or.inl (rd_ns_part hO' hst hKb hp hpK ht hm2))
      refine ⟨ch₀, hgood, fun X₀ hX₀ => ?_⟩
      obtain rfl := m5_c3First_unique hX₀ hX₀₀
      exact m5_c3Sub_align hsubA (fun J hJ => by rw [hJ.2.1])
    · exact ⟨[], ⟨by simp, by simp, by simp⟩, fun X₀ hX₀ => absurd ⟨X₀, hX₀⟩ hex⟩
  obtain ⟨ch₀, hgood, hsubA⟩ := hpack
  obtain ⟨res, hrun, hnone, hsome⟩ := Case3.RunsWithin.case3Prog_canonical (body := body)
    (sub := fun J => Main.c3Sub sub n₀ n L st w.1.length J) hOc hPc hφ hGv halt hw hWG hwS
    hloc heq hFxe hFye hFxi hFyi hVx hVxn hVy hVyn hVxF hVyF hm h5 hk B hgs hGG₀ Bk' hsk hBgk
    hBl hBgs (hcmp _) (hcmp _) (hcmp _) hBgP hBmem hBker hBg1 hBgen hsubA
  -- no fallback: `case3Prog` answers
  rcases res with _ | ans
  · exact absurd (hnone rfl) hnt
  obtain ⟨hok, hg⟩ := hsome ans rfl
  have hrun' : RunsWithin X body (Main.m5Case3Prog sub
      (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D) n₀ n L st k xy w
      (N, gs, d) Vx Vy) ans
      (Case3.c3CostC n N sIn gs.length k Vx.length Vy.length
        (certIsoCost N n k sIn B.Bstab B.Btr B.Borb Bk'.Bgen Bk'.Borb Bk'.Bstab Bgk
          (C (n / k) none + 4 + w.1.length + 6) Bl Bgs)
        (Case2b.sojZ (N - n)) BgP Bmem Bker Bl Bg1 Bgen'
        ((ch₀.map fun x => C x.1 x.2).sum + Wb + w.1.length + 6) + w.1.length + 3) := by
    apply RunsWithin.mono
    case h =>
      unfold Main.m5Case3Prog
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step hrun
      exact RunsWithin.caseOption_some
        (RunsWithin.ret (X := X) (body := body) (t := Ty.answer D) ans)
    case hc =>
      simp only [Prim.cost, Prim.eval, Args.head]
      omega
  have hsplit := c3CostC_split n N sIn gs.length k Vx.length Vy.length (Case2b.sojZ (N - n)) BgP
    Bmem Bker Bl Bg1 Bgen' B.Bstab B.Btr B.Borb Bk'.Bgen Bk'.Borb Bk'.Bstab Bgk Bgs w.1.length
    Wb (C (n / k) none) (ch₀.map fun x => C x.1 x.2).sum
  have hrepc := m5_replicate_cost (C := C) (k := Case3.c3R k Vy.length (Case2b.sojZ (N - n)))
    (ch₀ := ch₀)
  refine ⟨ans, (List.replicate (Case3.c3R k Vy.length (Case2b.sojZ (N - n))) ch₀).flatten,
    hrun'.mono ?_, hok, hg sIn (fun hs' hv _ => hB.genOut N le_rfl hs' hv),
    m5_replicate_childList hgood⟩
  rw [hrepc]
  omega

end Case3Part

/-! ### M5 with no stuck orbit -/

section NsDefs

variable {D : Ty}

/-- **The factor of the dispatch's children list with no stuck orbit**: `m` per aligned coset
in Cases 1, 2b and 3 (no kernel reduction in Case 3), none in Case 2a. -/
def m5CFns (O : Oracle (groupSig D)) (n N k : ℕ) (Fx Fy : GroupData D.denote) : ℕ :=
  match m5Sel O n N Fx Fy with
  | 1 => 1 * (N - n)
  | 3 => Case3.c3R k (fixPtsD (m5Os O n N Fy)).length (Case2b.sojZ (N - n)) * (N - n)
  | 4 => Case2b.c2bR N n (m5Cs O n N Fy).2.length (Case2b.degD O N n Fx (m5Cs O n N Fx).2 - 1)
      (Case2b.sojZ (N - n)) * (N - n)
  | _ => 0

/-- **The work of M5's dispatch with no stuck orbit**: as `m5W`, with reduce-and-derive at
factor `m` and no stuck work in Cases 2b and 3, and no kernel reduction in Case 3. -/
def m5Wns (O : Oracle (groupSig D)) (n N k s sIn Bgen Blift Bo Bd : ℕ)
    (G Fx Fy : GroupData D.denote) (wl : ℕ) (β : M5Bounds) (Bst Btr Borb Bkg Bko Bks : ℕ)
    (Bo' Bs' Bt' : ℕ → ℕ) : ℕ :=
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
      (m5Wb N n wl s sIn (N - n) Bd Blift Bgen Bo 0) + wl + 3 + 2 * fixPtsCost (N - n) + 20
  | 4 => (match m5Leaf2b O N n Fx (m5Cs O n N Fx).2 with
      | some X₀ => Case2b.c2bCost n N sIn G.2.1.length (m5Cs O n N Fx).2.length
          (m5Cs O n N Fy).2.length (Case2b.degD O N n Fx (m5Cs O n N Fx).2 - 1)
          (Case2b.outGensD (N - n) X₀).length Bst β.Bg (Case2b.sojZ (N - n)) β.BgP β.Bmem β.BkA
          β.BlA β.Bg1₂ᵦ β.Bgen₂ᵦ (m5Wb N n wl s sIn (N - n) Bd Blift Bgen Bo 0) Bo' Bs' Bt'
      | none => 0) + 28
  | _ => 28

/-- **The work of M5 with no stuck orbit**: as `m5CoreWork`, with `m5Wns` for the dispatch. -/
def m5CoreWorkNs (O : Oracle (groupSig D)) (n N k s sIn Bgen Blift Bo Bd : ℕ)
    (G Fx Fy : GroupData D.denote) (wl : ℕ) (β : M5Bounds) (Bst Btr Borb Bkg Bko Bks : ℕ)
    (Bo' Bs' Bt' : ℕ → ℕ) : ℕ :=
  2 * (certCount N n k * 4 +
      certWork N n k sIn Bst Btr Borb Bkg Bko Bks β.Bgk β.BlA β.Bgs β.BF) +
    m5DecCost O n N sIn Bst Borb β.Bg Bo' Bs' Fx + m5DecCost O n N sIn Bst Borb β.Bg Bo' Bs' Fy +
    m5Wns O n N k s sIn Bgen Blift Bo Bd G Fx Fy wl β Bst Btr Borb Bkg Bko Bks Bo' Bs' Bt' + 15

end NsDefs

section DispatchNs

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}
  {sub : HInstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)}
  {C : ℕ → Option ℕ → ℕ} {s : ℕ} {xy : StrData × StrData} {w : WinData}
  {N : ℕ} {gs : GensData} {d : D.denote} {n₀ n : ℕ} {L : LabelData} {st : ℕ × CJData}
  {sIn Lg Blift Bgen Bo Bk Bcr Bd : ℕ}

/-- **M5's dispatch with no stuck orbit.** Under the hypotheses of `RunsWithin.m5Dispatch`,
with `m · (sIn + 1) ≤ Lg` instead of `m! · (sIn + 1)`, `st` not a coloured Johnson structure,
and the leaves of Cases 2b and 3 colored `t`-partitions with `4t ≤ 3m` (`hpart₂ᵦ`, `hpart₃`;
in Case 3 also no more than `t` pairwise twins, `hnt₃`, which `m5_no_twins` gives under the
thresholds), each assumed only in its case (`m5Sel`): no orbit is stuck and Case 3 never runs
the kernel reduction. The children's factor is `m5CFns` (`m` per aligned coset in Cases 1, 2b
and 3, none in Case 2a) and the work `m5Wns` (no stuck work). -/
theorem RunsWithin.m5Dispatch_ns (hO : MeetsContractOn DV m5Ops X.O)
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
      m5Leaf2b X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 = some X₀ →
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
        (fixPtsD (m5Os X.O n N (N, fxs, ex))) X₀ →
      ∃ (p : CPart (Fin (N - n))) (t : ℕ), (Case2b.outOps (N - n)).dec X₀ = some (Sum.inl p) ∧
        IsColPart Finset.univ t p ∧ 4 * t ≤ 3 * (N - n)) :
    ∃ (ans : AnswerData D) (ch : List (ℕ × Option ℕ)),
      RunsWithin X body (Main.m5Dispatch sub
          (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D) n₀ n L st k xy w
          (N, gs, d) (N, fxs, ex) (N, fys, ey) (m5CaseD X.O n N (N, fxs, ex))
          (m5CaseD X.O n N (N, fys, ey))) ans
        ((ch.map fun x => C x.1 x.2).sum +
          m5CK X.O n N k (N, fxs, ex) (N, fys, ey) * C (n / k) none +
          m5CH X.O n N sIn w.1.length (N, fxs, ex) (N, fys, ey) * C (w.1.length / 2) none +
          m5Wns X.O n N k s sIn Bgen Blift Bo Bd (N, gs, d) (N, fxs, ex) (N, fys, ey)
            w.1.length β B.Bstab B.Btr B.Borb Bk'.Bgen Bk'.Borb Bk'.Bstab
            (fun M => (Bm M).Borb) (fun M => (Bm M).Bstab) (fun M => (Bm M).Btr)) ∧
      AnsOK DV N (w.denote N) 1 (GensData.denote N gs) (xy.1.denote N) (xy.2.denote N) ans ∧
      (∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sIn) ∧
      ChildList w.1.length (m5CFns X.O n N k (N, fxs, ex) (N, fys, ey))
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
    refine ⟨ans, ch, (m5Dispatch_run1 h1 hrun).mono ?_, hok, hg, ?_⟩
    · rw [m5CK_of_ne (by rw [hsel]; decide), m5CH_of_ne (by rw [hsel]; decide)]
      have hW : m5Wns X.O n N k s sIn Bgen Blift Bo Bd (N, gs, d) (N, fxs, ex) (N, fys, ey)
          w.1.length β B.Bstab B.Btr B.Borb Bk'.Bgen Bk'.Borb Bk'.Bstab
          (fun M => (Bm M).Borb) (fun M => (Bm M).Bstab) (fun M => (Bm M).Btr) =
          Giant.case1Cost n N gs.length
            (partGensD (N - n) (Giant.orbitPartModel X.O n N (N, fxs, ex))).length β.Box β.Boy
            β.BgP β.Bmem β.BkA β.BlA β.Bg1₁ Bgen
            (m5Wb N n w.1.length s sIn (N - n) Bd Blift Bgen Bo 0) sIn + 16 := by
        unfold m5Wns
        rw [hsel]
        rfl
      rw [hW]
      simp only [m5Wb]
      omega
    · have hF : m5CFns X.O n N k (N, fxs, ex) (N, fys, ey) = 1 * (N - n) := by
        unfold m5CFns
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
        refine ⟨ans, [], (m5Dispatch_run2 h2 (m5_run2a hok hA hrun)).mono ?_, hok',
          hg sIn (fun gs' hv hle => B.genOut gs' hv (hle.trans hGG₀)),
          ⟨by simp, by simp, by simp⟩⟩
        rw [m5CK_of_ne (by rw [hsel]; decide)]
        have hH : m5CH X.O n N sIn w.1.length (N, fxs, ex) (N, fys, ey) =
            (sIn + 1) * w.1.length := by
          unfold m5CH
          rw [if_pos' hsel]
        have hW : m5Wns X.O n N k s sIn Bgen Blift Bo Bd (N, gs, d) (N, fxs, ex)
            (N, fys, ey) w.1.length β B.Bstab B.Btr B.Borb Bk'.Bgen Bk'.Borb Bk'.Bstab
            (fun M => (Bm M).Borb) (fun M => (Bm M).Bstab) (fun M => (Bm M).Btr) =
            c2aWork n N gs.length ((setOps (N - n)).gens (m5Cs X.O n N (N, fxs, ex)).2).length
              (m5Cs X.O n N (N, fxs, ex)).2.length β.BgP β.Bmem β.BkA β.BlA β.Bg1₂ₐ β.Bgen₂ₐ
              sIn B.Bstab B.Borb β.Bpb w.1.length s β.sK β.Bgm β.Blift β.Bker β.Bgn + 30 := by
          unfold m5Wns
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
        obtain ⟨X₀, hX₀, ans, ch, hrun, hok', hg, hch⟩ := RunsWithin.m5Case2bProg_part hO2b
          hP2b hOrd hPrd hI B hGG₀ Bm hG halt (m5Fmap_loc hC φ k hwS) (m5Fmap_relabel hC φ k)
          hFxv hFyv hFxs hFys hFx₀ hFy₀ hFxe hFye hFxi hFyi hΦxn hΦxl hΦx2 hΦxo hΦyn hΦyl
          hΦy2 hΦyo (hngx h2 hA') (hngy h2y hAy') hBg hBgP hBmem hBkA hBlA hBg1₂ᵦ hBgen₂ᵦ
          hsubI hB hs hLg (by omega) hst hD₂ᵦ (hpart₂ᵦ hsel)
        refine ⟨ans, ch, (m5Dispatch_run2 h2 (m5_run2b hok hA' hrun)).mono ?_, hok', hg, ?_⟩
        · rw [m5CK_of_ne (by rw [hsel]; decide), m5CH_of_ne (by rw [hsel]; decide)]
          have hW : m5Wns X.O n N k s sIn Bgen Blift Bo Bd (N, gs, d) (N, fxs, ex)
              (N, fys, ey) w.1.length β B.Bstab B.Btr B.Borb Bk'.Bgen Bk'.Borb Bk'.Bstab
              (fun M => (Bm M).Borb) (fun M => (Bm M).Bstab) (fun M => (Bm M).Btr) =
              Case2b.c2bCost n N sIn gs.length (m5Cs X.O n N (N, fxs, ex)).2.length
                (m5Cs X.O n N (N, fys, ey)).2.length
                (Case2b.degD X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 - 1)
                (Case2b.outGensD (N - n) X₀).length B.Bstab β.Bg (Case2b.sojZ (N - n)) β.BgP
                β.Bmem β.BkA β.BlA β.Bg1₂ᵦ β.Bgen₂ᵦ
                (m5Wb N n w.1.length s sIn (N - n) Bd Blift Bgen Bo 0)
                (fun M => (Bm M).Borb) (fun M => (Bm M).Bstab) (fun M => (Bm M).Btr) + 28 := by
            unfold m5Wns
            rw [hsel]
            simp only
            rw [hX₀]
          rw [hW]
          simp only [m5Wb]
          omega
        · have hF : m5CFns X.O n N k (N, fxs, ex) (N, fys, ey) =
              Case2b.c2bR N n (m5Cs X.O n N (N, fys, ey)).2.length
                (Case2b.degD X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 - 1)
                (Case2b.sojZ (N - n)) * (N - n) := by
            unfold m5CFns
            rw [hsel]
            rfl
          rw [hF]
          exact hch
    · -- Case 2 for `x`, not in the same way for `y`: no isomorphism
      have hsel : m5Sel X.O n N (N, fxs, ex) (N, fys, ey) = 0 := by
        unfold m5Sel
        rw [if_neg' h1, if_pos' h2, if_neg' hok]
      refine ⟨none, [], (m5Dispatch_run2 h2 (m5_run2_none (Bool.eq_false_iff.2 hok))).mono ?_, ?_,
        by simp, ⟨by simp, by simp, by simp⟩⟩
      · rw [m5CK_of_ne (by rw [hsel]; decide), m5CH_of_ne (by rw [hsel]; decide)]
        have hW : m5Wns X.O n N k s sIn Bgen Blift Bo Bd (N, gs, d) (N, fxs, ex)
            (N, fys, ey) w.1.length β B.Bstab B.Btr B.Borb Bk'.Bgen Bk'.Borb Bk'.Bstab
            (fun M => (Bm M).Borb) (fun M => (Bm M).Bstab) (fun M => (Bm M).Btr) = 28 := by
          unfold m5Wns
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
    obtain ⟨ans, ch, hrun, hok', hg, hch⟩ := RunsWithin.m5Case3Prog_part hO3 hP3 hOrd hPrd
      hI hφ halt hwS (m5Fmap_loc hC φ k hwS) (m5Fmap_relabel hC φ k) hFxe hFye hFxi hFyi hVxl
      hVxn hVyl hVyn hVxF hVyF hm6 h5 hk B hgs hGG₀ Bk' hsk hBgk hBlA hBgs hBgP hBmem hBkA
      hBg1₃ hBgen₃ hsubI hCmono hB hs hLg hst hD₃ (hnt₃ hsel) (hpart₃ hsel)
    obtain ⟨hbx, hox⟩ := m5_os_bounds hosx
    obtain ⟨hby, hoy⟩ := m5_os_bounds hosy
    refine ⟨ans, ch, (m5Dispatch_run3 h1 h2 hbx hox hby hoy hrun).mono ?_, hok', hg, ?_⟩
    · rw [m5CH_of_ne (by rw [hsel]; decide)]
      have hK : m5CK X.O n N k (N, fxs, ex) (N, fys, ey) =
          c3Count (fixPtsD (m5Os X.O n N (N, fxs, ex))).length k n := by
        unfold m5CK
        rw [if_pos' hsel]
      have hW : m5Wns X.O n N k s sIn Bgen Blift Bo Bd (N, gs, d) (N, fxs, ex)
          (N, fys, ey) w.1.length β B.Bstab B.Btr B.Borb Bk'.Bgen Bk'.Borb Bk'.Bstab
          (fun M => (Bm M).Borb) (fun M => (Bm M).Bstab) (fun M => (Bm M).Btr) =
          c3Work n N sIn gs.length k (fixPtsD (m5Os X.O n N (N, fxs, ex))).length
            (fixPtsD (m5Os X.O n N (N, fys, ey))).length (Case2b.sojZ (N - n)) β.BgP β.Bmem
            β.BkA β.BlA β.Bg1₃ β.Bgen₃ B.Bstab B.Btr B.Borb Bk'.Bgen Bk'.Borb Bk'.Bstab β.Bgk
            β.Bgs w.1.length
            (m5Wb N n w.1.length s sIn (N - n) Bd Blift Bgen Bo 0) +
          w.1.length + 3 + 2 * fixPtsCost (N - n) + 20 := by
        unfold m5Wns
        rw [hsel]
        rfl
      rw [hK, hW]
      simp only [m5Wb]
      omega
    · have hF : m5CFns X.O n N k (N, fxs, ex) (N, fys, ey) =
          Case3.c3R k (fixPtsD (m5Os X.O n N (N, fys, ey))).length (Case2b.sojZ (N - n)) *
            (N - n) := by
        unfold m5CFns
        rw [hsel]
        rfl
      rw [hF]
      exact hch


end DispatchNs

section CoreNs

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}
  {sub : HInstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)}
  {C : ℕ → Option ℕ → ℕ} {s : ℕ} {xy : StrData × StrData} {w : WinData}
  {N : ℕ} {gs : GensData} {d : D.denote} {n₀ n : ℕ} {L : LabelData} {st : ℕ × CJData}
  {sIn Lg Blift Bgen Bo Bk Bcr Bd : ℕ}

/-- **M5 on the restricted instance with no stuck orbit.** Under the hypotheses of
`RunsWithin.m5CoreProg`, with `m · (sIn + 1) ≤ Lg`, `st` not a coloured Johnson structure, and
for every pair of full groups `M5Full` allows, in Case 2b a partition leaf and in Case 3 no
twins and a partition first structure (colored `t`-partitions with `4t ≤ 3m`): the answer is
correct for `I`, no orbit is stuck and Case 3 never runs the kernel reduction. The children's
factor is `m5CFns` and the work `m5CoreWorkNs`. -/
theorem RunsWithin.m5CoreProg_ns (hO : MeetsContractOn DV m5Ops X.O)
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
      m5Leaf2b X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 = some X₀ →
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
        (fixPtsD (m5Os X.O n N (N, fxs, ex))) X₀ →
      ∃ (p : CPart (Fin (N - n))) (t : ℕ), (Case2b.outOps (N - n)).dec X₀ = some (Sum.inl p) ∧
        IsColPart Finset.univ t p ∧ 4 * t ≤ 3 * (N - n)) :
    ∃ (fxs fys : GensData) (ex ey : D.denote) (ans : AnswerData D) (ch : List (ℕ × Option ℕ)),
      M5Full DV hC φ k sIn xy.1 fxs ex ∧ M5Full DV hC φ k sIn xy.2 fys ey ∧
      RunsWithin X body (Main.m5CoreProg sub
          (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D) k st) ans
        ((ch.map fun x => C x.1 x.2).sum + 2 * certCount N n k * C (n / k) none +
          m5CK X.O n N k (N, fxs, ex) (N, fys, ey) * C (n / k) none +
          m5CH X.O n N sIn w.1.length (N, fxs, ex) (N, fys, ey) * C (w.1.length / 2) none +
          m5CoreWorkNs X.O n N k s sIn Bgen Blift Bo Bd (N, gs, d) (N, fxs, ex)
            (N, fys, ey) w.1.length β B.Bstab B.Btr B.Borb Bk'.Bgen Bk'.Borb Bk'.Bstab
            (fun M => (Bm M).Borb) (fun M => (Bm M).Bstab) (fun M => (Bm M).Btr)) ∧
      InstData.OK (D := D) (xy, w, PermData.one N, N, gs, d) DV ans ∧
      (∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sIn) ∧
      ChildList w.1.length (m5CFns X.O n N k (N, fxs, ex) (N, fys, ey))
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
  obtain ⟨ans, ch, hrun, hok, hg, hch⟩ := RunsWithin.m5Dispatch_ns hO hPre hI hφ halt hwS h5 hk
    hm12 B hgs hGG₀ Bk' hsk Bm hsub hCmono hs hB hLg hst β hFx.1 hFy.1 hFx.2.1 hFy.2.1 hFx.2.2
    hFy.2.2 hBgP hBmem hBkA hBlA hBg hBgk hBgs (hBox _ _ hFx)
    (hBoy _ _ hFy) (hBg1₁ _ _ hFx) (hD₁ _ _ hFx) (hBg1₂ₐ _ _ hFx) hBgen₂ₐ
    (fun gs' hv hl h0 => hBpb gs' hv (hl.trans (Nat.add_le_add_left hFx.2.1 _)) h0) hBgm hBlift
    hBker hsK hBgn (hBg1₂ᵦ _ _ hFx) (hBgen₂ᵦ _ _ hFy) (hD₂ᵦ _ _ hFx)
    (hpart₂ᵦ _ _ _ _ hFx hFy) (hBg1₃ _ _ hFx) (hBgen₃ _ _ hFy) (hD₃ _ _ hFx)
    (hnt₃ _ _ _ _ hFx hFy) (hpart₃ _ _ _ _ hFx hFy)
  refine ⟨fxs, fys, ex, ey, ans, ch, hFx, hFy,
    (m5CoreProg_run hrx hry hcx hcy hrun).mono ?_, ?_, hg, hch⟩
  · have e1 := fullCost_le_count N n k sIn B.Bstab B.Btr B.Borb Bk'.Bgen Bk'.Borb Bk'.Bstab
      β.Bgk (C (n / k) none + 4) β.BlA β.Bgs β.BF
    unfold m5CoreWorkNs
    linarith
  · show AnsOK DV N (w.denote N) (PermData.denote N (PermData.one N)) (GensData.denote N gs)
      (xy.1.denote N) (xy.2.denote N) ans
    rw [PermData.denote_one]
    exact hok


end CoreNs

end GraphIso.Main
