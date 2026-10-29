module

public import GraphIso.Main.FullStep

/-!
# The full procedure: the step, the recursion and the headline

Stage 14j-5d, items 6–8 (`PLAN-14.md` §14.9).

* `caseWork`, `mainTestCost`, `mainWork`: the work of one step of the procedure, an explicit
  function of the instance's sizes: the dispatch's tests plus the work of the step it takes
  (`mainCase`), as stage 14j-5c computes it.
* `caseF`, `caseA`, `caseB`: the bounds on the children's factor and on M5's counted calls.
* `main_step`: one step of the procedure, for every sub-solver cost `C` monotone in the window
  without a hint, from the recursive call solving every smaller instance of the domain within
  `C`. `main_step_lab` (stage 14j-6a, `PLAN-14.md` §14.10): the same for a parent with
  `LabInv`, from the recursive call solving the smaller instances of the domain with `LabInv`
  (`MainSubL`), the form stage 14j-6c's induction uses. Both are cases of `main_step_gen`.
* `mainW`, `mainA`, `mainCost`: the work and multiplicity bounds on the domain (monotone
  envelopes, `workEnv`), and the cost bound `miniC mainA mainW` at the rank of the measure.
* `main_spec`: correctness and cost on the domain, by strong induction on the rank.
* `mainSolve_ss`: the entry on every valid instance, for every threshold program with
  `ThrSpec`; `mainSolve_ss_const`: at constant thresholds, with no hypothesis.
* **The parameters at the domain's bounds** (§14.9 item 4): `caseWorkDom` is each case's work
  with M4's `Lg = domLgM4 NB s` and M5's `Lg = domLgM5 NB s`, `uB = NB`, the parameters of
  `main_m4_dom` and `main_m5_dom`. It bounds the instance-level work (`caseWork_le_dom`), so
  `mainW ≤ mainWDom` and the headline holds at `mainWDom` (`main_spec_dom`,
  `mainSolve_ss_dom`).

The cost is exponential in the rank, as the mini procedure's: M3 branches over up to `m!`
cosets. The quasipolynomial bound is stage 14j-6's.
-/

@[expose] public section

namespace GraphIso.Main

open Equiv Cost GraphIso GraphIso.Programs GraphIso.Toolkit GraphIso.Recursion Sims

/-! ### The work and the multiplicities of a step -/

section Work

/-- **The work of each case**, for `n` string positions, degree `N`, a window of `p` points,
`g` generators, the domain's generator bound `s`, M5's `k` and M4's `j`. -/
def caseWork : MainCase → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  | .base, _, _, p, _, _, _, _ => fixedStepCost p
  | .chain, _, N, p, _, _, _, _ => chainCost N p p
  | .m0, n, N, p, g, s, _, _ => m0WorkSS n N p g s
  | .m1, n, N, p, g, s, _, _ => m1WorkSS n (N - n) p g s
  | .m2a, n, N, p, g, s, _, _ => m2aWorkSS n (N - n) p g s n
  | .m2b, n, N, p, g, s, _, _ => m2bWorkSS n (N - n) p g n s
  | .m3, n, N, p, g, s, _, _ => m3WorkSS n N p g s
  | .m4, n, N, p, _, s, _, j => m4WorkSS n (N - n) j p s n s (ssLgM4 (N - n) j s)
  | .m5, n, N, p, g, s, k, _ =>
    rbOverSS N p (N - n) g s + m5WorkSS p (N - n) k p s s (ssLgM5 (N - n) k s) (N - n)

/-- **The dispatch's tests**, over every path: the base-case test, the window's orbits, the
hinted prefix, the block test, the equidistribution test and the large-base tests (with the
thresholds' cost `t`). -/
def mainTestCost (n N p g s t : ℕ) : ℕ :=
  fixedTestCost p g + orbitsCost N g p + p + hintPreCost n N g + blkTestCost n N g +
    neqTestCost n N p + bigTestCost n N s t + 40

/-- **The work of one step** of the procedure on `I`: the tests and the work of the case it
takes, with the generator bound `s` and the thresholds `kf`, `ℓf` of cost `cT`. -/
def mainWork (kf ℓf cT : ℕ → ℕ) (s : ℕ) (I : HInstData Ty.unit) : ℕ :=
  mainTestCost I.n I.inst.degree I.winSize I.inst.2.2.2.gens.length s (cT I.n₀) +
    caseWork (mainCase kf ℓf I) I.n I.inst.degree I.winSize I.inst.2.2.2.gens.length s (kf I.n₀)
      (m4J ssCtx.O I.n (I.inst.degree, I.inst.2.2.2.gens, ()))

theorem mainWork_eq (kf ℓf cT : ℕ → ℕ) (s : ℕ) (xy : StrData × StrData) (w : WinData)
    (σd : PermData) (N : ℕ) (gs : GensData) (n₀ n : ℕ) (lab : Option LabelData) :
    mainWork kf ℓf cT s (((xy, w, σd, N, gs, ()), n₀, n, lab) : HInstData Ty.unit) =
      mainTestCost n N w.1.length gs.length s (cT n₀) +
        caseWork (mainCase kf ℓf (((xy, w, σd, N, gs, ()), n₀, n, lab) : HInstData Ty.unit)) n N
          w.1.length gs.length s (kf n₀) (m4J ssCtx.O n (N, gs, ())) := rfl

/-- **The children's factor** of each case: `1` for the chain rule, M0, M1 and M2a, the base
size for M2b, `m!` for M3, `m4R m j · m!` for M4 and `m5FB m k` for M5. -/
def caseF : MainCase → ℕ → ℕ → ℕ → ℕ → ℕ
  | .base, _, _, _, _ => 0
  | .chain, _, _, _, _ => 1
  | .m0, _, _, _, _ => 1
  | .m1, _, _, _, _ => 1
  | .m2a, _, _, _, _ => 1
  | .m2b, n, N, _, _ => N - n
  | .m3, n, N, _, _ => (N - n).factorial
  | .m4, n, N, _, j => m4R (N - n) j * (N - n).factorial
  | .m5, n, N, k, _ => m5FB (N - n) k

/-- **M5's counted calls on `p / k` points**: the certificates and Case 3's. -/
def caseA : MainCase → ℕ → ℕ → ℕ → ℕ → ℕ
  | .m5, n, N, p, k => 2 * certCount (p + (N - n)) p k + 2 * c3Count (N - n) k p
  | _, _, _, _, _ => 0

/-- **M5's counted calls on `p / 2` points**: Case 2a's. -/
def caseB : MainCase → ℕ → ℕ → ℕ
  | .m5, p, s => (s + 1) * p
  | _, _, _ => 0

end Work

/-! ### One step -/

section Step

variable {thr : ThrProg Ty.unit} {kf ℓf cT : ℕ → ℕ} {n₀ nB NB : ℕ}

/-- **The hinted dispatch inside the body**: the base-case test fails, and the hint is read. -/
theorem main_top_hint {xy : StrData × StrData} {w : WinData} {σd : PermData} {N : ℕ}
    {gs : GensData} {n₀' n : ℕ} {L : LabelData} (hfx : GensData.fixesB gs w = false)
    {ans : AnswerData Ty.unit} {c : ℕ}
    (h : RunsWithin ssCtx (mainBody thr Ty.denote) (Main.hintProg thr (fun J => Prog.recur J)
      (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit) L) ans c) :
    RunsWithin ssCtx (mainBody thr Ty.denote) (mainBody thr Ty.denote
      (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit)) ans
      (c + (fixedTestCost w.1.length gs.length + 5)) := by
  have ht : RunsWithin ssCtx (mainBody thr Ty.denote)
      (Main.fixedTestProg (S := groupSig Ty.unit)
        (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit))
      (GensData.fixesB gs w) (fixedTestCost w.1.length gs.length) :=
    RunsWithin.fixedTestProg _
  rw [hfx] at ht
  apply RunsWithin.mono
  case h =>
    run_step ht
    apply RunsWithin.ite_false
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.caseOption_some h
  case hc =>
    simp only [Prim.cost]
    clear * -
    omega

/-- **One step of the full procedure, with the label invariant when `b` holds** (stages
14j-5d and 14j-6a): `main_step` for `b = false` and `main_step_lab` for `b = true`. -/
theorem main_step_gen {b : Bool} (hT : ThrSpec thr kf ℓf cT) (h2 : 2 * nB ≤ NB)
    {I : HInstData Ty.unit} (hI : HInstValid ssDV I) (hd : MiniDom n₀ nB NB I)
    {C : ℕ → Option ℕ → ℕ} (hC : ∀ a b, a ≤ b → C a none ≤ C b none)
    (hsub : MainSubB thr b n₀ nB NB I C)
    (hbL : LabInvIf b I) :
    ∃ (ans : AnswerData Ty.unit) (ch : List (ℕ × Option ℕ)) (F a b : ℕ),
      RunsWithin ssCtx (mainBody thr Ty.denote) (mainBody thr Ty.denote I) ans
        ((ch.map fun x => C x.1 x.2).sum + a * C (I.winSize / kf I.n₀) none +
          b * C (I.winSize / 2) none + mainWork kf ℓf cT (NB * NB) I) ∧
      I.inst.OK ssDV ans ∧ (∀ c : CosetData Ty.unit, ans = some c → c.2.gens.length ≤ NB * NB) ∧
      ChildList I.winSize F (casePred (mainCase kf ℓf I) I.winSize (I.inst.degree - I.n)) ch ∧
      F ≤ caseF (mainCase kf ℓf I) I.n I.inst.degree (kf I.n₀)
        (m4J ssCtx.O I.n (I.inst.degree, I.inst.2.2.2.gens, ())) ∧
      a ≤ caseA (mainCase kf ℓf I) I.n I.inst.degree I.winSize (kf I.n₀) ∧
      b ≤ caseB (mainCase kf ℓf I) I.winSize (NB * NB) := by
  obtain ⟨⟨xy, w, σd, N, gs, d⟩, n₀', n, lab⟩ := I
  cases d
  have hv : InstData.Valid (D := Ty.unit) (xy, w, σd, N, gs, ()) ssDV := hI.valid
  have hgs : GensData.AllValid N gs := hv.group.1
  have hwn := sh_length_le hI
  have hn : n ≤ nB := hd.n_le
  have hN : N ≤ NB := hd.degree_le
  have hgl : gs.length ≤ NB * NB := hd.gens_le
  have ht : RunsWithin ssCtx (mainBody thr Ty.denote)
      (Main.fixedTestProg (S := groupSig Ty.unit)
        (((xy, w, σd, N, gs, ()), n₀', n, lab) : HInstData Ty.unit))
      (GensData.fixesB gs w) (fixedTestCost w.1.length gs.length) :=
    RunsWithin.fixedTestProg _
  cases hfx : GensData.fixesB gs w with
  | true =>
    rw [hfx] at ht
    obtain ⟨ans, hrun, hok, hg⟩ := RunsWithin.fixedStepProg (X := ssCtx)
      (body := mainBody thr Ty.denote) (n₀ := n₀') (n := n) (lab := lab) hv
      ((GensData.fixesB_iff hv.group.1 hv.win).1 hfx)
    have hc : mainCase kf ℓf (((xy, w, σd, N, gs, ()), n₀', n, lab) : HInstData Ty.unit) =
        .base := by
      simp [mainCase, hfx]
    refine ⟨ans, [], 0, 0, 0, ?_, hok, fun c hc => (hg c hc).trans hgl,
      ⟨by simp, by simp, by simp⟩, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩
    apply RunsWithin.mono
    case h =>
      run_step ht
      exact RunsWithin.ite_true hrun
    case hc =>
      rw [mainWork_eq, hc]
      simp only [caseWork, mainTestCost, List.map_nil, List.sum_nil, Nat.zero_mul]
      clear * -
      omega
  | false =>
    rw [hfx] at ht
    have hnfix : ¬ FixesPointwise (GensData.denote N gs) (w.denote N) := fun h => by
      have : GensData.fixesB gs w = true := (GensData.fixesB_iff hv.group.1 hv.win).2 h
      rw [hfx] at this
      exact Bool.false_ne_true this
    rcases lab with _ | L
    · obtain ⟨hrunO, hos⟩ := RunsWithin.winOrbitsProg (X := ssCtx)
        (body := mainBody thr Ty.denote) (n₀ := n₀') (n := n) (lab := none)
        (fun op x _ hx => ssOracle_meets op x hx) (fun _ h => h) hv
      have hosl := IsOrbitPartition.length_le_win hos
      have hBo : ssCtx.B.call GroupOp.orbits ((N, gs, ()), w)
          (ssCtx.O.run GroupOp.orbits ((N, gs, ()), w)) ≤ orbitsCost N gs.length w.1.length + 5 :=
        le_rfl
      have hrunO' := hrunO.mono (Nat.add_le_add_left hBo 6)
      by_cases hmany : 2 ≤ (ssCtx.O.run GroupOp.orbits ((N, gs, ()), w)).length
      · obtain ⟨ans, ch, hrun, hok, hg, hch⟩ := main_chain h2 hI hd hsub hbL hos hmany
        have hc : mainCase kf ℓf (((xy, w, σd, N, gs, ()), n₀', n, none) : HInstData Ty.unit) =
            .chain := by
          simp [mainCase, hfx, hmany]
        refine ⟨ans, ch, 1, 0, 0, ?_, hok, hg, by rw [hc]; exact hch, by rw [hc]; exact le_rfl,
          by rw [hc]; exact le_rfl, by rw [hc]; exact le_rfl⟩
        apply RunsWithin.mono
        case h =>
          run_step ht
          apply RunsWithin.ite_false
          run_step (RunsWithin.prim _ _)
          run_step (RunsWithin.prim _ _)
          run_step (RunsWithin.prim _ _)
          apply RunsWithin.caseOption_none
          run_step hrunO'
          run_step (RunsWithin.prim_le (c := w.1.length + 1) rfl (Nat.add_le_add_right hosl 1))
          run_step (RunsWithin.prim _ _)
          run_step (RunsWithin.prim_le (v := true)
            (show decide (1 < (ssCtx.O.run GroupOp.orbits ((N, gs, ()), w)).length) = true from
              decide_eq_true (by omega)) le_rfl)
          exact RunsWithin.ite_true hrun
        case hc =>
          rw [mainWork_eq, hc]
          simp only [caseWork, mainTestCost, Prim.cost, Nat.zero_mul]
          generalize (ch.map fun x => C x.1 x.2).sum = sc
          clear * -
          omega
      · have hone : (ssCtx.O.run GroupOp.orbits ((N, gs, ()), w)).length ≤ 1 := by omega
        obtain ⟨htr, h2w⟩ := mini_m0_case hv.invariant hnfix hos hone
        obtain ⟨ans, ch, hrun, hok, hg, hch⟩ := main_m0 h2 hI hd hsub hbL htr h2w
        have hc : mainCase kf ℓf (((xy, w, σd, N, gs, ()), n₀', n, none) : HInstData Ty.unit) =
            .m0 := by
          simp [mainCase, hfx, hmany]
        refine ⟨ans, ch, 1, 0, 0, ?_, hok, hg, by rw [hc]; exact hch, by rw [hc]; exact le_rfl,
          by rw [hc]; exact le_rfl, by rw [hc]; exact le_rfl⟩
        apply RunsWithin.mono
        case h =>
          run_step ht
          apply RunsWithin.ite_false
          run_step (RunsWithin.prim _ _)
          run_step (RunsWithin.prim _ _)
          run_step (RunsWithin.prim _ _)
          apply RunsWithin.caseOption_none
          run_step hrunO'
          run_step (RunsWithin.prim_le (c := w.1.length + 1) rfl (Nat.add_le_add_right hosl 1))
          run_step (RunsWithin.prim _ _)
          run_step (RunsWithin.prim_le (v := false)
            (show decide (1 < (ssCtx.O.run GroupOp.orbits ((N, gs, ()), w)).length) = false from
              decide_eq_false (by omega)) le_rfl)
          exact RunsWithin.ite_false hrun
        case hc =>
          rw [mainWork_eq, hc]
          simp only [caseWork, mainTestCost, Prim.cost, Nat.zero_mul]
          generalize (ch.map fun x => C x.1 x.2).sum = sc
          clear * -
          omega
    · have hm : 1 ≤ N - n := hI.base_pos rfl
      have hb : IsInvariant (GensData.denote N gs) (baseSet n N) := hI.base_inv
      have hnN : n ≤ N := hI.le
      have hNN : N * N ≤ NB * NB := Nat.mul_le_mul hN hN
      have hI' := HInstValid.normLab hI
      have hd' : MiniDom n₀ nB NB
          (((xy, w, σd, N, gs, ()), n₀', n, some (normLabD n L)) : HInstData Ty.unit) :=
        ⟨hd.n₀, hd.n_le, hd.degree_le, hd.gens_le⟩
      have hsub' : MainSubB thr b n₀ nB NB
          (((xy, w, σd, N, gs, ()), n₀', n, some (normLabD n L)) : HInstData Ty.unit) C := hsub
      have hbL' := LabInvIf.normLab hbL
      have hos : IsOrbitPartition (GensData.denote N gs) (baseWin n N)
          (ssCtx.O.run GroupOp.orbits ((N, gs, ()), baseWin n N)) := ss_baseOrbits hgs hb
      have hLs : (normLabD n L).size = n := normLabD_size n L
      by_cases hsplit : 2 ≤ (ssCtx.O.run GroupOp.orbits ((N, gs, ()), baseWin n N)).length
      · have hnt : ¬ IsTransOn (GensData.denote N gs) (baseSet n N) := fun h => by
          have := (base_trans_iff hos).1 h
          omega
        obtain ⟨ans, ch, hrun, hok, hg, hch⟩ := main_m1 h2 hI' hd' hsub' hbL' hnt
        have hc : mainCase kf ℓf (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit) =
            .m1 := by
          simp [mainCase, hintCase, hfx, hsplit]
        refine ⟨ans, ch, 1, 0, 0,
          (main_top_hint hfx (RunsWithin.hintProg_m1 hgs hb hsplit hrun)).mono ?_, hok, hg,
          by rw [hc]; exact hch, by rw [hc]; exact le_rfl, by rw [hc]; exact le_rfl,
          by rw [hc]; exact le_rfl⟩
        rw [mainWork_eq, hc]
        simp only [caseWork, mainTestCost, Nat.zero_mul]
        generalize (ch.map fun x => C x.1 x.2).sum = sc
        clear * -
        omega
      have hone : (ssCtx.O.run GroupOp.orbits ((N, gs, ()), baseWin n N)).length ≤ 1 := by omega
      have htrB : IsTransOn (GensData.denote N gs) (baseSet n N) := (base_trans_iff hos).2 hone
      cases hok : blkOKD (N - n) (mbD n N gs) with
      | true =>
        obtain ⟨-, -, -, -, -, hflat, h2bs⟩ := ss_mb_facts hI htrB hok
        have hh' : HintValid n N gs w (normLabD n L) := (hI'.hint _ rfl).1
        have hT : ∀ u ∈ w.1, ((normLabD n L).getD u []).length ≤ N - n := fun u hu =>
          mf_length_le_of_nodup (hh'.lab_nodup u hu) (hh'.lab_lt u hu)
        cases hne : neqD n N (mbD n N gs) (normLabD n L) w.1 with
        | true =>
          obtain ⟨ans, ch, hrun, hok', hg, hch⟩ := main_m2a h2 hI' hd' hsub' hbL' htrB hok hne
          have hc : mainCase kf ℓf (((xy, w, σd, N, gs, ()), n₀', n, some L) :
              HInstData Ty.unit) = .m2a := by
            simp [mainCase, hintCase, hfx, hsplit, hok, hne]
          refine ⟨ans, ch, 1, 0, 0, (main_top_hint hfx (RunsWithin.hintProg_m2a hgs hb hone hok
            hflat.le (by omega) hT hne hrun)).mono ?_, hok', hg, by rw [hc]; exact hch,
            by rw [hc]; exact le_rfl, by rw [hc]; exact le_rfl, by rw [hc]; exact le_rfl⟩
          rw [mainWork_eq, hc, hLs]
          simp only [caseWork, mainTestCost, Nat.zero_mul]
          generalize (ch.map fun x => C x.1 x.2).sum = sc
          clear * -
          omega
        | false =>
          obtain ⟨ans, ch, hrun, hok', hg, hch⟩ := main_m2b h2 hI' hd' hsub' hbL' htrB hok hne
          have hc : mainCase kf ℓf (((xy, w, σd, N, gs, ()), n₀', n, some L) :
              HInstData Ty.unit) = .m2b := by
            simp [mainCase, hintCase, hfx, hsplit, hok, hne]
          refine ⟨ans, ch, N - n, 0, 0, (main_top_hint hfx (RunsWithin.hintProg_m2b hgs hb hone
            hok hflat.le (by omega) hT hne hrun)).mono ?_, hok', hg, by rw [hc]; exact hch,
            by rw [hc]; exact le_rfl, by rw [hc]; exact le_rfl, by rw [hc]; exact le_rfl⟩
          rw [mainWork_eq, hc, hLs]
          simp only [caseWork, mainTestCost, Nat.zero_mul]
          generalize (ch.map fun x => C x.1 x.2).sum = sc
          clear * -
          omega
      | false =>
        obtain ⟨ans₃, ch₃, hrun₃, hok₃, hg₃, hch₃⟩ := main_m3 h2 hI' hd' hsub' hbL'
        have hB := ssBoundsS N (NB * NB) ⊤ hNN
        by_cases hℓ : ℓf n₀' < N - n
        · have hdegs := degreeModel_spec (cap := N - n - 2) (d := ())
            (fun op x _ hx => ssOracle_meets op x hx) hB ⟨hgs, trivial⟩ hgl le_top hb hnN (by omega)
          by_cases hgi : m4Deg ssCtx.O n (N, gs, ()) = N - n - 2
          · have halt : alternatingGroup (Fin (N - n)) ≤
                (baseHom (GensData.denote N gs) n hI.base_inv).range :=
              (giantModel_iff (d := ()) (fun op x _ hx => ssOracle_meets op x hx) hB ⟨hgs, trivial⟩
                hgl le_top hb hnN).1 (beq_iff_eq.2 hgi)
            cases h5 : m5OkD (kf n₀') (N - n) with
            | true =>
              obtain ⟨hk5, h2k, h12⟩ := m5OkD_iff.1 h5
              obtain ⟨ans, ch, F, a, b, hrun, hok', hg, hch, hF, ha, hb'⟩ :=
                main_m5 h2 hI' hd' hsub' hbL' hC halt hk5 h2k h12
              have hc : mainCase kf ℓf (((xy, w, σd, N, gs, ()), n₀', n, some L) :
                  HInstData Ty.unit) = .m5 := by
                simp [mainCase, hintCase, bigCase, hfx, hsplit, hok, hℓ, hgi, h5]
              refine ⟨ans, ch, F, a, b, (main_top_hint hfx (RunsWithin.hintProg_big hgs hb hone
                hok (RunsWithin.bigProg_m5 (s := NB * NB) hT hgs hb hnN hgl hNN hℓ hgi h5
                  hrun))).mono ?_, hok', hg, by rw [hc]; exact hch, by rw [hc]; exact hF,
                by rw [hc]; exact ha, by rw [hc]; exact hb'⟩
              rw [mainWork_eq, hc]
              simp only [caseWork, mainTestCost]
              dsimp only [HInstData.winSize, HInstData.n₀, HInstData.inst]
              generalize (ch.map fun x => C x.1 x.2).sum = sc
              generalize a * C (w.1.length / kf n₀') none = sa
              generalize b * C (w.1.length / 2) none = sb
              clear * -
              omega
            | false =>
              have hc : mainCase kf ℓf (((xy, w, σd, N, gs, ()), n₀', n, some L) :
                  HInstData Ty.unit) = .m3 := by
                simp [mainCase, hintCase, bigCase, hfx, hsplit, hok, hℓ, hgi, h5]
              refine ⟨ans₃, ch₃, (N - n).factorial, 0, 0, (main_top_hint hfx
                (RunsWithin.hintProg_big hgs hb hone hok (RunsWithin.bigProg_m5_m3 (s := NB * NB)
                  hT hgs hb hnN hgl hNN hℓ hgi h5 hrun₃))).mono ?_, hok₃, hg₃,
                by rw [hc]; exact hch₃, by rw [hc]; exact le_rfl, by rw [hc]; exact le_rfl,
                by rw [hc]; exact le_rfl⟩
              rw [mainWork_eq, hc]
              simp only [caseWork, mainTestCost, Nat.zero_mul]
              generalize (ch₃.map fun x => C x.1 x.2).sum = sc
              clear * -
              omega
          · have hng : m4Deg ssCtx.O n (N, gs, ()) < N - n - 2 := lt_of_le_of_ne hdegs.1 hgi
            cases h4 : m4OkD (m4Deg ssCtx.O n (N, gs, ())) (N - n) with
            | true =>
              obtain ⟨hk4, hS⟩ := m4OkD_iff.1 h4
              obtain ⟨ans, ch, hrun, hok', hg, hch⟩ := main_m4 h2 hI' hd' hsub' hbL' htrB hng hk4 hS
              have hc : mainCase kf ℓf (((xy, w, σd, N, gs, ()), n₀', n, some L) :
                  HInstData Ty.unit) = .m4 := by
                simp [mainCase, hintCase, bigCase, hfx, hsplit, hok, hℓ, hgi, h4]
              refine ⟨ans, ch, m4R (N - n) (m4J ssCtx.O n (N, gs, ())) * (N - n).factorial, 0, 0,
                (main_top_hint hfx (RunsWithin.hintProg_big hgs hb hone hok
                  (RunsWithin.bigProg_m4 (s := NB * NB) hT hgs hb hnN hgl hNN hℓ hgi h4
                    hrun))).mono ?_, hok', hg, by rw [hc]; exact hch, by rw [hc]; exact le_rfl,
                by rw [hc]; exact le_rfl, by rw [hc]; exact le_rfl⟩
              rw [mainWork_eq, hc, hLs]
              simp only [caseWork, mainTestCost, Nat.zero_mul]
              generalize (ch.map fun x => C x.1 x.2).sum = sc
              clear * -
              omega
            | false =>
              have hc : mainCase kf ℓf (((xy, w, σd, N, gs, ()), n₀', n, some L) :
                  HInstData Ty.unit) = .m3 := by
                simp [mainCase, hintCase, bigCase, hfx, hsplit, hok, hℓ, hgi, h4]
              refine ⟨ans₃, ch₃, (N - n).factorial, 0, 0, (main_top_hint hfx
                (RunsWithin.hintProg_big hgs hb hone hok (RunsWithin.bigProg_m4_m3 (s := NB * NB)
                  hT hgs hb hnN hgl hNN hℓ hgi h4 hrun₃))).mono ?_, hok₃, hg₃,
                by rw [hc]; exact hch₃, by rw [hc]; exact le_rfl, by rw [hc]; exact le_rfl,
                by rw [hc]; exact le_rfl⟩
              rw [mainWork_eq, hc]
              simp only [caseWork, mainTestCost, Nat.zero_mul]
              generalize (ch₃.map fun x => C x.1 x.2).sum = sc
              clear * -
              omega
        · have hc : mainCase kf ℓf (((xy, w, σd, N, gs, ()), n₀', n, some L) :
              HInstData Ty.unit) = .m3 := by
            simp [mainCase, hintCase, bigCase, hfx, hsplit, hok, hℓ]
          refine ⟨ans₃, ch₃, (N - n).factorial, 0, 0, (main_top_hint hfx
            (RunsWithin.hintProg_big hgs hb hone hok (RunsWithin.bigProg_small (s := NB * NB)
              hT hℓ hrun₃))).mono ?_, hok₃, hg₃,
            by rw [hc]; exact hch₃, by rw [hc]; exact le_rfl, by rw [hc]; exact le_rfl,
            by rw [hc]; exact le_rfl⟩
          rw [mainWork_eq, hc]
          simp only [caseWork, mainTestCost, Nat.zero_mul]
          generalize (ch₃.map fun x => C x.1 x.2).sum = sc
          clear * -
          omega

/-- **One step of the full procedure** (`PLAN-14.md` §14.9, item 6). For every sub-solver cost
`C` that is monotone in the window without a hint, if the recursive call solves every valid
instance of the domain of smaller measure within `C` (`MainSub`), then the procedure on `I`
returns a correct answer with at most `NB²` generators, within the children's costs, `a` calls
on `p / k` and `b` on `p / 2` points without a hint (M5's counted calls), and the work
`mainWork`. The children satisfy the predicate of the case the dispatcher takes
(`mainCase`), with a factor `F`; `F`, `a` and `b` are at most that case's bounds. -/
theorem main_step (hT : ThrSpec thr kf ℓf cT) (h2 : 2 * nB ≤ NB) {I : HInstData Ty.unit}
    (hI : HInstValid ssDV I) (hd : MiniDom n₀ nB NB I) {C : ℕ → Option ℕ → ℕ}
    (hC : ∀ a b, a ≤ b → C a none ≤ C b none) (hsub : MainSub thr n₀ nB NB I C) :
    ∃ (ans : AnswerData Ty.unit) (ch : List (ℕ × Option ℕ)) (F a b : ℕ),
      RunsWithin ssCtx (mainBody thr Ty.denote) (mainBody thr Ty.denote I) ans
        ((ch.map fun x => C x.1 x.2).sum + a * C (I.winSize / kf I.n₀) none +
          b * C (I.winSize / 2) none + mainWork kf ℓf cT (NB * NB) I) ∧
      I.inst.OK ssDV ans ∧ (∀ c : CosetData Ty.unit, ans = some c → c.2.gens.length ≤ NB * NB) ∧
      ChildList I.winSize F (casePred (mainCase kf ℓf I) I.winSize (I.inst.degree - I.n)) ch ∧
      F ≤ caseF (mainCase kf ℓf I) I.n I.inst.degree (kf I.n₀)
        (m4J ssCtx.O I.n (I.inst.degree, I.inst.2.2.2.gens, ())) ∧
      a ≤ caseA (mainCase kf ℓf I) I.n I.inst.degree I.winSize (kf I.n₀) ∧
      b ≤ caseB (mainCase kf ℓf I) I.winSize (NB * NB) :=
  main_step_gen hT h2 hI hd hC hsub.toB fun h => absurd h Bool.false_ne_true

/-- **One step of the full procedure with the label invariant** (`PLAN-14.md` §14.10, item 6).
For a parent with `LabInv`, the conclusion of `main_step` holds when the recursive call solves
the domain's instances with `LabInv` of smaller measure (`MainSubL`): every child the step
passes to the recursive call has `LabInv` (`SizeChild.lab`). -/
theorem main_step_lab (hT : ThrSpec thr kf ℓf cT) (h2 : 2 * nB ≤ NB) {I : HInstData Ty.unit}
    (hI : HInstValid ssDV I) (hd : MiniDom n₀ nB NB I) (hIL : LabInv I) {C : ℕ → Option ℕ → ℕ}
    (hC : ∀ a b, a ≤ b → C a none ≤ C b none) (hsub : MainSubL thr n₀ nB NB I C) :
    ∃ (ans : AnswerData Ty.unit) (ch : List (ℕ × Option ℕ)) (F a b : ℕ),
      RunsWithin ssCtx (mainBody thr Ty.denote) (mainBody thr Ty.denote I) ans
        ((ch.map fun x => C x.1 x.2).sum + a * C (I.winSize / kf I.n₀) none +
          b * C (I.winSize / 2) none + mainWork kf ℓf cT (NB * NB) I) ∧
      I.inst.OK ssDV ans ∧ (∀ c : CosetData Ty.unit, ans = some c → c.2.gens.length ≤ NB * NB) ∧
      ChildList I.winSize F (casePred (mainCase kf ℓf I) I.winSize (I.inst.degree - I.n)) ch ∧
      F ≤ caseF (mainCase kf ℓf I) I.n I.inst.degree (kf I.n₀)
        (m4J ssCtx.O I.n (I.inst.degree, I.inst.2.2.2.gens, ())) ∧
      a ≤ caseA (mainCase kf ℓf I) I.n I.inst.degree I.winSize (kf I.n₀) ∧
      b ≤ caseB (mainCase kf ℓf I) I.winSize (NB * NB) :=
  main_step_gen hT h2 hI hd hC hsub.toB fun _ => hIL

end Step

/-! ### The case facts -/

section CaseFacts

variable {kf ℓf : ℕ → ℕ} {xy : StrData × StrData} {w : WinData} {σd : PermData} {N : ℕ}
  {gs : GensData} {n₀ n : ℕ}

/-- **M5's case** has a hint and meets M5's numeric test. -/
theorem mainCase_m5 {lab : Option LabelData}
    (h : mainCase kf ℓf (((xy, w, σd, N, gs, ()), n₀, n, lab) : HInstData Ty.unit) = .m5) :
    lab.isSome ∧ m5OkD (kf n₀) (N - n) = true := by
  rcases lab with _ | L
  · simp only [mainCase] at h
    split_ifs at h
  · simp only [mainCase, hintCase, bigCase] at h
    split_ifs at h
    simp_all

/-- **M4's case** has a hint and meets M4's numeric test. -/
theorem mainCase_m4 {lab : Option LabelData}
    (h : mainCase kf ℓf (((xy, w, σd, N, gs, ()), n₀, n, lab) : HInstData Ty.unit) = .m4) :
    lab.isSome ∧ m4OkD (m4Deg ssCtx.O n (N, gs, ())) (N - n) = true := by
  rcases lab with _ | L
  · simp only [mainCase] at h
    split_ifs at h
  · simp only [mainCase, hintCase, bigCase] at h
    split_ifs at h
    simp_all

/-- **Without a hint**, the case is the base case, the chain rule or M0. -/
theorem mainCase_none :
    mainCase kf ℓf (((xy, w, σd, N, gs, ()), n₀, n, none) : HInstData Ty.unit) = .base ∨
      mainCase kf ℓf (((xy, w, σd, N, gs, ()), n₀, n, none) : HInstData Ty.unit) = .chain ∨
      mainCase kf ℓf (((xy, w, σd, N, gs, ()), n₀, n, none) : HInstData Ty.unit) = .m0 := by
  simp only [mainCase]
  split_ifs <;> simp

/-- **With a hint**, the case is neither the chain rule nor M0. -/
theorem mainCase_some {L : LabelData} :
    mainCase kf ℓf (((xy, w, σd, N, gs, ()), n₀, n, some L) : HInstData Ty.unit) ≠ .chain ∧
      mainCase kf ℓf (((xy, w, σd, N, gs, ()), n₀, n, some L) : HInstData Ty.unit) ≠ .m0 := by
  simp only [mainCase, hintCase, bigCase]
  constructor <;> split_ifs <;> simp

end CaseFacts

/-! ### The bounds on the domain -/

section Bounds

/-- **The monotone envelope** of a function of the sizes `(n, N, p, g, k, j)` over the domain:
`n, p ≤ nB`, `N, k, j ≤ NB` and `g ≤ NB²`. -/
def workEnv (f : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (nB NB : ℕ) : ℕ :=
  envSup [nB, NB, nB, NB * NB, NB, NB] fun xs =>
    f (xs.getD 0 0) (xs.getD 1 0) (xs.getD 2 0) (xs.getD 3 0) (xs.getD 4 0) (xs.getD 5 0)

theorem le_workEnv (f : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) {nB NB n N p g k j : ℕ} (hn : n ≤ nB)
    (hN : N ≤ NB) (hp : p ≤ nB) (hg : g ≤ NB * NB) (hk : k ≤ NB) (hj : j ≤ NB) :
    f n N p g k j ≤ workEnv f nB NB := by
  unfold workEnv
  refine le_of_eq_of_le ?_ (le_envSup (.cons hn (.cons hN (.cons hp (.cons hg (.cons hk
    (.cons hj .nil)))))) _)
  simp only [List.getD_cons_zero, List.getD_cons_succ]

/-- The cases of the dispatcher, as a list. -/
def allCases : List MainCase := [.base, .chain, .m0, .m1, .m2a, .m2b, .m3, .m4, .m5]

theorem mem_allCases (c : MainCase) : c ∈ allCases := by
  cases c <;> simp [allCases]

/-- **The work bound on the domain**: the envelopes of the tests' cost and of every case's
work, with the thresholds' cost `t` and the generator bound `NB²`. -/
def mainW (t nB NB : ℕ) : ℕ :=
  workEnv (fun n N p g _ _ => mainTestCost n N p g (NB * NB) t) nB NB +
    (allCases.map fun c =>
      workEnv (fun n N p g k j => caseWork c n N p g (NB * NB) k j) nB NB).sum

/-- **The multiplicity bound on the domain**: the envelopes of every case's children (`caseF`
per window point) and counted calls. -/
def mainA (nB NB : ℕ) : ℕ :=
  (allCases.map fun c => nB * workEnv (fun n N _ _ k j => caseF c n N k j) nB NB +
    workEnv (fun n N p _ k _ => caseA c n N p k) nB NB +
    workEnv (fun _ _ p _ _ _ => caseB c p (NB * NB)) nB NB).sum

/-- **The cost bound of the full procedure** at rank `r`, with the thresholds' cost `t`:
`mainCost t nB NB 0 = W` and `mainCost t nB NB (r + 1) = A (1 + mainCost t nB NB r) + W`. -/
abbrev mainCost (t nB NB : ℕ) : ℕ → ℕ := miniC (mainA nB NB) (mainW t nB NB)

variable {nB NB : ℕ}

theorem caseWork_le_env {c : MainCase} {n N p g k j : ℕ} (hn : n ≤ nB) (hN : N ≤ NB)
    (hp : p ≤ nB) (hg : g ≤ NB * NB) (hk : c = .m5 → k ≤ NB) (hj : c = .m4 → j ≤ NB) :
    caseWork c n N p g (NB * NB) k j ≤
      workEnv (fun n N p g k j => caseWork c n N p g (NB * NB) k j) nB NB := by
  have key : ∀ k' j', k' ≤ NB → j' ≤ NB → caseWork c n N p g (NB * NB) k' j' ≤
      workEnv (fun n N p g k j => caseWork c n N p g (NB * NB) k j) nB NB := fun k' j' hk' hj' =>
    le_workEnv (fun n N p g k j => caseWork c n N p g (NB * NB) k j) hn hN hp hg hk' hj'
  cases c
  case m4 => exact key 0 j (Nat.zero_le _) (hj rfl)
  case m5 => exact key k 0 (hk rfl) (Nat.zero_le _)
  all_goals exact key 0 0 (Nat.zero_le _) (Nat.zero_le _)

theorem caseF_le_env {c : MainCase} {n N k j : ℕ} (hn : n ≤ nB) (hN : N ≤ NB)
    (hk : c = .m5 → k ≤ NB) (hj : c = .m4 → j ≤ NB) :
    caseF c n N k j ≤ workEnv (fun n N _ _ k j => caseF c n N k j) nB NB := by
  have key : ∀ k' j', k' ≤ NB → j' ≤ NB → caseF c n N k' j' ≤
      workEnv (fun n N _ _ k j => caseF c n N k j) nB NB := fun k' j' hk' hj' =>
    le_workEnv (fun n N _ _ k j => caseF c n N k j) hn hN (Nat.zero_le nB) (Nat.zero_le _) hk' hj'
  cases c
  case m4 => exact key 0 j (Nat.zero_le _) (hj rfl)
  case m5 => exact key k 0 (hk rfl) (Nat.zero_le _)
  all_goals exact key 0 0 (Nat.zero_le _) (Nat.zero_le _)

theorem caseA_le_env {c : MainCase} {n N p k : ℕ} (hn : n ≤ nB) (hN : N ≤ NB) (hp : p ≤ nB)
    (hk : c = .m5 → k ≤ NB) :
    caseA c n N p k ≤ workEnv (fun n N p _ k _ => caseA c n N p k) nB NB := by
  cases c
  case m5 =>
    exact le_workEnv (fun n N p _ k _ => caseA .m5 n N p k) hn hN hp (Nat.zero_le _) (hk rfl)
      (Nat.zero_le NB)
  all_goals exact Nat.zero_le _

theorem caseB_le_env {c : MainCase} {p : ℕ} (hp : p ≤ nB) :
    caseB c p (NB * NB) ≤ workEnv (fun _ _ p _ _ _ => caseB c p (NB * NB)) nB NB := by
  cases c
  case m5 =>
    exact le_workEnv (fun _ _ p _ _ _ => caseB .m5 p (NB * NB)) (n := 0) (N := 0)
      (Nat.zero_le _) (Nat.zero_le _) hp (Nat.zero_le _) (Nat.zero_le NB) (Nat.zero_le NB)
  all_goals exact Nat.zero_le _

variable {kf ℓf cT : ℕ → ℕ} {n₀ : ℕ}

/-- The case's parameters are in the domain: M5's `k` and M4's `j` are at most the base. -/
theorem mainCase_kj {xy : StrData × StrData} {w : WinData} {σd : PermData} {N : ℕ}
    {gs : GensData} {n₀' n : ℕ} {lab : Option LabelData} (hN : N ≤ NB) :
    (mainCase kf ℓf (((xy, w, σd, N, gs, ()), n₀', n, lab) : HInstData Ty.unit) = .m5 →
        kf n₀' ≤ NB) ∧
      (mainCase kf ℓf (((xy, w, σd, N, gs, ()), n₀', n, lab) : HInstData Ty.unit) = .m4 →
        m4J ssCtx.O n (N, gs, ()) ≤ NB) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := m5OkD_iff.1 (mainCase_m5 h).2
    omega
  · have := m4OkD_iff.1 (mainCase_m4 h).2
    change m4Deg ssCtx.O n (N, gs, ()) - 1 ≤ NB
    omega

/-- **The work of a step is at most `mainW`** on the domain. -/
theorem mainWork_le {I : HInstData Ty.unit} (hI : HInstValid ssDV I) (hd : MiniDom n₀ nB NB I) :
    mainWork kf ℓf cT (NB * NB) I ≤ mainW (cT n₀) nB NB := by
  obtain ⟨⟨xy, w, σd, N, gs, d⟩, n₀', n, lab⟩ := I
  cases d
  have hn₀ : n₀' = n₀ := hd.n₀
  subst hn₀
  have hwn := sh_length_le hI
  have hn : n ≤ nB := hd.n_le
  have hN : N ≤ NB := hd.degree_le
  have hgl : gs.length ≤ NB * NB := hd.gens_le
  obtain ⟨hk, hj⟩ := mainCase_kj (kf := kf) (ℓf := ℓf) (xy := xy) (w := w) (σd := σd) (gs := gs)
    (n₀' := n₀') (n := n) (lab := lab) hN
  have h1 := le_workEnv (fun n N p g _ _ => mainTestCost n N p g (NB * NB) (cT n₀')) hn hN
    (hwn.trans hn) hgl (Nat.zero_le NB) (Nat.zero_le NB)
  have h2 := caseWork_le_env hn hN (hwn.trans hn) hgl hk hj
  have h3 := le_sum_of_mem_nat (List.mem_map.2 ⟨mainCase kf ℓf
    (((xy, w, σd, N, gs, ()), n₀', n, lab) : HInstData Ty.unit), mem_allCases _, rfl⟩) (l :=
    allCases.map fun c => workEnv (fun n N p g k j => caseWork c n N p g (NB * NB) k j) nB NB)
  rw [mainWork_eq]
  unfold mainW
  exact Nat.add_le_add h1 (h2.trans h3)

/-- **The sub-calls of a step number at most `mainA`** on the domain: the children (at most
`F` per window point) and M5's counted calls. -/
theorem main_count_le {I : HInstData Ty.unit} (hI : HInstValid ssDV I) (hd : MiniDom n₀ nB NB I)
    {P : ℕ × Option ℕ → Prop} {ch : List (ℕ × Option ℕ)} {F a b : ℕ}
    (hch : ChildList I.winSize F P ch)
    (hF : F ≤ caseF (mainCase kf ℓf I) I.n I.inst.degree (kf I.n₀)
      (m4J ssCtx.O I.n (I.inst.degree, I.inst.2.2.2.gens, ())))
    (ha : a ≤ caseA (mainCase kf ℓf I) I.n I.inst.degree I.winSize (kf I.n₀))
    (hb : b ≤ caseB (mainCase kf ℓf I) I.winSize (NB * NB)) :
    ch.length + a + b ≤ mainA nB NB := by
  obtain ⟨⟨xy, w, σd, N, gs, d⟩, n₀', n, lab⟩ := I
  cases d
  have hwn := sh_length_le hI
  have hn : n ≤ nB := hd.n_le
  have hN : N ≤ NB := hd.degree_le
  obtain ⟨hk, hj⟩ := mainCase_kj (kf := kf) (ℓf := ℓf) (xy := xy) (w := w) (σd := σd) (gs := gs)
    (n₀' := n₀') (n := n) (lab := lab) hN
  have hl : ch.length ≤ F * w.1.length := hch.length_le
  change F ≤ caseF (mainCase kf ℓf (((xy, w, σd, N, gs, ()), n₀', n, lab) : HInstData Ty.unit))
    n N (kf n₀') (m4J ssCtx.O n (N, gs, ())) at hF
  change a ≤ caseA (mainCase kf ℓf (((xy, w, σd, N, gs, ()), n₀', n, lab) : HInstData Ty.unit))
    n N w.1.length (kf n₀') at ha
  change b ≤ caseB (mainCase kf ℓf (((xy, w, σd, N, gs, ()), n₀', n, lab) : HInstData Ty.unit))
    w.1.length (NB * NB) at hb
  generalize mainCase kf ℓf (((xy, w, σd, N, gs, ()), n₀', n, lab) : HInstData Ty.unit) = c
    at hF ha hb hk hj
  have h1 := caseF_le_env (nB := nB) hn hN hk hj
  have h2 := caseA_le_env (nB := nB) hn hN (hwn.trans hn) hk
  have h3 := caseB_le_env (NB := NB) (c := c) (hwn.trans hn)
  have h4 := le_sum_of_mem_nat (List.mem_map.2 ⟨c, mem_allCases c, rfl⟩) (l :=
    allCases.map fun c => nB * workEnv (fun n N _ _ k j => caseF c n N k j) nB NB +
      workEnv (fun n N p _ k _ => caseA c n N p k) nB NB +
      workEnv (fun _ _ p _ _ _ => caseB c p (NB * NB)) nB NB)
  have h5 : F * w.1.length ≤ nB * workEnv (fun n N _ _ k j => caseF c n N k j) nB NB := by
    rw [Nat.mul_comm F]
    exact Nat.mul_le_mul (hwn.trans hn) (hF.trans h1)
  unfold mainA
  exact (Nat.add_le_add (Nat.add_le_add (hl.trans h5) (ha.trans h2)) (hb.trans h3)).trans h4

/-! #### The work at the domain's parameters -/

/-- **The work of each case at the domain's parameters**: as `caseWork`, with M4's
`Lg = domLgM4 NB s` and M5's `Lg = domLgM5 NB s` and `uB = NB` (`main_m4_dom`,
`main_m5_dom`). -/
def caseWorkDom (NB : ℕ) : MainCase → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  | .m4, n, N, p, _, s, _, j => m4WorkSS n (N - n) j p s n s (domLgM4 NB s)
  | .m5, n, N, p, g, s, k, _ =>
    rbOverSS N p (N - n) g s + m5WorkSS p (N - n) k p s s (domLgM5 NB s) NB
  | c, n, N, p, g, s, k, j => caseWork c n N p g s k j

/-- The instance-level work is at most the work at the domain's parameters, for a degree, a
certificate size and a depth of at most `NB`. -/
theorem caseWork_le_dom {c : MainCase} {n N p g s k j : ℕ} (hN : N ≤ NB) (hk : k ≤ NB)
    (hj : j ≤ NB) : caseWork c n N p g s k j ≤ caseWorkDom NB c n N p g s k j := by
  cases c
  case m4 =>
    exact m4WorkSS_mono le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl
      (ssLgM4_le_dom s (by omega) hj)
  case m5 =>
    exact Nat.add_le_add_left (m5WorkSS_mono le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl
      (ssLgM5_le_dom s (by omega) hk) (by omega)) _
  all_goals exact le_rfl

theorem envSup_mono_box : ∀ (as : List ℕ) {f g : List ℕ → ℕ},
    (∀ xs, List.Forall₂ (· ≤ ·) xs as → f xs ≤ g xs) → envSup as f ≤ envSup as g
  | [], _, _, h => h [] .nil
  | _ :: as, _, g, h => supTo_le fun x hx =>
    (envSup_mono_box as fun ys hys => h (x :: ys) (.cons hx hys)).trans
      (le_supTo (f := fun x => envSup as fun ys => g (x :: ys)) hx)

theorem workEnv_mono_box {f g : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ}
    (h : ∀ n N p q k j, n ≤ nB → N ≤ NB → p ≤ nB → q ≤ NB * NB → k ≤ NB → j ≤ NB →
      f n N p q k j ≤ g n N p q k j) :
    workEnv f nB NB ≤ workEnv g nB NB := by
  unfold workEnv
  refine envSup_mono_box _ fun xs hxs => ?_
  match xs, hxs with
  | [_, _, _, _, _, _], .cons h0 (.cons h1 (.cons h2 (.cons h3 (.cons h4 (.cons h5 .nil))))) =>
    exact h _ _ _ _ _ _ h0 h1 h2 h3 h4 h5

/-- **The work bound at the domain's parameters**: `mainW` with `caseWorkDom`. -/
def mainWDom (t nB NB : ℕ) : ℕ :=
  workEnv (fun n N p g _ _ => mainTestCost n N p g (NB * NB) t) nB NB +
    (allCases.map fun c =>
      workEnv (fun n N p g k j => caseWorkDom NB c n N p g (NB * NB) k j) nB NB).sum

theorem mainW_le_dom (t : ℕ) : mainW t nB NB ≤ mainWDom t nB NB :=
  Nat.add_le_add_left (List.sum_le_sum fun _ _ =>
    workEnv_mono_box fun _ _ _ _ _ _ _ hN _ _ hk hj => caseWork_le_dom hN hk hj) _

theorem miniC_mono_W (A : ℕ) {W W' : ℕ} (h : W ≤ W') : ∀ r, miniC A W r ≤ miniC A W' r
  | 0 => h
  | r + 1 => Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.add_le_add_left (miniC_mono_W A h r) 1)) h

end Bounds

/-! ### The recursion -/

section Spec

variable {thr : ThrProg Ty.unit} {kf ℓf cT : ℕ → ℕ} {n₀ nB NB : ℕ}

/-- **A call without a hint on at most half the window** has a smaller rank than a hinted
parent with a base of at least two points. -/
theorem miniRk_none_lt {q p m : ℕ} (hq : 2 * q ≤ p) (hm : 2 ≤ m) :
    miniRk NB q none < p * (NB + 2) + m := by
  unfold miniRk
  simp only [Option.getD_none]
  have h1 : 2 * q * (NB + 2) ≤ p * (NB + 2) := Nat.mul_le_mul_right _ hq
  have h2 : q * 2 ≤ q * (NB + 2) := Nat.mul_le_mul_left _ (by omega)
  have e : 2 * q * (NB + 2) = q * (NB + 2) + q * (NB + 2) := by ring
  omega

/-- **The children of a step have a smaller rank** than the parent with window `p` and base
`b`: `b = 2p + 1` for the chain rule's and M0's (no hint), `b = m ≥ 1` for the others'. -/
theorem casePred_rk (h2 : 2 * nB ≤ NB) {c : MainCase} {p m b : ℕ} (hp : p ≤ nB) (hmN : m ≤ NB)
    {x : ℕ × Option ℕ} (hx : casePred c p m x) (h1 : 1 ≤ x.1)
    (hn : c = .chain ∨ c = .m0 → b = 2 * p + 1) (hh : c ≠ .chain → c ≠ .m0 → b = m ∧ 1 ≤ m) :
    miniRk NB x.1 x.2 < p * (NB + 2) + b := by
  cases c
  case chain =>
    have hx' : ChainChild p x := hx
    rw [hn (Or.inl rfl)]
    exact miniRk_lt (ChainChild.measLt hx') (hx'.getD_le.trans (by omega))
  case m0 =>
    have hx' : FreeChild p (2 * p + 1) x := hx
    rw [hn (Or.inr rfl)]
    exact miniRk_lt (FreeChild.measLt hx' (h1.trans hx'.1))
      (hx'.getD_le.trans (max_le (by omega) (by omega)))
  case m1 =>
    have hx' : FreeChild p m x := hx
    obtain ⟨rfl, -⟩ := hh (by simp) (by simp)
    exact miniRk_lt (FreeChild.measLt hx' (h1.trans hx'.1))
      (hx'.getD_le.trans (max_le (by omega) (by omega)))
  case m2a =>
    have hx' : FreeChild p m x := hx
    obtain ⟨rfl, -⟩ := hh (by simp) (by simp)
    exact miniRk_lt (FreeChild.measLt hx' (h1.trans hx'.1))
      (hx'.getD_le.trans (max_le (by omega) (by omega)))
  all_goals
    have hx' : StepChild p m x := hx
    obtain ⟨rfl, hm⟩ := hh (by simp) (by simp)
    exact miniRk_lt (StepChild.measLt hx' (h1.trans hx'.1) hm)
      (hx'.getD_le.trans (max_le (by omega) (by omega)))

/-- **The cost of a step** within the bound at its rank `R`: sub-calls of smaller rank, at most
`A` of them, and work at most `W`. -/
theorem main_cost_le {A W R : ℕ} (hR : 1 ≤ R) {ch : List (ℕ × Option ℕ)} {a b pa pb e : ℕ}
    (hch : ∀ x ∈ ch, miniRk NB x.1 x.2 < R) (ha : a ≠ 0 → miniRk NB pa none < R)
    (hb : b ≠ 0 → miniRk NB pb none < R) (hn : ch.length + a + b ≤ A) (he : e ≤ W) :
    (ch.map fun x => 1 + miniC A W (miniRk NB x.1 x.2)).sum +
        a * (1 + miniC A W (miniRk NB pa none)) + b * (1 + miniC A W (miniRk NB pb none)) + e ≤
      miniC A W R := by
  obtain ⟨r, rfl⟩ : ∃ r, R = r + 1 := ⟨R - 1, by omega⟩
  have hs := mini_sum_le (A := A) (W := W) hch
  have hta : a * (1 + miniC A W (miniRk NB pa none)) ≤ a * (1 + miniC A W r) := by
    rcases Nat.eq_zero_or_pos a with h0 | hpos
    · simp [h0]
    · exact Nat.mul_le_mul_left _ (Nat.add_le_add_left
        (miniC_mono A W (Nat.lt_succ_iff.1 (ha (by omega)))) 1)
  have htb : b * (1 + miniC A W (miniRk NB pb none)) ≤ b * (1 + miniC A W r) := by
    rcases Nat.eq_zero_or_pos b with h0 | hpos
    · simp [h0]
    · exact Nat.mul_le_mul_left _ (Nat.add_le_add_left
        (miniC_mono A W (Nat.lt_succ_iff.1 (hb (by omega)))) 1)
  have hm := Nat.mul_le_mul_right (1 + miniC A W r) hn
  have e1 : (ch.length + a + b) * (1 + miniC A W r) =
      ch.length * (1 + miniC A W r) + a * (1 + miniC A W r) + b * (1 + miniC A W r) := by ring
  change _ ≤ A * (1 + miniC A W r) + W
  omega

/-- **The induction hypothesis** below rank `r`. -/
def MainIH (thr : ThrProg Ty.unit) (t n₀ nB NB r : ℕ) : Prop :=
  ∀ J : HInstData Ty.unit, HInstValid ssDV J → MiniDom n₀ nB NB J →
    miniRk NB J.winSize J.baseOpt < r →
    ∃ ans : AnswerData Ty.unit,
      RunsWithin ssCtx (mainBody thr Ty.denote) (mainBody thr Ty.denote J) ans
        (mainCost t nB NB (miniRk NB J.winSize J.baseOpt)) ∧
      J.inst.OK ssDV ans ∧ ∀ c : CosetData Ty.unit, ans = some c → c.2.gens.length ≤ NB * NB

/-- An instance of the domain has a base of at most `NB + 1` in its measure. -/
theorem dom_base_le (h2 : 2 * nB ≤ NB) {J : HInstData Ty.unit} (hJ : HInstValid ssDV J)
    (hd : MiniDom n₀ nB NB J) : J.baseOpt.getD (2 * J.winSize + 1) ≤ NB + 1 := by
  have hw := hJ.winSize_le
  have hn := hd.n_le
  have hN := hd.degree_le
  unfold HInstData.baseOpt
  rcases J.lab with _ | L
  · simp only [Option.map_none, Option.getD_none]
    omega
  · simp only [Option.map_some, Option.getD_some]
    omega

/-- **The recursive call solves every smaller instance of the domain**, by the induction
hypothesis. -/
theorem main_sub_of_ih (h2 : 2 * nB ≤ NB) {t : ℕ} {I : HInstData Ty.unit}
    (ih : MainIH thr t n₀ nB NB (miniRk NB I.winSize I.baseOpt)) :
    MainSub thr n₀ nB NB I (fun p bo => 1 + mainCost t nB NB (miniRk NB p bo)) := by
  intro J hJ ⟨hdJ, hlt⟩
  rw [hmeasure_eq, hmeasure_eq] at hlt
  obtain ⟨ans, hrun, hok, hg⟩ := ih J hJ hdJ (miniRk_lt hlt (dom_base_le h2 hJ hdJ))
  exact ⟨ans, RunsWithin.recur hrun, hok, hg⟩

theorem caseA_eq_zero {c : MainCase} (hc : c ≠ .m5) (n N p k : ℕ) : caseA c n N p k = 0 := by
  cases c <;> simp_all [caseA]

theorem caseB_eq_zero {c : MainCase} (hc : c ≠ .m5) (p s : ℕ) : caseB c p s = 0 := by
  cases c <;> simp_all [caseB]

/-- **One step of the induction**: the procedure on `I`, from the induction hypothesis below
its rank. -/
theorem main_ind_step (hT : ThrSpec thr kf ℓf cT) (h2 : 2 * nB ≤ NB) {I : HInstData Ty.unit}
    (hI : HInstValid ssDV I) (hd : MiniDom n₀ nB NB I)
    (ih : MainIH thr (cT n₀) n₀ nB NB (miniRk NB I.winSize I.baseOpt)) :
    ∃ ans : AnswerData Ty.unit,
      RunsWithin ssCtx (mainBody thr Ty.denote) (mainBody thr Ty.denote I) ans
        (mainCost (cT n₀) nB NB (miniRk NB I.winSize I.baseOpt)) ∧
      I.inst.OK ssDV ans ∧ ∀ c : CosetData Ty.unit, ans = some c → c.2.gens.length ≤ NB * NB := by
  have hC : ∀ a b, a ≤ b → 1 + mainCost (cT n₀) nB NB (miniRk NB a none) ≤
      1 + mainCost (cT n₀) nB NB (miniRk NB b none) := fun a b hab =>
    Nat.add_le_add_left (miniC_mono _ _ (by
      unfold miniRk
      simp only [Option.getD_none]
      have := Nat.mul_le_mul_right (NB + 2) hab
      omega)) 1
  obtain ⟨ans, ch, F, a, b, hrun, hok, hg, hch, hF, ha, hb⟩ :=
    main_step hT h2 hI hd hC (main_sub_of_ih h2 ih)
  refine ⟨ans, hrun.mono ?_, hok, hg⟩
  have hW := mainWork_le (kf := kf) (ℓf := ℓf) (cT := cT) hI hd
  have hA := main_count_le hI hd hch hF ha hb
  have hR := mini_rk_pos (NB := NB) hI
  obtain ⟨⟨xy, w, σd, N, gs, d⟩, n₀', n, lab⟩ := I
  cases d
  have hwn := sh_length_le hI
  have hn : n ≤ nB := hd.n_le
  have hN : N ≤ NB := hd.degree_le
  have hl := hch.length_le
  change ch.length ≤ F * w.1.length at hl
  change F ≤ caseF (mainCase kf ℓf (((xy, w, σd, N, gs, ()), n₀', n, lab) : HInstData Ty.unit))
    n N (kf n₀') (m4J ssCtx.O n (N, gs, ())) at hF
  change a ≤ caseA (mainCase kf ℓf (((xy, w, σd, N, gs, ()), n₀', n, lab) : HInstData Ty.unit))
    n N w.1.length (kf n₀') at ha
  change b ≤ caseB (mainCase kf ℓf (((xy, w, σd, N, gs, ()), n₀', n, lab) : HInstData Ty.unit))
    w.1.length (NB * NB) at hb
  have hpred : ∀ x ∈ ch, casePred (mainCase kf ℓf
      (((xy, w, σd, N, gs, ()), n₀', n, lab) : HInstData Ty.unit)) w.1.length (N - n) x :=
    hch.pred
  have hpos : ∀ x ∈ ch, 1 ≤ x.1 := hch.pos
  have h5 : mainCase kf ℓf (((xy, w, σd, N, gs, ()), n₀', n, lab) : HInstData Ty.unit) = .m5 →
      lab.isSome ∧ m5OkD (kf n₀') (N - n) = true := mainCase_m5
  rcases lab with _ | L
  · have hcs := mainCase_none (kf := kf) (ℓf := ℓf) (xy := xy) (w := w) (σd := σd) (N := N)
      (gs := gs) (n₀ := n₀') (n := n)
    generalize mainCase kf ℓf (((xy, w, σd, N, gs, ()), n₀', n, none) : HInstData Ty.unit) = c
      at hF ha hb hpred hcs h5
    have hc5 : c ≠ .m5 := fun h => by simpa using (h5 h).1
    rw [caseA_eq_zero hc5] at ha
    rw [caseB_eq_zero hc5] at hb
    refine main_cost_le hR (fun x hx => ?_) (fun h => absurd (by omega) h)
      (fun h => absurd (by omega) h) hA hW
    rcases hcs with rfl | hcs
    · simp only [caseF] at hF
      have : ch.length ≤ 0 := by rw [Nat.le_zero.1 hF, Nat.zero_mul] at hl; exact hl
      exact absurd (List.length_pos_of_mem hx) (by omega)
    · exact casePred_rk h2 (hwn.trans hn) (by omega) (hpred x hx) (hpos x hx) (fun _ => rfl)
        (fun h1 h2 => by rcases hcs with rfl | rfl <;> simp_all)
  · obtain ⟨hcc, hc0⟩ := mainCase_some (kf := kf) (ℓf := ℓf) (xy := xy) (w := w) (σd := σd)
      (N := N) (gs := gs) (n₀ := n₀') (n := n) (L := L)
    have hm : 1 ≤ N - n := hI.base_pos rfl
    generalize mainCase kf ℓf (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit) = c
      at hF ha hb hpred hcc hc0 h5
    refine main_cost_le hR (fun x hx => ?_) (fun h => ?_) (fun h => ?_) hA hW
    · by_cases hcb : c = .base
      · subst hcb
        simp only [caseF] at hF
        have : ch.length ≤ 0 := by rw [Nat.le_zero.1 hF, Nat.zero_mul] at hl; exact hl
        exact absurd (List.length_pos_of_mem hx) (by omega)
      · exact casePred_rk h2 (hwn.trans hn) (by omega) (hpred x hx) (hpos x hx)
          (fun h => by rcases h with rfl | rfl <;> simp_all) (fun _ _ => ⟨rfl, hm⟩)
    · by_cases hc5 : c = .m5
      · have hk := m5OkD_iff.1 (h5 hc5).2
        have hq : 2 * (w.1.length / kf n₀') ≤ w.1.length :=
          (Nat.mul_le_mul_left 2 (Nat.div_le_div_left (by omega) (by omega))).trans
            (Nat.mul_div_le w.1.length 2)
        exact miniRk_none_lt (m := N - n) hq (by omega)
      · rw [caseA_eq_zero hc5] at ha
        omega
    · by_cases hc5 : c = .m5
      · have hk := m5OkD_iff.1 (h5 hc5).2
        exact miniRk_none_lt (m := N - n) (Nat.mul_div_le w.1.length 2) (by omega)
      · rw [caseB_eq_zero hc5] at hb
        omega

/-- **Correctness and cost of the full procedure** (`PLAN-14.md` §14.9, item 7). For every
threshold program with `ThrSpec`, on the domain (`2 nB ≤ NB`): the procedure returns a correct
answer with at most `NB²` generators, within `mainCost (cT n₀) nB NB` of the rank of the
instance's measure. The proof is strong induction on the rank; each step's sub-solver
hypothesis is the induction hypothesis (`main_sub_of_ih`). -/
theorem main_spec (hT : ThrSpec thr kf ℓf cT) (h2 : 2 * nB ≤ NB) (I : HInstData Ty.unit)
    (hI : HInstValid ssDV I) (hd : MiniDom n₀ nB NB I) :
    ∃ ans : AnswerData Ty.unit,
      RunsWithin ssCtx (mainBody thr Ty.denote) (mainBody thr Ty.denote I) ans
        (mainCost (cT n₀) nB NB (miniRk NB I.winSize I.baseOpt)) ∧
      I.inst.OK ssDV ans ∧ ∀ c : CosetData Ty.unit, ans = some c → c.2.gens.length ≤ NB * NB := by
  suffices h : ∀ r, MainIH thr (cT n₀) n₀ nB NB r from h _ I hI hd (Nat.lt_succ_self _)
  intro r
  induction r with
  | zero => exact fun J _ _ h => absurd h (Nat.not_lt_zero _)
  | succ r ih =>
    intro J hJ hdJ hr
    rcases Nat.lt_succ_iff_lt_or_eq.1 hr with hlt | heq
    · exact ih J hJ hdJ hlt
    · rw [← heq] at ih
      exact main_ind_step hT h2 hJ hdJ ih

/-- **The recursion at the domain's parameters**: `main_spec` with the work bound `mainWDom`. -/
theorem main_spec_dom (hT : ThrSpec thr kf ℓf cT) (h2 : 2 * nB ≤ NB) (I : HInstData Ty.unit)
    (hI : HInstValid ssDV I) (hd : MiniDom n₀ nB NB I) :
    ∃ ans : AnswerData Ty.unit,
      RunsWithin ssCtx (mainBody thr Ty.denote) (mainBody thr Ty.denote I) ans
        (miniC (mainA nB NB) (mainWDom (cT n₀) nB NB) (miniRk NB I.winSize I.baseOpt)) ∧
      I.inst.OK ssDV ans ∧ ∀ c : CosetData Ty.unit, ans = some c → c.2.gens.length ≤ NB * NB := by
  obtain ⟨ans, hrun, hok, hg⟩ := main_spec hT h2 I hI hd
  exact ⟨ans, hrun.mono (miniC_mono_W _ (mainW_le_dom _) _), hok, hg⟩

end Spec

/-! ### The headline -/

section Headline

/-- **The full procedure on every valid instance** (`PLAN-14.md` §14.9, item 8). For every
threshold program `thr` with `ThrSpec thr kf ℓf cT`, and every valid instance, with no other
hypothesis: the entry generates the group (one charged `generate`, which leaves at most `N²`
generators), and the recursion runs on the instance without a hint, with `n₀ = n = N`, in the
domain `nB = N`, `NB = 2N` (`main_spec`). The answer is correct, within
`genCost N |gs| + 2 + 15 + mainCost (cT N) N (2N)` of the rank of the measure `(|W|, 2|W| + 1)`.
-/
theorem mainSolve_ss {thr : ThrProg Ty.unit} {kf ℓf cT : ℕ → ℕ} (hT : ThrSpec thr kf ℓf cT)
    {xy : StrData × StrData} {w : WinData} {σd : PermData} {N : ℕ} {gs : GensData}
    (hw : w.Valid N) (hσ : σd.Valid N) (hgs : GensData.AllValid N gs)
    (hinv : IsInvariant (GensData.denote N gs) (w.denote N)) :
    ∃ ans : AnswerData Ty.unit,
      RunsWithin ssCtx (mainBody thr Ty.denote)
        (mainEntry Ty.unit Ty.denote (xy, w, σd, N, gs)) ans
        (genCost N gs.length + 2 + 15 +
          mainCost (cT N) N (2 * N) (miniRk (2 * N) w.1.length none)) ∧
      AnsOK ssDV N (w.denote N) (σd.denote N) (gs.denote N) (xy.1.denote N) (xy.2.denote N)
        ans := by
  obtain ⟨hgv, hden, hlen⟩ := generateModel_spec hgs
  have hI : HInstValid ssDV
      (((xy, w, σd, N, generateModel N gs, ()), N, N, none) : HInstData Ty.unit) := by
    refine ⟨⟨hw, hσ, ⟨hgv, trivial⟩, ?_⟩, le_rfl, ?_, fun i hi => hw.lt i hi, ?_, ?_⟩
    · change IsInvariant (GensData.denote N (generateModel N gs)) (w.denote N)
      rw [hden]
      exact hinv
    · intro g _ u hu
      have hu' : u.val < N := u.2
      exact absurd (show N ≤ u.val from hu) (by omega)
    · intro g _ hg
      exact Equiv.ext fun j => hg j j.2
    · intro L hL
      cases hL
  have hd : MiniDom N N (2 * N)
      (((xy, w, σd, N, generateModel N gs, ()), N, N, none) : HInstData Ty.unit) :=
    ⟨rfl, le_rfl, by change N ≤ 2 * N; omega,
      hlen.trans (Nat.mul_le_mul (by omega) (by omega))⟩
  obtain ⟨ans, hrun, hok, -⟩ := main_spec hT le_rfl _ hI hd
  replace hrun : RunsWithin ssCtx (mainBody thr Ty.denote)
      (mainBody thr Ty.denote
        (((xy, w, σd, N, generateModel N gs, ()), N, N, none) : HInstData Ty.unit)) ans
      (mainCost (cT N) N (2 * N) (miniRk (2 * N) w.1.length none)) := hrun
  have hG : ssCtx.O.run GroupOp.generate (N, gs) = (N, generateModel N gs, ()) := rfl
  refine ⟨ans, ?_, ?_⟩
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.call (X := ssCtx) (op := GroupOp.generate) (x := (N, gs)) hgs)
      rw [hG]
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      exact RunsWithin.recur hrun
    case hc =>
      have hc : ssCtx.B.call GroupOp.generate (N, gs) (ssCtx.O.run GroupOp.generate (N, gs)) =
          genCost N gs.length + 2 := rfl
      simp only [Prim.cost]
      rw [hc]
      omega
  · change InstData.OK (D := Ty.unit) (xy, w, σd, N, generateModel N gs, ()) ssDV ans at hok
    unfold InstData.OK at hok
    change AnsOK ssDV N (w.denote N) (σd.denote N) (GensData.denote N (generateModel N gs))
      (xy.1.denote N) (xy.2.denote N) ans at hok
    rw [hden] at hok
    exact hok

/-- **The full procedure at constant thresholds**, with no hypothesis: `thrConst k ℓ` meets
`ThrSpec` at cost `3` (`thrConst_spec`). -/
theorem mainSolve_ss_const (k ℓ : ℕ) {xy : StrData × StrData} {w : WinData} {σd : PermData}
    {N : ℕ} {gs : GensData} (hw : w.Valid N) (hσ : σd.Valid N) (hgs : GensData.AllValid N gs)
    (hinv : IsInvariant (GensData.denote N gs) (w.denote N)) :
    ∃ ans : AnswerData Ty.unit,
      RunsWithin ssCtx (mainBody (thrConst k ℓ) Ty.denote)
        (mainEntry Ty.unit Ty.denote (xy, w, σd, N, gs)) ans
        (genCost N gs.length + 2 + 15 + mainCost 3 N (2 * N) (miniRk (2 * N) w.1.length none)) ∧
      AnsOK ssDV N (w.denote N) (σd.denote N) (gs.denote N) (xy.1.denote N) (xy.2.denote N)
        ans :=
  mainSolve_ss (thrConst_spec k ℓ) hw hσ hgs hinv

/-- **The headline at the domain's parameters**: `mainSolve_ss` with the work bound `mainWDom`
(§14.9 item 4: M4's `Lg = domLgM4 NB NB²`, M5's `Lg = domLgM5 NB NB²` and `uB = NB`, with
`NB = 2N`). -/
theorem mainSolve_ss_dom {thr : ThrProg Ty.unit} {kf ℓf cT : ℕ → ℕ} (hT : ThrSpec thr kf ℓf cT)
    {xy : StrData × StrData} {w : WinData} {σd : PermData} {N : ℕ} {gs : GensData}
    (hw : w.Valid N) (hσ : σd.Valid N) (hgs : GensData.AllValid N gs)
    (hinv : IsInvariant (GensData.denote N gs) (w.denote N)) :
    ∃ ans : AnswerData Ty.unit,
      RunsWithin ssCtx (mainBody thr Ty.denote)
        (mainEntry Ty.unit Ty.denote (xy, w, σd, N, gs)) ans
        (genCost N gs.length + 2 + 15 +
          miniC (mainA N (2 * N)) (mainWDom (cT N) N (2 * N)) (miniRk (2 * N) w.1.length none)) ∧
      AnsOK ssDV N (w.denote N) (σd.denote N) (gs.denote N) (xy.1.denote N) (xy.2.denote N)
        ans := by
  obtain ⟨ans, hrun, hok⟩ := mainSolve_ss hT hw hσ hgs hinv (xy := xy)
  exact ⟨ans, hrun.mono (Nat.add_le_add_left (miniC_mono_W _ (mainW_le_dom _) _) _), hok⟩

end Headline

end GraphIso.Main
