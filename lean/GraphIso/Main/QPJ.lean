module

public import GraphIso.Main.GraphQP

/-!
# Milestone 14's bounds for transitivity thresholds of polynomial growth

Stage 16b (`PLAN-16.md` §5). Milestone 14 assumes `QPHyp K T C C'`, whose bound
`T m ≤ C' (λ(m) + 1)` enters the analysis only through two consequences:

* `TBelow T (ℓT C')` (`tBelow_qp`), for the threshold program `thrQP C C'`;
* `supTo T m ≤ jMaxQ C' n₀` for `m ≤ 2 n₀` (`supTo_le_jMaxQ`), the depth bound of M4 and of
  Case 2b in the corner values `qpM4`, `qpM5`, `qpFac` of `Q(n₀) = QQP C C' n₀`; and `jMaxQ C'`
  is used there only through its growth class `PLB λ 5` (`jMaxQ_plb`).

**`QPHypJ K T C C' j`** keeps the interfaces and the growth of `K`, and replaces
`T m ≤ C' (λ(m) + 1)` by exactly these consequences, with any depth bound `j`. Everything below
is milestone 14's proofs with `jMaxQ C'` replaced by `j` (`QQPJ C C' j`, with
`QQP C C' = QQPJ C C' (jMaxQ C')` by definition, `QQP_eq_QQPJ`):

* the corner bounds (`caseWorkS_le_qpCasesJ`, `mainWorkS_le_QQPJ`, `caseFAB_le_QQPJ`,
  `winSize_add_two_le_QQPJ`), the potential (`pot_ind_stepJ`, `main_potJ`) and the headlines
  (`mainSolve_qpJ`, `mainSolve_qp_closedJ`);
* for `j ∈ PLB λ 5`, the closed bound `QQPJ_le_exp` and **`mainSolve_qp_expJ`**,
  **`giSolve_qp_expJ`**, **`gi_qp_simpleGraphJ`**: milestone 14's headlines with `QPHypJ` in
  place of `QPHyp`, at the same programs `thrQP C C'` and `qpSolver C C'` and with the same
  cost `2^{c (λ + 1)⁸}`.

`QPHyp K T C C'` gives `QPHypJ K T C C' (jMaxQ C')` (`QPHyp.toJ`).
-/

@[expose] public section

namespace GraphIso.Main

open Equiv Cost GraphIso GraphIso.Programs GraphIso.Toolkit GraphIso.Recursion GraphIso.Certificates
  Sims

/-! ### The hypothesis -/

/-- **The interfaces with a general transitivity threshold**: `AltQuotientIso K` for a monotone
`K ≤ C (λ + 1)⁵`, and `TransitivityBound T` with `TBelow T (ℓT C')` and `supTo T m ≤ j n₀` for
`m ≤ 2 n₀`. -/
structure QPHypJ (K T : ℕ → ℕ) (C C' : ℕ) (j : ℕ → ℕ) : Prop where
  iso : AltQuot.AltQuotientIso K
  mono : Monotone K
  le : ∀ n, K n ≤ C * (lam n + 1) ^ 5
  trans : AltQuot.TransitivityBound T
  below : TBelow T (ℓT C')
  sup : ∀ n₀ m, m ≤ 2 * n₀ → supTo T m ≤ j n₀

/-- `QPHyp` gives `QPHypJ` at `j = jMaxQ C'`. -/
theorem QPHyp.toJ {K T : ℕ → ℕ} {C C' : ℕ} (h : QPHyp K T C C') : QPHypJ K T C C' (jMaxQ C') :=
  ⟨h.iso, h.mono, h.le, h.trans, tBelow_qp h.tle, fun _ _ hm => supTo_le_jMaxQ h.tle hm⟩

/-- **`Thresholds` at `k(n₀)`**: `K n₀ ≤ C (λ(n₀) + 1)⁵ ≤ C L⁵ ≤ k`, and
`n₀ < 2^{λ(n₀) + 1} ≤ 2^{k - 1} ≤ k!/2`. -/
theorem thresholds_qpJ {K T : ℕ → ℕ} {C C' : ℕ} {j : ℕ → ℕ} (h : QPHypJ K T C C' j)
    (n₀ : ℕ) :
    Thresholds K n₀ (kQP C n₀) := by
  have hL := lam_add_one_le_qpL n₀
  refine ⟨h.iso, h.mono, five_le_kQP C n₀, ?_, ?_⟩
  · have h5 : C * (lam n₀ + 1) ^ 5 ≤ C * qpL n₀ ^ 5 :=
      Nat.mul_le_mul_left C (Nat.pow_le_pow_left hL 5)
    have := h.le n₀
    rw [kQP_eq]
    omega
  · have hk := five_le_kQP C n₀
    have hlt : n₀ < 2 ^ (lam n₀ + 1) := Nat.lt_pow_succ_log_self (by norm_num) n₀
    have hle : 2 ^ (lam n₀ + 1) ≤ 2 ^ (kQP C n₀ - 1) :=
      Nat.pow_le_pow_right (by norm_num) (by unfold kQP at hk ⊢; omega)
    have hf := two_pow_le_factorial (by omega : 4 ≤ kQP C n₀)
    have e : 2 ^ kQP C n₀ = 2 ^ (kQP C n₀ - 1) * 2 := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega)]
    have : 2 ^ (kQP C n₀ - 1) ≤ (kQP C n₀).factorial / 2 :=
      (Nat.le_div_iff_mul_le (by norm_num)).2 (e ▸ hf)
    omega

/-- **The numeric hypotheses hold at the thresholds**, under `QPHypJ`. -/
theorem sharpHyp_qpJ {K T : ℕ → ℕ} {C C' : ℕ} {j : ℕ → ℕ} (h : QPHypJ K T C C' j) (n₀ : ℕ) :
    SharpHyp K T n₀ (kQP C n₀) (ℓQP C C' n₀) :=
  ⟨thresholds_qpJ h n₀, h.trans, four_mul_kQP_le C C' n₀, h.below.mono (ℓT_le_ℓQP C C' n₀)⟩

/-! ### The corners -/

/-- M4's work at the corner, maximized over the depth. -/
def qpM4J (j : ℕ → ℕ) (n₀ : ℕ) : ℕ :=
  supTo (fun i => m4PtNsL n₀ (2 * n₀) i n₀ (sGQ n₀) n₀ (sGQ n₀)
    (ssLgM4Ns (2 * n₀ + j n₀) (j n₀) (uMaxQ n₀) (sGQ n₀)) (uMaxQ n₀)) (j n₀)

/-- M5's work at the corner: the restriction and `m5WorkUB`. -/
def qpM5J (C : ℕ) (j : ℕ → ℕ) (n₀ : ℕ) : ℕ :=
  rbOverSS (2 * n₀) n₀ (2 * n₀) (sGQ n₀) (sGQ n₀) +
    m5WorkUB n₀ (2 * n₀) (kQP C n₀) n₀ (sGQ n₀) (sGQ n₀)
      (ssLgM5Ns (2 * n₀) (kQP C n₀) (uMaxQ n₀) (j n₀) (sGQ n₀)) (uMaxQ n₀) (j n₀)

/-- Every case's work at the corner of its sizes. -/
def qpCasesJ (C C' : ℕ) (j : ℕ → ℕ) (n₀ : ℕ) : ℕ :=
  fixedStepCost n₀ + chainCost (2 * n₀) n₀ n₀ + m0WorkSS n₀ (2 * n₀) n₀ (sGQ n₀) (sGQ n₀) +
    m1WorkSS n₀ (2 * n₀) n₀ (sGQ n₀) (sGQ n₀) + m2aWorkSS n₀ (2 * n₀) n₀ (sGQ n₀) (sGQ n₀) n₀ +
    m2bWorkSS n₀ (2 * n₀) n₀ (sGQ n₀) n₀ (sGQ n₀) +
    m3WorkSS (2 * n₀ - mLQ C C' n₀) (2 * n₀) n₀ (sGQ n₀) (sGQ n₀) + qpM4J j n₀ + qpM5J C j n₀

/-- **The work at the corners**: the tests and every case. -/
def qpWorkJ (C C' : ℕ) (j : ℕ → ℕ) (n₀ : ℕ) : ℕ := qpTest C n₀ + qpCasesJ C C' j n₀

/-- **The factors and counted calls at the corners.** -/
def qpFacJ (C C' : ℕ) (j : ℕ → ℕ) (n₀ : ℕ) : ℕ :=
  2 * n₀ + (mLQ C C' n₀).factorial +
    m4R (2 * n₀ + j n₀) (j n₀) * max (2 * n₀) (uMaxQ n₀).factorial +
    m5FBns (2 * n₀) (kQP C n₀) (uMaxQ n₀) (j n₀) +
    (2 * certCount (n₀ + 2 * n₀) n₀ (kQP C n₀) + 2 * c3Count (2 * n₀) (kQP C n₀) n₀) +
    (sGQ n₀ + 1) * n₀ + 1

/-- **`Q(n₀)`**: `n₀ + 2`, the work and the factors at the corners. -/
def QQPJ (C C' : ℕ) (j : ℕ → ℕ) (n₀ : ℕ) : ℕ := n₀ + 2 + qpWorkJ C C' j n₀ + qpFacJ C C' j n₀

/-- `Q(n₀)` is `QQPJ` at `j = jMaxQ C'`. -/
theorem QQP_eq_QQPJ (C C' n₀ : ℕ) : QQP C C' n₀ = QQPJ C C' (jMaxQ C') n₀ := rfl

/-! ### The bounds -/

section Bounds

variable {K T : ℕ → ℕ} {C C' n₀ : ℕ} {j : ℕ → ℕ}

/-- **Every case's work is at most its corner value** on the domain with `LabInv`. -/
theorem caseWorkS_le_qpCasesJ (hQ : QPHypJ K T C C' j) {xy : StrData × StrData} {w : WinData}
    {σd : PermData} {N : ℕ} {gs : GensData} {n : ℕ} {lab : Option LabelData}
    (hI : HInstValid ssDV (((xy, w, σd, N, gs, ()), n₀, n, lab) : HInstData Ty.unit))
    (hd : MiniDom n₀ n₀ (2 * n₀) (((xy, w, σd, N, gs, ()), n₀, n, lab) : HInstData Ty.unit))
    (hIL : LabInv (((xy, w, σd, N, gs, ()), n₀, n, lab) : HInstData Ty.unit)) :
    caseWorkS (mainCase (kQP C) (ℓQP C C') (((xy, w, σd, N, gs, ()), n₀, n, lab) :
        HInstData Ty.unit)) n N w.1.length gs.length (sGQ n₀) (kQP C n₀)
        (m4J ssCtx.O n (N, gs, ()))
        (labT (((xy, w, σd, N, gs, ()), n₀, n, lab) : HInstData Ty.unit)) (supTo T (N - n)) ≤
      qpCasesJ C C' j n₀ := by
  have hwn := sh_length_le hI
  have hn : n ≤ n₀ := hd.n_le
  have hN : N ≤ 2 * n₀ := hd.degree_le
  have hg : gs.length ≤ sGQ n₀ := hd.gens_le
  have hnN : n ≤ N := hI.le
  have hS := sharpHyp_qpJ hQ n₀
  generalize hc : mainCase (kQP C) (ℓQP C C')
    (((xy, w, σd, N, gs, ()), n₀, n, lab) : HInstData Ty.unit) = c
  unfold qpCasesJ
  cases c
  case base =>
    have : fixedStepCost w.1.length ≤ fixedStepCost n₀ := by
      exact CostMono.Main_fixedStepCost (by omega)
    simp only [caseWorkS, caseWork]
    omega
  case chain =>
    have : chainCost N w.1.length w.1.length ≤ chainCost (2 * n₀) n₀ n₀ := by
      apply CostMono.Main_chainCost <;> omega
    simp only [caseWorkS, caseWork]
    omega
  case m0 =>
    have : m0WorkSS n N w.1.length gs.length (sGQ n₀) ≤
        m0WorkSS n₀ (2 * n₀) n₀ (sGQ n₀) (sGQ n₀) := by
      apply CostMono.Main_m0WorkSS <;> omega
    simp only [caseWorkS, caseWork]
    omega
  case m1 =>
    have : m1WorkSS n (N - n) w.1.length gs.length (sGQ n₀) ≤
        m1WorkSS n₀ (2 * n₀) n₀ (sGQ n₀) (sGQ n₀) := by
      apply CostMono.Main_m1WorkSS <;> omega
    simp only [caseWorkS, caseWork]
    omega
  case m2a =>
    have : m2aWorkSS n (N - n) w.1.length gs.length (sGQ n₀) n ≤
        m2aWorkSS n₀ (2 * n₀) n₀ (sGQ n₀) (sGQ n₀) n₀ := by
      apply CostMono.Main_m2aWorkSS <;> omega
    simp only [caseWorkS, caseWork]
    omega
  case m2b =>
    have : m2bWorkSS n (N - n) w.1.length gs.length n (sGQ n₀) ≤
        m2bWorkSS n₀ (2 * n₀) n₀ (sGQ n₀) n₀ (sGQ n₀) := by
      apply CostMono.Main_m2bWorkSS <;> omega
    simp only [caseWorkS, caseWork]
    omega
  case m3 =>
    have hℓ := mainCase_m3_le hS hI hc
    have hmL : N - n ≤ mLQ C C' n₀ := le_min hℓ (by omega)
    have hmL' : mLQ C C' n₀ ≤ 2 * n₀ := min_le_right _ _
    have : m3WorkSS n N w.1.length gs.length (sGQ n₀) ≤
        m3WorkSS (2 * n₀ - mLQ C C' n₀) (2 * n₀) n₀ (sGQ n₀) (sGQ n₀) := by
      apply CostMono.Main_m3WorkSS <;> omega
    simp only [caseWorkS, caseWork]
    omega
  case m4 =>
    obtain ⟨-, L, rfl, -, -, hbig⟩ := mainCase_big hc (Or.inl rfl)
    obtain ⟨hℓ, hgi, -⟩ := bigCase_eq_m4 hbig
    have hgs : GensData.AllValid N gs := hI.valid.group.1
    have hb : IsInvariant (GensData.denote N gs) (baseSet n N) := hI.base_inv
    have hj := (ss_m4J_le_T hQ.trans hgs hb hnN hgi).trans
      (hQ.sup n₀ _ (by omega))
    have hu : labLen L * lam (N - n) ≤ uMaxQ n₀ :=
      labLen_mul_lam_le (hIL.hint L rfl) ((ell0_le_ℓQP C C' n₀).trans_lt hℓ)
    have hLg : ssLgM4Ns (N - n) (m4J ssCtx.O n (N, gs, ())) (labLen L * lam (N - n)) (sGQ n₀) ≤
        ssLgM4Ns (2 * n₀ + j n₀) (j n₀) (uMaxQ n₀) (sGQ n₀) := by
      apply CostMono.Main_ssLgM4Ns <;> omega
    have h4 : caseWorkS .m4 n N w.1.length gs.length (sGQ n₀) (kQP C n₀)
        (m4J ssCtx.O n (N, gs, ())) (labLen L) (supTo T (N - n)) ≤ qpM4J j n₀ := by
      unfold qpM4J
      refine (caseWorkS_m4_le (by omega)).trans (supTo_le fun j' hj' => ?_)
      refine le_trans (m4PtNsL_mono (n' := n₀) (m' := 2 * n₀) (p' := n₀) (s' := sGQ n₀)
        (Ls' := n₀) (sIn' := sGQ n₀) hn (by omega) (by omega) le_rfl hn le_rfl hLg hu
        (by omega)) ?_
      exact le_supTo (f := fun i => m4PtNsL n₀ (2 * n₀) i n₀ (sGQ n₀) n₀ (sGQ n₀)
        (ssLgM4Ns (2 * n₀ + j n₀) (j n₀) (uMaxQ n₀) (sGQ n₀)) (uMaxQ n₀))
        (hj'.trans hj)
    change caseWorkS .m4 n N w.1.length gs.length (sGQ n₀) (kQP C n₀)
      (m4J ssCtx.O n (N, gs, ())) (labLen L) (supTo T (N - n)) ≤ _
    omega
  case m5 =>
    obtain ⟨-, L, rfl, -, -, hbig⟩ := mainCase_big hc (Or.inr rfl)
    obtain ⟨hℓ, -, hok⟩ := bigCase_eq_m5 hbig
    obtain ⟨hk5, hkm, -⟩ := m5OkD_iff.1 hok
    have hjB := hS.below (N - n) hℓ
    have hjM := hQ.sup n₀ _ (show N - n ≤ 2 * n₀ by omega)
    have hu : labLen L * lam (N - n) ≤ uMaxQ n₀ :=
      labLen_mul_lam_le (hIL.hint L rfl) ((ell0_le_ℓQP C C' n₀).trans_lt hℓ)
    have hLg : ssLgM5Ns (N - n) (kQP C n₀) (labLen L * lam (N - n)) (supTo T (N - n))
        (sGQ n₀) ≤ ssLgM5Ns (2 * n₀) (kQP C n₀) (uMaxQ n₀) (j n₀) (sGQ n₀) := by
      apply CostMono.Main_ssLgM5Ns <;> omega
    have hr : rbOverSS N w.1.length (N - n) gs.length (sGQ n₀) ≤
        rbOverSS (2 * n₀) n₀ (2 * n₀) (sGQ n₀) (sGQ n₀) := by
      apply CostMono.Main_rbOverSS <;> omega
    have h5 : caseWorkS .m5 n N w.1.length gs.length (sGQ n₀) (kQP C n₀)
        (m4J ssCtx.O n (N, gs, ())) (labLen L) (supTo T (N - n)) ≤ qpM5J C j n₀ :=
      (caseWorkS_m5_le (by omega) hkm (by omega)).trans (Nat.add_le_add hr
        (m5WorkUB_mono (by omega) (by omega) le_rfl (by omega) le_rfl le_rfl hLg hu hjM
          (by omega) (by omega) (by omega)))
    change caseWorkS .m5 n N w.1.length gs.length (sGQ n₀) (kQP C n₀)
      (m4J ssCtx.O n (N, gs, ())) (labLen L) (supTo T (N - n)) ≤ _
    omega

/-- **The step's work is at most `Q`** on the domain with `LabInv`. -/
theorem mainWorkS_le_QQPJ (hQ : QPHypJ K T C C' j) {I : HInstData Ty.unit} (hI : HInstValid ssDV I)
    (hd : MiniDom n₀ n₀ (2 * n₀) I) (hIL : LabInv I) :
    mainWorkS (kQP C) (ℓQP C C') (cTQP C) T (2 * n₀ * (2 * n₀)) I ≤ QQPJ C C' j n₀ := by
  obtain ⟨⟨xy, w, σd, N, gs, d⟩, n₀', n, lab⟩ := I
  cases d
  obtain rfl : n₀' = n₀ := hd.n₀
  have hwn := sh_length_le hI
  have hn : n ≤ n₀' := hd.n_le
  have hN : N ≤ 2 * n₀' := hd.degree_le
  have hg : gs.length ≤ sGQ n₀' := hd.gens_le
  have ht : mainTestCost n N w.1.length gs.length (sGQ n₀') (cTQP C n₀') ≤ qpTest C n₀' := by
    apply CostMono.Main_mainTestCost <;> omega
  have hc := caseWorkS_le_qpCasesJ hQ hI hd hIL
  change mainTestCost n N w.1.length gs.length (sGQ n₀') (cTQP C n₀') +
    caseWorkS (mainCase (kQP C) (ℓQP C C') (((xy, w, σd, N, gs, ()), n₀', n, lab) :
        HInstData Ty.unit)) n N w.1.length gs.length (sGQ n₀') (kQP C n₀')
        (m4J ssCtx.O n (N, gs, ()))
        (labT (((xy, w, σd, N, gs, ()), n₀', n, lab) : HInstData Ty.unit)) (supTo T (N - n)) ≤ _
  unfold QQPJ qpWorkJ
  omega

/-- **The factor plus the counted calls is at most `Q`** on the domain with `LabInv`. -/
theorem caseFAB_le_QQPJ (hQ : QPHypJ K T C C' j) {I : HInstData Ty.unit} (hI : HInstValid ssDV I)
    (hd : MiniDom n₀ n₀ (2 * n₀) I) (hIL : LabInv I) :
    caseFS (mainCase (kQP C) (ℓQP C C') I) I.n I.inst.degree (kQP C I.n₀)
        (m4J ssCtx.O I.n (I.inst.degree, I.inst.2.2.2.gens, ())) (labT I)
        (supTo T (I.inst.degree - I.n)) +
      caseA (mainCase (kQP C) (ℓQP C C') I) I.n I.inst.degree I.winSize (kQP C I.n₀) +
      caseB (mainCase (kQP C) (ℓQP C C') I) I.winSize (2 * n₀ * (2 * n₀)) ≤ QQPJ C C' j n₀ := by
  obtain ⟨⟨xy, w, σd, N, gs, d⟩, n₀', n, lab⟩ := I
  cases d
  obtain rfl : n₀' = n₀ := hd.n₀
  have hwn := sh_length_le hI
  have hn : n ≤ n₀' := hd.n_le
  have hN : N ≤ 2 * n₀' := hd.degree_le
  have hnN : n ≤ N := hI.le
  have hS := sharpHyp_qpJ hQ n₀'
  change caseFS (mainCase (kQP C) (ℓQP C C') (((xy, w, σd, N, gs, ()), n₀', n, lab) :
        HInstData Ty.unit)) n N (kQP C n₀') (m4J ssCtx.O n (N, gs, ()))
        (labT (((xy, w, σd, N, gs, ()), n₀', n, lab) : HInstData Ty.unit)) (supTo T (N - n)) +
      caseA (mainCase (kQP C) (ℓQP C C') (((xy, w, σd, N, gs, ()), n₀', n, lab) :
        HInstData Ty.unit)) n N w.1.length (kQP C n₀') +
      caseB (mainCase (kQP C) (ℓQP C C') (((xy, w, σd, N, gs, ()), n₀', n, lab) :
        HInstData Ty.unit)) w.1.length (sGQ n₀') ≤ _
  generalize hc : mainCase (kQP C) (ℓQP C C')
    (((xy, w, σd, N, gs, ()), n₀', n, lab) : HInstData Ty.unit) = c
  unfold QQPJ qpFacJ
  cases c
  case m3 =>
    have hℓ := mainCase_m3_le hS hI hc
    have : (N - n).factorial ≤ (mLQ C C' n₀').factorial :=
      Nat.factorial_le (le_min hℓ (by omega))
    simp only [caseFS, caseF, caseA, caseB]
    omega
  case m4 =>
    obtain ⟨-, L, rfl, -, -, hbig⟩ := mainCase_big hc (Or.inl rfl)
    obtain ⟨hℓ, hgi, -⟩ := bigCase_eq_m4 hbig
    have hgs : GensData.AllValid N gs := hI.valid.group.1
    have hb : IsInvariant (GensData.denote N gs) (baseSet n N) := hI.base_inv
    have hj := (ss_m4J_le_T hQ.trans hgs hb hnN hgi).trans
      (hQ.sup n₀' _ (by omega))
    have hu : labLen L * lam (N - n) ≤ uMaxQ n₀' :=
      labLen_mul_lam_le (hIL.hint L rfl) ((ell0_le_ℓQP C C' n₀').trans_lt hℓ)
    have hR : m4R (N - n) (m4J ssCtx.O n (N, gs, ())) ≤
        m4R (2 * n₀' + j n₀') (j n₀') := by
      apply CostMono.Main_m4R <;> omega
    have : m4R (N - n) (m4J ssCtx.O n (N, gs, ())) *
          max (N - n) (labLen L * lam (N - n)).factorial ≤
        m4R (2 * n₀' + j n₀') (j n₀') * max (2 * n₀') (uMaxQ n₀').factorial :=
      Nat.mul_le_mul hR (max_le_max (by omega) (Nat.factorial_le hu))
    rw [show labT (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit) = labLen L
      from rfl]
    simp only [caseFS, caseA, caseB]
    omega
  case m5 =>
    obtain ⟨-, L, rfl, -, -, hbig⟩ := mainCase_big hc (Or.inr rfl)
    obtain ⟨hℓ, -, hok⟩ := bigCase_eq_m5 hbig
    obtain ⟨-, hkm, -⟩ := m5OkD_iff.1 hok
    have hjM := hQ.sup n₀' _ (show N - n ≤ 2 * n₀' by omega)
    have hu : labLen L * lam (N - n) ≤ uMaxQ n₀' :=
      labLen_mul_lam_le (hIL.hint L rfl) ((ell0_le_ℓQP C C' n₀').trans_lt hℓ)
    have hF : m5FBns (N - n) (kQP C n₀') (labLen L * lam (N - n)) (supTo T (N - n)) ≤
        m5FBns (2 * n₀') (kQP C n₀') (uMaxQ n₀') (j n₀') := by
      apply CostMono.Main_m5FBns <;> omega
    have hcert : certCount (w.1.length + (N - n)) w.1.length (kQP C n₀') ≤
        certCount (n₀' + 2 * n₀') n₀' (kQP C n₀') := by
      refine CostMono.Main_certCount (by omega) le_rfl ?_
      rw [Nat.add_sub_cancel_left, Nat.add_sub_cancel_left]
      exact Nat.choose_le_choose _ (by omega)
    have hc3 : c3Count (N - n) (kQP C n₀') w.1.length ≤ c3Count (2 * n₀') (kQP C n₀') n₀' := by
      apply CostMono.Main_c3Count <;> omega
    have hB : (sGQ n₀' + 1) * w.1.length ≤ (sGQ n₀' + 1) * n₀' := Nat.mul_le_mul_left _ (by omega)
    rw [show labT (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit) = labLen L
      from rfl]
    simp only [caseFS, caseA, caseB]
    omega
  all_goals simp only [caseFS, caseF, caseA, caseB]; omega

/-- **The window is below `Q`**: `|W| + 2 ≤ n₀ + 2 ≤ Q`. -/
theorem winSize_add_two_le_QQPJ {I : HInstData Ty.unit} (hI : HInstValid ssDV I)
    (hd : MiniDom n₀ n₀ (2 * n₀) I) : I.winSize + 2 ≤ QQPJ C C' j n₀ := by
  have := hI.winSize_le
  have := hd.n_le
  unfold QQPJ
  omega

end Bounds

/-! ### The induction -/

section Induction

variable {K T : ℕ → ℕ} {C C' n₀ : ℕ} {j : ℕ → ℕ}

/-- **One step of the induction**: the procedure on `I` within the potential, from the induction
hypothesis below its rank. -/
theorem pot_ind_stepJ (hQ : QPHypJ K T C C' j) {I : HInstData Ty.unit} (hI : HInstValid ssDV I)
    (hd : MiniDom n₀ n₀ (2 * n₀) I) (hIL : LabInv I)
    (ih : PotIH (thrQP C C') (QQPJ C C' j n₀) n₀ (miniRk (2 * n₀) I.winSize I.baseOpt)) :
    ∃ ans : AnswerData Ty.unit,
      RunsWithin ssCtx (mainBody (thrQP C C') Ty.denote) (mainBody (thrQP C C') Ty.denote I) ans
        (potO (QQPJ C C' j n₀) 2 I.winSize I.baseOpt + QQPJ C C' j n₀) ∧
      I.inst.OK ssDV ans ∧
        ∀ c : CosetData Ty.unit, ans = some c → c.2.gens.length ≤ 2 * n₀ * (2 * n₀) := by
  have hQ1 : 1 ≤ QQPJ C C' j n₀ := by unfold QQPJ; omega
  have hC : ∀ a b, a ≤ b → 1 + (potO (QQPJ C C' j n₀) 2 a none + QQPJ C C' j n₀) ≤
      1 + (potO (QQPJ C C' j n₀) 2 b none + QQPJ C C' j n₀) := fun a b hab => by
    have := potO_none_mono (b := 2) hQ1 hab
    omega
  obtain ⟨-, ans, ch, F, a, b, hrun, hok, hg, hch, hF, ha, hb⟩ :=
    main_step_sharp (thrQP_spec C C') le_rfl hI hd hIL hC (pot_sub_of_ih ih) (sharpHyp_qpJ hQ n₀)
  refine ⟨ans, hrun.mono ?_, hok, hg⟩
  have hW := mainWorkS_le_QQPJ hQ hI hd hIL
  have hFab := caseFAB_le_QQPJ hQ hI hd hIL
  have hwQ := winSize_add_two_le_QQPJ (C := C) (C' := C') (j := j) hI hd
  obtain ⟨⟨xy, w, σd, N, gs, d⟩, n₀', n, lab⟩ := I
  cases d
  obtain rfl : n₀' = n₀ := hd.n₀
  have hk : 2 ≤ kQP C n₀' := by have := five_le_kQP C n₀'; omega
  change (ch.map fun x => 1 + (potO (QQPJ C C' j n₀') 2 x.1 x.2 + QQPJ C C' j n₀')).sum +
      a * (1 + (potO (QQPJ C C' j n₀') 2 (w.1.length / kQP C n₀') none + QQPJ C C' j n₀')) +
      b * (1 + (potO (QQPJ C C' j n₀') 2 (w.1.length / 2) none + QQPJ C C' j n₀')) +
      mainWorkS (kQP C) (ℓQP C C') (cTQP C) T (2 * n₀' * (2 * n₀'))
        (((xy, w, σd, N, gs, ()), n₀', n, lab) : HInstData Ty.unit) ≤
    potO (QQPJ C C' j n₀') 2 w.1.length (lab.map fun _ => N - n) + QQPJ C C' j n₀'
  change F ≤ caseFS (mainCase (kQP C) (ℓQP C C') (((xy, w, σd, N, gs, ()), n₀', n, lab) :
      HInstData Ty.unit)) n N (kQP C n₀') (m4J ssCtx.O n (N, gs, ()))
      (labT (((xy, w, σd, N, gs, ()), n₀', n, lab) : HInstData Ty.unit)) (supTo T (N - n)) at hF
  change a ≤ caseA (mainCase (kQP C) (ℓQP C C') (((xy, w, σd, N, gs, ()), n₀', n, lab) :
      HInstData Ty.unit)) n N w.1.length (kQP C n₀') at ha
  change b ≤ caseB (mainCase (kQP C) (ℓQP C C') (((xy, w, σd, N, gs, ()), n₀', n, lab) :
      HInstData Ty.unit)) w.1.length (2 * n₀' * (2 * n₀')) at hb
  change caseFS (mainCase (kQP C) (ℓQP C C') (((xy, w, σd, N, gs, ()), n₀', n, lab) :
        HInstData Ty.unit)) n N (kQP C n₀') (m4J ssCtx.O n (N, gs, ()))
        (labT (((xy, w, σd, N, gs, ()), n₀', n, lab) : HInstData Ty.unit)) (supTo T (N - n)) +
      caseA (mainCase (kQP C) (ℓQP C C') (((xy, w, σd, N, gs, ()), n₀', n, lab) :
        HInstData Ty.unit)) n N w.1.length (kQP C n₀') +
      caseB (mainCase (kQP C) (ℓQP C C') (((xy, w, σd, N, gs, ()), n₀', n, lab) :
        HInstData Ty.unit)) w.1.length (sGQ n₀') ≤ QQPJ C C' j n₀' at hFab
  change w.1.length + 2 ≤ QQPJ C C' j n₀' at hwQ
  change ChildList w.1.length F (casePred (mainCase (kQP C) (ℓQP C C')
    (((xy, w, σd, N, gs, ()), n₀', n, lab) : HInstData Ty.unit)) w.1.length (N - n)) ch at hch
  have hsome : ∀ m', lab.map (fun _ => N - n) = some m' → m' = N - n ∧ 1 ≤ N - n ∧
      mainCase (kQP C) (ℓQP C C') (((xy, w, σd, N, gs, ()), n₀', n, lab) : HInstData Ty.unit) ≠
        .chain ∧
      mainCase (kQP C) (ℓQP C C') (((xy, w, σd, N, gs, ()), n₀', n, lab) : HInstData Ty.unit) ≠
        .m0 := by
    intro m' hm'
    rcases lab with _ | L
    · cases hm'
    · cases hm'
      exact ⟨rfl, hI.base_pos rfl, mainCase_some.1, mainCase_some.2⟩
  have hnone : lab.map (fun _ => N - n) = none →
      mainCase (kQP C) (ℓQP C C') (((xy, w, σd, N, gs, ()), n₀', n, lab) : HInstData Ty.unit) =
        .base ∨
      mainCase (kQP C) (ℓQP C C') (((xy, w, σd, N, gs, ()), n₀', n, lab) : HInstData Ty.unit) =
        .chain ∨
      mainCase (kQP C) (ℓQP C C') (((xy, w, σd, N, gs, ()), n₀', n, lab) : HInstData Ty.unit) =
        .m0 := by
    intro h
    rcases lab with _ | L
    · exact mainCase_none
    · cases h
  have hS := sharpHyp_qpJ hQ n₀'
  have hm45 : N - n ≤ 1 →
      mainCase (kQP C) (ℓQP C C') (((xy, w, σd, N, gs, ()), n₀', n, lab) : HInstData Ty.unit) ≠
        .m4 ∧
      mainCase (kQP C) (ℓQP C C') (((xy, w, σd, N, gs, ()), n₀', n, lab) : HInstData Ty.unit) ≠
        .m5 := by
    intro hm1
    have hℓ := four_mul_kQP_le C C' n₀'
    have hk5 := five_le_kQP C n₀'
    refine ⟨fun h4 => ?_, fun h5 => ?_⟩
    · obtain ⟨-, L, -, -, -, hbig⟩ := mainCase_big h4 (Or.inl rfl)
      have := (bigCase_eq_m4 hbig).1
      omega
    · obtain ⟨-, L, -, -, -, hbig⟩ := mainCase_big h5 (Or.inr rfl)
      have := (bigCase_eq_m5 hbig).1
      omega
  generalize mainCase (kQP C) (ℓQP C C')
    (((xy, w, σd, N, gs, ()), n₀', n, lab) : HInstData Ty.unit) =
      c at hF ha hb hFab hch hsome hnone hm45
  have hab : c ≠ .m5 → a = 0 ∧ b = 0 := fun h5 => by
    rw [caseA_eq_zero h5] at ha
    rw [caseB_eq_zero h5] at hb
    omega
  rw [show sGQ n₀' = 2 * n₀' * (2 * n₀') from rfl] at hFab
  refine pot_case_le hk hwQ hW (by omega) hch hnone hsome hab (fun h => ?_) (fun h => ?_)
    (fun hm1 => ?_) (fun hp => ?_)
  · subst h
    simpa [caseFS, caseF] using hF
  · rcases h with rfl | rfl | rfl | rfl <;> simpa [caseFS, caseF] using hF
  · obtain ⟨h4, h5⟩ := hm45 hm1
    refine ⟨h4, h5, ?_⟩
    have hF' : F ≤ caseF c n N (kQP C n₀') (m4J ssCtx.O n (N, gs, ())) := by
      rwa [caseFS_of_ne h4 h5] at hF
    have hf1 : (N - n).factorial ≤ 1 := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hm1 with h | h <;> simp [h]
    cases c <;> simp only [caseF] at hF' <;>
      first | exact absurd rfl h4 | exact absurd rfl h5 | omega
  · rw [hp, caseA_zero_win] at ha
    rw [hp, caseB_zero_win] at hb
    omega

/-- **The potential bound** (`PLAN-14.md` §14.13 item 5). Under `QPHypJ K T C C' j`, every valid
instance of `MiniDom n₀ n₀ (2n₀)` with the label invariant gets a correct answer from
`mainBody (thrQP C C')`, with at most `(2n₀)²` generators, within `potO Q 2 |W| bo + Q` for
`Q = QQPJ C C' j n₀`. -/
theorem main_potJ (hQ : QPHypJ K T C C' j) (I : HInstData Ty.unit) (hI : HInstValid ssDV I)
    (hd : MiniDom n₀ n₀ (2 * n₀) I) (hIL : LabInv I) :
    ∃ ans : AnswerData Ty.unit,
      RunsWithin ssCtx (mainBody (thrQP C C') Ty.denote) (mainBody (thrQP C C') Ty.denote I) ans
        (potO (QQPJ C C' j n₀) 2 I.winSize I.baseOpt + QQPJ C C' j n₀) ∧
      I.inst.OK ssDV ans ∧
        ∀ c : CosetData Ty.unit, ans = some c → c.2.gens.length ≤ 2 * n₀ * (2 * n₀) := by
  suffices h : ∀ r, PotIH (thrQP C C') (QQPJ C C' j n₀) n₀ r from
    h _ I hI hd hIL (Nat.lt_succ_self _)
  intro r
  induction r with
  | zero => exact fun J _ _ _ h => absurd h (Nat.not_lt_zero _)
  | succ r ih =>
    intro J hJ hdJ hLJ hr
    rcases Nat.lt_succ_iff_lt_or_eq.1 hr with hlt | heq
    · exact ih J hJ hdJ hLJ hlt
    · rw [← heq] at ih
      exact pot_ind_stepJ hQ hJ hdJ hLJ ih

end Induction

section Headline

variable {K T : ℕ → ℕ} {C C' : ℕ} {j : ℕ → ℕ}

/-- **The full procedure within the potential** (`PLAN-14.md` §14.13 item 6). Under
`QPHypJ K T C C' j`, for every valid instance, the entry at the thresholds `thrQP C C'` generates
the group and recurses on the instance without a hint (`n₀ = n = N`, in the domain `nB = N`,
`NB = 2N`, which has the label invariant: `LabInv.entry`). The answer is correct, within
`genCost N |gs| + 2 + 15 + potO Q 2 |W| none + Q` for `Q = QQPJ C C' j N`. -/
theorem mainSolve_qpJ (hQ : QPHypJ K T C C' j) {xy : StrData × StrData} {w : WinData}
    {σd : PermData} {N : ℕ} {gs : GensData}
    (hw : w.Valid N) (hσ : σd.Valid N) (hgs : GensData.AllValid N gs)
    (hinv : IsInvariant (GensData.denote N gs) (w.denote N)) :
    ∃ ans : AnswerData Ty.unit,
      RunsWithin ssCtx (mainBody (thrQP C C') Ty.denote)
        (mainEntry Ty.unit Ty.denote (xy, w, σd, N, gs)) ans
        (genCost N gs.length + 2 + 15 +
          (potO (QQPJ C C' j N) 2 w.1.length none + QQPJ C C' j N)) ∧
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
  obtain ⟨ans, hrun, hok, -⟩ := main_potJ hQ _ hI hd (LabInv.entry _ N)
  replace hrun : RunsWithin ssCtx (mainBody (thrQP C C') Ty.denote)
      (mainBody (thrQP C C') Ty.denote
        (((xy, w, σd, N, generateModel N gs, ()), N, N, none) : HInstData Ty.unit)) ans
      (potO (QQPJ C C' j N) 2 w.1.length none + QQPJ C C' j N) := hrun
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

/-- **The headline in closed form in `Q`**: through `pot0_le`, the cost of `mainSolve_qpJ` is at
most `genCost N |gs| + 17 + (2N + 2) N² Q^{2 (5 λ(N) + 9 + 4 (λ(N) + 6)²)} + Q` with
`Q = QQPJ C C' j N`, i.e. `Q^{O(log² N)}`. -/
theorem mainSolve_qp_closedJ (hQ : QPHypJ K T C C' j) {xy : StrData × StrData} {w : WinData}
    {σd : PermData} {N : ℕ} {gs : GensData}
    (hw : w.Valid N) (hσ : σd.Valid N) (hgs : GensData.AllValid N gs)
    (hinv : IsInvariant (GensData.denote N gs) (w.denote N)) :
    ∃ ans : AnswerData Ty.unit,
      RunsWithin ssCtx (mainBody (thrQP C C') Ty.denote)
        (mainEntry Ty.unit Ty.denote (xy, w, σd, N, gs)) ans
        (genCost N gs.length + 17 +
          (2 * N + 2) * N ^ 2 *
            QQPJ C C' j N ^ (2 * (5 * lam N + 9 + 4 * (lam N + 6) ^ 2)) + QQPJ C C' j N) ∧
      AnsOK ssDV N (w.denote N) (σd.denote N) (gs.denote N) (xy.1.denote N) (xy.2.denote N)
        ans := by
  obtain ⟨ans, hrun, hok⟩ := mainSolve_qpJ hQ (xy := xy) hw hσ hgs hinv
  refine ⟨ans, hrun.mono ?_, hok⟩
  have hwN : w.1.length ≤ N := mf_length_le_of_nodup hw.nodup hw.lt
  have hQ1 : 1 ≤ QQPJ C C' j N := by unfold QQPJ; omega
  have h1 := potO_none_mono (b := 2) hQ1 hwN
  have h2 := pot0_le (QQPJ C C' j N) 2 N
  omega

end Headline

end GraphIso.Main

namespace GraphIso.Growth

open GraphIso.Main GraphIso.Recursion

theorem Main.qpM4J_qpb {j : ℕ → ℕ} (hj : PLB lam 5 j) :
    QPB lam 6 (fun n₀ => GraphIso.Main.qpM4J j n₀) := by
  unfold GraphIso.Main.qpM4J
  exact (QPB.supTo
    (Main.m4PtNsL_qpb (QPB.lift (id_qpb.comp _) (by norm_num))
      (QPB.mul (QPB.const _) (id_qpb.comp _)) (PLB.bvar_le hj)
      (QPB.lift (id_qpb.comp _) (by norm_num))
      (Main.sGQ_qpb (QPB.lift (id_qpb.comp _) (by norm_num)))
      (QPB.lift (id_qpb.comp _) (by norm_num))
      (Main.sGQ_qpb (QPB.lift (id_qpb.comp _) (by norm_num)))
      (Main.ssLgM4Ns_qpb
        (QPB.add (QPB.mul (QPB.const _) (id_qpb.comp _)) (PLB.qpb (PLB.comp hj _)))
        (PLB.comp hj _) (uMaxQ_plb.comp _)
        (Main.sGQ_qpb (QPB.lift (id_qpb.comp _) (by norm_num)))) (uMaxQ_plb.comp _)))

theorem Main.qpM5J_qpb (C : ℕ) {j : ℕ → ℕ} (hj : PLB lam 5 j) :
    QPB lam 6 (fun n₀ => GraphIso.Main.qpM5J C j n₀) := by
  unfold GraphIso.Main.qpM5J
  exact (QPB.add
    (Main.rbOverSS_qpb
      (QPB.mul (QPB.const _) (id_qpb.lift (by norm_num))) (id_qpb.lift (by norm_num))
      (QPB.mul (QPB.const _) (id_qpb.lift (by norm_num))) (Main.sGQ_qpb (id_qpb.lift (by norm_num)))
      (Main.sGQ_qpb (id_qpb.lift (by norm_num))))
    (Main.m5WorkUB_qpb id_qpb (QPB.mul (QPB.const _) id_qpb) (kQP_plb C) (id_qpb.lift (by norm_num))
      (Main.sGQ_qpb (id_qpb.lift (by norm_num))) (Main.sGQ_qpb (id_qpb.lift (by norm_num)))
      (Main.ssLgM5Ns_qpb (QPB.mul (QPB.const _) id_qpb) (kQP_plb C) uMaxQ_plb hj
        (Main.sGQ_qpb (id_qpb.lift (by norm_num)))) uMaxQ_plb hj))

theorem Main.qpCasesJ_qpb (C C' : ℕ) {j : ℕ → ℕ} (hj : PLB lam 5 j) :
    QPB lam 6 (fun n₀ => GraphIso.Main.qpCasesJ C C' j n₀) := by
  unfold GraphIso.Main.qpCasesJ
  exact (QPB.add
    (QPB.add
      (QPB.add
        (QPB.add
          (QPB.add
            (QPB.add
              (QPB.add
                (QPB.add
                  (Main.fixedStepCost_qpb (id_qpb.lift (by norm_num)))
                  (Main.chainCost_qpb
                    (QPB.mul (QPB.const _) (id_qpb.lift (by norm_num))) (id_qpb.lift (by norm_num))
                    (id_qpb.lift (by norm_num))))
                (Main.m0WorkSS_qpb (id_qpb.lift (by norm_num))
                  (QPB.mul (QPB.const _) (id_qpb.lift (by norm_num))) (id_qpb.lift (by norm_num))
                  (Main.sGQ_qpb (id_qpb.lift (by norm_num)))
                  (Main.sGQ_qpb (id_qpb.lift (by norm_num)))))
              (Main.m1WorkSS_qpb (id_qpb.lift (by norm_num))
                (QPB.mul (QPB.const _) (id_qpb.lift (by norm_num))) (id_qpb.lift (by norm_num))
                (Main.sGQ_qpb (id_qpb.lift (by norm_num)))
                (Main.sGQ_qpb (id_qpb.lift (by norm_num)))))
            (Main.m2aWorkSS_qpb (id_qpb.lift (by norm_num))
              (QPB.mul (QPB.const _) (id_qpb.lift (by norm_num))) (id_qpb.lift (by norm_num))
              (Main.sGQ_qpb (id_qpb.lift (by norm_num))) (Main.sGQ_qpb (id_qpb.lift (by norm_num)))
              (id_qpb.lift (by norm_num))))
          (Main.m2bWorkSS_qpb (id_qpb.lift (by norm_num))
            (QPB.mul (QPB.const _) (id_qpb.lift (by norm_num))) (id_qpb.lift (by norm_num))
            (Main.sGQ_qpb (id_qpb.lift (by norm_num))) (id_qpb.lift (by norm_num))
            (Main.sGQ_qpb (id_qpb.lift (by norm_num)))))
        (Main.m3WorkSS_qpb
          (QPB.mul (QPB.const _) (id_qpb.lift (by norm_num))) (id_qpb.lift (by norm_num))
          (Main.sGQ_qpb (id_qpb.lift (by norm_num))) (Main.sGQ_qpb (id_qpb.lift (by norm_num)))
          (m3_sub_plb C C'))) (Main.qpM4J_qpb hj)) (Main.qpM5J_qpb C hj))

theorem Main.qpWorkJ_qpb (C C' : ℕ) {j : ℕ → ℕ} (hj : PLB lam 5 j) :
    QPB lam 6 (fun n₀ => GraphIso.Main.qpWorkJ C C' j n₀) := by
  unfold GraphIso.Main.qpWorkJ
  exact (QPB.add (Main.qpTest_qpb C) (Main.qpCasesJ_qpb C C' hj))

theorem Main.qpFacJ_qpb (C C' : ℕ) {j : ℕ → ℕ} (hj : PLB lam 5 j) :
    QPB lam 6 (fun n₀ => GraphIso.Main.qpFacJ C C' j n₀) := by
  unfold GraphIso.Main.qpFacJ
  exact (QPB.add
    (QPB.add
      (QPB.add
        (QPB.add
          (QPB.add
            (QPB.add
              (QPB.mul (QPB.const _) (id_qpb.lift (by norm_num))) (QPB.factorial (mLQ_plb C C')))
            (QPB.mul
              (Main.m4R_qpb
                (QPB.add (QPB.mul (QPB.const _) id_qpb) (PLB.qpb hj)) hj)
              (QPB.max
                (QPB.mul (QPB.const _) (id_qpb.lift (by norm_num))) (QPB.factorial uMaxQ_plb))))
          (Main.m5FBns_qpb (QPB.mul (QPB.const _) id_qpb) (kQP_plb C) uMaxQ_plb hj))
        (QPB.add
          (QPB.mul (QPB.const _)
            (Main.certCount_qpb
              (QPB.add id_qpb (QPB.mul (QPB.const _) id_qpb)) (id_qpb.lift (by norm_num))
              (kQP_plb C)))
          (QPB.mul (QPB.const _)
            (Main.c3Count_qpb (QPB.mul (QPB.const _) id_qpb) (kQP_plb C)
              (id_qpb.lift (by norm_num))))))
      (QPB.mul
        (QPB.add (Main.sGQ_qpb (id_qpb.lift (by norm_num))) (QPB.const _))
        (id_qpb.lift (by norm_num)))) (QPB.const _))

theorem Main.QQPJ_qpb (C C' : ℕ) {j : ℕ → ℕ} (hj : PLB lam 5 j) :
    QPB lam 6 (fun n₀ => GraphIso.Main.QQPJ C C' j n₀) := by
  unfold GraphIso.Main.QQPJ
  exact (QPB.add
    (QPB.add (QPB.add (id_qpb.lift (by norm_num)) (QPB.const _)) (Main.qpWorkJ_qpb C C' hj))
    (Main.qpFacJ_qpb C C' hj))

end GraphIso.Growth

namespace GraphIso.Main

open Equiv Pointwise Cost GraphIso GraphIso.Graph GraphIso.Recursion Sims

/-- **The closed bound** for `j ∈ PLB λ 5`: `QQPJ C C' j n₀ ≤ 2^{c (λ(n₀) + 1)⁶}`. -/
theorem QQPJ_le_exp (C C' : ℕ) {j : ℕ → ℕ} (hj : Growth.PLB lam 5 j) :
    ∃ c, ∀ n₀, QQPJ C C' j n₀ ≤ 2 ^ (c * (lam n₀ + 1) ^ 6) :=
  Growth.Main.QQPJ_qpb C C' hj

/-- **The headline with the closed bound** (`PLAN-14.md` §14.14 item 5). For all `C`, `C'`
and `j ∈ PLB λ 5` there is `c` such that for all `K` and `T` with `QPHypJ K T C C' j`, on every
valid plain instance (as in `mainSolve_qpJ`), `mainEntry (thrQP C C')` returns a correct answer
(`AnsOK`) within `genCost N |gs| + 2^{c (λ(N) + 1)⁸}`. The constant `c` depends only on `C`, `C'`
and `j`. `QPHypJ Kpy Tq 192 181 jq` holds (`GraphIso.Wielandt.qpHypJ_final`). -/
theorem mainSolve_qp_expJ (C C' : ℕ) {j : ℕ → ℕ} (hj : Growth.PLB lam 5 j) :
    ∃ c, ∀ {K T : ℕ → ℕ}, QPHypJ K T C C' j →
      ∀ {xy : StrData × StrData} {w : WinData} {σd : PermData} {N : ℕ} {gs : GensData},
        w.Valid N → σd.Valid N → GensData.AllValid N gs →
        IsInvariant (GensData.denote N gs) (w.denote N) →
        ∃ ans : AnswerData Ty.unit,
          RunsWithin ssCtx (mainBody (thrQP C C') Ty.denote)
            (mainEntry Ty.unit Ty.denote (xy, w, σd, N, gs)) ans
            (genCost N gs.length + 2 ^ (c * (lam N + 1) ^ 8)) ∧
          AnsOK ssDV N (w.denote N) (σd.denote N) (gs.denote N) (xy.1.denote N)
            (xy.2.denote N) ans := by
  obtain ⟨c₀, hc₀⟩ := QQPJ_le_exp C C' hj
  refine ⟨306 * c₀ + 7, fun hQ xy w σd N gs hw hσ hgs hinv => ?_⟩
  obtain ⟨ans, hrun, hok⟩ := mainSolve_qp_closedJ hQ (xy := xy) hw hσ hgs hinv
  refine ⟨ans, hrun.mono ?_, hok⟩
  have := qp_closed_le (hc₀ N)
  omega

section Gens

variable {xy : StrData × StrData} {w : WinData} {σd : PermData} {N : ℕ} {gs : GensData}
variable {K T : ℕ → ℕ} {C C' : ℕ} {j : ℕ → ℕ}

/-- **`mainSolve_qpJ` with the generator count**: at most `(2N)²` generators. -/
theorem mainSolve_qp_gensJ (hQ : QPHypJ K T C C' j) (hw : w.Valid N) (hσ : σd.Valid N)
    (hgs : GensData.AllValid N gs) (hinv : IsInvariant (GensData.denote N gs) (w.denote N)) :
    ∃ ans : AnswerData Ty.unit,
      RunsWithin ssCtx (mainBody (thrQP C C') Ty.denote)
        (mainEntry Ty.unit Ty.denote (xy, w, σd, N, gs)) ans
        (genCost N gs.length + 2 + 15 +
          (potO (QQPJ C C' j N) 2 w.1.length none + QQPJ C C' j N)) ∧
      AnsOK ssDV N (w.denote N) (σd.denote N) (gs.denote N) (xy.1.denote N) (xy.2.denote N)
        ans ∧
      ∀ c : CosetData Ty.unit, ans = some c → c.2.gens.length ≤ 2 * N * (2 * N) := by
  obtain ⟨hI, hd, -⟩ := entry_hinst (xy := xy) hw hσ hgs hinv
  obtain ⟨ans, hrun, hok, hg⟩ := main_potJ hQ _ hI hd (LabInv.entry _ N)
  exact ⟨ans, mainEntry_of_body hgs hrun, entry_ok hgs hok, hg⟩

/-- **`mainSolve_qp_expJ` with the generator count.** -/
theorem mainSolve_qp_exp_gensJ (C C' : ℕ) {j : ℕ → ℕ} (hj : Growth.PLB lam 5 j) :
    ∃ c, ∀ {K T : ℕ → ℕ}, QPHypJ K T C C' j →
      ∀ {xy : StrData × StrData} {w : WinData} {σd : PermData} {N : ℕ} {gs : GensData},
        w.Valid N → σd.Valid N → GensData.AllValid N gs →
        IsInvariant (GensData.denote N gs) (w.denote N) →
        ∃ ans : AnswerData Ty.unit,
          RunsWithin ssCtx (mainBody (thrQP C C') Ty.denote)
            (mainEntry Ty.unit Ty.denote (xy, w, σd, N, gs)) ans
            (genCost N gs.length + 2 ^ (c * (lam N + 1) ^ 8)) ∧
          AnsOK ssDV N (w.denote N) (σd.denote N) (gs.denote N) (xy.1.denote N)
            (xy.2.denote N) ans ∧
          ∀ c : CosetData Ty.unit, ans = some c → c.2.gens.length ≤ 2 * N * (2 * N) := by
  obtain ⟨c₀, hc₀⟩ := QQPJ_le_exp C C' hj
  refine ⟨306 * c₀ + 7, fun hQ xy w σd N gs hw hσ hgs hinv => ?_⟩
  obtain ⟨ans, hrun, hok, hg⟩ := mainSolve_qp_gensJ hQ (xy := xy) hw hσ hgs hinv
  refine ⟨ans, hrun.mono ?_, hok, hg⟩
  have hwN : w.1.length ≤ N := mf_length_le_of_nodup hw.nodup hw.lt
  have hQ1 : 1 ≤ QQPJ C C' j N := by unfold QQPJ; omega
  have h1 := potO_none_mono (b := 2) hQ1 hwN
  have h2 := pot0_le (QQPJ C C' j N) 2 N
  have := qp_closed_le (hc₀ N)
  omega

end Gens

section GI

/-- **Graph isomorphism in time `2^{O((log n)⁸)}`** (`PLAN-14.md` §14.15 item 6). For all `C`,
`C'` and `j ∈ PLB λ 5` there is `c` such that for all `K`, `T` with `QPHypJ K T C C' j`: on valid
graph data `X`, `Y` on `n` points (of any degree), the closed entry at the thresholds
`thrQP C C'` (Schreier–Sims substituted, no oracle) returns a `GICosetOK` result with local cost
at most
`2^{c (λ(n) + 1)⁸}`. The cost covers the encoding, `generate`, the recursion and the decoding.

`QPHypJ Kpy Tq 192 181 jq` holds (`GraphIso.Wielandt.qpHypJ_final`); correctness alone is
`giSolve_ss`. -/
theorem giSolve_qp_expJ (C C' : ℕ) {j : ℕ → ℕ} (hj : Growth.PLB lam 5 j) :
    ∃ c, ∀ {K T : ℕ → ℕ}, QPHypJ K T C C' j → ∀ {Δ n : ℕ} {X Y : GraphData},
      X.ValidD Δ n → Y.ValidD Δ n →
      ∃ (r : Option (PermData × GensData)) (tr : Trace Signature.empty),
        Runs Ctx.empty.O ((qpSolver C C').proc Ty.denote)
          ((giEntry Ty.unit Ty.denote (n, X, Y)).subst ssImpl) r tr ∧
        Trace.localCost tr ≤ 2 ^ (c * (lam n + 1) ^ 8) ∧ GICosetOK n X Y r := by
  obtain ⟨c₁, hc₁⟩ := mainSolve_qp_exp_gensJ C C' hj
  refine ⟨256 * c₁ + 23, fun hQ Δ n X Y hX hY => ?_⟩
  obtain ⟨hw, hσ, hgs, hinv⟩ := giInst_valid n
  have hmain := hc₁ hQ (xy := (gStr n X, gStr n Y)) hw hσ hgs hinv
  obtain ⟨r, hrun, hok⟩ := giEntry_runs (thr := thrQP C C') hX hY hmain
  obtain ⟨tr, hr, hc⟩ := gi_close (thrQP_spec C C').wf hrun
  exact ⟨r, tr, hr, hc.trans (gi_cost_le n c₁), hok⟩

/-- **Graph isomorphism of simple graphs in time `2^{O((log n)⁸)}`.** For all `C`, `C'` and
`j ∈ PLB λ 5` there is `c` such that for all `K`, `T` with `QPHypJ K T C C' j`: for simple graphs
`G`, `H` on `Fin n`, given by their adjacency lists, the closed entry at the thresholds
`thrQP C C'` returns `r` with local cost at most `2^{c (λ(n) + 1)⁸}`; `r = none` exactly when
`G` and `H` are not isomorphic, and `r = some (τ, hs)` gives valid data of a permutation and of
generators such that the coset `τ • ⟨hs⟩` is exactly the set of the permutations underlying the
isomorphisms `G ≃g H`.
`QPHypJ Kpy Tq 192 181 jq` holds (`GraphIso.Wielandt.qpHypJ_final`). -/
theorem gi_qp_simpleGraphJ (C C' : ℕ) {j : ℕ → ℕ} (hj : Growth.PLB lam 5 j) :
    ∃ c, ∀ {K T : ℕ → ℕ}, QPHypJ K T C C' j → ∀ {n : ℕ} (G H : SimpleGraph (Fin n))
      [DecidableRel G.Adj] [DecidableRel H.Adj],
      ∃ (r : Option (PermData × GensData)) (tr : Trace Signature.empty),
        Runs Ctx.empty.O ((qpSolver C C').proc Ty.denote)
          ((giEntry Ty.unit Ty.denote
            (n, GraphData.ofSimpleGraph G, GraphData.ofSimpleGraph H)).subst ssImpl) r tr ∧
        Trace.localCost tr ≤ 2 ^ (c * (lam n + 1) ^ 8) ∧
        (r = none ↔ IsEmpty (G ≃g H)) ∧
        ∀ τ hs, r = some (τ, hs) → τ.Valid n ∧ GensData.AllValid n hs ∧
          {φ : Perm (Fin n) | ∃ e : G ≃g H, e.toEquiv = φ} =
            PermData.denote n τ • (GensData.denote n hs : Set (Perm (Fin n))) := by
  obtain ⟨c, hc⟩ := giSolve_qp_expJ C C' hj
  refine ⟨c, fun hQ n G H _ _ => ?_⟩
  have hG := valid_ofSimpleGraph (Δ := n) (H := G) fun v => (G.degree_lt_card_verts v).le.trans
    (by simp)
  have hH := valid_ofSimpleGraph (Δ := n) (H := H) fun v => (H.degree_lt_card_verts v).le.trans
    (by simp)
  obtain ⟨r, tr, hr, hcost, ⟨hnone, hsome⟩⟩ := hc hQ hG hH
  have hset : {φ : Perm (Fin n) | ∃ e : G ≃g H, e.toEquiv = φ} =
      {φ | IsIso n (GraphData.ofSimpleGraph G) (GraphData.ofSimpleGraph H) φ} := by
    ext φ
    exact (isIso_ofSimpleGraph_iff φ).symm
  refine ⟨r, tr, hr, hcost, ?_, fun τ hs h => ?_⟩
  · rw [hnone, not_exists, isEmpty_iff]
    constructor
    · intro h e
      exact h e.toEquiv ((isIso_ofSimpleGraph_iff _).2 ⟨e, rfl⟩)
    · intro h φ hφ
      obtain ⟨e, -⟩ := (isIso_ofSimpleGraph_iff φ).1 hφ
      exact h e
  · obtain ⟨h₁, h₂, -, h₄⟩ := hsome τ hs h
    exact ⟨h₁, h₂, hset.trans h₄⟩

end GI

end GraphIso.Main
