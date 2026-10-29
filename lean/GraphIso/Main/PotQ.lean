module

public import GraphIso.Main.PotWork
public import GraphIso.Main.PotThr

/-!
# The bound `Q(n₀)` on a step's work and multiplicity

Stage 14j-6c-1 (`PLAN-14.md` §14.13 items 2 and 3). On the domain `MiniDom n₀ n₀ (2n₀)` with
the label invariant, at the thresholds `kQP C`, `ℓQP C C'` (`GraphIso.Main.PotThr`), under
`QPHyp K T C C'`:

* **What the step sees.**
  - M3 occurs only on bases of at most `ℓ` points (`mainCase_m3_le`).
  - M4 and M5 occur only on bases above `ℓ ≥ ell0 n₀`. There the label invariant bounds the
    union cells: `t λ(m) ≤ uMaxQ n₀ = 2 (λ(n₀) + 1)²` (`labLen_mul_lam_le`).
  - M4's depth is at most `supTo T m` (`ss_m4J_le_T`, from `m4_deg_le_T`).
  - That depth bound and Case 2b's `supTo T m` are at most `jMaxQ C' n₀ = C' (λ(2n₀) + 1)`
    (`supTo_le_jMaxQ`).
  - M5 has `5 ≤ k`, `2k ≤ m`, and `supTo T m < m` (`TBelow`).
* **`Q(n₀)`** (`QQP C C' n₀`) is the sum of `n₀ + 2`, the work at the corners (`qpWork`) and
  the factors at the corners (`qpFac`).
  - `qpWork` is the tests' cost at the corner (`qpTest`) plus every case's work at the corner of
    its sizes (`qpCases`):
    - the base case, the chain rule, M0, M1, M2a and M2b at `n = p = n₀`, `N = m = 2n₀`, `2n₀`
      on the base and `(2n₀)²` generators;
    - M3 on a base of `min(ℓ, 2n₀)` points;
    - M4's corner bound (`caseWorkS_m4_le`) maximized over `j ≤ jMaxQ` (`qpM4`);
    - M5's (`caseWorkS_m5_le`) at `jB = jMaxQ` (`qpM5`).
  - `qpFac` is every case's factor plus its counted calls at the corners: `2n₀` (M2b),
    `min(ℓ, 2n₀)!` (M3), `m4R` and `uMaxQ!` (M4), `m5FBns`, the certificates' and Case 3's
    counted calls, and Case 2a's (M5).
* **The bounds** on every valid instance of the domain with `LabInv`, in the case the dispatcher
  takes:
  - `mainWorkS_le_QQP`: the step's work `mainWorkS` is at most `Q`;
  - `caseFAB_le_QQP`: the factor plus the counted calls is at most `Q`, hence at most `Q²`;
  - `winSize_add_two_le_QQP`: `|W| + 2 ≤ Q`.

  The corners are reached through the monotonicity lemmas of `SharpWork` and `PotWork`. A
  difference `N − n` is moved to the corner by shifting both arguments (for M3,
  `(2n₀ − min(ℓ, 2n₀), 2n₀)`). M4's `m − j` is moved by evaluating `m4R` and `ssLgM4Ns` at
  `m + jMaxQ`.

The only factorials in `Q` are `min(ℓ, 2n₀)!`, `uMaxQ!` and `k!`. No factorial of a base
above `ℓ` enters `Q`.
-/

@[expose] public section

namespace GraphIso.Main

open Equiv Cost GraphIso GraphIso.Programs GraphIso.Toolkit GraphIso.Recursion GraphIso.Certificates
  Sims

/-! ### The corners -/

section Corners

/-- The domain's generator bound `(2n₀)²`. -/
def sGQ (n₀ : ℕ) : ℕ := 2 * n₀ * (2 * n₀)

/-- The union-cell bound above `ell0 n₀`: `2 (λ(n₀) + 1)²`. -/
def uMaxQ (n₀ : ℕ) : ℕ := 2 * (lam n₀ + 1) ^ 2

/-- The bound `C' (λ(2n₀) + 1)` on M4's depth and on Case 2b's depth bound. -/
def jMaxQ (C' n₀ : ℕ) : ℕ := C' * (lam (2 * n₀) + 1)

/-- M3's base bound `min(ℓ, 2n₀)`. -/
def mLQ (C C' n₀ : ℕ) : ℕ := min (ℓQP C C' n₀) (2 * n₀)

/-- The tests' cost at the corner. -/
def qpTest (C n₀ : ℕ) : ℕ := mainTestCost n₀ (n₀ + 2 * n₀) n₀ (sGQ n₀) (sGQ n₀) (cTQP C n₀)

/-- M4's work at the corner, maximized over the depth. -/
def qpM4 (C' n₀ : ℕ) : ℕ :=
  supTo (fun j => m4PtNsL n₀ (2 * n₀) j n₀ (sGQ n₀) n₀ (sGQ n₀)
    (ssLgM4Ns (2 * n₀ + jMaxQ C' n₀) (jMaxQ C' n₀) (uMaxQ n₀) (sGQ n₀)) (uMaxQ n₀)) (jMaxQ C' n₀)

/-- M5's work at the corner: the restriction and `m5WorkUB`. -/
def qpM5 (C C' n₀ : ℕ) : ℕ :=
  rbOverSS (2 * n₀) n₀ (2 * n₀) (sGQ n₀) (sGQ n₀) +
    m5WorkUB n₀ (2 * n₀) (kQP C n₀) n₀ (sGQ n₀) (sGQ n₀)
      (ssLgM5Ns (2 * n₀) (kQP C n₀) (uMaxQ n₀) (jMaxQ C' n₀) (sGQ n₀)) (uMaxQ n₀) (jMaxQ C' n₀)

/-- Every case's work at the corner of its sizes. -/
def qpCases (C C' n₀ : ℕ) : ℕ :=
  fixedStepCost n₀ + chainCost (2 * n₀) n₀ n₀ + m0WorkSS n₀ (2 * n₀) n₀ (sGQ n₀) (sGQ n₀) +
    m1WorkSS n₀ (2 * n₀) n₀ (sGQ n₀) (sGQ n₀) + m2aWorkSS n₀ (2 * n₀) n₀ (sGQ n₀) (sGQ n₀) n₀ +
    m2bWorkSS n₀ (2 * n₀) n₀ (sGQ n₀) n₀ (sGQ n₀) +
    m3WorkSS (2 * n₀ - mLQ C C' n₀) (2 * n₀) n₀ (sGQ n₀) (sGQ n₀) + qpM4 C' n₀ + qpM5 C C' n₀

/-- **The work at the corners**: the tests and every case. -/
def qpWork (C C' n₀ : ℕ) : ℕ := qpTest C n₀ + qpCases C C' n₀

/-- **The factors and counted calls at the corners.** -/
def qpFac (C C' n₀ : ℕ) : ℕ :=
  2 * n₀ + (mLQ C C' n₀).factorial +
    m4R (2 * n₀ + jMaxQ C' n₀) (jMaxQ C' n₀) * max (2 * n₀) (uMaxQ n₀).factorial +
    m5FBns (2 * n₀) (kQP C n₀) (uMaxQ n₀) (jMaxQ C' n₀) +
    (2 * certCount (n₀ + 2 * n₀) n₀ (kQP C n₀) + 2 * c3Count (2 * n₀) (kQP C n₀) n₀) +
    (sGQ n₀ + 1) * n₀ + 1

/-- **`Q(n₀)`**: `n₀ + 2`, the work and the factors at the corners. -/
def QQP (C C' n₀ : ℕ) : ℕ := n₀ + 2 + qpWork C C' n₀ + qpFac C C' n₀

end Corners

/-! ### What the step sees -/

section Facts

variable {K T : ℕ → ℕ} {C C' n₀ : ℕ}

/-- **M4's depth is at most `supTo T m`**, for a base that is not a giant (`m4_deg_le_T`). -/
theorem ss_m4J_le_T (hT : AltQuot.TransitivityBound T) {n N : ℕ} {gs : GensData}
    (hgs : GensData.AllValid N gs) (hb : IsInvariant (GensData.denote N gs) (baseSet n N))
    (hn : n ≤ N) (hgi : m4Deg ssCtx.O n (N, gs, ()) ≠ N - n - 2) :
    m4J ssCtx.O n (N, gs, ()) ≤ supTo T (N - n) := by
  have hBd := ssBoundsS N (N * N + gs.length) ⊤ (Nat.le_add_right _ _)
  have hO : MeetsContractOn ssDV degreeOps ssCtx.O := fun op x _ hx => ssOracle_meets op x hx
  have hP : ¬ alternatingGroup (Fin (N - n)) ≤ (baseHom (GensData.denote N gs) n hb).range :=
    fun h => hgi (by
      have := (giantModel_iff (d := ()) hO hBd ⟨hgs, trivial⟩ (Nat.le_add_left _ _) le_top hb
        hn).2 h
      unfold giantModel at this
      exact beq_iff_eq.1 this)
  have hd := m4_deg_le_T (dd := ()) hT hO hBd ⟨hgs, trivial⟩ (Nat.le_add_left _ _) le_top hb hn hP
  have hs := le_supTo (f := T) (le_refl (N - n))
  unfold m4J
  omega

/-- **The depth bounds** on a base of at most `2n₀` points: `supTo T m ≤ C' (λ(2n₀) + 1)`. -/
theorem supTo_le_jMaxQ (hT : ∀ m, T m ≤ C' * (lam m + 1)) {m : ℕ} (hm : m ≤ 2 * n₀) :
    supTo T m ≤ jMaxQ C' n₀ :=
  supTo_le fun i hi => (hT i).trans
    (Nat.mul_le_mul_left C' (Nat.add_le_add_right (lam_mono (hi.trans hm)) 1))

/-- **The union cells above `ell0 n₀`**: `t λ(m) ≤ t (λ(m) + 1)² ≤ 2 (λ(n₀) + 1)²`. -/
theorem labLen_mul_lam_le {m t : ℕ} (h : LabInvAt n₀ m t) (hm : ell0 n₀ < m) :
    t * lam m ≤ uMaxQ n₀ := by
  have h1 : lam m ≤ (lam m + 1) ^ 2 :=
    (Nat.le_succ _).trans (Nat.le_self_pow (by norm_num) _)
  exact (Nat.mul_le_mul_left t h1).trans (h.2 hm)

end Facts

/-! ### The bounds -/

section Bounds

variable {K T : ℕ → ℕ} {C C' n₀ : ℕ}

/-- **Every case's work is at most its corner value** on the domain with `LabInv`. -/
theorem caseWorkS_le_qpCases (hQ : QPHyp K T C C') {xy : StrData × StrData} {w : WinData}
    {σd : PermData} {N : ℕ} {gs : GensData} {n : ℕ} {lab : Option LabelData}
    (hI : HInstValid ssDV (((xy, w, σd, N, gs, ()), n₀, n, lab) : HInstData Ty.unit))
    (hd : MiniDom n₀ n₀ (2 * n₀) (((xy, w, σd, N, gs, ()), n₀, n, lab) : HInstData Ty.unit))
    (hIL : LabInv (((xy, w, σd, N, gs, ()), n₀, n, lab) : HInstData Ty.unit)) :
    caseWorkS (mainCase (kQP C) (ℓQP C C') (((xy, w, σd, N, gs, ()), n₀, n, lab) :
        HInstData Ty.unit)) n N w.1.length gs.length (sGQ n₀) (kQP C n₀)
        (m4J ssCtx.O n (N, gs, ()))
        (labT (((xy, w, σd, N, gs, ()), n₀, n, lab) : HInstData Ty.unit)) (supTo T (N - n)) ≤
      qpCases C C' n₀ := by
  have hwn := sh_length_le hI
  have hn : n ≤ n₀ := hd.n_le
  have hN : N ≤ 2 * n₀ := hd.degree_le
  have hg : gs.length ≤ sGQ n₀ := hd.gens_le
  have hnN : n ≤ N := hI.le
  have hS := sharpHyp_qp hQ n₀
  generalize hc : mainCase (kQP C) (ℓQP C C')
    (((xy, w, σd, N, gs, ()), n₀, n, lab) : HInstData Ty.unit) = c
  unfold qpCases
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
      (supTo_le_jMaxQ (n₀ := n₀) hQ.tle (by omega))
    have hu : labLen L * lam (N - n) ≤ uMaxQ n₀ :=
      labLen_mul_lam_le (hIL.hint L rfl) ((ell0_le_ℓQP C C' n₀).trans_lt hℓ)
    have hLg : ssLgM4Ns (N - n) (m4J ssCtx.O n (N, gs, ())) (labLen L * lam (N - n)) (sGQ n₀) ≤
        ssLgM4Ns (2 * n₀ + jMaxQ C' n₀) (jMaxQ C' n₀) (uMaxQ n₀) (sGQ n₀) := by
      apply CostMono.Main_ssLgM4Ns <;> omega
    have h4 : caseWorkS .m4 n N w.1.length gs.length (sGQ n₀) (kQP C n₀)
        (m4J ssCtx.O n (N, gs, ())) (labLen L) (supTo T (N - n)) ≤ qpM4 C' n₀ := by
      unfold qpM4
      refine (caseWorkS_m4_le (by omega)).trans (supTo_le fun j' hj' => ?_)
      refine le_trans (m4PtNsL_mono (n' := n₀) (m' := 2 * n₀) (p' := n₀) (s' := sGQ n₀)
        (Ls' := n₀) (sIn' := sGQ n₀) hn (by omega) (by omega) le_rfl hn le_rfl hLg hu
        (by omega)) ?_
      exact le_supTo (f := fun j => m4PtNsL n₀ (2 * n₀) j n₀ (sGQ n₀) n₀ (sGQ n₀)
        (ssLgM4Ns (2 * n₀ + jMaxQ C' n₀) (jMaxQ C' n₀) (uMaxQ n₀) (sGQ n₀)) (uMaxQ n₀))
        (hj'.trans hj)
    change caseWorkS .m4 n N w.1.length gs.length (sGQ n₀) (kQP C n₀)
      (m4J ssCtx.O n (N, gs, ())) (labLen L) (supTo T (N - n)) ≤ _
    omega
  case m5 =>
    obtain ⟨-, L, rfl, -, -, hbig⟩ := mainCase_big hc (Or.inr rfl)
    obtain ⟨hℓ, -, hok⟩ := bigCase_eq_m5 hbig
    obtain ⟨hk5, hkm, -⟩ := m5OkD_iff.1 hok
    have hjB := hS.below (N - n) hℓ
    have hjM := supTo_le_jMaxQ hQ.tle (T := T) (show N - n ≤ 2 * n₀ by omega)
    have hu : labLen L * lam (N - n) ≤ uMaxQ n₀ :=
      labLen_mul_lam_le (hIL.hint L rfl) ((ell0_le_ℓQP C C' n₀).trans_lt hℓ)
    have hLg : ssLgM5Ns (N - n) (kQP C n₀) (labLen L * lam (N - n)) (supTo T (N - n))
        (sGQ n₀) ≤ ssLgM5Ns (2 * n₀) (kQP C n₀) (uMaxQ n₀) (jMaxQ C' n₀) (sGQ n₀) := by
      apply CostMono.Main_ssLgM5Ns <;> omega
    have hr : rbOverSS N w.1.length (N - n) gs.length (sGQ n₀) ≤
        rbOverSS (2 * n₀) n₀ (2 * n₀) (sGQ n₀) (sGQ n₀) := by
      apply CostMono.Main_rbOverSS <;> omega
    have h5 : caseWorkS .m5 n N w.1.length gs.length (sGQ n₀) (kQP C n₀)
        (m4J ssCtx.O n (N, gs, ())) (labLen L) (supTo T (N - n)) ≤ qpM5 C C' n₀ :=
      (caseWorkS_m5_le (by omega) hkm (by omega)).trans (Nat.add_le_add hr
        (m5WorkUB_mono (by omega) (by omega) le_rfl (by omega) le_rfl le_rfl hLg hu hjM
          (by omega) (by omega) (by omega)))
    change caseWorkS .m5 n N w.1.length gs.length (sGQ n₀) (kQP C n₀)
      (m4J ssCtx.O n (N, gs, ())) (labLen L) (supTo T (N - n)) ≤ _
    omega

/-- **The step's work is at most `Q`** on the domain with `LabInv`. -/
theorem mainWorkS_le_QQP (hQ : QPHyp K T C C') {I : HInstData Ty.unit} (hI : HInstValid ssDV I)
    (hd : MiniDom n₀ n₀ (2 * n₀) I) (hIL : LabInv I) :
    mainWorkS (kQP C) (ℓQP C C') (cTQP C) T (2 * n₀ * (2 * n₀)) I ≤ QQP C C' n₀ := by
  obtain ⟨⟨xy, w, σd, N, gs, d⟩, n₀', n, lab⟩ := I
  cases d
  obtain rfl : n₀' = n₀ := hd.n₀
  have hwn := sh_length_le hI
  have hn : n ≤ n₀' := hd.n_le
  have hN : N ≤ 2 * n₀' := hd.degree_le
  have hg : gs.length ≤ sGQ n₀' := hd.gens_le
  have ht : mainTestCost n N w.1.length gs.length (sGQ n₀') (cTQP C n₀') ≤ qpTest C n₀' := by
    apply CostMono.Main_mainTestCost <;> omega
  have hc := caseWorkS_le_qpCases hQ hI hd hIL
  change mainTestCost n N w.1.length gs.length (sGQ n₀') (cTQP C n₀') +
    caseWorkS (mainCase (kQP C) (ℓQP C C') (((xy, w, σd, N, gs, ()), n₀', n, lab) :
        HInstData Ty.unit)) n N w.1.length gs.length (sGQ n₀') (kQP C n₀')
        (m4J ssCtx.O n (N, gs, ()))
        (labT (((xy, w, σd, N, gs, ()), n₀', n, lab) : HInstData Ty.unit)) (supTo T (N - n)) ≤ _
  unfold QQP qpWork
  omega

/-- **The factor plus the counted calls is at most `Q`** on the domain with `LabInv`. -/
theorem caseFAB_le_QQP (hQ : QPHyp K T C C') {I : HInstData Ty.unit} (hI : HInstValid ssDV I)
    (hd : MiniDom n₀ n₀ (2 * n₀) I) (hIL : LabInv I) :
    caseFS (mainCase (kQP C) (ℓQP C C') I) I.n I.inst.degree (kQP C I.n₀)
        (m4J ssCtx.O I.n (I.inst.degree, I.inst.2.2.2.gens, ())) (labT I)
        (supTo T (I.inst.degree - I.n)) +
      caseA (mainCase (kQP C) (ℓQP C C') I) I.n I.inst.degree I.winSize (kQP C I.n₀) +
      caseB (mainCase (kQP C) (ℓQP C C') I) I.winSize (2 * n₀ * (2 * n₀)) ≤ QQP C C' n₀ := by
  obtain ⟨⟨xy, w, σd, N, gs, d⟩, n₀', n, lab⟩ := I
  cases d
  obtain rfl : n₀' = n₀ := hd.n₀
  have hwn := sh_length_le hI
  have hn : n ≤ n₀' := hd.n_le
  have hN : N ≤ 2 * n₀' := hd.degree_le
  have hnN : n ≤ N := hI.le
  have hS := sharpHyp_qp hQ n₀'
  change caseFS (mainCase (kQP C) (ℓQP C C') (((xy, w, σd, N, gs, ()), n₀', n, lab) :
        HInstData Ty.unit)) n N (kQP C n₀') (m4J ssCtx.O n (N, gs, ()))
        (labT (((xy, w, σd, N, gs, ()), n₀', n, lab) : HInstData Ty.unit)) (supTo T (N - n)) +
      caseA (mainCase (kQP C) (ℓQP C C') (((xy, w, σd, N, gs, ()), n₀', n, lab) :
        HInstData Ty.unit)) n N w.1.length (kQP C n₀') +
      caseB (mainCase (kQP C) (ℓQP C C') (((xy, w, σd, N, gs, ()), n₀', n, lab) :
        HInstData Ty.unit)) w.1.length (sGQ n₀') ≤ _
  generalize hc : mainCase (kQP C) (ℓQP C C')
    (((xy, w, σd, N, gs, ()), n₀', n, lab) : HInstData Ty.unit) = c
  unfold QQP qpFac
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
      (supTo_le_jMaxQ (n₀ := n₀') hQ.tle (by omega))
    have hu : labLen L * lam (N - n) ≤ uMaxQ n₀' :=
      labLen_mul_lam_le (hIL.hint L rfl) ((ell0_le_ℓQP C C' n₀').trans_lt hℓ)
    have hR : m4R (N - n) (m4J ssCtx.O n (N, gs, ())) ≤
        m4R (2 * n₀' + jMaxQ C' n₀') (jMaxQ C' n₀') := by
      apply CostMono.Main_m4R <;> omega
    have : m4R (N - n) (m4J ssCtx.O n (N, gs, ())) *
          max (N - n) (labLen L * lam (N - n)).factorial ≤
        m4R (2 * n₀' + jMaxQ C' n₀') (jMaxQ C' n₀') * max (2 * n₀') (uMaxQ n₀').factorial :=
      Nat.mul_le_mul hR (max_le_max (by omega) (Nat.factorial_le hu))
    rw [show labT (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit) = labLen L
      from rfl]
    simp only [caseFS, caseA, caseB]
    omega
  case m5 =>
    obtain ⟨-, L, rfl, -, -, hbig⟩ := mainCase_big hc (Or.inr rfl)
    obtain ⟨hℓ, -, hok⟩ := bigCase_eq_m5 hbig
    obtain ⟨-, hkm, -⟩ := m5OkD_iff.1 hok
    have hjM := supTo_le_jMaxQ hQ.tle (T := T) (show N - n ≤ 2 * n₀' by omega)
    have hu : labLen L * lam (N - n) ≤ uMaxQ n₀' :=
      labLen_mul_lam_le (hIL.hint L rfl) ((ell0_le_ℓQP C C' n₀').trans_lt hℓ)
    have hF : m5FBns (N - n) (kQP C n₀') (labLen L * lam (N - n)) (supTo T (N - n)) ≤
        m5FBns (2 * n₀') (kQP C n₀') (uMaxQ n₀') (jMaxQ C' n₀') := by
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
theorem winSize_add_two_le_QQP {I : HInstData Ty.unit} (hI : HInstValid ssDV I)
    (hd : MiniDom n₀ n₀ (2 * n₀) I) : I.winSize + 2 ≤ QQP C C' n₀ := by
  have := hI.winSize_le
  have := hd.n_le
  unfold QQP
  omega

end Bounds

end GraphIso.Main
