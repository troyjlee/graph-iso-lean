module

public import GraphIso.Main.FullSharp

/-!
# The thresholds of the quasipolynomial bound

Stage 14j-6c-1 (`PLAN-14.md` §14.13 item 1). The interfaces' growth assumptions
(`PLAN-12.md` §2), and the threshold program that meets the sharp dispatcher's numeric
hypotheses under them.

* **The interface hypotheses** `QPHyp K T C C'`: `AltQuotientIso K` with `K` monotone and
  `K n ≤ C (λ(n) + 1)⁵`, and `TransitivityBound T` with `T m ≤ C' (λ(m) + 1)`, where
  `λ = ⌊log₂⌋`. They are hypotheses here. The functions `K` and `T` appear in no program.
* **The thresholds**, with `L(n₀) = ⌈log₂ (n₀ + 2)⌉ ≥ λ(n₀) + 1` (`qpL`, `lam_add_one_le_qpL`):
  - the certificate size `kQP C n₀ = C L⁵ + L + 5`;
  - the base threshold `ℓQP C C' n₀ = 4 k + L³ + 2¹¹ + ℓT C'`, with `ℓT C' = 64 (C' + 1)²`.
* **The threshold program** `thrQP C C'` computes them with local operations (the logarithm by
  `clogProg`, products by repeated addition), within `cTQP C n₀` (`thrQP_spec`).
* **The numeric hypotheses hold** (`sharpHyp_qp`): under `QPHyp K T C C'`, every `n₀` has
  `SharpHyp K T n₀ (kQP C n₀) (ℓQP C C' n₀)` and `ell0 n₀ ≤ ℓQP C C' n₀`, the label invariant's
  threshold.
  - `Thresholds K n₀ k` (`thresholds_qp`): `K n₀ ≤ C L⁵ ≤ k`, and `n₀ < 2^{k-1} ≤ k!/2`.
  - `TBelow T ℓ` (`tBelow_qp`): above `ℓT C'`, `4 C' (λ(m) + 1) + 6 ≤ m`, since
    `(λ(m) + 1)² ≤ 4m`.

`QPHyp` is not shown satisfiable: the witness instances (`altQuotientIso_succ`,
`transitivityBound_id`) do not have these growth bounds. **Historical:** milestones 15 and 16
were to discharge it. Milestone 15 gives `K` (`altQuotientIso_pyber`), but milestone 16 gives only
the quadratic `Tq m = 256 (λ(m) + 1)²` (`transitivityBound_quad`), for which `QPHyp` fails
(`not_qpHyp_Tq`, `GraphIsoChecks/WielandtFinal.lean`). The unconditional theorems use the
generalized hypothesis `QPHypJ` (`GraphIso/Main/QPJ.lean`), discharged by `qpHypJ_final`
(`GraphIso/Wielandt/Final.lean`).
-/

@[expose] public section

namespace GraphIso.Main

open Cost GraphIso GraphIso.Recursion GraphIso.Certificates

/-! ### The interface hypotheses -/

/-- **The interfaces with their growth bounds** (`PLAN-12.md` §2): `AltQuotientIso K` for a
monotone `K ≤ C (λ + 1)⁵`, and `TransitivityBound T` for `T ≤ C' (λ + 1)`. -/
structure QPHyp (K T : ℕ → ℕ) (C C' : ℕ) : Prop where
  iso : AltQuot.AltQuotientIso K
  mono : Monotone K
  le : ∀ n, K n ≤ C * (lam n + 1) ^ 5
  trans : AltQuot.TransitivityBound T
  tle : ∀ m, T m ≤ C' * (lam m + 1)

/-! ### The thresholds -/

/-- `L(n₀) = ⌈log₂ (n₀ + 2)⌉`. -/
def qpL (n₀ : ℕ) : ℕ := Nat.clog 2 (n₀ + 2)

/-- **The certificate size** `k(n₀) = C L⁵ + L + 5`. -/
def kQP (C n₀ : ℕ) : ℕ := C * (qpL n₀ * qpL n₀ * qpL n₀ * qpL n₀ * qpL n₀) + qpL n₀ + 5

/-- The base above which `4 C' (λ(m) + 1) + 6 ≤ m`. -/
def ℓT (C' : ℕ) : ℕ := 64 * ((C' + 1) * (C' + 1))

/-- **The base threshold** `ℓ(n₀) = 4 k + L³ + 2¹¹ + ℓT C'`. -/
def ℓQP (C C' n₀ : ℕ) : ℕ :=
  kQP C n₀ + kQP C n₀ + (kQP C n₀ + kQP C n₀) + qpL n₀ * qpL n₀ * qpL n₀ + (2048 + ℓT C')

/-- `λ(n₀) + 1 ≤ L(n₀)`. -/
theorem lam_add_one_le_qpL (n₀ : ℕ) : lam n₀ + 1 ≤ qpL n₀ := by
  unfold qpL
  rw [Nat.add_one_le_iff, Nat.lt_clog_iff_pow_lt (by norm_num)]
  rcases Nat.eq_zero_or_pos n₀ with rfl | hn
  · simp [lam]
  · have := Nat.pow_log_le_self 2 (Nat.pos_iff_ne_zero.1 hn)
    unfold lam
    omega

/-- `L(n₀) ≤ λ(n₀) + 2`. -/
theorem qpL_le (n₀ : ℕ) : qpL n₀ ≤ lam n₀ + 2 := by
  unfold qpL
  apply Nat.clog_le_of_le_pow
  have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n₀
  have h1 : 1 ≤ 2 ^ Nat.log 2 n₀ := Nat.one_le_two_pow
  unfold lam
  rw [pow_succ, pow_succ] at *
  omega

theorem kQP_eq (C n₀ : ℕ) : kQP C n₀ = C * qpL n₀ ^ 5 + qpL n₀ + 5 := by
  unfold kQP; ring

theorem five_le_kQP (C n₀ : ℕ) : 5 ≤ kQP C n₀ := by unfold kQP; omega

theorem four_mul_kQP_le (C C' n₀ : ℕ) : 4 * kQP C n₀ ≤ ℓQP C C' n₀ := by unfold ℓQP; omega

theorem ℓT_le_ℓQP (C C' n₀ : ℕ) : ℓT C' ≤ ℓQP C C' n₀ := by unfold ℓQP; omega

/-- **The label invariant's threshold is below `ℓ`**. -/
theorem ell0_le_ℓQP (C C' n₀ : ℕ) : ell0 n₀ ≤ ℓQP C C' n₀ := by
  have h := Nat.pow_le_pow_left (lam_add_one_le_qpL n₀) 3
  have e : qpL n₀ ^ 3 = qpL n₀ * qpL n₀ * qpL n₀ := by ring
  unfold ell0 ℓQP
  rw [max_le_iff]
  constructor <;> omega

/-- `2^k ≤ k!` for `k ≥ 4`. -/
theorem two_pow_le_factorial {k : ℕ} (h : 4 ≤ k) : 2 ^ k ≤ k.factorial := by
  induction k, h using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    rw [pow_succ, Nat.factorial_succ]
    calc 2 ^ k * 2 ≤ k.factorial * (k + 1) := Nat.mul_le_mul ih (by omega)
      _ = (k + 1) * k.factorial := Nat.mul_comm _ _

/-- **`Thresholds` at `k(n₀)`**: `K n₀ ≤ C (λ(n₀) + 1)⁵ ≤ C L⁵ ≤ k`, and
`n₀ < 2^{λ(n₀) + 1} ≤ 2^{k - 1} ≤ k!/2`. -/
theorem thresholds_qp {K T : ℕ → ℕ} {C C' : ℕ} (h : QPHyp K T C C') (n₀ : ℕ) :
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

/-- `(L + 1)² ≤ 4 · 2^L`. -/
theorem sq_succ_le_four_pow (L : ℕ) : (L + 1) ^ 2 ≤ 4 * 2 ^ L := by
  induction L with
  | zero => decide
  | succ L ih =>
    have := Nat.lt_two_pow_self (n := L)
    have e : (L + 1 + 1) ^ 2 = (L + 1) ^ 2 + 2 * L + 3 := by ring
    rw [e, pow_succ 2 L]
    omega

/-- **`TBelow` above `ℓT C'`** for every `T ≤ C' (λ + 1)`: with `a = λ(m) + 1`, `a² ≤ 4m`, so
`m ≤ 4 C' a + 6` would give `m < 4 (C' + 1) a`, hence `m² < 64 (C' + 1)² m`. -/
theorem tBelow_qp {T : ℕ → ℕ} {C' : ℕ} (hT : ∀ m, T m ≤ C' * (lam m + 1)) :
    TBelow T (ℓT C') := by
  intro m hm
  unfold ℓT at hm
  have hs : supTo T m ≤ C' * (lam m + 1) :=
    supTo_le fun i hi => (hT i).trans
      (Nat.mul_le_mul_left C' (Nat.add_le_add_right (lam_mono hi) 1))
  have hp : 2 ^ lam m ≤ m := Nat.pow_log_le_self 2 (by omega)
  have ha2 : (lam m + 1) * (lam m + 1) ≤ 4 * m := by
    have := sq_succ_le_four_pow (lam m)
    rw [sq] at this
    omega
  have ha : 6 ≤ lam m := Nat.le_log_of_pow_le (by norm_num) (by
    have : 64 ≤ 64 * ((C' + 1) * (C' + 1)) := Nat.le_mul_of_pos_right _ (by positivity)
    omega)
  by_contra hc
  have h1 : m < 4 * (C' + 1) * (lam m + 1) := by
    have : 4 * C' * (lam m + 1) + 6 > m := by
      have := Nat.mul_le_mul_left 4 hs
      rw [← Nat.mul_assoc] at this
      omega
    nlinarith
  have h3 : m * m < 4 * (C' + 1) * (lam m + 1) * (4 * (C' + 1) * (lam m + 1)) :=
    Nat.mul_self_lt_mul_self h1
  have h4 : 4 * (C' + 1) * (lam m + 1) * (4 * (C' + 1) * (lam m + 1)) =
      16 * ((C' + 1) * (C' + 1)) * ((lam m + 1) * (lam m + 1)) := by ring
  have h5 : 16 * ((C' + 1) * (C' + 1)) * ((lam m + 1) * (lam m + 1)) ≤
      16 * ((C' + 1) * (C' + 1)) * (4 * m) := Nat.mul_le_mul_left _ ha2
  have h6 : m * m < 64 * ((C' + 1) * (C' + 1)) * m := by
    calc m * m < _ := h3
      _ = _ := h4
      _ ≤ 16 * ((C' + 1) * (C' + 1)) * (4 * m) := h5
      _ = 64 * ((C' + 1) * (C' + 1)) * m := by ring
  have := Nat.lt_of_mul_lt_mul_right h6
  omega

theorem TBelow.mono {T : ℕ → ℕ} {ℓ ℓ' : ℕ} (h : TBelow T ℓ) (hℓ : ℓ ≤ ℓ') : TBelow T ℓ' :=
  fun m hm => h m (lt_of_le_of_lt hℓ hm)

/-- **The sharp dispatcher's numeric hypotheses hold at the thresholds** (item 1). -/
theorem sharpHyp_qp {K T : ℕ → ℕ} {C C' : ℕ} (h : QPHyp K T C C') (n₀ : ℕ) :
    SharpHyp K T n₀ (kQP C n₀) (ℓQP C C' n₀) :=
  ⟨thresholds_qp h n₀, h.trans, four_mul_kQP_le C C' n₀,
    (tBelow_qp h.tle).mono (ℓT_le_ℓQP C C' n₀)⟩

/-! ### The threshold program -/

/-- The cost of `thrQP C C'` on `n₀`: the logarithm, the four products of `L`, `C L⁵`, and the
additions. -/
def cTQP (C n₀ : ℕ) : ℕ :=
  SoJProg.clogCost 2 (n₀ + 2) +
    3 * (qpL n₀ + qpL n₀ * qpL n₀ + qpL n₀ * qpL n₀ * qpL n₀ +
      qpL n₀ * qpL n₀ * qpL n₀ * qpL n₀) + 3 * C + 30

/-- **The threshold program**: `L = ⌈log₂ (n₀ + 2)⌉`, `k = C L⁵ + L + 5` and
`ℓ = 4k + L³ + 2¹¹ + ℓT C'`, with local operations only. -/
def thrQP {D : Ty} (C C' : ℕ) : ThrProg D := fun _ n₀ =>
  .bind (.op0 (.natLit 2)) fun two => .bind (.op2 .add n₀ two) fun n2 =>
  .bind (SoJProg.clogProg two n2) fun L =>
  .bind (Toolkit.mulProg L L) fun L2 => .bind (Toolkit.mulProg L2 L) fun L3 =>
  .bind (Toolkit.mulProg L3 L) fun L4 => .bind (Toolkit.mulProg L4 L) fun L5 =>
  .bind (.op0 (.natLit C)) fun c => .bind (Toolkit.mulProg c L5) fun cL5 =>
  .bind (.op2 .add cL5 L) fun a => .bind (.op0 (.natLit 5)) fun five =>
  .bind (.op2 .add a five) fun k => .bind (.op2 .add k k) fun k2 =>
  .bind (.op2 .add k2 k2) fun k4 => .bind (.op2 .add k4 L3) fun b =>
  .bind (.op0 (.natLit (2048 + ℓT C'))) fun c0 => .bind (.op2 .add b c0) fun ℓ =>
  .op2 .pair k ℓ

/-- **`thrQP` meets the threshold contract** with `kQP`, `ℓQP` and `cTQP`. -/
theorem thrQP_spec (C C' : ℕ) :
    ThrSpec (thrQP C C') (kQP C) (ℓQP C C') (cTQP C) := by
  refine ⟨fun _ _ _ _ _ _ _ => by
      unfold thrQP SoJProg.clogProg SoJProg.clogStepProg Coherent.mulNProg Toolkit.mulProg
      prog_wf,
    fun _ _ => by
      unfold thrQP SoJProg.clogProg SoJProg.clogStepProg Coherent.mulNProg Toolkit.mulProg
      repeat' (first | intro _ | constructor),
    fun body n₀ => ?_⟩
  apply RunsWithin.mono
  case h =>
    unfold thrQP
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (SoJProg.RunsWithin.clogProg _ _)
    run_step (Toolkit.RunsWithin.mulProg _ _)
    run_step (Toolkit.RunsWithin.mulProg _ _)
    run_step (Toolkit.RunsWithin.mulProg _ _)
    run_step (Toolkit.RunsWithin.mulProg _ _)
    run_step (RunsWithin.prim _ _)
    run_step (Toolkit.RunsWithin.mulProg _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim _ _
  case hc =>
    simp only [Prim.cost, Prim.eval, cTQP, qpL]
    omega

end GraphIso.Main
