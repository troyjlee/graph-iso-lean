module

public import GraphIso.Main.Full
public import GraphIso.Main.SimsM5Ns

/-!
# The sharp dispatcher

Stage 14j-6b-2 (`PLAN-14.md` §14.12). The full procedure, with M4 and M5 charged through the
steps without stuck orbits of stage 14j-6b-1 (`m4StepProg_nsL_ss`, `m5StepCJProg_ns_ss`). The
procedure and its programs are unchanged.

* **The numeric hypotheses** (`SharpHyp K T n₀ k ℓ`), at the thresholds `k = kf n₀`,
  `ℓ = ℓf n₀`: `Thresholds K n₀ k` (milestone 12), `TransitivityBound T`, `4k ≤ ℓ`, and
  `TBelow T ℓ`: every `m > ℓ` has `4 · supTo T m + 6 ≤ m`, where `supTo T m` is `T`'s maximum on
  `[0, m]`. `12 ≤ ℓ` is not needed: it follows from `4k ≤ ℓ` and `5 ≤ k`.
* **No M3 above `ℓ`** (`mainCase_m3_le`): a giant base meets M5's test, and a base that is not a
  giant has `2j + 6 ≤ m` (`ss_m4J_sharp`, from `m4_deg_le_T`) and meets M4's test.
* **M4 and M5 without stuck orbits** (`main_m4_sharp`, `main_m5_sharp`), with the union-cell
  bound `t · λ(m)` for any `t` at least the label length, `Lg = ssLgM4Ns`, `ssLgM5Ns`, and Case
  2b's depth bound `jB = supTo T m`.
* **The sharp case functions** `caseWorkS`, `caseFS` and `mainWorkS`: `caseWork`, `caseF` and
  `mainWork` except at M4 and M5, where they are the work and factor of the two steps above, at
  the instance's label length `labT I`. Apart from M3, whose base is at most `ℓ` above, they
  contain no factorial of the base size; M4's and M5's contain `(t · λ(m))!`, `k!` and powers of
  `m` (`m^j`, `m^{jB}`).
* **The step** `main_step_sharp`: `main_step_lab`'s conclusion with `mainWorkS` and `caseFS`, and
  `mainCase = .m3 → m ≤ ℓ`, under `SharpHyp`.
* **`TBelow` is satisfiable at Wielandt's bound** `wielandtT k = 3 (⌊log₂ k⌋ + 1)`, above
  `ℓ = 128` (`tBelow_wielandt`).

**What `SharpHyp` needs.** Its interfaces are hypotheses here. The witness instances
(`altQuotientIso_succ`, `transitivityBound_id`) do not give `SharpHyp`: `TBelow id ℓ` fails at
every `ℓ` (`not_tBelow_id`). **Historical:** milestones 15 (Pyber, `AltQuotientIso` for
`Thresholds`) and 16 (Wielandt, `TransitivityBound wielandtT`) were to discharge it. Milestone 16
proves the quadratic `TransitivityBound Tq` instead (`transitivityBound_quad`), and
`SharpHyp Kpy Tq n₀ (kQP 192 n₀) (ℓQP 192 181 n₀)` holds for every `n₀`, by
`sharpHyp_qpJ qpHypJ_final` (`GraphIso/Main/QPJ.lean`, `GraphIso/Wielandt/Final.lean`).
-/

@[expose] public section

namespace GraphIso.Main

open Equiv Cost GraphIso GraphIso.Programs GraphIso.Toolkit GraphIso.Recursion GraphIso.Certificates
  Sims

/-! ### The numeric hypotheses -/

section Numeric

/-- **The depths are small above `ℓ`**: every base of `m > ℓ` points has
`4 · max_{m' ≤ m} T(m') + 6 ≤ m`. -/
def TBelow (T : ℕ → ℕ) (ℓ : ℕ) : Prop := ∀ m, ℓ < m → 4 * supTo T m + 6 ≤ m

/-- **The numeric hypotheses of the sharp dispatcher**, at the thresholds `k` and `ℓ` of `n₀`,
for the interfaces' functions `K` and `T`. -/
structure SharpHyp (K T : ℕ → ℕ) (n₀ k ℓ : ℕ) : Prop where
  thr : Thresholds K n₀ k
  trans : AltQuot.TransitivityBound T
  k4 : 4 * k ≤ ℓ
  below : TBelow T ℓ

/-- `Thresholds` on a smaller degree. -/
theorem _root_.GraphIso.Certificates.Thresholds.of_le {K : ℕ → ℕ} {n n' k : ℕ}
    (h : Thresholds K n k) (hn : n' ≤ n) : Thresholds K n' k :=
  ⟨h.iso, h.mono, h.five, (h.mono hn).trans h.le, lt_of_le_of_lt hn h.lt⟩

/-- **Wielandt's transitivity bound** `T k = 3 (⌊log₂ k⌋ + 1)`. **Historical:** milestone 16 was
to discharge `TransitivityBound` with it, and proves the quadratic `Tq` instead
(`transitivityBound_quad`). -/
def wielandtT (k : ℕ) : ℕ := 3 * (lam k + 1)

/-- `wielandtT` is monotone, so its maximum on `[0, m]` is its value at `m`. -/
theorem supTo_wielandtT (m : ℕ) : supTo wielandtT m = wielandtT m :=
  le_antisymm (supTo_le fun _ hx =>
      Nat.mul_le_mul_left 3 (Nat.add_le_add_right (Nat.log_mono_right hx) 1))
    (le_supTo le_rfl)

theorem twelve_le_pow {a : ℕ} (h : 7 ≤ a) : 12 * a + 18 ≤ 2 ^ a := by
  induction a, h using Nat.le_induction with
  | base => decide
  | succ a _ ih =>
    rw [pow_succ]
    omega

/-- **`TBelow` holds at Wielandt's bound** (item 6), above `ℓ = 128`: the numeric hypothesis
is not vacuous for the intended `T`. (`TransitivityBound wielandtT` itself is not proved.) -/
theorem tBelow_wielandt : TBelow wielandtT 128 := by
  intro m hm
  rw [supTo_wielandtT]
  unfold wielandtT
  have ha : 7 ≤ lam m := Nat.le_log_of_pow_le (by decide) (by omega)
  have hp : 2 ^ lam m ≤ m := Nat.pow_log_le_self 2 (by omega)
  have := twelve_le_pow ha
  omega

/-- **`TBelow` fails for the trivial bound** `T = id` (`transitivityBound_id`), at every `ℓ`. -/
theorem not_tBelow_id (ℓ : ℕ) : ¬ TBelow id ℓ := fun h => by
  have h1 := h (ℓ + 1) (Nat.lt_succ_self ℓ)
  have h2 : id (ℓ + 1) ≤ supTo id (ℓ + 1) := le_supTo le_rfl
  simp only [id] at h2
  omega

end Numeric

/-! ### The dispatcher above `ℓ` -/

section Dispatch

/-- **M4's depth above `ℓ`**: under `TransitivityBound T` and `TBelow T ℓ`, a base of more than
`ℓ` points that is not a giant has `2j + 6 ≤ m` for M4's `j` (`m4_deg_le_T`). -/
theorem ss_m4J_sharp {T : ℕ → ℕ} (hT : AltQuot.TransitivityBound T) {ℓ : ℕ} (hB : TBelow T ℓ)
    {n N : ℕ} {gs : GensData} (hgs : GensData.AllValid N gs)
    (hb : IsInvariant (GensData.denote N gs) (baseSet n N)) (hn : n ≤ N) (hℓ : ℓ < N - n)
    (hgi : m4Deg ssCtx.O n (N, gs, ()) ≠ N - n - 2) :
    2 * m4J ssCtx.O n (N, gs, ()) + 6 ≤ N - n := by
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
  have := hB _ hℓ
  unfold m4J
  omega

theorem bigCase_eq_m4 {k ℓ n N : ℕ} {gs : GensData} (h : bigCase k ℓ n N gs = .m4) :
    ℓ < N - n ∧ m4Deg ssCtx.O n (N, gs, ()) ≠ N - n - 2 ∧
      m4OkD (m4Deg ssCtx.O n (N, gs, ())) (N - n) = true := by
  unfold bigCase at h
  split_ifs at h
  simp_all

theorem bigCase_eq_m5 {k ℓ n N : ℕ} {gs : GensData} (h : bigCase k ℓ n N gs = .m5) :
    ℓ < N - n ∧ m4Deg ssCtx.O n (N, gs, ()) = N - n - 2 ∧ m5OkD k (N - n) = true := by
  unfold bigCase at h
  split_ifs at h
  simp_all

variable {kf ℓf : ℕ → ℕ} {xy : StrData × StrData} {w : WinData} {σd : PermData} {N : ℕ}
  {gs : GensData} {n₀ n : ℕ}

/-- **The path to M4 and M5**: the window is not fixed, there is a hint, the base has one orbit
and no proper block system, and the large-base case is taken. -/
theorem mainCase_big {lab : Option LabelData} {c : MainCase}
    (h : mainCase kf ℓf (((xy, w, σd, N, gs, ()), n₀, n, lab) : HInstData Ty.unit) = c)
    (hc : c = .m4 ∨ c = .m5) :
    GensData.fixesB gs w = false ∧ ∃ L, lab = some L ∧
      ¬ 2 ≤ (ssCtx.O.run GroupOp.orbits ((N, gs, ()), baseWin n N)).length ∧
      blkOKD (N - n) (mbD n N gs) = false ∧ bigCase (kf n₀) (ℓf n₀) n N gs = c := by
  cases hfx : GensData.fixesB gs w with
  | true =>
    simp only [mainCase, hfx, ite_true] at h
    rcases hc with rfl | rfl <;> exact absurd h (by decide)
  | false =>
    refine ⟨rfl, ?_⟩
    rcases lab with _ | L
    · simp only [mainCase, hfx] at h
      rcases hc with rfl | rfl <;> split_ifs at h
    · refine ⟨L, rfl, ?_⟩
      simp only [mainCase, hfx, hintCase] at h
      rcases hc with rfl | rfl <;> split_ifs at h <;> simp_all

/-- **No M3 above `ℓ`** (item 1): under the numeric hypotheses, the dispatcher takes M3 only on
a base of at most `ℓ` points. -/
theorem mainCase_m3_le {K T : ℕ → ℕ} {lab : Option LabelData}
    (hS : SharpHyp K T n₀ (kf n₀) (ℓf n₀))
    (hI : HInstValid ssDV (((xy, w, σd, N, gs, ()), n₀, n, lab) : HInstData Ty.unit))
    (h : mainCase kf ℓf (((xy, w, σd, N, gs, ()), n₀, n, lab) : HInstData Ty.unit) = .m3) :
    N - n ≤ ℓf n₀ := by
  have hgs : GensData.AllValid N gs := hI.valid.group.1
  rcases lab with _ | L
  · simp only [mainCase] at h
    split_ifs at h
  · simp only [mainCase, hintCase, bigCase] at h
    by_contra hℓ
    have hℓ' : ℓf n₀ < N - n := by omega
    have h5 := hS.thr.five
    have hk4 := hS.k4
    split_ifs at h with h1 h2 h3 h4 h5' h6 h7
    · rw [m5OkD_iff] at h6
      omega
    · have hb : IsInvariant (GensData.denote N gs) (baseSet n N) := hI.base_inv
      have hnN : n ≤ N := hI.le
      have := ss_m4J_sharp hS.trans hS.below hgs hb hnN hℓ' h5'
      rw [m4OkD_iff] at h7
      unfold m4J at this
      omega

end Dispatch

/-! ### M4 and M5 without stuck orbits -/

section Steps

variable {thr : ThrProg Ty.unit} {n₀ nB NB : ℕ} {xy : StrData × StrData} {w : WinData}
  {σd : PermData} {N : ℕ} {gs : GensData} {n₀' n : ℕ} {C : ℕ → Option ℕ → ℕ} {b : Bool}

/-- **M4 in the full procedure without stuck orbits** (item 2): a transitive base that is not a
giant, with `2j + 6 ≤ m`, at `sIn = NB²`, the union-cell bound `t · λ(m)` for any `t` at least
the label length, and `Lg = ssLgM4Ns m j (t · λ(m)) NB²`. The children's factor is
`m4R m j · max(m, (t · λ(m))!)`. -/
theorem main_m4_sharp (h2 : 2 * nB ≤ NB) {L : LabelData}
    (hI : HInstValid ssDV (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit))
    (hd : MiniDom n₀ nB NB (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit))
    (hsub : MainSubB thr b n₀ nB NB
      (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit) C)
    (hbL : LabInvIf b (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit))
    (htr : IsTransOn (GensData.denote N gs) (baseSet n N))
    (hng : m4Deg ssCtx.O n (N, gs, ()) < N - n - 2)
    (hj : 2 * m4J ssCtx.O n (N, gs, ()) + 6 ≤ N - n) {t : ℕ} (ht : labLen L ≤ t) :
    ∃ (ans : AnswerData Ty.unit) (ch : List (ℕ × Option ℕ)),
      RunsWithin ssCtx (mainBody thr Ty.denote)
        (Main.m4StepProg (fun J => Prog.recur J)
          (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit)) ans
        ((ch.map fun x => C x.1 x.2).sum +
          m4WorkNsLSS n (N - n) (m4J ssCtx.O n (N, gs, ())) w.1.length (NB * NB) L.size (NB * NB)
            (ssLgM4Ns (N - n) (m4J ssCtx.O n (N, gs, ())) (t * lam (N - n)) (NB * NB))
            (t * lam (N - n))) ∧
      InstData.OK (D := Ty.unit) (xy, w, σd, N, gs, ()) ssDV ans ∧
      (∀ c : CosetData Ty.unit, ans = some c → c.2.gens.length ≤ NB * NB) ∧
      ChildList w.1.length
        (m4R (N - n) (m4J ssCtx.O n (N, gs, ())) * max (N - n) (t * lam (N - n)).factorial)
        (StepChild w.1.length (N - n)) ch := by
  have hN : N ≤ NB := hd.degree_le
  have hgl : gs.length ≤ NB * NB := hd.gens_le
  have hW : 1 ≤ w.1.length := hI.win_pos rfl
  have hm : 1 ≤ N - n := hI.base_pos rfl
  obtain ⟨hk4, hpart, hS, hm5⟩ := m4_numeric hj
  have hu : labLen L * lam (N - n) ≤ t * lam (N - n) := Nat.mul_le_mul_right _ ht
  have hf : max (N - n) (labLen L * lam (N - n)).factorial ≤
      max (N - n) (t * lam (N - n)).factorial :=
    max_le_max le_rfl (Nat.factorial_le hu)
  obtain ⟨ans, ch, hrun, hok, hg, hch, hR⟩ := RunsWithin.m4StepProg_nsL_ss hI
    (dv_baseHom_trans hI.base_inv htr) hng hk4 hpart hS hm5
    (hsub.step fun J hJ ⟨hS', hc⟩ => main_predB h2 hd hbL hJ hS' le_rfl (StepChild.measLt hc hW hm))
    hgl (Nat.mul_le_mul hN hN) le_rfl
    (Lg := ssLgM4Ns (N - n) (m4J ssCtx.O n (N, gs, ())) (t * lam (N - n)) (NB * NB))
    (Nat.mul_le_mul_right _ (hf.trans (Nat.le_add_right _ _)))
    (Nat.mul_le_mul_right _ (Nat.le_add_left _ _))
  exact ⟨ans, ch, hrun.mono (Nat.add_le_add_left (m4WorkNsLSS_mono le_rfl le_rfl le_rfl le_rfl
    le_rfl le_rfl le_rfl le_rfl hu) _), hok, hg, hch.mono_factor (Nat.mul_le_mul hR hf)⟩

/-- `m5FBns` is monotone in the union-cell bound. -/
theorem m5FBns_mono_u {m k uB uB' jB : ℕ} (h : uB ≤ uB') :
    m5FBns m k uB jB ≤ m5FBns m k uB' jB := by
  have hf : max m uB.factorial ≤ max m uB'.factorial := max_le_max le_rfl (Nat.factorial_le h)
  have h1 := Nat.mul_le_mul_left (Case3.c3R k m (Case2b.sojZ m)) hf
  have h2 := Nat.mul_le_mul_left (c2bRj m jB) hf
  unfold m5FBns
  omega

/-- **M5 in the full procedure without stuck orbits** (item 3): a giant base with `4k ≤ m`,
`12 ≤ m` and `Thresholds K p k` on the window, under `TransitivityBound T` with
`4 · supTo T m ≤ m`. It runs at `sIn = NB²`, the union-cell bound `uB = t · λ(m)` for any `t` at
least the label length, Case 2b's depth bound `jB = supTo T m` and
`Lg = ssLgM5Ns m k uB jB NB²`. The children's factor is at most `m5FBns m k uB jB`; the counted
calls are bounded as in `main_m5_at`. -/
theorem main_m5_sharp (h2 : 2 * nB ≤ NB) {L : LabelData}
    (hI : HInstValid ssDV (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit))
    (hd : MiniDom n₀ nB NB (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit))
    (hsub : MainSubB thr b n₀ nB NB
      (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit) C)
    (hbL : LabInvIf b (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit))
    (hC : ∀ a b, a ≤ b → C a none ≤ C b none)
    (halt : alternatingGroup (Fin (N - n)) ≤ (baseHom (GensData.denote N gs) n hI.base_inv).range)
    {k : ℕ} (h4k : 4 * k ≤ N - n) (h12 : 12 ≤ N - n) {K : ℕ → ℕ}
    (hTh : Thresholds K w.1.length k) {T : ℕ → ℕ} (hT : AltQuot.TransitivityBound T)
    (h4j : 4 * supTo T (N - n) ≤ N - n) {t : ℕ} (ht : labLen L ≤ t) :
    ∃ (ans : AnswerData Ty.unit) (ch : List (ℕ × Option ℕ)) (F a b : ℕ),
      RunsWithin ssCtx (mainBody thr Ty.denote)
        (Main.m5StepCJProg (fun J => Prog.recur J)
          (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit) L k noStD) ans
        ((ch.map fun x => C x.1 x.2).sum + a * C (w.1.length / k) none +
          b * C (w.1.length / 2) none +
          (rbOverSS N w.1.length (N - n) gs.length (NB * NB) +
            m5WorkNsSS w.1.length (N - n) k w.1.length (NB * NB) (NB * NB)
              (ssLgM5Ns (N - n) k (t * lam (N - n)) (supTo T (N - n)) (NB * NB))
              (t * lam (N - n)) (supTo T (N - n)))) ∧
      InstData.OK (D := Ty.unit) (xy, w, σd, N, gs, ()) ssDV ans ∧
      (∀ c : CosetData Ty.unit, ans = some c → c.2.gens.length ≤ NB * NB) ∧
      ChildList w.1.length F (StepChild w.1.length (N - n)) ch ∧
      F ≤ m5FBns (N - n) k (t * lam (N - n)) (supTo T (N - n)) ∧
      a ≤ 2 * certCount (w.1.length + (N - n)) w.1.length k +
        2 * c3Count (N - n) k w.1.length ∧
      b ≤ (NB * NB + 1) * w.1.length := by
  have hN : N ≤ NB := hd.degree_le
  have hn : n ≤ nB := hd.n_le
  have hgl : gs.length ≤ NB * NB := hd.gens_le
  have hNN : N * N ≤ NB * NB := Nat.mul_le_mul hN hN
  have hwn := sh_length_le hI
  have hW : 1 ≤ w.1.length := hI.win_pos rfl
  have hm : 1 ≤ N - n := hI.base_pos rfl
  have h5 := hTh.five
  have hsC : max (NB * NB) (supTo (fun M => M * M) (w.1.length / 2)) ≤ NB * NB :=
    max_le le_rfl (supTo_le fun M hM => by
      have : M ≤ NB := by omega
      exact Nat.mul_le_mul this this)
  have hu : labLen L * lam (N - n) ≤ t * lam (N - n) := Nat.mul_le_mul_right _ ht
  have hf : max (N - n) (labLen L * lam (N - n)).factorial ≤
      max (N - n) (t * lam (N - n)).factorial :=
    max_le_max le_rfl (Nat.factorial_le hu)
  have hjB : ∀ m' ≤ N - n, T m' ≤ supTo T (N - n) + 1 := fun m' hm' =>
    (le_supTo hm').trans (Nat.le_succ _)
  obtain ⟨fxs, fys, ex, ey, ans, ch, ⟨hCS, φ, -, hFx, hFy⟩, hrun, hok, hg, hch⟩ :=
    RunsWithin.m5StepCJProg_ns_ss hI halt
      (hsub.step fun J hJ ⟨hS, hc⟩ => main_predB h2 hd hbL hJ hS hsC (StepChild.measLt hc hW hm))
      h5 (by omega) (by omega) h12 hNN hgl hC le_rfl
      (Lg := ssLgM5Ns (N - n) k (t * lam (N - n)) (supTo T (N - n)) (NB * NB))
      (Nat.mul_le_mul_right _ ((hf.trans (Nat.le_add_right _ _)).trans (Nat.le_add_right _ _)))
      (Nat.mul_le_mul_right _ (by omega)) noStD_fst hT hjB h4j hTh h4k
  cases ex
  cases ey
  have hR := length_rbPts n N w
  have hRN : (rbPts n N w).length ≤ N := by
    have := hI.win_lt
    have hle : n ≤ N := hI.le
    rw [hR]
    omega
  have hRm : (rbPts n N w).length - w.1.length = N - n := by omega
  have hfx := hFx.1.1
  have hfy := hFy.1.1
  have hbx := hFx.base_inv
  have hby := hFy.base_inv
  have hNs : (rbPts n N w).length * (rbPts n N w).length ≤ NB * NB :=
    Nat.mul_le_mul (hRN.trans hN) (hRN.trans hN)
  have hjB' : ∀ m' ≤ (rbPts n N w).length - w.1.length, T m' ≤ supTo T (N - n) + 1 := by
    rw [hRm]
    exact hjB
  have hF := ss_m5CFnsCJ_le (k := k) (uB := labLen L * lam (N - n)) (jB := supTo T (N - n))
    hfy hby fun h4 => by
      obtain ⟨h2', hA⟩ := m5Sel_four h4
      exact ss_m5_depth_le hT hNs hjB' hFx h2' hA
  have hK := ss_m5CKCJ_le (k := k) (fys := fys) hfx hbx
  rw [hRm] at hF hK
  have hH := m5CH_le ssCtx.O w.1.length (rbPts n N w).length (NB * NB) w.1.length
    ((rbPts n N w).length, fxs, ()) ((rbPts n N w).length, fys, ())
  refine ⟨ans, ch, _, 2 * certCount (rbPts n N w).length w.1.length k +
      m5CKCJ ssCtx.O w.1.length (rbPts n N w).length k ((rbPts n N w).length, fxs, ())
        ((rbPts n N w).length, fys, ()),
    m5CH ssCtx.O w.1.length (rbPts n N w).length (NB * NB) w.1.length
      ((rbPts n N w).length, fxs, ()) ((rbPts n N w).length, fys, ()), ?_, hok,
    hg (NB * NB) (fun hs hv _ => (ssOracle_gens_le hv).1.trans hNN), hch,
    hF.trans (m5FBns_mono_u hu), Nat.add_le_add (le_of_eq (by rw [hR])) hK, hH⟩
  refine hrun.mono ?_
  rw [rbCost_eq]
  have hBgm := rbCost_mono_Bgm (N := N) (k := w.1.length) (m := N - n) (s := gs.length) (C' := 0)
    (s' := NB * NB) (sK := N * N) (Blift := Sims.liftCost N (NB * NB) N + 7)
    (Bker := kerCost N (NB * NB) N + 5) (Bgn := genCost N (N * N + NB * NB) + 2)
    (Nat.add_le_add_right (genCost_mono₂ hRN (le_refl (NB * NB))) 2)
  have hWm : m5WorkNsSS w.1.length (N - n) k w.1.length (NB * NB) (NB * NB)
      (ssLgM5Ns (N - n) k (t * lam (N - n)) (supTo T (N - n)) (NB * NB))
      (labLen L * lam (N - n)) (supTo T (N - n)) ≤
      m5WorkNsSS w.1.length (N - n) k w.1.length (NB * NB) (NB * NB)
        (ssLgM5Ns (N - n) k (t * lam (N - n)) (supTo T (N - n)) (NB * NB))
        (t * lam (N - n)) (supTo T (N - n)) :=
    m5WorkNsSS_mono le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl hu le_rfl
  unfold rbOverSS
  generalize C (w.1.length / k) none = X at *
  generalize C (w.1.length / 2) none = Y at *
  generalize (ch.map fun x => C x.1 x.2).sum = sc
  generalize certCount (rbPts n N w).length w.1.length k = cc
  generalize m5CKCJ ssCtx.O w.1.length (rbPts n N w).length k ((rbPts n N w).length, fxs, ())
    ((rbPts n N w).length, fys, ()) = ck
  generalize m5CH ssCtx.O w.1.length (rbPts n N w).length (NB * NB) w.1.length
    ((rbPts n N w).length, fxs, ()) ((rbPts n N w).length, fys, ()) = chh
  have e : (2 * cc + ck) * X = 2 * cc * X + ck * X := Nat.add_mul _ _ _
  omega

end Steps

/-! ### The sharp case functions -/

section Work

/-- **The work of each case without stuck orbits** (item 4), for `n` string positions, degree
`N`, a window of `p` points, `g` generators, the domain's generator bound `s`, M5's `k`, M4's
`j`, the label length `t` and Case 2b's depth bound `jB`: `caseWork` except at M4 and M5, whose
work is that of `main_m4_sharp` and `main_m5_sharp` (union-cell bound `t · λ(m)`). -/
def caseWorkS : MainCase → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  | .base, n, N, p, g, s, k, j, _, _ => caseWork .base n N p g s k j
  | .chain, n, N, p, g, s, k, j, _, _ => caseWork .chain n N p g s k j
  | .m0, n, N, p, g, s, k, j, _, _ => caseWork .m0 n N p g s k j
  | .m1, n, N, p, g, s, k, j, _, _ => caseWork .m1 n N p g s k j
  | .m2a, n, N, p, g, s, k, j, _, _ => caseWork .m2a n N p g s k j
  | .m2b, n, N, p, g, s, k, j, _, _ => caseWork .m2b n N p g s k j
  | .m3, n, N, p, g, s, k, j, _, _ => caseWork .m3 n N p g s k j
  | .m4, n, N, p, _, s, _, j, t, _ =>
    m4WorkNsLSS n (N - n) j p s n s (ssLgM4Ns (N - n) j (t * lam (N - n)) s) (t * lam (N - n))
  | .m5, n, N, p, g, s, k, _, t, jB =>
    rbOverSS N p (N - n) g s +
      m5WorkNsSS p (N - n) k p s s (ssLgM5Ns (N - n) k (t * lam (N - n)) jB s) (t * lam (N - n))
        jB

/-- **The children's factor of each case without stuck orbits**: `caseF` except at M4,
`m4R m j · max(m, (t · λ(m))!)`, and M5, `m5FBns m k (t · λ(m)) jB`. -/
def caseFS : MainCase → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  | .base, n, N, k, j, _, _ => caseF .base n N k j
  | .chain, n, N, k, j, _, _ => caseF .chain n N k j
  | .m0, n, N, k, j, _, _ => caseF .m0 n N k j
  | .m1, n, N, k, j, _, _ => caseF .m1 n N k j
  | .m2a, n, N, k, j, _, _ => caseF .m2a n N k j
  | .m2b, n, N, k, j, _, _ => caseF .m2b n N k j
  | .m3, n, N, k, j, _, _ => caseF .m3 n N k j
  | .m4, n, N, _, j, t, _ => m4R (N - n) j * max (N - n) (t * lam (N - n)).factorial
  | .m5, n, N, k, _, t, jB => m5FBns (N - n) k (t * lam (N - n)) jB

theorem caseWorkS_of_ne {c : MainCase} (h4 : c ≠ .m4) (h5 : c ≠ .m5) (n N p g s k j t jB : ℕ) :
    caseWorkS c n N p g s k j t jB = caseWork c n N p g s k j := by
  cases c <;> first | contradiction | rfl

theorem caseFS_of_ne {c : MainCase} (h4 : c ≠ .m4) (h5 : c ≠ .m5) (n N k j t jB : ℕ) :
    caseFS c n N k j t jB = caseF c n N k j := by
  cases c <;> first | contradiction | rfl

/-- The label length of an instance's hint, `0` without a hint. -/
def labT (I : HInstData Ty.unit) : ℕ :=
  match I.lab with
  | none => 0
  | some L => labLen L

/-- **The work of one step without stuck orbits** on `I`: the tests and `caseWorkS` of the case
the dispatcher takes, with the label length of `I` and Case 2b's depth bound `supTo T m`. -/
def mainWorkS (kf ℓf cT T : ℕ → ℕ) (s : ℕ) (I : HInstData Ty.unit) : ℕ :=
  mainTestCost I.n I.inst.degree I.winSize I.inst.2.2.2.gens.length s (cT I.n₀) +
    caseWorkS (mainCase kf ℓf I) I.n I.inst.degree I.winSize I.inst.2.2.2.gens.length s (kf I.n₀)
      (m4J ssCtx.O I.n (I.inst.degree, I.inst.2.2.2.gens, ())) (labT I)
      (supTo T (I.inst.degree - I.n))

theorem mainWorkS_eq (kf ℓf cT T : ℕ → ℕ) (s : ℕ) (xy : StrData × StrData) (w : WinData)
    (σd : PermData) (N : ℕ) (gs : GensData) (n₀ n : ℕ) (L : LabelData) :
    mainWorkS kf ℓf cT T s (((xy, w, σd, N, gs, ()), n₀, n, some L) : HInstData Ty.unit) =
      mainTestCost n N w.1.length gs.length s (cT n₀) +
        caseWorkS (mainCase kf ℓf (((xy, w, σd, N, gs, ()), n₀, n, some L) : HInstData Ty.unit))
          n N w.1.length gs.length s (kf n₀) (m4J ssCtx.O n (N, gs, ())) (labLen L)
          (supTo T (N - n)) := rfl

theorem mainWorkS_of_ne {kf ℓf cT T : ℕ → ℕ} {s : ℕ} {I : HInstData Ty.unit}
    (h4 : mainCase kf ℓf I ≠ .m4) (h5 : mainCase kf ℓf I ≠ .m5) :
    mainWorkS kf ℓf cT T s I = mainWork kf ℓf cT s I := by
  unfold mainWorkS mainWork
  rw [caseWorkS_of_ne h4 h5]

end Work

/-! ### One step -/

section Step

variable {thr : ThrProg Ty.unit} {kf ℓf cT : ℕ → ℕ} {n₀ nB NB : ℕ}

/-- **One step of the full procedure without stuck orbits** (item 5). For a parent with
`LabInv`, under the numeric hypotheses `SharpHyp K T n₀ k ℓ` at `k = kf n₀` and `ℓ = ℓf n₀`, the
conclusion of `main_step_lab` holds with the work `mainWorkS` and the factor bound `caseFS`, at
the parent's label length `t = labT I` and Case 2b's depth bound `supTo T m`; and the dispatcher
takes M3 only on a base of at most `ℓ` points. -/
theorem main_step_sharp (hT : ThrSpec thr kf ℓf cT) (h2 : 2 * nB ≤ NB) {I : HInstData Ty.unit}
    (hI : HInstValid ssDV I) (hd : MiniDom n₀ nB NB I) (hIL : LabInv I) {C : ℕ → Option ℕ → ℕ}
    (hC : ∀ a b, a ≤ b → C a none ≤ C b none) (hsub : MainSubL thr n₀ nB NB I C)
    {K T : ℕ → ℕ} (hS : SharpHyp K T n₀ (kf n₀) (ℓf n₀)) :
    (mainCase kf ℓf I = .m3 → I.inst.degree - I.n ≤ ℓf n₀) ∧
    ∃ (ans : AnswerData Ty.unit) (ch : List (ℕ × Option ℕ)) (F a b : ℕ),
      RunsWithin ssCtx (mainBody thr Ty.denote) (mainBody thr Ty.denote I) ans
        ((ch.map fun x => C x.1 x.2).sum + a * C (I.winSize / kf I.n₀) none +
          b * C (I.winSize / 2) none + mainWorkS kf ℓf cT T (NB * NB) I) ∧
      I.inst.OK ssDV ans ∧ (∀ c : CosetData Ty.unit, ans = some c → c.2.gens.length ≤ NB * NB) ∧
      ChildList I.winSize F (casePred (mainCase kf ℓf I) I.winSize (I.inst.degree - I.n)) ch ∧
      F ≤ caseFS (mainCase kf ℓf I) I.n I.inst.degree (kf I.n₀)
        (m4J ssCtx.O I.n (I.inst.degree, I.inst.2.2.2.gens, ())) (labT I)
        (supTo T (I.inst.degree - I.n)) ∧
      a ≤ caseA (mainCase kf ℓf I) I.n I.inst.degree I.winSize (kf I.n₀) ∧
      b ≤ caseB (mainCase kf ℓf I) I.winSize (NB * NB) := by
  obtain ⟨⟨xy, w, σd, N, gs, d⟩, n₀', n, lab⟩ := I
  cases d
  obtain rfl : n₀' = n₀ := hd.n₀
  refine ⟨mainCase_m3_le hS hI, ?_⟩
  by_cases h45 : mainCase kf ℓf (((xy, w, σd, N, gs, ()), n₀', n, lab) : HInstData Ty.unit) = .m4 ∨
      mainCase kf ℓf (((xy, w, σd, N, gs, ()), n₀', n, lab) : HInstData Ty.unit) = .m5
  swap
  · obtain ⟨h4, h5⟩ := not_or.1 h45
    obtain ⟨ans, ch, F, a, b, hrun, hok, hg, hch, hF, ha, hb⟩ :=
      main_step_lab hT h2 hI hd hIL hC hsub
    refine ⟨ans, ch, F, a, b, ?_, hok, hg, hch, ?_, ha, hb⟩
    · rw [mainWorkS_of_ne h4 h5]
      exact hrun
    · rw [caseFS_of_ne h4 h5]
      exact hF
  obtain ⟨hfx, L, rfl, hsplit, hok, hbig⟩ := mainCase_big rfl h45
  have hv : InstData.Valid (D := Ty.unit) (xy, w, σd, N, gs, ()) ssDV := hI.valid
  have hgs : GensData.AllValid N gs := hv.group.1
  have hwn := sh_length_le hI
  have hN : N ≤ NB := hd.degree_le
  have hgl : gs.length ≤ NB * NB := hd.gens_le
  have hnn₀ : n ≤ n₀' := hIL.n_le
  have hb : IsInvariant (GensData.denote N gs) (baseSet n N) := hI.base_inv
  have hnN : n ≤ N := hI.le
  have hNN : N * N ≤ NB * NB := Nat.mul_le_mul hN hN
  have hI' := HInstValid.normLab hI
  have hd' : MiniDom n₀' nB NB
      (((xy, w, σd, N, gs, ()), n₀', n, some (normLabD n L)) : HInstData Ty.unit) :=
    ⟨hd.n₀, hd.n_le, hd.degree_le, hd.gens_le⟩
  have hsub' : MainSubB thr true n₀' nB NB
      (((xy, w, σd, N, gs, ()), n₀', n, some (normLabD n L)) : HInstData Ty.unit) C := hsub.toB
  have hbL' := LabInvIf.normLab (b := true) fun _ => hIL
  have hos : IsOrbitPartition (GensData.denote N gs) (baseWin n N)
      (ssCtx.O.run GroupOp.orbits ((N, gs, ()), baseWin n N)) := ss_baseOrbits hgs hb
  have hLs : (normLabD n L).size = n := normLabD_size n L
  have hone : (ssCtx.O.run GroupOp.orbits ((N, gs, ()), baseWin n N)).length ≤ 1 := by omega
  have htrB : IsTransOn (GensData.denote N gs) (baseSet n N) := (base_trans_iff hos).2 hone
  have hB := ssBoundsS N (NB * NB) ⊤ hNN
  rcases h45 with hc | hc
  · rw [hc] at hbig
    obtain ⟨hℓ, hgi, h4⟩ := bigCase_eq_m4 hbig
    have hdegs := degreeModel_spec (cap := N - n - 2) (d := ())
      (fun op x _ hx => ssOracle_meets op x hx) hB ⟨hgs, trivial⟩ hgl le_top hb hnN (by omega)
    have hng : m4Deg ssCtx.O n (N, gs, ()) < N - n - 2 := lt_of_le_of_ne hdegs.1 hgi
    have hj := ss_m4J_sharp hS.trans hS.below hgs hb hnN hℓ hgi
    obtain ⟨ans, ch, hrun, hok', hg, hch⟩ := main_m4_sharp h2 hI' hd' hsub' hbL' htrB hng hj
      (labLen_normLabD_le n L)
    refine ⟨ans, ch, _, 0, 0, (main_top_hint hfx (RunsWithin.hintProg_big hgs hb hone hok
      (RunsWithin.bigProg_m4 (s := NB * NB) hT hgs hb hnN hgl hNN hℓ hgi h4 hrun))).mono ?_, hok',
      hg, by rw [hc]; exact hch, by rw [hc]; exact le_rfl, by rw [hc]; exact le_rfl,
      by rw [hc]; exact le_rfl⟩
    rw [mainWorkS_eq, hc, hLs]
    simp only [caseWorkS, mainTestCost, Nat.zero_mul]
    generalize (ch.map fun x => C x.1 x.2).sum = sc
    clear * -
    omega
  · rw [hc] at hbig
    obtain ⟨hℓ, hgi, h5⟩ := bigCase_eq_m5 hbig
    have halt : alternatingGroup (Fin (N - n)) ≤
        (baseHom (GensData.denote N gs) n hI.base_inv).range :=
      (giantModel_iff (d := ()) (fun op x _ hx => ssOracle_meets op x hx) hB ⟨hgs, trivial⟩
        hgl le_top hb hnN).1 (beq_iff_eq.2 hgi)
    obtain ⟨-, -, h12⟩ := m5OkD_iff.1 h5
    have h4k : 4 * kf n₀' ≤ N - n := by
      have := hS.k4
      omega
    have h4j : 4 * supTo T (N - n) ≤ N - n := by
      have := hS.below _ hℓ
      omega
    obtain ⟨ans, ch, F, a, b, hrun, hok', hg, hch, hF, ha, hb'⟩ :=
      main_m5_sharp h2 hI' hd' hsub' hbL' hC halt h4k h12 (hS.thr.of_le (hwn.trans hnn₀))
        hS.trans h4j (labLen_normLabD_le n L)
    refine ⟨ans, ch, F, a, b, (main_top_hint hfx (RunsWithin.hintProg_big hgs hb hone hok
      (RunsWithin.bigProg_m5 (s := NB * NB) hT hgs hb hnN hgl hNN hℓ hgi h5 hrun))).mono ?_, hok',
      hg, by rw [hc]; exact hch, by rw [hc]; exact hF, by rw [hc]; exact ha, by rw [hc]; exact hb'⟩
    rw [mainWorkS_eq, hc]
    simp only [caseWorkS, mainTestCost]
    dsimp only [HInstData.winSize, HInstData.n₀, HInstData.inst]
    generalize (ch.map fun x => C x.1 x.2).sum = sc
    generalize a * C (w.1.length / kf n₀') none = sa
    generalize b * C (w.1.length / 2) none = sb
    clear * -
    omega

end Step

end GraphIso.Main
