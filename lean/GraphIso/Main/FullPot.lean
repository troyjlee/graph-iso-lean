module

public import GraphIso.Main.PotQ
public import GraphIso.Recursion.PotOffset

/-!
# The potential bound of the full procedure

Stage 14j-6c-1 (`PLAN-14.md` §14.13 items 5 and 6). Under the interface hypotheses
`QPHyp K T C C'` (`GraphIso.Main.PotThr`), the full procedure at the thresholds `thrQP C C'`
costs at most `potO Q 2 |W| bo + Q` on every instance of the domain, for `Q = QQP C C' n₀`
(`GraphIso.Main.PotQ`).

* **The cost of a step within the potential** (`pot_case_le`). The step `main_step_sharp` is
  used with the sub-solver's cost `C x o = 1 + (potO Q 2 x o + Q)`; the `1` is the recursive
  call's own charge. Its work is at most `Q` (`mainWorkS_le_QQP`), and its factor plus counted
  calls at most `Q` (`caseFAB_le_QQP`). Each case goes to the inequality of
  `GraphIso.Recursion.PotOffset` that its children's predicate names, with the offset
  `R = Q + 1 ≤ 2Q`:
  - **the chain rule** (no hint): `pot_chain_off`;
  - **M0** (no hint, base `2|W| + 1`), **M1**, **M2a**, and **M2b and M3 on a base of one
    point** (factor at most `1`): `pot_free_off`;
  - **M2b, M3, M4 and M5 on a base of at least two points**: `pot_step_off`, for the children
    and the counted calls together (windows of `|W|/k` and `|W|/2` points, without a hint). The
    branching factor is `F + a + b ≤ Q ≤ Q²`, and there are at most `(F + a + b)(|W| + 1) ≤ Q³`
    entries.
  - **The base case** has no children and no counted calls.
  - **An empty window**: no children (every child's window is nonempty and within the parent's),
    and the counted calls of M5 vanish (`caseA` and `caseB` are `0` at `|W| = 0`).

  A valid hint has a base of at least one point (`HInstValid.base_pos`).
* **The induction** (`main_pot`), by strong induction on the rank `miniRk (2n₀)` as `main_spec`.
  Every valid instance of `MiniDom n₀ n₀ (2n₀)` with `LabInv` gets a correct answer with at most
  `(2n₀)²` generators, within `potO Q 2 |W| bo + Q`.
* **The headline** (`mainSolve_qp`). Every valid plain instance of degree `N` gets a correct
  answer from `mainEntry (thrQP C C')` within
  `genCost N |gs| + 2 + 15 + potO (QQP C C' N) 2 |W| none + QQP C C' N`. The corollary
  `mainSolve_qp_closed` (through `pot0_le`) bounds it by
  `genCost N |gs| + 17 + (2N + 2) N² Q^{2 (5 λ(N) + 9 + 4 (λ(N) + 6)²)} + Q`, i.e.
  `Q^{O(log² N)}`.

`QPHyp` is not shown satisfiable (`GraphIso.Main.PotThr`). **Historical:** milestones 15 and 16
were to supply `K` and `T` with these growth bounds; milestone 16 gives only a quadratic `T`, and
the unconditional theorems use the generalized `QPHypJ` (`main_potJ` in `GraphIso/Main/QPJ.lean`,
`qpHypJ_final`). The closed bound on `Q` is stage 14j-6c-2's.
-/

@[expose] public section

namespace GraphIso.Main

open Equiv Cost GraphIso GraphIso.Programs GraphIso.Toolkit GraphIso.Recursion GraphIso.Certificates
  Sims

/-! ### The cost of a step within the potential -/

section Arith

/-- The potential without a hint is monotone in the window. -/
theorem potO_none_mono {Q b x y : ℕ} (hQ : 1 ≤ Q) (h : x ≤ y) :
    potO Q b x none ≤ potO Q b y none := by
  simp only [potO, Recursion.pot]
  have hk := kap_mono (show 2 * x + 1 ≤ 2 * y + 1 by omega)
  have hl := Nat.pow_le_pow_left (Nat.add_le_add_right (lam_mono h) 6) 2
  exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_left h 2) (by omega))
    (Nat.pow_le_pow_right hQ (Nat.mul_le_mul_left b (by omega)))

/-- The recursive call's cost: `1 + (potO + Q) = potO + (Q + 1)`. -/
theorem sum_one_add {Q : ℕ} (ch : List (ℕ × Option ℕ)) :
    (ch.map fun x => 1 + (potO Q 2 x.1 x.2 + Q)).sum =
      (ch.map fun x => potO Q 2 x.1 x.2 + (Q + 1)).sum := by
  congr 1
  exact List.map_congr_left fun _ _ => by omega

/-- The counted calls as entries of the children's list. -/
theorem sum_counted (f : ℕ → Option ℕ → ℕ) (ch : List (ℕ × Option ℕ)) (a b q r : ℕ) :
    (ch.map fun x => f x.1 x.2).sum + a * f q none + b * f r none =
      ((ch ++ List.replicate a (q, none) ++ List.replicate b (r, none)).map
        fun x : ℕ × Option ℕ => f x.1 x.2).sum := by
  simp only [List.map_append, List.sum_append, List.map_replicate, List.sum_replicate,
    smul_eq_mul]

/-- **A step without branching**: children with `FreeChild`, a factor at most `1`, no counted
calls, and work at most `Q`. -/
theorem pot_free_case {Q p m F W : ℕ} {ch : List (ℕ × Option ℕ)} (hp : 1 ≤ p)
    (hpQ : p + 2 ≤ Q) (hW : W ≤ Q) (hF : F ≤ 1) (hch : ChildList p F (FreeChild p m) ch) :
    (ch.map fun x => 1 + (potO Q 2 x.1 x.2 + Q)).sum + W ≤ Recursion.pot Q 2 p m + Q := by
  rw [sum_one_add]
  refine pot_free_off le_rfl hp hpQ ch (hch.sum_le.trans (by nlinarith)) (fun x hx => ?_)
    hch.pos (by omega) hW
  exact (hch.pred x hx).2

/-- **A step with branching**: children with `StepChild` on a base of at least two points,
counted calls on windows of `|W|/k` and `|W|/2` points (`k ≥ 2`), the factor plus the counted
calls at most `Q`, and work at most `Q`. -/
theorem pot_step_case {Q p m k F a b W : ℕ} {ch : List (ℕ × Option ℕ)} (hp : 1 ≤ p)
    (hm : 2 ≤ m) (hk : 2 ≤ k) (hpQ : p + 2 ≤ Q) (hW : W ≤ Q) (hFab : F + a + b ≤ Q)
    (hch : ChildList p F (StepChild p m) ch) :
    (ch.map fun x => 1 + (potO Q 2 x.1 x.2 + Q)).sum + a * (1 + (potO Q 2 (p / k) none + Q)) +
      b * (1 + (potO Q 2 (p / 2) none + Q)) + W ≤ Recursion.pot Q 2 p m + Q := by
  rw [sum_counted (fun x o => 1 + (potO Q 2 x o + Q)), sum_one_add]
  have hQ1 : 1 ≤ Q := by omega
  have hc : F + a + b ≤ Q ^ 2 := hFab.trans (Nat.le_self_pow (by norm_num) Q)
  have hpk : p / k ≤ p / 2 := Nat.div_le_div_left hk (by norm_num)
  have h2 : 2 * (p / 2) ≤ p := Nat.mul_div_le p 2
  refine pot_step_off le_rfl hp hm hpQ hc _ ?_ ?_ ?_ (by omega) hW
  · simp only [List.map_append, List.sum_append, List.map_replicate, List.sum_replicate,
      smul_eq_mul]
    have h1 := hch.sum_le
    have hka : a * (p / k) ≤ a * p := Nat.mul_le_mul_left a (Nat.div_le_self p k)
    have hkb : b * (p / 2) ≤ b * p := Nat.mul_le_mul_left b (Nat.div_le_self p 2)
    have e : (F + a + b) * p = F * p + a * p + b * p := by ring
    omega
  · intro x hx
    simp only [List.mem_append, List.mem_replicate] at hx
    rcases hx with (hx | ⟨-, rfl⟩) | ⟨-, rfl⟩
    · exact hch.pred x hx
    · exact ⟨Nat.div_le_self p k, Or.inr ⟨rfl, by omega⟩⟩
    · exact ⟨Nat.div_le_self p 2, Or.inr ⟨rfl, h2⟩⟩
  · simp only [List.length_append, List.length_replicate]
    have hl := hch.length_le
    have hq : (F + a + b) * (p + 1) ≤ Q * Q := Nat.mul_le_mul hFab (by omega)
    have e : (F + a + b) * (p + 1) = F * p + a * p + b * p + (F + a + b) := by ring
    have e3 : Q * Q ≤ Q ^ 3 := by
      rw [pow_succ, sq]
      exact Nat.le_mul_of_pos_right _ (by omega)
    nlinarith

/-- **The chain rule**: no hint, children without a hint on proper parts of the window, a
factor at most `1`, and work at most `Q`. -/
theorem pot_chain_case {Q p F W : ℕ} {ch : List (ℕ × Option ℕ)} (hpQ : p + 2 ≤ Q) (hW : W ≤ Q)
    (hF : F ≤ 1) (hch : ChildList p F (ChainChild p) ch) :
    (ch.map fun x => 1 + (potO Q 2 x.1 x.2 + Q)).sum + W ≤ potO Q 2 p none + Q := by
  rw [sum_one_add]
  exact pot_chain_off (by norm_num) (by omega) ch (hch.sum_le.trans (by nlinarith))
    (fun x hx => hch.pred x hx) hch.pos (by omega) hW

/-- A child list on an empty window is empty. -/
theorem ChildList.eq_nil_of_zero {F : ℕ} {pred : ℕ × Option ℕ → Prop} {ch : List (ℕ × Option ℕ)}
    (h : ChildList 0 F pred ch) : ch = [] := by
  have := h.length_le
  rw [Nat.mul_zero, Nat.le_zero, List.length_eq_zero_iff] at this
  exact this

/-- **The cost of a step within the potential**, from the data `main_step_sharp` gives: the
case `c`, the base `bo` (`some m` with a hint), the children, the factor `F`, the counted calls
`a`, `b`, and the work `W`. -/
theorem pot_case_le {Q p k m F a b W : ℕ} {c : MainCase} {bo : Option ℕ}
    {ch : List (ℕ × Option ℕ)} (hk : 2 ≤ k) (hpQ : p + 2 ≤ Q) (hW : W ≤ Q)
    (hFab : F + a + b ≤ Q) (hch : ChildList p F (casePred c p m) ch)
    (hnone : bo = none → c = .base ∨ c = .chain ∨ c = .m0)
    (hsome : ∀ m', bo = some m' → m' = m ∧ 1 ≤ m ∧ c ≠ .chain ∧ c ≠ .m0)
    (hab : c ≠ .m5 → a = 0 ∧ b = 0) (hF0 : c = .base → F = 0)
    (hF1 : c = .chain ∨ c = .m0 ∨ c = .m1 ∨ c = .m2a → F ≤ 1)
    (hm1 : m ≤ 1 → c ≠ .m4 ∧ c ≠ .m5 ∧ F ≤ 1) (hp0 : p = 0 → a = 0 ∧ b = 0) :
    (ch.map fun x => 1 + (potO Q 2 x.1 x.2 + Q)).sum + a * (1 + (potO Q 2 (p / k) none + Q)) +
      b * (1 + (potO Q 2 (p / 2) none + Q)) + W ≤ potO Q 2 p bo + Q := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · obtain ⟨rfl, rfl⟩ := hp0 rfl
    rw [hch.eq_nil_of_zero]
    simp only [List.map_nil, List.sum_nil]
    omega
  -- the cases without branching have no counted calls
  have hfree : ∀ {m'}, c ≠ .m5 → ChildList p F (FreeChild p m') ch → F ≤ 1 →
      (ch.map fun x => 1 + (potO Q 2 x.1 x.2 + Q)).sum + a * (1 + (potO Q 2 (p / k) none + Q)) +
        b * (1 + (potO Q 2 (p / 2) none + Q)) + W ≤ Recursion.pot Q 2 p m' + Q := by
    intro m' h5 hc hF
    obtain ⟨rfl, rfl⟩ := hab h5
    simpa using pot_free_case hp hpQ hW hF hc
  rcases bo with _ | m'
  · rcases hnone rfl with rfl | rfl | rfl
    · obtain ⟨rfl, rfl⟩ := hab (by decide)
      have hF := hF0 rfl
      subst hF
      have : ch = [] := List.eq_nil_iff_forall_not_mem.2 fun x hx => by
        have := hch.length_le
        rw [Nat.zero_mul, Nat.le_zero, List.length_eq_zero_iff] at this
        simp [this] at hx
      subst this
      simp only [List.map_nil, List.sum_nil]
      omega
    · obtain ⟨rfl, rfl⟩ := hab (by decide)
      simpa using pot_chain_case hpQ hW (hF1 (Or.inl rfl)) hch
    · exact hfree (m' := 2 * p + 1) (by decide) hch (hF1 (Or.inr (Or.inl rfl)))
  · obtain ⟨rfl, hm1', hc1, hc2⟩ := hsome m' rfl
    change _ ≤ Recursion.pot Q 2 p m' + Q
    rcases Nat.lt_or_ge m' 2 with hlt | hge
    · obtain ⟨h4, h5, hF⟩ := hm1 (by omega)
      have hfc : ChildList p F (FreeChild p m') ch := by
        refine ⟨hch.sum_le, fun x hx => ?_, hch.pos⟩
        have hx' := hch.pred x hx
        cases c
        all_goals first
          | exact absurd rfl hc1 | exact absurd rfl hc2 | exact absurd rfl h4
          | exact absurd rfl h5 | exact hx'
          | obtain ⟨hxp, ⟨m'', he, h43⟩ | hd⟩ := hx'
            · exact ⟨hxp, Or.inl ⟨m'', he, by omega, Or.inl (by omega)⟩⟩
            · exact ⟨hxp, Or.inr hd⟩
      exact hfree h5 hfc hF
    · cases c
      case chain => exact absurd rfl hc1
      case m0 => exact absurd rfl hc2
      case m1 => exact hfree (by decide) hch (hF1 (Or.inr (Or.inr (Or.inl rfl))))
      case m2a => exact hfree (by decide) hch (hF1 (Or.inr (Or.inr (Or.inr rfl))))
      all_goals exact pot_step_case hp hge hk hpQ hW hFab hch

end Arith

/-! ### The induction -/

section Induction

variable {K T : ℕ → ℕ} {C C' n₀ : ℕ}

/-- **The induction hypothesis** below rank `r`: the potential bound on the domain with `LabInv`. -/
def PotIH (thr : ThrProg Ty.unit) (Q n₀ r : ℕ) : Prop :=
  ∀ J : HInstData Ty.unit, HInstValid ssDV J → MiniDom n₀ n₀ (2 * n₀) J → LabInv J →
    miniRk (2 * n₀) J.winSize J.baseOpt < r →
    ∃ ans : AnswerData Ty.unit,
      RunsWithin ssCtx (mainBody thr Ty.denote) (mainBody thr Ty.denote J) ans
        (potO Q 2 J.winSize J.baseOpt + Q) ∧
      J.inst.OK ssDV ans ∧
        ∀ c : CosetData Ty.unit, ans = some c → c.2.gens.length ≤ 2 * n₀ * (2 * n₀)

/-- The sub-solver hypothesis from the induction hypothesis, with the recursive call's charge. -/
theorem pot_sub_of_ih {thr : ThrProg Ty.unit} {Q : ℕ} {I : HInstData Ty.unit}
    (ih : PotIH thr Q n₀ (miniRk (2 * n₀) I.winSize I.baseOpt)) :
    MainSubL thr n₀ n₀ (2 * n₀) I (fun p bo => 1 + (potO Q 2 p bo + Q)) := by
  intro J hJ ⟨hdJ, hLJ, hlt⟩
  rw [hmeasure_eq, hmeasure_eq] at hlt
  obtain ⟨ans, hrun, hok, hg⟩ := ih J hJ hdJ hLJ (miniRk_lt hlt (dom_base_le le_rfl hJ hdJ))
  exact ⟨ans, RunsWithin.recur hrun, hok, hg⟩

theorem caseA_zero_win (c : MainCase) (n N k : ℕ) : caseA c n N 0 k = 0 := by
  cases c <;> simp [caseA, certCount, c3Count]

theorem caseB_zero_win (c : MainCase) (s : ℕ) : caseB c 0 s = 0 := by
  cases c <;> simp [caseB]

/-- **One step of the induction**: the procedure on `I` within the potential, from the induction
hypothesis below its rank. -/
theorem pot_ind_step (hQ : QPHyp K T C C') {I : HInstData Ty.unit} (hI : HInstValid ssDV I)
    (hd : MiniDom n₀ n₀ (2 * n₀) I) (hIL : LabInv I)
    (ih : PotIH (thrQP C C') (QQP C C' n₀) n₀ (miniRk (2 * n₀) I.winSize I.baseOpt)) :
    ∃ ans : AnswerData Ty.unit,
      RunsWithin ssCtx (mainBody (thrQP C C') Ty.denote) (mainBody (thrQP C C') Ty.denote I) ans
        (potO (QQP C C' n₀) 2 I.winSize I.baseOpt + QQP C C' n₀) ∧
      I.inst.OK ssDV ans ∧
        ∀ c : CosetData Ty.unit, ans = some c → c.2.gens.length ≤ 2 * n₀ * (2 * n₀) := by
  have hQ1 : 1 ≤ QQP C C' n₀ := by unfold QQP; omega
  have hC : ∀ a b, a ≤ b → 1 + (potO (QQP C C' n₀) 2 a none + QQP C C' n₀) ≤
      1 + (potO (QQP C C' n₀) 2 b none + QQP C C' n₀) := fun a b hab => by
    have := potO_none_mono (b := 2) hQ1 hab
    omega
  obtain ⟨-, ans, ch, F, a, b, hrun, hok, hg, hch, hF, ha, hb⟩ :=
    main_step_sharp (thrQP_spec C C') le_rfl hI hd hIL hC (pot_sub_of_ih ih) (sharpHyp_qp hQ n₀)
  refine ⟨ans, hrun.mono ?_, hok, hg⟩
  have hW := mainWorkS_le_QQP hQ hI hd hIL
  have hFab := caseFAB_le_QQP hQ hI hd hIL
  have hwQ := winSize_add_two_le_QQP (C := C) (C' := C') hI hd
  obtain ⟨⟨xy, w, σd, N, gs, d⟩, n₀', n, lab⟩ := I
  cases d
  obtain rfl : n₀' = n₀ := hd.n₀
  have hk : 2 ≤ kQP C n₀' := by have := five_le_kQP C n₀'; omega
  change (ch.map fun x => 1 + (potO (QQP C C' n₀') 2 x.1 x.2 + QQP C C' n₀')).sum +
      a * (1 + (potO (QQP C C' n₀') 2 (w.1.length / kQP C n₀') none + QQP C C' n₀')) +
      b * (1 + (potO (QQP C C' n₀') 2 (w.1.length / 2) none + QQP C C' n₀')) +
      mainWorkS (kQP C) (ℓQP C C') (cTQP C) T (2 * n₀' * (2 * n₀'))
        (((xy, w, σd, N, gs, ()), n₀', n, lab) : HInstData Ty.unit) ≤
    potO (QQP C C' n₀') 2 w.1.length (lab.map fun _ => N - n) + QQP C C' n₀'
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
        HInstData Ty.unit)) w.1.length (sGQ n₀') ≤ QQP C C' n₀' at hFab
  change w.1.length + 2 ≤ QQP C C' n₀' at hwQ
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
  have hS := sharpHyp_qp hQ n₀'
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

/-- **The potential bound** (`PLAN-14.md` §14.13 item 5). Under `QPHyp K T C C'`, every valid
instance of `MiniDom n₀ n₀ (2n₀)` with the label invariant gets a correct answer from
`mainBody (thrQP C C')`, with at most `(2n₀)²` generators, within `potO Q 2 |W| bo + Q` for
`Q = QQP C C' n₀`. -/
theorem main_pot (hQ : QPHyp K T C C') (I : HInstData Ty.unit) (hI : HInstValid ssDV I)
    (hd : MiniDom n₀ n₀ (2 * n₀) I) (hIL : LabInv I) :
    ∃ ans : AnswerData Ty.unit,
      RunsWithin ssCtx (mainBody (thrQP C C') Ty.denote) (mainBody (thrQP C C') Ty.denote I) ans
        (potO (QQP C C' n₀) 2 I.winSize I.baseOpt + QQP C C' n₀) ∧
      I.inst.OK ssDV ans ∧
        ∀ c : CosetData Ty.unit, ans = some c → c.2.gens.length ≤ 2 * n₀ * (2 * n₀) := by
  suffices h : ∀ r, PotIH (thrQP C C') (QQP C C' n₀) n₀ r from
    h _ I hI hd hIL (Nat.lt_succ_self _)
  intro r
  induction r with
  | zero => exact fun J _ _ _ h => absurd h (Nat.not_lt_zero _)
  | succ r ih =>
    intro J hJ hdJ hLJ hr
    rcases Nat.lt_succ_iff_lt_or_eq.1 hr with hlt | heq
    · exact ih J hJ hdJ hLJ hlt
    · rw [← heq] at ih
      exact pot_ind_step hQ hJ hdJ hLJ ih

end Induction

/-! ### The headline -/

section Headline

variable {K T : ℕ → ℕ} {C C' : ℕ}

/-- **The full procedure within the potential** (`PLAN-14.md` §14.13 item 6). Under
`QPHyp K T C C'`, for every valid instance, the entry at the thresholds `thrQP C C'` generates
the group and recurses on the instance without a hint (`n₀ = n = N`, in the domain `nB = N`,
`NB = 2N`, which has the label invariant: `LabInv.entry`). The answer is correct, within
`genCost N |gs| + 2 + 15 + potO Q 2 |W| none + Q` for `Q = QQP C C' N`. -/
theorem mainSolve_qp (hQ : QPHyp K T C C') {xy : StrData × StrData} {w : WinData}
    {σd : PermData} {N : ℕ} {gs : GensData}
    (hw : w.Valid N) (hσ : σd.Valid N) (hgs : GensData.AllValid N gs)
    (hinv : IsInvariant (GensData.denote N gs) (w.denote N)) :
    ∃ ans : AnswerData Ty.unit,
      RunsWithin ssCtx (mainBody (thrQP C C') Ty.denote)
        (mainEntry Ty.unit Ty.denote (xy, w, σd, N, gs)) ans
        (genCost N gs.length + 2 + 15 +
          (potO (QQP C C' N) 2 w.1.length none + QQP C C' N)) ∧
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
  obtain ⟨ans, hrun, hok, -⟩ := main_pot hQ _ hI hd (LabInv.entry _ N)
  replace hrun : RunsWithin ssCtx (mainBody (thrQP C C') Ty.denote)
      (mainBody (thrQP C C') Ty.denote
        (((xy, w, σd, N, generateModel N gs, ()), N, N, none) : HInstData Ty.unit)) ans
      (potO (QQP C C' N) 2 w.1.length none + QQP C C' N) := hrun
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

/-- **The headline in closed form in `Q`**: through `pot0_le`, the cost of `mainSolve_qp` is at
most `genCost N |gs| + 17 + (2N + 2) N² Q^{2 (5 λ(N) + 9 + 4 (λ(N) + 6)²)} + Q` with
`Q = QQP C C' N`, i.e. `Q^{O(log² N)}`. -/
theorem mainSolve_qp_closed (hQ : QPHyp K T C C') {xy : StrData × StrData} {w : WinData}
    {σd : PermData} {N : ℕ} {gs : GensData}
    (hw : w.Valid N) (hσ : σd.Valid N) (hgs : GensData.AllValid N gs)
    (hinv : IsInvariant (GensData.denote N gs) (w.denote N)) :
    ∃ ans : AnswerData Ty.unit,
      RunsWithin ssCtx (mainBody (thrQP C C') Ty.denote)
        (mainEntry Ty.unit Ty.denote (xy, w, σd, N, gs)) ans
        (genCost N gs.length + 17 +
          (2 * N + 2) * N ^ 2 *
            QQP C C' N ^ (2 * (5 * lam N + 9 + 4 * (lam N + 6) ^ 2)) + QQP C C' N) ∧
      AnsOK ssDV N (w.denote N) (σd.denote N) (gs.denote N) (xy.1.denote N) (xy.2.denote N)
        ans := by
  obtain ⟨ans, hrun, hok⟩ := mainSolve_qp hQ (xy := xy) hw hσ hgs hinv
  refine ⟨ans, hrun.mono ?_, hok⟩
  have hwN : w.1.length ≤ N := mf_length_le_of_nodup hw.nodup hw.lt
  have hQ1 : 1 ≤ QQP C C' N := by unfold QQP; omega
  have h1 := potO_none_mono (b := 2) hQ1 hwN
  have h2 := pot0_le (QQP C C' N) 2 N
  omega

end Headline

end GraphIso.Main
