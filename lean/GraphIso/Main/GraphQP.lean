module

public import GraphIso.Main.GraphEntryProg
public import GraphIso.Main.QPBound
public import GraphIso.Solver.Sims

/-!
# The graph-isomorphism entry: the theorems

Stage 14j-6c-3, items 4–6 (`PLAN-14.md` §14.15).

* **The generator count** (item 4). `mainSolve_ss` and `mainSolve_qp` drop the bound of the
  recursion on the answer's generators (`main_spec`, `main_pot`: at most `(2N)²`). The variants
  `mainSolve_ss_gens`, `mainSolve_qp_gens` and `mainSolve_qp_exp_gens` keep it; their proofs are
  those of the protected theorems, through `mainEntry_of_body` and `entry_hinst`.
* **The closed solver** `mainSolver thr`: the procedure `mainBody thr` with the Schreier–Sims
  implementations substituted, over the empty signature (no oracle). `qpSolver C C'` is it at
  the thresholds `thrQP C C'`.
* **`giSolve_ss`** (item 5): for every threshold program with `ThrSpec`, with no growth
  hypothesis, on valid graph data of any degree, the closed entry returns a `GICosetOK` result,
  within `giCostSS cT n` (the recursion's bound `mainCost`, exponential in general).
* **`giSolve_qp_exp`** and **`gi_qp_simpleGraph`** (item 6): for all `C`, `C'` there is `c`
  such that under `QPHyp K T C C'` the closed entry at `thrQP C C'` returns a `GICosetOK` result
  with local cost at most `2^{c (λ(n) + 1)⁸}`, on valid graph data on `n` points and on simple
  graphs on `Fin n` (`none` exactly when `IsEmpty (G ≃g H)`, and otherwise a coset equal to the
  set of the permutations underlying the isomorphisms `G ≃g H`).

`giSolve_ss` does not depend on `QPHyp`. **Historical:** when this stage was done, `QPHyp` was to
be shown satisfiable by milestones 15 (`K`) and 16 (`T` with `T m ≤ C' (λ(m) + 1)`). Milestone 15
gives `K` (`altQuotientIso_pyber`), but milestone 16 gives only the quadratic
`Tq m = 256 (λ(m) + 1)²` (`transitivityBound_quad`), for which `QPHyp` fails (`not_qpHyp_Tq`,
`GraphIsoChecks/WielandtFinal.lean`). The unconditional theorems come from the generalized
hypothesis `QPHypJ` instead: `qpHypJ_final`, `mainSolve_final`, `giSolve_final` and
`gi_simpleGraph_final` (`GraphIso/Wielandt/Final.lean`). `QPHyp` itself is not shown
satisfiable.
-/

@[expose] public section

namespace GraphIso.Main

open Equiv Pointwise Cost GraphIso GraphIso.Graph GraphIso.Recursion Sims

/-! ### The main entry with the generator count -/

section Gens

variable {thr : ThrProg Ty.unit} {xy : StrData × StrData} {w : WinData} {σd : PermData} {N : ℕ}
  {gs : GensData}

/-- The plain instance of the entry: generated group, no hint, `n₀ = n = N`. -/
abbrev entryI (xy : StrData × StrData) (w : WinData) (σd : PermData) (N : ℕ) (gs : GensData) :
    HInstData Ty.unit :=
  ((xy, w, σd, N, generateModel N gs, ()), N, N, none)

/-- The plain instance is valid, in the domain `nB = N`, `NB = 2N`, and its group is the input
group. -/
theorem entry_hinst (hw : w.Valid N) (hσ : σd.Valid N) (hgs : GensData.AllValid N gs)
    (hinv : IsInvariant (GensData.denote N gs) (w.denote N)) :
    HInstValid ssDV (entryI xy w σd N gs) ∧ MiniDom N N (2 * N) (entryI xy w σd N gs) ∧
      GensData.denote N (generateModel N gs) = GensData.denote N gs := by
  obtain ⟨hgv, hden, hlen⟩ := generateModel_spec hgs
  refine ⟨?_, ⟨rfl, le_rfl, by change N ≤ 2 * N; omega,
    hlen.trans (Nat.mul_le_mul (by omega) (by omega))⟩, hden⟩
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

/-- The answer of the plain instance answers the input. -/
theorem entry_ok (hgs : GensData.AllValid N gs) {ans : AnswerData Ty.unit}
    (hok : (entryI xy w σd N gs).inst.OK ssDV ans) :
    AnsOK ssDV N (w.denote N) (σd.denote N) (gs.denote N) (xy.1.denote N) (xy.2.denote N) ans := by
  obtain ⟨-, hden, -⟩ := generateModel_spec hgs
  change InstData.OK (D := Ty.unit) (xy, w, σd, N, generateModel N gs, ()) ssDV ans at hok
  unfold InstData.OK at hok
  change AnsOK ssDV N (w.denote N) (σd.denote N) (GensData.denote N (generateModel N gs))
    (xy.1.denote N) (xy.2.denote N) ans at hok
  rw [hden] at hok
  exact hok

/-- **The entry from a run of the body on the plain instance**: one charged `generate` and
`17` local steps. -/
theorem mainEntry_of_body (hgs : GensData.AllValid N gs) {ans : AnswerData Ty.unit} {c : ℕ}
    (hrun : RunsWithin ssCtx (mainBody thr Ty.denote)
      (mainBody thr Ty.denote (entryI xy w σd N gs)) ans c) :
    RunsWithin ssCtx (mainBody thr Ty.denote) (mainEntry Ty.unit Ty.denote (xy, w, σd, N, gs))
      ans (genCost N gs.length + 2 + 15 + c) := by
  have hG : ssCtx.O.run GroupOp.generate (N, gs) = (N, generateModel N gs, ()) := rfl
  apply RunsWithin.mono
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

/-- **`mainSolve_ss` with the generator count**: at most `(2N)²` generators. -/
theorem mainSolve_ss_gens {kf ℓf cT : ℕ → ℕ} (hT : ThrSpec thr kf ℓf cT)
    (hw : w.Valid N) (hσ : σd.Valid N) (hgs : GensData.AllValid N gs)
    (hinv : IsInvariant (GensData.denote N gs) (w.denote N)) :
    ∃ ans : AnswerData Ty.unit,
      RunsWithin ssCtx (mainBody thr Ty.denote)
        (mainEntry Ty.unit Ty.denote (xy, w, σd, N, gs)) ans
        (genCost N gs.length + 2 + 15 +
          mainCost (cT N) N (2 * N) (miniRk (2 * N) w.1.length none)) ∧
      AnsOK ssDV N (w.denote N) (σd.denote N) (gs.denote N) (xy.1.denote N) (xy.2.denote N)
        ans ∧
      ∀ c : CosetData Ty.unit, ans = some c → c.2.gens.length ≤ 2 * N * (2 * N) := by
  obtain ⟨hI, hd, -⟩ := entry_hinst (xy := xy) hw hσ hgs hinv
  obtain ⟨ans, hrun, hok, hg⟩ := main_spec hT le_rfl _ hI hd
  exact ⟨ans, mainEntry_of_body hgs hrun, entry_ok hgs hok, hg⟩

variable {K T : ℕ → ℕ} {C C' : ℕ}

/-- **`mainSolve_qp` with the generator count**: at most `(2N)²` generators. -/
theorem mainSolve_qp_gens (hQ : QPHyp K T C C') (hw : w.Valid N) (hσ : σd.Valid N)
    (hgs : GensData.AllValid N gs) (hinv : IsInvariant (GensData.denote N gs) (w.denote N)) :
    ∃ ans : AnswerData Ty.unit,
      RunsWithin ssCtx (mainBody (thrQP C C') Ty.denote)
        (mainEntry Ty.unit Ty.denote (xy, w, σd, N, gs)) ans
        (genCost N gs.length + 2 + 15 +
          (potO (QQP C C' N) 2 w.1.length none + QQP C C' N)) ∧
      AnsOK ssDV N (w.denote N) (σd.denote N) (gs.denote N) (xy.1.denote N) (xy.2.denote N)
        ans ∧
      ∀ c : CosetData Ty.unit, ans = some c → c.2.gens.length ≤ 2 * N * (2 * N) := by
  obtain ⟨hI, hd, -⟩ := entry_hinst (xy := xy) hw hσ hgs hinv
  obtain ⟨ans, hrun, hok, hg⟩ := main_pot hQ _ hI hd (LabInv.entry _ N)
  exact ⟨ans, mainEntry_of_body hgs hrun, entry_ok hgs hok, hg⟩

/-- **`mainSolve_qp_exp` with the generator count.** -/
theorem mainSolve_qp_exp_gens (C C' : ℕ) :
    ∃ c, ∀ {K T : ℕ → ℕ}, QPHyp K T C C' →
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
  obtain ⟨c₀, hc₀⟩ := QQP_le_exp C C'
  refine ⟨306 * c₀ + 7, fun hQ xy w σd N gs hw hσ hgs hinv => ?_⟩
  obtain ⟨ans, hrun, hok, hg⟩ := mainSolve_qp_gens hQ (xy := xy) hw hσ hgs hinv
  refine ⟨ans, hrun.mono ?_, hok, hg⟩
  have hwN : w.1.length ≤ N := mf_length_le_of_nodup hw.nodup hw.lt
  have hQ1 : 1 ≤ QQP C C' N := by unfold QQP; omega
  have h1 := potO_none_mono (b := 2) hQ1 hwN
  have h2 := pot0_le (QQP C C' N) 2 N
  have := qp_closed_le (hc₀ N)
  omega

end Gens

/-! ### The closed solver -/

/-- **The closed solver**: the procedure with the Schreier–Sims implementations substituted, a
program over the empty signature. -/
def mainSolver (thr : ThrProg Ty.unit) (hthr : ThrWf thr) :
    WfProc Signature.empty (hinstTy Ty.unit) (Ty.answer Ty.unit) :=
  WfProc.subst ⟨mainBody thr, mainBody_wf hthr⟩ ⟨ssImpl, ssImpl_wf⟩

/-- The closed solver at the thresholds `thrQP C C'`. -/
def qpSolver (C C' : ℕ) : WfProc Signature.empty (hinstTy Ty.unit) (Ty.answer Ty.unit) :=
  mainSolver (thrQP C C') (thrQP_spec C C').wf

/-! ### Correctness on every valid input -/

section Correct

variable {Δ n : ℕ} {X Y : GraphData}

/-- The cost of the closed entry at a threshold program with cost `cT`. -/
def giCostSS (cT : ℕ → ℕ) (n : ℕ) : ℕ :=
  encCost n + (genCost (gN n) (gensData n).length + 2 + 15 +
    mainCost (cT (gN n)) (gN n) (2 * gN n) (miniRk (2 * gN n) (gN n) none)) +
    decCost n (2 * gN n * (2 * gN n))

/-- The encoded instance is valid. -/
theorem giInst_valid (n : ℕ) :
    (WinData.ofPoints (gN n) (List.range (gN n))).Valid (gN n) ∧
      (PermData.one (gN n)).Valid (gN n) ∧ GensData.AllValid (gN n) (gensData n) ∧
      IsInvariant (GensData.denote (gN n) (gensData n))
        ((WinData.ofPoints (gN n) (List.range (gN n))).denote (gN n)) := by
  refine ⟨WinData.valid_univ _, PermData.valid_one _, gensData_valid n, ?_⟩
  rw [WinData.denote_univ]
  exact fun _ _ _ _ => Set.mem_univ _

/-- A run of the entry, closed by substitution. -/
theorem gi_close {thr : ThrProg Ty.unit} (hthr : ThrWf thr) {r : Option (PermData × GensData)}
    {c : ℕ} (h : RunsWithin ssCtx (mainBody thr Ty.denote) (giEntry Ty.unit Ty.denote (n, X, Y))
      r c) :
    ∃ tr : Trace Signature.empty,
      Runs Ctx.empty.O ((mainSolver thr hthr).proc Ty.denote)
        ((giEntry Ty.unit Ty.denote (n, X, Y)).subst ssImpl) r tr ∧ Trace.localCost tr ≤ c := by
  obtain ⟨tr, hr, hc, hpre⟩ := h
  obtain ⟨tr', hr', hc'⟩ := Runs.subst ssImpl_implements hr hpre
  refine ⟨tr', hr', ?_⟩
  rw [Trace.cost_empty] at hc'
  exact hc'.trans hc

/-- **Graph isomorphism, correct on every valid input** (`PLAN-14.md` §14.15 item 5). For every
threshold program with `ThrSpec`, with no growth hypothesis: for valid graph data `X`, `Y` on `n`
points (of any degree), the closed entry (Schreier–Sims substituted, no oracle) returns `r` with
`GICosetOK n X Y r`: `none` exactly when there is no isomorphism, and otherwise valid data of a
coset, with at most `(2N)²` generators, equal to the set of isomorphisms. Its local cost is at
most `giCostSS cT n`. -/
theorem giSolve_ss {thr : ThrProg Ty.unit} {kf ℓf cT : ℕ → ℕ} (hT : ThrSpec thr kf ℓf cT)
    (hX : X.ValidD Δ n) (hY : Y.ValidD Δ n) :
    ∃ (r : Option (PermData × GensData)) (tr : Trace Signature.empty),
      Runs Ctx.empty.O ((mainSolver thr hT.wf).proc Ty.denote)
        ((giEntry Ty.unit Ty.denote (n, X, Y)).subst ssImpl) r tr ∧
      Trace.localCost tr ≤ giCostSS cT n ∧ GICosetOK n X Y r := by
  obtain ⟨hw, hσ, hgs, hinv⟩ := giInst_valid n
  have hmain := mainSolve_ss_gens (xy := (gStr n X, gStr n Y)) hT hw hσ hgs hinv
  simp only [WinData.ofPoints_fst, List.length_range] at hmain
  obtain ⟨r, hrun, hok⟩ := giEntry_runs (thr := thr) hX hY hmain
  obtain ⟨tr, hr, hc⟩ := gi_close hT.wf hrun
  exact ⟨r, tr, hr, hc, hok⟩

end Correct

/-! ### The headline -/

section Headline

theorem lam_gN_le (n : ℕ) : lam (gN n) + 1 ≤ 2 * (lam n + 1) := by
  have hn : n < 2 ^ (lam n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  rcases Nat.eq_zero_or_pos (gN n) with h0 | hpos
  · rw [h0]
    simp only [lam, Nat.log_zero_right]
    omega
  · have hlt : gN n < 2 ^ (2 * (lam n + 1)) := by
      have h1 : n + 1 ≤ 2 ^ (lam n + 1) := hn
      calc gN n = n * (n + 1) := by unfold gN; ring
        _ < 2 ^ (lam n + 1) * 2 ^ (lam n + 1) :=
          Nat.mul_lt_mul_of_lt_of_le hn h1 (by omega)
        _ = 2 ^ (2 * (lam n + 1)) := by rw [← pow_add]; ring_nf
    have h' : lam (gN n) < 2 * (lam n + 1) := Nat.log_lt_of_lt_pow (by omega) hlt
    omega

/-- The polynomial parts of the cost: the encoding, `generate` (on at most two generators) and
the decoding, at most `1000 (n + 1)¹²`. -/
theorem gi_poly_le (n : ℕ) :
    encCost n + genCost (gN n) (gensData n).length + 17 + decCost n (2 * gN n * (2 * gN n)) ≤
      1000 * (n + 1) ^ 12 := by
  set Z := n + 1 with hZ
  have hZ1 : 1 ≤ Z := by omega
  have hL : (gensData n).length ≤ 2 := by unfold gensData; split <;> simp
  have hN : gN n + 1 ≤ Z ^ 2 := by unfold gN; nlinarith
  have hg := genCost_le (gN n) (gensData n).length
  have h6 : (gN n + 1) ^ 6 ≤ Z ^ 12 := by
    calc (gN n + 1) ^ 6 ≤ (Z ^ 2) ^ 6 := Nat.pow_le_pow_left hN 6
      _ = Z ^ 12 := by rw [← pow_mul]
  have h2 : (gN n + 1) ^ 2 ≤ Z ^ 4 := by
    calc (gN n + 1) ^ 2 ≤ (Z ^ 2) ^ 2 := Nat.pow_le_pow_left hN 2
      _ = Z ^ 4 := by rw [← pow_mul]
  have p1 : Z ≤ Z ^ 12 := by
    calc Z = Z ^ 1 := (pow_one Z).symm
      _ ≤ Z ^ 12 := Nat.pow_le_pow_right hZ1 (by omega)
  have p2 : Z ^ 2 ≤ Z ^ 12 := Nat.pow_le_pow_right hZ1 (by omega)
  have p4 : Z ^ 4 ≤ Z ^ 12 := Nat.pow_le_pow_right hZ1 (by omega)
  have p5 : Z ^ 5 ≤ Z ^ 12 := Nat.pow_le_pow_right hZ1 (by omega)
  have hG : genCost (gN n) (gensData n).length ≤ 220 * Z ^ 12 := by
    have : 60 * (gensData n).length * (gN n + 1) ^ 2 ≤ 120 * Z ^ 12 := by
      calc 60 * (gensData n).length * (gN n + 1) ^ 2 ≤ 60 * 2 * Z ^ 4 :=
            Nat.mul_le_mul (Nat.mul_le_mul_left _ hL) h2
        _ ≤ 120 * Z ^ 12 := by omega
    omega
  have hE : encCost n ≤ 200 * Z ^ 2 := by
    unfold encCost offCost strCost gensCost vtxCost liftDataCost liftArrCost gN
    nlinarith
  have hD : decCost n (2 * gN n * (2 * gN n)) ≤ 70 * Z ^ 5 + 20 * Z := by
    unfold decCost
    have hs : 2 * gN n * (2 * gN n) + 1 ≤ 5 * Z ^ 4 := by
      have : gN n * gN n ≤ Z ^ 4 := by
        calc gN n * gN n ≤ Z ^ 2 * Z ^ 2 := Nat.mul_le_mul (by omega) (by omega)
          _ = Z ^ 4 := by ring
      nlinarith
    have h14 : 12 * n + 14 ≤ 14 * Z := by omega
    calc (2 * gN n * (2 * gN n) + 1) * (12 * n + 14) + 6 ≤ 5 * Z ^ 4 * (14 * Z) + 6 :=
          Nat.add_le_add_right (Nat.mul_le_mul hs h14) _
      _ = 70 * Z ^ 5 + 6 := by ring
      _ ≤ 70 * Z ^ 5 + 20 * Z := by omega
  omega

/-- **The closed form of the entry's cost**: the polynomial parts and `2^{c₁ (λ(N) + 1)⁸}` are at
most `2^{(256 c₁ + 23) (λ(n) + 1)⁸}`. -/
theorem gi_cost_le (n c₁ : ℕ) :
    encCost n + (genCost (gN n) (gensData n).length + 2 ^ (c₁ * (lam (gN n) + 1) ^ 8)) +
        decCost n (2 * gN n * (2 * gN n)) ≤
      2 ^ ((256 * c₁ + 23) * (lam n + 1) ^ 8) := by
  set X := lam n + 1 with hX
  have hX1 : 1 ≤ X := by omega
  have hn : n + 1 ≤ 2 ^ X := Nat.lt_pow_succ_log_self (by norm_num) n
  have hP := gi_poly_le n
  have hP' : 1000 * (n + 1) ^ 12 ≤ 2 ^ (22 * X) := by
    calc 1000 * (n + 1) ^ 12 ≤ 2 ^ 10 * (2 ^ X) ^ 12 :=
          Nat.mul_le_mul (by norm_num) (Nat.pow_le_pow_left hn 12)
      _ = 2 ^ (10 + 12 * X) := by rw [← pow_mul, ← pow_add]; ring_nf
      _ ≤ 2 ^ (22 * X) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hX8 : X ≤ X ^ 8 := by
    calc X = X ^ 1 := (pow_one X).symm
      _ ≤ X ^ 8 := Nat.pow_le_pow_right hX1 (by omega)
  have hlam : (lam (gN n) + 1) ^ 8 ≤ 256 * X ^ 8 := by
    calc (lam (gN n) + 1) ^ 8 ≤ (2 * X) ^ 8 := Nat.pow_le_pow_left (lam_gN_le n) 8
      _ = 256 * X ^ 8 := by ring
  have hQ : 2 ^ (c₁ * (lam (gN n) + 1) ^ 8) ≤ 2 ^ (256 * c₁ * X ^ 8) :=
    Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have h1 : 2 ^ (22 * X) ≤ 2 ^ ((256 * c₁ + 22) * X ^ 8) :=
    Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have h2 : 2 ^ (256 * c₁ * X ^ 8) ≤ 2 ^ ((256 * c₁ + 22) * X ^ 8) :=
    Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have h3 : 2 ^ ((256 * c₁ + 22) * X ^ 8) * 2 ≤ 2 ^ ((256 * c₁ + 23) * X ^ 8) := by
    rw [← pow_succ]
    exact Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  omega

variable {K T : ℕ → ℕ} {C C' : ℕ}

/-- **Graph isomorphism in time `2^{O((log n)⁸)}`** (`PLAN-14.md` §14.15 item 6). For all `C`,
`C'` there is `c` such that for all `K`, `T` with `QPHyp K T C C'`: on valid graph data `X`, `Y`
on `n` points (of any degree), the closed entry at the thresholds `thrQP C C'` (Schreier–Sims
substituted, no oracle) returns a `GICosetOK` result with local cost at most
`2^{c (λ(n) + 1)⁸}`. The cost covers the encoding, `generate`, the recursion and the decoding.

`QPHyp` is not shown satisfiable (see the module docstring); correctness alone is
`giSolve_ss`. The unconditional version is `giSolve_final`, through `QPHypJ`. -/
theorem giSolve_qp_exp (C C' : ℕ) :
    ∃ c, ∀ {K T : ℕ → ℕ}, QPHyp K T C C' → ∀ {Δ n : ℕ} {X Y : GraphData},
      X.ValidD Δ n → Y.ValidD Δ n →
      ∃ (r : Option (PermData × GensData)) (tr : Trace Signature.empty),
        Runs Ctx.empty.O ((qpSolver C C').proc Ty.denote)
          ((giEntry Ty.unit Ty.denote (n, X, Y)).subst ssImpl) r tr ∧
        Trace.localCost tr ≤ 2 ^ (c * (lam n + 1) ^ 8) ∧ GICosetOK n X Y r := by
  obtain ⟨c₁, hc₁⟩ := mainSolve_qp_exp_gens C C'
  refine ⟨256 * c₁ + 23, fun hQ Δ n X Y hX hY => ?_⟩
  obtain ⟨hw, hσ, hgs, hinv⟩ := giInst_valid n
  have hmain := hc₁ hQ (xy := (gStr n X, gStr n Y)) hw hσ hgs hinv
  obtain ⟨r, hrun, hok⟩ := giEntry_runs (thr := thrQP C C') hX hY hmain
  obtain ⟨tr, hr, hc⟩ := gi_close (thrQP_spec C C').wf hrun
  exact ⟨r, tr, hr, hc.trans (gi_cost_le n c₁), hok⟩

/-- The isomorphisms of the data of simple graphs are the permutations underlying `G ≃g H`. -/
theorem isIso_ofSimpleGraph_iff {n : ℕ} {G H : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    [DecidableRel H.Adj] (φ : Perm (Fin n)) :
    IsIso n (GraphData.ofSimpleGraph G) (GraphData.ofSimpleGraph H) φ ↔
      ∃ e : G ≃g H, e.toEquiv = φ := by
  have hG := valid_ofSimpleGraph (Δ := n) (H := G) fun v => (G.degree_lt_card_verts v).le.trans
    (by simp)
  have hH := valid_ofSimpleGraph (Δ := n) (H := H) fun v => (H.degree_lt_card_verts v).le.trans
    (by simp)
  rw [isIso_iff hG hH, toSimpleGraph_ofSimpleGraph, toSimpleGraph_ofSimpleGraph]
  constructor
  · intro h
    exact ⟨⟨φ, fun {u v} => h u v⟩, rfl⟩
  · rintro ⟨e, rfl⟩ u v
    exact e.map_rel_iff

/-- **Graph isomorphism of simple graphs in time `2^{O((log n)⁸)}`.** For all `C`, `C'` there is
`c` such that for all `K`, `T` with `QPHyp K T C C'`: for simple graphs `G`, `H` on `Fin n`,
given by their adjacency lists, the closed entry at the thresholds `thrQP C C'` returns `r` with
local cost at most `2^{c (λ(n) + 1)⁸}`; `r = none` exactly when `G` and `H` are not isomorphic,
and `r = some (τ, hs)` gives valid data of a permutation and of generators such that the coset
`τ • ⟨hs⟩` is exactly the set of the permutations underlying the isomorphisms `G ≃g H`.

`QPHyp` is not shown satisfiable (see the module docstring). The unconditional version is
`gi_simpleGraph_final`, through `QPHypJ`. -/
theorem gi_qp_simpleGraph (C C' : ℕ) :
    ∃ c, ∀ {K T : ℕ → ℕ}, QPHyp K T C C' → ∀ {n : ℕ} (G H : SimpleGraph (Fin n))
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
  obtain ⟨c, hc⟩ := giSolve_qp_exp C C'
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

end Headline

end GraphIso.Main
