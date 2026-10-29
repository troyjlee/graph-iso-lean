module

public import GraphIso.TM.SingleTape.TM2Sim
public import GraphIso.TM.SingleTape.TM1Sim

/-!
# Stack machines on one tape: the composed simulation and its finite control

Stage 18d (`PLAN-18.md` §5), composing stage 18c (mathlib's `TM2to1.tr`, counted) with the
counted translation `TM1to0.tr` of `TM1Sim`. This module imports mathlib only.

* **Statement sizes of the simulator** (`stmtSize_trNormal`, `stmtSize_tr`): every statement of
  mathlib's simulator `TM2to1.tr M` has size at most `3`, for every stack machine `M` (stack
  actions become jumps to the shuttles; loads and branches cost nothing).
* **The composed simulation, counted** (`sim_run`): `N` steps of a stack machine from stacks of
  length at most `B`, with at most `s` stack actions per statement, are at most
  `3 N (1 + s (2 (B + s N) + 2))` transitions of the single-tape machine
  `TM1to0.tr (TM2to1.tr M)`, between configurations related by `TM2to1.TrCfg` and
  `TM1to0.trCfg`.
* **Bundled machines** (`sim_outputs`): if `TM2OutputsInTime tm x (some y) T`, then within
  `3 (2 s² + 2 s + 1) (T + 1) (|x| + T + 1)` transitions, `s = tmActs tm`. The labels of `tm`
  support its program (`supportsStmt_univ`), so mathlib's `TM2to1.tr_supports` and
  `TM1to0.tr_supports` give a finite closed set of states (`tr_supports_univ`).
* **The finite simulator** (`simTM0 tm hΓ`, for finite stack alphabets `hΓ`): the single-tape
  translation of the simulator restricted to its reachable states (`FinTM0.ofTM1`), with the
  start label `normal tm.main` and the local state `tm.initialState` (`mainInhabited`,
  `initList_eq_init`). **`simTM0_outputs`**: if `TM2OutputsInTime tm x (some y) T`, it runs from
  mathlib's initial simulator tape `trInit tm.k₀ x` to a configuration where it halts, whose
  tape holds the stacks of `haltList tm y` (`TrCfg`'s layout), within
  `3 (2 s² + 2 s + 1) (T + 1) (|x| + T + 1)` transitions. The framed input and output are
  stage 18e.
-/

@[expose] public section

namespace GraphIso.TM.SingleTape

open Turing StateTransition Function TM2to1

section Size

variable {K : Type*} {Γ : K → Type*} {Λ σ : Type*}

/-- A statement of mathlib's simulator without its stack actions has size `1`. -/
theorem stmtSize_trNormal (q : TM2.Stmt Γ Λ σ) :
    stmtSize (trNormal q : TM1.Stmt (Γ' K Γ) (Λ' K Γ Λ σ) σ) = 1 := by
  induction q with
  | push k f q IH => rfl
  | peek k f q IH => rfl
  | pop k f q IH => rfl
  | load a q IH => exact IH
  | branch p q₁ q₂ IH₁ IH₂ => exact (congrArg₂ max IH₁ IH₂).trans (max_self 1)
  | goto l => rfl
  | halt => rfl

/-- Every statement of a stack machine is supported by all its labels. -/
theorem supportsStmt_univ [Fintype Λ] (q : TM2.Stmt Γ Λ σ) : TM2.SupportsStmt Finset.univ q := by
  induction q with
  | push k f q IH => exact IH
  | peek k f q IH => exact IH
  | pop k f q IH => exact IH
  | load a q IH => exact IH
  | branch p q₁ q₂ IH₁ IH₂ => exact ⟨IH₁, IH₂⟩
  | goto l => exact fun _ => Finset.mem_univ _
  | halt => trivial

variable [DecidableEq K]

/-- **Every statement of mathlib's simulator has size at most `3`.** -/
theorem stmtSize_tr (M : Λ → TM2.Stmt Γ Λ σ) (l : Λ' K Γ Λ σ) : stmtSize (tr M l) ≤ 3 := by
  cases l with
  | normal q => exact (stmtSize_trNormal (M q)).trans_le (by decide)
  | go k s q => cases s <;> exact Nat.le_of_ble_eq_true rfl
  | ret q => exact max_le ((stmtSize_trNormal q).trans_le (by decide)) (Nat.le_of_ble_eq_true rfl)

/-- **The composed simulation, counted**: `N` steps of a stack machine from stacks of length at
most `B` are at most `3 N (1 + s (2 (B + s N) + 2))` single-tape transitions. -/
theorem sim_run [Inhabited Λ] [Inhabited σ] (M : Λ → TM2.Stmt Γ Λ σ) {s : ℕ}
    (hs : ∀ l, acts (M l) ≤ s) {N : ℕ} {c c' : TM2.Cfg Γ Λ σ} (h : StepsIn (TM2.step M) N c c')
    {t : TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ} (ht : TrCfg c t) {B : ℕ}
    (hB : ∀ k, (c.stk k).length ≤ B) :
    ∃ t' n, TrCfg c' t' ∧
      StepsIn (TM0.step (TM1to0.tr (tr M))) n (TM1to0.trCfg (tr M) t) (TM1to0.trCfg (tr M) t') ∧
      n ≤ 3 * (N * (1 + s * (2 * (B + s * N) + 2))) := by
  obtain ⟨t', m, ht', hm, hle⟩ := tr2_run M hs h ht hB
  obtain ⟨n, hn, hr⟩ := tr1_run (tr M) (stmtSize_tr M) hm
  exact ⟨t', n, ht', hr, hn.trans (by rw [Nat.mul_comm 3]; exact Nat.mul_le_mul_right 3 hle)⟩

end Size

section Fin

variable (tm : FinTM2)

/-- The main label as the default label: mathlib's convention for `TM2.init` and for the
simulator's start label. -/
scoped instance mainInhabited : Inhabited tm.Λ :=
  ⟨tm.main⟩

/-- `initList` is mathlib's `TM2.init` on the input stack. -/
theorem initList_eq_init (x : List (tm.Γ tm.k₀)) : initList tm x = TM2.init tm.k₀ x := by
  have h : (initList tm x).stk = update (fun _ => []) tm.k₀ x := by
    funext k
    by_cases hk : k = tm.k₀
    · subst hk
      rw [initList_stk_self, update_self]
    · rw [initList_stk_ne tm x hk, update_of_ne hk]
  change (⟨some tm.main, tm.initialState, (initList tm x).stk⟩ : TM2.Cfg _ _ _) = _
  rw [h]
  rfl

/-- **The composed simulation of a bundled machine**: within
`3 (2 s² + 2 s + 1) (T + 1) (|x| + T + 1)` single-tape transitions. -/
theorem sim_outputs {x : List (tm.Γ tm.k₀)} {y : List (tm.Γ tm.k₁)} {T : ℕ}
    (h : TM2OutputsInTime tm x (some y) T)
    {c₁ : TM1.Cfg (Γ' tm.K tm.Γ) (Λ' tm.K tm.Γ tm.Λ tm.σ) tm.σ}
    (hc : TrCfg (initList tm x) c₁) :
    ∃ c₁' n, TrCfg (haltList tm y) c₁' ∧
      StepsIn (TM0.step (TM1to0.tr (tr tm.m))) n (TM1to0.trCfg (tr tm.m) c₁)
        (TM1to0.trCfg (tr tm.m) c₁') ∧
      n ≤ 3 * ((2 * tmActs tm ^ 2 + 2 * tmActs tm + 1) * (T + 1) * (x.length + T + 1)) := by
  obtain ⟨c₁', m, hc', hm, hle⟩ := tr2_outputs tm h hc
  obtain ⟨n, hn, hr⟩ := tr1_run (tr tm.m) (stmtSize_tr tm.m) hm
  exact ⟨c₁', n, hc', hr, hn.trans (by rw [Nat.mul_comm 3]; exact Nat.mul_le_mul_right 3 hle)⟩

/-- **A finite set of labels supports the simulator**: mathlib's `TM2to1.trSupp` of all labels
(`TM2to1.tr_supports`). -/
theorem tr_supports_univ : ∃ S, TM1.Supports (tr tm.m) S :=
  letI := tm.ΛFin
  ⟨_, TM2to1.tr_supports tm.m (S := Finset.univ)
    ⟨Finset.mem_univ _, fun q _ => supportsStmt_univ (tm.m q)⟩⟩

/-- The simulator's alphabet is finite when the stack alphabets are. -/
theorem finite_Γ' (hΓ : ∀ k, Finite (tm.Γ k)) : Finite (Γ' tm.K tm.Γ) := by
  have := tm.kFin
  exact inferInstanceAs (Finite (Bool × ∀ k, Option (tm.Γ k)))

/-- **The finite single-tape simulator**: `TM1to0.tr (TM2to1.tr tm.m)` restricted to its
reachable states (stage 18d's `FinTM0.ofTM1`), finite by `TM1to0.tr_supports`. -/
def simTM0 (hΓ : ∀ k, Finite (tm.Γ k)) : FinTM0 :=
  haveI := finite_Γ' tm hΓ
  haveI := tm.σFin
  FinTM0.ofTM1 (tr tm.m) (tr_supports_univ tm)

/-- **The finite simulator, counted**: from mathlib's initial simulator tape `trInit tm.k₀ x`, it
halts on a tape holding the stacks of `haltList tm y` (bottom mark at the head, `TrCfg`'s layout)
within `3 (2 s² + 2 s + 1) (T + 1) (|x| + T + 1)` transitions. -/
theorem simTM0_outputs (hΓ : ∀ k, Finite (tm.Γ k)) {x : List (tm.Γ tm.k₀)}
    {y : List (tm.Γ tm.k₁)} {T : ℕ} (h : TM2OutputsInTime tm x (some y) T) :
    ∃ L : ListBlank (∀ k, Option (tm.Γ k)),
      (∀ k, L.map (proj k) = ListBlank.mk (((haltList tm y).stk k).map some).reverse) ∧
      ∃ q n, n ≤ 3 * ((2 * tmActs tm ^ 2 + 2 * tmActs tm + 1) * (T + 1) * (x.length + T + 1)) ∧
        StepsIn (simTM0 tm hΓ).step n (TM0.init (trInit tm.k₀ x))
          ⟨q, Tape.mk' ∅ (addBottom L)⟩ ∧
        (simTM0 tm hΓ).step ⟨q, Tape.mk' ∅ (addBottom L)⟩ = none := by
  have hc := trCfg_init (Λ := tm.Λ) (σ := tm.σ) tm.k₀ x
  rw [← initList_eq_init] at hc
  obtain ⟨c₁', n, hc', hn, hle⟩ := sim_outputs tm h hc
  obtain ⟨L, hL⟩ := hc'
  obtain ⟨hq, hr⟩ := restrict_steps (q := restrictStart (TM1to0.tr (tr tm.m))) hn
  exact ⟨L, hL, ⟨_, hq⟩, n, hle, hr, restrict_halt (tr1_halt _ _ _)⟩

end Fin

end GraphIso.TM.SingleTape
