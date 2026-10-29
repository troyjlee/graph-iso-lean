module

public import GraphIso.TM.SingleTape.Model
public import Mathlib.Computability.TuringMachine.Computable
public import Mathlib.Tactic.Linarith

/-!
# The simulation of stack machines on one tape, counted

Stage 18c (`PLAN-18.md` §4). Mathlib's `TM2to1.tr` simulates a stack machine (`TM2`) by a
machine with one tape and local state (`TM1`): the stacks are tracks of the tape over a bottom
mark, the head rests on the bottom mark, and every stack action travels to the stack's top and
back. Mathlib proves the simulation (`TM2to1.tr_respects`) without counting steps; here it is
counted, with mathlib's machine and configuration relation `TM2to1.TrCfg` unchanged.

* **Stack actions** (`acts q`): the number of stack actions on the longest path through the
  statement `q`, every branch included. A step of a `TM2` machine changes each stack's length by
  at most `acts` of the executed statement (`stepAux_length_le`, `step_length_le`).
* **The shuttles** (`go_steps`, `ret_steps`): travelling `n` cells to a stack's top, and back, are
  exactly `n` steps each.
* **One step** (`tr2_step`): if the stacks have length at most `B` and every statement has at most
  `s` stack actions, a step of the stack machine is simulated by at most
  `1 + s (2 (B + s) + 2)` steps: one to start, and per stack action at most `B + s` steps out,
  one at the top, at most `B + s` back and one to continue. Several stack actions in one
  statement are covered.
* **Runs** (`tr2_run`): `N` steps from stacks of length at most `B` are simulated by at most
  `N (1 + s (2 (B + s N) + 2))` steps; the stacks end with length at most `B + s N`
  (`run_length_le`).
* **Bundled machines** (`tmActs`, the largest `acts` of a statement of a `FinTM2`, over its
  finite labels; `tr2_outputs`): if `TM2OutputsInTime tm x (some y) T`, then from every
  configuration related to the initial one, mathlib's simulator reaches a configuration related
  to the final one (`haltList`, where it halts) within `A (T + 1) (|x| + T + 1)` steps, with
  `A = 2 s² + 2 s + 1` and `s = tmActs tm`; and `|y| ≤ |x| + s T` (`length_out_le`). Input and
  output stacks may differ.
-/

@[expose] public section

namespace GraphIso.TM.SingleTape

open Turing StateTransition Function TM2to1

section Acts

variable {K : Type*} {Γ : K → Type*} {Λ σ : Type*}

/-- **The stack actions of a statement**: the number of stack actions on its longest path. -/
def acts : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => acts q + 1
  | .peek _ _ q => acts q + 1
  | .pop _ _ q => acts q + 1
  | .load _ q => acts q
  | .branch _ q₁ q₂ => max (acts q₁) (acts q₂)
  | .goto _ => 0
  | .halt => 0

theorem acts_run {k : K} (s : StAct K Γ σ k) (q : TM2.Stmt Γ Λ σ) :
    acts (stRun s q) = acts q + 1 := by
  cases s <;> rfl

theorem length_stWrite_le {k : K} (v : σ) (l : List (Γ k)) (s : StAct K Γ σ k) :
    (stWrite v l s).length ≤ l.length + 1 := by
  cases s <;> simp [stWrite]
  omega

variable [DecidableEq K]

/-- A statement changes each stack's length by at most its number of stack actions. -/
theorem stepAux_length_le (q : TM2.Stmt Γ Λ σ) :
    ∀ (v : σ) (S : ∀ k, List (Γ k)) (B : ℕ), (∀ k, (S k).length ≤ B) →
      ∀ k, ((TM2.stepAux q v S).stk k).length ≤ B + acts q := by
  induction q using stmtStRec with
  | run k s q IH =>
    intro v S B hB
    rw [step_run, acts_run]
    have := IH (stVar v (S k) s) (update S k (stWrite v (S k) s)) (B + 1) fun j => by
      by_cases hj : j = k
      · subst hj
        rw [update_self]
        exact (length_stWrite_le _ _ _).trans (Nat.succ_le_succ (hB j))
      · rw [update_of_ne hj]
        exact (hB j).trans (Nat.le_succ B)
    intro j
    have := this j
    omega
  | load a q IH =>
    intro v S B hB
    exact IH _ S B hB
  | branch p q₁ q₂ IH₁ IH₂ =>
    intro v S B hB j
    simp only [TM2.stepAux, acts]
    cases p v
    · exact (IH₂ v S B hB j).trans (Nat.add_le_add_left (le_max_right _ _) B)
    · exact (IH₁ v S B hB j).trans (Nat.add_le_add_left (le_max_left _ _) B)
  | goto l =>
    intro v S B hB j
    exact hB j
  | halt =>
    intro v S B hB j
    exact hB j

/-- **Stack growth in one step**: a step changes each stack's length by at most the number of
stack actions of the executed statement. -/
theorem step_length_le (M : Λ → TM2.Stmt Γ Λ σ) {s : ℕ} (hs : ∀ l, acts (M l) ≤ s)
    {c c' : TM2.Cfg Γ Λ σ} (h : TM2.step M c = some c') {B : ℕ} (hB : ∀ k, (c.stk k).length ≤ B) :
    ∀ k, (c'.stk k).length ≤ B + s := by
  obtain ⟨_ | l, v, S⟩ := c
  · cases h
  · obtain rfl := Option.some.inj h
    intro k
    exact (stepAux_length_le (M l) v S B hB k).trans (Nat.add_le_add_left (hs l) B)

end Acts

section Shuttle

variable {K : Type*} [DecidableEq K] {Γ : K → Type*} {Λ σ : Type*}
variable (M : Λ → TM2.Stmt Γ Λ σ)

/-- **The outward shuttle**: `n` cells towards a stack's top are exactly `n` steps. -/
theorem go_steps {k : K} (o : StAct K Γ σ k) (q : TM2.Stmt Γ Λ σ) (v : σ) {S : List (Γ k)}
    {L : ListBlank (∀ k, Option (Γ k))} (hL : L.map (proj k) = ListBlank.mk (S.map some).reverse)
    (n : ℕ) (H : n ≤ S.length) :
    StepsIn (TM1.step (tr M)) n ⟨some (Λ'.go k o q), v, Tape.mk' ∅ (addBottom L)⟩
      ⟨some (Λ'.go k o q), v, (Tape.move Dir.right)^[n] (Tape.mk' ∅ (addBottom L))⟩ := by
  induction n with
  | zero => exact StepsIn.zero _
  | succ n IH =>
    apply (IH (le_of_lt H)).tail
    rw [iterate_succ_apply']
    simp only [TM1.step, TM1.stepAux, tr, Tape.mk'_nth_nat, Tape.move_right_n_head,
      addBottom_nth_snd]
    rw [stk_nth_val _ hL, List.getElem?_eq_getElem]
    · rfl
    · rwa [List.length_reverse]

/-- **The return shuttle**: `n` cells back to the bottom mark are exactly `n` steps. -/
theorem ret_steps (q : TM2.Stmt Γ Λ σ) (v : σ) (L : ListBlank (∀ k, Option (Γ k))) (n : ℕ) :
    StepsIn (TM1.step (tr M)) n
      ⟨some (Λ'.ret q), v, (Tape.move Dir.right)^[n] (Tape.mk' ∅ (addBottom L))⟩
      ⟨some (Λ'.ret q), v, Tape.mk' ∅ (addBottom L)⟩ := by
  induction n with
  | zero => exact StepsIn.zero _
  | succ n IH =>
    refine StepsIn.head ?_ IH
    simp only [TM1.step]
    rw [tr, TM1.stepAux, Tape.move_right_n_head, Tape.mk'_nth_nat, addBottom_nth_succ_fst,
      TM1.stepAux, iterate_succ', Function.comp_apply, Tape.move_right_left]
    rfl

/-- **A statement, counted**: from stacks of length at most `B`, the simulation of the rest of
the statement `q` takes at most `acts q (2 (B + acts q) + 2)` steps. -/
theorem trNormal_steps (q : TM2.Stmt Γ Λ σ) :
    ∀ {v : σ} {S : ∀ k, List (Γ k)} {T : ListBlank (∀ k, Option (Γ k))} {B : ℕ},
      (∀ k, T.map (proj k) = ListBlank.mk ((S k).map some).reverse) →
      (∀ k, (S k).length ≤ B) →
      ∃ b n, TrCfg (TM2.stepAux q v S) b ∧
        StepsIn (TM1.step (tr M)) n (TM1.stepAux (trNormal q) v (Tape.mk' ∅ (addBottom T))) b ∧
        n ≤ acts q * (2 * (B + acts q) + 2) := by
  induction q using stmtStRec with
  | run k s q IH =>
    intro v S T B hT hB
    rw [trNormal_run, step_run, acts_run]
    obtain ⟨T', hT', hrun⟩ := tr_respects_aux₂ (Λ := Λ) (q := TM1.Stmt.goto fun _ _ => Λ'.ret q)
      hT s
    set v' := stVar v (S k) s
    set S' := update S k (stWrite v (S k) s)
    have hgo := go_steps M s q v (hT k) _ le_rfl
    have htop : TM1.step (tr M) ⟨some (Λ'.go k s q), v,
        (Tape.move Dir.right)^[(S k).length] (Tape.mk' ∅ (addBottom T))⟩ =
        some ⟨some (Λ'.ret q), v',
          (Tape.move Dir.right)^[(S' k).length] (Tape.mk' ∅ (addBottom T'))⟩ := by
      simp only [TM1.step]
      rw [tr, TM1.stepAux, Tape.move_right_n_head, Tape.mk'_nth_nat, addBottom_nth_snd,
        stk_nth_val _ (hT k), List.getElem?_eq_none (le_of_eq List.length_reverse),
        Option.isNone, cond, hrun, TM1.stepAux]
    have hret := ret_steps M q v' T' (S' k).length
    have hbot : TM1.step (tr M) ⟨some (Λ'.ret q), v', Tape.mk' ∅ (addBottom T')⟩ =
        some (TM1.stepAux (trNormal q) v' (Tape.mk' ∅ (addBottom T'))) := by
      simp only [TM1.step]
      rw [tr, TM1.stepAux, Tape.mk'_head, addBottom_head_fst]
      rfl
    have hB' : ∀ j, (S' j).length ≤ B + 1 := fun j => by
      by_cases hj : j = k
      · subst hj
        simp only [S', update_self]
        exact (length_stWrite_le _ _ _).trans (Nat.succ_le_succ (hB j))
      · simp only [S', update_of_ne hj]
        exact (hB j).trans (Nat.le_succ B)
    obtain ⟨b, n, hb, hn, hle⟩ := IH hT' hB'
    refine ⟨b, (S k).length + 1 + (S' k).length + 1 + n, hb, ?_, ?_⟩
    · exact (((hgo.tail htop).trans hret).tail hbot).trans hn
    · have h1 := hB k
      have h2 := hB' k
      set a := acts q
      have : n ≤ a * (2 * (B + (a + 1)) + 2) := by
        rw [show B + (a + 1) = B + 1 + a by omega]
        exact hle
      rw [Nat.succ_mul]
      omega
  | load a q IH =>
    intro v S T B hT hB
    exact IH hT hB
  | branch p q₁ q₂ IH₁ IH₂ =>
    intro v S T B hT hB
    simp only [TM2.stepAux, trNormal, TM1.stepAux, acts]
    cases p v
    · obtain ⟨b, n, hb, hn, hle⟩ := IH₂ hT hB
      refine ⟨b, n, hb, hn, hle.trans ?_⟩
      exact Nat.mul_le_mul (le_max_right _ _)
        (by have := le_max_right (acts q₁) (acts q₂); omega)
    · obtain ⟨b, n, hb, hn, hle⟩ := IH₁ hT hB
      refine ⟨b, n, hb, hn, hle.trans ?_⟩
      exact Nat.mul_le_mul (le_max_left _ _)
        (by have := le_max_left (acts q₁) (acts q₂); omega)
  | goto l =>
    intro v S T B hT hB
    exact ⟨_, 0, ⟨T, hT⟩, StepsIn.zero _, Nat.zero_le _⟩
  | halt =>
    intro v S T B hT hB
    exact ⟨_, 0, ⟨T, hT⟩, StepsIn.zero _, Nat.zero_le _⟩

/-- **One step, counted**: if the stacks have length at most `B` and every statement has at most
`s` stack actions, a step of the stack machine is simulated by at most `1 + s (2 (B + s) + 2)`
steps. -/
theorem tr2_step {s : ℕ} (hs : ∀ l, acts (M l) ≤ s) {c₂ c₂' : TM2.Cfg Γ Λ σ}
    (h : TM2.step M c₂ = some c₂') {c₁ : TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ} (hc : TrCfg c₂ c₁)
    {B : ℕ} (hB : ∀ k, (c₂.stk k).length ≤ B) :
    ∃ c₁' n, TrCfg c₂' c₁' ∧ StepsIn (TM1.step (tr M)) n c₁ c₁' ∧
      n ≤ 1 + s * (2 * (B + s) + 2) := by
  obtain @⟨_ | l, v, S, T, hT⟩ := hc
  · cases h
  · obtain rfl := Option.some.inj h
    obtain ⟨b, n, hb, hn, hle⟩ := trNormal_steps M (M l) hT hB
    refine ⟨b, n + 1, hb, StepsIn.head rfl hn, ?_⟩
    have : acts (M l) * (2 * (B + acts (M l)) + 2) ≤ s * (2 * (B + s) + 2) :=
      Nat.mul_le_mul (hs l) (by have := hs l; omega)
    omega

/-- **Stack growth along a run**: after `N` steps from stacks of length at most `B`, every
stack has length at most `B + s N`. -/
theorem run_length_le {s : ℕ} (hs : ∀ l, acts (M l) ≤ s) {N : ℕ} {c c' : TM2.Cfg Γ Λ σ}
    (h : StepsIn (TM2.step M) N c c') {B : ℕ} (hB : ∀ k, (c.stk k).length ≤ B) :
    ∀ k, (c'.stk k).length ≤ B + s * N := by
  induction N generalizing c B with
  | zero =>
    obtain rfl := stepsIn_zero.1 h
    simpa using hB
  | succ N ih =>
    obtain ⟨c₃, h₁, h⟩ := stepsIn_succ.1 h
    intro k
    have := ih h (step_length_le M hs h₁ hB) k
    rw [Nat.mul_succ]
    omega

/-- **Runs, counted**: `N` steps of the stack machine from stacks of length at most `B` are
simulated by at most `N (1 + s (2 (B + s N) + 2))` steps. -/
theorem tr2_run {s : ℕ} (hs : ∀ l, acts (M l) ≤ s) {N : ℕ} {c₂ c₂' : TM2.Cfg Γ Λ σ}
    (h : StepsIn (TM2.step M) N c₂ c₂') {c₁ : TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ}
    (hc : TrCfg c₂ c₁) {B : ℕ} (hB : ∀ k, (c₂.stk k).length ≤ B) :
    ∃ c₁' n, TrCfg c₂' c₁' ∧ StepsIn (TM1.step (tr M)) n c₁ c₁' ∧
      n ≤ N * (1 + s * (2 * (B + s * N) + 2)) := by
  induction N generalizing c₂ c₁ B with
  | zero =>
    obtain rfl := stepsIn_zero.1 h
    exact ⟨c₁, 0, hc, StepsIn.zero _, Nat.zero_le _⟩
  | succ N ih =>
    obtain ⟨c₃, h₁, h⟩ := stepsIn_succ.1 h
    obtain ⟨c₄, n₁, hc₄, hn₁, hle₁⟩ := tr2_step M hs h₁ hc hB
    obtain ⟨c₁', n₂, hc', hn₂, hle₂⟩ := ih h hc₄ (step_length_le M hs h₁ hB)
    refine ⟨c₁', n₁ + n₂, hc', hn₁.trans hn₂, ?_⟩
    have e : B + s + s * N = B + s * (N + 1) := by rw [Nat.mul_succ]; omega
    rw [e] at hle₂
    have : s * (2 * (B + s) + 2) ≤ s * (2 * (B + s * (N + 1)) + 2) :=
      Nat.mul_le_mul_left s (by have := Nat.le_mul_of_pos_right s (Nat.succ_pos N); omega)
    rw [Nat.succ_mul]
    omega

end Shuttle

section Fin

open FinTM2

/-- **The stack actions of a bundled machine**: the largest number of stack actions of one of
its statements (over its finitely many labels). -/
def tmActs (tm : FinTM2) : ℕ :=
  letI := tm.ΛFin
  Finset.univ.sup fun l => SingleTape.acts (tm.m l)

theorem tmActs_le (tm : FinTM2) (l : tm.Λ) : SingleTape.acts (tm.m l) ≤ tmActs tm :=
  letI := tm.ΛFin
  Finset.le_sup (f := fun l => SingleTape.acts (tm.m l)) (Finset.mem_univ l)

variable (tm : FinTM2)

theorem initList_stk_self (x : List (tm.Γ tm.k₀)) : (initList tm x).stk tm.k₀ = x := by
  simp [initList]

theorem initList_stk_ne (x : List (tm.Γ tm.k₀)) {k : tm.K} (hk : k ≠ tm.k₀) :
    (initList tm x).stk k = [] := by
  simp [initList, hk]

theorem haltList_stk_self (y : List (tm.Γ tm.k₁)) : (haltList tm y).stk tm.k₁ = y := by
  simp [haltList]

theorem haltList_stk_ne (y : List (tm.Γ tm.k₁)) {k : tm.K} (hk : k ≠ tm.k₁) :
    (haltList tm y).stk k = [] := by
  simp [haltList, hk]

theorem initList_length_le (x : List (tm.Γ tm.k₀)) (k : tm.K) :
    ((initList tm x).stk k).length ≤ x.length := by
  by_cases hk : k = tm.k₀
  · subst hk
    rw [initList_stk_self]
  · rw [initList_stk_ne tm x hk]
    exact Nat.zero_le _

/-- `N (1 + s (2 (L + s N) + 2)) ≤ (2 s² + 2 s + 1) (N + 1) (L + N + 1)`. -/
theorem run_bound_le (s N L : ℕ) :
    N * (1 + s * (2 * (L + s * N) + 2)) ≤ (2 * s ^ 2 + 2 * s + 1) * (N + 1) * (L + N + 1) := by
  nlinarith [Nat.zero_le (s * N * L), Nat.zero_le (s * s * N * N), Nat.zero_le (s * N),
    Nat.zero_le (s * s * N * L), Nat.zero_le (N * L), Nat.zero_le (N * N), Nat.zero_le s,
    Nat.zero_le N, Nat.zero_le L, Nat.zero_le (s * s * N), Nat.zero_le (s * N * N)]

/-- **The simulation of a bundled machine, counted**: if `tm` outputs `y` on `x` within `T`
steps, then from every configuration related to the initial one, mathlib's simulator reaches a
configuration related to the final one within `(2 s² + 2 s + 1) (T + 1) (|x| + T + 1)` steps,
`s = tmActs tm`. -/
theorem tr2_outputs {x : List (tm.Γ tm.k₀)} {y : List (tm.Γ tm.k₁)} {T : ℕ}
    (h : TM2OutputsInTime tm x (some y) T)
    {c₁ : TM1.Cfg (Γ' tm.K tm.Γ) (Λ' tm.K tm.Γ tm.Λ tm.σ) tm.σ}
    (hc : TrCfg (initList tm x) c₁) :
    ∃ c₁' n, TrCfg (haltList tm y) c₁' ∧ StepsIn (TM1.step (tr tm.m)) n c₁ c₁' ∧
      n ≤ (2 * tmActs tm ^ 2 + 2 * tmActs tm + 1) * (T + 1) * (x.length + T + 1) := by
  obtain ⟨N, hN, hr⟩ := EvalsToInTime.stepsIn h
  obtain ⟨c₁', n, hc', hn, hle⟩ :=
    tr2_run tm.m (tmActs_le tm) hr hc (initList_length_le tm x)
  refine ⟨c₁', n, hc', hn, hle.trans ((run_bound_le _ _ _).trans ?_)⟩
  apply Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)

/-- **The output's length**: `|y| ≤ |x| + s T`. -/
theorem length_out_le {x : List (tm.Γ tm.k₀)} {y : List (tm.Γ tm.k₁)} {T : ℕ}
    (h : TM2OutputsInTime tm x (some y) T) : y.length ≤ x.length + tmActs tm * T := by
  obtain ⟨N, hN, hr⟩ := EvalsToInTime.stepsIn h
  have := run_length_le tm.m (tmActs_le tm) hr (initList_length_le tm x) tm.k₁
  rw [haltList_stk_self] at this
  exact this.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ hN) _)

end Fin

end GraphIso.TM.SingleTape
