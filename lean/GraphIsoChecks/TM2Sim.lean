module

public import GraphIso.TM.SingleTape.TM2Sim
import all Init.Data.Array.Basic
import all Init.Data.List.Sort.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Mathlib.Data.List.Sort

/-!
# Checks of stage 18c: the simulation of stack machines on one tape, counted

`PLAN-18.md` §4. This module does not import the graph-isomorphism development. Mathlib's
simulator `TM2to1.tr` is run by the kernel; its configurations are observed through the cells of
the tape (`stackOf`: the entries of one stack, bottom first, as the simulator stores them).

* **Reversal** (`revTM`, a bundled machine with input stack `true` and output stack `false`):
  it pops the input into its state and pushes it onto the output, so it outputs `x.reverse`. On
  `[true, false]` it halts with `[false, true]` after exactly `3` steps (`rev_outputs`, by the
  kernel); the simulator, started on mathlib's initial tape `trInit true [true, false]`, halts
  after exactly `21` steps with the input stack empty and the output stack `true, false` from the
  bottom, within the bound `(2 s² + 2 s + 1) (T + 1) (|x| + T + 1) = 312` of `tr2_outputs`
  (`s = tmActs revTM = 2`), which is also instantiated. On the empty input: `3` steps.
* **Several stack actions in one step** (`mixM`): a peek, a pop of an empty stack, two pushes
  and a pop, then a jump. From the stacks `[true, false]` and `[]` the step ends with stacks of
  different lengths, `[false]` and `[false, true]`; the simulator takes exactly `22` steps,
  within `1 + s (2 (B + s) + 2) = 81` of `tr2_step` (`s = 5`, `B = 2`).
* **Negative controls:** neither simulation is done a step earlier; the output stack is stored
  bottom first on the tape, not in list order; `revTM` does not output `[true, false]`.
-/

@[expose] public section

namespace GraphIsoChecks.TM2Sim

open Turing StateTransition GraphIso.TM.SingleTape TM2to1

/-- The stack alphabets: `Bool`. -/
abbrev BΓ : Bool → Type :=
  fun _ => Bool

/-- The simulator's tape cells: the entries of stack `k` in the first `n` cells, bottom first. -/
def stackOf (T : Tape (Γ' Bool BΓ)) (k : Bool) (n : ℕ) : List (Option Bool) :=
  (List.range n).map fun i => (T.nth i).2 k

/-- Configurations of machines with two stacks are compared stack by stack. -/
instance {Λ σ : Type} [DecidableEq Λ] [DecidableEq σ] : DecidableEq (TM2.Cfg BΓ Λ σ)
  | ⟨l, v, S⟩, ⟨l', v', S'⟩ =>
    decidable_of_iff (l = l' ∧ v = v' ∧ S = S') (by simp only [TM2.Cfg.mk.injEq])

/-! ### Reversal -/

/-- Pop the input stack `true` into the state; if it held a symbol, push it onto the output
stack `false` and repeat, otherwise halt. -/
def revStmt : TM2.Stmt BΓ Unit (Option Bool) :=
  .pop true (fun _ o => o)
    (.branch (fun v => v.isSome) (.push false (fun v => v.getD false) (.goto fun _ => ())) .halt)

/-- **The reversal machine.** -/
abbrev revTM : FinTM2 where
  K := Bool
  k₀ := true
  k₁ := false
  Γ := BΓ
  Λ := Unit
  main := ()
  σ := Option Bool
  initialState := none
  m := fun _ => revStmt

instance : DecidableEq revTM.Cfg :=
  inferInstanceAs (DecidableEq (TM2.Cfg BΓ Unit (Option Bool)))

/-- `revTM` outputs `[false, true]` on `[true, false]` in exactly `3` steps. -/
theorem rev_run : (flip bind revTM.step)^[3] (some (initList revTM [true, false])) =
    some (haltList revTM [false, true]) := by
  decide +kernel

def rev_outputs : TM2OutputsInTime revTM [true, false] (some [false, true]) 3 :=
  ⟨⟨3, rev_run⟩, le_rfl⟩

theorem tmActs_revTM : tmActs revTM = 2 := by
  decide +kernel

/-- The simulator's configurations. -/
abbrev SCfg : Type :=
  TM1.Cfg (Γ' Bool BΓ) (Λ' Bool BΓ Unit (Option Bool)) (Option Bool)

/-- The simulator after `n` steps from mathlib's initial tape for `x` on the input stack. -/
def simAfter (n : ℕ) (x : List Bool) : Option SCfg :=
  (flip bind (TM1.step (tr revTM.m)))^[n] (some (TM1.init (trInit true x)))

/-- `initList` is mathlib's `TM2.init` on the input stack. -/
theorem initList_rev : initList revTM [true, false] =
    (TM2.init true [true, false] : TM2.Cfg BΓ Unit (Option Bool)) := by
  change (⟨some (), none, (initList revTM [true, false]).stk⟩ : TM2.Cfg BΓ Unit (Option Bool)) =
    ⟨some (), none, Function.update (fun _ => []) true [true, false]⟩
  congr 1
  funext k
  cases k <;> rfl

/-- **The simulator halts after exactly `21` steps**, with the input stack empty and the output
stack `true, false` from the bottom (the list `[false, true]`, reversed), the bottom mark on the
first cell. -/
example : (simAfter 21 [true, false]).map (fun c => (c.l.isNone, c.var, (c.Tape.nth 0).1,
    stackOf c.Tape true 3, stackOf c.Tape false 3)) =
      some (true, none, true, [none, none, none], [some true, some false, none]) := by
  decide +kernel

/-- **Negative control**: not halted before `21` steps. -/
theorem sim_running_lt_21 : ∀ n < 21, (simAfter n [true, false]).map (fun c => c.l.isSome) =
    some true := by
  decide +kernel

/-- **Negative control**: the output stack is stored bottom first, not in list order. -/
example : (simAfter 21 [true, false]).map (fun c => stackOf c.Tape false 2) ≠
    some ([false, true].map some) := by
  decide +kernel

/-- The empty input: `3` steps. -/
example : (simAfter 3 []).map (fun c => (c.l.isNone, stackOf c.Tape false 1)) =
    some (true, [none]) := by
  decide +kernel

/-- **`tr2_outputs` instantiated**: within `(2 · 2² + 2 · 2 + 1) (3 + 1) (2 + 3 + 1) = 312`
steps. -/
example : ∃ c₁' n, TrCfg (haltList revTM [false, true]) c₁' ∧
    StepsIn (TM1.step (tr revTM.m)) n (TM1.init (trInit true [true, false])) c₁' ∧
      n ≤ 312 := by
  have hc : TrCfg (initList revTM [true, false])
      (TM1.init (trInit true [true, false]) : SCfg) := by
    rw [initList_rev]
    exact trCfg_init (Γ := BΓ) (Λ := Unit) (σ := Option Bool) true [true, false]
  have := tr2_outputs revTM rev_outputs hc
  rwa [tmActs_revTM] at this

/-- **Negative control**: `revTM` does not output the input itself. -/
example (m : ℕ) : IsEmpty (TM2OutputsInTime revTM [true, false] (some [true, false]) m) :=
  ⟨fun h => by
    obtain ⟨n, -, hn⟩ := EvalsToInTime.stepsIn h
    obtain ⟨-, e⟩ := hn.halt_unique rfl rev_run rfl
    have := congrArg (fun c : revTM.Cfg => c.stk false) e
    exact absurd this (by decide +kernel)⟩

/-! ### Several stack actions in one step -/

/-- The labels of `mixM`. -/
inductive ML where
  | start
  | done
  deriving DecidableEq

instance : Inhabited ML :=
  ⟨.start⟩

/-- A peek of stack `true`, a pop of the empty stack `false`, two pushes onto `false` and a pop
of `true`, in one step. -/
def mixM : ML → TM2.Stmt BΓ ML (Option Bool)
  | .start => .peek true (fun _ o => o) (.pop false (fun v _ => v)
      (.push false (fun v => v.getD false) (.push false (fun v => !(v.getD false))
        (.pop true (fun v _ => v) (.goto fun _ => .done)))))
  | .done => .halt

theorem acts_mixM : acts (mixM .start) = 5 :=
  rfl

/-- The step of `mixM`: the stacks `[true, false]` and `[]` become `[false]` and
`[false, true]`. -/
example : (TM2.step mixM (TM2.init true [true, false])).map
    (fun c => (c.l, c.var, c.stk true, c.stk false)) =
      some (some .done, some true, [false], [false, true]) := by
  decide +kernel

/-- Whether the simulator is at the label `done`. -/
def isDone : Option (Λ' Bool BΓ ML (Option Bool)) → Bool
  | some (.normal .done) => true
  | _ => false

/-- The simulator of `mixM` after `n` steps. -/
def mixAfter (n : ℕ) :
    Option (TM1.Cfg (Γ' Bool BΓ) (Λ' Bool BΓ ML
      (Option Bool)) (Option Bool)) :=
  (flip bind (TM1.step (tr mixM)))^[n] (some (TM1.init (trInit true [true, false])))

/-- **The step simulated in exactly `22` steps**, within `1 + 5 (2 (2 + 5) + 2) = 81`. -/
example : (mixAfter 22).map (fun c => (isDone c.l, c.var, stackOf c.Tape true 3,
    stackOf c.Tape false 3)) =
      some (true, some true, [some false, none, none], [some true, some false, none]) := by
  decide +kernel

example : 22 ≤ 1 + acts (mixM .start) * (2 * (2 + acts (mixM .start)) + 2) := by
  decide

/-- **Negative control**: not at `done` before `22` steps. -/
example : ∀ n < 22, (mixAfter n).map (fun c => isDone c.l) = some false := by
  decide +kernel

end GraphIsoChecks.TM2Sim
