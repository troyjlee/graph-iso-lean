module

public import GraphIso.TM.SingleTape.Programs
public import GraphIsoChecks.TM2Sim
public import GraphIsoChecks.TMCode
import all Init.Data.Array.Basic
import all Init.Data.List.Sort.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Mathlib.Data.List.Sort

/-!
# Checks of stage 18d: stack machines on one tape, composed, with finite control

`PLAN-18.md` §5. This module does not import the graph-isomorphism development; it uses the
reversal machine of stage 18c (`GraphIsoChecks.TM2Sim.revTM`) and the negation machine of stage
17a (`GraphIsoChecks.TMCode.negM = toFinTM2 negProg 0 2`, a compiled stack program). The finite
simulators `simTM0` are run by the kernel from mathlib's initial simulator tape and observed
through their tape cells.

* **Reversal** (`simTM0 revTM _`): from `trInit true [true, false]` it halts after exactly `37`
  transitions, the input stack empty and the output stack `true, false` from the bottom, within
  the bound `3 · 312 = 936` of `simTM0_outputs` (instantiated).
* **A compiled stack program** (`simTM0 negM _`, with `finite_toFinTM2`: the symbols and the
  return labels are finite): on `[true, false]` it halts after exactly `161` transitions with
  the output stack holding `[false, true]` and the input stack empty, within
  `3 (2 + 2 + 1) (32 + 2) (2 + 32 + 2) = 18360` (`exec_simTM0` instantiated with the program's
  run of `32` steps); on `[]` after `25`.
* **Negative controls:** neither machine halts earlier; the stacks are stored bottom first.
-/

@[expose] public section

namespace GraphIsoChecks.TMSim

open Turing StateTransition GraphIso.TM.SingleTape GraphIsoChecks.TM2Sim GraphIsoChecks.TMCode

example (l : TM2to1.Λ' Bool BΓ Unit (Option Bool)) : stmtSize (TM2to1.tr revTM.m l) ≤ 3 :=
  stmtSize_tr _ l

/-! ### Reversal -/

theorem revFin : ∀ k, Finite (revTM.Γ k) :=
  fun _ => inferInstanceAs (Finite Bool)

/-- **The finite simulator of the reversal machine.** -/
abbrev revS : FinTM0 :=
  simTM0 revTM revFin

example : Finite revS.Λ ∧ Finite revS.Γ :=
  ⟨inferInstance, inferInstance⟩

/-- The configuration after `n` transitions from mathlib's initial simulator tape. -/
def revAfter (n : ℕ) (x : List Bool) : Option (TM0.Cfg revS.Γ revS.Λ) :=
  (flip bind revS.step)^[n] (some (TM0.init (TM2to1.trInit true x)))

/-- **Halts after exactly `37` transitions**, the input stack empty and the output stack
`true, false` from the bottom. -/
example : (revAfter 37 [true, false]).map (fun c => ((revS.step c).isNone,
    stackOf c.Tape true 3, stackOf c.Tape false 3)) =
      some (true, [none, none, none], [some true, some false, none]) := by
  decide +kernel

/-- **Negative control**: not halted before. -/
example : ∀ n < 37, (revAfter n [true, false]).map (fun c => (revS.step c).isSome) =
    some true := by
  decide +kernel

/-- **`simTM0_outputs` instantiated**: a halting run within `3 · 312`. -/
example : ∃ c n, n ≤ 3 * 312 ∧
    StepsIn revS.step n (TM0.init (TM2to1.trInit true [true, false])) c ∧ revS.step c = none := by
  obtain ⟨L, -, q, n, hn, hr, hh⟩ := simTM0_outputs revTM revFin rev_outputs
  rw [tmActs_revTM] at hn
  exact ⟨_, n, hn, hr, hh⟩

/-! ### A compiled stack program -/

/-- **The finite simulator of the compiled negation program.** -/
abbrev negS : FinTM0 :=
  simTM0 negM (GraphIso.TM.finite_toFinTM2 negProg 0 2)

example : Finite negS.Λ ∧ Finite negS.Γ :=
  ⟨inferInstance, inferInstance⟩

/-- The configuration after `n` transitions from mathlib's initial simulator tape. -/
def negAfter (n : ℕ) (x : List Bool) : Option (TM0.Cfg negS.Γ negS.Λ) :=
  (flip bind negS.step)^[n] (some (TM0.init (TM2to1.trInit (some 0) x)))

/-- The entry of stack `k` in a cell of the simulator's tape. -/
def entry (a : TM2to1.Γ' negM.K negM.Γ) (k : Fin 3) : Option Bool :=
  a.2 (some k)

/-- The entries of stack `k` in the first `n` cells, bottom first. -/
def negStack (T : Tape (TM2to1.Γ' negM.K negM.Γ)) (k : Fin 3) (n : ℕ) : List (Option Bool) :=
  (List.range n).map fun i => entry (T.nth i) k

/-- **Halts after exactly `161` transitions**, the output stack `2` holding `[false, true]`
(bottom first: `true, false`), the input stack `0` empty. -/
example : (negAfter 161 [true, false]).map (fun c => ((negS.step c).isNone,
    negStack c.Tape 0 3, negStack c.Tape 2 3)) =
      some (true, [none, none, none], [some true, some false, none]) := by
  decide +kernel

/-- **Negative control**: not halted before. -/
example : ∀ n < 161, (negAfter n [true, false]).map (fun c => (negS.step c).isSome) =
    some true := by
  decide +kernel

/-- The empty input: `25` transitions. -/
example : (negAfter 25 []).map (fun c => ((negS.step c).isNone, negStack c.Tape 2 1)) =
    some (true, [none]) := by
  decide +kernel

theorem tmActs_negM : tmActs negM = 1 := by
  decide +kernel

/-- **`exec_simTM0` instantiated** with the program's run of `12 · 2 + 8 = 32` steps: a halting
run within `3 (2 + 2 + 1) (32 + 2) (2 + 32 + 2) = 18360`. -/
example : ∃ c m, m ≤ 18360 ∧
    StepsIn negS.step m (TM0.init (TM2to1.trInit (some 0) [true, false])) c ∧
      negS.step c = none := by
  obtain ⟨L, -, q, m, hm, hr, hh⟩ := GraphIso.TM.exec_simTM0 negProg 0 2 (main_exec [true, false])
  rw [tmActs_negM] at hm
  exact ⟨_, m, hm, hr, hh⟩

end GraphIsoChecks.TMSim
