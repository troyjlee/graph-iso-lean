module

public import GraphIso.TM.SingleTape.TM1Sim
import all Init.Data.Array.Basic
import all Init.Data.List.Sort.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Mathlib.Data.List.Sort

/-!
# Checks of stage 18d: machines with local state on one tape, counted, with finite control

`PLAN-18.md` §5. This module does not import the graph-isomorphism development.

* **The machine** (`walkM`, alphabet and local state `Bool`, one label): it loads the scanned
  symbol into its state and branches on it; on `true` it writes `false` and moves right, on
  `false` it moves left, writes `true` and halts. Every statement has size `3`
  (`walk_size`), and the single label supports it (`walk_supports`).
* **Exact counts against the bound**: on `[true, true]` the machine takes `3` steps and its
  translation `TM1to0.tr walkM` exactly `9 = 3 · 3` transitions, to the same tape, halting
  (`walk_run`, `walk_tr_run`, by kernel reduction); the restriction to the reachable states,
  `FinTM0.ofTM1 walkM walk_supports`, takes the same `9` transitions. On `[false]` it outputs
  `[true, false]` in one step, and `ofTM1_outputs` gives the timed output within `3`, also run by
  the kernel.
* **Negative controls:** the translation has not halted after `8` transitions; no other output
  (`[false, true]`) within any bound; a trailing blank is invisible, so `[true]` is the same
  output as `[true, false]`.
-/

@[expose] public section

namespace GraphIsoChecks.TM1Sim

open Turing StateTransition GraphIso.TM.SingleTape

/-- Load the scanned symbol; on `true` write `false` and move right, on `false` move left, write
`true` and halt. -/
def walkM : Unit → TM1.Stmt Bool Unit Bool
  | () => .load (fun a _ => a) (.branch (fun _ v => v)
      (.write (fun _ _ => false) (.move .right (.goto fun _ _ => ())))
      (.move .left (.write (fun _ _ => true) .halt)))

theorem walk_size (l : Unit) : stmtSize (walkM l) ≤ 3 :=
  le_rfl

theorem walk_supports : ∃ S, TM1.Supports walkM S :=
  ⟨{()}, Finset.mem_singleton_self _, fun _ _ => ⟨fun _ _ => Finset.mem_singleton_self _, trivial⟩⟩

/-- **The machine's run on `[true, true]`**: `3` steps. -/
theorem walk_run : StepsIn (TM1.step walkM) 3 (TM1.init [true, true])
    ⟨none, false, ⟨true, ListBlank.mk [false], ListBlank.mk [false]⟩⟩ :=
  rfl

/-- **The translation's run**: exactly `9 = 3 · 3` transitions to the translated final
configuration, where it halts. -/
theorem walk_tr_run : StepsIn (TM0.step (TM1to0.tr walkM)) 9 (TM0.init [true, true])
    ⟨(none, false), ⟨true, ListBlank.mk [false], ListBlank.mk [false]⟩⟩ :=
  rfl

example : TM0.step (TM1to0.tr walkM)
    ⟨(none, false), ⟨true, ListBlank.mk [false], ListBlank.mk [false]⟩⟩ = none :=
  rfl

/-- `tr1_run` instantiated: at most `3 · 3` transitions. -/
example : ∃ n ≤ 3 * 3, StepsIn (TM0.step (TM1to0.tr walkM)) n (TM0.init [true, true])
    ⟨(none, false), ⟨true, ListBlank.mk [false], ListBlank.mk [false]⟩⟩ :=
  tr1_run walkM walk_size walk_run

/-- **Negative control**: the translation has not halted after `8` transitions. -/
example : ((flip bind (TM0.step (TM1to0.tr walkM)))^[8] (some (TM0.init [true, true]))).map
    (fun c => c.q.1.isSome) = some true :=
  rfl

/-- The finite machine: the translation restricted to its reachable states. -/
abbrev walkTM0 : FinTM0 :=
  FinTM0.ofTM1 walkM walk_supports

example : Finite walkTM0.Λ :=
  inferInstance

/-- **The restriction's run**: the same `9` transitions, to the same tape, halting. -/
example : ∃ h, StepsIn walkTM0.step 9 (TM0.init [true, true])
    ⟨⟨(none, false), h⟩, ⟨true, ListBlank.mk [false], ListBlank.mk [false]⟩⟩ :=
  ⟨_, rfl⟩

/-- **A timed output** on `[false]`: `[true, false]` in one step of `walkM`, so within `3`
transitions (`ofTM1_outputs`). -/
theorem walk_outputs : TM0OutputsInTime walkTM0 [false] [true, false] (1 * 3) :=
  ofTM1_outputs walkM walk_supports walk_size (v := false) rfl

/-- The same timed output, run by the kernel: exactly `3` transitions. -/
example : TM0OutputsInTime walkTM0 [false] [true, false] 3 :=
  ⟨_, 3, le_rfl, rfl, rfl⟩

/-- **Negative control**: no other output, within any bound. -/
example (m : ℕ) : ¬TM0OutputsInTime walkTM0 [false] [false, true] m := fun h => by
  have e := congrArg (fun L : ListBlank Bool => L.nth 0) (walk_outputs.unique h)
  exact absurd e (by decide)

/-- **Negative control**: a trailing blank (`false`) is invisible: `[true]` is the same
output. -/
example : TM0OutputsInTime walkTM0 [false] [true] 3 := by
  have : Tape.mk₁ [true] = Tape.mk₁ [true, false] := by
    change Tape.mk' (ListBlank.mk []) (ListBlank.mk [true]) =
      Tape.mk' (ListBlank.mk []) (ListBlank.mk [true, false])
    rw [show ListBlank.mk [true] = ListBlank.mk [true, false] from
      Quotient.sound (Or.inl ⟨1, rfl⟩)]
  obtain ⟨q, n, hn, hr, hh⟩ := walk_outputs
  exact ⟨q, n, hn, this ▸ hr, this ▸ hh⟩

end GraphIsoChecks.TM1Sim
