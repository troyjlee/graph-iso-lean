module

public import GraphIso.TM.Arith
import all Init.Data.Array.Basic
import all Init.Data.List.Sort.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Mathlib.Data.List.Sort

/-!
# Checks of stage 17b: numbers and arithmetic on stacks

`PLAN-17.md` §5.

* **Kernel runs** of the routines on concrete numbers, with the final stacks, registers and
  exact step counts: `11 + 6 = 17` in `129` steps (the bound of `addNum_sat`, attained),
  truncated `3 - 5 = 0` and `13 - 5 = 8`, `5 < 13`, equality of the non-canonical `[1]` and
  `[1, 0, 0]` (both `1`) and inequality of `1` and `2`, `7 + 1`, `0 - 1 = 0`, copying, moving a
  segment and erasing a stack.
* **The specifications on a concrete input**: `addNum_sat` and `eqNum_sat` give the values
  directly (`add_spec`, `eq_spec`).
* **Negative control**: `addNum` on `11 + 6` cannot finish within `128` steps (`add_not_128`),
  so the bound of `addNum_sat` cannot be lowered.
-/

@[expose] public section

namespace GraphIsoChecks.TMArith

open GraphIso.TM Function

/-- A program running one routine. -/
def prog1 (x : Code (Fin 4) Sym Rg Unit) : Program (Fin 4) Sym Rg Unit := ⟨fun _ => x, ()⟩

/-- A configuration with empty registers. -/
def cfg (s₀ s₁ s₂ s₃ : List Sym) : Cfg (Fin 4) Sym Rg := ⟨Regs.empty, ![s₀, s₁, s₂, s₃]⟩

/-- A number on a stack. -/
def num (l : List Bool) : List Sym := bits l ++ [.nd]

/-- Run a routine: the four stacks, the four registers and the step count. -/
def go (x : Code (Fin 4) Sym Rg Unit) (c : Cfg (Fin 4) Sym Rg) :
    Option (List (List Sym) × List (Option Sym) × ℕ) :=
  (run (prog1 x) 2000 x c).map fun r =>
    ([r.1.stk 0, r.1.stk 1, r.1.stk 2, r.1.stk 3], [r.1.regs 0, r.1.regs 1, r.1.regs 2, r.1.regs 3],
      r.2)

/-- Empty registers. -/
abbrev none4 : List (Option Sym) := [none, none, none, none]

/-- `11 + 6 = 17`, in `23 · 4 + 37 = 129` steps. -/
example : go (addNum 0 1 2 3) (cfg (num [true, true, false, true]) (num [false, true, true]) [] [])
    = some ([[], [], num [true, false, false, false, true], []], none4, 129) := by
  decide +kernel

/-- Truncated `3 - 5 = 0` (the empty bit list). -/
example : go (subNum 0 1 2 3) (cfg (num [true, true]) (num [true, false, true]) [] [])
    = some ([[], [], num [], []], none4, 91) := by
  decide +kernel

/-- `13 - 5 = 8`. -/
example : go (subNum 0 1 2 3) (cfg (num [true, false, true, true]) (num [true, false, true]) [] [])
    = some ([[], [], num [false, false, false, true], []], none4, 128) := by
  decide +kernel

/-- `5 < 13`. -/
example : go (ltNum 0 1 2 3) (cfg (num [true, false, true]) (num [true, false, true, true]) [] [])
    = some ([[], [], [.bit true], []], none4, 109) := by
  decide +kernel

/-- `¬ 13 < 5`. -/
example : go (ltNum 0 1 2 3) (cfg (num [true, false, true, true]) (num [true, false, true]) [] [])
    = some ([[], [], [.bit false], []], none4, 109) := by
  decide +kernel

/-- Equality of non-canonical bit lists: `[1]` and `[1, 0, 0]` both stand for `1`. -/
example : go (eqNum 0 1 2 3) (cfg (num [true]) (num [true, false, false]) [] [])
    = some ([[], [], [.bit true], []], none4, 91) := by
  decide +kernel

/-- `1 ≠ 2`. -/
example : go (eqNum 0 1 2 3) (cfg (num [true]) (num [false, true]) [] [])
    = some ([[], [], [.bit false], []], none4, 72) := by
  decide +kernel

/-- `7 + 1 = 8`. -/
example : go (incNum 0 1 2 3) (cfg (num [true, true, true]) [] [] [])
    = some ([[], [], num [false, false, false, true], []], none4, 110) := by
  decide +kernel

/-- Truncated `0 - 1 = 0`. -/
example : go (decNum 0 1 2 3) (cfg (num []) [] [] []) = some ([[], [], num [], []], none4, 57) := by
  decide +kernel

/-- Copying a number keeps the source and the temporary stack. -/
example : go (copyNum 0 1 2) (cfg (num [true, false, true]) [.nd] [.mk 1] [])
    = some ([num [true, false, true], num [true, false, true] ++ [.nd], [.mk 1], []], none4, 63)
    := by
  decide +kernel

/-- Moving a segment up to the first `mk 0` reverses it. -/
example : go (moveSeg (.mk 0) 0 1) (cfg [.nd, .bit true, .tag .pair, .mk 0, .mk 1] [.nd] [] [])
    = some ([[.mk 1], [.mk 0, .tag .pair, .bit true, .nd, .nd], [], []], none4, 19) := by
  decide +kernel

/-- Erasing a stack. -/
example : go (erase 0) (cfg [.nd, .bit true, .mk 0] [.nd] [] [])
    = some ([[], [.nd], [], []], none4, 11) := by
  decide +kernel

/-- The input of the addition. -/
def cAdd : Cfg (Fin 4) Sym Rg := cfg (num [true, true, false, true]) (num [false, true, true]) [] []

/-- **The specification on a concrete input**: `addNum_sat` gives `17` within `129` steps. -/
theorem add_spec : Sat (prog1 (addNum 0 1 2 3)) (addNum 0 1 2 3) cAdd 129 fun c' =>
    c'.stk 2 = num [true, false, false, false, true] := by
  refine (addNum_sat (xs := [true, true, false, true]) (ys := [false, true, true]) (ra := [])
    (rb := []) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl
    rfl).mono le_rfl fun c' ⟨_, _, _, h, _⟩ => ?_
  rw [h]
  decide +kernel

/-- `eqNum_sat` decides equality of the values, whatever the lengths. -/
theorem eq_spec : Sat (prog1 (eqNum 0 1 2 3)) (eqNum 0 1 2 3)
    (cfg (num [true]) (num [true, false, false]) [] []) 91 fun c' => c'.stk 2 = [.bit true] := by
  refine (eqNum_sat (xs := [true]) (ys := [true, false, false]) (ra := []) (rb := [])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl
    rfl).mono le_rfl fun c' ⟨_, _, _, h, _⟩ => ?_
  rw [h]
  decide +kernel

/-- **Negative control**: the addition does not finish within `128` steps. -/
theorem add_not_128 : ¬ Sat (prog1 (addNum 0 1 2 3)) (addNum 0 1 2 3) cAdd 128 fun _ => True := by
  rintro ⟨c', n, e, hn, -⟩
  have h₁ := run_of_exec e 2000 (by omega)
  have h₂ : (run (prog1 (addNum 0 1 2 3)) 2000 (addNum 0 1 2 3) cAdd).map Prod.snd = some 129 := by
    decide +kernel
  rw [h₁] at h₂
  simp only [Option.map_some, Option.some.injEq] at h₂
  omega

end GraphIsoChecks.TMArith
