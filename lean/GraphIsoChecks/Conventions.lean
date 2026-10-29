module

public import GraphIso
meta import GraphIso
public import Mathlib.Data.Fin.VecNotation
meta import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Perm
meta import Mathlib.Data.Fintype.Perm
import all Init.Data.Array.Basic
import all Init.Data.List.Sort.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Mathlib.Data.List.Sort

/-!
# Phase 0 checks: composition and relabelling conventions

Executable and kernel-checked examples showing that `g * h` means "first `h`, then `g`",
that the two orders differ, and that `relabel g` moves the symbol at `u` to `g u`.
-/

@[expose] public section

namespace GraphIsoChecks.Conventions

open Equiv GraphIso

/-- The transposition of `0` and `1`. -/
def s01 : Perm (Fin 3) := swap 0 1
/-- The transposition of `1` and `2`. -/
def s12 : Perm (Fin 3) := swap 1 2
/-- The 3-cycle `0 ↦ 1 ↦ 2 ↦ 0`, obtained as `s01 * s12`. -/
def c : Perm (Fin 3) := s01 * s12

-- `(g * h) u = g (h u)`: apply `s12` first.
example : (s01 * s12) 1 = 2 := by decide
example : (s12 * s01) 1 = 0 := by decide
example : s01 * s12 ≠ s12 * s01 := by decide

-- The same facts, evaluated by the compiler.
#guard (s01 * s12) 1 == 2
#guard (s12 * s01) 1 == 0
#guard (s01 * s12) 0 == 1 && (s01 * s12) 2 == 0

example : c 0 = 1 ∧ c 1 = 2 ∧ c 2 = 0 := by decide
example : c⁻¹ 1 = 0 := by decide

/-- A string with three distinct symbols. -/
def abc : Fin 3 → Fin 3 := ![0, 1, 2]

-- `relabel g x` moves the symbol at `u` to `g u`: `(relabel g x) u = x (g⁻¹ u)`.
example : relabel c abc = ![2, 0, 1] := by decide
example : ∀ u, relabel c abc (c u) = abc u := by decide

-- Relabelling is an action for the composition order: `relabel (g * h) = relabel g ∘ relabel h`,
-- and the two orders give different strings.
example : relabel (s01 * s12) abc = relabel s01 (relabel s12 abc) := relabel_mul _ _ _
example : relabel (s01 * s12) abc ≠ relabel (s12 * s01) abc := by decide

-- `Matches` is stated without inverses, and agrees with relabelling on the full domain.
example : Matches Set.univ c abc (relabel c abc) := matches_univ_iff.2 rfl
example : Matches Set.univ c abc ![2, 0, 1] := by decide
example : ¬ Matches Set.univ c⁻¹ abc ![2, 0, 1] := by decide

-- Normalizing a representative moves it onto the target: `σ * g` matches `x` to `y`
-- exactly when `g` matches `x` to `y ∘ σ`.
example : Matches Set.univ (s01 * s12) abc ![2, 0, 1] ↔
    Matches Set.univ s12 abc (fun u => (![2, 0, 1] : Fin 3 → Fin 3) (s01 u)) :=
  matches_mul_iff

end GraphIsoChecks.Conventions
