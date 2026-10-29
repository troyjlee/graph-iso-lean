module

public import GraphIsoChecks.MainSteps
public import GraphIso.Main.SimsM5Ns
public import GraphIso.Main.Full
import all Init.Data.Array.Basic
import all Init.Data.List.Sort.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Mathlib.Data.List.Sort

/-!
# Checks of stage 14j-6b-1: the steps without stuck orbits

`PLAN-14.md` §14.11 item 7, by kernel `decide` on small data.

* **The partition bound of item 1** on a fixture: the singleton partition of `Fin 3` (each point
  its own colour) is a colored `1`-partition; extended along `Fin 3 ↪ Fin 7` (`extPart`), its
  blocks have at most `max 1 (7 − 3) = 4` points (`extPart_partLe`), and the complement block
  attains the bound.
* **The union bound of item 4**, on 14j-6a's fixture (the labels of `fRD5` through the cells of
  `cj12`): the union label at the first point has `4 ≤ labLen L · λ(12) = 2 · 3` entries
  (`ss_union_le_lab`), with the Johnson parameter `s = 2 ≤ λ(12) = 3` (`s_le_lam`).
* **No `m!`** (item 6), at `m = 3000`, `k = 5`, `uB = 4`, `jB = 3`, `j = 3`, `sIn = 0`: M5's
  factor bound `m5FBns` and its `Lg` bound `ssLgM5Ns`, and M4's `ssLgM4Ns`, are below `m!`.
  A negative control: the bounds with stuck orbits (`m5FB`, `ssLgM5`, `ssLgM4`) are not.
  The crossover is large because Split-or-Johnson's count `2^(129 (⌈log₂ m⌉ + 2)²)` is in every
  bound: at `m = 2048` it still exceeds `m!`.
-/

@[expose] public section

namespace GraphIsoChecks.NoStuck

open Equiv Finset GraphIso GraphIso.Main GraphIso.Toolkit GraphIso.Recursion GraphIso.SplitJohnson
  GraphIso.Case2b GraphIsoChecks.MainSteps

/-! ### The partition bound -/

/-- The singleton partition of `Fin 3`, each point its own colour (admissible). -/
def pfix : CPart (Fin 3) := ⟨fun v => v.val, fun v => {v}⟩

/-- `Fin 3` in `Fin 7`. -/
def efix : Fin 3 ↪ Fin 7 := Fin.castLEEmb (by decide)

/-- The singleton partition is a colored `1`-partition. -/
theorem pfix_valid : IsColPart univ 1 pfix where
  mem_blk := by decide +kernel
  blk_sub := by decide +kernel
  blk_eq := by decide +kernel
  col_eq := by decide +kernel
  card_eq := by decide +kernel
  admissible := by decide +kernel
  card_le := by decide +kernel

/-- **Item 1's bound on the fixture**: the extension is a colored `t`-partition with
`t ≤ max 1 (7 − 3)`. -/
example : ∃ t ≤ max 1 (7 - 3), IsColPart univ t (extPart efix pfix) :=
  extPart_partLe efix pfix_valid le_rfl

/-- The blocks of the extension have at most `4` points, and the complement block has `4`. -/
example : (∀ v : Fin 7, ((extPart efix pfix).blk v).card ≤ 4) ∧
    ∃ v : Fin 7, ((extPart efix pfix).blk v).card = 4 := by decide +kernel

/-! ### The union bound -/

/-- **Item 4's bound on 14j-6a's fixture**: the union label at the first point of the orbit
`[0, 1, 2, 3]` has `4` entries, at most `labLen L · λ(12) = 6`; the Johnson parameter is
`2 ≤ λ(12) = 3`. -/
example : (((labJUD cj12.1.2.1.length (markArr 12 cj12.1.1) cj12.1.2.2.2
      #[[1, 4], [1, 4], [2, 3], [2, 3]] [0, 1, 2, 3]).getD 0 []).length == 4 &&
    decide (4 ≤ labLen #[[1, 4], [1, 4], [2, 3], [2, 3]] * lam 12) &&
    decide (cj12.1.2.2.1 ≤ lam 12) && lam 12 == 3) = true := by decide +kernel

/-! ### No factorial of the base size -/

/-- **M5's factor and `Lg` bounds without stuck orbits are below `m!`** at `m = 3000`. -/
example : m5FBns 3000 5 4 3 < Nat.factorial 3000 ∧ ssLgM5Ns 3000 5 4 3 0 < Nat.factorial 3000 :=
  ⟨by decide +kernel, by decide +kernel⟩

/-- **M4's `Lg` bound without stuck orbits is below `m!`** at `m = 3000`, `j = 3`, `uB = 4`. -/
example : ssLgM4Ns 3000 3 4 0 < Nat.factorial 3000 := by decide +kernel

/-- **A negative control**: the bounds with stuck orbits are at least `m!`. -/
example : Nat.factorial 3000 ≤ m5FB 3000 5 ∧ Nat.factorial 3000 ≤ ssLgM5 3000 5 0 ∧
    Nat.factorial 3000 ≤ ssLgM4 3000 3 0 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

end GraphIsoChecks.NoStuck
