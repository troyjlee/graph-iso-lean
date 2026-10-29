module

public import GraphIso.TM.Main
public import GraphIsoChecks.TMPrims
import all Init.Data.Array.Basic
import all Init.Data.List.Sort.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Mathlib.Data.List.Sort

/-!
# Checks of stage 17g: the simulation on Turing machines

`PLAN-17.md` §10.

* **Kernel runs of `main`** (`mainProg`: initialize the counter, load the input, run the compiled
  entry, make the result's pointer canonical, write the result, erase `heap` and `cnt`) from the
  input configuration `inCfg .inp`, with the output, every other stack (including `heap` and
  `cnt`) empty, empty registers and exact step counts:
  - `copyRec` (recursion) on `[1, 2, 3]`: `42340` steps;
  - `natOps` on `(5, 3)`: `45410`; `listOps` on `[1, 2, 3]`: `67665`;
  - `share` (`pair x x`, twice: two units of local cost, an output four times as long as the
    input) on `[1, 2, 3]`: `102694`.
* **`canonPtr`** on a pointer with a high zero bit: `75` steps.
* **Sharing in the cost model** (`square`, `m` copies of one list of `m` numbers): at `m = 20`,
  local cost `62` and an input of `6` symbols, but an output of `2221` symbols (more than
  `m² = 400`). This is why the bound of `main_exec` involves the output's length.
* **The theorems instantiated** on `copyRec` and the input `[1, 2, 3]` (local cost `12`): the
  run of `main_exec` within `mainPoly = 7577600 ^ 120` steps, and the machine of `main_tm`, whose
  step count (computed by the interpreter) is `42341`.
* **Negative controls**: a wrong step count, a wrong output.
-/

@[expose] public section

namespace GraphIsoChecks.TMMain

open GraphIso.TM GraphIso.Cost GraphIsoChecks.TMCompile GraphIsoChecks.TMPrims

/-- Run `main` from the input configuration of a serialized input: the output, the other
thirteen stacks, the registers and the step count. -/
def goMain (prog : Program Stk Sym Rg Bool) (inp : List Sym) :
    Option (List Sym × List (List Sym) × List (Option Sym) × ℕ) :=
  (run prog 10000000 (prog.body prog.main) (inCfg .inp inp)).map fun r =>
    (r.1.stk .out, [r.1.stk .inp, r.1.stk .heap, r.1.stk .scan, r.1.stk .cnt, r.1.stk .work,
      r.1.stk .ptr, r.1.stk .env, r.1.stk .lst, r.1.stk .t0, r.1.stk .t1, r.1.stk .t2,
      r.1.stk .t3, r.1.stk .t4], [r.1.regs 0, r.1.regs 1, r.1.regs 2, r.1.regs 3], r.2)

/-- Thirteen empty stacks. -/
abbrev empty13 : List (List Sym) := [[], [], [], [], [], [], [], [], [], [], [], [], []]

theorem same_wf (a : Ty) : Proc.Wf (same a) := fun _ _ _ _ => by unfold same; prog_wf

/-- `(pair x x, pair x x)`: an output four times as long as the input, for two units of local
cost. -/
def share (rec : Ty × Ty) (var : Ty → Type) (xs : var (.list .nat)) :
    Prog Signature.empty rec var
      (.prod (.prod (.list .nat) (.list .nat)) (.prod (.list .nat) (.list .nat))) :=
  .bind (.op2 .pair xs xs) fun p => .op2 .pair p p

/-- The main programs. -/
def copyMain : Program Stk Sym Rg Bool := mainProg ⟨copyRec, copyRec_wf⟩ fun _ l => .recur l

def natMain : Program Stk Sym Rg Bool := mainProg ⟨same (.prod .nat .nat), same_wf _⟩ (natOps _)

def listMain : Program Stk Sym Rg Bool := mainProg ⟨same (.list .nat), same_wf _⟩ (listOps _)

def shareMain : Program Stk Sym Rg Bool := mainProg ⟨same (.list .nat), same_wf _⟩ (share _)

/-! ### Runs of `main` -/

/-- **Recursion**: `copyRec` copies `[1, 2, 3]`; every stack but `out` ends empty. -/
example : goMain copyMain (ser (.list .nat) [1, 2, 3]) =
    some (ser (.list .nat) [1, 2, 3], empty13, [none, none, none, none], 42340) := by
  decide +kernel

/-- **Negative control**: not in `42339` steps. -/
theorem copyMain_not_42339 : goMain copyMain (ser (.list .nat) [1, 2, 3]) ≠
    some (ser (.list .nat) [1, 2, 3], empty13, [none, none, none, none], 42339) := by
  decide +kernel

/-- **Negative control**: not the reversed list. -/
theorem copyMain_not_rev : (goMain copyMain (ser (.list .nat) [1, 2, 3])).map Prod.fst ≠
    some (ser (.list .nat) [3, 2, 1]) := by
  decide +kernel

/-- **Arithmetic and comparisons.** -/
example : goMain natMain (ser (.prod .nat .nat) (5, 3)) =
    some (ser (.prod .nat (.prod .nat (.prod .bool .bool))) (8, 2, false, false), empty13,
      [none, none, none, none], 45410) := by
  decide +kernel

/-- **Lists.** -/
example : goMain listMain (ser (.list .nat) [1, 2, 3]) =
    some (ser (.prod .nat (.list .nat)) (3, [3, 2, 1]), empty13, [none, none, none, none],
      67665) := by
  decide +kernel

/-- **Sharing**: the output is written out in full. -/
example : goMain shareMain (ser (.list .nat) [1, 2, 3]) =
    some (ser (.prod (.prod (.list .nat) (.list .nat)) (.prod (.list .nat) (.list .nat)))
      (([1, 2, 3], [1, 2, 3]), ([1, 2, 3], [1, 2, 3])), empty13, [none, none, none, none],
      102694) := by
  decide +kernel

/-! ### Canonical pointers -/

/-- **`canonPtr`** drops the high zero bits of `4 = 0b100` written as `0010` (least significant
bit first), and leaves `t0` empty. -/
example : (run copyMain 100 canonPtr
      (inCfg .ptr (bits [false, false, true, false] ++ [.nd]))).map
      (fun r => (r.1.stk .ptr, r.1.stk .t0, r.1.regs 0, r.2)) =
    some (bits [false, false, true] ++ [.nd], [], none, 75) := by
  decide +kernel

/-! ### Sharing -/

/-- `m` copies of the list `[0, …, m - 1]`, all sharing its cells. -/
def square (rec : Ty × Ty) (var : Ty → Type) (m : var .nat) :
    Prog Signature.empty rec var (.list (.list .nat)) :=
  .bind (.op1 .range m) fun xs => .bind (.op0 .nil) fun e =>
    .foldList xs e fun acc _ => .op2 .cons xs acc

/-- **Sharing**: at `m = 20`, local cost `62` and an input of `6` symbols, but an output of `2221`
symbols, more than `20² = 400`. -/
example : (eval O₀ (same .nat Ty.denote) 100 (square _ Ty.denote 20)).map
      (fun r => (r.2.localCost, (ser .nat 20).length, (ser (.list (.list .nat)) r.1).length)) =
    some (62, 6, 2221) := by
  decide +kernel

/-! ### The theorems on a concrete program -/

/-- The trace of `copyRec` on `[1, 2, 3]`. -/
def trCopy : Trace Signature.empty :=
  ((eval O₀ (copyRec Ty.denote) 12 (.recur [1, 2, 3])).map Prod.snd).getD []

theorem copy_runs : Runs O₀ (copyRec Ty.denote) (.recur [1, 2, 3]) [1, 2, 3] trCopy :=
  ⟨12, rfl⟩

example : trCopy.localCost = 12 ∧ (ser (.list .nat) [1, 2, 3]).length = 12 := by
  decide +kernel

theorem copy_entry_wf : ∀ (x₁ : (Ty.list .nat).denote) (x₂ : Lv (.list .nat)),
    Prog.Wf true [⟨.list .nat, x₁, x₂⟩] (Prog.recur (S := Signature.empty)
      (rec := (.list .nat, .list .nat)) x₁) (Prog.recur x₂) :=
  fun _ _ => .recur rfl (List.mem_singleton_self _)

/-- **The time bound evaluated**: `κ = 4096 (3 + 3 + 11 + 31 + 1 + 1) = 204800` and
`C + L + L' + 1 = 37`. -/
theorem copy_bound : mainPoly ⟨copyRec, copyRec_wf⟩ (fun _ l => .recur l) trCopy.localCost
    (ser (.list .nat) [1, 2, 3]).length (ser (.list .nat) [1, 2, 3]).length = 7577600 ^ 120 := by
  decide +kernel

/-- **`main_exec` instantiated**. -/
theorem copy_exec : ∃ n, Exec copyMain (copyMain.body copyMain.main)
    (inCfg .inp (ser (.list .nat) [1, 2, 3])) (inCfg .out (ser (.list .nat) [1, 2, 3])) n ∧
    n ≤ 7577600 ^ 120 := by
  rw [← copy_bound]
  exact main_exec _ _ copy_entry_wf O₀ copy_runs

/-- **`main_tm` instantiated**: the Turing machine of `copyMain`. -/
def copyTM : Turing.TM2OutputsInTime (toFinTM2 copyMain .inp .out) (ser (.list .nat) [1, 2, 3])
    (some (ser (.list .nat) [1, 2, 3])) (mainPoly ⟨copyRec, copyRec_wf⟩ (fun _ l => .recur l)
      trCopy.localCost (ser (.list .nat) [1, 2, 3]).length
      (ser (.list .nat) [1, 2, 3]).length + 1) :=
  main_tm _ _ copy_entry_wf O₀ copy_runs

/-- Its step count, computed by the interpreter. -/
example : copyTM.steps = 42341 := by
  decide +kernel

end GraphIsoChecks.TMMain
