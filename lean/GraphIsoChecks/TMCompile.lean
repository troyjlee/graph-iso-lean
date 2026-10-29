module

public import GraphIso.TM.Compile
import all Init.Data.Array.Basic
import all Init.Data.List.Sort.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Mathlib.Data.List.Sort

/-!
# Checks of stage 17e: the compiler

`PLAN-17.md` §8. The primitives are stage 17f; the runs below use `pcDemo`, code for the few
primitives the test programs need (`nil`, `none`, `natLit`, `some`, `cons`, `pair`, `fst`,
`snd`), written for these runs only.

* **Kernel runs of compiled programs** (`testProg`: load the input, bind it at level `0`, run
  the compiled entry, write the result), with the output, all other stacks but `heap` and
  `cnt` empty, empty registers and exact step counts:
  - `revFold`, a fold (reverse `[1, 2, 3]`): `47016` steps;
  - `copyRec`, a recursive procedure with case analysis on lists (copy `[1, 2, 3]`): `41434`;
  - `revLoop`, a loop whose state is a pair (reverse `[1, 2]`): `81340`;
  - `optBr`, case analysis on an option and a branch, on `some true`, `some false` and `none`:
    `2206`, `2242` and `1078` steps.
* **The compiled code** of `revFold` (`comp_revFold`): the levels of the fold.
* **Sizes**: `psize` of the test programs.
* **Environments**: `fetchLv` copies a level of a concrete frame.
* **The size invariant** `HeapBnd` on a concrete heap, the heap-length bound there, and
  `HeapBnd.of_length`.
* `copyRec_wf`, the well-formedness of `copyRec`, and the oracle `O₀`, for the simulation
  theorem on a concrete program with the primitives' code (`TMPrims.copy_spec`, stage 17f).
* **Negative controls**: a wrong step count, a wrong output, a wrong branch, heaps that break
  `HeapBnd`.
-/

@[expose] public section

namespace GraphIsoChecks.TMCompile

open GraphIso.TM GraphIso.Cost Function

/-! ### Code for a few primitives (for these runs only; the primitives are stage 17f) -/

/-- Allocate a cell with the pointer on `work` as its one field. -/
def alloc1 (tg : Tag) : Code Stk Sym Rg Bool :=
  .seq (moveNum2 .work .t1 .t0) (.seq (.act (.push .work (.mk 2)))
    (.seq (moveNum2 .t1 .work .t0) (alloc tg)))

/-- Allocate a cell with the two pointers on `work` (the second on top) as its fields. -/
def alloc2 (tg : Tag) : Code Stk Sym Rg Bool :=
  .seq (moveNum2 .work .t1 .t0) (.seq (moveNum2 .work .t2 .t0) (.seq (.act (.push .work (.mk 2)))
    (.seq (moveNum2 .t1 .work .t0) (.seq (moveNum2 .t2 .work .t0) (alloc tg)))))

/-- The first (`true`) or second field of the pair whose pointer is on `work`. -/
def proj (first : Bool) : Code Stk Sym Rg Bool :=
  .seq (moveNum2 .work .ptr .t0) (.seq fetchCell (.seq (.act (.set 1 none))
    (if first then .seq (moveNum2 .work .t1 .t0) (.seq (dropNum .work)
        (.seq closeCell (moveNum2 .t1 .work .t0)))
      else .seq (dropNum .work) (.seq (moveNum2 .work .t1 .t0)
        (.seq closeCell (moveNum2 .t1 .work .t0))))))

/-- Code for the primitives the test programs use (`skip` for the others). -/
def pcDemo : {args : List Ty} → {t : Ty} → Prim args t → Code Stk Sym Rg Bool
  | _, _, .nil => alloc0 .nil
  | _, _, .none => alloc0 .none
  | _, _, .natLit k => .seq (.act (.push .work (.mk 2))) (.seq (pushNum (toBits k) .work)
      (alloc .nat))
  | _, _, .some => alloc1 .some
  | _, _, .cons => alloc2 .cons
  | _, _, .pair => alloc2 .pair
  | _, _, .fst => proj true
  | _, _, .snd => proj false
  | _, _, _ => .skip

/-! ### Test programs -/

/-- Reverse a list with a fold. -/
def revFold (rec : Ty × Ty) (var : Ty → Type) (xs : var (.list .nat)) :
    Prog Signature.empty rec var (.list .nat) :=
  .bind (.op0 .nil) fun n => .foldList xs n fun acc x => .op2 .cons x acc

/-- Copy a list by recursion. -/
def copyRec : Proc Signature.empty (.list .nat) (.list .nat) := fun _ l =>
  .caseList l (.op0 .nil) fun x xs => .bind (.recur xs) fun r => .op2 .cons x r

/-- Reverse a list with a loop whose state is a pair (remaining, reversed so far). -/
def revLoop (rec : Ty × Ty) (var : Ty → Type) (xs : var (.list .nat)) :
    Prog Signature.empty rec var (.list .nat) :=
  .bind (.op0 .nil) fun n => .bind (.op2 .pair xs n) fun s₀ =>
  .bind (.loop s₀ fun s => .bind (.op1 .fst s) fun r => .bind (.op1 .snd s) fun acc =>
      .caseList r (.op0 .none) fun y ys => .bind (.op2 .cons y acc) fun acc' =>
        .bind (.op2 .pair ys acc') fun s' => .op1 .some s') fun fin =>
  .op1 .snd fin

/-- Case analysis on an optional Boolean, then a branch. -/
def optBr (rec : Ty × Ty) (var : Ty → Type) (o : var (.option .bool)) :
    Prog Signature.empty rec var .nat :=
  .caseOption o (.op0 (.natLit 0)) fun x => .ite x (.op0 (.natLit 1)) (.op0 (.natLit 2))

/-- The machine for an entry `E` and a procedure `Pr` (the procedure `true`): `main` loads an
input of type `a`, binds it at level `0`, runs the compiled entry, drops the level and writes
the result. -/
def testProg {a b c : Ty} (Pr : Proc Signature.empty a b)
    (E : (var : Ty → Type) → var a → Prog Signature.empty (a, b) var c) :
    Program Stk Sym Rg Bool :=
  ⟨fun q => if q then comp pcDemo true 1 (Pr Lv 0) else
    .seq (load a) (.seq pushEnv (.seq (comp pcDemo true 1 (E Lv 0))
      (.seq popEnv (.seq (moveNum2 .work .ptr .t0) (write c))))), false⟩

/-- The machine with `inp` on the input stack, an empty heap and the counter `0`. -/
def cfgIn (inp : List Sym) : Cfg Stk Sym Rg :=
  ⟨Regs.empty, fun k => match k with
    | .inp => inp
    | .cnt => [.nd]
    | _ => []⟩

/-- Run `main` on a serialized input: the output, the stacks other than `out`, `heap`, `cnt`
(these must be empty), the registers and the step count. -/
def go (prog : Program Stk Sym Rg Bool) (inp : List Sym) :
    Option (List Sym × List (List Sym) × List (Option Sym) × ℕ) :=
  (run prog 10000000 (prog.body false) (cfgIn inp)).map fun r =>
    (r.1.stk .out, [r.1.stk .inp, r.1.stk .scan, r.1.stk .work, r.1.stk .ptr, r.1.stk .env,
      r.1.stk .lst, r.1.stk .t0, r.1.stk .t1, r.1.stk .t2, r.1.stk .t3, r.1.stk .t4],
      [r.1.regs 0, r.1.regs 1, r.1.regs 2, r.1.regs 3], r.2)

/-- A procedure that is never called. -/
def idle : Proc Signature.empty (.list .nat) (.list .nat) := fun _ l => .ret l

/-- Eleven empty stacks. -/
abbrev empty11 : List (List Sym) := [[], [], [], [], [], [], [], [], [], [], []]

/-- **A fold**: `revFold` reverses `[1, 2, 3]`. -/
example : go (testProg idle (revFold _)) (ser (.list .nat) [1, 2, 3]) =
    some (ser (.list .nat) [3, 2, 1], empty11, [none, none, none, none], 47016) := by
  decide +kernel

/-- **Negative control**: not in `47015` steps. -/
theorem revFold_not_47015 : go (testProg idle (revFold _)) (ser (.list .nat) [1, 2, 3]) ≠
    some (ser (.list .nat) [3, 2, 1], empty11, [none, none, none, none], 47015) := by
  decide +kernel

/-- **Recursion**: `copyRec` copies `[1, 2, 3]`. -/
example : go (testProg copyRec fun _ l => .recur l) (ser (.list .nat) [1, 2, 3]) =
    some (ser (.list .nat) [1, 2, 3], empty11, [none, none, none, none], 41434) := by
  decide +kernel

/-- **Negative control**: the copy is not reversed. -/
theorem copyRec_not_rev : (go (testProg copyRec fun _ l => .recur l)
    (ser (.list .nat) [1, 2, 3])).map (·.1) ≠ some (ser (.list .nat) [3, 2, 1]) := by
  decide +kernel

/-- **A loop**: `revLoop` reverses `[1, 2]`. -/
example : go (testProg idle (revLoop _)) (ser (.list .nat) [1, 2]) =
    some (ser (.list .nat) [2, 1], empty11, [none, none, none, none], 81340) := by
  decide +kernel

/-- The procedure for `optBr` (never called). -/
def idleOpt : Proc Signature.empty (.option .bool) .nat := fun _ _ => .op0 (.natLit 0)

/-- **Case analysis and branches**: `optBr` on `some true`, `some false`, `none`. -/
example : go (testProg idleOpt (optBr _)) (ser (.option .bool) (some true)) =
    some (ser .nat 1, empty11, [none, none, none, none], 2206) := by
  decide +kernel

example : go (testProg idleOpt (optBr _)) (ser (.option .bool) (some false)) =
    some (ser .nat 2, empty11, [none, none, none, none], 2242) := by
  decide +kernel

example : go (testProg idleOpt (optBr _)) (ser (.option .bool) none) =
    some (ser .nat 0, empty11, [none, none, none, none], 1078) := by
  decide +kernel

/-- **Negative control**: `some true` does not take the `false` branch. -/
theorem optBr_not_two : (go (testProg idleOpt (optBr _))
    (ser (.option .bool) (some true))).map (·.1) ≠ some (ser .nat 2) := by
  decide +kernel

/-- **The compiled code of `revFold`** at depth `1`: `nil` is bound at level `1`; the fold keeps
the remaining list at level `2`, and its body runs at depth `5` with the accumulator at level `3`
and the element at level `4`. -/
theorem comp_revFold : comp pcDemo true 1 (revFold (.list .nat, .list .nat) Lv 0) =
    .seq (.seq .skip (alloc0 .nil)) (.seq pushEnv
      (.seq (foldCode 2 0 1 (.seq (.seq (fetchLv 5 4 .work) (.seq (fetchLv 5 3 .work) .skip))
        (alloc2 .cons))) popEnv)) := rfl

/-- **Sizes** of the test programs. -/
example : psize 1 (revFold (.list .nat, .list .nat) Lv 0) = 9 ∧ psize 1 (copyRec Lv 0) = 9 ∧
    psize 1 (revLoop (.list .nat, .list .nat) Lv 0) = 37 ∧
    psize 1 (optBr (.option .bool, .nat) Lv 0) = 14 := by
  decide +kernel

/-! ### Environments -/

/-- A frame of depth `3`, levels `[1]`, `[0, 1]` and `[]`. -/
def frame3 : List (List Bool) := [[true], [false, true], []]

/-- **`fetchLv`** copies the level `1` of the frame onto `work` and restores `env`. -/
example : (run (testProg idle (revFold _)) 1000 (fetchLv 3 1 .work)
    ⟨Regs.empty, fun k => if k = .env then envEnc frame3 else []⟩).map
      (fun r => (r.1.stk .work, r.1.stk .env, r.1.stk .t1, r.2)) =
    some (bits [false, true] ++ [.nd], envEnc frame3, [], 93) := by
  decide +kernel

/-! ### The size invariant -/

/-- A heap of three cells: the natural `1`, `nil`, and `cons` of the two. -/
def h₀ : List Cell :=
  [⟨[], .nat, [[true]]⟩, ⟨[true, false], .nil, []⟩, ⟨[false, true, false], .cons, [[], [true]]⟩]

theorem h₀_bnd : HeapBnd 1 2 h₀ := by
  unfold HeapBnd; decide +kernel

/-- **Negative controls**: the natural needs `B ≥ 1`, the `cons` cell `F ≥ 2`. -/
theorem h₀_not_bnd : ¬ HeapBnd 0 2 h₀ ∧ ¬ HeapBnd 1 1 h₀ := by
  unfold HeapBnd; decide +kernel

/-- The heap-length bound on `h₀`: `22 ≤ 3 * (1 + 3 + 4 + 2 * (1 + 3 + 1))`. -/
example : (encHeap h₀).length = 22 ∧ (encHeap h₀).length ≤ 54 :=
  ⟨by decide +kernel, (length_encHeap_le_bnd h₀_bnd).trans (by decide +kernel)⟩

/-- Every heap satisfies the invariant for `B` and `F` at least its length in symbols. -/
example : HeapBnd 22 22 h₀ := HeapBnd.of_length (by decide +kernel) (by decide +kernel)

/-! ### For the simulation theorem on a concrete program (stage 17f, `TMPrims`) -/

/-- The oracle of the empty signature. -/
def O₀ : Oracle Signature.empty := ⟨fun op => (op : Empty).elim⟩

theorem copyRec_wf : Proc.Wf copyRec := fun _ _ _ _ => by
  unfold copyRec; prog_wf

end GraphIsoChecks.TMCompile
