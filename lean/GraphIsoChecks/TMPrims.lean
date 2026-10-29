module

public import GraphIso.TM.Prims
public import GraphIsoChecks.TMCompile
import all Init.Data.Array.Basic
import all Init.Data.List.Sort.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Mathlib.Data.List.Sort

/-!
# Checks of stage 17f: the primitives

`PLAN-17.md` §9.

* **Kernel runs** (`primProg`: load the input, bind it at level `0`, run the entry compiled with
  `primCode`, write the result), with the output, all other stacks but `heap` and `cnt` empty,
  empty registers and exact step counts:
  - `natOps` (`add`, `sub`, `natEq`, `natLt`, `pair`, `fst`, `snd`) on `(5, 3)`, `(3, 5)` and
    `(4, 4)`: `44992`, `44786` and `45140` steps;
  - `boolOps` (`not`, `and`, `or`, `boolLit`) on `(true, false)` and `(false, true)`: `27646`
    and `27582`;
  - `listOps` (`length`, `reverse`) on `[1, 2, 3]`: `67077`; `listOps'` (`append`, `range`,
    `natLit`) on `[1, 2]`: `142792`;
  - `arrOps` (`arrayOfList`, `arraySize`, `arrayGet` in and out of bounds, `arrayMk`,
    `arrayToList`) on `[4, 5, 6]`: `165549`; `updOps` (`arrayUpdate` with an out-of-bounds write,
    `nil`, `cons`) on `[4, 5, 6]`: `251701`;
  - `pairDefault` (the default value of a pair, from an out-of-bounds read): `16626`;
  - `optOps` (`unit`, `none`, `some`, `nil`, `cons`): `38422`;
  - `copyRec` (recursion with case analysis on lists) with `primCode`: `41962`.
* **`primCode_spec`** instantiated.
* **The 17e simulation theorem with `primCode`** (`copy_spec`, replacing the check of the same
  name in `TMCompile`, whose premise `PrimSpec` for `pcDemo` could not hold): `comp_sat` for
  `copyRec` with no premise on the primitives, and a concrete instance (`copy_nil`) whose
  premises are all discharged.
* **Negative controls**: wrong step counts, a wrong result of an out-of-bounds read, an
  out-of-bounds write that does not change the array.
-/

@[expose] public section

namespace GraphIsoChecks.TMPrims

open GraphIso.TM GraphIso.Cost GraphIsoChecks.TMCompile

/-- The machine for an entry `E` and a procedure `Pr` (the procedure `true`), with `primCode`:
`main` loads an input of type `a`, binds it at level `0`, runs the compiled entry, drops the level
and writes the result. -/
def primProg {a b c : Ty} (Pr : Proc Signature.empty a b)
    (E : (var : Ty → Type) → var a → Prog Signature.empty (a, b) var c) :
    Program Stk Sym Rg Bool :=
  ⟨fun q => if q then comp primCode true 1 (Pr Lv 0) else
    .seq (load a) (.seq pushEnv (.seq (comp primCode true 1 (E Lv 0))
      (.seq popEnv (.seq (moveNum2 .work .ptr .t0) (write c))))), false⟩

/-- A procedure that is never called. -/
def same (a : Ty) : Proc Signature.empty a a := fun _ x => .ret x

/-- Arithmetic and comparisons on a pair `(m, n)`: `(m + n, m - n, m = n, m < n)`. -/
def natOps (rec : Ty × Ty) (var : Ty → Type) (x : var (.prod .nat .nat)) :
    Prog Signature.empty rec var (.prod .nat (.prod .nat (.prod .bool .bool))) :=
  .bind (.op1 .fst x) fun m => .bind (.op1 .snd x) fun n =>
  .bind (.op2 .add m n) fun s => .bind (.op2 .sub m n) fun d =>
  .bind (.op2 .natEq m n) fun e => .bind (.op2 .natLt m n) fun l =>
  .bind (.op2 .pair e l) fun el => .bind (.op2 .pair d el) fun del => .op2 .pair s del

/-- Booleans on a pair `(p, q)`: `(¬ p, p ∧ q, p ∨ q, true)`. -/
def boolOps (rec : Ty × Ty) (var : Ty → Type) (x : var (.prod .bool .bool)) :
    Prog Signature.empty rec var (.prod .bool (.prod .bool (.prod .bool .bool))) :=
  .bind (.op1 .fst x) fun p => .bind (.op1 .snd x) fun q =>
  .bind (.op1 .not p) fun np => .bind (.op2 .and p q) fun a => .bind (.op2 .or p q) fun o =>
  .bind (.op0 (.boolLit true)) fun t => .bind (.op2 .pair o t) fun ot =>
  .bind (.op2 .pair a ot) fun aot => .op2 .pair np aot

/-- Lists on `xs`: `(length xs, reverse xs)`. -/
def listOps (rec : Ty × Ty) (var : Ty → Type) (xs : var (.list .nat)) :
    Prog Signature.empty rec var (.prod .nat (.list .nat)) :=
  .bind (.op1 .length xs) fun n => .bind (.op1 .reverse xs) fun r => .op2 .pair n r

/-- Lists on `xs`: `(xs ++ xs, range 3)`. -/
def listOps' (rec : Ty × Ty) (var : Ty → Type) (xs : var (.list .nat)) :
    Prog Signature.empty rec var (.prod (.list .nat) (.list .nat)) :=
  .bind (.op2 .append xs xs) fun a => .bind (.op0 (.natLit 3)) fun k =>
  .bind (.op1 .range k) fun rg => .op2 .pair a rg

/-- Arrays from `xs`: with `a = arrayOfList xs`, `(arraySize a, a[1], a[7], arrayToList
(arrayMk 2 a[0]))`; `a[7]` is out of bounds (the default `0`). -/
def arrOps (rec : Ty × Ty) (var : Ty → Type) (xs : var (.list .nat)) :
    Prog Signature.empty rec var (.prod .nat (.prod .nat (.prod .nat (.list .nat)))) :=
  .bind (.op1 .arrayOfList xs) fun a => .bind (.op1 .arraySize a) fun sz =>
  .bind (.op0 (.natLit 1)) fun one => .bind (.op2 .arrayGet a one) fun g1 =>
  .bind (.op0 (.natLit 7)) fun sev => .bind (.op2 .arrayGet a sev) fun g7 =>
  .bind (.op0 (.natLit 0)) fun zero => .bind (.op2 .arrayGet a zero) fun x₀ =>
  .bind (.op0 (.natLit 2)) fun two => .bind (.op2 .arrayMk two x₀) fun m =>
  .bind (.op1 .arrayToList m) fun ml => .bind (.op2 .pair g7 ml) fun p₃ =>
  .bind (.op2 .pair g1 p₃) fun p₂ => .op2 .pair sz p₂

/-- Array writes on `xs`: `arrayToList (arrayUpdate (arrayOfList xs) [(0, 9), (5, 1), (2, 7)])`;
the write at `5` is out of bounds. -/
def updOps (rec : Ty × Ty) (var : Ty → Type) (xs : var (.list .nat)) :
    Prog Signature.empty rec var (.list .nat) :=
  .bind (.op1 .arrayOfList xs) fun a => .bind (.op0 (.natLit 0)) fun zero =>
  .bind (.op0 (.natLit 9)) fun nine => .bind (.op0 (.natLit 5)) fun five =>
  .bind (.op0 (.natLit 1)) fun one => .bind (.op0 (.natLit 2)) fun two =>
  .bind (.op0 (.natLit 7)) fun sev =>
  .bind (.op2 .pair zero nine) fun w₁ => .bind (.op2 .pair five one) fun w₂ =>
  .bind (.op2 .pair two sev) fun w₃ => .bind (.op0 .nil) fun n₀ =>
  .bind (.op2 .cons w₃ n₀) fun l₃ => .bind (.op2 .cons w₂ l₃) fun l₂ =>
  .bind (.op2 .cons w₁ l₂) fun ws => .bind (.op2 .arrayUpdate a ws) fun u => .op1 .arrayToList u

/-- The default value of a pair: an out-of-bounds read of an array of pairs gives `(0, false)`. -/
def pairDefault (rec : Ty × Ty) (var : Ty → Type) (xs : var (.list (.prod .nat .bool))) :
    Prog Signature.empty rec var (.prod .nat .bool) :=
  .bind (.op1 .arrayOfList xs) fun a => .bind (.op0 (.natLit 3)) fun k => .op2 .arrayGet a k

/-- Options, the unit and lists of options on `x`: `((), none, some x, [some x])`. -/
def optOps (rec : Ty × Ty) (var : Ty → Type) (x : var .nat) :
    Prog Signature.empty rec var
      (.prod .unit (.prod (.option .nat) (.prod (.option .nat) (.list (.option .nat))))) :=
  .bind (.op0 .unit) fun u => .bind (.op0 .none) fun n => .bind (.op1 .some x) fun s =>
  .bind (.op0 .nil) fun e => .bind (.op2 .cons s e) fun l => .bind (.op2 .pair s l) fun sl =>
  .bind (.op2 .pair n sl) fun nsl => .op2 .pair u nsl

/-! ### Kernel runs -/

/-- **Arithmetic and comparisons.** -/
example : go (primProg (same _) (natOps _)) (ser (.prod .nat .nat) (5, 3)) =
    some (ser (.prod .nat (.prod .nat (.prod .bool .bool))) (8, 2, false, false), empty11,
      [none, none, none, none], 44992) := by
  decide +kernel

example : go (primProg (same _) (natOps _)) (ser (.prod .nat .nat) (3, 5)) =
    some (ser (.prod .nat (.prod .nat (.prod .bool .bool))) (8, 0, false, true), empty11,
      [none, none, none, none], 44786) := by
  decide +kernel

example : go (primProg (same _) (natOps _)) (ser (.prod .nat .nat) (4, 4)) =
    some (ser (.prod .nat (.prod .nat (.prod .bool .bool))) (8, 0, true, false), empty11,
      [none, none, none, none], 45140) := by
  decide +kernel

/-- **Negative control**: not in `44991` steps. -/
theorem natOps_not_44991 : go (primProg (same _) (natOps _)) (ser (.prod .nat .nat) (5, 3)) ≠
    some (ser (.prod .nat (.prod .nat (.prod .bool .bool))) (8, 2, false, false), empty11,
      [none, none, none, none], 44991) := by
  decide +kernel

/-- **Booleans.** -/
example : go (primProg (same _) (boolOps _)) (ser (.prod .bool .bool) (true, false)) =
    some (ser (.prod .bool (.prod .bool (.prod .bool .bool))) (false, false, true, true), empty11,
      [none, none, none, none], 27646) := by
  decide +kernel

example : go (primProg (same _) (boolOps _)) (ser (.prod .bool .bool) (false, true)) =
    some (ser (.prod .bool (.prod .bool (.prod .bool .bool))) (true, false, true, true), empty11,
      [none, none, none, none], 27582) := by
  decide +kernel

/-- **Lists.** -/
example : go (primProg (same _) (listOps _)) (ser (.list .nat) [1, 2, 3]) =
    some (ser (.prod .nat (.list .nat)) (3, [3, 2, 1]), empty11, [none, none, none, none],
      67077) := by
  decide +kernel

example : go (primProg (same _) (listOps' _)) (ser (.list .nat) [1, 2]) =
    some (ser (.prod (.list .nat) (.list .nat)) ([1, 2, 1, 2], [0, 1, 2]), empty11,
      [none, none, none, none], 142792) := by
  decide +kernel

/-- **Arrays.** -/
example : go (primProg (same _) (arrOps _)) (ser (.list .nat) [4, 5, 6]) =
    some (ser (.prod .nat (.prod .nat (.prod .nat (.list .nat)))) (3, 5, 0, [4, 4]), empty11,
      [none, none, none, none], 165549) := by
  decide +kernel

/-- **Negative control**: the out-of-bounds read gives the default `0`, not the last element. -/
theorem arrOps_default : (go (primProg (same _) (arrOps _)) (ser (.list .nat) [4, 5, 6])).map
    (·.1) ≠ some (ser (.prod .nat (.prod .nat (.prod .nat (.list .nat)))) (3, 5, 6, [4, 4])) := by
  decide +kernel

example : go (primProg (same _) (updOps _)) (ser (.list .nat) [4, 5, 6]) =
    some (ser (.list .nat) [9, 5, 7], empty11, [none, none, none, none], 251701) := by
  decide +kernel

/-- **Negative control**: the out-of-bounds write leaves the array as it was (no write at the
last index). -/
theorem updOps_oob : (go (primProg (same _) (updOps _)) (ser (.list .nat) [4, 5, 6])).map
    (·.1) ≠ some (ser (.list .nat) [9, 5, 1]) := by
  decide +kernel

example : go (primProg (same _) (pairDefault _)) (ser (.list (.prod .nat .bool)) [(1, true)]) =
    some (ser (.prod .nat .bool) (0, false), empty11, [none, none, none, none], 16626) := by
  decide +kernel

/-- **Options and the unit.** -/
example : go (primProg (same _) (optOps _)) (ser .nat 6) =
    some (ser (.prod .unit (.prod (.option .nat) (.prod (.option .nat) (.list (.option .nat)))))
      ((), none, some 6, [some 6]), empty11, [none, none, none, none], 38422) := by
  decide +kernel

/-- **Recursion with `primCode`**: `copyRec` copies `[1, 2, 3]`. -/
example : go (primProg copyRec fun _ l => .recur l) (ser (.list .nat) [1, 2, 3]) =
    some (ser (.list .nat) [1, 2, 3], empty11, [none, none, none, none], 41962) := by
  decide +kernel

/-! ### The specification -/

/-- **`primCode_spec`** for `B = 3`, `F = 2` and `Q N = primB (3 + N)`. -/
example (prog : Program Stk Sym Rg Bool) (K : ℕ) :
    PrimSpec prog primCode 3 2 K fun N => primB (3 + N) :=
  primCode_spec prog (by decide) le_rfl fun _ => le_rfl

/-- **The simulation theorem with the primitives' code**: for `copyRec`, with `K = 10`,
`D = 28` and `Q N = ctrlB 28 (B + N) + primB (B + N)`, for every `B` and `F` with `10 ≤ B`,
`F + 1 ≤ B` and `2 ≤ F`, the compiled call `recur l` on a frame holding the input pushes a
pointer representing the result of every run. There is no premise on the primitives. -/
theorem copy_spec {E : (var : Ty → Type) → var (.list .nat) →
      Prog Signature.empty (.list .nat, .list .nat) var (.list .nat)} {B F : ℕ} (hB : 10 ≤ B)
    (hFB : F + 1 ≤ B) (h2F : 2 ≤ F) {xs v : List ℕ} {tr : Trace Signature.empty} {fuel : ℕ}
    (he : eval O₀ (copyRec Ty.denote) fuel (.recur xs) = some (v, tr))
    {h : List Cell} {c : Cfg Stk Sym Rg} (hH : HeapAt h c) (hb : HeapBnd B F h)
    (hv : c.regs = Regs.empty) (hE : EnvAt B [⟨.list .nat, xs, 0⟩] 1 h c)
    (hF : Trace.localCost tr ≤ F) :
    Pushes (primProg copyRec E) (comp primCode true 1
      (Prog.recur (S := Signature.empty) (rec := (.list .nat, .list .nat)) (var := Lv) 0)) c h
      (.list .nat) v B F 10 (fun N => ctrlB 28 (B + N) + primB (B + N)) 1
      (Trace.localCost tr) := by
  have hmono : Monotone (fun N => ctrlB 28 (B + N) + primB (B + N)) :=
    fun _ _ hN => Nat.add_le_add (ctrlB_mono (by omega)) (primB_mono (by omega))
  have hps : PrimSpec (primProg copyRec E) primCode B F 10
      (fun N => ctrlB 28 (B + N) + primB (B + N)) :=
    primCode_spec (Q := fun N => ctrlB 28 (B + N) + primB (B + N)) _ hFB h2F
      fun N => Nat.le_add_left (primB (B + N)) (ctrlB 28 (B + N))
  have hprog : (primProg copyRec E).body true = comp primCode true 1 (copyRec Lv 0) := rfl
  have hK : psize 1 (copyRec Lv 0) + 1 ≤ 10 := by decide +kernel
  have hD : 1 + 3 * psize 1 (copyRec Lv 0) ≤ 28 := by decide +kernel
  exact comp_sat primCode true ⟨copyRec, copyRec_wf⟩ O₀ hprog hmono
    (fun _ => Nat.le_add_right _ _) hB hps hK hD fuel (.recur rfl (List.mem_singleton_self _)) he
    hH hb hv hE (by decide) (by decide) hF

/-- The heap holding the empty list, and the machine with it bound at level `0`. -/
def hNil : List Cell := [⟨[], .nil, []⟩]

def cNil : Cfg Stk Sym Rg := ⟨Regs.empty, fun k => match k with
  | .heap => encHeap hNil
  | .cnt => bits [true] ++ [.nd]
  | .env => envEnc [[]]
  | _ => []⟩

/-- **A concrete instance** of `copy_spec`, all premises discharged: copying the empty list
(three units of local cost) from `cNil`, with `B = 10` and `F = 3`. -/
theorem copy_nil : ∃ v tr, eval O₀ (copyRec Ty.denote) 3 (.recur []) = some (v, tr) ∧
    Pushes (primProg copyRec fun _ l => .recur l) (comp primCode true 1
      (Prog.recur (S := Signature.empty) (rec := (.list .nat, .list .nat)) (var := Lv) 0)) cNil
      hNil (.list .nat) v 10 3 10 (fun N => ctrlB 28 (10 + N) + primB (10 + N)) 1
      (Trace.localCost tr) :=
  ⟨_, _, rfl, copy_spec (fuel := 3) (by decide) (by decide) (by decide) rfl
    ⟨by unfold HeapWF; decide +kernel, rfl, rfl, [true], rfl, rfl, by decide⟩
    (by unfold HeapBnd; decide +kernel) rfl
    ⟨[[]], [], rfl, rfl, by decide, fun e he => by
      simp only [List.mem_singleton] at he; subst he
      exact ⟨by decide, Rep.nil ⟨by decide, rfl, rfl⟩⟩⟩
    (by decide +kernel)⟩

end GraphIsoChecks.TMPrims
