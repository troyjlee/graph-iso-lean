module

public import GraphIso.TM.Machine
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fin.VecNotation
import all Init.Data.Array.Basic
import all Init.Data.List.Sort.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Mathlib.Data.List.Sort

/-!
# Checks of stage 17a: stack programs and Turing machines

`PLAN-17.md` §3.

* **A recursive program** (`negProg`) that complements a list of Booleans, preserving the order:
  the procedure `false` pops a bit, saves it on stack `1`, calls itself, restores the bit and
  pushes its complement onto the output stack `2`; `main` (`true`) calls it and clears the
  register. Its exact semantics (`negBody_exec`: `12 |l| + 4` steps, `main_exec`: `12 |l| + 8`)
  and the resulting `TM2ComputableInTime` for `List.map not` in time `12 L + 9` (`negTM`).
* **Kernel runs** of the interpreter and of the compiled machine's `step` on `[true, false]`:
  the machine reaches `haltList` after exactly `33` steps, and a negative control:
  `TM2OutputsInTime` in `32` steps is impossible (`not_outputs_32`).
-/

@[expose] public section

namespace GraphIsoChecks.TMCode

open Function GraphIso.TM Turing

/-- The stacks: input `0`, saved bits `1`, output `2`. -/
def st (a b c : List Bool) : Fin 3 → List Bool := ![a, b, c]

/-- The recursive step: save the bit, recurse, restore it and push its complement. -/
def negElse : Code (Fin 3) Bool 1 Bool :=
  .seq (.act (.pushReg 1 0))
    (.seq (.call false)
      (.seq (.act (.pop 1 0))
        (.ite (.is 0 (some true)) (.act (.push 2 false)) (.act (.push 2 true)))))

/-- The recursive procedure. -/
def negBody : Code (Fin 3) Bool 1 Bool :=
  .seq (.act (.pop 0 0)) (.ite (.is 0 none) .skip negElse)

/-- The program: `main = true` calls the procedure `false` and clears the register. -/
def negProg : Program (Fin 3) Bool 1 Bool where
  body
    | true => .seq (.call false) (.act (.set 0 none))
    | false => negBody
  main := true

@[simp] theorem st0 (a b c : List Bool) : st a b c 0 = a := rfl
@[simp] theorem st1 (a b c : List Bool) : st a b c 1 = b := rfl
@[simp] theorem st2 (a b c : List Bool) : st a b c 2 = c := rfl

theorem upd0 (a b c x : List Bool) : update (st a b c) 0 x = st x b c := by
  funext i; fin_cases i <;> simp

theorem upd1 (a b c x : List Bool) : update (st a b c) 1 x = st a x c := by
  funext i; fin_cases i <;> simp

theorem upd2 (a b c x : List Bool) : update (st a b c) 2 x = st a b x := by
  funext i; fin_cases i <;> simp

theorem updR (r : Regs Bool 1) (o : Option Bool) : update r 0 o = fun _ => o := by
  funext i; fin_cases i; rfl

/-- **The procedure**: from `l` on the input it leaves the input empty, the saved bits as they
were, and `map not l` on top of the output, in `12 |l| + 4` steps. -/
theorem negBody_exec :
    ∀ (l : List Bool) (r : Regs Bool 1) (t o : List Bool),
      Exec negProg negBody ⟨r, st l t o⟩ ⟨fun _ => l.head?, st [] t (l.map not ++ o)⟩
        (12 * l.length + 4)
  | [], r, t, o => by
    have h₁ := Exec.act (prog := negProg) (.pop 0 0) ⟨r, st [] t o⟩
    simp only [Act.run, updR, upd0, st0, List.head?_nil, List.tail_nil] at h₁
    have h := h₁.seq (Exec.ite_true (y := negElse) (b := .is 0 none) rfl (Exec.skip _))
    unfold negBody
    convert h using 1
    simp
  | x :: xs, r, t, o => by
    have h₁ := Exec.act (prog := negProg) (.pop 0 0) ⟨r, st (x :: xs) t o⟩
    simp only [Act.run, updR, upd0, st0, List.head?_cons, List.tail_cons] at h₁
    have h₂ := Exec.act (prog := negProg) (.pushReg 1 0) ⟨fun _ => some x, st xs t o⟩
    simp only [Act.run, upd1, st1, Option.getD_some] at h₂
    have h₃ : Exec negProg (.call false) ⟨fun _ => some x, st xs (x :: t) o⟩
        ⟨fun _ => xs.head?, st [] (x :: t) (xs.map not ++ o)⟩ (12 * xs.length + 4 + 2) :=
      .call (negBody_exec xs _ (x :: t) o)
    have h₄ := Exec.act (prog := negProg) (.pop 1 0)
      ⟨fun _ => xs.head?, st [] (x :: t) (xs.map not ++ o)⟩
    simp only [Act.run, updR, upd1, st1, List.head?_cons, List.tail_cons] at h₄
    have h₅ : Exec negProg (.ite (.is 0 (some true)) (.act (.push 2 false)) (.act (.push 2 true)))
        ⟨fun _ => some x, st [] t (xs.map not ++ o)⟩
        ⟨fun _ => some x, st [] t ((x :: xs).map not ++ o)⟩ 2 := by
      cases x
      · have := Exec.act (prog := negProg) (.push 2 true)
          ⟨fun _ => some false, st [] t (xs.map not ++ o)⟩
        simp only [Act.run, upd2, st2] at this
        exact .ite_false rfl this
      · have := Exec.act (prog := negProg) (.push 2 false)
          ⟨fun _ => some true, st [] t (xs.map not ++ o)⟩
        simp only [Act.run, upd2, st2] at this
        exact .ite_true rfl this
    have h := h₁.seq (Exec.ite_false (b := .is 0 none) (x := .skip) rfl
      (show Exec negProg negElse _ _ _ from h₂.seq (h₃.seq (h₄.seq h₅))))
    unfold negBody
    convert h using 1
    · simp
    · simp only [List.length_cons]; omega

theorem inStk_zero (l : List Bool) : inStk 0 l = st l [] [] := by
  funext i; fin_cases i <;> rfl

theorem inStk_two (l : List Bool) : inStk 2 l = st [] [] l := by
  funext i; fin_cases i <;> rfl

/-- **`main`**: from the input configuration of `l` to the output configuration of
`map not l`, in `12 |l| + 8` steps. -/
theorem main_exec (l : List Bool) :
    Exec negProg (negProg.body negProg.main) (inCfg 0 l) (inCfg 2 (l.map not))
      (12 * l.length + 8) := by
  have h₁ : Exec negProg (.call false) (inCfg 0 l)
      ⟨fun _ => l.head?, st [] [] (l.map not ++ [])⟩ (12 * l.length + 4 + 2) := by
    have := negBody_exec l Regs.empty [] []
    rw [← inStk_zero] at this
    exact .call this
  have h₂ := Exec.act (prog := negProg) (.set 0 none)
    ⟨fun _ => l.head?, st [] [] (l.map not ++ [])⟩
  simp only [Act.run, updR] at h₂
  have h := h₁.seq h₂
  rw [List.append_nil, ← inStk_two] at h
  exact h

/-- **`List.map not` on a Turing machine** in time `12 L + 9`. -/
def negTM : TM2ComputableInTime (fun l : List Bool => l) (fun l => l) (List.map not) :=
  computableInTime negProg 0 2 _ _ _ (fun L => 12 * L + 8)
    fun l => ⟨_, le_rfl, main_exec l⟩

example (L : ℕ) : negTM.time L = 12 * L + 9 := rfl

/-! ### Kernel runs -/

/-- The interpreter on `[true, false, true]`: the output and the step count `12 · 3 + 8`. -/
example : (run negProg 100 (negProg.body negProg.main) (inCfg 0 [true, false, true])).map
    (fun r => (r.1.stk 2, r.1.stk 0, r.1.stk 1, r.1.regs 0, r.2)) =
      some ([false, true, false], [], [], none, 44) := by
  decide +kernel

/-- The compiled machine. -/
abbrev negM : FinTM2 := toFinTM2 negProg 0 2

/-- A program stack of a configuration of the compiled machine. -/
def stkOf (c : negM.Cfg) (k : Fin 3) : List Bool := c.stk (some k)

/-- The register of a configuration of the compiled machine. -/
def regOf (c : negM.Cfg) : Option Bool := c.var.1 0

/-- The configuration after `k` steps on `[true, false]`. -/
def after (k : ℕ) : Option negM.Cfg :=
  (flip bind negM.step)^[k] (some (initList negM [true, false]))

/-- The compiled machine halts on `[true, false]` after exactly `33 = 12 · 2 + 9` steps, with
the output `[false, true]`, every other stack empty and the state reset. -/
example : (after 33).map (fun c => c.l.isNone && c.var.2.isNone && (c.stk none).isEmpty) =
    some true := by
  decide +kernel

example : (after 33).map regOf = some none := by
  decide +kernel

example : (after 33).map (fun c => (stkOf c 0, stkOf c 1, stkOf c 2)) =
    some ([], [], [false, true]) := by
  decide +kernel

/-- Before `33` steps the machine has not halted. -/
theorem running_lt_33 : ∀ k < 33,
    ((flip bind negM.step)^[k] (some (initList negM [true, false]))).map
      (fun c => c.l.isSome) = some true := by
  decide +kernel

/-- **Negative control**: the output in at most `32` steps is impossible. -/
theorem not_outputs_32 : IsEmpty (TM2OutputsInTime negM [true, false] (some [false, true]) 32) :=
  ⟨fun h => by
    have e := h.evals_in_steps
    have r := running_lt_33 h.steps (by have := h.steps_le_m; omega)
    rw [e, Option.map_some, Option.map_some] at r
    exact Bool.false_ne_true (Option.some.inj r)⟩

end GraphIsoChecks.TMCode
