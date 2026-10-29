module

public import Mathlib.Logic.Function.Basic
public import Mathlib.Order.Basic

/-!
# Structured stack programs

Stage 17a (`PLAN-17.md` §3). Programs for Turing machines are written in a small structured
language over finitely many stacks, and compiled to mathlib's `Turing.FinTM2` in
`GraphIso.TM.Machine`.

* **Configurations** (`Cfg`): `R` registers, each holding a symbol or nothing, and stacks named by
  `K`, holding lists of symbols of the alphabet `Γ` (the head is the top).
* **Actions** (`Act`): push a constant symbol, push the symbol of a register (`default` if it is
  empty), pop the top of a stack into a register (nothing if the stack is empty), peek at the top
  into a register, set a register.
* **Conditions** (`Cond`): a register holds a given value; negation and conjunction.
* **Code** (`Code`): `skip`, an action, sequence, `ite` and `loop` (a while loop) on a
  condition, and `call p` of a procedure `p`. Actions and conditions are data, interpreted by
  `Act.run` and `Cond.eval`, so code has decidable equality.
* **Programs** (`Program`): a body for each procedure (in a finite type `P`), and a main
  procedure. Procedures may call each other recursively; registers are global.
* **Semantics** (`Exec`): a big-step relation with a step count: one step for `skip`, an action,
  a `seq`, and each test of `ite` and `loop`; a call costs its body plus two steps (call and
  return). These are exactly the steps of the compiled machine.
* **An interpreter** (`run`): fuel-bounded, computable, and agreeing with `Exec` whenever the fuel
  is at least the step count (`run_of_exec`). So `Exec` is deterministic (`Exec.det`), and step
  counts can be computed as data.
-/

@[expose] public section

namespace GraphIso.TM

open Function

/-- Registers: `R` slots, each holding a symbol or nothing. -/
abbrev Regs (Γ : Type) (R : ℕ) : Type := Fin R → Option Γ

/-- Empty registers. -/
def Regs.empty {Γ : Type} {R : ℕ} : Regs Γ R := fun _ => none

/-- Actions on registers and stacks. -/
inductive Act (K Γ : Type) (R : ℕ) where
  /-- Push a constant symbol onto stack `k`. -/
  | push (k : K) (s : Γ)
  /-- Push the symbol of register `r` (`default` if empty) onto stack `k`. -/
  | pushReg (k : K) (r : Fin R)
  /-- Pop the top of stack `k` into register `r` (`none` if the stack is empty). -/
  | pop (k : K) (r : Fin R)
  /-- Copy the top of stack `k` into register `r` (`none` if the stack is empty). -/
  | peek (k : K) (r : Fin R)
  /-- Set register `r`. -/
  | set (r : Fin R) (o : Option Γ)
  deriving DecidableEq

/-- Conditions on the registers. -/
inductive Cond (Γ : Type) (R : ℕ) where
  /-- Register `r` holds `o`. -/
  | is (r : Fin R) (o : Option Γ)
  /-- Negation. -/
  | not (b : Cond Γ R)
  /-- Conjunction. -/
  | and (b c : Cond Γ R)
  deriving DecidableEq

/-- Structured code over procedures `P`. -/
inductive Code (K Γ : Type) (R : ℕ) (P : Type) where
  /-- Do nothing (one step). -/
  | skip
  /-- An action. -/
  | act (a : Act K Γ R)
  /-- Sequence. -/
  | seq (c d : Code K Γ R P)
  /-- Branch on a condition. -/
  | ite (b : Cond Γ R) (c d : Code K Γ R P)
  /-- Run the body while the condition holds. -/
  | loop (b : Cond Γ R) (c : Code K Γ R P)
  /-- Call a procedure. -/
  | call (p : P)
  deriving DecidableEq

/-- A configuration: registers and stacks. -/
structure Cfg (K Γ : Type) (R : ℕ) where
  /-- The registers. -/
  regs : Regs Γ R
  /-- The stacks; the head of a list is the top. -/
  stk : K → List Γ

/-- A program: a body for each procedure, and the main procedure. -/
structure Program (K Γ : Type) (R : ℕ) (P : Type) where
  /-- The body of each procedure. -/
  body : P → Code K Γ R P
  /-- The main procedure. -/
  main : P

variable {K Γ : Type} {R : ℕ} {P : Type}

section Semantics

variable [DecidableEq K] [DecidableEq Γ] [Inhabited Γ]

/-- The effect of an action. -/
def Act.run : Act K Γ R → Cfg K Γ R → Cfg K Γ R
  | .push k s, c => ⟨c.regs, update c.stk k (s :: c.stk k)⟩
  | .pushReg k r, c => ⟨c.regs, update c.stk k ((c.regs r).getD default :: c.stk k)⟩
  | .pop k r, c => ⟨update c.regs r (c.stk k).head?, update c.stk k (c.stk k).tail⟩
  | .peek k r, c => ⟨update c.regs r (c.stk k).head?, c.stk⟩
  | .set r o, c => ⟨update c.regs r o, c.stk⟩

/-- The value of a condition. -/
def Cond.eval : Cond Γ R → Regs Γ R → Bool
  | .is r o, v => decide (v r = o)
  | .not b, v => !b.eval v
  | .and b c, v => b.eval v && c.eval v

/-- Big-step semantics with step counts. -/
inductive Exec (prog : Program K Γ R P) :
    Code K Γ R P → Cfg K Γ R → Cfg K Γ R → ℕ → Prop where
  | skip (c : Cfg K Γ R) : Exec prog .skip c c 1
  | act (a : Act K Γ R) (c : Cfg K Γ R) : Exec prog (.act a) c (a.run c) 1
  | seq {x y : Code K Γ R P} {c₁ c₂ c₃ : Cfg K Γ R} {n m : ℕ} :
      Exec prog x c₁ c₂ n → Exec prog y c₂ c₃ m → Exec prog (.seq x y) c₁ c₃ (n + m + 1)
  | ite_true {b : Cond Γ R} {x y : Code K Γ R P} {c₁ c₂ : Cfg K Γ R} {n : ℕ} :
      b.eval c₁.regs = true → Exec prog x c₁ c₂ n → Exec prog (.ite b x y) c₁ c₂ (n + 1)
  | ite_false {b : Cond Γ R} {x y : Code K Γ R P} {c₁ c₂ : Cfg K Γ R} {n : ℕ} :
      b.eval c₁.regs = false → Exec prog y c₁ c₂ n → Exec prog (.ite b x y) c₁ c₂ (n + 1)
  | loop_false {b : Cond Γ R} {x : Code K Γ R P} {c : Cfg K Γ R} :
      b.eval c.regs = false → Exec prog (.loop b x) c c 1
  | loop_true {b : Cond Γ R} {x : Code K Γ R P} {c₁ c₂ c₃ : Cfg K Γ R} {n m : ℕ} :
      b.eval c₁.regs = true → Exec prog x c₁ c₂ n → Exec prog (.loop b x) c₂ c₃ m →
      Exec prog (.loop b x) c₁ c₃ (n + m + 1)
  | call {p : P} {c₁ c₂ : Cfg K Γ R} {n : ℕ} :
      Exec prog (prog.body p) c₁ c₂ n → Exec prog (.call p) c₁ c₂ (n + 2)

/-- A fuel-bounded interpreter returning the final configuration and the step count. -/
def run (prog : Program K Γ R P) : ℕ → Code K Γ R P → Cfg K Γ R → Option (Cfg K Γ R × ℕ)
  | 0, _, _ => none
  | _ + 1, .skip, c => some (c, 1)
  | _ + 1, .act a, c => some (a.run c, 1)
  | f + 1, .seq x y, c =>
    match run prog f x c with
    | none => none
    | some (c', n) =>
      match run prog f y c' with
      | none => none
      | some (c'', m) => some (c'', n + m + 1)
  | f + 1, .ite b x y, c =>
    match run prog f (cond (b.eval c.regs) x y) c with
    | none => none
    | some (c', n) => some (c', n + 1)
  | f + 1, .loop b x, c =>
    if b.eval c.regs then
      match run prog f x c with
      | none => none
      | some (c', n) =>
        match run prog f (.loop b x) c' with
        | none => none
        | some (c'', m) => some (c'', n + m + 1)
    else some (c, 1)
  | f + 1, .call p, c =>
    match run prog f (prog.body p) c with
    | none => none
    | some (c', n) => some (c', n + 2)

theorem Exec.one_le {prog : Program K Γ R P} {x : Code K Γ R P} {c c' : Cfg K Γ R} {n : ℕ}
    (h : Exec prog x c c' n) : 1 ≤ n := by
  cases h <;> omega

/-- The interpreter agrees with `Exec` when the fuel is at least the step count. -/
theorem run_of_exec {prog : Program K Γ R P} {x : Code K Γ R P} {c c' : Cfg K Γ R} {n : ℕ}
    (h : Exec prog x c c' n) : ∀ f, n ≤ f → run prog f x c = some (c', n) := by
  induction h with
  | skip c => intro f hf; obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩; rfl
  | act a c => intro f hf; obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩; rfl
  | seq h₁ h₂ ih₁ ih₂ =>
    intro f hf
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    simp only [run, ih₁ f (by omega), ih₂ f (by omega)]
  | ite_true hb h ih =>
    intro f hf
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    simp only [run, hb, Bool.cond_true, ih f (by omega)]
  | ite_false hb h ih =>
    intro f hf
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    simp only [run, hb, Bool.cond_false, ih f (by omega)]
  | loop_false hb =>
    intro f hf
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    simp only [run, hb, Bool.false_eq_true, ↓reduceIte]
  | loop_true hb h₁ h₂ ih₁ ih₂ =>
    intro f hf
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    simp only [run, hb, ↓reduceIte, ih₁ f (by omega), ih₂ f (by omega)]
  | call h ih =>
    intro f hf
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    simp only [run, ih f (by omega)]

/-- `Exec` is deterministic, in the result and in the step count. -/
theorem Exec.det {prog : Program K Γ R P} {x : Code K Γ R P} {c c₁ c₂ : Cfg K Γ R} {n₁ n₂ : ℕ}
    (h₁ : Exec prog x c c₁ n₁) (h₂ : Exec prog x c c₂ n₂) : c₁ = c₂ ∧ n₁ = n₂ := by
  have e₁ := run_of_exec h₁ (max n₁ n₂) (Nat.le_max_left _ _)
  have e₂ := run_of_exec h₂ (max n₁ n₂) (Nat.le_max_right _ _)
  rw [e₁] at e₂
  simp only [Option.some.injEq, Prod.mk.injEq] at e₂
  exact e₂

/-- The interpreter is sound: a result of `run` is an `Exec`. -/
theorem exec_of_run {prog : Program K Γ R P} :
    ∀ (f : ℕ) (x : Code K Γ R P) (c c' : Cfg K Γ R) (n : ℕ),
      run prog f x c = some (c', n) → Exec prog x c c' n
  | 0, _, _, _, _, h => by simp [run] at h
  | f + 1, .skip, c, c', n, h => by
    simp only [run, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .skip c
  | f + 1, .act a, c, c', n, h => by
    simp only [run, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .act a c
  | f + 1, .seq x y, c, c', n, h => by
    simp only [run] at h
    rcases h₁ : run prog f x c with _ | ⟨c₁, n₁⟩
    · simp [h₁] at h
    rcases h₂ : run prog f y c₁ with _ | ⟨c₂, n₂⟩
    · simp [h₁, h₂] at h
    simp only [h₁, h₂, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .seq (exec_of_run f x c c₁ n₁ h₁) (exec_of_run f y c₁ c₂ n₂ h₂)
  | f + 1, .ite b x y, c, c', n, h => by
    simp only [run] at h
    rcases hb : b.eval c.regs
    · rw [hb, Bool.cond_false] at h
      rcases h₁ : run prog f y c with _ | ⟨c₁, n₁⟩
      · simp [h₁] at h
      simp only [h₁, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .ite_false hb (exec_of_run f y c c₁ n₁ h₁)
    · rw [hb, Bool.cond_true] at h
      rcases h₁ : run prog f x c with _ | ⟨c₁, n₁⟩
      · simp [h₁] at h
      simp only [h₁, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .ite_true hb (exec_of_run f x c c₁ n₁ h₁)
  | f + 1, .loop b x, c, c', n, h => by
    simp only [run] at h
    rcases hb : b.eval c.regs
    · simp only [hb, Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .loop_false hb
    · simp only [hb, ↓reduceIte] at h
      rcases h₁ : run prog f x c with _ | ⟨c₁, n₁⟩
      · simp [h₁] at h
      rcases h₂ : run prog f (.loop b x) c₁ with _ | ⟨c₂, n₂⟩
      · simp [h₁, h₂] at h
      simp only [h₁, h₂, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .loop_true hb (exec_of_run f x c c₁ n₁ h₁) (exec_of_run f (.loop b x) c₁ c₂ n₂ h₂)
  | f + 1, .call p, c, c', n, h => by
    simp only [run] at h
    rcases h₁ : run prog f (prog.body p) c with _ | ⟨c₁, n₁⟩
    · simp [h₁] at h
    simp only [h₁, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .call (exec_of_run f (prog.body p) c c₁ n₁ h₁)

end Semantics

end GraphIso.TM
