module

public import GraphIso.TM.Code
public import Mathlib.Computability.TuringMachine.Computable
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Prod

/-!
# Stack programs as Turing machines

Stage 17a (`PLAN-17.md` §3). A program (`GraphIso.TM.Program`) is compiled to mathlib's
`Turing.FinTM2`:

* **Labels** are continuations: the list of code fragments still to run in the current
  procedure. `reach c k` is the finite set of labels met while running `c` before `k`; every
  local successor of a label in `reach c k` is in `reach c k` or is `k` (`reach_succ`), and so is
  every tail (`reach_tail`). The labels of the machine are the subtype of
  `labs prog = {[]} ∪ ⋃_p reach (body p) []`.
* **Stacks** are the program's stacks (`some k`, alphabet `Γ`) and a return stack (`none`) whose
  alphabet is the label type.
* **Local state** is the registers and a return slot.
* **Statements** (`stmt`): `skip`, an action, `seq`, a test of `ite` or `loop`, and `call p`
  (push the continuation, go to `[body p]`) each take one step; the label `[]` pops a return
  address into the slot and jumps to it, or halts if the return stack is empty.

**`sim`**: an `Exec` of `n` steps from `c` to `c'` is exactly `n` machine steps from the label
`x :: k` to the label `k`, for every continuation `k`, return stack and return slot.
**`halts`**: running `main` takes one more step, to the halting configuration.

**`outputsInTime`**: if `main` runs from the input on the input stack (registers empty, other
stacks empty) to the output on the output stack (registers empty, other stacks empty) in `n`
steps, then `TM2OutputsInTime` holds in `n + 1` steps. **`computableInTime`**: if this holds for
every `a`, with output `eb (f a)` within `T |ea a|` steps, a `TM2ComputableInTime ea eb f` with
time `T + 1`; the step counts are computed by the interpreter `run`.
-/

@[expose] public section

namespace GraphIso.TM

open Function Turing

variable {K Γ : Type} {R : ℕ} {P : Type}

/-- Labels: the code still to run in the current procedure. -/
abbrev Lab (K Γ : Type) (R : ℕ) (P : Type) := List (Code K Γ R P)

section Reach

variable [DecidableEq K] [DecidableEq Γ] [DecidableEq P]

/-- The labels met while running `c` before the continuation `k`. -/
def reach : Code K Γ R P → Lab K Γ R P → Finset (Lab K Γ R P)
  | .seq x y, k => insert (.seq x y :: k) (reach x (y :: k) ∪ reach y k)
  | .ite b x y, k => insert (.ite b x y :: k) (reach x k ∪ reach y k)
  | .loop b x, k => insert (.loop b x :: k) (reach x (.loop b x :: k))
  | .skip, k => {.skip :: k}
  | .act a, k => {.act a :: k}
  | .call p, k => {.call p :: k}

theorem mem_reach_self (c : Code K Γ R P) (k : Lab K Γ R P) : c :: k ∈ reach c k := by
  cases c <;> simp [reach]

/-- Local successors of a label (the jump of `call` is handled separately). -/
inductive Succ : Lab K Γ R P → Lab K Γ R P → Prop where
  | skip (k : Lab K Γ R P) : Succ (.skip :: k) k
  | act (a : Act K Γ R) (k : Lab K Γ R P) : Succ (.act a :: k) k
  | seq (x y : Code K Γ R P) (k : Lab K Γ R P) : Succ (.seq x y :: k) (x :: y :: k)
  | ite₁ (b : Cond Γ R) (x y : Code K Γ R P) (k : Lab K Γ R P) : Succ (.ite b x y :: k) (x :: k)
  | ite₂ (b : Cond Γ R) (x y : Code K Γ R P) (k : Lab K Γ R P) : Succ (.ite b x y :: k) (y :: k)
  | loop₁ (b : Cond Γ R) (x : Code K Γ R P) (k : Lab K Γ R P) :
      Succ (.loop b x :: k) (x :: .loop b x :: k)
  | loop₂ (b : Cond Γ R) (x : Code K Γ R P) (k : Lab K Γ R P) : Succ (.loop b x :: k) k
  | call (p : P) (k : Lab K Γ R P) : Succ (.call p :: k) k

/-- Successors stay in `reach c k`, or return to `k`. -/
theorem reach_succ (c : Code K Γ R P) :
    ∀ (k l l' : Lab K Γ R P), l ∈ reach c k → Succ l l' → l' ∈ reach c k ∨ l' = k := by
  induction c with
  | skip => intro k l l' hl hs; simp only [reach, Finset.mem_singleton] at hl; subst hl; cases hs
            exact Or.inr rfl
  | act a => intro k l l' hl hs; simp only [reach, Finset.mem_singleton] at hl; subst hl; cases hs
             exact Or.inr rfl
  | call p => intro k l l' hl hs; simp only [reach, Finset.mem_singleton] at hl; subst hl; cases hs
              exact Or.inr rfl
  | seq x y ihx ihy =>
    intro k l l' hl hs
    simp only [reach, Finset.mem_insert, Finset.mem_union] at hl ⊢
    rcases hl with rfl | hl | hl
    · cases hs
      exact Or.inl (Or.inr (Or.inl (mem_reach_self _ _)))
    · rcases ihx _ _ _ hl hs with h | rfl
      · exact Or.inl (Or.inr (Or.inl h))
      · exact Or.inl (Or.inr (Or.inr (mem_reach_self _ _)))
    · rcases ihy _ _ _ hl hs with h | rfl
      · exact Or.inl (Or.inr (Or.inr h))
      · exact Or.inr rfl
  | ite b x y ihx ihy =>
    intro k l l' hl hs
    simp only [reach, Finset.mem_insert, Finset.mem_union] at hl ⊢
    rcases hl with rfl | hl | hl
    · cases hs
      · exact Or.inl (Or.inr (Or.inl (mem_reach_self _ _)))
      · exact Or.inl (Or.inr (Or.inr (mem_reach_self _ _)))
    · rcases ihx _ _ _ hl hs with h | rfl
      · exact Or.inl (Or.inr (Or.inl h))
      · exact Or.inr rfl
    · rcases ihy _ _ _ hl hs with h | rfl
      · exact Or.inl (Or.inr (Or.inr h))
      · exact Or.inr rfl
  | loop b x ih =>
    intro k l l' hl hs
    simp only [reach, Finset.mem_insert] at hl ⊢
    rcases hl with rfl | hl
    · cases hs
      · exact Or.inl (Or.inr (mem_reach_self _ _))
      · exact Or.inr rfl
    · rcases ih _ _ _ hl hs with h | rfl
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl rfl)

/-- Tails stay in `reach c k`, or are `k`. -/
theorem reach_tail (c : Code K Γ R P) :
    ∀ (k : Lab K Γ R P) (x : Code K Γ R P) (l : Lab K Γ R P), x :: l ∈ reach c k →
      l ∈ reach c k ∨ l = k := by
  induction c with
  | skip => intro k x l hl; simp only [reach, Finset.mem_singleton, List.cons.injEq] at hl
            exact Or.inr hl.2
  | act a => intro k x l hl; simp only [reach, Finset.mem_singleton, List.cons.injEq] at hl
             exact Or.inr hl.2
  | call p => intro k x l hl; simp only [reach, Finset.mem_singleton, List.cons.injEq] at hl
              exact Or.inr hl.2
  | seq c d ihc ihd =>
    intro k x l hl
    simp only [reach, Finset.mem_insert, Finset.mem_union, List.cons.injEq] at hl ⊢
    rcases hl with ⟨rfl, rfl⟩ | hl | hl
    · exact Or.inr rfl
    · rcases ihc _ _ _ hl with h | rfl
      · exact Or.inl (Or.inr (Or.inl h))
      · exact Or.inl (Or.inr (Or.inr (mem_reach_self _ _)))
    · rcases ihd _ _ _ hl with h | rfl
      · exact Or.inl (Or.inr (Or.inr h))
      · exact Or.inr rfl
  | ite b c d ihc ihd =>
    intro k x l hl
    simp only [reach, Finset.mem_insert, Finset.mem_union, List.cons.injEq] at hl ⊢
    rcases hl with ⟨rfl, rfl⟩ | hl | hl
    · exact Or.inr rfl
    · rcases ihc _ _ _ hl with h | rfl
      · exact Or.inl (Or.inr (Or.inl h))
      · exact Or.inr rfl
    · rcases ihd _ _ _ hl with h | rfl
      · exact Or.inl (Or.inr (Or.inr h))
      · exact Or.inr rfl
  | loop b c ih =>
    intro k x l hl
    simp only [reach, Finset.mem_insert, List.cons.injEq] at hl ⊢
    rcases hl with ⟨rfl, rfl⟩ | hl
    · exact Or.inr rfl
    · rcases ih _ _ _ hl with h | rfl
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl rfl)

variable [Fintype P]

/-- The labels of a program: the empty continuation and everything reachable in a body. -/
def labs (prog : Program K Γ R P) : Finset (Lab K Γ R P) :=
  insert [] (Finset.univ.biUnion fun p => reach (prog.body p) [])

variable {prog : Program K Γ R P}

theorem nil_mem_labs : ([] : Lab K Γ R P) ∈ labs prog := Finset.mem_insert_self _ _

theorem body_mem_labs (p : P) : [prog.body p] ∈ labs prog :=
  Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨p, Finset.mem_univ _, mem_reach_self _ _⟩)

theorem labs_succ {l l' : Lab K Γ R P} (hl : l ∈ labs prog) (hs : Succ l l') : l' ∈ labs prog := by
  simp only [labs, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ, true_and] at hl ⊢
  rcases hl with rfl | ⟨p, hp⟩
  · cases hs
  · rcases reach_succ _ _ _ _ hp hs with h | rfl
    · exact Or.inr ⟨p, h⟩
    · exact Or.inl rfl

theorem labs_tail {x : Code K Γ R P} {l : Lab K Γ R P} (hl : x :: l ∈ labs prog) :
    l ∈ labs prog := by
  simp only [labs, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ, true_and,
    reduceCtorEq, false_or] at hl ⊢
  obtain ⟨p, hp⟩ := hl
  rcases reach_tail _ _ _ _ hp with h | rfl
  · exact Or.inr ⟨p, h⟩
  · exact Or.inl rfl

end Reach

/-! ### The machine -/

section Machine

variable [DecidableEq K] [DecidableEq Γ] [DecidableEq P] [Fintype P] [Inhabited Γ]
variable (prog : Program K Γ R P)

/-- The machine's labels. -/
abbrev Label := {l : Lab K Γ R P // l ∈ labs prog}

/-- The label of the main procedure. -/
def mainLab : Label prog := ⟨[prog.body prog.main], body_mem_labs _⟩

/-- The machine's alphabets: the program's stacks (`some k`) and the return stack (`none`). -/
@[reducible] def MΓ : Option K → Type
  | none => Label prog
  | some _ => Γ

/-- The machine's local state: registers and a return slot. -/
abbrev MState := Regs Γ R × Option (Label prog)

/-- The machine's statements. -/
abbrev MStmt := TM2.Stmt (MΓ prog) (Label prog) (MState prog)

/-- The statement of an action, followed by `q`. -/
def actStmt (a : Act K Γ R) (q : MStmt prog) : MStmt prog :=
  match a with
  | .push k s => .push (some k) (fun _ => (s : Γ)) q
  | .pushReg k r => .push (some k) (fun v => ((v.1 r).getD default : Γ)) q
  | .pop k r => .pop (some k) (fun v (o : Option Γ) => (update v.1 r o, v.2)) q
  | .peek k r => .peek (some k) (fun v (o : Option Γ) => (update v.1 r o, v.2)) q
  | .set r o => .load (fun v => (update v.1 r o, v.2)) q

/-- The statement of a label. -/
def stmt : (l : Lab K Γ R P) → l ∈ labs prog → MStmt prog
  | [], _ =>
    .pop none (fun v (o : Option (Label prog)) => (v.1, o))
      (.branch (fun v => v.2.isSome) (.goto fun v => v.2.getD (mainLab prog)) .halt)
  | .skip :: k, h => .goto fun _ => ⟨k, labs_succ h (.skip k)⟩
  | .act a :: k, h => actStmt prog a (.goto fun _ => ⟨k, labs_succ h (.act a k)⟩)
  | .seq x y :: k, h => .goto fun _ => ⟨x :: y :: k, labs_succ h (.seq x y k)⟩
  | .ite b x y :: k, h =>
    .branch (fun v => b.eval v.1) (.goto fun _ => ⟨x :: k, labs_succ h (.ite₁ b x y k)⟩)
      (.goto fun _ => ⟨y :: k, labs_succ h (.ite₂ b x y k)⟩)
  | .loop b x :: k, h =>
    .branch (fun v => b.eval v.1) (.goto fun _ => ⟨x :: .loop b x :: k, labs_succ h (.loop₁ b x k)⟩)
      (.goto fun _ => ⟨k, labs_succ h (.loop₂ b x k)⟩)
  | .call p :: k, h =>
    .push none (fun _ => (⟨k, labs_succ h (.call p k)⟩ : Label prog))
      (.goto fun _ => ⟨[prog.body p], body_mem_labs p⟩)

/-- The machine's program. -/
def mach : Label prog → MStmt prog := fun l => stmt prog l.1 l.2

/-- The machine's stacks from a return stack and the program's stacks. -/
def embedStk (rs : List (Label prog)) (s : K → List Γ) : (k : Option K) → List (MΓ prog k)
  | none => rs
  | some k => s k

/-- The machine configuration at a label. -/
def mcfg (l : Option (Label prog)) (regs : Regs Γ R) (ret : Option (Label prog))
    (rs : List (Label prog)) (s : K → List Γ) : TM2.Cfg (MΓ prog) (Label prog) (MState prog) :=
  ⟨l, (regs, ret), embedStk prog rs s⟩

variable [Fintype K] [Fintype Γ]

/-- **The compiled machine**, with input stack `kin` and output stack `kout`. -/
def toFinTM2 (kin kout : K) : FinTM2 where
  K := Option K
  k₀ := some kin
  k₁ := some kout
  Γ := MΓ prog
  Λ := Label prog
  main := mainLab prog
  σ := MState prog
  initialState := (Regs.empty, none)
  Γk₀Fin := (inferInstance : Fintype Γ)
  m := mach prog

end Machine

/-! ### Simulation -/

section Sim

variable [DecidableEq K] [DecidableEq Γ] [DecidableEq P] [Fintype P] [Inhabited Γ]
variable {prog : Program K Γ R P}

omit [Inhabited Γ] in
theorem embedStk_update_some (rs : List (Label prog)) (s : K → List Γ) (k : K) (x : List Γ) :
    update (embedStk prog rs s) (some k) x = embedStk prog rs (update s k x) := by
  funext j
  cases j with
  | none => rw [update_of_ne (by simp)]; rfl
  | some j =>
    by_cases hj : j = k
    · subst hj
      rw [update_self]
      show x = update s j x j
      rw [update_self]
    · rw [update_of_ne (by simpa using hj)]
      show s j = update s k x j
      rw [update_of_ne hj]

omit [Inhabited Γ] in
theorem embedStk_update_none (rs rs' : List (Label prog)) (s : K → List Γ) :
    update (embedStk prog rs s) none rs' = embedStk prog rs' s := by
  funext j
  cases j with
  | none => rw [update_self]; rfl
  | some j => rw [update_of_ne (by simp)]; rfl

theorem stepAux_actStmt (a : Act K Γ R) (q : MStmt prog) (regs : Regs Γ R)
    (ret : Option (Label prog)) (rs : List (Label prog)) (s : K → List Γ) :
    TM2.stepAux (actStmt prog a q) (regs, ret) (embedStk prog rs s) =
      TM2.stepAux q ((a.run ⟨regs, s⟩).regs, ret) (embedStk prog rs (a.run ⟨regs, s⟩).stk) := by
  cases a with
  | push k x =>
    simp only [actStmt, TM2.stepAux, Act.run]
    rw [← embedStk_update_some]; rfl
  | pushReg k r =>
    simp only [actStmt, TM2.stepAux, Act.run]
    rw [← embedStk_update_some]; rfl
  | pop k r =>
    simp only [actStmt, TM2.stepAux, Act.run]
    rw [← embedStk_update_some]; rfl
  | peek k r => rfl
  | set r o => rfl

/-- Iterating the step: one step first. -/
theorem iter_succ {α : Type} (f : α → Option α) (n : ℕ) (a : α) :
    (flip Option.bind f)^[n + 1] (some a) = (flip Option.bind f)^[n] (f a) := by
  rw [iterate_succ_apply]; rfl

/-- Iterating the step: `n` steps, then `m`. -/
theorem iter_add {α : Type} (f : α → Option α) (n m : ℕ) (a : Option α) :
    (flip Option.bind f)^[n + m] a = (flip Option.bind f)^[m] ((flip Option.bind f)^[n] a) := by
  rw [Nat.add_comm, iterate_add_apply]

/-- **Simulation**: an `Exec` of `n` steps is exactly `n` machine steps from the label `x :: k`
to the label `k`, for every continuation, return stack and return slot. -/
theorem sim {x : Code K Γ R P} {c c' : Cfg K Γ R} {n : ℕ} (h : Exec prog x c c' n) :
    ∀ (k : Lab K Γ R P) (hx : x :: k ∈ labs prog) (rs : List (Label prog))
      (ret : Option (Label prog)),
      ∃ ret', (flip Option.bind (TM2.step (mach prog)))^[n]
          (some (mcfg prog (some ⟨x :: k, hx⟩) c.regs ret rs c.stk)) =
        some (mcfg prog (some ⟨k, labs_tail hx⟩) c'.regs ret' rs c'.stk) := by
  induction h with
  | skip c => intro k hx rs ret; exact ⟨ret, rfl⟩
  | act a c =>
    intro k hx rs ret
    refine ⟨ret, ?_⟩
    show some (TM2.stepAux (actStmt prog a _) (c.regs, ret) (embedStk prog rs c.stk)) = _
    rw [stepAux_actStmt]
    rfl
  | @seq x y c₁ c₂ c₃ n m h₁ h₂ ih₁ ih₂ =>
    intro k hx rs ret
    have hx₁ : x :: y :: k ∈ labs prog := labs_succ hx (.seq x y k)
    obtain ⟨ret₁, e₁⟩ := ih₁ (y :: k) hx₁ rs ret
    obtain ⟨ret₂, e₂⟩ := ih₂ k (labs_tail hx₁) rs ret₁
    refine ⟨ret₂, ?_⟩
    rw [show n + m + 1 = (n + m) + 1 from rfl, iter_succ, iter_add]
    exact (congrArg _ e₁).trans e₂
  | @ite_true b x y c₁ c₂ n hb h ih =>
    intro k hx rs ret
    obtain ⟨ret₁, e₁⟩ := ih k (labs_succ hx (.ite₁ b x y k)) rs ret
    refine ⟨ret₁, ?_⟩
    rw [iter_succ]
    refine Eq.trans ?_ e₁
    congr 1
    show some (TM2.stepAux (.branch _ _ _) (c₁.regs, ret) _) = _
    simp only [TM2.stepAux, hb, Bool.cond_true]
    rfl
  | @ite_false b x y c₁ c₂ n hb h ih =>
    intro k hx rs ret
    obtain ⟨ret₁, e₁⟩ := ih k (labs_succ hx (.ite₂ b x y k)) rs ret
    refine ⟨ret₁, ?_⟩
    rw [iter_succ]
    refine Eq.trans ?_ e₁
    congr 1
    show some (TM2.stepAux (.branch _ _ _) (c₁.regs, ret) _) = _
    simp only [TM2.stepAux, hb, Bool.cond_false]
    rfl
  | @loop_false b x c hb =>
    intro k hx rs ret
    refine ⟨ret, ?_⟩
    show some (TM2.stepAux (.branch _ _ _) (c.regs, ret) _) = _
    simp only [TM2.stepAux, hb, Bool.cond_false]
    rfl
  | @loop_true b x c₁ c₂ c₃ n m hb h₁ h₂ ih₁ ih₂ =>
    intro k hx rs ret
    have hx₁ : x :: .loop b x :: k ∈ labs prog := labs_succ hx (.loop₁ b x k)
    obtain ⟨ret₁, e₁⟩ := ih₁ (.loop b x :: k) hx₁ rs ret
    obtain ⟨ret₂, e₂⟩ := ih₂ k (labs_tail hx₁) rs ret₁
    refine ⟨ret₂, ?_⟩
    rw [show n + m + 1 = (n + m) + 1 from rfl, iter_succ, iter_add]
    refine Eq.trans ?_ e₂
    congr 1
    refine Eq.trans ?_ e₁
    congr 1
    show some (TM2.stepAux (.branch _ _ _) (c₁.regs, ret) _) = _
    simp only [TM2.stepAux, hb, Bool.cond_true]
    rfl
  | @call p c₁ c₂ n h ih =>
    intro k hx rs ret
    have hk : k ∈ labs prog := labs_succ hx (.call p k)
    obtain ⟨ret₁, e₁⟩ := ih [] (body_mem_labs p) (⟨k, hk⟩ :: rs) ret
    refine ⟨some ⟨k, hk⟩, ?_⟩
    rw [show n + 2 = (n + 1) + 1 from rfl, iter_succ, iterate_succ_apply']
    have e₀ : TM2.step (mach prog) (mcfg prog (some ⟨.call p :: k, hx⟩) c₁.regs ret rs c₁.stk) =
        some (mcfg prog (some ⟨[prog.body p], body_mem_labs p⟩) c₁.regs ret (⟨k, hk⟩ :: rs)
          c₁.stk) := by
      show some (TM2.stepAux (.push none _ _) (c₁.regs, ret) _) = _
      simp only [TM2.stepAux]
      rw [embedStk_update_none]
      rfl
    rw [e₀, e₁]
    show some (TM2.stepAux (.pop none _ _) (c₂.regs, ret₁) _) = _
    simp only [TM2.stepAux]
    rw [embedStk_update_none]
    rfl

/-- **Halting**: running `main` takes one more step, to the halting configuration. -/
theorem halts {c c' : Cfg K Γ R} {n : ℕ} (h : Exec prog (prog.body prog.main) c c' n)
    (ret : Option (Label prog)) :
    (flip Option.bind (TM2.step (mach prog)))^[n + 1]
        (some (mcfg prog (some (mainLab prog)) c.regs ret [] c.stk)) =
      some (mcfg prog none c'.regs none [] c'.stk) := by
  obtain ⟨ret₁, e₁⟩ := sim h [] (body_mem_labs prog.main) [] ret
  rw [iterate_succ_apply']
  unfold mainLab
  rw [e₁]
  show some (TM2.stepAux (.pop none _ _) (c'.regs, ret₁) _) = _
  simp only [TM2.stepAux]
  rw [embedStk_update_none]
  rfl

end Sim

/-! ### Outputs and computability -/

section Outputs

variable [DecidableEq K] [DecidableEq Γ] [DecidableEq P] [Fintype P] [Inhabited Γ]
variable [Fintype K] [Fintype Γ]
variable (prog : Program K Γ R P)

/-- The stacks with `l` on stack `k` and every other stack empty. -/
def inStk (k : K) (l : List Γ) : K → List Γ := fun j => if j = k then l else []

/-- The configuration with `l` on stack `k`, every other stack empty and the registers empty. -/
def inCfg (k : K) (l : List Γ) : Cfg K Γ R := ⟨Regs.empty, inStk k l⟩

theorem initList_eq (kin kout : K) (l : List Γ) :
    initList (toFinTM2 prog kin kout) l =
      mcfg prog (some (mainLab prog)) Regs.empty none [] (inStk kin l) := by
  simp only [initList, mcfg]
  congr 1
  funext j
  cases j with
  | none => simp [toFinTM2, embedStk]
  | some j =>
    by_cases hj : j = kin
    · subst hj; simp [toFinTM2, embedStk, inStk]; rfl
    · simp [toFinTM2, embedStk, inStk, hj]

theorem haltList_eq (kin kout : K) (l : List Γ) :
    haltList (toFinTM2 prog kin kout) l = mcfg prog none Regs.empty none [] (inStk kout l) := by
  simp only [haltList, mcfg]
  congr 1
  funext j
  cases j with
  | none => simp [toFinTM2, embedStk]
  | some j =>
    by_cases hj : j = kout
    · subst hj; simp [toFinTM2, embedStk, inStk]; rfl
    · simp [toFinTM2, embedStk, inStk, hj]

/-- **The compiled machine outputs `l'` on input `l`** in `n + 1` steps, if `main` runs from the
input configuration of `l` to the output configuration of `l'` in `n` steps. -/
def outputsInTime (kin kout : K) {l l' : List Γ} {n : ℕ}
    (h : Exec prog (prog.body prog.main) (inCfg kin l) (inCfg kout l') n) :
    TM2OutputsInTime (toFinTM2 prog kin kout) l (some l') (n + 1) where
  steps := n + 1
  evals_in_steps := by
    show (flip Option.bind (TM2.step (mach prog)))^[n + 1]
        (some (initList (toFinTM2 prog kin kout) l)) = some (haltList (toFinTM2 prog kin kout) l')
    rw [initList_eq, haltList_eq]
    exact halts h none
  steps_le_m := le_rfl

/-- The step count of `main` from `c`, computed by the interpreter with the given fuel. -/
def stepsOf (fuel : ℕ) (c : Cfg K Γ R) : ℕ :=
  ((run prog fuel (prog.body prog.main) c).map Prod.snd).getD 0

omit [DecidableEq P] [Fintype P] [Fintype K] [Fintype Γ] in
theorem stepsOf_eq {fuel n : ℕ} {c c' : Cfg K Γ R}
    (h : Exec prog (prog.body prog.main) c c' n) (hn : n ≤ fuel) : stepsOf prog fuel c = n := by
  simp [stepsOf, run_of_exec h fuel hn]

/-- **A `TM2ComputableInTime` from stack programs**: if for every `a`, `main` runs from the input
configuration of `ea a` to the output configuration of `eb (f a)` within `T |ea a|` steps, the
compiled machine computes `f` in time `T + 1`. -/
def computableInTime (kin kout : K) {α β : Type} (ea : α → List Γ) (eb : β → List Γ)
    (f : α → β) (T : ℕ → ℕ)
    (h : ∀ a, ∃ n ≤ T (ea a).length,
      Exec prog (prog.body prog.main) (inCfg kin (ea a)) (inCfg kout (eb (f a))) n) :
    TM2ComputableInTime ea eb f where
  tm := toFinTM2 prog kin kout
  inputAlphabet := Equiv.refl Γ
  outputAlphabet := Equiv.refl Γ
  time := fun L => T L + 1
  outputsFun := fun a =>
    { steps := stepsOf prog (T (ea a).length) (inCfg kin (ea a)) + 1
      evals_in_steps := by
        obtain ⟨n, hn, he⟩ := h a
        rw [stepsOf_eq prog he hn]
        show (flip Option.bind (TM2.step (mach prog)))^[n + 1]
            (some (initList (toFinTM2 prog kin kout) (List.map id (ea a) : List Γ))) =
          some (haltList (toFinTM2 prog kin kout) (List.map id (eb (f a)) : List Γ))
        rw [List.map_id, List.map_id]
        exact (outputsInTime prog kin kout he).evals_in_steps
      steps_le_m := by
        obtain ⟨n, hn, he⟩ := h a
        rw [stepsOf_eq prog he hn]
        exact Nat.add_le_add_right hn 1 }

end Outputs



end GraphIso.TM
