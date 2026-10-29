module

public import GraphIso.Coherent.Tuples
public import GraphIso.Coherent.ListProg

/-!
# Programs for the tuple tables

Programs computing the tables of `GraphIso/Coherent/Tuples.lean`, with no arithmetic beyond
addition, subtraction and comparison:

* `tupsProg k m`: the digit lists of all codes `t < m^k` (`tupList k m`), by `k` extensions;
* `pwTabProg k m`: the products `z · mʲ` (`pwTab k m`), by repeated addition;
* `infoProg k m`: the information on every tuple (`infoL k m`): its equality pattern, the codes
  of its neighbours and of its rearrangements.

`RunsWithin.foldList_gen` is a fold whose body cost may depend on the accumulator; the costs
of `tupsProg` and `infoProg` are bounded through it.
-/

@[expose] public section

namespace GraphIso.Coherent

open Cost Programs Sims

/-- The information on a tuple, as a value type. -/
abbrev infoTy : Ty := .prod .nat (.prod (.list .nat) (.prod (.list (.list .nat)) (.list .nat)))

/-! ### Programs -/

section Prog

variable {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- Prepend every digit of `rm` to `t`, onto `r`. -/
def extTProg (rm : var (.list .nat)) (r : var (.list (.list .nat))) (t : var (.list .nat)) :
    Prog S rec var (.list (.list .nat)) :=
  .foldList rm r fun r' z => .bind (.op2 .cons z t) fun zt => .op2 .cons zt r'

/-- Prepend every digit of `rm` to every list of `acc`. -/
def extProg (rm : var (.list .nat)) (acc : var (.list (.list .nat))) :
    Prog S rec var (.list (.list .nat)) :=
  .bind (.op0 .nil) fun nil =>
  .bind (.foldList acc nil fun r t => extTProg rm r t) fun racc =>
  .op1 .reverse racc

/-- **The digit lists of length `k` over `m` digits, in the order of their codes.** -/
def tupsProg (k m : var .nat) : Prog S rec var (.list (.list .nat)) :=
  .bind (.op1 .range m) fun rm => .bind (.op1 .range k) fun rk =>
  .bind (.op0 .nil) fun nil => .bind (.op0 .nil) fun e => .bind (.op2 .cons nil e) fun one =>
  .foldList rk one fun acc _ => extProg rm acc

/-- The product `a * b`, by repeated addition. -/
def mulNProg (a b : var .nat) : Prog S rec var .nat :=
  .bind (.op1 .range a) fun ra => .bind (.op0 (.natLit 0)) fun z =>
  .foldList ra z fun acc _ => .op2 .add acc b

/-- One step of a row of multiples. -/
def pwStepProg (p : var .nat) (st : var (.prod .nat (.list .nat))) :
    Prog S rec var (.prod .nat (.list .nat)) :=
  .bind (.op1 .fst st) fun c => .bind (.op1 .snd st) fun l => .bind (.op2 .cons c l) fun l' =>
  .bind (.op2 .add c p) fun c' => .op2 .pair c' l'

/-- The row `[0, p, …, (m − 1) p]`. -/
def pwRowProg (rm : var (.list .nat)) (p : var .nat) : Prog S rec var (.array .nat) :=
  .bind (.op0 (.natLit 0)) fun z => .bind (.op0 .nil) fun nl => .bind (.op2 .pair z nl) fun st₀ =>
  .bind (.foldList rm st₀ fun st _ => pwStepProg p st) fun st =>
  .bind (.op1 .snd st) fun l => .bind (.op1 .reverse l) fun l' => .op1 .arrayOfList l'

/-- One step of the table: the row of the current power, and the next power. -/
def pwTabStepProg (m : var .nat) (rm : var (.list .nat))
    (st : var (.prod .nat (.list (.array .nat)))) :
    Prog S rec var (.prod .nat (.list (.array .nat))) :=
  .bind (.op1 .fst st) fun p => .bind (.op1 .snd st) fun rows =>
  .bind (pwRowProg rm p) fun row => .bind (.op2 .cons row rows) fun rows' =>
  .bind (mulNProg m p) fun p' => .op2 .pair p' rows'

/-- **The table of the products `z · mʲ`.** -/
def pwTabProg (m : var .nat) (rk rm : var (.list .nat)) :
    Prog S rec var (.array (.array .nat)) :=
  .bind (.op0 (.natLit 1)) fun one => .bind (.op0 .nil) fun nl =>
  .bind (.op2 .pair one nl) fun st₀ =>
  .bind (.foldList rk st₀ fun st _ => pwTabStepProg m rm st) fun st =>
  .bind (.op1 .snd st) fun rows => .bind (.op1 .reverse rows) fun rows' =>
  .op1 .arrayOfList rows'

/-- A read of a table of rows. -/
def get2Prog (pw : var (.array (.array .nat))) (j v : var .nat) : Prog S rec var .nat :=
  .bind (.op2 .arrayGet pw j) fun row => .op2 .arrayGet row v

/-- One term of the code of `x ∘ τ`. -/
def codeStepProg (pw : var (.array (.array .nat))) (dA τA : var (.array .nat)) (acc i : var .nat) :
    Prog S rec var .nat :=
  .bind (.op2 .arrayGet τA i) fun ti => .bind (.op2 .arrayGet dA ti) fun d =>
  .bind (get2Prog pw i d) fun v => .op2 .add acc v

/-- The code of `x ∘ τ`. -/
def codeProg (pw : var (.array (.array .nat))) (dA τA : var (.array .nat)) (rk : var (.list .nat)) :
    Prog S rec var .nat :=
  .bind (.op0 (.natLit 0)) fun z => .foldList rk z fun acc i => codeStepProg pw dA τA acc i

/-- The code of `update x j z`. -/
def nbrCodeProg (pw : var (.array (.array .nat))) (t : var .nat) (dA : var (.array .nat))
    (z j : var .nat) : Prog S rec var .nat :=
  .bind (.op2 .arrayGet dA j) fun d => .bind (get2Prog pw j d) fun a =>
  .bind (get2Prog pw j z) fun b => .bind (.op2 .sub t a) fun s => .op2 .add s b

/-- The codes of the neighbours. -/
def nbrRowProg (pw : var (.array (.array .nat))) (t : var .nat) (dA : var (.array .nat))
    (rk rm : var (.list .nat)) : Prog S rec var (.list (.list .nat)) :=
  mapList rm fun z => mapList rk fun j => nbrCodeProg pw t dA z j

/-- The codes of the rearrangements. -/
def monoRowProg (pw : var (.array (.array .nat))) (dA : var (.array .nat))
    (mapsA : var (.list (.array .nat))) (rk : var (.list .nat)) : Prog S rec var (.list .nat) :=
  mapList mapsA fun τA => codeProg pw dA τA rk

/-- One entry of the equality pattern. -/
def patBitProg (dA : var (.array .nat)) (i : var .nat) (acc : var (.list .nat)) (j : var .nat) :
    Prog S rec var (.list .nat) :=
  .bind (.op2 .arrayGet dA i) fun a => .bind (.op2 .arrayGet dA j) fun b =>
  .bind (.op2 .natEq a b) fun e =>
  .bind (.ite e (.op0 (.natLit 1)) (.op0 (.natLit 0))) fun bit => .op2 .cons bit acc

/-- Row `i` of the equality pattern, onto `acc`. -/
def patRowIProg (dA : var (.array .nat)) (rk : var (.list .nat)) (acc : var (.list .nat))
    (i : var .nat) : Prog S rec var (.list .nat) :=
  .foldList rk acc fun acc' j => patBitProg dA i acc' j

/-- The equality pattern. -/
def patRowProg (dA : var (.array .nat)) (rk : var (.list .nat)) : Prog S rec var (.list .nat) :=
  .bind (.op0 .nil) fun nl =>
  .bind (.foldList rk nl fun acc i => patRowIProg dA rk acc i) fun racc =>
  .op1 .reverse racc

/-- The information on the tuple of code `t`. -/
def infoAtProg (pw : var (.array (.array .nat))) (tupsA : var (.array (.list .nat)))
    (mapsA : var (.list (.array .nat))) (rk rm : var (.list .nat)) (t : var .nat) :
    Prog S rec var infoTy :=
  .bind (.op2 .arrayGet tupsA t) fun d => .bind (.op1 .arrayOfList d) fun dA =>
  .bind (patRowProg dA rk) fun pat => .bind (nbrRowProg pw t dA rk rm) fun nb =>
  .bind (monoRowProg pw dA mapsA rk) fun mo =>
  .bind (.op2 .pair nb mo) fun r₂ => .bind (.op2 .pair pat r₂) fun r₁ => .op2 .pair t r₁

/-- **The information on all tuples, in the order of their codes.** -/
def infoProg (k m : var .nat) : Prog S rec var (.list infoTy) :=
  .bind (.op1 .range k) fun rk => .bind (.op1 .range m) fun rm =>
  .bind (tupsProg k m) fun tups => .bind (.op1 .arrayOfList tups) fun tupsA =>
  .bind (tupsProg k k) fun maps => .bind (mapList maps fun τ => .op1 .arrayOfList τ) fun mapsA =>
  .bind (pwTabProg m rk rm) fun pw => .bind (.op1 .length tups) fun N =>
  .bind (.op1 .range N) fun rN => mapList rN fun t => infoAtProg pw tupsA mapsA rk rm t

end Prog

/-! ### Models of the folds -/

theorem foldl_ext_eq (m : ℕ) :
    ∀ (acc : List (List ℕ)) (r : List (List ℕ)),
      acc.foldl (fun r t => (List.range m).foldl (fun r' z => (z :: t) :: r') r) r =
        (ext m acc).reverse ++ r
  | [], r => by simp [ext]
  | t :: acc, r => by
    have hin : ∀ (l : List ℕ) (r : List (List ℕ)),
        l.foldl (fun r' z => (z :: t) :: r') r = (l.map (· :: t)).reverse ++ r := by
      intro l
      induction l with
      | nil => simp
      | cons z l ih => intro r; simp [ih]
    rw [List.foldl_cons, hin, foldl_ext_eq m acc]
    simp [ext]

theorem pwRow_fold (p : ℕ) :
    ∀ n : ℕ, (List.range n).foldl (fun st _ => (st.1 + p, st.1 :: st.2)) ((0 : ℕ), ([] : List ℕ)) =
      (n * p, ((List.range n).map (· * p)).reverse)
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.foldl_append, pwRow_fold p n]
    simp [Nat.succ_mul]

theorem pwTab_fold (m : ℕ) :
    ∀ n : ℕ, (List.range n).foldl (fun st _ => (m * st.1, pwRow m st.1 :: st.2))
        ((1 : ℕ), ([] : List (Array ℕ))) =
      (m ^ n, ((List.range n).map fun j => pwRow m (m ^ j)).reverse)
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.foldl_append, pwTab_fold m n]
    simp [pow_succ, Nat.mul_comm]

theorem patRow_fold (dA : Array ℕ) (k : ℕ) :
    ((List.range k).foldl (fun acc i => (List.range k).foldl
        (fun acc' j => (if get dA i = get dA j then 1 else 0) :: acc') acc) []).reverse =
      patRowM dA k := by
  have hin : ∀ (i : ℕ) (l : List ℕ) (r : List ℕ),
      l.foldl (fun acc' j => (if get dA i = get dA j then 1 else 0) :: acc') r =
        (l.map fun j => if get dA i = get dA j then 1 else 0).reverse ++ r := by
    intro i l
    induction l with
    | nil => simp
    | cons z l ih => intro r; simp [ih]
  have hout : ∀ (l : List ℕ) (r : List ℕ),
      l.foldl (fun acc i => (List.range k).foldl
        (fun acc' j => (if get dA i = get dA j then 1 else 0) :: acc') acc) r =
        (l.flatMap fun i => (List.range k).map fun j =>
          if get dA i = get dA j then 1 else 0).reverse ++ r := by
    intro l
    induction l with
    | nil => simp
    | cons i l ih =>
      intro r
      rw [List.foldl_cons, hin, ih, List.flatMap_cons, List.reverse_append, List.append_assoc]
  rw [hout]
  simp [patRowM]

/-! ### A fold with accumulator-dependent cost -/

/-- The cost of a fold whose body costs `cf acc x`. -/
def foldCost {α β : Type} (F : β → α → β) (cf : β → α → ℕ) : List α → β → ℕ
  | [], _ => 0
  | x :: xs, b => 1 + cf b x + foldCost F cf xs (F b x)

theorem foldCost_append {α β : Type} (F : β → α → β) (cf : β → α → ℕ) (x : α) :
    ∀ (l : List α) (b : β),
      foldCost F cf (l ++ [x]) b = foldCost F cf l b + (1 + cf (l.foldl F b) x)
  | [], b => by simp [foldCost]
  | y :: l, b => by
    simp only [List.cons_append, foldCost, List.foldl_cons, foldCost_append F cf x l]
    omega

section Specs

variable {S : Signature} {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

/-- A fold whose body has a functional model `F` and a cost `cf acc x` depending on the
accumulator. -/
theorem RunsWithin.foldList_gen {a' b' : Ty}
    {f : b'.denote → a'.denote → Prog S (a, b) Ty.denote b'} {F : b'.denote → a'.denote → b'.denote}
    {cf : b'.denote → a'.denote → ℕ} :
    ∀ (xs : List a'.denote) (init : b'.denote),
      (∀ acc, ∀ x ∈ xs, RunsWithin X body (f acc x) (F acc x) (cf acc x)) →
      RunsWithin X body (.foldList xs init f) (xs.foldl F init) (foldCost F cf xs init)
  | [], init, _ => by simpa [foldCost] using RunsWithin.foldList_nil
  | x :: xs, init, hf => by
    have h := RunsWithin.foldList_cons (hf init x List.mem_cons_self)
      (RunsWithin.foldList_gen xs (F init x) fun acc y hy => hf acc y (List.mem_cons_of_mem _ hy))
    simpa [foldCost] using h

end Specs

/-! ### Costs -/

/-- The cost of one extension of `L` lists. -/
def extCost (m L : ℕ) : ℕ := L * (4 * m + 1) + 2

/-- The cost of the digit lists. -/
def tupsCost (k m : ℕ) : ℕ := m + k + 5 + k * (1 + extCost m (m ^ k + 1))

/-- The cost of the table of products. -/
def pwTabCost (k m : ℕ) : ℕ := k * (11 * m + 15) + 6

/-- The cost of the information on one tuple, with `K` maps of positions. -/
def infoAtCost (k m K : ℕ) : ℕ := 8 * k ^ 2 + 2 * k + 11 + m * (10 * k + 5) + K * (6 * k + 4)

/-- The cost of the information on all tuples. -/
def infoCost (k m : ℕ) : ℕ :=
  k + m + 2 + tupsCost k m + (m ^ k + 1) + tupsCost k k + (k ^ k * (k + 4) + 2) + pwTabCost k m +
    2 * (m ^ k + 1) + (m ^ k * (infoAtCost k m (k ^ k) + 3) + 2)

theorem pow_le_pow_add_one {m i k : ℕ} (hi : i ≤ k) : m ^ i ≤ m ^ k + 1 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rcases Nat.eq_zero_or_pos i with rfl | hi'
    · simp
    · rw [Nat.zero_pow hi']
      exact Nat.zero_le _
  · exact (Nat.pow_le_pow_right hm hi).trans (Nat.le_succ _)

theorem length_ext (m : ℕ) (acc : List (List ℕ)) : (ext m acc).length = acc.length * m := by
  induction acc with
  | nil => simp [ext]
  | cons t acc ih =>
    simp only [ext, List.flatMap_cons, List.length_append, List.length_map,
      List.length_range] at ih ⊢
    rw [ih, List.length_cons, Nat.succ_mul]
    omega

theorem foldl_range_ext (m : ℕ) :
    ∀ j : ℕ, (List.range j).foldl (fun acc _ => ext m acc) [[]] = tupList j m
  | _ => rfl

theorem extCost_mono (m : ℕ) {L L' : ℕ} (h : L ≤ L') : extCost m L ≤ extCost m L' := by
  unfold extCost
  have := Nat.mul_le_mul_right (4 * m + 1) h
  omega

theorem foldCost_tups (k m : ℕ) :
    ∀ j : ℕ, j ≤ k → foldCost (fun acc _ => ext m acc) (fun acc _ => extCost m acc.length)
      (List.range j) [[]] ≤ j * (1 + extCost m (m ^ k + 1))
  | 0, _ => by simp [foldCost]
  | j + 1, hj => by
    rw [List.range_succ, foldCost_append, foldl_range_ext, length_tupList]
    have ih := foldCost_tups k m j (by omega)
    have h2 := extCost_mono m (pow_le_pow_add_one (m := m) (by omega : j ≤ k))
    rw [Nat.succ_mul]
    omega

section Specs

variable {S : Signature} {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

theorem RunsWithin.extTProg (m : ℕ) (r : List (List ℕ)) (t : List ℕ) :
    RunsWithin X body (Coherent.extTProg (List.range m) r t)
      ((List.range m).foldl (fun r' z => (z :: t) :: r') r) (3 * m) := by
  have h := RunsWithin.foldList_of (X := X) (body := body) (a' := .nat)
    (b' := .list (.list .nat)) (cf := fun _ => 2) (F := fun r' z => (z :: t) :: r')
    (f := fun r' z => .bind (.op2 .cons z t) fun zt => .op2 .cons zt r') (List.range m) r
    fun r' z _ => RunsWithin.bind_le (RunsWithin.prim _ _) (RunsWithin.prim _ _)
      (by simp [Prim.cost])
  rw [sum_map_const, List.length_range] at h
  exact h.mono (by omega)

theorem RunsWithin.extProg (m : ℕ) (acc : List (List ℕ)) :
    RunsWithin X body (Coherent.extProg (List.range m) acc) (ext m acc) (extCost m acc.length) := by
  have hfold := RunsWithin.foldList_of (X := X) (body := body) (cf := fun _ => 3 * m)
    (F := fun r t => (List.range m).foldl (fun r' z => (z :: t) :: r') r)
    (f := fun r t => Coherent.extTProg (List.range m) r t) acc []
    fun r t _ => RunsWithin.extTProg m r t
  rw [sum_map_const, foldl_ext_eq, List.append_nil] at hfold
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step hfold
    exact (RunsWithin.prim _ _).of_eq (by simp [Prim.eval])
  case hc =>
    simp only [Prim.cost, Args.head_cons, List.length_reverse, length_ext, extCost]
    nlinarith

theorem RunsWithin.tupsProg (k m : ℕ) :
    RunsWithin X body (Coherent.tupsProg k m) (tupList k m) (tupsCost k m) := by
  have hfold := RunsWithin.foldList_gen (X := X) (body := body) (a' := .nat)
    (b' := .list (.list .nat)) (F := fun acc _ => ext m acc)
    (cf := fun acc _ => extCost m acc.length)
    (f := fun acc _ => Coherent.extProg (List.range m) acc) (List.range k) [[]]
    fun acc _ _ => RunsWithin.extProg m acc
  replace hfold := hfold.mono (foldCost_tups k m k le_rfl)
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact hfold
  case hc =>
    simp only [Prim.cost, Args.head_cons, tupsCost]
    omega

theorem RunsWithin.mulNProg (a' b' : ℕ) :
    RunsWithin X body (Coherent.mulNProg a' b') (a' * b') (3 * a' + 2) := by
  have hfold := RunsWithin.foldList_of (X := X) (body := body) (a' := .nat) (b' := .nat)
    (cf := fun _ => 1) (F := fun acc _ => acc + b') (f := fun acc _ => .op2 .add acc b')
    (List.range a') 0 fun acc x _ => RunsWithin.prim_le rfl (by simp [Prim.cost])
  rw [sum_map_const, List.length_range] at hfold
  have hv : (List.range a').foldl (fun acc _ => acc + b') 0 = a' * b' := by
    have : ∀ n, (List.range n).foldl (fun acc _ => acc + b') 0 = n * b' := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [List.range_succ, List.foldl_append, ih]; simp [Nat.succ_mul]
    exact this a'
  rw [hv] at hfold
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact hfold
  case hc => simp only [Prim.cost, Args.head_cons]; omega

theorem RunsWithin.pwRowProg (m p : ℕ) :
    RunsWithin X body (Coherent.pwRowProg (List.range m) p) (pwRow m p) (8 * m + 6) := by
  have hfold := RunsWithin.foldList_of (X := X) (body := body)
    (a' := .nat) (b' := .prod .nat (.list .nat)) (cf := fun _ => 5)
    (F := fun st _ => (st.1 + p, st.1 :: st.2)) (f := fun st _ => Coherent.pwStepProg p st)
    (List.range m) (0, []) fun st _ _ => by
      apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        exact (RunsWithin.prim _ _).of_eq (by simp [Prim.eval])
      case hc => simp [Prim.cost]
  rw [sum_map_const, List.length_range, pwRow_fold] at hfold
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step hfold
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact (RunsWithin.prim _ _).of_eq (by simp [Prim.eval, pwRow])
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head_cons, List.length_reverse, List.length_map,
      List.length_range]
    omega

theorem RunsWithin.pwTabProg (k m : ℕ) :
    RunsWithin X body (Coherent.pwTabProg m (List.range k) (List.range m)) (pwTab k m)
      (pwTabCost k m) := by
  have hfold := RunsWithin.foldList_of (X := X) (body := body)
    (a' := .nat) (b' := .prod .nat (.list (.array .nat))) (cf := fun _ => 11 * m + 12)
    (F := fun st _ => (m * st.1, pwRow m st.1 :: st.2))
    (f := fun st _ => Coherent.pwTabStepProg m (List.range m) st)
    (List.range k) (1, []) fun st _ _ => by
      apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.pwRowProg m _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.mulNProg m _)
        exact (RunsWithin.prim _ _).of_eq (by simp [Prim.eval])
      case hc => simp [Prim.cost]; omega
  rw [sum_map_const, List.length_range, pwTab_fold] at hfold
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step hfold
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact (RunsWithin.prim _ _).of_eq (by simp [Prim.eval, pwTab])
  case hc => simp [Prim.cost, Prim.eval, pwTabCost]; nlinarith

theorem RunsWithin.get2Prog (pw : Array (Array ℕ)) (j v : ℕ) :
    RunsWithin X body (Coherent.get2Prog pw j v) (get2 pw j v) 2 :=
  (RunsWithin.prim _ _).bind_le (RunsWithin.prim_le (by
    simp [Prim.eval, get2, Array.getD_eq_getD_getElem?]; rfl) le_rfl) (by simp [Prim.cost])

theorem RunsWithin.codeStepProg (pw : Array (Array ℕ)) (dA τA : Array ℕ) (acc i : ℕ) :
    RunsWithin X body (Coherent.codeStepProg pw dA τA acc i)
      (acc + get2 pw i (get dA (get τA i))) 5 := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.get2Prog _ _ _)
    exact (RunsWithin.prim _ _).of_eq (by
      simp [Prim.eval, get, Array.getD_eq_getD_getElem?, Ty.default])
  case hc => simp [Prim.cost]

theorem RunsWithin.codeProg (pw : Array (Array ℕ)) (dA τA : Array ℕ) (k : ℕ) :
    RunsWithin X body (Coherent.codeProg pw dA τA (List.range k)) (codeM pw dA τA k)
      (6 * k + 1) := by
  have hfold := RunsWithin.foldList_of (X := X) (body := body) (cf := fun _ => 5)
    (F := fun acc i => acc + get2 pw i (get dA (get τA i)))
    (f := fun acc i => Coherent.codeStepProg pw dA τA acc i) (List.range k) 0
    fun acc i _ => RunsWithin.codeStepProg pw dA τA acc i
  rw [sum_map_const, List.length_range] at hfold
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    exact hfold
  case hc => simp [Prim.cost]; omega

theorem RunsWithin.nbrRowProg (pw : Array (Array ℕ)) (t : ℕ) (dA : Array ℕ) (k m : ℕ) :
    RunsWithin X body (Coherent.nbrRowProg pw t dA (List.range k) (List.range m))
      (nbrRowM pw t dA k m) (m * (10 * k + 5) + 2) := by
  have hcode : ∀ z j, RunsWithin X body (Coherent.nbrCodeProg pw t dA z j)
      (t - get2 pw j (get dA j) + get2 pw j z) 7 := fun z j => by
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.get2Prog _ _ _)
      run_step (RunsWithin.get2Prog _ _ _)
      run_step (RunsWithin.prim _ _)
      exact (RunsWithin.prim _ _).of_eq (by
        simp [Prim.eval, get, Array.getD_eq_getD_getElem?, Ty.default])
    case hc => simp [Prim.cost]
  have hrow : ∀ z, RunsWithin X body
      (mapList (a' := .nat) (b' := .nat) (List.range k) fun j => Coherent.nbrCodeProg pw t dA z j)
      ((List.range k).map fun j => t - get2 pw j (get dA j) + get2 pw j z) (10 * k + 2) := by
    intro z
    have := RunsWithin.mapList_le (X := X) (body := body) (a' := .nat) (b' := .nat)
      (xs := List.range k) (fun j _ => hcode z j)
    rw [List.length_range] at this
    exact this.mono (by omega)
  have := RunsWithin.mapList_le (X := X) (body := body) (a' := .nat) (b' := .list .nat)
    (xs := List.range m) (fun z _ => hrow z)
  rw [List.length_range] at this
  exact this.mono (le_of_eq (by ring))

theorem RunsWithin.monoRowProg (pw : Array (Array ℕ)) (dA : Array ℕ) (mapsA : List (Array ℕ))
    (k : ℕ) :
    RunsWithin X body (Coherent.monoRowProg pw dA mapsA (List.range k))
      (monoRowM pw dA mapsA k) (mapsA.length * (6 * k + 4) + 2) := by
  have := RunsWithin.mapList_le (X := X) (body := body) (a' := .array .nat) (b' := .nat)
    (f := fun τA => Coherent.codeProg pw dA τA (List.range k)) (xs := mapsA)
    (fun τA _ => RunsWithin.codeProg pw dA τA k)
  exact this.mono (le_of_eq (by ring))

theorem RunsWithin.patRowProg (dA : Array ℕ) (k : ℕ) :
    RunsWithin X body (Coherent.patRowProg dA (List.range k)) (patRowM dA k)
      (8 * k ^ 2 + k + 2) := by
  have hbit : ∀ i acc j, RunsWithin X body (Coherent.patBitProg dA i acc j)
      ((if get dA i = get dA j then 1 else 0) :: acc) 6 := by
    intro i acc j
    by_cases h : get dA i = get dA j
    · apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.ite_pos (show (dA.getD i 0 == dA.getD j 0) = true by
          simpa [get] using h) (RunsWithin.prim _ _))
        exact (RunsWithin.prim _ _).of_eq (by simp [Prim.eval, h])
      case hc => simp [Prim.cost]
    · apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.ite_neg (show (dA.getD i 0 == dA.getD j 0) = false by
          simpa [get] using h) (RunsWithin.prim _ _))
        exact (RunsWithin.prim _ _).of_eq (by simp [Prim.eval, h])
      case hc => simp [Prim.cost]
  have hin : ∀ i acc, RunsWithin X body (Coherent.patRowIProg dA (List.range k) acc i)
      ((List.range k).foldl (fun acc' j => (if get dA i = get dA j then 1 else 0) :: acc') acc)
      (7 * k) := by
    intro i acc
    have := RunsWithin.foldList_of (X := X) (body := body) (cf := fun _ => 6)
      (F := fun acc' j => (if get dA i = get dA j then 1 else 0) :: acc')
      (f := fun acc' j => Coherent.patBitProg dA i acc' j) (List.range k) acc
      fun acc' j _ => hbit i acc' j
    rw [sum_map_const, List.length_range] at this
    exact this.mono (by omega)
  have hfold := RunsWithin.foldList_of (X := X) (body := body) (cf := fun _ => 7 * k)
    (f := fun acc i => Coherent.patRowIProg dA (List.range k) acc i) (List.range k) []
    fun acc i _ => hin i acc
  rw [sum_map_const, List.length_range] at hfold
  have hlen : ((List.range k).foldl (fun acc i => (List.range k).foldl
      (fun acc' j => (if get dA i = get dA j then 1 else 0) :: acc') acc) []).length = k * k := by
    rw [← List.length_reverse, patRow_fold]
    simp [patRowM, List.length_flatMap]
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step hfold
    exact (RunsWithin.prim _ _).of_eq (by simp only [Prim.eval]; exact patRow_fold dA k)
  case hc =>
    simp only [Prim.cost, Args.head_cons, hlen]
    nlinarith

theorem length_digitsOf (k m t : ℕ) : (digitsOf k m t).length = k := by
  simp [digitsOf]

theorem length_getD_tupList (k m t : ℕ) : ((tupList k m).getD t []).length ≤ k := by
  by_cases ht : t < m ^ k
  · rw [getD_tupList ht, length_digitsOf]
  · rw [List.getD_eq_default _ _ (by rw [length_tupList]; omega)]
    simp

theorem length_of_mem_tupList {k m : ℕ} {d : List ℕ} (hd : d ∈ tupList k m) : d.length = k := by
  rw [tupList_eq] at hd
  obtain ⟨t, _, rfl⟩ := List.mem_map.1 hd
  exact length_digitsOf k m t

theorem length_mapsArr (k : ℕ) : (mapsArr k).length = k ^ k := by
  simp [mapsArr, length_tupList]

theorem RunsWithin.infoAtProg (k m t : ℕ) :
    RunsWithin X body (Coherent.infoAtProg (pwTab k m) (tupList k m).toArray (mapsArr k)
      (List.range k) (List.range m) t) (infoAt k m t) (infoAtCost k m (k ^ k)) := by
  have hd := length_getD_tupList k m t
  have hget : Prim.eval (Prim.arrayGet (a := .list .nat))
      (.cons (tupList k m).toArray (.cons t .nil)) = (tupList k m).getD t [] := by
    simp [Prim.eval, Ty.default]
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.patRowProg _ k)
    run_step (RunsWithin.nbrRowProg _ t _ k m)
    run_step (RunsWithin.monoRowProg _ _ _ k)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    refine (RunsWithin.prim _ _).of_eq ?_
    have hget' : (tupList k m).toArray.getD t (Ty.default (.list .nat)) =
        (tupList k m).getD t [] := by
      simp [Ty.default, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
    simp only [Prim.eval, hget', infoAt]
  case hc =>
    simp only [Prim.cost, Args.head_cons, hget, length_mapsArr, infoAtCost]
    omega

/-- **The information on all tuples.** -/
theorem RunsWithin.infoProg (k m : ℕ) :
    RunsWithin X body (Coherent.infoProg k m) (infoL k m) (infoCost k m) := by
  have hmaps := RunsWithin.mapList_le (X := X) (body := body) (a' := .list .nat)
    (b' := .array .nat) (xs := tupList k k) (f := fun τ => .op1 .arrayOfList τ)
    (F := List.toArray) (c := k + 1) fun τ hτ => RunsWithin.prim_le rfl (by
      simp [Prim.cost, length_of_mem_tupList hτ])
  rw [length_tupList, show k + 1 + 3 = k + 4 from rfl] at hmaps
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.tupsProg k m)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.tupsProg k k)
    run_step hmaps
    run_step (RunsWithin.pwTabProg k m)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    refine (RunsWithin.mapList_le (F := infoAt k m) (c := infoAtCost k m (k ^ k))
      fun t _ => ?_).of_eq ?_
    · exact RunsWithin.infoAtProg k m t
    · simp [Prim.eval, length_tupList, infoL]
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head_cons, length_tupList, List.length_range, infoCost]
    omega

end Specs

/-! ### Well-formedness -/

section Wf

variable {S : Signature} {rec : Ty × Ty} {var₁ var₂ : Ty → Type} {r : Bool}
  {Γ : WfCtx var₁ var₂}

theorem wf_extProg {rm₁ : var₁ (.list .nat)} {rm₂ : var₂ (.list .nat)}
    {acc₁ : var₁ (.list (.list .nat))} {acc₂ : var₂ (.list (.list .nat))}
    (hrm : ⟨.list .nat, rm₁, rm₂⟩ ∈ Γ) (hacc : ⟨.list (.list .nat), acc₁, acc₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (extProg rm₁ acc₁) (extProg rm₂ acc₂) := by
  unfold extProg extTProg
  prog_wf

theorem wf_tupsProg {k₁ m₁ : var₁ .nat} {k₂ m₂ : var₂ .nat} (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ)
    (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (tupsProg k₁ m₁) (tupsProg k₂ m₂) := by
  unfold tupsProg
  refine .bind (.prim _ (.cons hm .nil)) fun _ _ => .bind (.prim _ (.cons (by simp [hk]) .nil))
    fun _ _ => .bind (.prim _ .nil) fun _ _ => .bind (.prim _ .nil) fun _ _ =>
    .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ =>
    .foldList (by simp) (by simp) fun _ _ _ _ => wf_extProg (by simp) (by simp)

theorem wf_pwTabProg {m₁ : var₁ .nat} {m₂ : var₂ .nat} {rk₁ rm₁ : var₁ (.list .nat)}
    {rk₂ rm₂ : var₂ (.list .nat)} (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) (hrk : ⟨.list .nat, rk₁, rk₂⟩ ∈ Γ)
    (hrm : ⟨.list .nat, rm₁, rm₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (pwTabProg m₁ rk₁ rm₁) (pwTabProg m₂ rk₂ rm₂) := by
  unfold pwTabProg pwTabStepProg pwRowProg pwStepProg mulNProg
  prog_wf

theorem wf_patRowProg {dA₁ : var₁ (.array .nat)} {dA₂ : var₂ (.array .nat)}
    {rk₁ : var₁ (.list .nat)} {rk₂ : var₂ (.list .nat)} (hdA : ⟨.array .nat, dA₁, dA₂⟩ ∈ Γ)
    (hrk : ⟨.list .nat, rk₁, rk₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (patRowProg dA₁ rk₁) (patRowProg dA₂ rk₂) := by
  unfold patRowProg patRowIProg patBitProg
  prog_wf

theorem wf_nbrRowProg {pw₁ : var₁ (.array (.array .nat))} {pw₂ : var₂ (.array (.array .nat))}
    {t₁ : var₁ .nat} {t₂ : var₂ .nat} {dA₁ : var₁ (.array .nat)} {dA₂ : var₂ (.array .nat)}
    {rk₁ rm₁ : var₁ (.list .nat)} {rk₂ rm₂ : var₂ (.list .nat)}
    (hpw : ⟨.array (.array .nat), pw₁, pw₂⟩ ∈ Γ) (ht : ⟨.nat, t₁, t₂⟩ ∈ Γ)
    (hdA : ⟨.array .nat, dA₁, dA₂⟩ ∈ Γ) (hrk : ⟨.list .nat, rk₁, rk₂⟩ ∈ Γ)
    (hrm : ⟨.list .nat, rm₁, rm₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (nbrRowProg pw₁ t₁ dA₁ rk₁ rm₁)
      (nbrRowProg pw₂ t₂ dA₂ rk₂ rm₂) := by
  unfold nbrRowProg
  refine wf_mapList hrm fun Γ' hΓ z₁ z₂ hz => wf_mapList (hΓ hrk) fun Γ'' hΓ' j₁ j₂ hj => ?_
  have := hΓ' (hΓ hpw)
  have := hΓ' (hΓ ht)
  have := hΓ' (hΓ hdA)
  have := hΓ' hz
  unfold nbrCodeProg get2Prog
  prog_wf

theorem wf_monoRowProg {pw₁ : var₁ (.array (.array .nat))} {pw₂ : var₂ (.array (.array .nat))}
    {dA₁ : var₁ (.array .nat)} {dA₂ : var₂ (.array .nat)}
    {mA₁ : var₁ (.list (.array .nat))} {mA₂ : var₂ (.list (.array .nat))}
    {rk₁ : var₁ (.list .nat)} {rk₂ : var₂ (.list .nat)}
    (hpw : ⟨.array (.array .nat), pw₁, pw₂⟩ ∈ Γ) (hdA : ⟨.array .nat, dA₁, dA₂⟩ ∈ Γ)
    (hmA : ⟨.list (.array .nat), mA₁, mA₂⟩ ∈ Γ) (hrk : ⟨.list .nat, rk₁, rk₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (monoRowProg pw₁ dA₁ mA₁ rk₁)
      (monoRowProg pw₂ dA₂ mA₂ rk₂) := by
  unfold monoRowProg
  refine wf_mapList hmA fun Γ' hΓ τ₁ τ₂ hτ => ?_
  have := hΓ hpw
  have := hΓ hdA
  have := hΓ hrk
  unfold codeProg codeStepProg get2Prog
  prog_wf

theorem wf_infoAtProg {pw₁ : var₁ (.array (.array .nat))} {pw₂ : var₂ (.array (.array .nat))}
    {tA₁ : var₁ (.array (.list .nat))} {tA₂ : var₂ (.array (.list .nat))}
    {mA₁ : var₁ (.list (.array .nat))} {mA₂ : var₂ (.list (.array .nat))}
    {rk₁ rm₁ : var₁ (.list .nat)} {rk₂ rm₂ : var₂ (.list .nat)} {t₁ : var₁ .nat} {t₂ : var₂ .nat}
    (hpw : ⟨.array (.array .nat), pw₁, pw₂⟩ ∈ Γ) (htA : ⟨.array (.list .nat), tA₁, tA₂⟩ ∈ Γ)
    (hmA : ⟨.list (.array .nat), mA₁, mA₂⟩ ∈ Γ) (hrk : ⟨.list .nat, rk₁, rk₂⟩ ∈ Γ)
    (hrm : ⟨.list .nat, rm₁, rm₂⟩ ∈ Γ) (ht : ⟨.nat, t₁, t₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (infoAtProg pw₁ tA₁ mA₁ rk₁ rm₁ t₁)
      (infoAtProg pw₂ tA₂ mA₂ rk₂ rm₂ t₂) := by
  unfold infoAtProg
  refine .bind (.prim _ (.cons htA (.cons ht .nil))) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (wf_patRowProg (by simp) (by simp [hrk])) fun _ _ =>
    .bind (wf_nbrRowProg (by simp [hpw]) (by simp [ht]) (by simp) (by simp [hrk])
      (by simp [hrm])) fun _ _ =>
    .bind (wf_monoRowProg (by simp [hpw]) (by simp) (by simp [hmA]) (by simp [hrk])) fun _ _ =>
    ?_
  prog_wf

theorem wf_infoProg {k₁ m₁ : var₁ .nat} {k₂ m₂ : var₂ .nat} (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ)
    (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (infoProg k₁ m₁) (infoProg k₂ m₂) := by
  unfold infoProg
  refine .bind (.prim _ (.cons hk .nil)) fun _ _ => .bind (.prim _ (.cons (by simp [hm]) .nil))
    fun _ _ => .bind (wf_tupsProg (by simp [hk]) (by simp [hm])) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (wf_tupsProg (by simp [hk]) (by simp [hk])) fun _ _ =>
    .bind (wf_mapList (by simp) fun Γ' _ _ _ h => by prog_wf) fun _ _ =>
    .bind (wf_pwTabProg (by simp [hm]) (by simp) (by simp)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => .bind (.prim _ (.cons (by simp) .nil))
    fun _ _ => wf_mapList (by simp) fun Γ' hΓ t₁ t₂ ht => wf_infoAtProg (hΓ (by simp))
      (hΓ (by simp)) (hΓ (by simp)) (hΓ (by simp)) (hΓ (by simp)) ht

end Wf

end GraphIso.Coherent
