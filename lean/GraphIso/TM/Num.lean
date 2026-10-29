module

public import GraphIso.TM.Sat
public import GraphIso.TM.Bits
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

/-!
# Numbers on stacks

Stage 17b (`PLAN-17.md` §5). Programs over the alphabet `Sym` with `4` registers (`Rg`). A
number, a list of bits `l` (least significant first), sits on a stack as `bits l ++ nd :: …`,
least significant bit on top. Each routine starts and ends with empty registers, and changes
only the stacks it names; its specification (`Sat`) gives the stacks it names and a step bound.

* `moveBits a b`: moves the bits of the number on `a` onto `b`, which reverses them, with an `nd`
  under them, and drops the `nd` of `a` (`moveBits_sat`, `6 |l| + 9` steps);
* `moveBits2 a b d`: the same onto two stacks (`moveBits2_sat`, `8 |l| + 12` steps);
* `copyNum a b t`: copies the number on `a` onto `b` through the stack `t`, which ends as it
  started (`copyNum_sat`, `14 |l| + 22` steps);
* `dropNum a`: removes the number on `a` (`dropNum_sat`, `2 |l| + 5` steps);
* `pushNum l a`: pushes the constant number `l` (`pushNum_sat`, `2 |l| + 1` steps; it keeps the
  registers, whatever they hold);
* `moveSeg s a b`: moves the symbols of `a` up to and including the first `s` onto `b`, one by
  one, so they end reversed with `s` on top (`moveSeg_sat`, `4 |w| + 7` steps for the segment
  `w ++ [s]` with `s ∉ w`);
* `dropSeg s a`: drops them (`dropSeg_sat`, `2 |w| + 5` steps);
* `erase a`: empties `a` (`erase_sat`, `2 |a| + 5` steps).

Registers are written `rv x₀ x₁ x₂ x₃` in proofs (`empty_eq_rv`, `update_rv_zero`, …).
-/

@[expose] public section

namespace GraphIso.TM

open Function

/-- The simulator's number of registers. -/
abbrev Rg : ℕ := 4

/-- The bits as symbols. -/
def bits (l : List Bool) : List Sym := l.map .bit

@[simp] theorem bits_nil : bits [] = [] := rfl
@[simp] theorem bits_cons (b : Bool) (l : List Bool) : bits (b :: l) = .bit b :: bits l := rfl
@[simp] theorem bits_append (l m : List Bool) : bits (l ++ m) = bits l ++ bits m :=
  List.map_append ..
@[simp] theorem length_bits (l : List Bool) : (bits l).length = l.length := List.length_map ..

/-- Register contents. -/
def rv (x₀ x₁ x₂ x₃ : Option Sym) : Regs Sym Rg := ![x₀, x₁, x₂, x₃]

section Rv

variable (x₀ x₁ x₂ x₃ y : Option Sym)

@[simp] theorem rv_zero : rv x₀ x₁ x₂ x₃ 0 = x₀ := rfl
@[simp] theorem rv_one : rv x₀ x₁ x₂ x₃ 1 = x₁ := rfl
@[simp] theorem rv_two : rv x₀ x₁ x₂ x₃ 2 = x₂ := rfl
@[simp] theorem rv_three : rv x₀ x₁ x₂ x₃ 3 = x₃ := rfl

@[simp] theorem update_rv_zero : update (rv x₀ x₁ x₂ x₃) 0 y = rv y x₁ x₂ x₃ := by
  funext i; fin_cases i <;> rfl
@[simp] theorem update_rv_one : update (rv x₀ x₁ x₂ x₃) 1 y = rv x₀ y x₂ x₃ := by
  funext i; fin_cases i <;> rfl
@[simp] theorem update_rv_two : update (rv x₀ x₁ x₂ x₃) 2 y = rv x₀ x₁ y x₃ := by
  funext i; fin_cases i <;> rfl
@[simp] theorem update_rv_three : update (rv x₀ x₁ x₂ x₃) 3 y = rv x₀ x₁ x₂ y := by
  funext i; fin_cases i <;> rfl

theorem empty_eq_rv : (Regs.empty : Regs Sym Rg) = rv none none none none := by
  funext i; fin_cases i <;> rfl

end Rv

/-- Disjunction of conditions. -/
def Cond.or {Γ : Type} {R : ℕ} (b d : Cond Γ R) : Cond Γ R := .not (.and (.not b) (.not d))

@[simp] theorem Cond.or_eval {Γ : Type} {R : ℕ} [DecidableEq Γ] (b d : Cond Γ R) (v : Regs Γ R) :
    (b.or d).eval v = (b.eval v || d.eval v) := by
  simp [Cond.or, Cond.eval]

/-- The register holds a bit. -/
def isBit (r : Fin Rg) : Cond Sym Rg := .or (.is r (some (.bit false))) (.is r (some (.bit true)))

theorem isBit_eval_bit {v : Regs Sym Rg} {r : Fin Rg} (b : Bool) (h : v r = some (.bit b)) :
    (isBit r).eval v = true := by
  cases b <;> simp [isBit, Cond.eval, h]

theorem isBit_eval_nd {v : Regs Sym Rg} {r : Fin Rg} (h : v r = some .nd) :
    (isBit r).eval v = false := by
  simp [isBit, Cond.eval, h]

variable {K P : Type} [DecidableEq K] {prog : Program K Sym Rg P}

/-! ### Moving numbers -/

/-- Move the bits on `a` down to `nd` onto `b` (reversing them), with an `nd` under them, and
drop the `nd` of `a`. -/
def moveBits (a b : K) : Code K Sym Rg P :=
  .seq (.act (.push b .nd))
    (.seq (.act (.peek a 0))
      (.seq (.loop (isBit 0)
          (.seq (.act (.pop a 0)) (.seq (.act (.pushReg b 0)) (.act (.peek a 0)))))
        (.seq (.act (.pop a 0)) (.act (.set 0 none)))))

theorem moveBits_sat {a b : K} (hab : a ≠ b) {c : Cfg K Sym Rg} {l : List Bool}
    {rest : List Sym} (hv : c.regs = Regs.empty) (ha : c.stk a = bits l ++ .nd :: rest) :
    Sat prog (moveBits a b) c (6 * l.length + 9) fun c' =>
      c'.regs = Regs.empty ∧ c'.stk a = rest ∧ c'.stk b = bits l.reverse ++ .nd :: c.stk b ∧
        ∀ j, j ≠ a → j ≠ b → c'.stk j = c.stk j := by
  rw [empty_eq_rv] at hv ⊢
  have hloop := Sat.loop (prog := prog) (b := isBit 0)
    (x := .seq (.act (.pop a 0)) (.seq (.act (.pushReg b 0)) (.act (.peek a 0)))) (t := 5)
    (I := fun m c₁ => ∃ l₁ l₂, l₁ ++ l₂ = l ∧ l₂.length = m ∧
      c₁.regs = rv (c₁.stk a).head? none none none ∧ c₁.stk a = bits l₂ ++ .nd :: rest ∧
      c₁.stk b = bits l₁.reverse ++ .nd :: c.stk b ∧ ∀ j, j ≠ a → j ≠ b → c₁.stk j = c.stk j)
    (Q := fun c₁ => c₁.regs = rv (some .nd) none none none ∧ c₁.stk a = .nd :: rest ∧
      c₁.stk b = bits l.reverse ++ .nd :: c.stk b ∧ ∀ j, j ≠ a → j ≠ b → c₁.stk j = c.stk j)
    (fun m c₁ ⟨l₁, l₂, hl, hlen, hr, ha₁, hb₁, hj₁⟩ => by
      obtain ⟨x, l₂, rfl⟩ : ∃ x l₂', l₂ = x :: l₂' := by
        cases l₂ with
        | nil => simp at hlen
        | cons x l₂' => exact ⟨x, l₂', rfl⟩
      refine ⟨isBit_eval_bit x (by simp [hr, ha₁]), ?_⟩
      refine Sat.act_seq (by omega) (Sat.act_seq (by omega) (Sat.act_le (by omega) ?_))
      refine ⟨l₁ ++ [x], l₂, by simp [← hl], by simpa using hlen, ?_, ?_, ?_, ?_⟩
      · simp [Act.run, hr]
      · simp [Act.run, ha₁, update_of_ne hab]
      · simp [Act.run, ha₁, hb₁, hr, update_of_ne (Ne.symm hab)]
      · intro j hja hjb
        simp [Act.run, update_of_ne hja, update_of_ne hjb, hj₁ j hja hjb])
    (fun c₁ ⟨l₁, l₂, hl, hlen, hr, ha₁, hb₁, hj₁⟩ => by
      obtain rfl : l₂ = [] := List.eq_nil_of_length_eq_zero hlen
      simp only [List.append_nil] at hl
      subst hl
      exact ⟨isBit_eval_nd (by simp [hr, ha₁]), by simp [hr, ha₁], by simpa using ha₁, hb₁,
        hj₁⟩)
  unfold moveBits
  refine Sat.act_seq (by omega) (Sat.act_seq (by omega) ?_)
  refine Sat.seq_le (hloop l.length _ ⟨[], l, by simp, rfl, ?_, ?_, ?_, ?_⟩) (by omega)
    fun c₃ ⟨hr₃, ha₃, hb₃, hj₃⟩ => ?_
  · simp [Act.run, hv]
  · simp [Act.run, ha, update_of_ne hab]
  · simp [Act.run]
  · intro j hja hjb; simp [Act.run, update_of_ne hjb]
  refine Sat.act_seq (by omega) (Sat.act_le (by omega) ?_)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [Act.run, hr₃]
  · simp [Act.run, ha₃]
  · simp [Act.run, hb₃, update_of_ne (Ne.symm hab)]
  · intro j hja hjb; simp [Act.run, update_of_ne hja, hj₃ j hja hjb]

/-- Move the bits on `a` down to `nd` onto both `b` and `d` (reversing them), with an `nd` under
them, and drop the `nd` of `a`. -/
def moveBits2 (a b d : K) : Code K Sym Rg P :=
  .seq (.act (.push b .nd))
    (.seq (.act (.push d .nd))
      (.seq (.act (.peek a 0))
        (.seq (.loop (isBit 0)
            (.seq (.act (.pop a 0))
              (.seq (.act (.pushReg b 0)) (.seq (.act (.pushReg d 0)) (.act (.peek a 0))))))
          (.seq (.act (.pop a 0)) (.act (.set 0 none))))))

theorem moveBits2_sat {a b d : K} (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
    {c : Cfg K Sym Rg} {l : List Bool} {rest : List Sym} (hv : c.regs = Regs.empty)
    (ha : c.stk a = bits l ++ .nd :: rest) :
    Sat prog (moveBits2 a b d) c (8 * l.length + 11) fun c' =>
      c'.regs = Regs.empty ∧ c'.stk a = rest ∧ c'.stk b = bits l.reverse ++ .nd :: c.stk b ∧
        c'.stk d = bits l.reverse ++ .nd :: c.stk d ∧
        ∀ j, j ≠ a → j ≠ b → j ≠ d → c'.stk j = c.stk j := by
  rw [empty_eq_rv] at hv ⊢
  have hloop := Sat.loop (prog := prog) (b := isBit 0)
    (x := .seq (.act (.pop a 0))
      (.seq (.act (.pushReg b 0)) (.seq (.act (.pushReg d 0)) (.act (.peek a 0))))) (t := 7)
    (I := fun m c₁ => ∃ l₁ l₂, l₁ ++ l₂ = l ∧ l₂.length = m ∧
      c₁.regs = rv (c₁.stk a).head? none none none ∧ c₁.stk a = bits l₂ ++ .nd :: rest ∧
      c₁.stk b = bits l₁.reverse ++ .nd :: c.stk b ∧
      c₁.stk d = bits l₁.reverse ++ .nd :: c.stk d ∧
      ∀ j, j ≠ a → j ≠ b → j ≠ d → c₁.stk j = c.stk j)
    (Q := fun c₁ => c₁.regs = rv (some .nd) none none none ∧ c₁.stk a = .nd :: rest ∧
      c₁.stk b = bits l.reverse ++ .nd :: c.stk b ∧ c₁.stk d = bits l.reverse ++ .nd :: c.stk d ∧
      ∀ j, j ≠ a → j ≠ b → j ≠ d → c₁.stk j = c.stk j)
    (fun m c₁ ⟨l₁, l₂, hl, hlen, hr, ha₁, hb₁, hd₁, hj₁⟩ => by
      obtain ⟨x, l₂, rfl⟩ : ∃ x l₂', l₂ = x :: l₂' := by
        cases l₂ with
        | nil => simp at hlen
        | cons x l₂' => exact ⟨x, l₂', rfl⟩
      refine ⟨isBit_eval_bit x (by simp [hr, ha₁]), ?_⟩
      refine Sat.act_seq (by omega) (Sat.act_seq (by omega)
        (Sat.act_seq (by omega) (Sat.act_le (by omega) ?_)))
      refine ⟨l₁ ++ [x], l₂, by simp [← hl], by simpa using hlen, ?_, ?_, ?_, ?_, ?_⟩
      · simp [Act.run, hr]
      · simp [Act.run, ha₁, update_of_ne hab, update_of_ne had]
      · simp [Act.run, ha₁, hb₁, hr, update_of_ne (Ne.symm hab), update_of_ne hbd]
      · simp [Act.run, ha₁, hd₁, hr, update_of_ne (Ne.symm had), update_of_ne (Ne.symm hbd),
          update_of_ne had]
      · intro j hja hjb hjd
        simp [Act.run, update_of_ne hja, update_of_ne hjb, update_of_ne hjd, hj₁ j hja hjb hjd])
    (fun c₁ ⟨l₁, l₂, hl, hlen, hr, ha₁, hb₁, hd₁, hj₁⟩ => by
      obtain rfl : l₂ = [] := List.eq_nil_of_length_eq_zero hlen
      simp only [List.append_nil] at hl
      subst hl
      exact ⟨isBit_eval_nd (by simp [hr, ha₁]), by simp [hr, ha₁], by simpa using ha₁, hb₁, hd₁,
        hj₁⟩)
  unfold moveBits2
  refine Sat.act_seq (by omega) (Sat.act_seq (by omega) (Sat.act_seq (by omega) ?_))
  refine Sat.seq_le (hloop l.length _ ⟨[], l, by simp, rfl, ?_, ?_, ?_, ?_, ?_⟩) (by omega)
    fun c₃ ⟨hr₃, ha₃, hb₃, hd₃, hj₃⟩ => ?_
  · simp [Act.run, hv]
  · simp [Act.run, ha, update_of_ne hab, update_of_ne had]
  · simp [Act.run, update_of_ne hbd]
  · simp [Act.run, update_of_ne (Ne.symm hbd)]
  · intro j hja hjb hjd; simp [Act.run, update_of_ne hjb, update_of_ne hjd]
  refine Sat.act_seq (by omega) (Sat.act_le (by omega) ?_)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [Act.run, hr₃]
  · simp [Act.run, ha₃]
  · simp [Act.run, hb₃, update_of_ne (Ne.symm hab)]
  · simp [Act.run, hd₃, update_of_ne (Ne.symm had)]
  · intro j hja hjb hjd; simp [Act.run, update_of_ne hja, hj₃ j hja hjb hjd]

/-- Copy the number on `a` onto `b`, through `t`. -/
def copyNum (a b t : K) : Code K Sym Rg P := .seq (moveBits a t) (moveBits2 t a b)

theorem copyNum_sat {a b t : K} (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) {c : Cfg K Sym Rg}
    {l : List Bool} {rest : List Sym} (hv : c.regs = Regs.empty)
    (ha : c.stk a = bits l ++ .nd :: rest) :
    Sat prog (copyNum a b t) c (14 * l.length + 21) fun c' =>
      c'.regs = Regs.empty ∧ c'.stk b = bits l ++ .nd :: c.stk b ∧
        ∀ j, j ≠ b → c'.stk j = c.stk j := by
  refine Sat.seq_le (moveBits_sat hat hv ha) (by omega) fun c₁ ⟨hr₁, ha₁, ht₁, hj₁⟩ => ?_
  refine (moveBits2_sat (Ne.symm hat) (Ne.symm hbt) hab hr₁ ht₁).mono (by simp; omega)
    fun c₂ ⟨hr₂, ht₂, ha₂, hb₂, hj₂⟩ => ⟨hr₂, ?_, fun j hjb => ?_⟩
  · rw [hb₂, hj₁ b hab.symm hbt]; simp
  · by_cases hja : j = a
    · subst hja; rw [ha₂, ha₁, ha]; simp
    by_cases hjt : j = t
    · subst hjt; rw [ht₂]
    rw [hj₂ j hjt hja hjb, hj₁ j hja hjt]

/-- Remove the number on `a`. -/
def dropNum (a : K) : Code K Sym Rg P :=
  .seq (.act (.pop a 0)) (.seq (.loop (isBit 0) (.act (.pop a 0))) (.act (.set 0 none)))

theorem exists_cons_bits (l : List Bool) (rest : List Sym) :
    ∃ s t, bits l ++ .nd :: rest = s :: t := by
  cases l <;> simp

theorem dropNum_sat {a : K} {c : Cfg K Sym Rg} {l : List Bool} {rest : List Sym}
    (hv : c.regs = Regs.empty) (ha : c.stk a = bits l ++ .nd :: rest) :
    Sat prog (dropNum a) c (2 * l.length + 5) fun c' =>
      c'.regs = Regs.empty ∧ c'.stk a = rest ∧ ∀ j, j ≠ a → c'.stk j = c.stk j := by
  rw [empty_eq_rv] at hv ⊢
  have hloop := Sat.loop (prog := prog) (b := isBit 0) (x := .act (.pop a 0)) (t := 1)
    (I := fun m c₁ => ∃ l₂ s, l₂.length = m ∧ bits l₂ ++ .nd :: rest = s :: c₁.stk a ∧
      c₁.regs = rv (some s) none none none ∧ ∀ j, j ≠ a → c₁.stk j = c.stk j)
    (Q := fun c₁ => c₁.regs = rv (some .nd) none none none ∧ c₁.stk a = rest ∧
      ∀ j, j ≠ a → c₁.stk j = c.stk j)
    (fun m c₁ ⟨l₂, s, hlen, hl, hr, hj₁⟩ => by
      obtain ⟨x, l₂, rfl⟩ : ∃ x l₂', l₂ = x :: l₂' := by
        cases l₂ with
        | nil => simp at hlen
        | cons x l₂' => exact ⟨x, l₂', rfl⟩
      simp only [bits_cons, List.cons_append, List.cons.injEq] at hl
      obtain ⟨rfl, hl⟩ := hl
      obtain ⟨s', t', e⟩ := exists_cons_bits l₂ rest
      refine ⟨isBit_eval_bit x (by simp [hr]), Sat.act_le le_rfl ?_⟩
      refine ⟨l₂, s', by simpa using hlen, ?_, ?_, ?_⟩
      · simp [Act.run, ← hl, e]
      · simp [Act.run, hr, ← hl, e]
      · intro j hja; simp [Act.run, update_of_ne hja, hj₁ j hja])
    (fun c₁ ⟨l₂, s, hlen, hl, hr, hj₁⟩ => by
      obtain rfl : l₂ = [] := List.eq_nil_of_length_eq_zero hlen
      simp only [bits_nil, List.nil_append, List.cons.injEq] at hl
      obtain ⟨rfl, hl⟩ := hl
      exact ⟨isBit_eval_nd (by simp [hr]), hr, hl.symm, hj₁⟩)
  obtain ⟨s, t, e⟩ := exists_cons_bits l rest
  unfold dropNum
  refine Sat.act_seq (by omega) (Sat.seq_le (hloop l.length _ ⟨l, s, rfl, ?_, ?_, ?_⟩) (by omega)
    fun c₃ ⟨hr₃, ha₃, hj₃⟩ => Sat.act_le (by omega) ⟨?_, ?_, ?_⟩)
  · simp [Act.run, ha, e]
  · simp [Act.run, hv, ha, e]
  · intro j hja; simp [Act.run, update_of_ne hja]
  · simp [Act.run, hr₃]
  · simp [Act.run, ha₃]
  · intro j hja; simp [Act.run, hj₃ j hja]

/-- Push the constant number `l`. -/
def pushNum : List Bool → K → Code K Sym Rg P
  | [], a => .act (.push a .nd)
  | b :: l, a => .seq (pushNum l a) (.act (.push a (.bit b)))

theorem pushNum_sat (a : K) (c : Cfg K Sym Rg) :
    ∀ l : List Bool, Sat prog (pushNum l a) c (2 * l.length + 1) fun c' =>
      c'.regs = c.regs ∧ c'.stk a = bits l ++ .nd :: c.stk a ∧
        ∀ j, j ≠ a → c'.stk j = c.stk j
  | [] => Sat.act_le le_rfl ⟨rfl, by simp [Act.run], fun j hja => by
      simp [Act.run, update_of_ne hja]⟩
  | b :: l => Sat.seq_le (pushNum_sat a c l) (by simp)
      fun c₁ ⟨hr₁, ha₁, hj₁⟩ => Sat.act_le (by simp; omega)
        ⟨hr₁, by simp [Act.run, ha₁], fun j hja => by simp [Act.run, update_of_ne hja, hj₁ j hja]⟩

/-! ### Segments -/

/-- Move the symbols of `a` up to and including the first `s` onto `b`, one by one (so they end
reversed, with `s` on top). -/
def moveSeg (s : Sym) (a b : K) : Code K Sym Rg P :=
  .seq (.act (.pop a 0))
    (.seq (.act (.pushReg b 0))
      (.seq (.loop (.not (.is 0 (some s))) (.seq (.act (.pop a 0)) (.act (.pushReg b 0))))
        (.act (.set 0 none))))

/-- In `w ++ [s]` with `s ∉ w`, an element followed by `w₂` is `s` exactly when `w₂ = []`. -/
theorem eq_last_iff {s x : Sym} {w w₁ w₂ : List Sym} (hw : s ∉ w)
    (h : w₁ ++ x :: w₂ = w ++ [s]) : x = s ↔ w₂ = [] := by
  constructor
  · intro hx
    subst hx
    by_contra hne
    obtain ⟨y, w₃, rfl⟩ := List.exists_cons_of_ne_nil hne
    have : x ∈ w := by
      have h' : (w₁ ++ x :: y :: w₃).dropLast = (w ++ [x]).dropLast := by rw [h]
      rw [List.dropLast_concat] at h'
      rw [← h']
      simp [List.dropLast_append_of_ne_nil, List.dropLast_cons_of_ne_nil]
    exact hw this
  · rintro rfl
    exact (List.append_inj' h rfl).2 |> List.cons.inj |>.1

theorem moveSeg_sat {s : Sym} {a b : K} (hab : a ≠ b) {c : Cfg K Sym Rg} {w rest : List Sym}
    (hw : s ∉ w) (hv : c.regs = Regs.empty) (ha : c.stk a = w ++ s :: rest) :
    Sat prog (moveSeg s a b) c (4 * w.length + 7) fun c' =>
      c'.regs = Regs.empty ∧ c'.stk a = rest ∧ c'.stk b = s :: w.reverse ++ c.stk b ∧
        ∀ j, j ≠ a → j ≠ b → c'.stk j = c.stk j := by
  rw [empty_eq_rv] at hv ⊢
  have hloop := Sat.loop (prog := prog) (b := .not (.is 0 (some s)))
    (x := .seq (.act (.pop a 0)) (.act (.pushReg b 0))) (t := 3)
    (I := fun m c₁ => ∃ w₁ x w₂, w₁ ++ x :: w₂ = w ++ [s] ∧ w₂.length = m ∧
      c₁.regs = rv (some x) none none none ∧ c₁.stk a = w₂ ++ rest ∧
      c₁.stk b = x :: w₁.reverse ++ c.stk b ∧ ∀ j, j ≠ a → j ≠ b → c₁.stk j = c.stk j)
    (Q := fun c₁ => c₁.regs = rv (some s) none none none ∧ c₁.stk a = rest ∧
      c₁.stk b = s :: w.reverse ++ c.stk b ∧ ∀ j, j ≠ a → j ≠ b → c₁.stk j = c.stk j)
    (fun m c₁ ⟨w₁, x, w₂, hl, hlen, hr, ha₁, hb₁, hj₁⟩ => by
      obtain ⟨y, w₂, rfl⟩ : ∃ y w₂', w₂ = y :: w₂' := by
        cases w₂ with
        | nil => simp at hlen
        | cons y w₂' => exact ⟨y, w₂', rfl⟩
      have hx : x ≠ s := fun h => List.cons_ne_nil _ _ ((eq_last_iff hw hl).1 h)
      refine ⟨by simp [Cond.eval, hr, hx], ?_⟩
      refine Sat.act_seq (by omega) (Sat.act_le (by omega) ?_)
      refine ⟨w₁ ++ [x], y, w₂, by simp [← hl], by simpa using hlen, ?_, ?_, ?_, ?_⟩
      · simp [Act.run, ha₁, hr]
      · simp [Act.run, ha₁, update_of_ne hab]
      · simp [Act.run, ha₁, hb₁, update_of_ne (Ne.symm hab)]
      · intro j hja hjb
        simp [Act.run, update_of_ne hja, update_of_ne hjb, hj₁ j hja hjb])
    (fun c₁ ⟨w₁, x, w₂, hl, hlen, hr, ha₁, hb₁, hj₁⟩ => by
      obtain rfl : w₂ = [] := List.eq_nil_of_length_eq_zero hlen
      have hxs : x = s := (eq_last_iff hw hl).2 rfl
      subst hxs
      have hw₁ : w₁ = w := (List.append_inj' hl rfl).1
      subst hw₁
      exact ⟨by simp [Cond.eval, hr], hr, by simpa using ha₁, hb₁, hj₁⟩)
  obtain ⟨x, w₂, hx⟩ : ∃ x w₂, w ++ [s] = x :: w₂ := by cases w <;> simp
  unfold moveSeg
  refine Sat.act_seq (by omega) (Sat.act_seq (by omega) (Sat.seq_le (hloop w.length _
    ⟨[], x, w₂, by simp [hx], ?_, ?_, ?_, ?_, ?_⟩) (by omega)
    fun c₃ ⟨hr₃, ha₃, hb₃, hj₃⟩ => Sat.act_le (by omega) ⟨?_, ?_, ?_, ?_⟩))
  · have := congrArg List.length hx; simp at this; omega
  · have h₁ : c.stk a = x :: (w₂ ++ rest) := by rw [ha, ← List.cons_append, ← hx]; simp
    simp [Act.run, hv, h₁]
  · have h₁ : c.stk a = x :: (w₂ ++ rest) := by rw [ha, ← List.cons_append, ← hx]; simp
    simp [Act.run, h₁, update_of_ne hab]
  · have h₁ : c.stk a = x :: (w₂ ++ rest) := by rw [ha, ← List.cons_append, ← hx]; simp
    simp [Act.run, h₁, update_of_ne (Ne.symm hab)]
  · intro j hja hjb; simp [Act.run, update_of_ne hja, update_of_ne hjb]
  · simp [Act.run, hr₃]
  · simp [Act.run, ha₃]
  · simp [Act.run, hb₃]
  · intro j hja hjb; simp [Act.run, hj₃ j hja hjb]

/-- Drop the symbols of `a` up to and including the first `s`. -/
def dropSeg (s : Sym) (a : K) : Code K Sym Rg P :=
  .seq (.act (.pop a 0)) (.seq (.loop (.not (.is 0 (some s))) (.act (.pop a 0)))
    (.act (.set 0 none)))

theorem dropSeg_sat {s : Sym} {a : K} {c : Cfg K Sym Rg} {w rest : List Sym}
    (hw : s ∉ w) (hv : c.regs = Regs.empty) (ha : c.stk a = w ++ s :: rest) :
    Sat prog (dropSeg s a) c (2 * w.length + 5) fun c' =>
      c'.regs = Regs.empty ∧ c'.stk a = rest ∧ ∀ j, j ≠ a → c'.stk j = c.stk j := by
  rw [empty_eq_rv] at hv ⊢
  have hloop := Sat.loop (prog := prog) (b := .not (.is 0 (some s))) (x := .act (.pop a 0))
    (t := 1)
    (I := fun m c₁ => ∃ w₁ x w₂, w₁ ++ x :: w₂ = w ++ [s] ∧ w₂.length = m ∧
      c₁.regs = rv (some x) none none none ∧ c₁.stk a = w₂ ++ rest ∧
      ∀ j, j ≠ a → c₁.stk j = c.stk j)
    (Q := fun c₁ => c₁.regs = rv (some s) none none none ∧ c₁.stk a = rest ∧
      ∀ j, j ≠ a → c₁.stk j = c.stk j)
    (fun m c₁ ⟨w₁, x, w₂, hl, hlen, hr, ha₁, hj₁⟩ => by
      obtain ⟨y, w₂, rfl⟩ : ∃ y w₂', w₂ = y :: w₂' := by
        cases w₂ with
        | nil => simp at hlen
        | cons y w₂' => exact ⟨y, w₂', rfl⟩
      have hx : x ≠ s := fun h => List.cons_ne_nil _ _ ((eq_last_iff hw hl).1 h)
      refine ⟨by simp [Cond.eval, hr, hx], Sat.act_le le_rfl ?_⟩
      refine ⟨w₁ ++ [x], y, w₂, by simp [← hl], by simpa using hlen, ?_, ?_, ?_⟩
      · simp [Act.run, ha₁, hr]
      · simp [Act.run, ha₁]
      · intro j hja; simp [Act.run, update_of_ne hja, hj₁ j hja])
    (fun c₁ ⟨w₁, x, w₂, hl, hlen, hr, ha₁, hj₁⟩ => by
      obtain rfl : w₂ = [] := List.eq_nil_of_length_eq_zero hlen
      have hxs : x = s := (eq_last_iff hw hl).2 rfl
      subst hxs
      exact ⟨by simp [Cond.eval, hr], hr, by simpa using ha₁, hj₁⟩)
  obtain ⟨x, w₂, hx⟩ : ∃ x w₂, w ++ [s] = x :: w₂ := by cases w <;> simp
  have h₁ : c.stk a = x :: (w₂ ++ rest) := by rw [ha, ← List.cons_append, ← hx]; simp
  unfold dropSeg
  refine Sat.act_seq (by omega) (Sat.seq_le (hloop w.length _
    ⟨[], x, w₂, by simp [hx], ?_, ?_, ?_, ?_⟩) (by omega)
    fun c₃ ⟨hr₃, ha₃, hj₃⟩ => Sat.act_le (by omega) ⟨?_, ?_, ?_⟩)
  · have := congrArg List.length hx; simp at this; omega
  · simp [Act.run, hv, h₁]
  · simp [Act.run, h₁]
  · intro j hja; simp [Act.run, update_of_ne hja]
  · simp [Act.run, hr₃]
  · simp [Act.run, ha₃]
  · intro j hja; simp [Act.run, hj₃ j hja]

/-- Empty the stack `a`. -/
def erase (a : K) : Code K Sym Rg P :=
  .seq (.act (.pop a 0)) (.seq (.loop (.not (.is 0 none)) (.act (.pop a 0))) (.act (.set 0 none)))

theorem erase_sat {a : K} {c : Cfg K Sym Rg} (hv : c.regs = Regs.empty) :
    Sat prog (erase a) c (2 * (c.stk a).length + 5) fun c' =>
      c'.regs = Regs.empty ∧ c'.stk a = [] ∧ ∀ j, j ≠ a → c'.stk j = c.stk j := by
  rw [empty_eq_rv] at hv ⊢
  have hloop := Sat.loop (prog := prog) (b := .not (.is 0 none)) (x := .act (.pop a 0)) (t := 1)
    (I := fun m c₁ => ∃ o, c₁.regs = rv o none none none ∧
      ((m = 0 ∧ o = none ∧ c₁.stk a = []) ∨ (o ≠ none ∧ (c₁.stk a).length + 1 = m)) ∧
      ∀ j, j ≠ a → c₁.stk j = c.stk j)
    (Q := fun c₁ => c₁.regs = rv none none none none ∧ c₁.stk a = [] ∧
      ∀ j, j ≠ a → c₁.stk j = c.stk j)
    (fun m c₁ ⟨o, hr, hm, hj₁⟩ => by
      obtain ⟨ho, hlen⟩ : o ≠ none ∧ (c₁.stk a).length + 1 = m + 1 := by
        rcases hm with h | h
        · omega
        · exact h
      refine ⟨by simp [Cond.eval, hr, ho], Sat.act_le le_rfl ⟨(c₁.stk a).head?, ?_, ?_, ?_⟩⟩
      · simp [Act.run, hr]
      · cases h : c₁.stk a with
        | nil => simp [h] at hlen; simp [Act.run, h, hlen]
        | cons y l => simp [h] at hlen; simp [Act.run, h, hlen]
      · intro j hja; simp [Act.run, update_of_ne hja, hj₁ j hja])
    (fun c₁ ⟨o, hr, hm, hj₁⟩ => by
      obtain ⟨-, rfl, ha₁⟩ : 0 = 0 ∧ o = none ∧ c₁.stk a = [] := by
        rcases hm with h | h
        · exact h
        · omega
      exact ⟨by simp [Cond.eval, hr], hr, ha₁, hj₁⟩)
  unfold erase
  refine Sat.act_seq (by omega) (Sat.seq_le (hloop (c.stk a).length _
    ⟨(c.stk a).head?, ?_, ?_, ?_⟩) (by omega)
    fun c₃ ⟨hr₃, ha₃, hj₃⟩ => Sat.act_le (by omega) ⟨?_, ?_, ?_⟩)
  · simp [Act.run, hv]
  · cases h : c.stk a with
    | nil => simp [Act.run, h]
    | cons y l => simp [Act.run, h]
  · intro j hja; simp [Act.run, update_of_ne hja]
  · simp [Act.run, hr₃]
  · simp [Act.run, ha₃]
  · intro j hja; simp [Act.run, hj₃ j hja]

end GraphIso.TM
