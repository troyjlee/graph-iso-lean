module

public import Mathlib.Data.Fintype.Sum
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-!
# The simulator's alphabet and serial arithmetic on bit lists

Stage 17b (`PLAN-17.md` §5).

* **`Sym`**: bits `bit b`, the end mark `nd`, cell tags `tag t` (used from stage 17c) and four
  markers `mk i`; `Fintype`, as the tape alphabet of a `FinTM2` must be.
* **Numbers** are lists of bits `l`, least significant first and of any length, standing for
  `ofBits l = Σ lᵢ 2ⁱ` (`ofBits_append`, `ofBits_lt`).
* **`zipL f xs ys c`**: the serial bit processor that the stack routines run. It reads the two
  lists bit by bit (a missing bit reads as `false`), starting from the carry `c`, and returns the
  output bits, of length `max |xs| |ys|` (`length_zipL`), and the final carry. With the full adder
  it adds (`zipL_add_val`: the output with the final carry appended has value
  `ofBits xs + ofBits ys`), with the full subtractor it subtracts (`zipL_sub_borrow`: the borrow
  is set exactly when `ofBits xs < ofBits ys`; `zipL_sub_val`: otherwise the output has value
  `ofBits xs - ofBits ys`), and with `diffBit` it compares (`zipL_diff`: the final carry is set
  exactly when the values differ).
-/

@[expose] public section

namespace GraphIso.TM

/-- Cell tags (used from stage 17c). -/
inductive Tag where
  | unit | ff | tt | nat | pair | none | some | nil | cons | arr
  deriving DecidableEq, Repr

instance : Fintype Tag where
  elems := [.unit, .ff, .tt, .nat, .pair, .none, .some, .nil, .cons, .arr].toFinset
  complete x := by cases x <;> decide

/-- The simulator's alphabet. -/
inductive Sym where
  /-- A bit. -/
  | bit (b : Bool)
  /-- The end of a number. -/
  | nd
  /-- A cell tag. -/
  | tag (t : Tag)
  /-- A marker. -/
  | mk (i : Fin 4)
  deriving DecidableEq, Fintype, Repr

instance : Inhabited Sym := ⟨.nd⟩

/-- The value of a list of bits, least significant first. -/
def ofBits : List Bool → ℕ
  | [] => 0
  | b :: l => b.toNat + 2 * ofBits l

@[simp] theorem ofBits_nil : ofBits [] = 0 := rfl
@[simp] theorem ofBits_cons (b : Bool) (l : List Bool) :
    ofBits (b :: l) = b.toNat + 2 * ofBits l := rfl

theorem ofBits_append (l m : List Bool) :
    ofBits (l ++ m) = ofBits l + 2 ^ l.length * ofBits m := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih, pow_succ]; ring

theorem ofBits_lt (l : List Bool) : ofBits l < 2 ^ l.length := by
  induction l with
  | nil => simp
  | cons b l ih => cases b <;> simp [pow_succ] <;> omega

/-- The first bit, `false` if there is none. -/
def hd : List Bool → Bool
  | [] => false
  | b :: _ => b

/-- The bits after the first. -/
abbrev tl (l : List Bool) : List Bool := l.tail

@[simp] theorem hd_nil : hd [] = false := rfl
@[simp] theorem hd_cons (b : Bool) (l : List Bool) : hd (b :: l) = b := rfl

theorem ofBits_hd_tl (l : List Bool) : ofBits l = (hd l).toNat + 2 * ofBits (tl l) := by
  cases l <;> simp

/-- A serial bit processor: `f x y c = (output, carry)`; missing bits read as `false`. -/
def zipL (f : Bool → Bool → Bool → Bool × Bool) : List Bool → List Bool → Bool →
    List Bool × Bool
  | [], [], c => ([], c)
  | x :: xs, [], c => ((f x false c).1 :: (zipL f xs [] (f x false c).2).1,
      (zipL f xs [] (f x false c).2).2)
  | [], y :: ys, c => ((f false y c).1 :: (zipL f [] ys (f false y c).2).1,
      (zipL f [] ys (f false y c).2).2)
  | x :: xs, y :: ys, c => ((f x y c).1 :: (zipL f xs ys (f x y c).2).1,
      (zipL f xs ys (f x y c).2).2)
termination_by xs ys => xs.length + ys.length

variable (f : Bool → Bool → Bool → Bool × Bool)

@[simp] theorem zipL_nil (c : Bool) : zipL f [] [] c = ([], c) := by simp [zipL]

/-- One step of `zipL` when a bit is left. -/
theorem zipL_step (xs ys : List Bool) (c : Bool) (h : xs ≠ [] ∨ ys ≠ []) :
    zipL f xs ys c = ((f (hd xs) (hd ys) c).1 :: (zipL f (tl xs) (tl ys) (f (hd xs) (hd ys) c).2).1,
      (zipL f (tl xs) (tl ys) (f (hd xs) (hd ys) c).2).2) := by
  cases xs <;> cases ys <;> simp_all [zipL]

theorem length_zipL :
    ∀ (xs ys : List Bool) (c : Bool), (zipL f xs ys c).1.length = max xs.length ys.length
  | [], [], c => by simp
  | x :: xs, [], c => by simp [zipL, length_zipL xs [] _]
  | [], y :: ys, c => by simp [zipL, length_zipL [] ys _]
  | x :: xs, y :: ys, c => by simp [zipL, length_zipL xs ys _, Nat.succ_max_succ]
termination_by xs ys => xs.length + ys.length

/-- The full adder. -/
def fullAdd (x y c : Bool) : Bool × Bool := (xor (xor x y) c, (x && y) || (c && xor x y))

/-- The full subtractor (`x - y - b`, with the borrow out). -/
def fullSub (x y b : Bool) : Bool × Bool := (xor (xor x y) b, (!x && (y || b)) || (y && b))

/-- The comparator: the carry records whether a pair of different bits was seen. -/
def diffBit (x y c : Bool) : Bool × Bool := (false, c || xor x y)

theorem zipL_add :
    ∀ (xs ys : List Bool) (c : Bool),
      ofBits (zipL fullAdd xs ys c).1 +
          2 ^ max xs.length ys.length * (zipL fullAdd xs ys c).2.toNat =
        ofBits xs + ofBits ys + c.toNat
  | [], [], c => by simp
  | x :: xs, [], c => by
    have ih := zipL_add xs [] (fullAdd x false c).2
    simp only [zipL, ofBits_cons, List.length_cons, List.length_nil, ofBits_nil] at ih ⊢
    simp only [Nat.max_zero] at ih ⊢
    rw [pow_succ]
    cases x <;> cases c <;> simp [fullAdd] at ih ⊢ <;> linarith
  | [], y :: ys, c => by
    have ih := zipL_add [] ys (fullAdd false y c).2
    simp only [zipL, ofBits_cons, List.length_cons, List.length_nil, ofBits_nil] at ih ⊢
    simp only [Nat.zero_max] at ih ⊢
    rw [pow_succ]
    cases y <;> cases c <;> simp [fullAdd] at ih ⊢ <;> linarith
  | x :: xs, y :: ys, c => by
    have ih := zipL_add xs ys (fullAdd x y c).2
    simp only [zipL, ofBits_cons, List.length_cons] at ih ⊢
    rw [Nat.succ_max_succ, pow_succ]
    cases x <;> cases y <;> cases c <;> simp [fullAdd] at ih ⊢ <;> linarith
termination_by xs ys => xs.length + ys.length

theorem zipL_sub :
    ∀ (xs ys : List Bool) (b : Bool),
      ofBits (zipL fullSub xs ys b).1 + ofBits ys + b.toNat =
        ofBits xs + 2 ^ max xs.length ys.length * (zipL fullSub xs ys b).2.toNat
  | [], [], b => by simp
  | x :: xs, [], b => by
    have ih := zipL_sub xs [] (fullSub x false b).2
    simp only [zipL, ofBits_cons, List.length_cons, List.length_nil, ofBits_nil] at ih ⊢
    simp only [Nat.max_zero] at ih ⊢
    rw [pow_succ]
    cases x <;> cases b <;> simp [fullSub] at ih ⊢ <;> linarith
  | [], y :: ys, b => by
    have ih := zipL_sub [] ys (fullSub false y b).2
    simp only [zipL, ofBits_cons, List.length_cons, List.length_nil, ofBits_nil] at ih ⊢
    simp only [Nat.zero_max] at ih ⊢
    rw [pow_succ]
    cases y <;> cases b <;> simp [fullSub] at ih ⊢ <;> linarith
  | x :: xs, y :: ys, b => by
    have ih := zipL_sub xs ys (fullSub x y b).2
    simp only [zipL, ofBits_cons, List.length_cons] at ih ⊢
    rw [Nat.succ_max_succ, pow_succ]
    cases x <;> cases y <;> cases b <;> simp [fullSub] at ih ⊢ <;> linarith
termination_by xs ys => xs.length + ys.length

/-- The borrow of a subtraction is set exactly when `x < y + b`. -/
theorem zipL_sub_borrow (xs ys : List Bool) (b : Bool) :
    (zipL fullSub xs ys b).2 = decide (ofBits xs < ofBits ys + b.toNat) := by
  have h := zipL_sub xs ys b
  have h₁ := ofBits_lt (zipL fullSub xs ys b).1
  rw [length_zipL] at h₁
  have hx := ofBits_lt xs
  have hy := ofBits_lt ys
  have hx' : 2 ^ xs.length ≤ 2 ^ max xs.length ys.length :=
    Nat.pow_le_pow_right (by norm_num) (Nat.le_max_left _ _)
  have hy' : 2 ^ ys.length ≤ 2 ^ max xs.length ys.length :=
    Nat.pow_le_pow_right (by norm_num) (Nat.le_max_right _ _)
  cases hz : (zipL fullSub xs ys b).2 <;> rw [hz] at h <;> cases b <;>
    simp at h ⊢ <;> omega

/-- The difference when there is no borrow. -/
theorem zipL_sub_val (xs ys : List Bool) (b : Bool) (hb : (zipL fullSub xs ys b).2 = false) :
    ofBits (zipL fullSub xs ys b).1 = ofBits xs - ofBits ys - b.toNat := by
  have h := zipL_sub xs ys b
  rw [hb] at h
  simp at h
  omega

/-- The sum, with the final carry appended. -/
theorem zipL_add_val (xs ys : List Bool) :
    ofBits ((zipL fullAdd xs ys false).1 ++ [(zipL fullAdd xs ys false).2]) =
      ofBits xs + ofBits ys := by
  have h := zipL_add xs ys false
  rw [ofBits_append, length_zipL]
  simp at h ⊢
  omega

/-- The comparator's final carry is set exactly when it starts set or the values differ. -/
theorem zipL_diff :
    ∀ (xs ys : List Bool) (c : Bool),
      (zipL diffBit xs ys c).2 = true ↔ c = true ∨ ofBits xs ≠ ofBits ys
  | [], [], c => by simp
  | x :: xs, [], c => by
    have ih := zipL_diff xs [] (diffBit x false c).2
    simp only [zipL, ofBits_cons, ofBits_nil] at ih ⊢
    rw [ih]
    cases x <;> cases c <;> simp [diffBit]
  | [], y :: ys, c => by
    have ih := zipL_diff [] ys (diffBit false y c).2
    simp only [zipL, ofBits_cons, ofBits_nil] at ih ⊢
    rw [ih]
    cases y <;> cases c <;> simp [diffBit] <;> omega
  | x :: xs, y :: ys, c => by
    have ih := zipL_diff xs ys (diffBit x y c).2
    simp only [zipL, ofBits_cons] at ih ⊢
    rw [ih]
    cases x <;> cases y <;> cases c <;> simp [diffBit] <;> omega
termination_by xs ys => xs.length + ys.length

/-- The bits of a sum: the adder's output with the final carry appended. -/
def addBits (xs ys : List Bool) : List Bool :=
  (zipL fullAdd xs ys false).1 ++ [(zipL fullAdd xs ys false).2]

theorem ofBits_addBits (xs ys : List Bool) : ofBits (addBits xs ys) = ofBits xs + ofBits ys :=
  zipL_add_val xs ys

theorem length_addBits (xs ys : List Bool) :
    (addBits xs ys).length = max xs.length ys.length + 1 := by
  simp [addBits, length_zipL]

/-- The bits of a truncated difference: the subtractor's output, or no bits at a borrow. -/
def subBits (xs ys : List Bool) : List Bool :=
  if (zipL fullSub xs ys false).2 then [] else (zipL fullSub xs ys false).1

theorem ofBits_subBits (xs ys : List Bool) : ofBits (subBits xs ys) = ofBits xs - ofBits ys := by
  unfold subBits
  split
  · rename_i h
    rw [zipL_sub_borrow] at h
    simp at h
    simp
    omega
  · rename_i h
    rw [zipL_sub_val _ _ _ (by simpa using h)]
    simp

theorem length_subBits_le (xs ys : List Bool) :
    (subBits xs ys).length ≤ max xs.length ys.length := by
  unfold subBits
  split <;> simp [length_zipL]

/-- The borrow of `xs - ys` decides `ofBits xs < ofBits ys`. -/
theorem zipL_sub_lt (xs ys : List Bool) :
    (zipL fullSub xs ys false).2 = decide (ofBits xs < ofBits ys) := by
  simp [zipL_sub_borrow]

/-- The comparator from `false` decides `ofBits xs ≠ ofBits ys`. -/
theorem zipL_diff_false (xs ys : List Bool) :
    (zipL diffBit xs ys false).2 = !decide (ofBits xs = ofBits ys) := by
  have h := zipL_diff xs ys false
  cases hz : (zipL diffBit xs ys false).2 <;> simp_all

end GraphIso.TM
