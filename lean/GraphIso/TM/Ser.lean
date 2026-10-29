module

public import GraphIso.TM.Rep

/-!
# Serialized values

Stage 17d (`PLAN-17.md` §7). The input and the output of the simulator are values written as
lists of symbols.

* **`toBits n`**: the binary digits of `n`, least significant first, without trailing zeros;
  `ofBits (toBits n) = n` (`ofBits_toBits`).
* **`ser t v`**: the serialization of `v : t.denote`, a prefix code:
  - the unit is empty, a Boolean is the tag `tt` or `ff`, a natural is `toBits n` and `nd`;
  - a pair is its two components, an option is the tag `none`, or `some` and its value;
  - a list is each element after the tag `cons`, then the tag `nil`;
  - an array is the same for its elements **in reverse order**, so that a loader reading the
    elements one by one pushes their pointers in the order of the cell's fields.
* **`wt t`**: a weight of the type `t` (its constructors, lists and arrays counted twice). The
  step bounds of loading and writing a value of type `t` with a serialization of length `L` are
  at most `wt t * (L + 1)` times a polynomial in the sizes involved.
-/

@[expose] public section

namespace GraphIso.TM

open GraphIso.Cost

/-- The binary digits of `n`, least significant first, without trailing zeros. -/
def toBits : ℕ → List Bool
  | 0 => []
  | n + 1 => ((n + 1) % 2 == 1) :: toBits ((n + 1) / 2)

theorem ofBits_toBits : ∀ n, ofBits (toBits n) = n
  | 0 => by simp [toBits]
  | n + 1 => by
    rw [toBits, ofBits_cons, ofBits_toBits ((n + 1) / 2)]
    rcases Nat.mod_two_eq_zero_or_one (n + 1) with h | h <;> simp [h] <;> omega

theorem length_toBits_le : ∀ n, (toBits n).length ≤ n
  | 0 => by simp [toBits]
  | n + 1 => by
    rw [toBits, List.length_cons]
    have := length_toBits_le ((n + 1) / 2)
    omega

/-- The serialization of a value. -/
def ser : (t : Ty) → t.denote → List Sym
  | .unit, _ => []
  | .bool, b => [.tag (if b then .tt else .ff)]
  | .nat, n => bits (toBits n) ++ [.nd]
  | .prod a b, v => ser a v.1 ++ ser b v.2
  | .option _, none => [.tag .none]
  | .option a, some x => .tag .some :: ser a x
  | .list a, xs => (xs.map fun x => .tag .cons :: ser a x).flatten ++ [.tag .nil]
  | .array a, v => (v.toList.reverse.map fun x => .tag .cons :: ser a x).flatten ++ [.tag .nil]

/-- The weight of a type: its constructors, lists and arrays counted twice. -/
def wt : Ty → ℕ
  | .unit => 1
  | .bool => 1
  | .nat => 1
  | .prod a b => wt a + wt b + 1
  | .option a => wt a + 1
  | .list a => wt a + 2
  | .array a => wt a + 2

theorem one_le_wt (t : Ty) : 1 ≤ wt t := by
  cases t <;> simp [wt]

/-- The serialization of a list of elements, each after the tag `cons`. -/
def serElems (a : Ty) (xs : List a.denote) : List Sym :=
  (xs.map fun x => .tag .cons :: ser a x).flatten

theorem serElems_cons (a : Ty) (x : a.denote) (xs : List a.denote) :
    serElems a (x :: xs) = .tag .cons :: (ser a x ++ serElems a xs) := by
  simp [serElems]

theorem length_serElems (a : Ty) (xs : List a.denote) :
    (serElems a xs).length = (xs.map fun x => (ser a x).length + 1).sum := by
  induction xs with
  | nil => simp [serElems]
  | cons x xs ih => rw [serElems_cons]; simp [ih]; omega

theorem ser_list (a : Ty) (xs : List a.denote) : ser (.list a) xs = serElems a xs ++ [.tag .nil] :=
  rfl

theorem ser_array (a : Ty) (v : Array a.denote) :
    ser (.array a) v = serElems a v.toList.reverse ++ [.tag .nil] := rfl

end GraphIso.TM
