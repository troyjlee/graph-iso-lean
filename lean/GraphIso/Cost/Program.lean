module

public import Mathlib.Data.List.Basic
public import Mathlib.Order.Basic

/-!
# A small costed program language

Programs are a deep embedding in parametric higher-order abstract syntax (PHOAS). Runtime values
are bound as `var t` for a type family `var`, and a closed program is a term
`∀ var, … → Prog S rec var t`. Every constructor below is charged by the evaluator
(`GraphIso.Cost.eval`), and no constructor embeds a Lean function on runtime values.

The type alone does **not** guarantee that a program computes only through these
constructors: Lean can inspect `var` by classical case analysis on a type equality. Accepted
programs therefore carry the relational well-formedness witness of
`GraphIso.Cost.WellFormed` (`Proc.Wf`, `Impl.Wf`), which excludes such programs.

* `Ty`: value types (unit, Booleans, naturals, pairs, lists, arrays, options).
* `Prim`: local data operations, each with a cost (`Prim.cost`) in the stated model:
  unit-cost word operations and pointer operations, array reads in one step, and
  copying/scanning/materializing charged by length.
* `Signature`: the operations of an abstract backend, with argument and result types.
* `Prog S rec var t`: return, sequencing, primitives, branching, case analysis, bounded
  iteration over a list (`foldList`), a loop that runs while its body returns `some`
  (`loop`), a recursive call of the enclosing procedure of type `rec` (`recur`), and
  backend calls (`call`).

Natural numbers are unit-cost words. Programs in this library only manipulate positions,
symbols below the input alphabet bound, and counters bounded by data lengths.
-/

@[expose] public section

namespace GraphIso.Cost

/-- Value types. -/
inductive Ty where
  | unit
  | bool
  | nat
  | prod (a b : Ty)
  | list (a : Ty)
  | array (a : Ty)
  | option (a : Ty)
  deriving DecidableEq, Repr

namespace Ty

/-- The Lean type of runtime values of a value type. -/
@[reducible] def denote : Ty → Type
  | unit => Unit
  | bool => Bool
  | nat => ℕ
  | prod a b => a.denote × b.denote
  | list a => List a.denote
  | array a => Array a.denote
  | option a => Option a.denote

/-- The default value, returned by out-of-bounds array reads. -/
def default : (t : Ty) → t.denote
  | unit => ()
  | bool => false
  | nat => 0
  | prod a b => (a.default, b.default)
  | list _ => []
  | array _ => #[]
  | option _ => none

instance (t : Ty) : Inhabited t.denote := ⟨t.default⟩

end Ty

/-- A list of arguments, one variable per type. -/
inductive Args (var : Ty → Type) : List Ty → Type where
  | nil : Args var []
  | cons {t : Ty} {ts : List Ty} : var t → Args var ts → Args var (t :: ts)

namespace Args

variable {var : Ty → Type} {t : Ty} {ts : List Ty}

/-- The first argument. -/
def head : Args var (t :: ts) → var t
  | .cons x _ => x

/-- The remaining arguments. -/
def tail : Args var (t :: ts) → Args var ts
  | .cons _ xs => xs

@[simp] theorem head_cons (x : var t) (xs : Args var ts) : (Args.cons x xs).head = x := rfl
@[simp] theorem tail_cons (x : var t) (xs : Args var ts) : (Args.cons x xs).tail = xs := rfl

end Args

/-- Local primitive operations, indexed by argument types and result type. -/
inductive Prim : List Ty → Ty → Type where
  | unit : Prim [] .unit
  | natLit (k : ℕ) : Prim [] .nat
  | boolLit (b : Bool) : Prim [] .bool
  | add : Prim [.nat, .nat] .nat
  | sub : Prim [.nat, .nat] .nat
  | natEq : Prim [.nat, .nat] .bool
  | natLt : Prim [.nat, .nat] .bool
  | not : Prim [.bool] .bool
  | and : Prim [.bool, .bool] .bool
  | or : Prim [.bool, .bool] .bool
  | pair {a b : Ty} : Prim [a, b] (.prod a b)
  | fst {a b : Ty} : Prim [.prod a b] a
  | snd {a b : Ty} : Prim [.prod a b] b
  | none {a : Ty} : Prim [] (.option a)
  | some {a : Ty} : Prim [a] (.option a)
  | nil {a : Ty} : Prim [] (.list a)
  | cons {a : Ty} : Prim [a, .list a] (.list a)
  | append {a : Ty} : Prim [.list a, .list a] (.list a)
  | reverse {a : Ty} : Prim [.list a] (.list a)
  | length {a : Ty} : Prim [.list a] .nat
  | range : Prim [.nat] (.list .nat)
  | arrayMk {a : Ty} : Prim [.nat, a] (.array a)
  | arraySize {a : Ty} : Prim [.array a] .nat
  | arrayGet {a : Ty} : Prim [.array a, .nat] a
  | arrayUpdate {a : Ty} : Prim [.array a, .list (.prod .nat a)] (.array a)
  | arrayOfList {a : Ty} : Prim [.list a] (.array a)
  | arrayToList {a : Ty} : Prim [.array a] (.list a)

namespace Prim

/-- Apply a list of index-value writes to an array, ignoring out-of-bounds indices. -/
def applyWrites {a : Ty} (arr : Array a.denote) (ws : List (ℕ × a.denote)) : Array a.denote :=
  ws.foldl (fun arr w => arr.setIfInBounds w.1 w.2) arr

/-- The value computed by a primitive. -/
def eval : {args : List Ty} → {t : Ty} → Prim args t → Args Ty.denote args → t.denote
  | _, _, .unit, .nil => ()
  | _, _, .natLit k, .nil => k
  | _, _, .boolLit b, .nil => b
  | _, _, .add, .cons x (.cons y .nil) => x + y
  | _, _, .sub, .cons x (.cons y .nil) => x - y
  | _, _, .natEq, .cons x (.cons y .nil) => x == y
  | _, _, .natLt, .cons x (.cons y .nil) => decide (x < y)
  | _, _, .not, .cons b .nil => !b
  | _, _, .and, .cons b (.cons c .nil) => b && c
  | _, _, .or, .cons b (.cons c .nil) => b || c
  | _, _, .pair, .cons x (.cons y .nil) => (x, y)
  | _, _, .fst, .cons p .nil => p.1
  | _, _, .snd, .cons p .nil => p.2
  | _, _, .none, .nil => Option.none
  | _, _, .some, .cons x .nil => Option.some x
  | _, _, .nil, .nil => []
  | _, _, .cons, .cons x (.cons xs .nil) => x :: xs
  | _, _, .append, .cons xs (.cons ys .nil) => xs ++ ys
  | _, _, .reverse, .cons xs .nil => xs.reverse
  | _, _, .length, .cons xs .nil => xs.length
  | _, _, .range, .cons k .nil => List.range k
  | _, _, .arrayMk, .cons k (.cons v .nil) => Array.replicate k v
  | _, _, .arraySize, .cons arr .nil => arr.size
  | _, a, .arrayGet, .cons arr (.cons i .nil) => arr.getD i a.default
  | _, _, .arrayUpdate, .cons arr (.cons ws .nil) => applyWrites arr ws
  | _, _, .arrayOfList, .cons xs .nil => xs.toArray
  | _, _, .arrayToList, .cons arr .nil => arr.toList

/-- The charged cost of a primitive on its actual arguments: one unit for word and pointer
operations and for an array read; the length for operations that scan, copy or materialize
a list or array. -/
def cost : {args : List Ty} → {t : Ty} → Prim args t → Args Ty.denote args → ℕ
  | _, _, .unit, _ => 1
  | _, _, .natLit _, _ => 1
  | _, _, .boolLit _, _ => 1
  | _, _, .add, _ => 1
  | _, _, .sub, _ => 1
  | _, _, .natEq, _ => 1
  | _, _, .natLt, _ => 1
  | _, _, .not, _ => 1
  | _, _, .and, _ => 1
  | _, _, .or, _ => 1
  | _, _, .pair, _ => 1
  | _, _, .fst, _ => 1
  | _, _, .snd, _ => 1
  | _, _, .none, _ => 1
  | _, _, .some, _ => 1
  | _, _, .nil, _ => 1
  | _, _, .cons, _ => 1
  | _, _, .append, xs => xs.head.length + 1
  | _, _, .reverse, xs => xs.head.length + 1
  | _, _, .length, xs => xs.head.length + 1
  | _, _, .range, xs => xs.head + 1
  | _, _, .arrayMk, xs => xs.head + 1
  | _, _, .arraySize, _ => 1
  | _, _, .arrayGet, _ => 1
  | _, _, .arrayUpdate, xs => xs.head.size + xs.tail.head.length + 1
  | _, _, .arrayOfList, xs => xs.head.length + 1
  | _, _, .arrayToList, xs => xs.head.size + 1

theorem one_le_cost {args : List Ty} {t : Ty} (p : Prim args t) (xs : Args Ty.denote args) :
    1 ≤ p.cost xs := by
  cases p <;> simp [cost]

end Prim

/-- The operations of an abstract backend. -/
structure Signature where
  /-- Operation names. -/
  Op : Type
  /-- Argument type of each operation. -/
  arg : Op → Ty
  /-- Result type of each operation. -/
  res : Op → Ty

/-- The signature with no backend operations. -/
def Signature.empty : Signature where
  Op := Empty
  arg := Empty.elim
  res := Empty.elim

/-- Programs over backend signature `S`, inside a recursive procedure of type
`rec.1 → rec.2`, with variables `var`, returning a value of type `t`. -/
inductive Prog (S : Signature) (rec : Ty × Ty) (var : Ty → Type) : Ty → Type where
  /-- Return a bound value. -/
  | ret {t : Ty} : var t → Prog S rec var t
  /-- Run a program and continue with its result. -/
  | bind {a t : Ty} : Prog S rec var a → (var a → Prog S rec var t) → Prog S rec var t
  /-- A local primitive operation. -/
  | prim {args : List Ty} {t : Ty} : Prim args t → Args var args → Prog S rec var t
  /-- Branch on a Boolean. -/
  | ite {t : Ty} : var .bool → Prog S rec var t → Prog S rec var t → Prog S rec var t
  /-- Case analysis on an option. -/
  | caseOption {a t : Ty} : var (.option a) → Prog S rec var t → (var a → Prog S rec var t) →
      Prog S rec var t
  /-- Case analysis on a list. -/
  | caseList {a t : Ty} : var (.list a) → Prog S rec var t →
      (var a → var (.list a) → Prog S rec var t) → Prog S rec var t
  /-- Bounded iteration: fold the body over the elements of a list, from an initial value. -/
  | foldList {a b : Ty} : var (.list a) → var b → (var b → var a → Prog S rec var b) →
      Prog S rec var b
  /-- Iterate the body from an initial state while it returns `some` new state; return the
  state for which it returns `none`. -/
  | loop {s : Ty} : var s → (var s → Prog S rec var (.option s)) → Prog S rec var s
  /-- Recursive call of the enclosing procedure. -/
  | recur : var rec.1 → Prog S rec var rec.2
  /-- Backend call. -/
  | call (op : S.Op) : var (S.arg op) → Prog S rec var (S.res op)

namespace Prog

variable {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- A nullary primitive. -/
abbrev op0 {t : Ty} (p : Prim [] t) : Prog S rec var t := .prim p .nil
/-- A unary primitive. -/
abbrev op1 {a t : Ty} (p : Prim [a] t) (x : var a) : Prog S rec var t := .prim p (.cons x .nil)
/-- A binary primitive. -/
abbrev op2 {a b t : Ty} (p : Prim [a, b] t) (x : var a) (y : var b) : Prog S rec var t :=
  .prim p (.cons x (.cons y .nil))

end Prog

/-- A closed recursive procedure from `a` to `b`: a body for every choice of variables. -/
abbrev Proc (S : Signature) (a b : Ty) : Type 1 :=
  (var : Ty → Type) → var a → Prog S (a, b) var b

end GraphIso.Cost
