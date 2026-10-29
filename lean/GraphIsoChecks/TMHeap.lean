module

public import GraphIso.TM.Alloc
public import GraphIso.TM.Rep
public import Mathlib.Tactic.IntervalCases
import all Init.Data.Array.Basic
import all Init.Data.List.Sort.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Mathlib.Data.List.Sort

/-!
# Checks of stage 17c: the heap

`PLAN-17.md` §6.

* **Kernel runs** on a concrete heap of three cells (`h₃`: the natural `5`, `none`, and the pair
  of them), with all final stacks, registers and exact step counts: `lookup` of each cell
  copies it onto `work`, consumes the pointer and leaves the heap, the scan stack, the counter
  and the temporaries as they were (`603`, `462` and `298` steps, deepest cell first); a
  non-canonical pointer (`[0, 1, 0, 0]`, the value `2`) finds the same cell; `alloc` appends a
  `some` cell and a pair cell at address `3`, pushes the address and increments the counter.
* **The specifications on concrete inputs**: `lookup_sat` and `alloc_sat` instantiated at `h₃`
  (`lookup_spec`, `alloc_spec`).
* **Representation**: the pair cell represents `(5, none)` (`rep_pair`), still after an
  allocation (`rep_pair_mono`), and the new `some` cell represents `some 5` (`rep_some`).
  Negative controls: the pair cell does not represent `(4, none)` (`not_rep_pair`), the natural
  cell represents no Boolean (`not_rep_bool`), and a heap whose cell `0` has address `1` is not
  well formed (`not_wf`).
-/

@[expose] public section

namespace GraphIsoChecks.TMHeap

open GraphIso.TM GraphIso.Cost Function

/-- A program running one routine over the simulator's stacks. -/
def prog1 (x : Code Stk Sym Rg Unit) : Program Stk Sym Rg Unit := ⟨fun _ => x, ()⟩

/-- The heap: `0 ↦ 5`, `1 ↦ none`, `2 ↦ (0, 1)`. Addresses are written `[]`, `[true]`,
`[false, true]`. -/
def h₃ : List Cell :=
  [⟨[], .nat, [[true, false, true]]⟩, ⟨[true], .none, []⟩,
    ⟨[false, true], .pair, [[], [true]]⟩]

theorem h₃_wf : HeapWF h₃ := by
  intro i hi
  simp only [h₃, List.length_cons, List.length_nil] at hi
  interval_cases i <;> rfl

/-- The machine with the heap `h₃`, the counter `3 = [true, true]`, a pointer on `ptr`, and
`work`. -/
def cfgH (p : List Bool) (work : List Sym) : Cfg Stk Sym Rg :=
  ⟨Regs.empty, fun k => match k with
    | .heap => encHeap h₃
    | .cnt => bits [true, true] ++ [.nd]
    | .ptr => bits p ++ [.nd]
    | .work => work
    | _ => []⟩

/-- Run a routine: the stacks other than `inp`, `out`, `env` and `lst` (these are untouched),
the registers and the step count. -/
def go (x : Code Stk Sym Rg Unit) (c : Cfg Stk Sym Rg) :
    Option (List (List Sym) × List (Option Sym) × ℕ) :=
  (run (prog1 x) 100000 x c).map fun r =>
    ([r.1.stk .heap, r.1.stk .scan, r.1.stk .cnt, r.1.stk .work, r.1.stk .ptr, r.1.stk .t0,
      r.1.stk .t1, r.1.stk .t2, r.1.stk .t3, r.1.stk .t4],
      [r.1.regs 0, r.1.regs 1, r.1.regs 2, r.1.regs 3], r.2)

/-- Empty registers. -/
abbrev none4 : List (Option Sym) := [none, none, none, none]

/-- The counter `3`. -/
abbrev cnt3 : List Sym := bits [true, true] ++ [.nd]

/-- Lookup of cell `0` (the deepest). -/
example : go lookup (cfgH [] [])
    = some ([encHeap h₃, [], cnt3, encCell h₃[0], [], [], [], [], [], []], none4, 603) := by
  decide +kernel

/-- Lookup of cell `1`. -/
example : go lookup (cfgH [true] [])
    = some ([encHeap h₃, [], cnt3, encCell h₃[1], [], [], [], [], [], []], none4, 462) := by
  decide +kernel

/-- Lookup of cell `2` (the top). -/
example : go lookup (cfgH [false, true] [])
    = some ([encHeap h₃, [], cnt3, encCell h₃[2], [], [], [], [], [], []], none4, 298) := by
  decide +kernel

/-- A non-canonical pointer to cell `2`, onto a non-empty `work`. -/
example : go lookup (cfgH [false, true, false, false] [.nd])
    = some ([encHeap h₃, [], cnt3, encCell h₃[2] ++ [.nd], [], [], [], [], [], []], none4, 368)
    := by
  decide +kernel

/-- Allocating `some 5` (a cell pointing at cell `0`): address `3`, counter `4`. -/
example : go (alloc .some) (cfgH [] (encFields [[]] ++ [.mk 2]))
    = some ([encHeap (h₃ ++ [⟨[true, true], .some, [[]]⟩]), [], bits [false, false, true] ++ [.nd],
      bits [true, true] ++ [.nd], [.nd], [], [], [], [], []], none4, 295) := by
  decide +kernel

/-- Allocating a pair of cells `2` and `1`; the stack below the marker is kept. -/
example : go (alloc .pair) (cfgH [] (encFields [[false, true], [true]] ++ [.mk 2, .nd]))
    = some ([encHeap (h₃ ++ [⟨[true, true], .pair, [[false, true], [true]]⟩]), [],
      bits [false, false, true] ++ [.nd], bits [true, true] ++ [.nd, .nd], [.nd], [], [], [], [],
      []], none4, 359) := by
  decide +kernel

/-- **`lookup_sat` on a concrete input**: the pair cell, within the bound. -/
theorem lookup_spec : Sat (prog1 lookup) lookup (cfgH [false, true] [])
    (lookupBound (encHeap h₃).length 2) fun c' =>
      c'.stk .work = encCell ⟨[false, true], .pair, [[], [true]]⟩ ∧ c'.stk .heap = encHeap h₃ := by
  refine (lookup_sat (p := [false, true]) (rp := []) h₃_wf rfl rfl rfl rfl
    (by decide)).mono le_rfl fun c' ⟨_, hw, _, hj⟩ => ⟨?_, hj .heap (by decide) (by decide)⟩
  rw [hw]
  rfl

/-- **`alloc_sat` on a concrete input**: the new cell gets the address `3`. -/
theorem alloc_spec : Sat (prog1 (alloc .some)) (alloc .some) (cfgH [] (encFields [[]] ++ [.mk 2]))
    (allocBound (encFields [[]]).length 3) fun c' =>
      ∃ l, ofBits l = 3 ∧ c'.stk .heap = encHeap (h₃ ++ [⟨l, .some, [[]]⟩]) := by
  refine (alloc_sat (h := h₃) (fs := [[]]) (rest := []) .some
    ⟨h₃_wf, rfl, rfl, [true, true], rfl, rfl, by decide⟩ rfl rfl).mono le_rfl
    fun c' ⟨_, l, hH, hl, _⟩ => ⟨l, hl, hH.heap⟩

/-- The pair cell represents `(5, none)`. -/
theorem rep_pair : Rep h₃ (.prod .nat (.option .nat)) (5, none) 2 :=
  .pair (l₁ := []) (l₂ := [true]) ⟨by decide, rfl, rfl⟩
    (.nat (l := [true, false, true]) ⟨by decide, rfl, rfl⟩) (.none ⟨by decide, rfl, rfl⟩)

/-- The heap after allocating `some 5`. -/
def h₄ : List Cell := h₃ ++ [⟨[true, true], .some, [[]]⟩]

/-- Representations survive allocation. -/
theorem rep_pair_mono : Rep h₄ (.prod .nat (.option .nat)) (5, none) 2 := rep_pair.mono

/-- The new cell represents `some 5`. -/
theorem rep_some : Rep h₄ (.option .nat) (some 5) 3 :=
  .some (l := []) ⟨by decide, rfl, rfl⟩ (.nat (l := [true, false, true]) ⟨by decide, rfl, rfl⟩)

/-- **Negative control**: the pair cell does not represent `(4, none)`. -/
theorem not_rep_pair : ¬ Rep h₃ (.prod .nat (.option .nat)) (4, none) 2 := by
  intro r
  cases r with
  | pair hc r₁ _ =>
    obtain ⟨_, _, hf⟩ := hc
    simp only [h₃, List.getElem_cons_succ, List.getElem_cons_zero, List.cons.injEq,
      and_true] at hf
    obtain ⟨rfl, -⟩ := hf
    obtain ⟨l, ⟨_, _, hl⟩, hv⟩ := r₁.nat_inv
    simp only [h₃, ofBits_nil, List.getElem_cons_zero, List.cons.injEq, and_true] at hl
    subst hl
    simp at hv

/-- **Negative control**: the natural cell represents no Boolean. -/
theorem not_rep_bool (b : Bool) : ¬ Rep h₃ .bool b 0 := by
  intro r
  cases r with
  | bool _ hc =>
    obtain ⟨_, ht, _⟩ := hc
    cases b <;> simp [h₃] at ht

/-- **Negative control**: a heap whose cell `0` has address `1` is not well formed. -/
theorem not_wf : ¬ HeapWF [⟨[true], .unit, []⟩] := fun h => by
  have := h 0 (by decide)
  simp at this

end GraphIsoChecks.TMHeap
