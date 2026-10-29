module

public import GraphIso.TM.Write
import all Init.Data.Array.Basic
import all Init.Data.List.Sort.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Mathlib.Data.List.Sort

/-!
# Checks of stage 17d: input and output

`PLAN-17.md` §7.

* **Serialization**: `ser` of the test value `v₁ = (5, [some true, none])` of type
  `T₁ = ℕ × List (Option Bool)`, and of the array `#[3, 0, 1]` (elements in reverse order).
* **Kernel runs**, with all final stacks, registers and exact step counts:
  - `load T₁` reads `ser T₁ v₁` in `4660` steps and builds the eight cells `h₁` (addresses
    `0, …, 7`; the counter pads addresses with zeros), leaving the pointer `7` on `work`;
  - `write T₁` from the heap `h₁` and the pointer `7` writes `ser T₁ v₁` in `17743` steps;
  - a round trip of the array `#[3, 0, 1]` (load, move the pointer, write);
  - `write .nat` of a cell holding the non-canonical bits `[0, 1, 0, 0]` (the value `2`), through
    the non-canonical pointer `[0, 0]`, writes the canonical `ser .nat 2`.
* **Representation**: the cell `7` of `h₁` represents `v₁` (`rep_v₁`, by the constructors).
* **The specifications on concrete inputs**: `load_sat` and `write_sat` at `v₁` (`load_spec`,
  `write_spec`).
* **Negative controls**: the load does not take `4659` steps (`load_not_4659`); the cell `2`
  of `h₁` does not represent `some false` (`not_rep_some_false`); the output of the write is not
  the serialization of `(5, [some false, none])` (`write_not_other`).
-/

@[expose] public section

namespace GraphIsoChecks.TMIO

open GraphIso.TM GraphIso.Cost Function

/-- A program running one routine over the simulator's stacks. -/
def prog1 (x : Code Stk Sym Rg Unit) : Program Stk Sym Rg Unit := ⟨fun _ => x, ()⟩

/-- The machine with `inp` on the input stack, an empty heap and the counter `0`. -/
def cfgIn (inp : List Sym) : Cfg Stk Sym Rg :=
  ⟨Regs.empty, fun k => match k with
    | .inp => inp
    | .cnt => [.nd]
    | _ => []⟩

/-- The machine with the heap `h`, the counter `cnt` and the pointer `p` on `ptr`. -/
def cfgOut (h : List Cell) (cnt p : List Bool) : Cfg Stk Sym Rg :=
  ⟨Regs.empty, fun k => match k with
    | .heap => encHeap h
    | .cnt => bits cnt ++ [.nd]
    | .ptr => bits p ++ [.nd]
    | _ => []⟩

/-- Run a routine: the stacks other than `env` and `lst` (these are untouched), the registers
and the step count. -/
def go (x : Code Stk Sym Rg Unit) (c : Cfg Stk Sym Rg) :
    Option (List (List Sym) × List (Option Sym) × ℕ) :=
  (run (prog1 x) 1000000 x c).map fun r =>
    ([r.1.stk .inp, r.1.stk .out, r.1.stk .heap, r.1.stk .scan, r.1.stk .cnt, r.1.stk .work,
      r.1.stk .ptr, r.1.stk .t0, r.1.stk .t1, r.1.stk .t2, r.1.stk .t3, r.1.stk .t4],
      [r.1.regs 0, r.1.regs 1, r.1.regs 2, r.1.regs 3], r.2)

/-- Empty registers. -/
abbrev none4 : List (Option Sym) := [none, none, none, none]

/-- The test type: a natural and a list of optional Booleans. -/
abbrev T₁ : Ty := .prod .nat (.list (.option .bool))

/-- The test value `(5, [some true, none])`. -/
def v₁ : T₁.denote := (5, [some true, none])

theorem ser_v₁ : ser T₁ v₁ = bits [true, false, true] ++
    [.nd, .tag .cons, .tag .some, .tag .tt, .tag .cons, .tag .none, .tag .nil] := by
  decide +kernel

/-- Arrays are serialized with their elements in reverse order. -/
theorem ser_arr : ser (.array .nat) #[3, 0, 1] =
    [.tag .cons, .bit true, .nd, .tag .cons, .nd, .tag .cons, .bit true, .bit true, .nd,
      .tag .nil] := by
  decide +kernel

/-- The address `k`, padded with zeros to the length `k + 1` (and `[]` for `0`): the addresses
that the counter of stage 17c produces. -/
def ad : ℕ → List Bool
  | 0 => []
  | k + 1 => (toBits (k + 1)).rightpad (k + 2) false

/-- The cells of `v₁`, in the order `load` allocates them: `5`, `true`, `some`, `none`, `nil`,
the two `cons` cells (from the end of the list), the pair. -/
def h₁ : List Cell :=
  [⟨ad 0, .nat, [[true, false, true]]⟩, ⟨ad 1, .tt, []⟩, ⟨ad 2, .some, [ad 1]⟩,
    ⟨ad 3, .none, []⟩, ⟨ad 4, .nil, []⟩, ⟨ad 5, .cons, [ad 3, ad 4]⟩,
    ⟨ad 6, .cons, [ad 2, ad 5]⟩, ⟨ad 7, .pair, [ad 0, ad 6]⟩]

/-- `h₁` is well formed: the cell `i` has the address `i`. -/
theorem h₁_wf : HeapWF h₁ := by
  unfold HeapWF
  decide +kernel

/-- **The cell `7` of `h₁` represents `v₁`**, by the constructors of `Rep`. -/
theorem rep_v₁ : Rep h₁ T₁ v₁ 7 :=
  .pair (l₁ := ad 0) (l₂ := ad 6) ⟨by decide +kernel, by decide +kernel⟩
    (.nat (l := [true, false, true]) ⟨by decide +kernel, by decide +kernel⟩)
    (.cons (l₁ := ad 2) (l₂ := ad 5) ⟨by decide +kernel, by decide +kernel⟩
      (.some (l := ad 1) ⟨by decide +kernel, by decide +kernel⟩
        (.bool true ⟨by decide +kernel, by decide +kernel⟩))
      (.cons (l₁ := ad 3) (l₂ := ad 4) ⟨by decide +kernel, by decide +kernel⟩
        (.none ⟨by decide +kernel, by decide +kernel⟩)
        (.nil ⟨by decide +kernel, by decide +kernel⟩)))

/-- **Negative control**: the cell `2` of `h₁` (`some true`) does not represent `some false`. -/
theorem not_rep_some_false : ¬ Rep h₁ (.option .bool) (some false) 2 := by
  intro r
  obtain ⟨l, ⟨_, _, hf⟩, r₁⟩ := r.some_inv
  have hl : l = ad 1 := by simpa [h₁] using hf.symm
  subst hl
  have e : ofBits (ad 1) = 1 := by decide +kernel
  rw [e] at r₁
  obtain ⟨_, ht, _⟩ := r₁.bool_inv
  simp [h₁] at ht

/-- **`load_sat` on a concrete input**: from the empty heap, `load T₁` builds a heap `h'` on which
the pointer it leaves represents `v₁`, within `ldB T₁ v₁ 8` steps (`8` cells). -/
theorem load_spec : Sat (prog1 (load T₁)) (load T₁) (cfgIn (ser T₁ v₁)) (ldB T₁ v₁ 8) fun c' =>
    ∃ h' l, HeapAt h' c' ∧ Rep h' T₁ v₁ (ofBits l) ∧ c'.stk .inp = [] ∧
      c'.stk .work = bits l ++ [.nd] := by
  refine (load_sat T₁ (prog1 (load T₁)) v₁ [] (cfgIn (ser T₁ v₁)) [] 8
    ⟨fun i hi => absurd hi (by simp), rfl, rfl, [], rfl, rfl, by decide⟩ rfl
    (by simp [cfgIn]) (by decide +kernel)).mono le_rfl
    fun c' ⟨_, h', l, hH, _, _, hR, hi, hw, _⟩ => ⟨h', l, by simpa using hH, by simpa using hR, hi,
      by simpa [cfgIn] using hw⟩

/-- **`write_sat` on a concrete input**: from `h₁` and the pointer `7`, `write T₁` outputs
`ser T₁ v₁` within `wrB T₁ v₁ N` steps, `N` the length of the heap. -/
theorem write_spec : Sat (prog1 (write T₁)) (write T₁) (cfgOut h₁ (ad 8) (ad 7))
    (wrB T₁ v₁ (encHeap h₁).length) fun c' => c'.stk .out = ser T₁ v₁ ∧ c'.stk .ptr = [] := by
  have e : ofBits (ad 7) = 7 := by decide +kernel
  refine (write_sat T₁ (prog1 (write T₁)) v₁ h₁ (cfgOut h₁ (ad 8) (ad 7)) (ad 7) [] h₁_wf rfl rfl
    rfl (by rw [e]; exact rep_v₁) (by decide +kernel) rfl).mono le_rfl
    fun c' ⟨_, ho, hp, _⟩ => ⟨by simpa [cfgOut] using ho, hp⟩

/-- **Loading** `v₁`: the input is consumed, the heap is `h₁`, the counter is `8` and the pointer
`7` is on `work`. -/
example : go (load T₁) (cfgIn (ser T₁ v₁))
    = some ([[], [], encHeap h₁, [], bits (ad 8) ++ [.nd], bits (ad 7) ++ [.nd], [], [], [], [],
      [], []], none4, 4660) := by
  decide +kernel

/-- **Negative control**: the load does not take `4659` steps. -/
theorem load_not_4659 : go (load T₁) (cfgIn (ser T₁ v₁))
    ≠ some ([[], [], encHeap h₁, [], bits (ad 8) ++ [.nd], bits (ad 7) ++ [.nd], [], [], [], [],
      [], []], none4, 4659) := by
  decide +kernel

/-- **Writing** `v₁` from `h₁`: the output is `ser T₁ v₁`, the pointer is consumed, the heap and
the counter are unchanged. -/
example : go (write T₁) (cfgOut h₁ (ad 8) (ad 7))
    = some ([[], ser T₁ v₁, encHeap h₁, [], bits (ad 8) ++ [.nd], [], [], [], [], [], [], []],
      none4, 17743) := by
  decide +kernel

/-- **Negative control**: the output is not the serialization of `(5, [some false, none])`. -/
theorem write_not_other : (go (write T₁) (cfgOut h₁ (ad 8) (ad 7))).map (·.1[1]!)
    ≠ some (ser T₁ (5, [some false, none])) := by
  decide +kernel

/-- Load, move the pointer from `work` to `ptr`, and write. -/
def roundTrip (t : Ty) : Code Stk Sym Rg Unit :=
  .seq (load t) (.seq (moveNum2 .work .ptr .t0) (write t))

/-- **A round trip** of the array `#[3, 0, 1]`: the output is its serialization. -/
example : (go (roundTrip (.array .nat)) (cfgIn (ser (.array .nat) #[3, 0, 1]))).map
    (fun r => (r.1[1]!, r.2.2)) = some (ser (.array .nat) #[3, 0, 1], 5272) := by
  decide +kernel

/-- **A non-canonical natural**: the cell holds `[0, 1, 0, 0]` (the value `2`), the pointer is
`[0, 0]` (the address `0`); the output is the canonical `ser .nat 2`. -/
example : go (write .nat) (cfgOut [⟨[], .nat, [[false, true, false, false]]⟩] [true]
      [false, false])
    = some ([[], ser .nat 2, encHeap [⟨[], .nat, [[false, true, false, false]]⟩], [],
      bits [true] ++ [.nd], [], [], [], [], [], [], []], none4, 366) := by
  decide +kernel

end GraphIsoChecks.TMIO
