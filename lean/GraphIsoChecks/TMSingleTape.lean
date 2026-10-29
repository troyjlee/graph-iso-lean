module

public import GraphIso.TM.SingleTape.Compile
public import GraphIsoChecks.TM2Sim
public import GraphIsoChecks.TMCode
import all Init.Data.Array.Basic
import all Init.Data.List.Sort.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Mathlib.Data.List.Sort

/-!
# Checks of stage 18e: the compiler from stack machines to single-tape machines

`PLAN-18.md` §6. This module does not import the graph-isomorphism development; it uses the
reversal machine of stage 18c (`GraphIsoChecks.TM2Sim.revTM`) and the negation machine of stage
17a (`GraphIsoChecks.TMCode.negM`, a compiled stack program). The compiled machines are run by
the kernel and observed through their tape cells around the head (`view`).

* **Reversal** (`revTM0 = compile revTM _`, input stack `true`, output stack `false`): on
  `encodeIn [true, false]` it halts after exactly `63` transitions with the head on the left
  mark of `encodeOut [false, true]` and blanks around it (`rev_view`); `compile_outputs`
  instantiated gives the bound `compileConst revTM (2 + 3 + 1)² = 80 · 36`, and with the run,
  the timed output in exactly `63` (`rev_exact`). The empty input: the empty output after `17`.
* **Negation** (`negTM0 = compile negM _`, input stack `0`, output stack `2`): for every input
  `l`, `compile_outputs` gives the output `encodeOut (l.map not)` within
  `compileConst negM (13 |l| + 10)²` (`neg_outputs`, with `compileConst negM = 44`); run by the
  kernel: the empty output on `[]` after `39` transitions, `[false]` on `[true]` after `101`.
* **Negative controls:** the reversal is not done within `62` transitions, and outputs nothing
  else within any bound; the negation's output on `[true]` is not `[true]`.
-/

@[expose] public section

namespace GraphIsoChecks.TMSingleTape

open Turing StateTransition GraphIso.TM.SingleTape GraphIso.TM.SingleTape.Sym
open GraphIsoChecks.TM2Sim GraphIsoChecks.TMCode

deriving instance DecidableEq for GraphIso.TM.SingleTape.Sym

/-! ### Reversal -/

theorem revFin : ∀ k, Finite (revTM.Γ k) :=
  fun _ => inferInstanceAs (Finite Bool)

/-- **The compiled reversal machine.** -/
abbrev revTM0 : FinTM0 :=
  compile revTM revFin

instance : DecidableEq (WorkSym revTM) :=
  inferInstanceAs (DecidableEq (Bool × (Bool → Option Bool)))

/-- The configuration after `n` transitions on `encodeIn x`. -/
def revAfter (n : ℕ) (x : List Bool) : Option (TM0.Cfg revTM0.Γ revTM0.Λ) :=
  (flip bind revTM0.step)^[n] (some (TM0.init (encodeIn x)))

/-- Whether the machine halts, and the cells `-2, …, 4` around the head. -/
def view (c : TM0.Cfg revTM0.Γ revTM0.Λ) : Bool × List (CSym revTM) :=
  ((revTM0.step c).isNone, (List.range 7).map fun i => c.Tape.nth (i - 2 : ℤ))

/-- **The run on `[true, false]`**: after exactly `63` transitions the machine halts, the head
on the left mark of `encodeOut [false, true]`, blanks to the left and after the right mark. -/
theorem rev_view : (revAfter 63 [true, false]).map view =
    some (true, [default, default, lmark, out false, out true, rmark, default]) := by
  decide +kernel

/-- **Negative control**: not halted within `62` transitions. -/
theorem rev_running : ∀ n < 63, (revAfter n [true, false]).map (fun c => (revTM0.step c).isSome)
    = some true := by
  decide +kernel

/-- The empty input: the empty output after `17` transitions. -/
example : (revAfter 17 []).map view =
    some (true, [default, default, lmark, rmark, default, default, default]) := by
  decide +kernel

/-- **`compile_outputs` instantiated**: within `compileConst revTM (2 + 3 + 1)² = 80 · 36`. -/
theorem rev_outputs0 : TM0OutputsInTime revTM0 (encodeIn [true, false]) (encodeOut [false, true])
    (compileConst revTM * (2 + 3 + 1) ^ 2) :=
  compile_outputs revTM revFin rev_outputs

example : compileConst revTM = 80 := by
  decide +kernel

/-- The run halts after `63` transitions. -/
theorem rev_halts : ∃ c, StepsIn revTM0.step 63 (TM0.init (encodeIn [true, false])) c ∧
    revTM0.step c = none := by
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1
    (show (revAfter 63 [true, false]).isSome by decide +kernel)
  refine ⟨c, hc, ?_⟩
  have h : (revAfter 63 [true, false]).map (fun c => (revTM0.step c).isNone) = some true := by
    decide +kernel
  rw [hc, Option.map_some] at h
  exact Option.isNone_iff_eq_none.1 (Option.some.inj h)

/-- **The timed output in exactly `63` transitions**: `compile_outputs` and the kernel run. -/
theorem rev_exact :
    TM0OutputsInTime revTM0 (encodeIn [true, false]) (encodeOut [false, true]) 63 := by
  obtain ⟨q, n, -, hr, hh⟩ := rev_outputs0
  obtain ⟨c, hc, hch⟩ := rev_halts
  obtain ⟨rfl, -⟩ := hr.halt_unique hh hc hch
  exact ⟨q, 63, le_rfl, hr, hh⟩

/-- **Negative control**: not within `62` transitions. -/
example : ¬TM0OutputsInTime revTM0 (encodeIn [true, false]) (encodeOut [false, true]) 62 :=
  fun h => by
    obtain ⟨q, n, -, hr, hh⟩ := rev_exact
    obtain ⟨c, hc, hch⟩ := rev_halts
    obtain ⟨rfl, -⟩ := hr.halt_unique hh hc hch
    exact absurd (h.steps_le hr hh) (by decide)

/-- **Negative control**: no other output, within any bound. -/
example (m : ℕ) : ¬TM0OutputsInTime revTM0 (encodeIn [true, false]) (encodeOut [true, false]) m :=
  fun h => absurd (mk_encodeOut_inj (rev_exact.unique h)) (by decide)

/-! ### Negation -/

theorem negFin : ∀ k, Finite (negM.Γ k)
  | none => (inferInstance : Finite (GraphIso.TM.Label negProg))
  | some _ => (inferInstance : Finite Bool)

/-- **The compiled negation machine.** -/
abbrev negTM0 : FinTM0 :=
  compile negM negFin

/-- **For every input**, the compiled negation machine outputs the complement within
`compileConst negM (|l| + (12 |l| + 9) + 1)²` transitions. -/
theorem neg_outputs (l : List Bool) : TM0OutputsInTime negTM0 (encodeIn l)
    (encodeOut (l.map not)) (compileConst negM * (l.length + (12 * l.length + 8 + 1) + 1) ^ 2) :=
  compile_outputs negM negFin (GraphIso.TM.outputsInTime negProg 0 2 (main_exec l))

example : compileConst negM = 44 := by
  decide +kernel

/-- `t` for `true`, `f` for `false`. -/
def bcode (b : Bool) (t f : ℕ) : ℕ :=
  if b then t else f

/-- A coarse view of a cell: `0` for a work symbol, then the marks and the input and output
symbols. -/
def code : CSym negM → ℕ
  | work _ => 0
  | lmark => 1
  | rmark => 2
  | inp b => bcode b 3 4
  | out b => bcode b 5 6

/-- The configuration after `n` transitions on `encodeIn x`. -/
def negAfter (n : ℕ) (x : List Bool) : Option (TM0.Cfg negTM0.Γ negTM0.Λ) :=
  (flip bind negTM0.step)^[n] (some (TM0.init (encodeIn x)))

/-- Whether the machine halts, and the cells `-2, …, 4` around the head, coarsely. -/
def nview (c : TM0.Cfg negTM0.Γ negTM0.Λ) : Bool × List ℕ :=
  ((negTM0.step c).isNone, (List.range 7).map fun i => code (c.Tape.nth (i - 2 : ℤ)))

/-- The empty output on `[]`, after `39` transitions. -/
example : (negAfter 39 []).map nview = some (true, [0, 0, 1, 2, 0, 0, 0]) := by
  decide +kernel

/-- `[false]` on `[true]`, after `101` transitions. -/
example : (negAfter 101 [true]).map nview = some (true, [0, 0, 1, 6, 2, 0, 0]) := by
  decide +kernel

/-- **Negative control**: the output on `[true]` is not `[true]`. -/
example (m : ℕ) : ¬TM0OutputsInTime negTM0 (encodeIn [true]) (encodeOut [true]) m :=
  fun h => absurd (mk_encodeOut_inj ((neg_outputs [true]).unique h))
    (show ([false] : List Bool) ≠ [true] by decide)

end GraphIsoChecks.TMSingleTape
