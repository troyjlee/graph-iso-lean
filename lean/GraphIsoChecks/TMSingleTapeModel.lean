module

public import GraphIso.TM.SingleTape.Model
import all Init.Data.Array.Basic
import all Init.Data.List.Sort.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Mathlib.Data.List.Sort

/-!
# Checks of stage 18b: finite single-tape machines, timed outputs and framed tapes

`PLAN-18.md` §3. This module does not import the graph-isomorphism development.

* **The framed tapes**: lengths `|x| + 2` by the kernel; the empty output, `[false]` and
  `[true]` have pairwise distinct tapes (`mk_encodeOut_inj`).
* **A machine run** (`copyM`, alphabet `Sym Unit Bool Bool`, four states): it rewrites each input
  symbol as an output symbol moving right, then returns to the left mark and halts. On
  `encodeIn [true, false]` it outputs `encodeOut [true, false]` after exactly `8` transitions,
  on `encodeIn []` it outputs `encodeOut []` after `2`; the runs are kernel reductions (`rfl`)
  of mathlib's `TM0.step`, ending in the configuration `Tape.mk₁ (encodeOut y)`, where the
  machine halts. Hence `ListBlank.mk (encodeOut y) ∈ TM0.eval`.
* **Negative controls**: the run does not output `encodeOut [false, true]` within any bound, nor
  `encodeOut [true, false]` within `7` transitions; a trailing blank is invisible on a tape
  (`ListBlank.mk [lmark, blank] = ListBlank.mk [lmark]`), which is why outputs end in `rmark`;
  `copyM` does not halt on the input tape itself.
-/

@[expose] public section

namespace GraphIsoChecks.TMSingleTapeModel

open Turing GraphIso.TM.SingleTape GraphIso.TM.SingleTape.Sym

/-! ### Framed tapes -/

abbrev S := Sym Unit Bool Bool

example : (encodeIn [true, false] : List S).length = 4 ∧
    (encodeOut ([] : List Bool) : List S).length = 2 := by
  decide +kernel

example : ListBlank.mk (encodeOut ([] : List Bool) : List S) ≠ ListBlank.mk (encodeOut [false]) ∧
    ListBlank.mk (encodeOut [false] : List S) ≠ ListBlank.mk (encodeOut [true]) :=
  ⟨fun h => absurd (mk_encodeOut_inj h) (by decide),
    fun h => absurd (mk_encodeOut_inj h) (by decide)⟩

/-- **Negative control**: a trailing blank is invisible on a tape. -/
example : ListBlank.mk [lmark, (default : S)] = ListBlank.mk [lmark] :=
  Quotient.sound (Or.inr ⟨1, rfl⟩)

/-! ### A machine -/

/-- The states of `copyM`. -/
inductive St where
  | s0 | s1 | s2 | s3
  deriving DecidableEq

/-- The states as numbers. -/
def St.toFin : St → Fin 4
  | .s0 => 0
  | .s1 => 1
  | .s2 => 2
  | .s3 => 3

instance : Finite St :=
  Finite.of_injective St.toFin fun a b h => by
    cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

/-- Rewrite the input symbols as output symbols moving right, return to the left mark, halt. -/
def copyM : FinTM0 where
  Γ := S
  blank := default
  Λ := St
  start := .s0
  m
    | .s0, _ => some (.s1, .move .right)
    | .s1, .inp b => some (.s2, .write (.out b))
    | .s1, _ => some (.s3, .move .left)
    | .s2, _ => some (.s1, .move .right)
    | .s3, .lmark => none
    | .s3, _ => some (.s3, .move .left)

/-- **The run on `[true, false]`**: exactly `8` transitions, to the output tape, halting. -/
theorem copy_run : StepsIn copyM.step 8 (TM0.init (encodeIn [true, false]))
    ⟨St.s3, Tape.mk₁ (encodeOut [true, false])⟩ :=
  rfl

theorem copy_halt : copyM.step ⟨St.s3, Tape.mk₁ (encodeOut [true, false])⟩ = none :=
  rfl

theorem copy_out : TM0OutputsInTime copyM (encodeIn [true, false]) (encodeOut [true, false]) 8 :=
  ⟨.s3, 8, le_rfl, copy_run, copy_halt⟩

/-- The empty input: `2` transitions. -/
example : TM0OutputsInTime copyM (encodeIn []) (encodeOut []) 2 :=
  ⟨.s3, 2, le_rfl, rfl, rfl⟩

example :
    ListBlank.mk (encodeOut [true, false]) ∈ TM0.eval copyM.machine (encodeIn [true, false]) :=
  copy_out.mem_eval

/-! ### Negative controls -/

/-- **Negative control**: no other output, within any bound. -/
example (m : ℕ) :
    ¬TM0OutputsInTime copyM (encodeIn [true, false]) (encodeOut [false, true]) m := fun h => by
  cases mk_encodeOut_inj (copy_out.unique h)

/-- **Negative control**: not within `7` transitions. -/
example : ¬TM0OutputsInTime copyM (encodeIn [true, false]) (encodeOut [true, false]) 7 :=
  fun h => absurd (h.steps_le copy_run copy_halt) (by decide)

/-- **Negative control**: `copyM` does not halt at the start. -/
example : copyM.step (TM0.init (encodeIn [true, false])) ≠ none :=
  Option.isSome_iff_ne_none.1 rfl

end GraphIsoChecks.TMSingleTapeModel
