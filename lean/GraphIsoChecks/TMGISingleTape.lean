module

public import GraphIso.TM.SingleTape.GI
public import GraphIsoChecks.TMVertices
import all Init.Data.Array.Basic
import all Init.Data.List.Sort.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Mathlib.Data.List.Sort

/-!
# Checks of stage 18f: graph isomorphism on a single tape

`PLAN-18.md` §7. Theorem instantiations: the compiled GI machines are not run (the generic
compiler is run on small machines in `GraphIsoChecks.TMSingleTape`).

* **The machines are finite**: `giDecTM0` and `giCosetTM0` have finitely many states and symbols.
* **The input tapes**: `L₀ = |p.enc| + 2`; `42` symbols on the two paths `pp`, `49` on a path
  and the triangle `pt`, `5` and `10` on the empty pairs at `n = 0, 1`, by the kernel;
  `GraphPair.lam_tape_le` at `pp`.
* **In the number of vertices**: by `gi_tm0_vertices`, the single-tape decision machine outputs
  `encodeOut (ser .bool true)` on the two paths and `encodeOut (ser .bool false)` on a path and
  the triangle within `2 ^ (c 2⁸)` transitions (`λ(3) = 1`), and `true` on the empty pairs at
  `n = 0, 1` within `2 ^ c` (`λ(0) = λ(1) = 0`); by `gi_coset_tm0_vertices`, the single-tape
  coset machine outputs `some` on the two paths and `none` on a path and the triangle within
  `2 ^ (c 2⁸)`, and `some` on the empty pairs within `2 ^ c`.
* **In the input's length**: by `gi_tm0`, `true` on the two paths and `false` on a path and the
  triangle within `2 ^ (c 6⁸)` transitions (`λ(42) = λ(49) = 5`); by `gi_coset_tm0`, `some` and
  `none` on them within `2 ^ (c 6⁸)`.
* **Negative controls**: the decision machine does not output `true` on a path and the
  triangle, within any bound; the input tape's length is neither the encoding's length nor the
  number of vertices; `λ(L₀) + 1 ≤ λ(n) + 1` fails on the two paths.
-/

@[expose] public section

namespace GraphIsoChecks.TMGISingleTape

open Equiv GraphIso GraphIso.Cost GraphIso.Graph GraphIso.Main GraphIso.Recursion GraphIso.TM
  GraphIsoChecks.TMGI GraphIsoChecks.TMVertices

example : Finite giDecTM0.Λ ∧ Finite giDecTM0.Γ ∧ Finite giCosetTM0.Λ ∧ Finite giCosetTM0.Γ :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

/-! ### The input tapes -/

theorem tape_pp : (SingleTape.encodeIn pp.enc : List giDecTM0.Γ).length = 42 := by
  rw [length_giDec_tape]
  decide +kernel

theorem tape_pt : (SingleTape.encodeIn pt.enc : List giDecTM0.Γ).length = 49 := by
  rw [length_giDec_tape]
  decide +kernel

theorem tape_coset : (SingleTape.encodeIn pp.enc : List giCosetTM0.Γ).length = 42 ∧
    (SingleTape.encodeIn pt.enc : List giCosetTM0.Γ).length = 49 := by
  rw [length_giCoset_tape, length_giCoset_tape]
  decide +kernel

example : (SingleTape.encodeIn (emptyPair 0).enc : List giDecTM0.Γ).length = 5 ∧
    (SingleTape.encodeIn (emptyPair 1).enc : List giDecTM0.Γ).length = 10 := by
  rw [length_giDec_tape, length_giDec_tape]
  decide +kernel

example : lam (pp.enc.length + 2) + 1 ≤ 8 * (lam pp.n + 1) :=
  pp.lam_tape_le

/-! ### The machines -/

/-- **The single-tape decision machine, in the number of vertices**: `true` on the two paths,
`false` on a path and the triangle within `2 ^ (c 2⁸)` transitions, and `true` on the empty
pairs at `n = 0, 1` within `2 ^ c`. -/
example : ∃ c,
    SingleTape.TM0OutputsInTime giDecTM0 (SingleTape.encodeIn pp.enc)
      (SingleTape.encodeOut (ser .bool true)) (2 ^ (c * 2 ^ 8)) ∧
    SingleTape.TM0OutputsInTime giDecTM0 (SingleTape.encodeIn pt.enc)
      (SingleTape.encodeOut (ser .bool false)) (2 ^ (c * 2 ^ 8)) ∧
    SingleTape.TM0OutputsInTime giDecTM0 (SingleTape.encodeIn (emptyPair 0).enc)
      (SingleTape.encodeOut (ser .bool true)) (2 ^ (c * 1)) ∧
    SingleTape.TM0OutputsInTime giDecTM0 (SingleTape.encodeIn (emptyPair 1).enc)
      (SingleTape.encodeOut (ser .bool true)) (2 ^ (c * 1)) := by
  obtain ⟨c, h⟩ := gi_tm0_vertices
  have hl : lam pp.n = 1 ∧ lam pt.n = 1 ∧ lam (emptyPair 0).n = 0 ∧ lam (emptyPair 1).n = 0 := by
    decide +kernel
  have he : isoDecide (emptyPair 0) = true ∧ isoDecide (emptyPair 1) = true := by
    decide +kernel
  refine ⟨c, ?_, ?_, ?_, ?_⟩
  · have := h pp
    rwa [pp_iso, hl.1] at this
  · have := h pt
    rwa [pt_not_iso, hl.2.1] at this
  · have := h (emptyPair 0)
    rwa [he.1, hl.2.2.1] at this
  · have := h (emptyPair 1)
    rwa [he.2, hl.2.2.2] at this

/-- **The single-tape coset machine, in the number of vertices**: `some` on the two paths and
`none` on a path and the triangle within `2 ^ (c 2⁸)` transitions. -/
example : ∃ c, (∃ τ hs, SingleTape.TM0OutputsInTime giCosetTM0 (SingleTape.encodeIn pp.enc)
      (SingleTape.encodeOut (ser Ty.giCoset (some (τ, hs)))) (2 ^ (c * 2 ^ 8))) ∧
    SingleTape.TM0OutputsInTime giCosetTM0 (SingleTape.encodeIn pt.enc)
      (SingleTape.encodeOut (ser Ty.giCoset none)) (2 ^ (c * 2 ^ 8)) := by
  obtain ⟨c, hc⟩ := gi_coset_tm0_vertices
  have hl : lam pp.n = 1 ∧ lam pt.n = 1 := by decide +kernel
  refine ⟨c, ?_, ?_⟩
  · obtain ⟨r, hM, hnone, -⟩ := hc pp
    rw [hl.1] at hM
    rcases r with _ | ⟨τ, hs⟩
    · exact absurd (hnone.1 rfl) (not_isEmpty_iff.2 ((isoDecide_iff pp).1 pp_iso))
    · exact ⟨τ, hs, hM⟩
  · obtain ⟨r, hM, hnone, -⟩ := hc pt
    rw [hl.2] at hM
    have hr : r = none :=
      hnone.2 (not_nonempty_iff.1 fun h =>
        Bool.false_ne_true (pt_not_iso.symm.trans ((isoDecide_iff pt).2 h)))
    exact hr ▸ hM

/-- **The single-tape coset machine on the empty pairs**: `some` at `n = 0, 1` within `2 ^ c`
transitions. -/
example : ∃ c,
    (∃ τ hs, SingleTape.TM0OutputsInTime giCosetTM0 (SingleTape.encodeIn (emptyPair 0).enc)
      (SingleTape.encodeOut (ser Ty.giCoset (some (τ, hs)))) (2 ^ (c * 1))) ∧
    ∃ τ hs, SingleTape.TM0OutputsInTime giCosetTM0 (SingleTape.encodeIn (emptyPair 1).enc)
      (SingleTape.encodeOut (ser Ty.giCoset (some (τ, hs)))) (2 ^ (c * 1)) := by
  obtain ⟨c, hc⟩ := gi_coset_tm0_vertices
  have hl : lam (emptyPair 0).n = 0 ∧ lam (emptyPair 1).n = 0 := by decide +kernel
  have he : isoDecide (emptyPair 0) = true ∧ isoDecide (emptyPair 1) = true := by
    decide +kernel
  refine ⟨c, ?_, ?_⟩
  · obtain ⟨r, hM, hnone, -⟩ := hc (emptyPair 0)
    rw [hl.1] at hM
    rcases r with _ | ⟨τ, hs⟩
    · exact absurd (hnone.1 rfl) (not_isEmpty_iff.2 ((isoDecide_iff _).1 he.1))
    · exact ⟨τ, hs, hM⟩
  · obtain ⟨r, hM, hnone, -⟩ := hc (emptyPair 1)
    rw [hl.2] at hM
    rcases r with _ | ⟨τ, hs⟩
    · exact absurd (hnone.1 rfl) (not_isEmpty_iff.2 ((isoDecide_iff _).1 he.2))
    · exact ⟨τ, hs, hM⟩

/-- **The single-tape decision machine, in the input's length**: `true` on the two paths and
`false` on a path and the triangle within `2 ^ (c 6⁸)` transitions (`λ(42) = λ(49) = 5`). -/
example : ∃ c, SingleTape.TM0OutputsInTime giDecTM0 (SingleTape.encodeIn pp.enc)
      (SingleTape.encodeOut (ser .bool true)) (2 ^ (c * 6 ^ 8)) ∧
    SingleTape.TM0OutputsInTime giDecTM0 (SingleTape.encodeIn pt.enc)
      (SingleTape.encodeOut (ser .bool false)) (2 ^ (c * 6 ^ 8)) := by
  obtain ⟨c, h⟩ := gi_tm0
  have hl : lam 42 = 5 ∧ lam 49 = 5 := by decide +kernel
  refine ⟨c, ?_, ?_⟩
  · have := h pp
    rwa [pp_iso, tape_pp, hl.1] at this
  · have := h pt
    rwa [pt_not_iso, tape_pt, hl.2] at this

/-- **The single-tape coset machine, in the input's length**: `some` on the two paths and `none`
on a path and the triangle within `2 ^ (c 6⁸)` transitions. -/
example : ∃ c, (∃ τ hs, SingleTape.TM0OutputsInTime giCosetTM0 (SingleTape.encodeIn pp.enc)
      (SingleTape.encodeOut (ser Ty.giCoset (some (τ, hs)))) (2 ^ (c * 6 ^ 8))) ∧
    SingleTape.TM0OutputsInTime giCosetTM0 (SingleTape.encodeIn pt.enc)
      (SingleTape.encodeOut (ser Ty.giCoset none)) (2 ^ (c * 6 ^ 8)) := by
  obtain ⟨c, hc⟩ := gi_coset_tm0
  have hl : lam 42 = 5 ∧ lam 49 = 5 := by decide +kernel
  refine ⟨c, ?_, ?_⟩
  · obtain ⟨r, hM, hnone, -⟩ := hc pp
    rw [tape_coset.1, hl.1] at hM
    rcases r with _ | ⟨τ, hs⟩
    · exact absurd (hnone.1 rfl) (not_isEmpty_iff.2 ((isoDecide_iff pp).1 pp_iso))
    · exact ⟨τ, hs, hM⟩
  · obtain ⟨r, hM, hnone, -⟩ := hc pt
    rw [tape_coset.2, hl.2] at hM
    have hr : r = none :=
      hnone.2 (not_nonempty_iff.1 fun h =>
        Bool.false_ne_true (pt_not_iso.symm.trans ((isoDecide_iff pt).2 h)))
    exact hr ▸ hM

/-! ### Negative controls -/

/-- **Negative control**: the decision machine does not output `true` on a path and the
triangle, within any bound. -/
example (m : ℕ) : ¬SingleTape.TM0OutputsInTime giDecTM0 (SingleTape.encodeIn pt.enc)
    (SingleTape.encodeOut (ser .bool true)) m := fun h => by
  obtain ⟨c, hc⟩ := gi_tm0_vertices
  have := SingleTape.mk_encodeOut_inj ((hc pt).unique h)
  rw [pt_not_iso] at this
  exact absurd this (show ser Ty.bool false ≠ ser Ty.bool true by decide +kernel)

/-- **Negative control**: the input tape's length is neither the encoding's length nor the number
of vertices. -/
example : (SingleTape.encodeIn pp.enc : List giDecTM0.Γ).length ≠ pp.enc.length ∧
    (SingleTape.encodeIn pp.enc : List giDecTM0.Γ).length ≠ pp.n := by
  rw [tape_pp]
  decide +kernel

/-- **Negative control**: `λ(L₀) + 1 ≤ λ(n) + 1` fails on the two paths, so `lam_tape_le` needs a
factor. -/
example : ¬lam (pp.enc.length + 2) + 1 ≤ lam pp.n + 1 := by
  decide +kernel

end GraphIsoChecks.TMGISingleTape
