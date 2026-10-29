module

public import GraphIso.TM.Vertices
public import GraphIsoChecks.TMGI
import all Init.Data.Array.Basic
import all Init.Data.List.Sort.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Mathlib.Data.List.Sort

/-!
# Checks of stage 18a: graph isomorphism on Turing machines, in the number of vertices

`PLAN-18.md` §2.

* **The encoding bounds** at `n = 0` and `n = 1` (the pairs of empty graphs, encodings of `3`
  and `8` symbols) and at the two paths `pp` on `Fin 3` (`40` symbols), by the kernel: the
  lengths against `5 (n + 1)³`, `λ(L) + 1` against `8 (λ(n) + 1)`, a list of naturals below `3`
  against `|xs| (n + 1) + 1` and the path's adjacency lists against `n (n (n + 1) + 2) + 1`;
  and the theorems instantiated.
* **The machines**, theorem instantiations (the machines are not run): by `gi_tm_vertices`, the
  decision machine outputs `true` on the two paths and `false` on a path and the triangle
  within `2 ^ (c 2⁸)` steps (`λ(3) = 1`), and `true` on the empty pairs at `n = 0, 1` within
  `2 ^ c` steps (`λ(0) = λ(1) = 0`); by `gi_coset_tm_vertices`, the coset machine outputs `some`
  on the two paths and `none` on a path and the triangle within `2 ^ (c 2⁸)` steps.
* **Negative controls**: the time parameter is the number of vertices, not the input's length
  (`8 ≠ 1` on the one-vertex pair); `λ(L) + 1 ≤ λ(n) + 1` fails on the two paths
  (`λ(40) = 5`, `λ(3) = 1`), so a factor is needed; `L ≤ (n + 1)³` fails at `n = 0`.
-/

@[expose] public section

namespace GraphIsoChecks.TMVertices

open Equiv GraphIso GraphIso.Cost GraphIso.Graph GraphIso.Main GraphIso.Recursion GraphIso.TM
  GraphIsoChecks.TMGI

/-- The pair of empty graphs on `Fin n`. -/
def emptyPair (n : ℕ) : GraphPair := ⟨n, ⊥, ⊥⟩

/-! ### The encoding bounds -/

example : (emptyPair 0).enc.length = 3 ∧ (emptyPair 1).enc.length = 8 ∧ pp.enc.length = 40 := by
  decide +kernel

/-- `L ≤ 5 (n + 1)³` at `n = 0, 1, 3`. -/
example : (emptyPair 0).enc.length ≤ 5 * (0 + 1) ^ 3 ∧ (emptyPair 1).enc.length ≤ 5 * (1 + 1) ^ 3 ∧
    pp.enc.length ≤ 5 * (3 + 1) ^ 3 := by
  decide +kernel

/-- `λ(L) + 1 ≤ 8 (λ(n) + 1)` at `n = 0, 1, 3`. -/
example : lam (emptyPair 0).enc.length + 1 ≤ 8 * (lam 0 + 1) ∧
    lam (emptyPair 1).enc.length + 1 ≤ 8 * (lam 1 + 1) ∧
    lam pp.enc.length + 1 ≤ 8 * (lam 3 + 1) := by
  decide +kernel

/-- A list of naturals below `3`, and the adjacency lists of the path `0 - 1 - 2`. -/
example : (ser (.list .nat) [0, 2]).length ≤ 2 * (3 + 1) + 1 ∧
    (ser Ty.graph (GraphData.ofSimpleGraph path₁)).length ≤ 3 * (3 * (3 + 1) + 2) + 1 := by
  decide +kernel

example : pp.enc.length ≤ 5 * (3 + 1) ^ 3 := pp.enc_length_le

example : lam pp.enc.length + 1 ≤ 8 * (lam 3 + 1) := pp.lam_enc_le

example (n : ℕ) : (emptyPair n).enc.length ≤ 5 * (n + 1) ^ 3 := (emptyPair n).enc_length_le

/-! ### The machines -/

/-- **The decision machine, in the number of vertices**: `true` on the two paths, `false` on a
path and the triangle within `2 ^ (c 2⁸)` steps, and `true` on the empty pairs at `n = 0, 1`
within `2 ^ c` steps. -/
example : ∃ c, Nonempty (Turing.TM2OutputsInTime (toFinTM2 giDecProg .inp .out) pp.enc
      (some (ser .bool true)) (2 ^ (c * 2 ^ 8))) ∧
    Nonempty (Turing.TM2OutputsInTime (toFinTM2 giDecProg .inp .out) pt.enc
      (some (ser .bool false)) (2 ^ (c * 2 ^ 8))) ∧
    Nonempty (Turing.TM2OutputsInTime (toFinTM2 giDecProg .inp .out) (emptyPair 0).enc
      (some (ser .bool true)) (2 ^ (c * 1))) ∧
    Nonempty (Turing.TM2OutputsInTime (toFinTM2 giDecProg .inp .out) (emptyPair 1).enc
      (some (ser .bool true)) (2 ^ (c * 1))) := by
  obtain ⟨c, h⟩ := gi_tm_vertices
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

/-- **The coset machine, in the number of vertices**: `some` on the two paths and `none` on a
path and the triangle within `2 ^ (c 2⁸)` steps. -/
example : ∃ c, (∃ τ hs, Nonempty (Turing.TM2OutputsInTime (toFinTM2 giCosetProg .inp .out)
      pp.enc (some (ser Ty.giCoset (some (τ, hs)))) (2 ^ (c * 2 ^ 8)))) ∧
    Nonempty (Turing.TM2OutputsInTime (toFinTM2 giCosetProg .inp .out) pt.enc
      (some (ser Ty.giCoset none)) (2 ^ (c * 2 ^ 8))) := by
  obtain ⟨c, hc⟩ := gi_coset_tm_vertices
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

/-! ### Negative controls -/

/-- **Negative control**: the time parameter is the number of vertices, not the input's length;
on the one-vertex pair they differ. -/
example : (emptyPair 1).enc.length ≠ (emptyPair 1).n := by
  decide +kernel

/-- **Negative control**: `λ(L) + 1 ≤ λ(n) + 1` fails on the two paths, so `lam_enc_le` needs a
factor. -/
example : ¬lam pp.enc.length + 1 ≤ lam pp.n + 1 := by
  decide +kernel

/-- **Negative control**: `L ≤ (n + 1)³` fails at `n = 0`, so `enc_length_le` needs a factor. -/
example : ¬(emptyPair 0).enc.length ≤ ((emptyPair 0).n + 1) ^ 3 := by
  decide +kernel

end GraphIsoChecks.TMVertices
