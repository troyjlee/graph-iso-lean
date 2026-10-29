module

public import GraphIsoChecks.Restriction
import all Init.Data.Array.Basic
import all Init.Data.List.Sort.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Mathlib.Data.List.Sort

/-!
# Phase 7 checks: the remaining cases of the verification list

Kernel-evaluated runs of the reference solver on the cases of `PLAN.md`'s verification list
that the phase-5 and phase-6 checks do not already cover. Each run is tied to
`solve_reference` through `runRef_spec`, and its answer is compared with brute force.

* The trivial group, with a match and an impossible match.
* A singleton domain.
* Constant strings: every element of `S₃` is a solution.
* An intransitive action with linked orbits: `⟨(0 1)(2 3)⟩` on `{0, 1, 2, 3}`. The orbits
  `{0, 1}` and `{2, 3}` are solved one after the other, and the choice on the first fixes the
  second. A match that needs `(0 1)` without `(2 3)` has no solution.
* The dihedral group of order 8, solved directly. The answer denotes the same coset as the
  block reduction's in `GraphIsoChecks/Restriction.lean`, with a different representative.

The other cases of the list are covered elsewhere:

* `S₃`, distinct symbols and an impossible match: `GraphIsoChecks/Reference.lean`.
* `C₃` with the nonidentity outer representative `(0 1)`: also there.
* The empty window: also there.
* Branching over the nonnormal point stabilizer `⟨(1 2)⟩` of `S₃`: the full-window `S₃` runs
  there; the semantic example in `GraphIsoChecks/Semantics.lean`; and the combination of its
  branch answers in `GraphIsoChecks/Reductions.lean`.
* A restriction with a nontrivial kernel: `GraphIsoChecks/Restriction.lean`.

`GraphIsoChecks/Sweep.lean` compares many more instances in compiled code.
-/

@[expose] public section

namespace GraphIsoChecks.Coverage

open Equiv GraphIso GraphIso.Cost GraphIso.Programs GraphIso.Solver GraphIso.Reference
  GraphIso.Enum GraphIsoChecks.Reference GraphIsoChecks.Restriction

/-! ### The trivial group -/

theorem runTrivial : runRef ((#[0, 1, 2], #[0, 1, 2]), univ3, idD, 3, []) =
    some (ans idD [idD], 93) := by
  decide +kernel

example := runRef_spec (by decide) (by decide) (by decide) (by decide) runTrivial

example : ∀ g, g ∈ Answer.denote (AnswerData.denote 3 (ans idD [idD])) ↔
    BruteIso univ3 idD [] #[0, 1, 2] #[0, 1, 2] g := by
  intro g
  rw [ans, mem_denote_some (by decide)]
  revert g
  decide

theorem runTrivialNone : runRef ((#[0, 1, 2], #[0, 2, 1]), univ3, idD, 3, []) =
    some (none, 93) := by
  decide +kernel

example := runRef_spec (by decide) (by decide) (by decide) (by decide) runTrivialNone

example : ∀ g, ¬ BruteIso univ3 idD [] #[0, 1, 2] #[0, 2, 1] g := by decide

/-! ### A singleton domain -/

def univ1 : WinData := WinData.ofPoints 1 [0]
def id1 : PermData := PermData.one 1

/-- The answer `id • ⟨id⟩` of degree 1. -/
def ans1 : AnswerData Ty.gens := some (id1, (1, [id1], [id1]))

theorem runSingle : runRef ((#[5], #[5]), univ1, id1, 1, []) = some (ans1, 65) := by
  decide +kernel

example := runRef_spec (by decide) (by decide) (by decide) (by decide) runSingle

example : ∀ g, g ∈ Answer.denote (AnswerData.denote 1 ans1) ↔
    GraphIsoChecks.Restriction.BruteIso 1 univ1 id1 [] #[5] #[5] g := by
  intro g
  rw [ans1, mem_denote_some (by decide)]
  revert g
  decide

theorem runSingleNone : runRef ((#[5], #[6]), univ1, id1, 1, []) = some (none, 65) := by
  decide +kernel

example := runRef_spec (by decide) (by decide) (by decide) (by decide) runSingleNone

example : ∀ g, ¬ GraphIsoChecks.Restriction.BruteIso 1 univ1 id1 [] #[5] #[6] g := by decide

/-! ### Constant strings -/

/-- The elements of `S₃`, in the order the reference `generate` lists them for the generators
the solver passes it. -/
def s3list : GensData :=
  [(#[2, 0, 1], #[1, 2, 0]), (#[1, 2, 0], #[2, 0, 1]), (#[2, 1, 0], #[2, 1, 0]),
    (#[1, 0, 2], #[1, 0, 2]), (#[0, 2, 1], #[0, 2, 1]), (#[0, 1, 2], #[0, 1, 2])]

theorem runConst : runRef ((#[0, 0, 0], #[0, 0, 0]), univ3, idD, 3, s3gens) =
    some (ans c3D s3list, 30480) := by
  decide +kernel

example := runRef_spec (by decide) (by decide) (by decide) (by decide) runConst

-- Every element of `S₃` is a solution, and the answer denotes them all.
example : ∀ g, g ∈ Answer.denote (AnswerData.denote 3 (ans c3D s3list)) ↔
    BruteIso univ3 idD s3gens #[0, 0, 0] #[0, 0, 0] g := by
  intro g
  rw [ans, mem_denote_some (by decide)]
  revert g
  decide

example : ∀ g, BruteIso univ3 idD s3gens #[0, 0, 0] #[0, 0, 0] g := by decide

/-! ### Linked orbits -/

/-- `(0 1)(2 3)`. -/
def p0123 : PermData := PermData.ofPerm (swap (0 : Fin 4) 1 * swap 2 3)

theorem runLinked : runRef ((#[0, 1, 2, 2], #[1, 0, 2, 2]), wAll, id4, 4, [p0123]) =
    some (ans4 p0123 [id4], 3349) := by
  decide +kernel

example := runRef_spec (by decide) (by decide) (by decide) (by decide) runLinked

example : ∀ g, g ∈ Answer.denote (AnswerData.denote 4 (ans4 p0123 [id4])) ↔
    GraphIsoChecks.Restriction.BruteIso 4 wAll id4 [p0123] #[0, 1, 2, 2] #[1, 0, 2, 2] g := by
  intro g
  rw [ans4, mem_denote_some (by decide)]
  revert g
  decide

theorem runLinkedNone : runRef ((#[0, 1, 2, 3], #[1, 0, 2, 3]), wAll, id4, 4, [p0123]) =
    some (none, 1440) := by
  decide +kernel

example := runRef_spec (by decide) (by decide) (by decide) (by decide) runLinkedNone

example : ∀ g,
    ¬ GraphIsoChecks.Restriction.BruteIso 4 wAll id4 [p0123] #[0, 1, 2, 3] #[1, 0, 2, 3] g := by
  decide

/-! ### The dihedral group, solved directly -/

/-- `(0 3 1 2)`. -/
def r4 : PermData := (#[3, 2, 0, 1], #[2, 3, 1, 0])

theorem runDihedral : runRef ((#[0, 1, 0, 0], #[0, 0, 1, 0]), wAll, id4, 4, d4) =
    some (ans4 r4 [p23, id4], 16109) := by
  decide +kernel

example := runRef_spec (by decide) (by decide) (by decide) (by decide) runDihedral

example : ∀ g, g ∈ Answer.denote (AnswerData.denote 4 (ans4 r4 [p23, id4])) ↔
    GraphIsoChecks.Restriction.BruteIso 4 wAll id4 d4 #[0, 1, 0, 0] #[0, 0, 1, 0] g := by
  intro g
  rw [ans4, mem_denote_some (by decide)]
  revert g
  decide

-- The block reduction's answer denotes the same coset, from the representative `(0 3)(1 2)`.
example : ∀ g, g ∈ Answer.denote (AnswerData.denote 4 (ans4 r4 [p23, id4])) ↔
    g ∈ Answer.denote (AnswerData.denote 4
      (ans4 (PermData.ofPerm (swap (0 : Fin 4) 3 * swap 1 2)) [p23, id4])) := by
  intro g
  rw [ans4, ans4, mem_denote_some (by decide), mem_denote_some (by decide)]
  revert g
  decide

end GraphIsoChecks.Coverage
