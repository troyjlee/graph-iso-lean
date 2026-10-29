module

public import GraphIso
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Tactic.FinCases
import all Init.Data.Array.Basic
import all Init.Data.List.Sort.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Mathlib.Data.List.Sort

/-!
# Phase 1 checks: solution cosets on small examples

Exhaustive kernel checks over `Perm (Fin 3)` together with instantiations of the general
theorems. The examples cover empty and singleton domains, impossible matches, nonidentity
outer representatives that do not preserve the window, and branching over a nonnormal
point stabilizer.
-/

@[expose] public section

namespace GraphIsoChecks.Semantics

open Equiv GraphIso Pointwise

/-! ### Empty and singleton domains -/

example (W : Set (Fin 0)) (σ : Perm (Fin 0)) (G : Subgroup (Perm (Fin 0)))
    (x y : Fin 0 → Bool) : iso W σ G x y = σ • (G : Set (Perm (Fin 0))) :=
  iso_of_isEmpty

example (σ : Perm (Fin 3)) (G : Subgroup (Perm (Fin 3))) (x y : Fin 3 → Bool) :
    iso ∅ σ G x y = σ • (G : Set (Perm (Fin 3))) :=
  iso_empty_window

/-- On a one-point domain, the answer is the whole coset or empty. -/
example (x y : Fin 1 → Bool) (h : x 0 ≠ y 0) : iso Set.univ 1 ⊤ x y = ∅ := by
  ext g
  simp only [mem_iso, Set.mem_empty_iff_false, iff_false, not_and]
  intro _ hm
  exact h (by simpa [Subsingleton.elim (g 0) 0] using hm 0 trivial)

example (x : Fin 1 → Bool) : iso Set.univ 1 ⊤ x x = (⊤ : Set (Perm (Fin 1))) := by
  ext g
  simp only [mem_iso, Subgroup.mem_top, true_and, Set.top_eq_univ, Set.mem_univ, iff_true]
  intro u _
  rw [Subsingleton.elim (g u) u]

/-! ### The full symmetric group on three points

Source `x = 001` and target `y = 100`. The solutions are the 3-cycle `c` and the
transposition `(0 2)`; the automorphism subgroup of `x` is `{1, (0 1)}`. -/

def c : Perm (Fin 3) := swap 0 1 * swap 1 2
def x : Fin 3 → Fin 2 := ![0, 0, 1]
def y : Fin 3 → Fin 2 := ![1, 0, 0]

example : c 0 = 1 ∧ c 1 = 2 ∧ c 2 = 0 := by decide

theorem iso_univ_x_y (σ : Perm (Fin 3)) :
    ∀ g, g ∈ iso Set.univ σ ⊤ x y ↔ g = c ∨ g = swap 0 2 := by
  simp only [mem_iso, Subgroup.mem_top, true_and]
  decide

theorem aut_univ_x :
    ∀ g, g ∈ aut (isInvariant_univ ⊤) x ↔ g = 1 ∨ g = swap 0 1 := by
  simp only [mem_aut, Subgroup.mem_top, true_and]
  decide

-- The solution-coset theorem, through either solution; the representative `σ` is arbitrary.
example (σ : Perm (Fin 3)) :
    iso Set.univ σ ⊤ x y = c • (aut (isInvariant_univ ⊤) x : Set (Perm (Fin 3))) :=
  iso_eq_smul_aut _ ((iso_univ_x_y σ c).2 (Or.inl rfl))

example (σ : Perm (Fin 3)) :
    iso Set.univ σ ⊤ x y = swap (0 : Fin 3) 2 • (aut (isInvariant_univ ⊤) x : Set (Perm (Fin 3))) :=
  iso_eq_smul_aut _ ((iso_univ_x_y σ (swap 0 2)).2 (Or.inr rfl))

-- Cross-check the coset `c • aut` against the exhaustive description.
example : ∀ g, g ∈ c • (aut (isInvariant_univ ⊤) x : Set (Perm (Fin 3))) ↔
    g = c ∨ g = swap 0 2 := by
  simp only [mem_leftCoset_iff', mem_aut, Subgroup.mem_top, true_and]
  decide

/-- An impossible match: different symbol counts. -/
example (σ : Perm (Fin 3)) : iso Set.univ σ ⊤ x (![1, 1, 0] : Fin 3 → Fin 2) = ∅ := by
  ext g
  simp only [mem_iso, Subgroup.mem_top, true_and, Set.mem_empty_iff_false, iff_false]
  revert g
  decide

/-! ### A window not preserved by the representative

`G` is the stabilizer of `2`, so `W = {0, 1}` is `G`-invariant, while the representative
`c` maps `W` to `{1, 2}`. -/

def G2 : Subgroup (Perm (Fin 3)) := MulAction.stabilizer (Perm (Fin 3)) (2 : Fin 3)
def W01 : Set (Fin 3) := {u | u ≠ 2}

instance : DecidablePred (· ∈ W01) := fun u => inferInstanceAs (Decidable (u ≠ 2))

theorem mem_G2 (g : Perm (Fin 3)) : g ∈ G2 ↔ g 2 = 2 := MulAction.mem_stabilizer_iff

theorem W01_invariant : IsInvariant G2 W01 := by
  intro g hg u hu
  rw [mem_G2] at hg
  simp only [W01, Set.mem_ofPred_eq] at hu ⊢
  intro h
  exact hu (g.injective (h.trans hg.symm))

example : ¬ ∀ u ∈ W01, c u ∈ W01 := by decide

def x' : Fin 3 → Fin 2 := ![0, 1, 0]
def y' : Fin 3 → Fin 2 := ![0, 0, 1]

theorem iso_W01 : ∀ g, g ∈ iso W01 c G2 x' y' ↔ g = c := by
  simp only [mem_iso, mem_G2]
  decide

theorem aut_W01 : ∀ g, g ∈ aut W01_invariant x' ↔ g = 1 := by
  simp only [mem_aut, mem_G2]
  decide

example : iso W01 c G2 x' y' = c • (aut W01_invariant x' : Set (Perm (Fin 3))) :=
  iso_eq_smul_aut W01_invariant ((iso_W01 c).2 rfl)

/-! ### Normalization -/

example : iso W01 c G2 x' y' = c • iso W01 1 G2 x' (fun u => y' (c u)) :=
  iso_eq_smul_iso_one _ _ _ _ _

example : ∀ g, g ∈ iso W01 1 G2 x' (fun u => y' (c u)) ↔ g = 1 := by
  simp only [mem_iso, mem_G2]
  decide

/-! ### Sequential windows

Over `G = ⊤`, solve the invariant window `{0, 1, 2}` as `W₁ ∪ W₂` with `W₁ = ∅`, and the
two-step version where the first answer is `c • aut`. -/

example (W₂ : Set (Fin 3)) :
    iso (∅ ∪ W₂) c ⊤ x y = iso W₂ c ⊤ x y :=
  iso_union_of_eq_smul (by simp)

example :
    iso (Set.univ ∪ Set.univ) 1 ⊤ x y = iso Set.univ c (aut (isInvariant_univ ⊤) x) x y :=
  iso_union_eq_iso_aut (isInvariant_univ ⊤) ((iso_univ_x_y 1 c).2 (Or.inl rfl))

/-! ### Branching over a nonnormal point stabilizer

`K` is the stabilizer of `0`, which is not normal in `S₃`. The representatives `1`, `(0 1)`,
`(0 2)` cover `S₃`. Starting from the outer representative `c`, only the first two branches
are nonempty, each with a single solution; the reconstruction recovers `aut x = {1, (0 1)}`
from the representative difference alone. -/

def K0 : Subgroup (Perm (Fin 3)) := MulAction.stabilizer (Perm (Fin 3)) (0 : Fin 3)

theorem mem_K0 (g : Perm (Fin 3)) : g ∈ K0 ↔ g 0 = 0 := MulAction.mem_stabilizer_iff

example : ¬ ∀ g k : Perm (Fin 3), k ∈ K0 → g * k * g⁻¹ ∈ K0 := by
  simp only [mem_K0]
  decide

def r : Fin 3 → Perm (Fin 3) := ![1, swap 0 1, swap 0 2]

theorem r_cover : IsLeftCover ⊤ K0 r := by
  refine ⟨fun _ => Subgroup.mem_top _, ?_⟩
  simp only [Subgroup.mem_top, true_implies, mem_K0]
  decide

theorem r_transversal : IsLeftTransversal ⊤ K0 r := by
  refine ⟨r_cover, ?_⟩
  simp only [mem_K0]
  decide

example : iso Set.univ c ⊤ x y = ⋃ i, iso Set.univ (c * r i) K0 x y :=
  iso_eq_iUnion_of_isLeftCover r_cover le_top

example : ∀ g, g ∈ iso Set.univ (c * r 0) K0 x y ↔ g = c := by
  simp only [mem_iso, mem_K0]
  decide

example : ∀ g, g ∈ iso Set.univ (c * r 1) K0 x y ↔ g = swap 0 2 := by
  simp only [mem_iso, mem_K0]
  decide

example : ∀ g, g ∉ iso Set.univ (c * r 2) K0 x y := by
  simp only [mem_iso, mem_K0]
  decide

/-- The nonempty branch answers: representatives `c`, `(0 2)` with trivial subgroups. -/
def τ : Fin 2 → Perm (Fin 3) := ![c, swap 0 2]

theorem iso_eq_branches :
    iso Set.univ c ⊤ x y = ⋃ i, τ i • ((⊥ : Subgroup (Perm (Fin 3))) : Set (Perm (Fin 3))) := by
  ext g
  simp only [Set.mem_iUnion, mem_leftCoset_iff', Subgroup.mem_bot, inv_mul_eq_one]
  rw [iso_univ_x_y]
  simp only [Fin.exists_fin_two, τ]
  exact ⟨fun h => h.imp Eq.symm Eq.symm, fun h => h.imp Eq.symm Eq.symm⟩

/-- Reconstruction: `aut x` is generated by the single representative difference. -/
example : aut (isInvariant_univ ⊤) x = Subgroup.closure
    ((⋃ _ : Fin 2, ((⊥ : Subgroup (Perm (Fin 3))) : Set (Perm (Fin 3)))) ∪
      Set.range fun i => (τ 0)⁻¹ * τ i) :=
  aut_eq_closure_of_iso_eq_iUnion (isInvariant_univ ⊤) iso_eq_branches 0

example : (τ 0)⁻¹ * τ 1 = swap 0 1 := by decide

/-! ### Combining branch answers

The same branching, packaged as answers: two successful branches and one empty one. -/

def rs : List (Perm (Fin 3)) := [1, swap 0 1, swap 0 2]

theorem rs_cover : IsLeftCover ⊤ K0 fun i : Fin rs.length => rs.get i := by
  refine ⟨fun _ => Subgroup.mem_top _, ?_⟩
  simp only [Subgroup.mem_top, true_implies, mem_K0]
  decide

def branchAnswers : List (Answer (Fin 3)) := [some (c, ⊥), some (swap 0 2, ⊥), none]

theorem branchAnswers_correct (i : Fin rs.length) :
    Answer.IsCorrect (branchAnswers.get (i.cast rfl)) Set.univ (c * rs.get i) K0 x y := by
  unfold Answer.IsCorrect
  fin_cases i <;> ext g <;>
    simp only [branchAnswers, rs, Fin.cast, List.get, Answer.denote_some, Answer.denote_none,
      mem_leftCoset_iff', Subgroup.mem_bot, mem_iso, mem_K0, Set.mem_empty_iff_false] <;>
    revert g <;> decide

example : Answer.IsCorrect (combineBranches branchAnswers) Set.univ c ⊤ x y :=
  Answer.IsCorrect.combineBranches (isInvariant_univ ⊤) rs_cover le_top rfl branchAnswers_correct

example : combineBranches branchAnswers =
    some (c, branchSubgroup c [(c, ⊥), (swap 0 2, ⊥)]) := rfl

/-! ### Invariance from generators -/

example : IsInvariant (Subgroup.closure {swap (0 : Fin 3) 1}) W01 := by
  rw [isInvariant_closure_iff (Set.toFinite _)]
  simp only [Set.mem_singleton_iff, forall_eq]
  decide

example : FixesPointwise (Subgroup.closure {swap (0 : Fin 3) 1}) {2} := by
  rw [fixesPointwise_closure_iff]
  simp only [Set.mem_singleton_iff, forall_eq]
  decide

end GraphIsoChecks.Semantics
