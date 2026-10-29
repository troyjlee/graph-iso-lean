module

public import GraphIso.Semantics.StringIso

/-!
# Sequential processing of invariant windows, at the level of answers

`Answer.IsCorrect.union`: after solving the first window as `a₁`, the union of two windows is
solved by `none` if `a₁ = none`, and otherwise by any correct answer for the second window
inside the **updated** coset `a₁ = some (τ, H)`. No independence between the two windows is
assumed; the second window stays invariant under `H` because `H` is the automorphism
subgroup of the first window inside `G`.

`seqUnion` folds this over a list of windows (for example the orbits of `G` on a window).
Solving every window in the original coset independently would be wrong: the witnesses may be
incompatible. The sequential form passes the updated coset along.
-/

@[expose] public section

namespace GraphIso

open Equiv Pointwise

variable {Ω α : Type*}

/-- The union of a list of windows. -/
def seqUnion : List (Set Ω) → Set Ω
  | [] => ∅
  | W :: Ws => W ∪ seqUnion Ws

@[simp] theorem seqUnion_nil : seqUnion ([] : List (Set Ω)) = ∅ := rfl

@[simp] theorem seqUnion_cons (W : Set Ω) (Ws : List (Set Ω)) :
    seqUnion (W :: Ws) = W ∪ seqUnion Ws := rfl

theorem mem_seqUnion {Ws : List (Set Ω)} {u : Ω} : u ∈ seqUnion Ws ↔ ∃ W ∈ Ws, u ∈ W := by
  induction Ws with
  | nil => simp
  | cons W Ws ih => simp [ih]

theorem isInvariant_seqUnion {G : Subgroup (Perm Ω)} {Ws : List (Set Ω)}
    (h : ∀ W ∈ Ws, IsInvariant G W) : IsInvariant G (seqUnion Ws) := by
  induction Ws with
  | nil => exact isInvariant_empty G
  | cons W Ws ih =>
    exact (h W List.mem_cons_self).union (ih fun V hV => h V (List.mem_cons_of_mem _ hV))

section

variable {W₁ W₂ : Set Ω} {σ τ : Perm Ω} {G H : Subgroup (Perm Ω)} {x y : Ω → α}

/-- A first step with no solution: the union has none either. -/
theorem Answer.IsCorrect.union_none (h₁ : Answer.IsCorrect (none : Answer Ω) W₁ σ G x y) :
    Answer.IsCorrect (none : Answer Ω) (W₁ ∪ W₂) σ G x y := by
  unfold Answer.IsCorrect at h₁ ⊢
  rw [iso_union_of_eq_empty h₁.symm]
  rfl

/-- **Sequential windows.** After solving `W₁` as `τ • H`, a correct answer for `W₂` in the
updated coset `τ • H` is a correct answer for `W₁ ∪ W₂` in `σ • G`. -/
theorem Answer.IsCorrect.union_some {a₂ : Answer Ω}
    (h₁ : Answer.IsCorrect (some (τ, H)) W₁ σ G x y) (h₂ : Answer.IsCorrect a₂ W₂ τ H x y) :
    Answer.IsCorrect a₂ (W₁ ∪ W₂) σ G x y := by
  unfold Answer.IsCorrect at h₁ h₂ ⊢
  rw [h₂, iso_union_of_eq_smul h₁.symm]

/-- The subgroup of a correct successful first step leaves every `G`-invariant window
invariant, so the second step is a valid instance. -/
theorem Answer.IsCorrect.isInvariant_of_some {V : Set Ω} (hW₁ : IsInvariant G W₁)
    (h₁ : Answer.IsCorrect (some (τ, H)) W₁ σ G x y) (hV : IsInvariant G V) :
    IsInvariant H V := by
  rw [(Answer.IsCorrect.of_some hW₁ h₁).2]
  exact hV.aut hW₁ x

end

end GraphIso
