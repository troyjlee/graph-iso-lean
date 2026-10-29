module

public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Set.Lattice.Indexed

/-!
# Permutations acting on strings

This file fixes the conventions used throughout the library (see also
`docs/conventions.md`).

* `Equiv.Perm Ω` is multiplied by composition, `(g * h) u = g (h u)`
  (`Equiv.Perm.mul_apply`).
* A string over the alphabet `α` is a function `x : Ω → α`. A permutation relabels a
  string by `(relabel g x) u = x (g⁻¹ u)`, so the symbol at position `u` moves to
  position `g u`. This is mathlib's `arrowAction`, which is a definition rather than a
  global instance; `relabel_eq_smul` is the bridge.
* `Matches W g x y` says that `g` carries `x` to `y` on the window `W`:
  `∀ u ∈ W, x u = y (g u)`. It does not mention `g⁻¹`, so executable checks never need
  to invert a permutation. On the whole domain it is equivalent to `relabel g x = y`
  (`matches_univ_iff`).
-/

@[expose] public section

namespace GraphIso

open Equiv

variable {Ω α : Type*}

@[simp] theorem perm_apply_inv_self (g : Perm Ω) (u : Ω) : g (g⁻¹ u) = u :=
  Equiv.apply_symm_apply g u

@[simp] theorem perm_inv_apply_self (g : Perm Ω) (u : Ω) : g⁻¹ (g u) = u :=
  Equiv.symm_apply_apply g u

/-- Relabel a string by a permutation: `(relabel g x) u = x (g⁻¹ u)`. -/
def relabel (g : Perm Ω) (x : Ω → α) : Ω → α := fun u => x (g⁻¹ u)

@[simp] theorem relabel_apply (g : Perm Ω) (x : Ω → α) (u : Ω) :
    relabel g x u = x (g⁻¹ u) := rfl

@[simp] theorem relabel_apply_self (g : Perm Ω) (x : Ω → α) (u : Ω) :
    relabel g x (g u) = x u := by
  simp

@[simp] theorem relabel_one (x : Ω → α) : relabel 1 x = x := rfl

theorem relabel_mul (g h : Perm Ω) (x : Ω → α) :
    relabel (g * h) x = relabel g (relabel h x) := by
  funext u
  simp [mul_inv_rev]

/-- `relabel` is the action `(g • x) u = x (g⁻¹ • u)` of mathlib's `arrowAction`. -/
theorem relabel_eq_smul (g : Perm Ω) (x : Ω → α) :
    letI : MulAction (Perm Ω) (Ω → α) := arrowAction
    g • x = relabel g x := rfl

/-- `Matches W g x y`: the permutation `g` carries the string `x` to the string `y` on the
window `W`, that is, `x u = y (g u)` for every `u ∈ W`. -/
def Matches (W : Set Ω) (g : Perm Ω) (x y : Ω → α) : Prop :=
  ∀ u ∈ W, x u = y (g u)

instance [Fintype Ω] [DecidableEq α] (W : Set Ω) [DecidablePred (· ∈ W)] (g : Perm Ω)
    (x y : Ω → α) : Decidable (Matches W g x y) :=
  inferInstanceAs (Decidable (∀ u ∈ W, x u = y (g u)))

theorem matches_iff {W : Set Ω} {g : Perm Ω} {x y : Ω → α} :
    Matches W g x y ↔ ∀ u ∈ W, x u = y (g u) := Iff.rfl

theorem Matches.mono {W V : Set Ω} {g : Perm Ω} {x y : Ω → α} (h : Matches V g x y)
    (hWV : W ⊆ V) : Matches W g x y :=
  fun u hu => h u (hWV hu)

@[simp] theorem matches_empty (g : Perm Ω) (x y : Ω → α) : Matches ∅ g x y :=
  fun _ hu => hu.elim

theorem matches_union {W₁ W₂ : Set Ω} {g : Perm Ω} {x y : Ω → α} :
    Matches (W₁ ∪ W₂) g x y ↔ Matches W₁ g x y ∧ Matches W₂ g x y := by
  simp only [Matches, Set.mem_union]
  exact ⟨fun h => ⟨fun u hu => h u (Or.inl hu), fun u hu => h u (Or.inr hu)⟩,
    fun h u hu => hu.elim (h.1 u) (h.2 u)⟩

theorem matches_iUnion {ι : Sort*} {W : ι → Set Ω} {g : Perm Ω} {x y : Ω → α} :
    Matches (⋃ i, W i) g x y ↔ ∀ i, Matches (W i) g x y := by
  simp only [Matches, Set.mem_iUnion]
  exact ⟨fun h i u hu => h u ⟨i, hu⟩, fun h u ⟨i, hu⟩ => h i u hu⟩

theorem matches_one_iff {W : Set Ω} {x y : Ω → α} :
    Matches W 1 x y ↔ ∀ u ∈ W, x u = y u := Iff.rfl

/-- Moving a left factor of the permutation onto the target string. This is the pointwise
form of coset normalization. -/
theorem matches_mul_iff {W : Set Ω} {σ g : Perm Ω} {x y : Ω → α} :
    Matches W (σ * g) x y ↔ Matches W g x (fun u => y (σ u)) := Iff.rfl

/-- Composition of matches: if `g` carries `x` to `y` on `W` and `h` carries `y` to `z` on
the image `g '' W`, then `h * g` carries `x` to `z` on `W`. -/
theorem Matches.mul {W : Set Ω} {g h : Perm Ω} {x y z : Ω → α} (hg : Matches W g x y)
    (hh : Matches (g '' W) h y z) : Matches W (h * g) x z :=
  fun u hu => (hg u hu).trans (hh (g u) ⟨u, hu, rfl⟩)

/-- Reversing a match: if `g` carries `x` to `y` on `W`, then `g⁻¹` carries `y` to `x` on
`g '' W`. -/
theorem Matches.inv {W : Set Ω} {g : Perm Ω} {x y : Ω → α} (hg : Matches W g x y) :
    Matches (g '' W) g⁻¹ y x := by
  rintro _ ⟨u, hu, rfl⟩
  simpa using (hg u hu).symm

/-- On the whole domain, `Matches` is the relabelling equation `g • x = y`. -/
theorem matches_univ_iff {g : Perm Ω} {x y : Ω → α} :
    Matches Set.univ g x y ↔ relabel g x = y := by
  constructor
  · intro h
    funext u
    simpa using h (g⁻¹ u) trivial
  · rintro rfl u _
    simp

/-- The bridge to mathlib's `arrowAction`: on the whole domain, `Matches` is `g • x = y`. -/
theorem matches_univ_iff_smul {g : Perm Ω} {x y : Ω → α} :
    letI : MulAction (Perm Ω) (Ω → α) := arrowAction
    Matches Set.univ g x y ↔ g • x = y :=
  matches_univ_iff

end GraphIso
