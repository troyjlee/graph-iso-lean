module

public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.GroupTheory.Coset.Basic
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.GroupTheory.GroupAction.Blocks
public import Mathlib.GroupTheory.Schreier
public import Mathlib.Computability.TuringMachine.Computable

/-!
# Phase 0 checks: the pinned mathlib API

Source-file availability does not settle theorem signatures, so this file restates the exact
forms of the mathlib facts the library relies on. It fails to compile if the pin changes them.
-/

@[expose] public section

namespace GraphIsoChecks.MathlibAPI

open Pointwise

variable {Ω : Type*} {G : Type*} [Group G]

-- Composition convention for permutations.
example (f g : Equiv.Perm Ω) (u : Ω) : (f * g) u = f (g u) := Equiv.Perm.mul_apply f g u
example (f : Equiv.Perm Ω) (u : Ω) : f⁻¹ u = f.symm u := rfl
example (f : Equiv.Perm Ω) (u : Ω) : f • u = f u := rfl

-- The string action is mathlib's `arrowAction`: `(g • F) a = F (g⁻¹ • a)`.
example (g : Equiv.Perm Ω) (F : Ω → Bool) :
    letI : MulAction (Equiv.Perm Ω) (Ω → Bool) := arrowAction
    g • F = fun a => F (g⁻¹ a) := rfl

-- Generated subgroups and closure induction.
example (k : Set G) (K : Subgroup G) : Subgroup.closure k ≤ K ↔ k ⊆ K := Subgroup.closure_le K
example (k : Set G) : k ⊆ Subgroup.closure k := Subgroup.subset_closure
example (s : Set G) (t : Set G) :
    Subgroup.closure (s ∪ t) = Subgroup.closure s ⊔ Subgroup.closure t :=
  Subgroup.closure_union s t
example {k : Set G} {p : (g : G) → g ∈ Subgroup.closure k → Prop}
    (mem : ∀ x (hx : x ∈ k), p x (Subgroup.subset_closure hx)) (one : p 1 (one_mem _))
    (mul : ∀ x y hx hy, p x hx → p y hy → p (x * y) (mul_mem hx hy))
    (inv : ∀ x hx, p x hx → p x⁻¹ (inv_mem hx)) {x} (hx : x ∈ Subgroup.closure k) : p x hx :=
  Subgroup.closure_induction mem one mul inv hx

-- Left cosets are pointwise translates `a • (H : Set G)`.
example (H : Subgroup G) (a x : G) : x ∈ a • (H : Set G) ↔ a⁻¹ * x ∈ H :=
  mem_leftCoset_iff a
example (H : Subgroup G) (a b : G) : a • (H : Set G) = b • H ↔ a⁻¹ * b ∈ H :=
  leftCoset_eq_iff H

-- Orbits and stabilizers.
example {X : Type*} [MulAction G X] (a b : X) : b ∈ MulAction.orbit G a ↔ ∃ g : G, g • a = b :=
  MulAction.mem_orbit_iff
example {X : Type*} [MulAction G X] (a : X) (g : G) :
    g ∈ MulAction.stabilizer G a ↔ g • a = a :=
  MulAction.mem_stabilizer_iff

-- Blocks.
example {X : Type*} [MulAction G X] (B : Set X) :
    MulAction.IsBlock G B ↔ ∀ ⦃g₁ g₂ : G⦄, g₁ • B ≠ g₂ • B → Disjoint (g₁ • B) (g₂ • B) :=
  Iff.rfl

-- Schreier's lemma (abstract generating set for a stabilizer-type subgroup).
example {H : Subgroup G} {R S : Set G} (hR : Subgroup.IsComplement (H : Set G) R)
    (hR1 : (1 : G) ∈ R) (hS : Subgroup.closure S = ⊤) :
    Subgroup.closure ((R * S).image fun g => g * (hR.toRightFun g : G)⁻¹) = H :=
  Subgroup.closure_mul_image_eq hR hR1 hS

-- Turing-machine time bounds, for the later machine bridge.
example : Type 1 := Turing.FinTM2
example {α β αΓ βΓ : Type} (ea : α → List αΓ) (eb : β → List βΓ) (f : α → β) : Type 1 :=
  Turing.TM2ComputableInPolyTime ea eb f

end GraphIsoChecks.MathlibAPI
