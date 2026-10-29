module

public import GraphIso.Semantics.Action
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Data.Set.Card
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic

/-!
# Invariant windows

A window is a set of positions `W : Set Ω`. A coset-valued answer is only available when
`W` is invariant under the current group `G`; this is an explicit hypothesis
`IsInvariant G W` throughout the library, never an implicit convention. The coset
representative is *not* required to preserve `W`.

The main results here:

* `IsInvariant.apply_mem_iff`, `IsInvariant.image_eq`: forward invariance under a subgroup
  already gives `g '' W = W`, because the subgroup contains `g⁻¹`.
* `isInvariant_closure_iff`: for a *finite* window, invariance under the generated subgroup
  is equivalent to forward invariance under the generators. Executable validation therefore
  only inspects the supplied generators.
* `FixesPointwise` and the orbit lemmas used by the solver.
-/

@[expose] public section

namespace GraphIso

open Equiv Pointwise

variable {Ω : Type*}

/-- The window `W` is invariant under the subgroup `G`: every element of `G` maps `W` into
`W`. -/
def IsInvariant (G : Subgroup (Perm Ω)) (W : Set Ω) : Prop :=
  ∀ g ∈ G, ∀ u ∈ W, g u ∈ W

/-- The subgroup `G` fixes every point of the window `W`. -/
def FixesPointwise (G : Subgroup (Perm Ω)) (W : Set Ω) : Prop :=
  ∀ g ∈ G, ∀ u ∈ W, g u = u

/-- The pointwise stabilizer `{g ∈ G | ∀ u ∈ W, g u = u}`. -/
def pointwiseStab (G : Subgroup (Perm Ω)) (W : Set Ω) : Subgroup (Perm Ω) where
  carrier := {g | g ∈ G ∧ ∀ u ∈ W, g u = u}
  one_mem' := ⟨G.one_mem, fun _ _ => rfl⟩
  mul_mem' := by
    rintro g h ⟨hg, hg'⟩ ⟨hh, hh'⟩
    exact ⟨mul_mem hg hh, fun u hu => by rw [Perm.mul_apply, hh' u hu, hg' u hu]⟩
  inv_mem' := by
    rintro g ⟨hg, hg'⟩
    exact ⟨inv_mem hg, fun u hu => by
      conv_lhs => rw [← hg' u hu]
      simp⟩

theorem mem_pointwiseStab {G : Subgroup (Perm Ω)} {W : Set Ω} {g : Perm Ω} :
    g ∈ pointwiseStab G W ↔ g ∈ G ∧ ∀ u ∈ W, g u = u := Iff.rfl

theorem pointwiseStab_le (G : Subgroup (Perm Ω)) (W : Set Ω) : pointwiseStab G W ≤ G :=
  fun _ h => h.1

namespace IsInvariant

variable {G H : Subgroup (Perm Ω)} {W V : Set Ω} {g : Perm Ω} {u : Ω}

theorem apply_mem (hW : IsInvariant G W) (hg : g ∈ G) (hu : u ∈ W) : g u ∈ W :=
  hW g hg u hu

theorem inv_apply_mem (hW : IsInvariant G W) (hg : g ∈ G) (hu : u ∈ W) : g⁻¹ u ∈ W :=
  hW g⁻¹ (inv_mem hg) u hu

theorem apply_mem_iff (hW : IsInvariant G W) (hg : g ∈ G) : g u ∈ W ↔ u ∈ W :=
  ⟨fun h => by simpa using hW.inv_apply_mem hg h, hW.apply_mem hg⟩

theorem image_eq (hW : IsInvariant G W) (hg : g ∈ G) : g '' W = W := by
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact hW.apply_mem hg hu
  · intro hv
    exact ⟨g⁻¹ v, hW.inv_apply_mem hg hv, by simp⟩

theorem mono (hW : IsInvariant G W) (hHG : H ≤ G) : IsInvariant H W :=
  fun g hg u hu => hW g (hHG hg) u hu

theorem union (hW : IsInvariant G W) (hV : IsInvariant G V) : IsInvariant G (W ∪ V) := by
  rintro g hg u (hu | hu)
  · exact Or.inl (hW.apply_mem hg hu)
  · exact Or.inr (hV.apply_mem hg hu)

theorem inter (hW : IsInvariant G W) (hV : IsInvariant G V) : IsInvariant G (W ∩ V) :=
  fun _ hg _ hu => ⟨hW.apply_mem hg hu.1, hV.apply_mem hg hu.2⟩

theorem compl (hW : IsInvariant G W) : IsInvariant G Wᶜ :=
  fun _ hg _ hu h => hu ((hW.apply_mem_iff hg).1 h)

theorem diff (hW : IsInvariant G W) (hV : IsInvariant G V) : IsInvariant G (W \ V) :=
  hW.inter hV.compl

end IsInvariant

theorem isInvariant_empty (G : Subgroup (Perm Ω)) : IsInvariant G ∅ :=
  fun _ _ _ hu => hu.elim

theorem isInvariant_univ (G : Subgroup (Perm Ω)) : IsInvariant G Set.univ :=
  fun _ _ _ _ => trivial

theorem isInvariant_bot (W : Set Ω) : IsInvariant ⊥ W := by
  intro g hg u hu
  rw [Subgroup.mem_bot] at hg
  simpa [hg] using hu

theorem isInvariant_iUnion {ι : Sort*} {G : Subgroup (Perm Ω)} {W : ι → Set Ω}
    (hW : ∀ i, IsInvariant G (W i)) : IsInvariant G (⋃ i, W i) := by
  intro g hg u hu
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hu
  exact Set.mem_iUnion.2 ⟨i, (hW i).apply_mem hg hi⟩

/-- Invariance is containment in the setwise stabilizer of the window. -/
theorem isInvariant_iff_le_stabilizer {G : Subgroup (Perm Ω)} {W : Set Ω} :
    IsInvariant G W ↔ G ≤ MulAction.stabilizer (Perm Ω) W := by
  constructor
  · intro hW g hg
    rw [MulAction.mem_stabilizer_iff, ← Set.image_smul]
    exact hW.image_eq hg
  · intro hG g hg u hu
    have h : g • W = W := hG hg
    rw [← Set.image_smul] at h
    exact h ▸ ⟨u, hu, rfl⟩

/-- A permutation that maps a finite set into itself maps it onto itself. -/
theorem image_eq_of_mapsTo_of_finite {W : Set Ω} (hW : W.Finite) {g : Perm Ω}
    (hg : ∀ u ∈ W, g u ∈ W) : g '' W = W := by
  have hsub : g '' W ⊆ W := by
    rintro _ ⟨u, hu, rfl⟩
    exact hg u hu
  refine Set.eq_of_subset_of_ncard_le hsub ?_ hW
  rw [Set.ncard_image_of_injective W g.injective]

/-- For a finite window, invariance under the generated subgroup is equivalent to forward
invariance under each generator. Executable validation uses only the right-hand side. -/
theorem isInvariant_closure_iff {S : Set (Perm Ω)} {W : Set Ω} (hW : W.Finite) :
    IsInvariant (Subgroup.closure S) W ↔ ∀ g ∈ S, ∀ u ∈ W, g u ∈ W := by
  refine ⟨fun h g hg => h g (Subgroup.subset_closure hg), fun h => ?_⟩
  rw [isInvariant_iff_le_stabilizer, Subgroup.closure_le]
  intro g hg
  rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, ← Set.image_smul]
  exact image_eq_of_mapsTo_of_finite hW (h g hg)

theorem isInvariant_of_fixesPointwise {G : Subgroup (Perm Ω)} {W : Set Ω}
    (h : FixesPointwise G W) : IsInvariant G W := by
  intro g hg u hu
  rw [h g hg u hu]
  exact hu

theorem FixesPointwise.mono {G H : Subgroup (Perm Ω)} {W V : Set Ω} (h : FixesPointwise G W)
    (hHG : H ≤ G) (hVW : V ⊆ W) : FixesPointwise H V :=
  fun g hg u hu => h g (hHG hg) u (hVW hu)

theorem fixesPointwise_empty (G : Subgroup (Perm Ω)) : FixesPointwise G ∅ :=
  fun _ _ _ hu => hu.elim

theorem fixesPointwise_bot (W : Set Ω) : FixesPointwise ⊥ W := by
  intro g hg u _
  rw [Subgroup.mem_bot] at hg
  simp [hg]

/-- Pointwise fixing by a generated subgroup is checked on the generators. -/
theorem fixesPointwise_closure_iff {S : Set (Perm Ω)} {W : Set Ω} :
    FixesPointwise (Subgroup.closure S) W ↔ ∀ g ∈ S, ∀ u ∈ W, g u = u := by
  refine ⟨fun h g hg => h g (Subgroup.subset_closure hg), fun h g hg => ?_⟩
  induction hg using Subgroup.closure_induction with
  | mem g hg => exact h g hg
  | one => exact fun _ _ => rfl
  | mul g₁ g₂ _ _ ih₁ ih₂ =>
    intro u hu
    rw [Perm.mul_apply, ih₂ u hu, ih₁ u hu]
  | inv g _ ih =>
    intro u hu
    conv_lhs => rw [← ih u hu]
    simp

/-! ### Orbits of a subgroup -/

/-- The orbit of `u` under the subgroup `G`, as a set of positions. -/
def orbitOf (G : Subgroup (Perm Ω)) (u : Ω) : Set Ω :=
  {v | ∃ g ∈ G, g u = v}

theorem mem_orbitOf {G : Subgroup (Perm Ω)} {u v : Ω} :
    v ∈ orbitOf G u ↔ ∃ g ∈ G, g u = v := Iff.rfl

theorem self_mem_orbitOf (G : Subgroup (Perm Ω)) (u : Ω) : u ∈ orbitOf G u :=
  ⟨1, one_mem G, rfl⟩

theorem orbitOf_eq_orbit (G : Subgroup (Perm Ω)) (u : Ω) :
    orbitOf G u = MulAction.orbit G u := by
  ext v
  rw [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, hg⟩, rfl⟩
  · rintro ⟨⟨g, hg⟩, rfl⟩
    exact ⟨g, hg, rfl⟩

theorem isInvariant_orbitOf (G : Subgroup (Perm Ω)) (u : Ω) : IsInvariant G (orbitOf G u) := by
  rintro g hg _ ⟨h, hh, rfl⟩
  exact ⟨g * h, mul_mem hg hh, rfl⟩

theorem orbitOf_subset {G : Subgroup (Perm Ω)} {W : Set Ω} (hW : IsInvariant G W) {u : Ω}
    (hu : u ∈ W) : orbitOf G u ⊆ W := by
  rintro _ ⟨g, hg, rfl⟩
  exact hW.apply_mem hg hu

theorem orbitOf_eq_of_mem {G : Subgroup (Perm Ω)} {u v : Ω} (hv : v ∈ orbitOf G u) :
    orbitOf G v = orbitOf G u := by
  obtain ⟨g, hg, rfl⟩ := hv
  ext w
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h * g, mul_mem hh hg, rfl⟩
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h * g⁻¹, mul_mem hh (inv_mem hg), by simp⟩

theorem orbitOf_mono {G H : Subgroup (Perm Ω)} (hHG : H ≤ G) (u : Ω) :
    orbitOf H u ⊆ orbitOf G u := by
  rintro _ ⟨g, hg, rfl⟩
  exact ⟨g, hHG hg, rfl⟩

/-- The group acts transitively on the window `W`. -/
def IsTransitiveOn (G : Subgroup (Perm Ω)) (W : Set Ω) : Prop :=
  ∀ u ∈ W, ∀ v ∈ W, ∃ g ∈ G, g u = v

theorem IsTransitiveOn.orbitOf_eq {G : Subgroup (Perm Ω)} {W : Set Ω} (hW : IsInvariant G W)
    (hT : IsTransitiveOn G W) {u : Ω} (hu : u ∈ W) : orbitOf G u = W :=
  Set.Subset.antisymm (orbitOf_subset hW hu) fun v hv => hT u hu v hv

end GraphIso
