module

public import Mathlib.Algebra.Group.Action.Pointwise.Finset
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Labelled hints

The recursion of milestone 14 (`PLAN-14.md` §2.1) carries, with an instance on a window `W`,
an optional **hint**: a finite **base** `Γ`, a homomorphism `ψ : M → Sym(Γ)` from the group
acting on the domain, and **labels** `lab : Ω → Finset Γ` that are equivariant on `W` and not
constant on `W`.

* `Equivar ψ W lab`, `NonConst W lab`, `IsHint ψ W lab`;
* the fibres of the labels are blocks; when `M` is transitive on `W` every fibre has at most
  `|W|/2` points (`card_fiber_le`), so a subset of `W` on which the labels are constant has
  at most `|W|/2` points (`card_le_of_const`);
* an element whose image fixes every label maps each point into its own fibre
  (`lab_smul_of_fix`);
* hints restrict to subgroups and to subwindows on which the labels are not constant
  (`IsHint.restrict`). Hinted instances are transitive on their windows: after a reduction
  `H ≤ M` of a transitive instance, each `H`-orbit keeps the hint or has at most half of the
  window (`orbit_child`).

The group is an arbitrary group `M` acting on `Ω`; in the applications `M = ↥G` for
`G : Subgroup (Perm Ω)`, or a subgroup of it.
-/

@[expose] public section

namespace GraphIso.Recursion

open Equiv MulAction Pointwise

variable {M Ω Γ : Type*} [Group M] [MulAction M Ω] [DecidableEq Γ]

/-- The labels are equivariant on the window `W`. -/
def Equivar (ψ : M →* Perm Γ) (W : Finset Ω) (lab : Ω → Finset Γ) : Prop :=
  ∀ g : M, ∀ u ∈ W, lab (g • u) = ψ g • lab u

/-- The labels are not constant on `W`. -/
def NonConst (W : Finset Ω) (lab : Ω → Finset Γ) : Prop :=
  ∃ u ∈ W, ∃ v ∈ W, lab u ≠ lab v

/-- **A hint** on the window `W`: equivariant labels that are not constant on `W`. -/
structure IsHint (ψ : M →* Perm Γ) (W : Finset Ω) (lab : Ω → Finset Γ) : Prop where
  equivar : Equivar ψ W lab
  nonconst : NonConst W lab

/-- `W` is invariant under `M`. -/
def Invariant (M : Type*) [Group M] [MulAction M Ω] (W : Finset Ω) : Prop :=
  ∀ g : M, ∀ u ∈ W, g • u ∈ W

/-- `M` is transitive on `W`. -/
def Transitive (M : Type*) [Group M] [MulAction M Ω] (W : Finset Ω) : Prop :=
  ∀ u ∈ W, ∀ v ∈ W, ∃ g : M, g • u = v

/-- The fibre of `u`: the points of `W` with the label of `u`. -/
def fiber (W : Finset Ω) (lab : Ω → Finset Γ) (u : Ω) : Finset Ω :=
  W.filter fun v => lab v = lab u

variable {ψ : M →* Perm Γ} {W : Finset Ω} {lab : Ω → Finset Γ}

/-- **Fibres are blocks**: `g` maps the fibre of `u` onto the fibre of `g • u`. -/
theorem card_fiber_smul (hW : Invariant M W) (h : Equivar ψ W lab) (g : M) {u : Ω}
    (hu : u ∈ W) : (fiber W lab (g • u)).card = (fiber W lab u).card := by
  have hgu := h g u hu
  refine Finset.card_nbij' (fun v => g⁻¹ • v) (fun v => g • v) ?_ ?_ ?_ ?_
  · intro v hv
    simp only [fiber, Finset.coe_filter, Set.mem_ofPred_eq] at hv ⊢
    refine ⟨hW _ _ hv.1, ?_⟩
    have h1 := h g⁻¹ v hv.1
    rw [h1, hv.2, hgu, map_inv, inv_smul_smul]
  · intro v hv
    simp only [fiber, Finset.coe_filter, Set.mem_ofPred_eq] at hv ⊢
    refine ⟨hW _ _ hv.1, ?_⟩
    rw [h g v hv.1, hv.2, hgu]
  · intro v _
    simp
  · intro v _
    simp

/-- **Fibres have at most half of the window** when `M` is transitive on `W`. -/
theorem card_fiber_le (hW : Invariant M W) (hT : Transitive M W) (hh : IsHint ψ W lab)
    {u : Ω} (hu : u ∈ W) : 2 * (fiber W lab u).card ≤ W.card := by
  obtain ⟨a, ha, b, hb, hab⟩ := hh.nonconst
  obtain ⟨v, hv, hvu⟩ : ∃ v ∈ W, lab v ≠ lab u := by
    by_cases hau : lab a = lab u
    · exact ⟨b, hb, fun hbu => hab (hau.trans hbu.symm)⟩
    · exact ⟨a, ha, hau⟩
  obtain ⟨g, rfl⟩ := hT u hu v hv
  have hcard := card_fiber_smul hW hh.equivar g hu
  have hdisj : Disjoint (fiber W lab u) (fiber W lab (g • u)) := by
    rw [Finset.disjoint_left]
    intro w hw hw'
    simp only [fiber, Finset.mem_filter] at hw hw'
    exact hvu (hw'.2.symm.trans hw.2)
  have hsub : (fiber W lab u).disjUnion (fiber W lab (g • u)) hdisj ⊆ W := by
    intro w hw
    rw [Finset.mem_disjUnion] at hw
    rcases hw with hw | hw <;> exact (Finset.mem_filter.1 hw).1
  have := Finset.card_le_card hsub
  rw [Finset.card_disjUnion, hcard] at this
  omega

/-- **Constant labels mean a small set**: a subset of `W` on which the labels are constant has
at most `|W|/2` points. -/
theorem card_le_of_const (hW : Invariant M W) (hT : Transitive M W) (hh : IsHint ψ W lab)
    {O : Finset Ω} (hO : O ⊆ W) (hc : ¬ NonConst O lab) : 2 * O.card ≤ W.card := by
  rcases O.eq_empty_or_nonempty with rfl | ⟨u₀, hu₀⟩
  · simp
  have hsub : O ⊆ fiber W lab u₀ := by
    intro u hu
    simp only [fiber, Finset.mem_filter]
    refine ⟨hO hu, ?_⟩
    by_contra hne
    exact hc ⟨u, hu, u₀, hu₀, hne⟩
  have := card_fiber_le hW hT hh (hO hu₀)
  have := Finset.card_le_card hsub
  omega

/-- An element whose image fixes every label keeps each point of `W` in its fibre. -/
theorem lab_smul_of_fix (h : Equivar ψ W lab) {g : M} (hg : ∀ u ∈ W, ψ g • lab u = lab u)
    {u : Ω} (hu : u ∈ W) : lab (g • u) = lab u :=
  (h g u hu).trans (hg u hu)

/-- **Restriction**: a hint restricts to a subgroup `H` and to a subwindow `O` on which the
labels are not constant. -/
theorem IsHint.restrict (h : Equivar ψ W lab) (H : Subgroup M) {O : Finset Ω} (hO : O ⊆ W)
    (hn : NonConst O lab) : IsHint (ψ.comp H.subtype) O lab :=
  ⟨fun g u hu => h g u (hO hu), hn⟩

/-- **The children of a macro-step.** Hinted instances are transitive on their windows (the
recursion keeps a hint only on an orbit of the current group). If `M` is transitive on `W` and
`H ≤ M`, every `H`-orbit `O` in `W` either carries the restricted hint or has at most half of
the window, so it may drop the hint. -/
theorem orbit_child (hW : Invariant M W) (hT : Transitive M W) (hh : IsHint ψ W lab)
    (H : Subgroup M) {O : Finset Ω} (hO : O ⊆ W) :
    IsHint (ψ.comp H.subtype) O lab ∨ 2 * O.card ≤ W.card := by
  by_cases hn : NonConst O lab
  · exact Or.inl (IsHint.restrict hh.equivar H hO hn)
  · exact Or.inr (card_le_of_const hW hT hh hO hn)

end GraphIso.Recursion
