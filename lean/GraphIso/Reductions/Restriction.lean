module

public import GraphIso.Semantics.StringIso
public import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Restriction to an invariant window

For a `G`-invariant window `W ⊆ Ω` and a reindexing `e : α ≃ W` (for a listed window, its list
order), `restrictHom hW e : G →* Perm α` is the action of `G` on `W`, transported to `α`. A
string `x` restricts to `x ∘ e`.

* `matches_restrict`: for `g ∈ G`, matching on `W` is matching of `ρ g` on all of `α`.
* `mem_iso_one_iff_restrict`: the solutions in `G` on `W` are the elements of `G` whose
  restrictions solve the restricted instance in `ρ(G)` on all of `α`.
* `iso_one_eq_of_restrict` (**lifting**): if the restricted solutions are `τ' • H'`, `τ ∈ G`
  restricts to `τ'`, and `ρ(L)` generates `H'` for some `L ⊆ G`, then the solutions on `W` are
  `τ • (⟨L⟩ ⊔ K)`, where `K = pointwiseStab G W` is the kernel of the restriction.
* `iso_one_eq_empty_of_restrict`: no restricted solution, no solution.
* `pointwiseStab_le_aut`: the kernel lies in every automorphism subgroup on `W`. So the kernel
  cannot be dropped: whenever the restriction is not faithful and `⟨L⟩` misses part of `K`,
  `τ • ⟨L⟩` misses solutions.
* `iso_eq_of_restrict`: the same with an arbitrary outer representative `σ`, after the target
  is normalized to `y ∘ σ`.
-/

@[expose] public section

namespace GraphIso

open Equiv Pointwise

variable {Ω α β : Type*} {G : Subgroup (Perm Ω)} {W : Set Ω}

section Hom

variable (hW : IsInvariant G W) (e : α ≃ W)

/-- The restriction of `g ∈ G` to the invariant window, as a permutation of `W`. -/
def restrictPermW (g : G) : Perm W :=
  (g : Perm Ω).subtypePerm fun _ => hW.apply_mem_iff g.2

/-- The action of `G` on the invariant window `W`, transported to `α` along `e`. -/
def restrictHom : G →* Perm α where
  toFun g := e.symm.permCongr (restrictPermW hW g)
  map_one' := by
    ext j
    simp [restrictPermW, Equiv.permCongr_apply]
  map_mul' g h := by
    ext j
    simp [restrictPermW, Equiv.permCongr_apply, Perm.mul_apply]

/-- The defining property: `e (ρ g j) = g (e j)`. -/
theorem restrictHom_apply (g : G) (j : α) :
    (e (restrictHom hW e g j) : Ω) = (g : Perm Ω) (e j) := by
  simp [restrictHom, restrictPermW, Equiv.permCongr_apply]

theorem restrictHom_eq_iff (g : G) (π : Perm α) :
    restrictHom hW e g = π ↔ ∀ j, (g : Perm Ω) (e j) = e (π j) := by
  constructor
  · rintro rfl j
    exact (restrictHom_apply hW e g j).symm
  · intro h
    ext j
    exact e.injective (Subtype.ext ((restrictHom_apply hW e g j).trans (h j)))

/-- The kernel of the restriction is the pointwise stabilizer of the window. -/
theorem restrictHom_eq_one_iff (g : G) :
    restrictHom hW e g = 1 ↔ (g : Perm Ω) ∈ pointwiseStab G W := by
  rw [restrictHom_eq_iff, mem_pointwiseStab]
  simp only [Perm.coe_one, id_eq]
  constructor
  · intro h
    refine ⟨g.2, fun u hu => ?_⟩
    simpa using h (e.symm ⟨u, hu⟩)
  · rintro ⟨-, h⟩ j
    exact h _ (e j).2

theorem map_ker_restrictHom :
    (restrictHom hW e).ker.map G.subtype = pointwiseStab G W := by
  ext g
  simp only [Subgroup.mem_map, MonoidHom.mem_ker, Subgroup.coe_subtype]
  constructor
  · rintro ⟨g', hg', rfl⟩
    exact (restrictHom_eq_one_iff hW e g').1 hg'
  · intro hg
    exact ⟨⟨g, hg.1⟩, (restrictHom_eq_one_iff hW e _).2 hg, rfl⟩

/-- Matching on the window is matching of the restriction on the whole reindexed domain. -/
theorem matches_restrict (g : G) (x y : Ω → β) :
    Matches W g x y ↔
      Matches Set.univ (restrictHom hW e g) (fun j => x (e j)) (fun j => y (e j)) := by
  simp only [Matches, Set.mem_univ, true_implies, restrictHom_apply]
  constructor
  · intro h j
    exact h _ (e j).2
  · intro h u hu
    simpa using h (e.symm ⟨u, hu⟩)

end Hom

section Iso

variable (hW : IsInvariant G W) (e : α ≃ W) {x y : Ω → β}

/-- The solutions on `W` are the elements of `G` whose restrictions solve the restricted
instance. -/
theorem mem_iso_one_iff_restrict {g : Perm Ω} :
    g ∈ iso W 1 G x y ↔ ∃ hg : g ∈ G, restrictHom hW e ⟨g, hg⟩ ∈
      iso Set.univ 1 (restrictHom hW e).range (fun j => x (e j)) (fun j => y (e j)) := by
  rw [mem_iso_one]
  constructor
  · rintro ⟨hg, hm⟩
    refine ⟨hg, ?_⟩
    rw [mem_iso_one]
    exact ⟨⟨⟨g, hg⟩, rfl⟩, (matches_restrict hW e ⟨g, hg⟩ x y).1 hm⟩
  · rintro ⟨hg, h⟩
    rw [mem_iso_one] at h
    exact ⟨hg, (matches_restrict hW e ⟨g, hg⟩ x y).2 h.2⟩

/-- No restricted solution, no solution. -/
theorem iso_one_eq_empty_of_restrict
    (h : iso Set.univ 1 (restrictHom hW e).range (fun j => x (e j)) (fun j => y (e j)) = ∅) :
    iso W 1 G x y = ∅ := by
  ext g
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hg
  obtain ⟨hgG, hr⟩ := (mem_iso_one_iff_restrict hW e).1 hg
  rw [h] at hr
  exact hr

/-- **Lifting a restricted answer.** The kernel `pointwiseStab G W` is part of the answer. -/
theorem iso_one_eq_of_restrict {τ' : Perm α} {H' : Subgroup (Perm α)}
    (h : iso Set.univ 1 (restrictHom hW e).range (fun j => x (e j)) (fun j => y (e j)) =
      τ' • (H' : Set (Perm α)))
    {τ : Perm Ω} (hτ : τ ∈ G) (hττ : restrictHom hW e ⟨τ, hτ⟩ = τ') {L : Set (Perm Ω)}
    (hLG : L ⊆ G)
    (hL : Subgroup.closure {π | ∃ l, ∃ hl : l ∈ G, l ∈ L ∧ restrictHom hW e ⟨l, hl⟩ = π} = H') :
    iso W 1 G x y =
      τ • ((Subgroup.closure L ⊔ pointwiseStab G W : Subgroup (Perm Ω)) : Set (Perm Ω)) := by
  set ρ := restrictHom hW e
  set LG : Set G := {g | (g : Perm Ω) ∈ L}
  have himg : ρ '' LG = {π | ∃ l, ∃ hl : l ∈ G, l ∈ L ∧ ρ ⟨l, hl⟩ = π} := by
    ext π
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨g, g.2, hg, rfl⟩
    · rintro ⟨l, hl, hlL, rfl⟩
      exact ⟨⟨l, hl⟩, hlL, rfl⟩
  have hH' : H' = (Subgroup.closure LG).map ρ := by
    rw [MonoidHom.map_closure, himg, hL]
  have hsub : G.subtype '' LG = L := by
    ext g
    constructor
    · rintro ⟨g', hg', rfl⟩
      exact hg'
    · intro hg
      exact ⟨⟨g, hLG hg⟩, hg, rfl⟩
  have hS : ((H'.comap ρ).map G.subtype) = Subgroup.closure L ⊔ pointwiseStab G W := by
    rw [hH', Subgroup.comap_map_eq, Subgroup.map_sup, MonoidHom.map_closure, hsub,
      map_ker_restrictHom]
  rw [← hS]
  ext g
  rw [mem_iso_one_iff_restrict hW e, h, mem_leftCoset_iff, SetLike.mem_coe]
  constructor
  · rintro ⟨hg, hgH⟩
    rw [mem_leftCoset_iff, SetLike.mem_coe] at hgH
    refine ⟨⟨τ⁻¹ * g, mul_mem (inv_mem hτ) hg⟩, ?_, rfl⟩
    show ρ (⟨τ, hτ⟩⁻¹ * ⟨g, hg⟩) ∈ H'
    rw [map_mul, map_inv, hττ]
    exact hgH
  · rintro ⟨g', hg', hgg'⟩
    have hg : g ∈ G := by
      have : g = τ * g' := by rw [Subgroup.coe_subtype] at hgg'; rw [hgg']; group
      rw [this]
      exact mul_mem hτ g'.2
    refine ⟨hg, ?_⟩
    rw [mem_leftCoset_iff, SetLike.mem_coe]
    have he : (⟨τ, hτ⟩⁻¹ * ⟨g, hg⟩ : G) = g' := Subtype.ext (by simpa using hgg'.symm)
    rw [← hττ, ← map_inv, ← map_mul, he]
    exact hg'

/-- The kernel lies in the automorphism subgroup of every string on the window. -/
theorem pointwiseStab_le_aut (x : Ω → β) : pointwiseStab G W ≤ aut hW x := by
  rintro g ⟨hg, hfix⟩
  rw [mem_aut]
  exact ⟨hg, fun u hu => by rw [hfix u hu]⟩

/-- **Restriction with an outer representative.** The target is normalized to `y ∘ σ`, the
normalized instance is restricted and its answer lifted. -/
theorem iso_eq_of_restrict (σ : Perm Ω) {τ' : Perm α} {H' : Subgroup (Perm α)}
    (h : iso Set.univ 1 (restrictHom hW e).range (fun j => x (e j)) (fun j => y (σ (e j))) =
      τ' • (H' : Set (Perm α)))
    {τ : Perm Ω} (hτ : τ ∈ G) (hττ : restrictHom hW e ⟨τ, hτ⟩ = τ') {L : Set (Perm Ω)}
    (hLG : L ⊆ G)
    (hL : Subgroup.closure {π | ∃ l, ∃ hl : l ∈ G, l ∈ L ∧ restrictHom hW e ⟨l, hl⟩ = π} = H') :
    iso W σ G x y =
      (σ * τ) • ((Subgroup.closure L ⊔ pointwiseStab G W : Subgroup (Perm Ω)) :
        Set (Perm Ω)) := by
  rw [iso_eq_smul_iso_one, iso_one_eq_of_restrict hW e (y := fun u => y (σ u)) h hτ hττ hLG hL,
    smul_smul]

theorem iso_eq_empty_of_restrict (σ : Perm Ω)
    (h : iso Set.univ 1 (restrictHom hW e).range (fun j => x (e j)) (fun j => y (σ (e j))) = ∅) :
    iso W σ G x y = ∅ := by
  rw [iso_eq_smul_iso_one, iso_one_eq_empty_of_restrict hW e (y := fun u => y (σ u)) h,
    Set.smul_set_empty]

end Iso

end GraphIso
