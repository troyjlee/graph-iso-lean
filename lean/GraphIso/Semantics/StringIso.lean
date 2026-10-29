module

public import GraphIso.Semantics.Window
public import GraphIso.Semantics.Coset

/-!
# Windowed string isomorphism

For a window `W`, a left coset `σ • G` and strings `x y : Ω → α`,
`iso W σ G x y` is the set of `g ∈ σ • G` carrying `x` to `y` on `W`. When `W` is
`G`-invariant, `aut hW x` is the subgroup of `G` preserving `x` on `W`.

Main results:

* `iso_eq_smul_aut` (**solution-coset theorem**): if `τ` is any solution then the solution
  set is exactly the coset `τ • aut hW x`. The answer subgroup is the full automorphism
  subgroup of the *source* string inside the *input* group.
* `iso_eq_smul_iso_one` (**normalization**): `iso W σ G x y = σ • iso W 1 G x (y ∘ σ)`.
  The representative `σ` is arbitrary and need not preserve `W`.
* `iso_union_of_eq_smul` (**sequential windows**): once the first window has been solved as
  `τ • H`, the union is solved by the second window inside the *updated* coset `τ • H`.
* `iso_eq_iUnion_of_isLeftCover` and `aut_eq_closure_of_iso_eq_iUnion` (**branching**): the
  solution set splits along a cover of `G` by cosets of `K ≤ G`, and the branch answers
  reconstruct the automorphism subgroup.
* `Answer` and `Answer.IsCorrect`: the semantic form of a solver result.
-/

@[expose] public section

namespace GraphIso

open Equiv Pointwise

variable {Ω α : Type*}

/-- The windowed isomorphisms from `x` to `y` in the left coset `σ • G`:
`{g ∈ σ • G | ∀ u ∈ W, x u = y (g u)}`. -/
def iso (W : Set Ω) (σ : Perm Ω) (G : Subgroup (Perm Ω)) (x y : Ω → α) : Set (Perm Ω) :=
  {g | g ∈ σ • (G : Set (Perm Ω)) ∧ Matches W g x y}

section Iso

variable {W W₁ W₂ : Set Ω} {σ τ g : Perm Ω} {G H K : Subgroup (Perm Ω)} {x y : Ω → α}

theorem mem_iso : g ∈ iso W σ G x y ↔ σ⁻¹ * g ∈ G ∧ Matches W g x y := by
  rw [iso, Set.mem_ofPred_eq, mem_leftCoset_iff']

theorem iso_subset_leftCoset : iso W σ G x y ⊆ σ • (G : Set (Perm Ω)) :=
  fun _ hg => hg.1

theorem Matches.mem_iso (hm : Matches W g x y) (hg : σ⁻¹ * g ∈ G) : g ∈ iso W σ G x y :=
  GraphIso.mem_iso.2 ⟨hg, hm⟩

theorem iso_anti_window (hWV : W₁ ⊆ W₂) : iso W₂ σ G x y ⊆ iso W₁ σ G x y :=
  fun _ hg => ⟨hg.1, hg.2.mono hWV⟩

theorem iso_mono_group (hHG : H ≤ G) (hτ : σ⁻¹ * τ ∈ G) :
    iso W τ H x y ⊆ iso W σ G x y := fun _ hg =>
  ⟨leftCoset_subset_leftCoset ((mem_leftCoset_iff' (H := G)).2 hτ) hHG hg.1, hg.2⟩

/-- Replacing the representative by another one of the same coset does not change the
solution set. -/
theorem iso_congr_leftCoset {σ' : Perm Ω} (h : σ • (G : Set (Perm Ω)) = σ' • (G : Set _)) :
    iso W σ G x y = iso W σ' G x y := by
  ext g
  simp only [iso, Set.mem_ofPred_eq, h]

/-- An empty window imposes no condition: the answer is the whole input coset. -/
@[simp] theorem iso_empty_window : iso ∅ σ G x y = σ • (G : Set (Perm Ω)) := by
  ext g
  simp [iso]

/-- Over an empty domain every window is empty. -/
theorem iso_of_isEmpty [IsEmpty Ω] : iso W σ G x y = σ • (G : Set (Perm Ω)) := by
  rw [Set.eq_empty_of_isEmpty W, iso_empty_window]

/-- On the full domain, the solutions are the elements of the coset relabelling `x` to `y`. -/
theorem mem_iso_univ : g ∈ iso Set.univ σ G x y ↔ σ⁻¹ * g ∈ G ∧ relabel g x = y := by
  rw [mem_iso, matches_univ_iff]

/-! ### Normalization of the coset representative -/

/-- Left multiplication of the representative moves onto the target string. -/
theorem iso_mul_left (π : Perm Ω) :
    iso W (π * σ) G x y = π • iso W σ G x (fun u => y (π u)) := by
  ext g
  rw [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul, mem_iso, mem_iso, mul_inv_rev,
    mul_assoc, ← matches_mul_iff, mul_inv_cancel_left]

/-- **Normalization.** An arbitrary coset `σ • G` reduces to the subgroup `G` itself by
replacing the target `y` by `y ∘ σ`. -/
theorem iso_eq_smul_iso_one (W : Set Ω) (σ : Perm Ω) (G : Subgroup (Perm Ω)) (x y : Ω → α) :
    iso W σ G x y = σ • iso W 1 G x (fun u => y (σ u)) := by
  simpa using iso_mul_left (W := W) (σ := 1) (G := G) (x := x) (y := y) σ

theorem mem_iso_one : g ∈ iso W 1 G x y ↔ g ∈ G ∧ Matches W g x y := by
  rw [mem_iso, inv_one, one_mul]

/-! ### Unions of windows -/

theorem iso_union : iso (W₁ ∪ W₂) σ G x y = iso W₁ σ G x y ∩ {g | Matches W₂ g x y} := by
  ext g
  simp only [iso, Set.mem_inter_iff, Set.mem_ofPred_eq, matches_union, and_assoc]

/-- **Sequential windows.** If the first window has been solved as the coset `τ • H`, then the
union of the windows is solved by the second window inside the updated coset `τ • H`. -/
theorem iso_union_of_eq_smul (h : iso W₁ σ G x y = τ • (H : Set (Perm Ω))) :
    iso (W₁ ∪ W₂) σ G x y = iso W₂ τ H x y := by
  rw [iso_union, h]
  rfl

/-- If the first window has no solution, neither has the union. -/
theorem iso_union_of_eq_empty (h : iso W₁ σ G x y = ∅) : iso (W₁ ∪ W₂) σ G x y = ∅ := by
  rw [iso_union, h, Set.empty_inter]

/-! ### Groups fixing the window pointwise -/

theorem matches_iff_of_fixesPointwise (hG : FixesPointwise G W) (hg : σ⁻¹ * g ∈ G) :
    Matches W g x y ↔ Matches W σ x y := by
  have hgu : ∀ u ∈ W, g u = σ u := fun u hu => by
    have := hG _ hg u hu
    rw [Perm.mul_apply, Perm.inv_eq_iff_eq] at this
    exact this
  simp only [Matches]
  exact ⟨fun h u hu => (hgu u hu) ▸ h u hu, fun h u hu => (hgu u hu).symm ▸ h u hu⟩

/-- If `G` fixes `W` pointwise and the representative matches, every element of the coset
matches. -/
theorem iso_of_fixesPointwise_of_matches (hG : FixesPointwise G W) (hm : Matches W σ x y) :
    iso W σ G x y = σ • (G : Set (Perm Ω)) := by
  ext g
  rw [mem_iso, mem_leftCoset_iff']
  exact ⟨fun h => h.1, fun h => ⟨h, (matches_iff_of_fixesPointwise hG h).2 hm⟩⟩

/-- If `G` fixes `W` pointwise and the representative does not match, nothing matches. -/
theorem iso_of_fixesPointwise_of_not_matches (hG : FixesPointwise G W)
    (hm : ¬ Matches W σ x y) : iso W σ G x y = ∅ := by
  ext g
  simp only [Set.mem_empty_iff_false, iff_false]
  intro h
  rw [mem_iso] at h
  exact hm ((matches_iff_of_fixesPointwise hG h.1).1 h.2)

/-! ### Branching over a subgroup -/

/-- **Branching.** If the cosets `r i • K` (with `K ≤ G`) cover `G`, then the solutions in
`σ • G` are the union of the solutions in the branch cosets `(σ * r i) • K`. Every solution
lies in some branch; no branch introduces a non-solution. -/
theorem iso_eq_iUnion_of_isLeftCover {ι : Type*} {r : ι → Perm Ω} (hr : IsLeftCover G K r)
    (hK : K ≤ G) : iso W σ G x y = ⋃ i, iso W (σ * r i) K x y := by
  ext g
  simp only [iso, Set.mem_iUnion, Set.mem_ofPred_eq, hr.leftCoset_eq_iUnion hK σ]
  exact ⟨fun ⟨⟨i, hi⟩, hm⟩ => ⟨i, hi, hm⟩, fun ⟨i, hi, hm⟩ => ⟨⟨i, hi⟩, hm⟩⟩

end Iso

/-! ### The automorphism subgroup -/

section Aut

variable {W W₁ W₂ : Set Ω} {σ τ g h : Perm Ω} {G H K : Subgroup (Perm Ω)} {x y : Ω → α}

/-- The automorphism subgroup of `x` on the `G`-invariant window `W`: the elements of `G`
preserving `x` at every position of `W`. Invariance of `W` is what makes this a subgroup. -/
def aut (hW : IsInvariant G W) (x : Ω → α) : Subgroup (Perm Ω) where
  carrier := {h | h ∈ G ∧ Matches W h x x}
  one_mem' := ⟨G.one_mem, fun _ _ => rfl⟩
  mul_mem' := by
    rintro h₁ h₂ ⟨hh₁, hm₁⟩ ⟨hh₂, hm₂⟩
    refine ⟨mul_mem hh₁ hh₂, fun u hu => ?_⟩
    rw [Perm.mul_apply]
    exact (hm₂ u hu).trans (hm₁ _ (hW.apply_mem hh₂ hu))
  inv_mem' := by
    rintro h ⟨hh, hm⟩
    refine ⟨inv_mem hh, fun u hu => ?_⟩
    have := hm _ (hW.inv_apply_mem hh hu)
    rw [perm_apply_inv_self] at this
    exact this.symm

theorem mem_aut (hW : IsInvariant G W) : h ∈ aut hW x ↔ h ∈ G ∧ Matches W h x x := Iff.rfl

theorem aut_le (hW : IsInvariant G W) (x : Ω → α) : aut hW x ≤ G := fun _ h => h.1

theorem coe_aut (hW : IsInvariant G W) (x : Ω → α) :
    (aut hW x : Set (Perm Ω)) = iso W 1 G x x := by
  ext h
  rw [mem_iso_one]
  rfl

/-- The window remains invariant under the automorphism subgroup of any invariant window. -/
theorem IsInvariant.aut {V : Set Ω} (hV : IsInvariant G V) (hW : IsInvariant G W)
    (x : Ω → α) : IsInvariant (aut hW x) V :=
  hV.mono (aut_le hW x)

@[simp] theorem aut_empty_window (x : Ω → α) : aut (isInvariant_empty G) x = G := by
  ext h
  simp [mem_aut]

theorem aut_of_fixesPointwise (hG : FixesPointwise G W) (x : Ω → α) :
    aut (isInvariant_of_fixesPointwise hG) x = G := by
  ext h
  rw [mem_aut]
  refine ⟨fun h => h.1, fun hh => ⟨hh, fun u hu => by rw [hG h hh u hu]⟩⟩

/-- **Solution-coset theorem.** If `τ` is a solution, then the solution set is exactly the
left coset of the automorphism subgroup through `τ`. Neither `σ` nor `τ` needs to preserve
`W`. -/
theorem iso_eq_smul_aut (hW : IsInvariant G W) (hτ : τ ∈ iso W σ G x y) :
    iso W σ G x y = τ • (aut hW x : Set (Perm Ω)) := by
  rw [mem_iso] at hτ
  obtain ⟨hστ, hτm⟩ := hτ
  ext g
  rw [mem_iso, mem_leftCoset_iff', mem_aut]
  constructor
  · rintro ⟨hσg, hgm⟩
    have hG : τ⁻¹ * g ∈ G := by
      have : τ⁻¹ * g = (σ⁻¹ * τ)⁻¹ * (σ⁻¹ * g) := by group
      rw [this]
      exact mul_mem (inv_mem hστ) hσg
    refine ⟨hG, fun u hu => ?_⟩
    have hv := hτm _ (hW.apply_mem hG hu)
    rw [Perm.mul_apply, perm_apply_inv_self] at hv
    exact (hgm u hu).trans hv.symm
  · rintro ⟨hG, hm⟩
    refine ⟨?_, fun u hu => ?_⟩
    · have : σ⁻¹ * g = (σ⁻¹ * τ) * (τ⁻¹ * g) := by group
      rw [this]
      exact mul_mem hστ hG
    · have hv := hτm _ (hW.apply_mem hG hu)
      rw [Perm.mul_apply, perm_apply_inv_self] at hv
      exact (hm u hu).trans hv

/-- The solution set is empty or a single left coset of the automorphism subgroup. -/
theorem iso_eq_empty_or_eq_smul_aut (hW : IsInvariant G W) :
    iso W σ G x y = ∅ ∨ ∃ τ ∈ iso W σ G x y, iso W σ G x y = τ • (aut hW x : Set (Perm Ω)) := by
  rcases (iso W σ G x y).eq_empty_or_nonempty with h | ⟨τ, hτ⟩
  · exact Or.inl h
  · exact Or.inr ⟨τ, hτ, iso_eq_smul_aut hW hτ⟩

/-- A solution coset determines its subgroup: if `iso W σ G x y = τ • H` then `H` is the
automorphism subgroup. -/
theorem eq_aut_of_iso_eq_smul (hW : IsInvariant G W) (h : iso W σ G x y = τ • (H : Set (Perm Ω))) :
    H = aut hW x := by
  have hτ : τ ∈ iso W σ G x y := h ▸ self_mem_leftCoset τ H
  have h' := h.symm.trans (iso_eq_smul_aut hW hτ)
  ext k
  have := congrArg (fun S : Set (Perm Ω) => τ * k ∈ S) h'
  simp only [mem_leftCoset_iff', inv_mul_cancel_left, eq_iff_iff] at this
  exact this

/-- **Sequential windows, coset form.** After the first window is solved by `τ`, the union is
solved by the second window inside `τ • aut hW₁ x`; that window is still invariant there. -/
theorem iso_union_eq_iso_aut (hW₁ : IsInvariant G W₁) (hτ : τ ∈ iso W₁ σ G x y) :
    iso (W₁ ∪ W₂) σ G x y = iso W₂ τ (aut hW₁ x) x y :=
  iso_union_of_eq_smul (iso_eq_smul_aut hW₁ hτ)

/-- **Branch reconstruction.** Suppose the solution set is the union of the branch answers
`τ i • H i`, indexed by the nonempty branches. Then for any chosen branch `i₀`, the
automorphism subgroup is generated by the branch subgroups together with the representative
differences `(τ i₀)⁻¹ * τ i`. -/
theorem aut_eq_closure_of_iso_eq_iUnion (hW : IsInvariant G W) {ι : Type*} {τ : ι → Perm Ω}
    {H : ι → Subgroup (Perm Ω)} (hS : iso W σ G x y = ⋃ i, τ i • (H i : Set (Perm Ω)))
    (i₀ : ι) :
    aut hW x = Subgroup.closure ((⋃ i, (H i : Set (Perm Ω))) ∪
      Set.range fun i => (τ i₀)⁻¹ * τ i) := by
  have hτ : τ i₀ ∈ iso W σ G x y := by
    rw [hS]
    exact Set.mem_iUnion.2 ⟨i₀, self_mem_leftCoset _ _⟩
  rw [iso_eq_smul_aut hW hτ] at hS
  exact eq_closure_of_leftCoset_eq_iUnion hS i₀

/-- The reconstructed coset: under the hypotheses of `aut_eq_closure_of_iso_eq_iUnion`, the
solution set is `τ i₀ • ⟨⋃ H i ∪ {(τ i₀)⁻¹ * τ i}⟩`. -/
theorem iso_eq_smul_closure_of_iso_eq_iUnion (hW : IsInvariant G W) {ι : Type*}
    {τ : ι → Perm Ω} {H : ι → Subgroup (Perm Ω)}
    (hS : iso W σ G x y = ⋃ i, τ i • (H i : Set (Perm Ω))) (i₀ : ι) :
    iso W σ G x y = τ i₀ • (Subgroup.closure ((⋃ i, (H i : Set (Perm Ω))) ∪
      Set.range fun i => (τ i₀)⁻¹ * τ i) : Set (Perm Ω)) := by
  have hτ : τ i₀ ∈ iso W σ G x y := by
    rw [hS]
    exact Set.mem_iUnion.2 ⟨i₀, self_mem_leftCoset _ _⟩
  rw [← aut_eq_closure_of_iso_eq_iUnion hW hS i₀]
  exact iso_eq_smul_aut hW hτ

end Aut

/-! ### Semantic answers -/

/-- The semantic form of a solver result: `none`, or a representative and a subgroup. -/
abbrev Answer (Ω : Type*) := Option (Perm Ω × Subgroup (Perm Ω))

/-- The set of permutations denoted by an answer. -/
def Answer.denote : Answer Ω → Set (Perm Ω)
  | none => ∅
  | some (τ, H) => τ • (H : Set (Perm Ω))

@[simp] theorem Answer.denote_none : Answer.denote (none : Answer Ω) = ∅ := rfl

@[simp] theorem Answer.denote_some (τ : Perm Ω) (H : Subgroup (Perm Ω)) :
    Answer.denote (some (τ, H)) = τ • (H : Set (Perm Ω)) := rfl

/-- An answer is correct for the instance when it denotes exactly the solution set. -/
def Answer.IsCorrect (a : Answer Ω) (W : Set Ω) (σ : Perm Ω) (G : Subgroup (Perm Ω))
    (x y : Ω → α) : Prop :=
  a.denote = iso W σ G x y

section Answer

variable {W : Set Ω} {σ τ : Perm Ω} {G H : Subgroup (Perm Ω)} {x y : Ω → α} {a : Answer Ω}

/-- A correct answer is `none` exactly when there is no solution. -/
theorem Answer.IsCorrect.eq_none_iff (ha : Answer.IsCorrect a W σ G x y) :
    a = none ↔ iso W σ G x y = ∅ := by
  unfold Answer.IsCorrect at ha
  rcases a with _ | ⟨τ, H⟩
  · simpa using ha.symm
  · simp only [reduceCtorEq, false_iff]
    rw [← ha, Answer.denote_some]
    exact Set.nonempty_iff_ne_empty.1 ⟨τ, self_mem_leftCoset τ H⟩

/-- A successful correct answer carries a solution and exactly the automorphism subgroup. -/
theorem Answer.IsCorrect.of_some (hW : IsInvariant G W)
    (ha : Answer.IsCorrect (some (τ, H)) W σ G x y) :
    τ ∈ iso W σ G x y ∧ H = aut hW x := by
  unfold Answer.IsCorrect at ha
  rw [Answer.denote_some] at ha
  exact ⟨ha ▸ self_mem_leftCoset τ H, eq_aut_of_iso_eq_smul hW ha.symm⟩

/-- A solution together with the automorphism subgroup is a correct answer. -/
theorem Answer.isCorrect_some_aut (hW : IsInvariant G W) (hτ : τ ∈ iso W σ G x y) :
    Answer.IsCorrect (some (τ, aut hW x)) W σ G x y :=
  (iso_eq_smul_aut hW hτ).symm

theorem Answer.isCorrect_none (h : iso W σ G x y = ∅) :
    Answer.IsCorrect (none : Answer Ω) W σ G x y :=
  h.symm

end Answer

end GraphIso
