module

public import GraphIso.Reductions.Sequential
public import GraphIso.Representation.Group

/-!
# Branching over a subgroup, at the level of answers

Given a left cover `r` of `G` by cosets of `K ≤ G` and correct answers `aᵢ` for the branch
cosets `(σ * r i) • K`, the combined answer `combineBranches` is

* `none` if every branch answer is `none`;
* otherwise `some (τ₀, ⟨⋃ Hᵢ ∪ {τ₀⁻¹ τᵢ}⟩)` where `(τᵢ, Hᵢ)` are the successful branch answers
  and `τ₀` is the first of them.

`Answer.IsCorrect.combineBranches` proves that this is a correct answer for `σ • G`. The
proof uses both the exhaustive branch cover and the solution-coset theorem; generating a
subgroup from an arbitrary union of cosets could overapproximate it.

At the level of represented generators, `branchGens` lists the generators of every `Hᵢ`
followed by the `k - 1` differences `τ₀⁻¹ τᵢ` for `i ≥ 1`. Its length is exactly
`Σ sᵢ + k - 1` (`length_branchGens`), and it generates the reconstructed subgroup
(`denote_branchGens`): the difference `τ₀⁻¹ τ₀ = 1` may be omitted.
-/

@[expose] public section

namespace GraphIso

open Equiv Pointwise

variable {Ω α : Type*}

/-- The successful branch answers, in order. -/
def successes (as : List (Answer Ω)) : List (Perm Ω × Subgroup (Perm Ω)) := as.filterMap id

theorem successes_eq_nil_iff {as : List (Answer Ω)} : successes as = [] ↔ ∀ a ∈ as, a = none := by
  simp [successes, List.filterMap_eq_nil_iff]

/-- The reconstructed subgroup from successful branch answers with chosen first
representative `τ₀`. -/
def branchSubgroup (τ₀ : Perm Ω) (ss : List (Perm Ω × Subgroup (Perm Ω))) :
    Subgroup (Perm Ω) :=
  Subgroup.closure ((⋃ p ∈ ss, (p.2 : Set (Perm Ω))) ∪ {g | ∃ p ∈ ss, g = τ₀⁻¹ * p.1})

/-- Combine branch answers. -/
def combineBranches (as : List (Answer Ω)) : Answer Ω :=
  match successes as with
  | [] => none
  | (τ₀, H₀) :: ss => some (τ₀, branchSubgroup τ₀ ((τ₀, H₀) :: ss))

section

variable {W : Set Ω} {σ : Perm Ω} {G K : Subgroup (Perm Ω)} {x y : Ω → α}

/-- The union of the branch solution sets is the union of the successful branch cosets. -/
theorem iUnion_branches_eq {ι : Type*} {r : ι → Perm Ω} {a : ι → Answer Ω}
    (ha : ∀ i, Answer.IsCorrect (a i) W (σ * r i) K x y) :
    (⋃ i, iso W (σ * r i) K x y) = ⋃ i, (a i).denote := by
  simp only [Answer.IsCorrect] at ha
  simp [ha]

theorem denote_eq_iUnion_successes (as : List (Answer Ω)) :
    (⋃ a ∈ as, Answer.denote a) = ⋃ p ∈ successes as, p.1 • (p.2 : Set (Perm Ω)) := by
  induction as with
  | nil => simp [successes]
  | cons a as ih =>
    rcases a with _ | ⟨τ, H⟩
    · simpa [successes] using ih
    · simp only [successes, List.filterMap_cons, id, List.mem_cons, Set.iUnion_iUnion_eq_or_left,
        Answer.denote_some] at ih ⊢
      rw [ih]

/-- **Branch combination.** If the branch cosets cover `σ • G` (via a left cover of `G` by
cosets of `K ≤ G`) and every branch answer is correct, the combined answer is correct. -/
theorem Answer.IsCorrect.combineBranches (hW : IsInvariant G W) {rs : List (Perm Ω)}
    (hr : IsLeftCover G K fun i : Fin rs.length => rs.get i) (hK : K ≤ G)
    {as : List (Answer Ω)} (hlen : as.length = rs.length)
    (ha : ∀ i : Fin rs.length,
      Answer.IsCorrect (as.get (i.cast hlen.symm)) W (σ * rs.get i) K x y) :
    Answer.IsCorrect (GraphIso.combineBranches as) W σ G x y := by
  have hcover : iso W σ G x y = ⋃ a ∈ as, Answer.denote a := by
    rw [iso_eq_iUnion_of_isLeftCover hr hK, iUnion_branches_eq ha]
    ext g
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨_, List.get_mem _ _, hi⟩
    · rintro ⟨a, ha', hg⟩
      obtain ⟨i, rfl⟩ := List.get_of_mem ha'
      exact ⟨i.cast hlen, by simpa using hg⟩
  rw [denote_eq_iUnion_successes] at hcover
  unfold GraphIso.combineBranches Answer.IsCorrect
  rcases hs : successes as with _ | ⟨⟨τ₀, H₀⟩, ss⟩
  · rw [hs] at hcover
    simpa using hcover.symm
  · rw [hs] at hcover
    simp only [Answer.denote_some]
    -- index the successful branches by `Fin`
    set L := (τ₀, H₀) :: ss with hL
    have hS : iso W σ G x y = ⋃ i : Fin L.length, (L.get i).1 • ((L.get i).2 : Set (Perm Ω)) := by
      rw [hcover]
      ext g
      simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨p, hp, hg⟩
        obtain ⟨i, rfl⟩ := List.get_of_mem hp
        exact ⟨i, hg⟩
      · rintro ⟨i, hg⟩
        exact ⟨_, List.get_mem _ _, hg⟩
    have h0 : (L.get ⟨0, by simp [hL]⟩).1 = τ₀ := rfl
    rw [iso_eq_smul_closure_of_iso_eq_iUnion hW hS ⟨0, by simp [hL]⟩, h0]
    congr 2
    unfold branchSubgroup
    congr 1
    ext g
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_range, Set.mem_ofPred_eq, SetLike.mem_coe,
      exists_prop]
    constructor
    · rintro (⟨p, hp, hg⟩ | ⟨p, hp, rfl⟩)
      · obtain ⟨i, rfl⟩ := List.get_of_mem hp
        exact Or.inl ⟨i, hg⟩
      · obtain ⟨i, rfl⟩ := List.get_of_mem hp
        exact Or.inr ⟨i, rfl⟩
    · rintro (⟨i, hg⟩ | ⟨i, rfl⟩)
      · exact Or.inl ⟨_, List.get_mem _ _, hg⟩
      · exact Or.inr ⟨_, List.get_mem _ _, rfl⟩

end

/-! ### Represented generators of the reconstructed subgroup -/

/-- The generators of the reconstructed subgroup from represented branch answers: all branch
generators, followed by the differences `τ₀⁻¹ τᵢ` for the branches after the first. -/
def branchGens (τ₀inv : PermData) (ss : List (PermData × GensData)) : GensData :=
  (ss.map Prod.snd).flatten ++ (ss.drop 1).map fun p => PermData.mul τ₀inv p.1

/-- `s_out = Σ sᵢ + k - 1` for `k` successful branches. -/
theorem length_branchGens (τ₀inv : PermData) (ss : List (PermData × GensData)) :
    (branchGens τ₀inv ss).length = (ss.map fun p => p.2.length).sum + (ss.length - 1) := by
  simp [branchGens, List.length_flatten, Function.comp_def]

theorem allValid_branchGens {n : ℕ} {τ₀inv : PermData} (hτ : τ₀inv.Valid n)
    {ss : List (PermData × GensData)}
    (hss : ∀ p ∈ ss, p.1.Valid n ∧ GensData.AllValid n p.2) :
    GensData.AllValid n (branchGens τ₀inv ss) := by
  intro g hg
  rcases List.mem_append.1 hg with hg | hg
  · obtain ⟨gs, hgs, hg⟩ := List.mem_flatten.1 hg
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hgs
    exact (hss p hp).2 g hg
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hg
    exact hτ.mul (hss p (List.mem_of_mem_drop hp)).1

/-- The represented generators generate the reconstructed subgroup. -/
theorem denote_branchGens {n : ℕ} {τ₀ : PermData} {H₀ : GensData} {ss : List (PermData × GensData)}
    (hτ : τ₀.Valid n) (hss : ∀ p ∈ (τ₀, H₀) :: ss, p.1.Valid n ∧ GensData.AllValid n p.2) :
    GensData.denote n (branchGens τ₀.inv ((τ₀, H₀) :: ss)) =
      branchSubgroup (τ₀.denote n)
        (((τ₀, H₀) :: ss).map fun p => (p.1.denote n, GensData.denote n p.2)) := by
  apply le_antisymm
  · rw [GensData.denote_le_iff]
    intro g hg
    rcases List.mem_append.1 hg with hg | hg
    · obtain ⟨gs, hgs, hg⟩ := List.mem_flatten.1 hg
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hgs
      refine Subgroup.subset_closure (Or.inl ?_)
      simp only [Set.mem_iUnion, List.mem_map, SetLike.mem_coe]
      exact ⟨_, ⟨p, hp, rfl⟩, GensData.mem_denote_of_mem hg⟩
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hg
      have hp' : p ∈ (τ₀, H₀) :: ss := List.mem_cons_of_mem _ (List.mem_of_mem_drop hp)
      refine Subgroup.subset_closure (Or.inr ⟨_, List.mem_map.2 ⟨p, hp', rfl⟩, ?_⟩)
      rw [PermData.denote_mul hτ.inv (hss p hp').1, PermData.denote_inv hτ]
  · unfold branchSubgroup
    rw [Subgroup.closure_le]
    rintro g (hg | ⟨q, hq, rfl⟩)
    · simp only [Set.mem_iUnion, List.mem_map] at hg
      obtain ⟨_, ⟨p, hp, rfl⟩, hg⟩ := hg
      refine (GensData.denote_le_iff.2 fun h hh => ?_) hg
      refine GensData.mem_denote_of_mem (List.mem_append_left _ ?_)
      exact List.mem_flatten.2 ⟨p.2, List.mem_map.2 ⟨p, hp, rfl⟩, hh⟩
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
      rcases List.mem_cons.1 hp with rfl | hp
      · simp only [inv_mul_cancel]
        exact one_mem _
      · have := GensData.mem_denote_of_mem (n := n) (gs := branchGens τ₀.inv ((τ₀, H₀) :: ss))
          (g := PermData.mul τ₀.inv p.1) (List.mem_append_right _ (by
            simp only [List.drop_succ_cons, List.drop_zero]
            exact List.mem_map.2 ⟨p, hp, rfl⟩))
        rwa [PermData.denote_mul hτ.inv (hss p (List.mem_cons_of_mem _ hp)).1,
          PermData.denote_inv hτ] at this

end GraphIso
