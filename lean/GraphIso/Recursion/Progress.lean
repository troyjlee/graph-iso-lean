module

public import GraphIso.SplitJohnson.Output
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Progress lemmas

How a canonical structure on the base forces progress (`PLAN-14.md` §2.2, §5 item 4). Let
`P ≤ Sym(Γ)` preserve the structure and let `O` be a `P`-orbit inside `V`.

* `colPart_orbit`: for a colored `t`-partition of `V` (milestone 11's `IsColPart`), either
  `|O| ≤ t`, or `2|O| ≤ |V|`, or the blocks cut `O` into a `P`-invariant partition with at least
  two parts of at least two points each. In the last case the block coarsening (M2a, M2b) halves
  the base.
* `johnson_orbit`: for a Johnson structure (`IsJohnson`), either `O ⊆ V₀`, where the Johnson
  union applies, or `O` misses `V₀` and has fewer than `|V| - t` points.
-/

@[expose] public section

namespace GraphIso.Recursion

open Equiv Pointwise GraphIso.SplitJohnson

variable {Γ : Type*} [DecidableEq Γ] {P : Subgroup (Perm Γ)} {V O : Finset Γ} {t : ℕ}

omit [DecidableEq Γ] in
/-- A permutation mapping a finite set into itself maps it onto itself. -/
private theorem smul_finset_eq_of_mapsTo [DecidableEq Γ] {σ : Perm Γ} {O : Finset Γ}
    (h : ∀ γ ∈ O, σ γ ∈ O) : σ • O = O := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_smul_finset.1 hx
    exact h y hy
  · rw [Finset.card_smul_finset]

/-- **Orbits under a colored partition.** -/
theorem colPart_orbit {p : CPart Γ} (hp : IsColPart V t p)
    (hP : ∀ σ ∈ P, ∀ γ ∈ V, p.col (σ γ) = p.col γ ∧ p.blk (σ γ) = σ • p.blk γ)
    (hO : O ⊆ V) (hOinv : ∀ σ ∈ P, ∀ γ ∈ O, σ γ ∈ O)
    (hOtr : ∀ γ ∈ O, ∀ δ ∈ O, ∃ σ ∈ P, σ γ = δ) (hO2 : 2 ≤ O.card) :
    O.card ≤ t ∨ 2 * O.card ≤ V.card ∨
      (2 ≤ (O.image fun γ => p.blk γ ∩ O).card ∧
        (∀ B ∈ O.image (fun γ => p.blk γ ∩ O), 2 ≤ B.card) ∧
        ∀ σ ∈ P, ∀ B ∈ O.image (fun γ => p.blk γ ∩ O), σ • B ∈ O.image fun γ => p.blk γ ∩ O) := by
  -- the parts move with `P`
  have hpart : ∀ σ ∈ P, ∀ γ ∈ O, p.blk (σ γ) ∩ O = σ • (p.blk γ ∩ O) := by
    intro σ hσ γ hγ
    rw [(hP σ hσ γ (hO hγ)).2, Finset.smul_finset_inter,
      smul_finset_eq_of_mapsTo (hOinv σ hσ)]
  -- all parts have the same size
  have hcard : ∀ γ ∈ O, ∀ δ ∈ O, (p.blk γ ∩ O).card = (p.blk δ ∩ O).card := by
    intro γ hγ δ hδ
    obtain ⟨σ, hσ, rfl⟩ := hOtr γ hγ δ hδ
    rw [hpart σ hσ γ hγ, Finset.card_smul_finset]
  have hmem : ∀ γ ∈ O, γ ∈ p.blk γ ∩ O := fun γ hγ =>
    Finset.mem_inter.2 ⟨hp.mem_blk γ (hO hγ), hγ⟩
  obtain ⟨γ₀, hγ₀⟩ : O.Nonempty := Finset.card_pos.1 (by omega)
  have hk1 : 1 ≤ (p.blk γ₀ ∩ O).card := Finset.card_pos.2 ⟨γ₀, hmem γ₀ hγ₀⟩
  have hkO : (p.blk γ₀ ∩ O).card ≤ O.card := Finset.card_le_card Finset.inter_subset_right
  rcases Nat.lt_or_ge (p.blk γ₀ ∩ O).card O.card with hlt | hge
  · rcases Nat.lt_or_ge 1 (p.blk γ₀ ∩ O).card with hk2 | hk1'
    · -- parts of at least two points, at least two parts
      right; right
      refine ⟨?_, ?_, ?_⟩
      · by_contra hlt2
        have hle : (O.image fun γ => p.blk γ ∩ O).card ≤ 1 := by omega
        rw [Finset.card_le_one] at hle
        have hsub : O ⊆ p.blk γ₀ ∩ O := by
          intro δ hδ
          have := hle _ (Finset.mem_image_of_mem _ hδ) _ (Finset.mem_image_of_mem _ hγ₀)
          rw [← this]
          exact hmem δ hδ
        have := Finset.card_le_card hsub
        omega
      · intro B hB
        obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.1 hB
        rw [hcard δ hδ γ₀ hγ₀]
        omega
      · intro σ hσ B hB
        obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.1 hB
        rw [← hpart σ hσ δ hδ]
        exact Finset.mem_image_of_mem _ (hOinv σ hσ δ hδ)
    · -- singleton parts: `O` meets distinct blocks of size at least two
      right; left
      have hone : ∀ δ ∈ O, (p.blk δ ∩ O).card = 1 := fun δ hδ => by
        rw [hcard δ hδ γ₀ hγ₀]
        omega
      have hcol : ∀ δ ∈ O, p.col δ = p.col γ₀ := by
        intro δ hδ
        obtain ⟨σ, hσ, rfl⟩ := hOtr γ₀ hγ₀ δ hδ
        exact (hP σ hσ γ₀ (hO hγ₀)).1
      have hb2 : ∀ δ ∈ O, 2 ≤ (p.blk δ).card := by
        intro δ hδ
        have hb : (p.blk δ).card = (p.blk γ₀).card :=
          hp.card_eq δ (hO hδ) γ₀ (hO hγ₀) (hcol δ hδ)
        have hpos : 1 ≤ (p.blk δ).card := Finset.card_pos.2 ⟨δ, hp.mem_blk δ (hO hδ)⟩
        by_contra h1
        have hb1 : (p.blk δ).card = 1 := by omega
        obtain ⟨ε, hε, hne⟩ := Finset.exists_mem_ne hO2 δ
        exact hne (hp.admissible δ (hO hδ) hb1 ε (hO hε) ((hcol ε hε).trans (hcol δ hδ).symm))
      have hdisj : ∀ δ ∈ O, ∀ ε ∈ O, δ ≠ ε → Disjoint (p.blk δ) (p.blk ε) := by
        intro δ hδ ε hε hne
        rw [Finset.disjoint_left]
        intro w hwδ hwε
        have h1 := hp.blk_eq δ (hO hδ) w hwδ
        have h2 := hp.blk_eq ε (hO hε) w hwε
        have heq : p.blk δ = p.blk ε := h1.symm.trans h2
        have hle : (p.blk δ ∩ O).card ≤ 1 := (hone δ hδ).le
        rw [Finset.card_le_one] at hle
        have hεδ : ε ∈ p.blk δ ∩ O := by rw [heq]; exact hmem ε hε
        exact hne (hle δ (hmem δ hδ) ε hεδ)
      have hsum : 2 * O.card ≤ (O.biUnion fun δ => p.blk δ).card := by
        rw [Finset.card_biUnion fun δ hδ ε hε hne =>
          hdisj δ (Finset.mem_coe.1 hδ) ε (Finset.mem_coe.1 hε) hne]
        calc 2 * O.card = ∑ _δ ∈ O, 2 := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
          _ ≤ ∑ δ ∈ O, (p.blk δ).card := Finset.sum_le_sum hb2
      have hsub : (O.biUnion fun δ => p.blk δ) ⊆ V := by
        intro w hw
        obtain ⟨δ, hδ, hwδ⟩ := Finset.mem_biUnion.1 hw
        exact hp.blk_sub δ (hO hδ) hwδ
      exact hsum.trans (Finset.card_le_card hsub)
  · -- a single part: `O` lies in one block
    left
    have hsub : O ⊆ p.blk γ₀ := by
      have heq : p.blk γ₀ ∩ O = O :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_right hge
      intro δ hδ
      rw [← heq] at hδ
      exact (Finset.mem_inter.1 hδ).1
    exact (Finset.card_le_card hsub).trans (hp.card_le γ₀ (hO hγ₀))

/-- **Orbits under a Johnson structure.** -/
theorem johnson_orbit {J : JEmb Γ} (hJ : IsJohnson V t J) (hP : ∀ σ ∈ P, σ • J = J)
    (hO : O ⊆ V) (hOtr : ∀ γ ∈ O, ∀ δ ∈ O, ∃ σ ∈ P, σ γ = δ) :
    O ⊆ J.V0 ∨ (Disjoint O J.V0 ∧ O.card + t < V.card) := by
  have hV0 : ∀ σ ∈ P, ∀ γ ∈ J.V0, σ γ ∈ J.V0 := by
    intro σ hσ γ hγ
    have h := congrArg JEmb.V0 (hP σ hσ)
    rw [JEmb.smul_V0] at h
    rw [← h]
    exact Finset.smul_mem_smul_finset hγ
  by_cases h : ∃ γ ∈ O, γ ∈ J.V0
  · obtain ⟨γ, hγO, hγV⟩ := h
    left
    intro δ hδ
    obtain ⟨σ, hσ, rfl⟩ := hOtr γ hγO δ hδ
    exact hV0 σ hσ γ hγV
  · push Not at h
    right
    refine ⟨Finset.disjoint_left.2 h, ?_⟩
    have hsub : O ⊆ V \ J.V0 := fun γ hγ => Finset.mem_sdiff.2 ⟨hO hγ, h γ hγ⟩
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_sdiff_of_subset hJ.sub] at h1
    have h2 := hJ.card_gt
    have h3 := Finset.card_le_card hJ.sub
    omega

end GraphIso.Recursion
