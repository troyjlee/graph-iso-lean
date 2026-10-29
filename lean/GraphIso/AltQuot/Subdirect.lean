module

public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Data.Fintype.Lattice
public import Mathlib.Data.Fintype.EquivFin

/-!
# Simple quotients of subdirect products

**Babai, Lemma 8.1.1** (proof by P. P. Pálfy): let `M i` (`i` in a finite index type) be normal
subgroups of `G` with trivial intersection — the kernels of the projections of a subdirect
product — and `φ : G → S` an epimorphism onto a nonabelian simple group. Then some `M i` lies in
`ker φ`, so `φ` factors through the `i`-th projection (`exists_le_ker_of_simple`).

Proof: otherwise every `φ(M i)` is a nontrivial normal subgroup of `S`, hence `S`. Since
`⁅A, B⁆ ≤ A ⊓ B` for normal `A`, `B`, and `⁅S, S⁆ = S` (`S` is nonabelian simple), the image of
the intersection of any finite set of the `M i` is `S`; for all of them this is `φ(⊥) = ⊥`.
-/

@[expose] public section

namespace GraphIso.AltQuot

/-- A nonabelian simple group is perfect. -/
theorem commutator_top_eq_top_of_simple {S : Type*} [Group S] [IsSimpleGroup S]
    (hS : ∃ a b : S, a * b ≠ b * a) : ⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hS
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h
    exact hab (Subgroup.mem_centralizer_iff.1 (h (Subgroup.mem_top b)) a
      (Subgroup.mem_top a))
  · exact h

/-- **Simple quotient of a subdirect product** (Babai, Lemma 8.1.1). -/
theorem exists_le_ker_of_simple {G S : Type*} [Group G] [Group S] [IsSimpleGroup S]
    (hS : ∃ a b : S, a * b ≠ b * a) {ι : Type*} [Finite ι] (M : ι → Subgroup G)
    (hM : ∀ i, (M i).Normal) (hinf : ⨅ i, M i = ⊥) (φ : G →* S)
    (hφ : Function.Surjective φ) : ∃ i, M i ≤ φ.ker := by
  classical
  have := Fintype.ofFinite ι
  by_contra hcon
  push Not at hcon
  -- every `φ (M i)` is a nontrivial normal subgroup of `S`, hence `S`
  have htop : ∀ i, (M i).map φ = ⊤ := by
    intro i
    have hn : ((M i).map φ).Normal := (hM i).map φ hφ
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((M i).map φ) with h | h
    · exact absurd ((Subgroup.map_eq_bot_iff _).1 h) (hcon i)
    · exact h
  have hperf := commutator_top_eq_top_of_simple hS
  -- the images of finite intersections are `S`
  have key : ∀ s : Finset ι, (s.inf M).Normal ∧ (s.inf M).map φ = ⊤ := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨?_, ?_⟩
      · rw [Finset.inf_empty]
        infer_instance
      · rw [Finset.inf_empty, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top]
        exact hφ
    | insert a s ha ih =>
      obtain ⟨hn, hs⟩ := ih
      rw [Finset.inf_insert]
      have hna := hM a
      refine ⟨inferInstance, ?_⟩
      refine eq_top_iff.2 ?_
      calc (⊤ : Subgroup S) = ⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ := hperf.symm
        _ = ⁅(M a).map φ, (s.inf M).map φ⁆ := by rw [htop a, hs]
        _ = ⁅M a, s.inf M⁆.map φ := (Subgroup.map_commutator _ _ _).symm
        _ ≤ (M a ⊓ s.inf M).map φ := Subgroup.map_mono (Subgroup.commutator_le_inf _ _)
  have h := (key Finset.univ).2
  rw [Finset.inf_univ_eq_iInf, hinf, Subgroup.map_bot] at h
  obtain ⟨a, b, hab⟩ := hS
  have ha : a ∈ (⊥ : Subgroup S) := h ▸ Subgroup.mem_top a
  have hb : b ∈ (⊥ : Subgroup S) := h ▸ Subgroup.mem_top b
  rw [Subgroup.mem_bot] at ha hb
  exact hab (by rw [ha, hb])

end GraphIso.AltQuot
