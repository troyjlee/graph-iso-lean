module

public import GraphIso.Certificates.Cases
public import Mathlib.GroupTheory.GroupAction.SubMulAction.Combination
public import GraphIso.Coherent.WLOn
public import GraphIso.SplitJohnson.DLAux
public import GraphIso.SplitJohnson.CoherentSpec
public import GraphIso.SplitJohnson.Main

/-!
# Primitive quotients

Group theory for the macro-steps on a primitive action (`PLAN-14.md` §2.2, §5 item 3).

* `alt_le_iff`: a permutation group contains `Alt(Γ)` exactly when it is
  `(|Γ| - 2)`-transitive. This is the giant test.
* `exists_smul_eq_of_alt_le`: a group containing `Alt(Γ)` (`|Γ| ≥ 3`) is transitive on the
  subsets of each size. In the giant macro-step the labels are therefore all `t`-subsets.
* `exists_blockStab_smul_eq`: the setwise stabilizer of a block of a transitive group is
  transitive on the block (macro-step M2b).
* `orbital_uniprimitive`: the orbital configuration of a primitive group that is not doubly
  transitive is a classical coherent configuration that is uniprimitive. These are the
  hypotheses of `split_or_johnson` (milestone 11) for macro-step M4, where the configuration
  depends on the group alone and is fixed by it exactly.
* **A configuration with canonical colour names** (Case 2b). There the group depends on the
  string, and isomorphisms may permute numbered orbitals. So one orbital `R` is chosen (the
  orbital of a chosen pair). Its pairs are coloured `0` (diagonal), `1` (in `R`) or `2`, and
  2-ary Weisfeiler–Leman refines the colouring (`wlRel`). The refinement:
  - is natural under bijections, colour names included (`wlRel_natural`);
  - is a classical coherent configuration, homogeneous, not a clique, and invariant under the
    group (`wlRel_spec`);
  - is uniprimitive when the group is primitive (`wlRel_uniprimitive`).
  The step branches on the **configuration**, not on the action
  (`wlRel_split_or_uniprimitive`, Babai's Split-or-UPCC test). Either some colour graph is
  disconnected, and the components of the least such colour form a colored
  `⌊|Φ|/2⌋`-partition (milestone 11's `isColPart_comp`), or the refinement is uniprimitive
  and Split-or-Johnson applies. An imprimitive action may still give a primitive refinement:
  round 2 of the audit found one on `(ℤ/4ℤ)²` (finding F3).
-/

@[expose] public section

namespace GraphIso.Recursion

open Equiv MulAction Pointwise GraphIso.Coherent

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ]

/-- **The giant test**: `Alt(Γ) ≤ P` exactly when `P` is `(|Γ| - 2)`-transitive. -/
theorem alt_le_iff (P : Subgroup (Perm Γ)) :
    alternatingGroup Γ ≤ P ↔ IsMultiplyPretransitive P Γ (Fintype.card Γ - 2) := by
  constructor
  · intro h
    have hA := alternatingGroup.isMultiplyPretransitive Γ
    rw [Nat.card_eq_fintype_card] at hA
    refine ⟨fun x y => ?_⟩
    obtain ⟨a, ha⟩ := hA.exists_smul_eq x y
    exact ⟨⟨a, h a.2⟩, ha⟩
  · intro h
    apply IsMultiplyPretransitive.alternatingGroup_le
    rwa [Nat.card_eq_fintype_card]

/-- A group containing `Alt(Γ)`, `|Γ| ≥ 3`, is transitive on the subsets of each size. -/
theorem exists_smul_eq_of_alt_le {P : Subgroup (Perm Γ)} (hP : alternatingGroup Γ ≤ P)
    (h3 : 3 ≤ Fintype.card Γ) {T T' : Finset Γ} (hT : T.card = T'.card) :
    ∃ p ∈ P, p • T = T' := by
  have hA := Set.powersetCard.isPretransitive_alternatingGroup (α := Γ) (n := T.card)
    (by rw [Nat.card_eq_fintype_card]; exact h3)
  obtain ⟨a, ha⟩ := hA.exists_smul_eq (⟨T, rfl⟩ : Set.powersetCard Γ T.card) ⟨T', hT.symm⟩
  refine ⟨a, hP a.2, ?_⟩
  have := congrArg Subtype.val ha
  simpa [Subgroup.smul_def] using this

omit [Fintype Γ] in
/-- **The stabilizer of a block is transitive on it**: if `P` is transitive on `Γ` and `B` is a
block (each translate is `B` or disjoint from it), then for `γ, δ ∈ B` some `p ∈ P` maps `B` to
itself and `γ` to `δ`. -/
theorem exists_blockStab_smul_eq {P : Subgroup (Perm Γ)} (htr : ∀ γ δ : Γ, ∃ p ∈ P, p γ = δ)
    {B : Finset Γ} (hB : ∀ p ∈ P, p • B = B ∨ Disjoint (p • B) B) {γ δ : Γ} (hγ : γ ∈ B)
    (hδ : δ ∈ B) : ∃ p ∈ P, p • B = B ∧ p γ = δ := by
  obtain ⟨p, hp, hpγ⟩ := htr γ δ
  refine ⟨p, hp, ?_, hpγ⟩
  rcases hB p hp with h | h
  · exact h
  · exfalso
    have hmem : p • γ ∈ p • B := Finset.smul_mem_smul_finset hγ
    rw [Perm.smul_def, hpγ] at hmem
    exact Finset.disjoint_left.mp h hmem hδ

/-- **Orbital configurations of uniprimitive groups.** If `P` is primitive and not doubly
transitive on `Φ`, its orbital configuration `c` (colours of pairs are equal
exactly on the orbits of `P` on pairs) is a classical coherent configuration that is
uniprimitive: homogeneous, every off-diagonal colour graph connected, not a clique. -/
theorem orbital_uniprimitive {Φ : Type} [Fintype Φ] [DecidableEq Φ] {P : Type*} [Group P]
    [MulAction P Φ] [IsPreprimitive P Φ] (h₂ : ¬ IsMultiplyPretransitive P Φ 2)
    (c : Φ → Φ → ℕ)
    (hc : ∀ u v u' v', c u v = c u' v' ↔ ∃ g : P, g • u = u' ∧ g • v = v') :
    IsCoherent2 c ∧ IsUniprimitive Finset.univ c := by
  -- the colours are the orbitals: `P` preserves them
  have hg : ∀ (g : P) (u v : Φ), c (g • u) (g • v) = c u v :=
    fun g u v => ((hc u v _ _).mpr ⟨g, rfl, rfl⟩).symm
  obtain ⟨-, hhom, hcl⟩ := GraphIso.Certificates.orbital_config h₂ c hc
  refine ⟨⟨fun x y x' y' hxy => ?_, fun x y x' y' hxy r s => ?_⟩, ⟨hhom, ?_⟩, hcl⟩
  · obtain ⟨g, hx, hy⟩ := (hc x y x' y').mp hxy
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← hx, ← hy, smul_left_cancel_iff]
    · exact (hc _ _ _ _).mpr ⟨g, hy, hx⟩
    · exact (hc _ _ _ _).mpr ⟨g, hx, hx⟩
    · exact (hc _ _ _ _).mpr ⟨g, hy, hy⟩
  · -- `g` maps the points counted for `(x, y)` to those counted for `(x', y')`
    obtain ⟨g, hx, hy⟩ := (hc x y x' y').mp hxy
    refine Finset.card_nbij' (fun z => g • z) (fun z => g⁻¹ • z) (fun z hz => ?_)
      (fun z hz => ?_) (fun z _ => inv_smul_smul g z) (fun z _ => smul_inv_smul g z)
    · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hz ⊢
      rw [← hx, ← hy, hg, hg]
      exact hz
    · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hz ⊢
      rw [← hg g, ← hg g _ y, smul_inv_smul, hx, hy]
      exact hz
  · -- every off-diagonal colour graph is connected
    intro r hr x _ y _
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hr
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at hab
    set R := Relation.ReflTransGen (Adj Finset.univ c (c a b)) with hR
    have hsymm : ∀ {u v : Φ}, R u v → R v u := by
      intro u v huv
      induction huv with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ hvw ih => exact Relation.ReflTransGen.head ⟨hvw.2.1, hvw.1, hvw.2.2.symm⟩ ih
    -- `R` is preserved by `P`
    have hinv : ∀ (g : P) {u v : Φ}, R u v → R (g • u) (g • v) := by
      intro g u v huv
      induction huv with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ hvw ih =>
        refine ih.tail ⟨Finset.mem_univ _, Finset.mem_univ _, ?_⟩
        rw [hg, hg]
        exact hvw.2.2
    -- the class of `a` is a block
    have hblock : IsBlock P {z | R a z} := by
      have hsmul : ∀ g : P, g • {z | R a z} = {z | R (g • a) z} := by
        intro g
        ext z
        rw [Set.mem_smul_set_iff_inv_smul_mem]
        constructor
        · intro hz
          have := hinv g hz
          rwa [smul_inv_smul] at this
        · intro hz
          have := hinv g⁻¹ hz
          rwa [inv_smul_smul] at this
      intro g₁ g₂ hne
      rw [hsmul, hsmul] at hne ⊢
      refine Set.disjoint_left.mpr fun z hz₁ hz₂ => hne ?_
      ext w
      constructor
      · intro hw
        exact (hz₂.trans (hsymm hz₁)).trans hw
      · intro hw
        exact (hz₁.trans (hsymm hz₂)).trans hw
    have hab' : R a b :=
      Relation.ReflTransGen.single ⟨Finset.mem_univ _, Finset.mem_univ _, Or.inl rfl⟩
    rcases IsPreprimitive.isTrivialBlock_of_isBlock hblock with hsub | huniv
    · exact absurd (hsub (Relation.ReflTransGen.refl : R a a) hab') hab
    · have hxa : R a x := by
        have : x ∈ {z | R a z} := by rw [huniv]; exact Set.mem_univ x
        exact this
      have hya : R a y := by
        have : y ∈ {z | R a z} := by rw [huniv]; exact Set.mem_univ y
        exact this
      exact (hsymm hxa).trans hya

/-! ### A configuration with canonical colour names -/

section WLRel

variable {Φ : Type*} [Fintype Φ] [DecidableEq Φ]

/-- The colouring of pairs by a relation: `0` on the diagonal, `1` on `R`, `2` elsewhere. -/
def relCol (R : Φ → Φ → Prop) [DecidableRel R] (u v : Φ) : ℕ :=
  if u = v then 0 else if R u v then 1 else 2

/-- The 2-ary Weisfeiler–Leman refinement of `relCol R`. -/
def wlRel (R : Φ → Φ → Prop) [DecidableRel R] (u v : Φ) : ℕ :=
  wlOn 2 (fun x : Fin 2 → Φ => relCol R (x 0) (x 1)) ![u, v]

omit [Fintype Φ] in
/-- A bijection carrying `R` to `R'` carries `relCol R` to `relCol R'`. -/
theorem relCol_equiv {Φ' : Type*} [DecidableEq Φ'] (e : Φ ≃ Φ') (R : Φ → Φ → Prop)
    [DecidableRel R] (R' : Φ' → Φ' → Prop) [DecidableRel R']
    (hR : ∀ u v, R' (e u) (e v) ↔ R u v) (u v : Φ) : relCol R' (e u) (e v) = relCol R u v := by
  unfold relCol
  by_cases huv : u = v
  · simp [huv]
  · have : e u ≠ e v := fun h => huv (e.injective h)
    simp only [this, huv, ite_false, hR]

/-- **Naturality, colour names included**: a bijection carrying `R` to `R'` carries
`wlRel R` to `wlRel R'`. -/
theorem wlRel_natural {Φ' : Type*} [Fintype Φ'] [DecidableEq Φ'] (e : Φ ≃ Φ')
    (R : Φ → Φ → Prop) [DecidableRel R] (R' : Φ' → Φ' → Prop) [DecidableRel R']
    (hR : ∀ u v, R' (e u) (e v) ↔ R u v) (u v : Φ) : wlRel R' (e u) (e v) = wlRel R u v := by
  have hc : (fun x : Fin 2 → Φ => relCol R' ((⇑e ∘ x) 0) ((⇑e ∘ x) 1)) =
      fun x => relCol R (x 0) (x 1) := by
    funext x
    exact relCol_equiv e R R' hR (x 0) (x 1)
  have hnat := wlOn_natural (k := 2) e (fun x : Fin 2 → Φ' => relCol R' (x 0) (x 1))
  rw [hc] at hnat
  unfold wlRel
  rw [hnat]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- **The refinement of an orbital.** For a transitive group that is not doubly transitive
and `R` the orbital of a pair of distinct points, `wlRel R` is a classical coherent
configuration that is homogeneous, not a clique, and invariant under the group. -/
theorem wlRel_spec {P : Type*} [Group P] [MulAction P Φ] [IsPretransitive P Φ]
    (h₂ : ¬ IsMultiplyPretransitive P Φ 2) {a b : Φ} (hab : a ≠ b) (R : Φ → Φ → Prop)
    [DecidableRel R] (hR : ∀ u v, R u v ↔ ∃ g : P, g • a = u ∧ g • b = v) :
    IsCoherent2 (wlRel R) ∧ IsHomog Finset.univ (wlRel R) ∧ ¬ IsClique (wlRel R) Finset.univ ∧
      ∀ (g : P) (u v : Φ), wlRel R (g • u) (g • v) = wlRel R u v := by
  -- `R` is an orbital, so it is invariant
  have hRg : ∀ (g : P) (u v : Φ), R (g • u) (g • v) ↔ R u v := by
    intro g u v
    rw [hR, hR]
    constructor
    · rintro ⟨h, hu, hv⟩
      exact ⟨g⁻¹ * h, by rw [mul_smul, hu, inv_smul_smul],
        by rw [mul_smul, hv, inv_smul_smul]⟩
    · rintro ⟨h, hu, hv⟩
      exact ⟨g * h, by rw [mul_smul, hu], by rw [mul_smul, hv]⟩
  have hinv : ∀ (g : P) (u v : Φ), wlRel R (g • u) (g • v) = wlRel R u v :=
    fun g u v => wlRel_natural (MulAction.toPerm g) R R (fun u v => hRg g u v) u v
  refine ⟨?_, ?_, ?_, hinv⟩
  · exact GraphIso.SplitJohnson.isCoherent2_pair (wlOn_isCoherent _)
  · intro x _ y _
    obtain ⟨g, hg⟩ := exists_smul_eq P x y
    rw [← hg, hinv]
  · -- some pair of distinct points lies outside `R`
    have hout : ∃ u v : Φ, u ≠ v ∧ ¬ R u v := by
      by_contra hne
      push Not at hne
      apply h₂
      rw [is_two_pretransitive_iff]
      intro x y z w hxy hzw
      obtain ⟨g₁, hg₁a, hg₁b⟩ := (hR x y).mp (hne x y hxy)
      obtain ⟨g₂, hg₂a, hg₂b⟩ := (hR z w).mp (hne z w hzw)
      refine ⟨g₂ * g₁⁻¹, ?_, ?_⟩
      · rw [mul_smul, ← hg₁a, inv_smul_smul, hg₂a]
      · rw [mul_smul, ← hg₁b, inv_smul_smul, hg₂b]
    obtain ⟨u, v, huv, hnR⟩ := hout
    intro hcl
    have heq := hcl a (Finset.mem_univ _) b (Finset.mem_univ _) u (Finset.mem_univ _)
      v (Finset.mem_univ _) hab huv
    have href := wlOn_refines (k := 2) (fun x : Fin 2 → Φ => relCol R (x 0) (x 1)) heq
    have hRab : R a b := (hR a b).mpr ⟨1, one_smul P a, one_smul P b⟩
    simp only [relCol, Matrix.cons_val_zero, Matrix.cons_val_one, hab, huv, ite_false, hRab,
      hnR, ite_true] at href
    exact absurd href (by decide)

/-- A homogeneous colouring of pairs invariant under a primitive group is primitive: every
off-diagonal colour graph is connected, since its reachability classes are blocks. -/
theorem isPrimitive_of_invariant {P : Type*} [Group P] [MulAction P Φ] [IsPreprimitive P Φ]
    (c : Φ → Φ → ℕ) (hg : ∀ (g : P) (u v : Φ), c (g • u) (g • v) = c u v)
    (hhom : IsHomog Finset.univ c) : IsPrimitive Finset.univ c := by
  refine ⟨hhom, ?_⟩
  intro r hr x _ y _
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hr
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at hab
  set R := Relation.ReflTransGen (Adj Finset.univ c (c a b)) with hR
  have hsymm : ∀ {u v : Φ}, R u v → R v u := by
    intro u v huv
    induction huv with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hvw ih => exact Relation.ReflTransGen.head ⟨hvw.2.1, hvw.1, hvw.2.2.symm⟩ ih
  -- `R` is preserved by `P`
  have hinv : ∀ (g : P) {u v : Φ}, R u v → R (g • u) (g • v) := by
    intro g u v huv
    induction huv with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hvw ih =>
      refine ih.tail ⟨Finset.mem_univ _, Finset.mem_univ _, ?_⟩
      rw [hg, hg]
      exact hvw.2.2
  -- the class of `a` is a block
  have hblock : IsBlock P {z | R a z} := by
    have hsmul : ∀ g : P, g • {z | R a z} = {z | R (g • a) z} := by
      intro g
      ext z
      rw [Set.mem_smul_set_iff_inv_smul_mem]
      constructor
      · intro hz
        have := hinv g hz
        rwa [smul_inv_smul] at this
      · intro hz
        have := hinv g⁻¹ hz
        rwa [inv_smul_smul] at this
    intro g₁ g₂ hne
    rw [hsmul, hsmul] at hne ⊢
    refine Set.disjoint_left.mpr fun z hz₁ hz₂ => hne ?_
    ext w
    constructor
    · intro hw
      exact (hz₂.trans (hsymm hz₁)).trans hw
    · intro hw
      exact (hz₁.trans (hsymm hz₂)).trans hw
  have hab' : R a b :=
    Relation.ReflTransGen.single ⟨Finset.mem_univ _, Finset.mem_univ _, Or.inl rfl⟩
  rcases IsPreprimitive.isTrivialBlock_of_isBlock hblock with hsub | huniv
  · exact absurd (hsub (Relation.ReflTransGen.refl : R a a) hab') hab
  · have hxa : R a x := by
      have : x ∈ {z | R a z} := by rw [huniv]; exact Set.mem_univ x
      exact this
    have hya : R a y := by
      have : y ∈ {z | R a z} := by rw [huniv]; exact Set.mem_univ y
      exact this
    exact (hsymm hxa).trans hya

/-- **Uniprimitivity**: for a primitive group the refinement of an orbital is uniprimitive,
the hypothesis of `split_or_johnson`. -/
theorem wlRel_uniprimitive {P : Type*} [Group P] [MulAction P Φ] [IsPreprimitive P Φ]
    (h₂ : ¬ IsMultiplyPretransitive P Φ 2) {a b : Φ} (hab : a ≠ b) (R : Φ → Φ → Prop)
    [DecidableRel R] (hR : ∀ u v, R u v ↔ ∃ g : P, g • a = u ∧ g • b = v) :
    IsUniprimitive Finset.univ (wlRel R) := by
  obtain ⟨-, hhom, hcl, hg⟩ := wlRel_spec h₂ hab R hR
  exact ⟨isPrimitive_of_invariant (wlRel R) hg hhom, hcl⟩

/-- **The exhaustive alternative** (Babai's Split-or-UPCC test, applied to the refinement). For
a transitive, not doubly transitive group and the orbital `R` of a pair of distinct points,
either the least disconnected colour of `wlRel R` exists and its components form a colored
`⌊|Φ|/2⌋`-partition, or `wlRel R` is uniprimitive. -/
theorem wlRel_split_or_uniprimitive {P : Type*} [Group P] [MulAction P Φ]
    [IsPretransitive P Φ] (h₂ : ¬ IsMultiplyPretransitive P Φ 2) {a b : Φ} (hab : a ≠ b)
    (R : Φ → Φ → Prop) [DecidableRel R] (hR : ∀ u v, R u v ↔ ∃ g : P, g • a = u ∧ g • b = v) :
    (∃ h : (GraphIso.SplitJohnson.disconn Finset.univ (wlRel R)).Nonempty,
        GraphIso.SplitJohnson.IsColPart Finset.univ (Fintype.card Φ / 2)
          ⟨fun _ => 0, comp Finset.univ (wlRel R)
            ((GraphIso.SplitJohnson.disconn Finset.univ (wlRel R)).min' h)⟩) ∨
      IsUniprimitive Finset.univ (wlRel R) := by
  obtain ⟨hcoh, hhom, hncl, -⟩ := wlRel_spec h₂ hab R hR
  by_cases h : (GraphIso.SplitJohnson.disconn Finset.univ (wlRel R)).Nonempty
  · refine Or.inl ⟨h, ?_⟩
    have := GraphIso.SplitJohnson.isColPart_comp (GraphIso.SplitJohnson.isCoh2On_univ hcoh) hhom
      ((GraphIso.SplitJohnson.disconn Finset.univ (wlRel R)).min'_mem h)
    rwa [Finset.card_univ] at this
  · refine Or.inr ⟨⟨hhom, fun r hr x _ y _ => ?_⟩, hncl⟩
    have hx : comp Finset.univ (wlRel R) r x = Finset.univ := by
      by_contra hne
      exact h ⟨r, Finset.mem_filter.2 ⟨hr, x, Finset.mem_univ _, hne⟩⟩
    have hy : y ∈ comp Finset.univ (wlRel R) r x := by
      rw [hx]
      exact Finset.mem_univ _
    exact (mem_comp.1 hy).2

end WLRel

end GraphIso.Recursion
