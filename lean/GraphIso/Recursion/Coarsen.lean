module

public import GraphIso.Recursion.Hint
public import GraphIso.SplitJohnson.Output
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Coarsening a hint

The derived hints of the macro-steps (`PLAN-14.md` §2.2, §5 item 2). Each takes a hint
`(Γ, ψ, lab)` and builds a hint on a new base, with labels computed from the old ones.

* **Restriction to an invariant set** (`restrictHom`): a homomorphism into `Perm X` restricts
  to a `ψ`-invariant `S : Finset X`; `setAct ψ` is the induced action on `Finset Γ`.
* **Invariant subsets (M1):** for a `ψ`-invariant `Γ' ⊆ Γ`, the labels `lab ∩ Γ'`
  (`hint_inter`). Of finitely many invariant sets covering `Γ` (for example the orbits), one
  has non-constant intersections (`exists_nonConst_inter`).
* **Block quotient (M2a):** for a block system `Ψ` of a transitive `ψ`, the blocks met by a
  label, or, when it meets every block, the blocks of least intersection (`blockLabel`). If the
  labels are not equidistributed over the blocks this is a hint on `Ψ` (`hint_blockLabel`),
  with no larger labels and at most `|Γ|/2` blocks.
* **Block stabilizer (M2b):** if the labels are equidistributed, then under the preimage of the
  stabilizer of a block `B₀` the labels `lab ∩ B₀` are not constant on any orbit
  (`hint_blockStab`).
* **Johnson union (M4, Align):** for a Johnson structure `J` preserved by `ψ`, the union of the
  `s`-subsets of `Λ` labelling `lab u ∩ V₀` (`jUnion`). Either `lab ∖ V₀` or the union is not
  constant (`hint_jUnion`), or both are constant and every element fixing the cells of the
  union fixes every label (`fix_of_jUnion_const`). `|Λ| (|Λ| - 1) ≤ 2 |V₀|` (`card_cells`).
-/

@[expose] public section

namespace GraphIso.Recursion

open Equiv MulAction Pointwise GraphIso.SplitJohnson

variable {M Ω Γ : Type*} [Group M] [MulAction M Ω] [DecidableEq Γ]

/-! ### Restriction to invariant sets -/

/-- The restriction of `ρ : M →* Perm X` to a `ρ`-invariant finite set `S`. -/
def restrictHom {X : Type*} [DecidableEq X] (ρ : M →* Perm X) (S : Finset X)
    (hS : ∀ g : M, ∀ x ∈ S, ρ g x ∈ S) : M →* Perm ↥S where
  toFun g := (ρ g).subtypePerm fun x => by
    refine ⟨fun hx => ?_, hS g x⟩
    have := hS g⁻¹ _ hx
    rw [map_inv] at this
    simpa using this
  map_one' := by ext; simp
  map_mul' g h := by
    ext x
    show ρ (g * h) x = ρ g (ρ h x)
    rw [map_mul, Perm.mul_apply]

theorem restrictHom_apply {X : Type*} [DecidableEq X] (ρ : M →* Perm X) (S : Finset X)
    (hS : ∀ g : M, ∀ x ∈ S, ρ g x ∈ S) (g : M) (x : ↥S) :
    ((restrictHom ρ S hS g x : ↥S) : X) = ρ g x := rfl

/-- The action on finite sets of points induced by `ψ`. -/
def setAct (ψ : M →* Perm Γ) : M →* Perm (Finset Γ) :=
  (MulAction.toPermHom (Perm Γ) (Finset Γ)).comp ψ

theorem setAct_apply (ψ : M →* Perm Γ) (g : M) (T : Finset Γ) : setAct ψ g T = ψ g • T := rfl

/-- The labels seen inside an invariant set `S`, as a subset of `↥S`. -/
def subLab {X : Type*} [DecidableEq X] (S : Finset X) (L : Finset X) : Finset ↥S :=
  L.subtype (· ∈ S)

theorem card_subLab_le {X : Type*} [DecidableEq X] (S L : Finset X) :
    (subLab S L).card ≤ L.card := by
  rw [subLab, Finset.card_subtype]
  exact Finset.card_filter_le _ _

theorem mem_subLab {X : Type*} [DecidableEq X] {S L : Finset X} {x : ↥S} :
    x ∈ subLab S L ↔ (x : X) ∈ L := by
  simp [subLab]

/-- `subLab` sees exactly the intersection with `S`. -/
theorem subLab_eq_iff {X : Type*} [DecidableEq X] {S A B : Finset X} :
    subLab S A = subLab S B ↔ A ∩ S = B ∩ S := by
  constructor
  · intro h
    ext x
    simp only [Finset.mem_inter]
    constructor
    · rintro ⟨hxA, hxS⟩
      have : (⟨x, hxS⟩ : ↥S) ∈ subLab S B := h ▸ mem_subLab.2 hxA
      exact ⟨mem_subLab.1 this, hxS⟩
    · rintro ⟨hxB, hxS⟩
      have : (⟨x, hxS⟩ : ↥S) ∈ subLab S A := h.symm ▸ mem_subLab.2 hxB
      exact ⟨mem_subLab.1 this, hxS⟩
  · intro h
    ext x
    rw [mem_subLab, mem_subLab]
    constructor
    · intro hx
      have : (x : X) ∈ A ∩ S := Finset.mem_inter.2 ⟨hx, x.2⟩
      rw [h] at this
      exact (Finset.mem_inter.1 this).1
    · intro hx
      have : (x : X) ∈ B ∩ S := Finset.mem_inter.2 ⟨hx, x.2⟩
      rw [← h] at this
      exact (Finset.mem_inter.1 this).1

/-- `subLab` is equivariant. -/
theorem subLab_smul {X : Type*} [DecidableEq X] (ρ : M →* Perm X) (S : Finset X)
    (hS : ∀ g : M, ∀ x ∈ S, ρ g x ∈ S) (g : M) (L : Finset X) :
    subLab S (ρ g • L) = restrictHom ρ S hS g • subLab S L := by
  ext x
  rw [mem_subLab, Finset.mem_smul_finset, Finset.mem_smul_finset]
  constructor
  · rintro ⟨z, hz, hzx⟩
    have hzS : z ∈ S := by
      have := hS g⁻¹ _ x.2
      rw [← hzx, map_inv] at this
      simpa using this
    refine ⟨⟨z, hzS⟩, mem_subLab.2 hz, ?_⟩
    apply Subtype.ext
    simpa [restrictHom_apply] using hzx
  · rintro ⟨y, hy, hyx⟩
    refine ⟨y, mem_subLab.1 hy, ?_⟩
    rw [← hyx]
    simp [restrictHom_apply]

variable {ψ : M →* Perm Γ} {W O : Finset Ω} {lab : Ω → Finset Γ}

/-! ### M1: invariant subsets -/

/-- **Restriction to an invariant set** `Γ'`: labels `lab ∩ Γ'` give a hint wherever they are
not constant. -/
theorem hint_inter {Γ' : Finset Γ} (hΓ' : ∀ g : M, ∀ γ ∈ Γ', ψ g γ ∈ Γ')
    (he : Equivar ψ O lab) (hn : NonConst O fun u => lab u ∩ Γ') :
    IsHint (restrictHom ψ Γ' hΓ') O fun u => subLab Γ' (lab u) := by
  refine ⟨fun g u hu => ?_, ?_⟩
  · show subLab Γ' (lab (g • u)) = _
    rw [he g u hu, subLab_smul]
  · obtain ⟨u, hu, v, hv, huv⟩ := hn
    exact ⟨u, hu, v, hv, fun h => huv (subLab_eq_iff.1 h)⟩

/-- Of finitely many sets covering `Γ`, one meets the labels non-constantly. -/
theorem exists_nonConst_inter {ι : Type*} (I : Finset ι) (Γs : ι → Finset Γ)
    (hcov : ∀ γ : Γ, ∃ i ∈ I, γ ∈ Γs i) (hn : NonConst O lab) :
    ∃ i ∈ I, NonConst O fun u => lab u ∩ Γs i := by
  by_contra hcon
  push Not at hcon
  obtain ⟨u, hu, v, hv, huv⟩ := hn
  apply huv
  ext γ
  obtain ⟨i, hi, hγ⟩ := hcov γ
  have hc := hcon i hi
  simp only [NonConst, not_exists, not_and, not_not] at hc
  have := congrArg (γ ∈ ·) (hc u hu v hv)
  simp only [Finset.mem_inter, hγ, and_true, eq_iff_iff] at this
  exact this

/-! ### M2: block systems -/

/-- A block system `Ψ` for `ψ`: nonempty, pairwise disjoint blocks covering `Γ`, permuted by
`ψ`. -/
structure IsBlockSys (ψ : M →* Perm Γ) (Ψ : Finset (Finset Γ)) : Prop where
  nonempty : ∀ B ∈ Ψ, B.Nonempty
  disj : ∀ B ∈ Ψ, ∀ C ∈ Ψ, B ≠ C → Disjoint B C
  cover : ∀ γ : Γ, ∃ B ∈ Ψ, γ ∈ B
  inv : ∀ g : M, ∀ B ∈ Ψ, setAct ψ g B ∈ Ψ

/-- The blocks met by `T`. -/
def metBlocks (Ψ : Finset (Finset Γ)) (T : Finset Γ) : Finset (Finset Γ) :=
  Ψ.filter fun B => (T ∩ B).Nonempty

/-- The blocks whose intersection with `T` is least. -/
def leastBlocks (Ψ : Finset (Finset Γ)) (T : Finset Γ) : Finset (Finset Γ) :=
  Ψ.filter fun B => ∀ C ∈ Ψ, (T ∩ B).card ≤ (T ∩ C).card

/-- The block label: the blocks met by `T`, or, if `T` meets every block, those of least
intersection. -/
def blockLabel (Ψ : Finset (Finset Γ)) (T : Finset Γ) : Finset (Finset Γ) :=
  if metBlocks Ψ T = Ψ then leastBlocks Ψ T else metBlocks Ψ T

/-- `T` meets every block of `Ψ` in the same number of points. -/
def Equidist (Ψ : Finset (Finset Γ)) (T : Finset Γ) : Prop :=
  ∀ B ∈ Ψ, ∀ C ∈ Ψ, (T ∩ B).card = (T ∩ C).card

theorem card_blockLabel_le (Ψ : Finset (Finset Γ)) (hdisj : ∀ B ∈ Ψ, ∀ C ∈ Ψ, B ≠ C →
    Disjoint B C) (T : Finset Γ) : (blockLabel Ψ T).card ≤ T.card := by
  have hmet : (metBlocks Ψ T).card ≤ T.card := by
    have hsub : (metBlocks Ψ T).biUnion (fun B => T ∩ B) ⊆ T :=
      Finset.biUnion_subset.2 fun _ _ => Finset.inter_subset_left
    have hcard := Finset.card_le_card hsub
    have hpd : (↑(metBlocks Ψ T) : Set (Finset Γ)).PairwiseDisjoint fun B => T ∩ B := by
      intro B hB C hC hBC
      have hB' : B ∈ Ψ := (Finset.mem_filter.1 (Finset.mem_coe.1 hB)).1
      have hC' : C ∈ Ψ := (Finset.mem_filter.1 (Finset.mem_coe.1 hC)).1
      exact (hdisj B hB' C hC' hBC).mono Finset.inter_subset_right Finset.inter_subset_right
    rw [Finset.card_biUnion hpd] at hcard
    refine le_trans ?_ hcard
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fun B hB =>
      Finset.one_le_card.2 (Finset.mem_filter.1 hB).2
  unfold blockLabel
  split_ifs with h
  · refine le_trans (Finset.card_le_card ?_) hmet
    rw [h]
    exact Finset.filter_subset _ _
  · exact hmet

/-- A block system with blocks of at least two points has at most `|Γ|/2` blocks. -/
theorem card_blockSys_le [Fintype Γ] {Ψ : Finset (Finset Γ)} (hΨ : IsBlockSys ψ Ψ)
    (h2 : ∀ B ∈ Ψ, 2 ≤ B.card) :
    2 * Ψ.card ≤ Fintype.card Γ := by
  have hcard := Finset.card_le_univ (Ψ.biUnion id)
  have hpd : (↑Ψ : Set (Finset Γ)).PairwiseDisjoint id := fun B hB C hC hBC =>
    hΨ.disj B (Finset.mem_coe.1 hB) C (Finset.mem_coe.1 hC) hBC
  rw [Finset.card_biUnion hpd] at hcard
  refine le_trans ?_ hcard
  rw [Finset.card_eq_sum_ones, Finset.mul_sum]
  exact Finset.sum_le_sum fun B hB => by simpa using h2 B hB

theorem mem_leastBlocks {Ψ : Finset (Finset Γ)} {T B : Finset Γ} :
    B ∈ leastBlocks Ψ T ↔ B ∈ Ψ ∧ ∀ C ∈ Ψ, (T ∩ B).card ≤ (T ∩ C).card :=
  Finset.mem_filter

theorem mem_metBlocks {Ψ : Finset (Finset Γ)} {T B : Finset Γ} :
    B ∈ metBlocks Ψ T ↔ B ∈ Ψ ∧ (T ∩ B).Nonempty :=
  Finset.mem_filter

theorem blockLabel_subset (Ψ : Finset (Finset Γ)) (T : Finset Γ) : blockLabel Ψ T ⊆ Ψ := by
  unfold blockLabel
  split_ifs <;> exact Finset.filter_subset _ _

theorem if_pos' {p : Prop} [Decidable p] {α : Sort*} {a b : α} (h : p) :
    (if p then a else b) = a := by simp [h]

theorem if_neg' {p : Prop} [Decidable p] {α : Sort*} {a b : α} (h : ¬ p) :
    (if p then a else b) = b := by simp [h]

/-- `ψ g` permutes the blocks. -/
theorem IsBlockSys.smul_mem_iff {Ψ : Finset (Finset Γ)} (hΨ : IsBlockSys ψ Ψ) (g : M)
    (B : Finset Γ) : ψ g • B ∈ Ψ ↔ B ∈ Ψ := by
  refine ⟨fun h => ?_, fun h => hΨ.inv g B h⟩
  have := hΨ.inv g⁻¹ _ h
  rwa [setAct_apply, map_inv, inv_smul_smul] at this

/-- The action of `setAct ψ g` on sets of blocks is the pointwise action of `ψ g`. -/
theorem setAct_smul_eq (g : M) (L : Finset (Finset Γ)) : setAct ψ g • L = ψ g • L := by
  ext C
  simp only [Finset.mem_smul_finset, Perm.smul_def, setAct_apply]

/-- Filtering the blocks commutes with a permutation of the blocks. -/
theorem filter_eq_smul {Ψ : Finset (Finset Γ)} {σ : Perm Γ} (hσ : ∀ B, σ • B ∈ Ψ ↔ B ∈ Ψ)
    (p q : Finset Γ → Prop) [DecidablePred p] [DecidablePred q] (hpq : ∀ B, p (σ • B) ↔ q B) :
    Ψ.filter p = σ • Ψ.filter q := by
  ext C
  rw [Finset.mem_filter, Finset.mem_smul_finset]
  constructor
  · rintro ⟨hC, hp⟩
    refine ⟨σ⁻¹ • C, Finset.mem_filter.2 ⟨?_, ?_⟩, smul_inv_smul σ C⟩
    · rw [← hσ, smul_inv_smul]
      exact hC
    · rw [← hpq, smul_inv_smul]
      exact hp
  · rintro ⟨B, hB, rfl⟩
    rw [Finset.mem_filter] at hB
    exact ⟨(hσ B).2 hB.1, (hpq B).2 hB.2⟩

theorem smul_blocks {Ψ : Finset (Finset Γ)} {σ : Perm Γ} (hσ : ∀ B, σ • B ∈ Ψ ↔ B ∈ Ψ) :
    σ • Ψ = Ψ := by
  have := filter_eq_smul hσ (fun _ => True) (fun _ => True) fun _ => Iff.rfl
  simpa using this.symm

theorem card_smul_inter (σ : Perm Γ) (T B : Finset Γ) :
    (σ • T ∩ σ • B).card = (T ∩ B).card := by
  rw [← Finset.smul_finset_inter, Finset.card_smul_finset]

theorem metBlocks_smul {Ψ : Finset (Finset Γ)} {σ : Perm Γ} (hσ : ∀ B, σ • B ∈ Ψ ↔ B ∈ Ψ)
    (T : Finset Γ) : metBlocks Ψ (σ • T) = σ • metBlocks Ψ T := by
  refine filter_eq_smul hσ _ _ fun B => ?_
  rw [← Finset.smul_finset_inter, Finset.smul_finset_nonempty]

theorem leastBlocks_smul {Ψ : Finset (Finset Γ)} {σ : Perm Γ} (hσ : ∀ B, σ • B ∈ Ψ ↔ B ∈ Ψ)
    (T : Finset Γ) : leastBlocks Ψ (σ • T) = σ • leastBlocks Ψ T := by
  refine filter_eq_smul hσ _ _ fun B => ?_
  constructor
  · intro h C hC
    have := h (σ • C) ((hσ C).2 hC)
    rwa [card_smul_inter, card_smul_inter] at this
  · intro h C hC
    have := h (σ⁻¹ • C) (by rw [← hσ, smul_inv_smul]; exact hC)
    rw [← card_smul_inter σ T B, ← card_smul_inter σ T (σ⁻¹ • C), smul_inv_smul] at this
    exact this

theorem blockLabel_smul {Ψ : Finset (Finset Γ)} {σ : Perm Γ} (hσ : ∀ B, σ • B ∈ Ψ ↔ B ∈ Ψ)
    (T : Finset Γ) : blockLabel Ψ (σ • T) = σ • blockLabel Ψ T := by
  have hiff : metBlocks Ψ (σ • T) = Ψ ↔ metBlocks Ψ T = Ψ := by
    rw [metBlocks_smul hσ]
    calc σ • metBlocks Ψ T = Ψ ↔ σ • metBlocks Ψ T = σ • Ψ := by rw [smul_blocks hσ]
      _ ↔ metBlocks Ψ T = Ψ := smul_left_cancel_iff σ
  unfold blockLabel
  by_cases h : metBlocks Ψ T = Ψ
  · rw [if_pos' (hiff.2 h), if_pos' h, leastBlocks_smul hσ]
  · rw [if_neg' (mt hiff.1 h), if_neg' h, metBlocks_smul hσ]

theorem equidist_smul {Ψ : Finset (Finset Γ)} {σ : Perm Γ} (hσ : ∀ B, σ • B ∈ Ψ ↔ B ∈ Ψ)
    (T : Finset Γ) : Equidist Ψ (σ • T) ↔ Equidist Ψ T := by
  constructor
  · intro h B hB C hC
    have := h (σ • B) ((hσ B).2 hB) (σ • C) ((hσ C).2 hC)
    rwa [card_smul_inter, card_smul_inter] at this
  · intro h B hB C hC
    have := h (σ⁻¹ • B) (by rw [← hσ, smul_inv_smul]; exact hB) (σ⁻¹ • C)
      (by rw [← hσ, smul_inv_smul]; exact hC)
    rwa [← card_smul_inter σ T, ← card_smul_inter σ T (σ⁻¹ • C), smul_inv_smul,
      smul_inv_smul] at this

/-- `ψ` is transitive on the blocks. -/
theorem IsBlockSys.exists_smul_eq {Ψ : Finset (Finset Γ)} (hΨ : IsBlockSys ψ Ψ)
    (htr : ∀ γ δ : Γ, ∃ g : M, ψ g γ = δ) {B C : Finset Γ} (hB : B ∈ Ψ) (hC : C ∈ Ψ)
    {γ δ : Γ} (hγ : γ ∈ B) (hδ : δ ∈ C) : ∃ g : M, ψ g γ = δ ∧ ψ g • B = C := by
  obtain ⟨g, hg⟩ := htr γ δ
  refine ⟨g, hg, ?_⟩
  by_contra hne
  have hgB := hΨ.inv g B hB
  rw [setAct_apply] at hgB
  have hδ' : δ ∈ ψ g • B := by
    rw [← hg]
    exact Finset.smul_mem_smul_finset hγ
  exact Finset.disjoint_left.1 (hΨ.disj _ hgB C hC hne) hδ' hδ

/-- **M2a**: if `ψ` is transitive on `Γ` and some label is not equidistributed over the block
system `Ψ`, the block labels form a hint on `Ψ`. -/
theorem hint_blockLabel [Fintype Γ] {Ψ : Finset (Finset Γ)} (hΨ : IsBlockSys ψ Ψ)
    (htr : ∀ γ δ : Γ, ∃ g : M, ψ g γ = δ) (hW : Invariant M W)
    (hh : IsHint ψ W lab) {u₀ : Ω} (hu₀ : u₀ ∈ W) (hne : ¬ Equidist Ψ (lab u₀)) :
    IsHint (restrictHom (setAct ψ) Ψ hΨ.inv) W fun u => subLab Ψ (blockLabel Ψ (lab u)) := by
  have hσ : ∀ g : M, ∀ B, ψ g • B ∈ Ψ ↔ B ∈ Ψ := hΨ.smul_mem_iff
  refine ⟨fun g u hu => ?_, ?_⟩
  · show subLab Ψ (blockLabel Ψ (lab (g • u))) = _
    rw [hh.equivar g u hu, blockLabel_smul (hσ g), ← setAct_smul_eq, subLab_smul]
  set T₀ := lab u₀ with hT₀
  set L := blockLabel Ψ T₀ with hL
  have hLΨ : L ⊆ Ψ := blockLabel_subset Ψ T₀
  -- `L` is a nonempty proper subset of `Ψ`
  have hne' : ∃ B ∈ Ψ, ∃ C ∈ Ψ, (T₀ ∩ B).card ≠ (T₀ ∩ C).card := by
    by_contra hc
    push Not at hc
    exact hne hc
  obtain ⟨B₁, hB₁, C₁, hC₁, hBC₁⟩ := hne'
  have hprop : ∃ B ∈ L, ∃ C ∈ Ψ, C ∉ L := by
    by_cases hm : metBlocks Ψ T₀ = Ψ
    · have hLeq : L = leastBlocks Ψ T₀ := by rw [hL]; unfold blockLabel; rw [if_pos' hm]
      obtain ⟨B, hB, hmin⟩ := Finset.exists_min_image Ψ (fun B => (T₀ ∩ B).card) ⟨B₁, hB₁⟩
      refine ⟨B, hLeq ▸ mem_leastBlocks.2 ⟨hB, hmin⟩, ?_⟩
      rcases lt_or_gt_of_ne hBC₁ with hlt | hlt
      · refine ⟨C₁, hC₁, fun hC => ?_⟩
        rw [hLeq] at hC
        have := (mem_leastBlocks.1 hC).2 B₁ hB₁
        omega
      · refine ⟨B₁, hB₁, fun hB' => ?_⟩
        rw [hLeq] at hB'
        have := (mem_leastBlocks.1 hB').2 C₁ hC₁
        omega
    · have hLeq : L = metBlocks Ψ T₀ := by rw [hL]; unfold blockLabel; rw [if_neg' hm]
      have hT₀ne : T₀.Nonempty := by
        by_contra h0
        rw [Finset.not_nonempty_iff_eq_empty] at h0
        simp [h0] at hBC₁
      obtain ⟨γ, hγ⟩ := hT₀ne
      obtain ⟨B, hB, hγB⟩ := hΨ.cover γ
      refine ⟨B, hLeq ▸ mem_metBlocks.2 ⟨hB, γ, Finset.mem_inter.2 ⟨hγ, hγB⟩⟩, ?_⟩
      have hss : metBlocks Ψ T₀ ⊂ Ψ :=
        Finset.ssubset_iff_subset_ne.2 ⟨Finset.filter_subset _ _, hm⟩
      obtain ⟨C, hC, hCn⟩ := Finset.exists_of_ssubset hss
      exact ⟨C, hC, hLeq ▸ hCn⟩
  obtain ⟨B, hBL, C, hC, hCL⟩ := hprop
  obtain ⟨γ, hγ⟩ := hΨ.nonempty B (hLΨ hBL)
  obtain ⟨δ, hδ⟩ := hΨ.nonempty C hC
  obtain ⟨g, -, hgB⟩ := hΨ.exists_smul_eq htr (hLΨ hBL) hC hγ hδ
  refine ⟨g • u₀, hW g u₀ hu₀, u₀, hu₀, fun heq => ?_⟩
  simp only at heq
  rw [hh.equivar g u₀ hu₀, blockLabel_smul (hσ g), subLab_eq_iff] at heq
  have hsub : ψ g • L ⊆ Ψ := by
    intro X hX
    obtain ⟨Y, hY, rfl⟩ := Finset.mem_smul_finset.1 hX
    exact (hσ g Y).2 (hLΨ hY)
  rw [Finset.inter_eq_left.2 hsub, Finset.inter_eq_left.2 hLΨ] at heq
  apply hCL
  rw [← heq, ← hgB]
  exact Finset.smul_mem_smul_finset hBL

/-- The preimage of the setwise stabilizer of `B₀`. -/
def blockStab (ψ : M →* Perm Γ) (B₀ : Finset Γ) : Subgroup M :=
  (stabilizer (Perm Γ) B₀).comap ψ

theorem blockStab_inv (B₀ : Finset Γ) :
    ∀ g : ↥(blockStab ψ B₀), ∀ γ ∈ B₀, (ψ.comp (blockStab ψ B₀).subtype) g γ ∈ B₀ := by
  intro g γ hγ
  have hg : ψ g • B₀ = B₀ := g.2
  have h := Finset.smul_mem_smul_finset (a := ψ g) hγ
  rw [hg] at h
  exact h

/-- **M2b**: if the labels are equidistributed over the block system `Ψ` of a transitive `ψ`,
then on every orbit of the stabilizer of a block `B₀` the labels `lab ∩ B₀` form a hint. -/
theorem hint_blockStab [Fintype Γ] {Ψ : Finset (Finset Γ)} (hΨ : IsBlockSys ψ Ψ)
    (htr : ∀ γ δ : Γ, ∃ g : M, ψ g γ = δ) (hT : Transitive M W)
    (hh : IsHint ψ W lab) {u₀ : Ω} (hu₀ : u₀ ∈ W) (heq : Equidist Ψ (lab u₀))
    {B₀ : Finset Γ} (hB₀ : B₀ ∈ Ψ) (hO : O ⊆ W) (hOne : O.Nonempty)
    (hOinv : Invariant (blockStab ψ B₀) O) :
    IsHint (restrictHom (ψ.comp (blockStab ψ B₀).subtype) B₀ (blockStab_inv B₀)) O
      fun u => subLab B₀ (lab u) := by
  have hσ : ∀ g : M, ∀ B, ψ g • B ∈ Ψ ↔ B ∈ Ψ := hΨ.smul_mem_iff
  refine ⟨fun g u hu => ?_, ?_⟩
  · show subLab B₀ (lab ((g : M) • u)) = _
    rw [hh.equivar (g : M) u (hO hu)]
    exact subLab_smul (ψ.comp (blockStab ψ B₀).subtype) B₀ (blockStab_inv B₀) g (lab u)
  obtain ⟨u, hu⟩ := hOne
  have huW := hO hu
  set T := lab u with hTdef
  -- every label of `W` is a translate of `T`
  have htrans : ∀ v ∈ W, ∃ g : M, lab v = ψ g • T := by
    intro v hv
    obtain ⟨g, rfl⟩ := hT u huW v hv
    exact ⟨g, hh.equivar g u huW⟩
  have hTeq : Equidist Ψ T := by
    obtain ⟨g, hg⟩ := htrans u₀ hu₀
    rw [hg, equidist_smul (hσ g)] at heq
    exact heq
  -- a label invariant under every `ψ g` would make the labels constant
  have hnotinv : ∀ X : Finset Γ, (∀ g : M, ψ g • X = X) → T ≠ X := by
    intro X hX hTX
    obtain ⟨a, ha, b, hb, hab⟩ := hh.nonconst
    obtain ⟨g, hg⟩ := htrans a ha
    obtain ⟨g', hg'⟩ := htrans b hb
    rw [hg, hg', hTX, hX, hX] at hab
    exact hab rfl
  have hcardB : ∀ B ∈ Ψ, B.card = B₀.card := by
    intro B hB
    obtain ⟨γ, hγ⟩ := hΨ.nonempty B₀ hB₀
    obtain ⟨δ, hδ⟩ := hΨ.nonempty B hB
    obtain ⟨g, -, hgB⟩ := hΨ.exists_smul_eq htr hB₀ hB hγ hδ
    rw [← hgB, Finset.card_smul_finset]
  -- `T ∩ B₀` is a nonempty proper subset of `B₀`
  have hγ : (T ∩ B₀).Nonempty := by
    by_contra h0
    rw [Finset.not_nonempty_iff_eq_empty] at h0
    apply hnotinv ∅ (fun g => Finset.smul_finset_empty _)
    ext γ
    simp only [Finset.notMem_empty, iff_false]
    intro hγ
    obtain ⟨B, hB, hγB⟩ := hΨ.cover γ
    have h1 := hTeq B hB B₀ hB₀
    rw [h0, Finset.card_empty] at h1
    have : γ ∈ T ∩ B := Finset.mem_inter.2 ⟨hγ, hγB⟩
    rw [Finset.card_eq_zero.1 h1] at this
    exact Finset.notMem_empty _ this
  have hδ : ∃ δ ∈ B₀, δ ∉ T := by
    by_contra hall
    push Not at hall
    apply hnotinv Finset.univ (fun g => Finset.smul_finset_univ)
    ext γ
    simp only [Finset.mem_univ, iff_true]
    obtain ⟨B, hB, hγB⟩ := hΨ.cover γ
    have h1 := hTeq B hB B₀ hB₀
    have h2 : T ∩ B₀ = B₀ := Finset.inter_eq_right.2 hall
    rw [h2, ← hcardB B hB] at h1
    have h3 : T ∩ B = B :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_right h1.ge
    have : γ ∈ T ∩ B := by rw [h3]; exact hγB
    exact (Finset.mem_inter.1 this).1
  obtain ⟨γ, hγT⟩ := hγ
  obtain ⟨δ, hδB, hδT⟩ := hδ
  obtain ⟨g, hgγ, hgB⟩ := hΨ.exists_smul_eq htr hB₀ hB₀ (Finset.mem_inter.1 hγT).2 hδB
  let g' : ↥(blockStab ψ B₀) := ⟨g, hgB⟩
  refine ⟨g' • u, hOinv g' u hu, u, hu, fun heq' => ?_⟩
  simp only at heq'
  rw [subLab_eq_iff] at heq'
  have hmem : δ ∈ lab (g' • u) ∩ B₀ := by
    refine Finset.mem_inter.2 ⟨?_, hδB⟩
    show δ ∈ lab ((g : M) • u)
    rw [hh.equivar g u huW, ← hgγ]
    exact Finset.smul_mem_smul_finset (Finset.mem_inter.1 hγT).1
  rw [heq'] at hmem
  exact hδT (Finset.mem_inter.1 hmem).1

/-! ### Johnson union -/

/-- The union of the `s`-subsets of `Λ` labelling the points of `T` in `V₀`. -/
def jUnion (J : JEmb Γ) (T : Finset Γ) : Finset (Finset Γ) := (T ∩ J.V0).biUnion J.f

/-- An invariant Johnson structure: `ψ g` preserves `V₀`. -/
theorem jemb_V0 {J : JEmb Γ} (hinv : ∀ g : M, ψ g • J = J) (g : M) : ψ g • J.V0 = J.V0 := by
  have := congrArg JEmb.V0 (hinv g)
  rwa [JEmb.smul_V0] at this

/-- An invariant Johnson structure: `ψ g` preserves the cells. -/
theorem jemb_Λ {J : JEmb Γ} (hinv : ∀ g : M, ψ g • J = J) (g : M) : ψ g • J.Λ = J.Λ := by
  have := congrArg JEmb.Λ (hinv g)
  rwa [JEmb.smul_Λ] at this

/-- An invariant Johnson structure: the labelling is equivariant. -/
theorem jemb_f {J : JEmb Γ} (hinv : ∀ g : M, ψ g • J = J) (g : M) (γ : Γ) :
    J.f (ψ g γ) = ψ g • J.f γ := by
  have h := congrFun (congrArg JEmb.f (hinv g)) (ψ g γ)
  rw [JEmb.smul_f] at h
  rw [← h]
  simp

/-- `n (n - 1) = 2 C(n, 2)`. -/
theorem mul_pred_eq_two_mul_choose (n : ℕ) : n * (n - 1) = 2 * n.choose 2 := by
  rw [Nat.choose_two_right, Nat.mul_div_cancel' (Nat.even_mul_pred_self n).two_dvd]

/-- `C(n, a) ≤ C(n, b)` for `a ≤ b ≤ n / 2`. -/
theorem choose_le_choose_of_le_half {n a b : ℕ} (hab : a ≤ b) (hb : b ≤ n / 2) :
    n.choose a ≤ n.choose b := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b _ ih => exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

theorem card_jUnion_le {V : Finset Γ} {t : ℕ} {J : JEmb Γ} (hJ : IsJohnson V t J)
    (T : Finset Γ) : (jUnion J T).card ≤ T.card * J.s := by
  refine Finset.card_biUnion_le.trans ?_
  have : ∀ γ ∈ T ∩ J.V0, (J.f γ).card = J.s := fun γ hγ =>
    (Finset.mem_powersetCard.1 (hJ.maps_to γ (Finset.mem_inter.1 hγ).2)).2
  rw [Finset.sum_congr rfl this, Finset.sum_const, smul_eq_mul]
  exact Nat.mul_le_mul_right _ (Finset.card_le_card Finset.inter_subset_left)

theorem jUnion_subset {V : Finset Γ} {t : ℕ} {J : JEmb Γ} (hJ : IsJohnson V t J)
    (T : Finset Γ) : jUnion J T ⊆ J.Λ :=
  Finset.biUnion_subset.2 fun γ hγ =>
    (Finset.mem_powersetCard.1 (hJ.maps_to γ (Finset.mem_inter.1 hγ).2)).1

omit [DecidableEq Γ] in
/-- The cells of a Johnson structure: `|Λ| (|Λ| - 1) ≤ 2 |V₀|`, so `|Λ| ≤ √(2|V₀|) + 1`. -/
theorem card_cells {V : Finset Γ} {t : ℕ} {J : JEmb Γ} (hJ : IsJohnson V t J) :
    J.Λ.card * (J.Λ.card - 1) ≤ 2 * J.V0.card := by
  have hV : J.V0.card = (J.Λ.powersetCard J.s).card := by
    refine Finset.card_bij (fun v _ => J.f v) (fun v hv => hJ.maps_to v hv)
      (fun v hv w hw h => hJ.inj v hv w hw h) fun T hT => ?_
    obtain ⟨v, hv, rfl⟩ := hJ.surj T hT
    exact ⟨v, hv, rfl⟩
  rw [hV, Finset.card_powersetCard, mul_pred_eq_two_mul_choose]
  exact Nat.mul_le_mul_left 2
    (choose_le_choose_of_le_half hJ.two_le (by have := hJ.le_half; omega))

theorem cells_inv {J : JEmb Γ}
    (hinv : ∀ g : M, ψ g • J = J) : ∀ g : M, ∀ a ∈ J.Λ, setAct ψ g a ∈ J.Λ := by
  intro g a ha
  rw [setAct_apply, ← jemb_Λ hinv g]
  exact Finset.smul_mem_smul_finset ha

/-- The Johnson union is equivariant. -/
theorem jUnion_smul {J : JEmb Γ} (hinv : ∀ g : M, ψ g • J = J) (g : M) (T : Finset Γ) :
    jUnion J (ψ g • T) = ψ g • jUnion J T := by
  unfold jUnion
  have hV := jemb_V0 hinv g
  calc (ψ g • T ∩ J.V0).biUnion J.f = (ψ g • (T ∩ J.V0)).biUnion J.f := by
        rw [Finset.smul_finset_inter, hV]
    _ = (T ∩ J.V0).biUnion fun γ => J.f (ψ g γ) := by
        rw [Finset.smul_finset_def, Finset.image_biUnion]
        rfl
    _ = (T ∩ J.V0).biUnion fun γ => ψ g • J.f γ := by
        simp_rw [jemb_f hinv]
    _ = ψ g • (T ∩ J.V0).biUnion J.f := by
        rw [Finset.smul_finset_def (s := (T ∩ J.V0).biUnion J.f), Finset.biUnion_image]
        rfl

/-- **Johnson union**: where the union is not constant, it is a hint on the cells `Λ`. -/
theorem hint_jUnion {V : Finset Γ} {t : ℕ} {J : JEmb Γ} (hJ : IsJohnson V t J)
    (hinv : ∀ g : M, ψ g • J = J) (he : Equivar ψ O lab)
    (hn : NonConst O fun u => jUnion J (lab u)) :
    IsHint (restrictHom (setAct ψ) J.Λ (cells_inv hinv)) O
      fun u => subLab J.Λ (jUnion J (lab u)) := by
  refine ⟨fun g u hu => ?_, ?_⟩
  · show subLab J.Λ (jUnion J (lab (g • u))) = _
    rw [he g u hu, jUnion_smul hinv, ← setAct_smul_eq, subLab_smul]
  · obtain ⟨u, hu, v, hv, huv⟩ := hn
    refine ⟨u, hu, v, hv, fun h => huv ?_⟩
    rwa [subLab_eq_iff, Finset.inter_eq_left.2 (jUnion_subset hJ _),
      Finset.inter_eq_left.2 (jUnion_subset hJ _)] at h

/-- **The Johnson fallback**: if on an orbit both `lab ∖ V₀` and the union are constant, every
element fixing each cell of the union fixes every label of the orbit. -/
theorem fix_of_jUnion_const {V : Finset Γ} {t : ℕ} {J : JEmb Γ} (hJ : IsJohnson V t J)
    (hinv : ∀ g : M, ψ g • J = J) (hOinv : Invariant M O) (he : Equivar ψ O lab)
    (hA : ¬ NonConst O fun u => lab u \ J.V0)
    (hU : ¬ NonConst O fun u => jUnion J (lab u)) {u₀ : Ω} (hu₀ : u₀ ∈ O) {g : M}
    (hg : ∀ a ∈ jUnion J (lab u₀), ψ g • a = a) : ∀ u ∈ O, ψ g • lab u = lab u := by
  intro u hu
  have hA' : ∀ v ∈ O, lab v \ J.V0 = lab u₀ \ J.V0 := by
    intro v hv
    by_contra hne
    exact hA ⟨v, hv, u₀, hu₀, hne⟩
  have hU' : ∀ v ∈ O, jUnion J (lab v) = jUnion J (lab u₀) := by
    intro v hv
    by_contra hne
    exact hU ⟨v, hv, u₀, hu₀, hne⟩
  -- the part outside `V₀` is invariant
  have hAinv : ψ g • (lab u₀ \ J.V0) = lab u₀ \ J.V0 := by
    have h1 := hA' (g • u₀) (hOinv g u₀ hu₀)
    rw [he g u₀ hu₀] at h1
    rw [Finset.smul_finset_sdiff, jemb_V0 hinv g]
    exact h1
  -- the part inside `V₀` is fixed pointwise
  have hfix : ∀ γ ∈ lab u ∩ J.V0, ψ g γ = γ := by
    intro γ hγ
    have hsub : J.f γ ⊆ jUnion J (lab u₀) :=
      hU' u hu ▸ Finset.subset_biUnion_of_mem J.f hγ
    have hfγ : ψ g • J.f γ = J.f γ := by
      ext a
      constructor
      · intro ha
        obtain ⟨b, hb, rfl⟩ := Finset.mem_smul_finset.1 ha
        rw [hg b (hsub hb)]
        exact hb
      · intro ha
        rw [← hg a (hsub ha)]
        exact Finset.smul_mem_smul_finset ha
    have hmem : ψ g γ ∈ J.V0 := by
      rw [← jemb_V0 hinv g]
      exact Finset.smul_mem_smul_finset (Finset.mem_inter.1 hγ).2
    exact hJ.inj _ hmem γ (Finset.mem_inter.1 hγ).2 (by rw [jemb_f hinv, hfγ])
  have hAu := hA' u hu
  ext x
  rw [Finset.mem_smul_finset]
  constructor
  · rintro ⟨y, hy, rfl⟩
    by_cases hyV : y ∈ J.V0
    · rw [Perm.smul_def, hfix y (Finset.mem_inter.2 ⟨hy, hyV⟩)]
      exact hy
    · have hy' : y ∈ lab u₀ \ J.V0 := hAu ▸ Finset.mem_sdiff.2 ⟨hy, hyV⟩
      have : ψ g • y ∈ lab u₀ \ J.V0 := hAinv ▸ Finset.smul_mem_smul_finset hy'
      rw [← hAu] at this
      exact (Finset.mem_sdiff.1 this).1
  · intro hx
    by_cases hxV : x ∈ J.V0
    · exact ⟨x, hx, hfix x (Finset.mem_inter.2 ⟨hx, hxV⟩)⟩
    · have hx' : x ∈ ψ g • (lab u₀ \ J.V0) := by
        rw [hAinv, ← hAu]
        exact Finset.mem_sdiff.2 ⟨hx, hxV⟩
      obtain ⟨y, hy, hyx⟩ := Finset.mem_smul_finset.1 hx'
      rw [← hAu] at hy
      exact ⟨y, (Finset.mem_sdiff.1 hy).1, hyx⟩

end GraphIso.Recursion
