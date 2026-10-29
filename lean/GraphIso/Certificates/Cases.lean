module

public import GraphIso.SplitJohnson.Output
public import GraphIso.Coherent.Classical
public import GraphIso.AltQuot.Interfaces
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import Mathlib.GroupTheory.GroupAction.SubMulAction.OfFixingSubgroup

/-!
# Aggregation, Cases 1 and 2: orbit colourings and orbital configurations

Helfgott §6.2, for a permutation group `P` on a finite set (in the application `P = φ(F)`, the
group induced on `Γ` by the certificates of fullness).
* **Case 1** (`orbitPart_valid`): when the points moved by `P` are at least half of `Γ` and no
  orbit has more than half of the points, colouring `Γ` by orbit length, with the orbits as
  blocks and the fixed points as one block (`IsOrbitPart`), is a colored `⌊m/2⌋`-partition.
* **Case 2**: an orbit of more than half of the points is unique (`large_orbit_unique`). In case
  2b (the induced group is not a giant) the degree of transitivity `d` exists and is bounded by
  the interface `TransitivityBound` (`exists_degree`), and fixing `d − 1` points of a
  `d`-transitive, not `(d + 1)`-transitive group leaves a transitive, not doubly transitive
  action (`fixing_transitive_not_two`), whose orbital configuration is a homogeneous classical
  coherent configuration that is not a clique (`orbital_config`).
-/

@[expose] public section

namespace GraphIso.Certificates

open Equiv MulAction Pointwise GraphIso.SplitJohnson GraphIso.Coherent

variable {Γ : Type} [Fintype Γ]

/-! ### Case 1 -/

/-- `p` colours `Γ` by orbit length under `P`, with the orbits as blocks and the fixed points
as one block. -/
def IsOrbitPart (P : Subgroup (Perm Γ)) (p : CPart Γ) : Prop :=
  ∀ γ, p.col γ = Nat.card (orbit P γ) ∧
    (p.blk γ : Set Γ) =
      if Nat.card (orbit P γ) = 1 then {δ : Γ | Nat.card (orbit P δ) = 1} else orbit P γ

/-- Orbits are nonempty. -/
private theorem one_le_card_orbit (P : Subgroup (Perm Γ)) (γ : Γ) : 1 ≤ Nat.card (orbit P γ) :=
  haveI : Nonempty (orbit P γ) := ⟨⟨γ, mem_orbit_self γ⟩⟩
  Nat.card_pos

theorem exists_orbitPart (P : Subgroup (Perm Γ)) : ∃ p, IsOrbitPart P p := by
  refine ⟨⟨fun γ => Nat.card (orbit P γ), fun γ =>
    if Nat.card (orbit P γ) = 1 then Finset.univ.filter fun δ => Nat.card (orbit P δ) = 1
    else (Set.toFinite (orbit P γ)).toFinset⟩, fun γ => ⟨rfl, ?_⟩⟩
  dsimp only
  split_ifs
  · simp only [Finset.coe_filter, Finset.mem_univ, true_and]
  · exact Set.Finite.coe_toFinset _

/-- **Case 1**: the orbit colouring is a colored `⌊m/2⌋`-partition. -/
theorem orbitPart_valid (P : Subgroup (Perm Γ))
    (hS : Fintype.card Γ ≤ 2 * Nat.card {γ : Γ // 1 < Nat.card (orbit P γ)})
    (hO : ∀ γ : Γ, 2 * Nat.card (orbit P γ) ≤ Fintype.card Γ) {p : CPart Γ}
    (hp : IsOrbitPart P p) : IsColPart Finset.univ (Fintype.card Γ / 2) p := by
  -- the blocks: the set of fixed points, and the orbits of more than one point
  have hfix : ∀ γ, Nat.card (orbit P γ) = 1 →
      p.blk γ = Finset.univ.filter fun δ => Nat.card (orbit P δ) = 1 := fun γ h => by
    apply Finset.coe_injective
    rw [(hp γ).2, ite_eq_left h]
    simp only [Finset.coe_filter, Finset.mem_univ, true_and]
  have horb : ∀ γ, Nat.card (orbit P γ) ≠ 1 → (p.blk γ : Set Γ) = orbit P γ := fun γ h => by
    rw [(hp γ).2, ite_eq_right h]
  have hcard : ∀ γ, Nat.card (orbit P γ) ≠ 1 → (p.blk γ).card = Nat.card (orbit P γ) :=
    fun γ h => by rw [← horb γ h, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  -- a point of the block of `γ` has the orbit length of `γ` and the same block
  have hmem : ∀ γ, ∀ δ ∈ p.blk γ, Nat.card (orbit P δ) = Nat.card (orbit P γ) ∧
      p.blk δ = p.blk γ := by
    intro γ δ hδ
    by_cases h : Nat.card (orbit P γ) = 1
    · rw [hfix γ h] at hδ ⊢
      have hδ1 : Nat.card (orbit P δ) = 1 := (Finset.mem_filter.mp hδ).2
      exact ⟨hδ1.trans h.symm, hfix δ hδ1⟩
    · have hδ' : δ ∈ orbit P γ := by rw [← horb γ h]; exact hδ
      have he : orbit P δ = orbit P γ := orbit_eq_iff.mpr hδ'
      refine ⟨by rw [he], Finset.coe_injective ?_⟩
      rw [horb γ h, horb δ (by rwa [he]), he]
  refine ⟨fun γ _ => ?_, fun _ _ => Finset.subset_univ _, fun γ _ δ hδ => (hmem γ δ hδ).2,
    fun γ _ δ hδ => ?_, fun γ _ δ _ hc => ?_, fun γ _ h1 δ _ hc => ?_, fun γ _ => ?_⟩
  · by_cases h : Nat.card (orbit P γ) = 1
    · rw [hfix γ h]; simpa using h
    · rw [← Finset.mem_coe, horb γ h]; exact mem_orbit_self γ
  · rw [(hp δ).1, (hp γ).1]; exact (hmem γ δ hδ).1
  · rw [(hp γ).1, (hp δ).1] at hc
    by_cases h : Nat.card (orbit P γ) = 1
    · rw [hfix γ h, hfix δ (hc ▸ h)]
    · rw [hcard γ h, hcard δ (hc ▸ h), hc]
  · rw [(hp γ).1, (hp δ).1] at hc
    by_cases h : Nat.card (orbit P γ) = 1
    · rw [hfix γ h] at h1
      have hγ : γ ∈ Finset.univ.filter fun δ => Nat.card (orbit P δ) = 1 := by simpa using h
      have hδ : δ ∈ Finset.univ.filter fun δ => Nat.card (orbit P δ) = 1 := by
        simpa using hc.trans h
      exact Finset.card_le_one.mp h1.le δ hδ γ hγ
    · exact absurd ((hcard γ h).symm.trans h1) h
  · by_cases h : Nat.card (orbit P γ) = 1
    · -- the fixed points are at most half of the points
      rw [hfix γ h, Nat.le_div_iff_mul_le two_pos]
      have hsplit := Finset.card_filter_add_card_filter_not (s := Finset.univ)
        fun δ : Γ => Nat.card (orbit P δ) = 1
      have hmov : (Finset.univ.filter fun δ : Γ => ¬ Nat.card (orbit P δ) = 1).card =
          Nat.card {γ : Γ // 1 < Nat.card (orbit P γ)} := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
        congr 1
        refine Finset.filter_congr fun δ _ => ?_
        have := one_le_card_orbit P δ
        omega
      rw [Finset.card_univ] at hsplit
      omega
    · rw [hcard γ h, Nat.le_div_iff_mul_le two_pos, mul_comm]
      exact hO γ

/-! ### Case 2 -/

/-- An orbit of more than half of the points is unique. -/
theorem large_orbit_unique (P : Subgroup (Perm Γ)) {γ δ : Γ}
    (hγ : Fintype.card Γ < 2 * Nat.card (orbit P γ))
    (hδ : Fintype.card Γ < 2 * Nat.card (orbit P δ)) : orbit P γ = orbit P δ := by
  obtain ⟨z, hzγ, hzδ⟩ : (orbit P γ ∩ orbit P δ).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty, ← Set.disjoint_iff_inter_eq_empty] at h
    have hu := Set.ncard_union_eq h
    have hle := Set.ncard_le_card (orbit P γ ∪ orbit P δ)
    rw [Nat.card_coe_set_eq] at hγ hδ
    rw [Nat.card_eq_fintype_card] at hle
    omega
  rw [← orbit_eq_iff.mpr hzγ, orbit_eq_iff.mpr hzδ]

/-- If `P` is `e`-transitive and the pointwise stabilizer of `e` distinct points `u` is doubly
transitive on the other points, then `P` is `(e + 2)`-transitive: move the first `e` entries of
a tuple onto `u`, then the last two with the stabilizer. -/
private theorem isMultiplyPretransitive_add_two {Φ : Type} (P : Subgroup (Perm Φ)) {e : ℕ}
    (u : Fin e ↪ Φ) (h : IsMultiplyPretransitive P Φ e)
    (h2 : IsMultiplyPretransitive (fixingSubgroup P (Set.range u))
      (SubMulAction.ofFixingSubgroup P (Set.range u)) 2) :
    IsMultiplyPretransitive P Φ (e + 2) := by
  have key : ∀ x : Fin (e + 2) ↪ Φ, ∃ a : P, ∀ i : Fin e, a • x (Fin.castAdd 2 i) = u i := by
    intro x
    obtain ⟨a, ha⟩ := h.exists_smul_eq ((Fin.castAddEmb 2).trans x) u
    exact ⟨a, fun i => by rw [← ha]; rfl⟩
  have hout : ∀ (x : Fin (e + 2) ↪ Φ) (a : P), (∀ i : Fin e, a • x (Fin.castAdd 2 i) = u i) →
      ∀ j : Fin 2, a • x (Fin.natAdd e j) ∈ SubMulAction.ofFixingSubgroup P (Set.range u) := by
    intro x a ha j
    rw [SubMulAction.mem_ofFixingSubgroup_iff]
    rintro ⟨i, hi⟩
    rw [← ha i] at hi
    have := congrArg Fin.val (x.injective (smul_left_cancel a hi))
    simp only [Fin.val_castAdd, Fin.val_natAdd] at this
    omega
  have hne : ∀ (x : Fin (e + 2) ↪ Φ) (a : P), a • x (Fin.natAdd e 0) ≠ a • x (Fin.natAdd e 1) :=
    fun x a hx => by
      have := congrArg Fin.val (x.injective (smul_left_cancel a hx))
      simp at this
  constructor
  intro x y
  obtain ⟨a, ha⟩ := key x
  obtain ⟨b, hb⟩ := key y
  rw [is_two_pretransitive_iff] at h2
  obtain ⟨f, hf0, hf1⟩ := h2 (a := ⟨_, hout x a ha 0⟩) (b := ⟨_, hout x a ha 1⟩)
    (c := ⟨_, hout y b hb 0⟩) (d := ⟨_, hout y b hb 1⟩)
    (fun h' => hne x a (congrArg Subtype.val h')) (fun h' => hne y b (congrArg Subtype.val h'))
  have hf : ∀ i : Fin e, (f : P) • u i = u i :=
    fun i => (mem_fixingSubgroup_iff P).mp f.prop _ ⟨i, rfl⟩
  have hf0' := congrArg Subtype.val hf0
  have hf1' := congrArg Subtype.val hf1
  simp only [SubMulAction.val_smul] at hf0' hf1'
  refine ⟨b⁻¹ * (f : P) * a, ?_⟩
  ext i
  rw [Function.Embedding.smul_apply, mul_smul, mul_smul, inv_smul_eq_iff]
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [ha j, hf j, hb j]
  · fin_cases j
    · exact hf0'
    · exact hf1'

/-- **Case 2b, the degree of transitivity**: a transitive group `P` on `Φ` not containing
`Alt(Φ)` has a degree of transitivity `d`: it is `d`-transitive and not `(d + 1)`-transitive,
with `1 ≤ d`, `d + 2 ≤ |Φ|`, and `d ≤ T |Φ|` under the interface `TransitivityBound T`. -/
theorem exists_degree {T : ℕ → ℕ} (hT : GraphIso.AltQuot.TransitivityBound T) {Φ : Type}
    [Fintype Φ] [DecidableEq Φ] (P : Subgroup (Perm Φ)) [IsPretransitive P Φ]
    (hP : ¬ alternatingGroup Φ ≤ P) :
    ∃ d, 1 ≤ d ∧ d + 2 ≤ Fintype.card Φ ∧ d ≤ T (Fintype.card Φ) ∧
      IsMultiplyPretransitive P Φ d ∧ ¬ IsMultiplyPretransitive P Φ (d + 1) := by
  classical
  -- `P` is not `(|Φ| - 1)`-transitive, since it is not all of `Sym(Φ)`
  have htop : ¬ IsMultiplyPretransitive P Φ (Fintype.card Φ - 1) := fun h => by
    rw [← Nat.card_eq_fintype_card] at h
    exact hP ((Equiv.Perm.eq_top_of_isMultiplyPretransitive h).symm ▸ le_top)
  have h1 : IsMultiplyPretransitive P Φ 1 := is_one_pretransitive_iff.mpr inferInstance
  have hc : 2 ≤ Fintype.card Φ := by
    by_contra hc
    exact htop (by rw [show Fintype.card Φ - 1 = 0 by omega]; exact is_zero_pretransitive')
  have hex : ∃ d, ¬ IsMultiplyPretransitive P Φ (d + 1) :=
    ⟨Fintype.card Φ - 2, by rwa [show Fintype.card Φ - 2 + 1 = Fintype.card Φ - 1 by omega]⟩
  have hle : Nat.find hex ≤ Fintype.card Φ - 2 :=
    Nat.find_min' hex (by rwa [show Fintype.card Φ - 2 + 1 = Fintype.card Φ - 1 by omega])
  have hd1 : 1 ≤ Nat.find hex := by
    by_contra h0
    have := Nat.find_spec hex
    rw [show Nat.find hex = 0 by omega] at this
    exact this h1
  have hdt : IsMultiplyPretransitive P Φ (Nat.find hex) := by
    have := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    rwa [not_not, show Nat.find hex - 1 + 1 = Nat.find hex by omega] at this
  exact ⟨Nat.find hex, hd1, by omega, hT Φ P _ (by omega) hdt hP, hdt, Nat.find_spec hex⟩

/-- **Case 2b**: if `P` is `d`-transitive but not `(d + 1)`-transitive (`1 ≤ d`,
`d + 1 ≤ |Φ|`), fixing `d − 1` distinct points leaves a transitive action on the rest that is
not doubly transitive. -/
theorem fixing_transitive_not_two {Φ : Type} [Fintype Φ] [DecidableEq Φ]
    (P : Subgroup (Perm Φ)) {d : ℕ} (hd : 1 ≤ d) (hdΦ : d + 1 ≤ Fintype.card Φ)
    (h₁ : IsMultiplyPretransitive P Φ d) (h₂ : ¬ IsMultiplyPretransitive P Φ (d + 1))
    (u : Fin (d - 1) ↪ Φ) :
    IsPretransitive (fixingSubgroup P (Set.range u))
        (SubMulAction.ofFixingSubgroup P (Set.range u)) ∧
      ¬ IsMultiplyPretransitive (fixingSubgroup P (Set.range u))
        (SubMulAction.ofFixingSubgroup P (Set.range u)) 2 := by
  have hu : (Set.range u).ncard + 1 = d := by
    rw [Set.ncard_range_of_injective u.injective, Nat.card_fin]
    omega
  have := h₁
  refine ⟨is_one_pretransitive_iff.mp
    (SubMulAction.ofFixingSubgroup.isMultiplyPretransitive P (Set.range u) hu), fun h2 => h₂ ?_⟩
  have : IsMultiplyPretransitive P Φ (d - 1) :=
    isMultiplyPretransitive_of_le (n := d) (by omega) (by rw [Nat.card_eq_fintype_card]; omega)
  have := isMultiplyPretransitive_add_two P u this h2
  rwa [show d - 1 + 2 = d + 1 by omega] at this

/-- **The orbital configuration** of a transitive group that is not doubly transitive is a
homogeneous classical coherent configuration that is not a clique. -/
theorem orbital_config {Φ : Type} [Fintype Φ] [DecidableEq Φ] {P : Type*} [Group P]
    [MulAction P Φ] [IsPretransitive P Φ] (h₂ : ¬ IsMultiplyPretransitive P Φ 2)
    (c : Φ → Φ → ℕ)
    (hc : ∀ u v u' v', c u v = c u' v' ↔ ∃ g : P, g • u = u' ∧ g • v = v') :
    IsCoh2On Finset.univ c ∧ IsHomog Finset.univ c ∧ ¬ IsClique c Finset.univ := by
  -- the colours are the orbitals: `P` preserves them
  have hg : ∀ (g : P) (u v : Φ), c (g • u) (g • v) = c u v :=
    fun g u v => ((hc u v _ _).mpr ⟨g, rfl, rfl⟩).symm
  refine ⟨⟨fun x y x' y' hxy => ?_, fun x y x' y' hxy r s => ?_⟩, fun x _ y _ => ?_,
    fun hcl => h₂ ?_⟩
  · obtain ⟨g, hx, hy⟩ := (hc x y x' y').mp hxy
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [Subtype.ext_iff, Subtype.ext_iff, ← hx, ← hy, smul_left_cancel_iff]
    · exact (hc _ _ _ _).mpr ⟨g, hy, hx⟩
    · exact (hc _ _ _ _).mpr ⟨g, hx, hx⟩
    · exact (hc _ _ _ _).mpr ⟨g, hy, hy⟩
  · -- `g` maps the points counted for `(x, y)` to those counted for `(x', y')`
    obtain ⟨g, hx, hy⟩ := (hc x y x' y').mp hxy
    refine Finset.card_nbij' (fun z => ⟨g • (z : Φ), Finset.mem_univ _⟩)
      (fun z => ⟨g⁻¹ • (z : Φ), Finset.mem_univ _⟩) (fun z hz => ?_) (fun z hz => ?_)
      (fun z _ => Subtype.ext (inv_smul_smul g (z : Φ)))
      (fun z _ => Subtype.ext (smul_inv_smul g (z : Φ)))
    · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hz ⊢
      rw [← hx, ← hy, hg, hg]
      exact hz
    · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hz ⊢
      rw [← hg g, ← hg g _ (y : Φ), smul_inv_smul, hx, hy]
      exact hz
  · obtain ⟨g, hxy⟩ := exists_smul_eq P x y
    exact (hc x x y y).mpr ⟨g, hxy, hxy⟩
  · -- a clique would make `P` doubly transitive
    rw [is_two_pretransitive_iff]
    intro a b a' b' hab hab'
    exact (hc a b a' b').mp (hcl a (Finset.mem_univ _) b (Finset.mem_univ _) a'
      (Finset.mem_univ _) b' (Finset.mem_univ _) hab hab')

end GraphIso.Certificates
