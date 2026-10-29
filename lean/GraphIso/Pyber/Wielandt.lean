module

public import GraphIso.Pyber.Orbital
public import GraphIso.Pyber.Residual
public import Mathlib.GroupTheory.GroupAction.SubMulAction.OfFixingSubgroup

/-!
# Wielandt's Lemma 4, self-paired form

Stage 15c. `G` acts faithfully and primitively on `Ω`, and `x ≠ y` with the orbital
`O = orbit G (x, y)` self-paired: `(y, x) ∈ O`. For a point `a`, `T(a)` (`suborbitKer G x y a`)
is the subgroup fixing `a` and every point of the suborbit `{b | (a, b) ∈ O}` at `a`. Let
`G_{xy} = G_x ∩ G_y` and `S = compA (G_{xy} ⧸ T(x))`.

* **Wielandt's Lemma 4** (`compA_suborbitKer_subset`): `compA T(x) ⊆ S`. With `R(a)` the
  residual of `T(a)` for the class `compA ⊆ S` (15a item 6):
  - `G_{xy} ≥ T(x)` and `G_{xy} ≥ T(y)` are one-step chains: the first by the definition of
    `S`, the second by conjugating with an element exchanging `x` and `y` (self-pairing);
  - so `R(x) = resid S G_{xy} = R(y)`, and by equivariance `R(a) = R(b)` for every `(a, b) ∈ O`;
  - by the connectivity lemma `R(a) = R(x)` for every `a`, so `R(x)` fixes every point, and
    `R(x) = ⊥` by faithfulness.
* **The corollary** (Pyber's `(∗)`, `compA_stabilizer_subset`): with `P` the image of `G_x` in
  `Perm Δ(x)` and `P_y` the stabilizer of `y` in `P`, `compA G_x ⊆ compA P ∪ compA P_y`. Here
  `T(x)` is the kernel of `G_x → P`, and `G_{xy} ⧸ T(x) ≅ P_y`.
-/

@[expose] public section

namespace GraphIso.Pyber

open Subgroup MulAction
open scoped Pointwise

variable {G Ω : Type*} [Group G] [MulAction G Ω]

/-- **The kernel at `a`:** the elements fixing `a` and the suborbit `{b | (a, b) ∈ O}` at `a` of
the orbital `O` of `(x, y)` pointwise. -/
def suborbitKer (G : Type*) [Group G] [MulAction G Ω] (x y a : Ω) : Subgroup G :=
  fixingSubgroup G (insert a {b | (a, b) ∈ orbit G (x, y)})

theorem mem_suborbitKer {x y a : Ω} {g : G} :
    g ∈ suborbitKer G x y a ↔ g • a = a ∧ ∀ b, (a, b) ∈ orbit G (x, y) → g • b = b := by
  rw [suborbitKer, mem_fixingSubgroup_iff]
  constructor
  · intro h
    exact ⟨h a (Set.mem_insert _ _), fun b hb => h b (Set.mem_insert_of_mem _ hb)⟩
  · rintro ⟨ha, hb⟩ c (rfl | hc)
    · exact ha
    · exact hb c hc

theorem suborbitKer_le {x y a b : Ω} (hab : (a, b) ∈ orbit G (x, y)) :
    suborbitKer G x y a ≤ stabilizer G a ⊓ stabilizer G b := fun _ hg =>
  ⟨(mem_suborbitKer.mp hg).1, (mem_suborbitKer.mp hg).2 b hab⟩

/-- `T(a)` is normal in `G_a ∩ G_b`. -/
theorem suborbitKer_normal {x y a b : Ω} :
    ((suborbitKer G x y a).subgroupOf (stabilizer G a ⊓ stabilizer G b)).Normal := by
  constructor
  intro t ht g
  rw [mem_subgroupOf] at ht ⊢
  have hga : (g : G) • a = a := (mem_inf.mp g.2).1
  rw [mem_suborbitKer] at ht ⊢
  simp only [coe_mul, coe_inv]
  constructor
  · rw [mul_smul, mul_smul, inv_smul_eq_iff.mpr hga.symm, ht.1, hga]
  · intro c hc
    have hc' : (a, (g : G)⁻¹ • c) ∈ orbit G (x, y) := by
      have := smul_mem_orbit_pair hc (g : G)⁻¹
      rwa [inv_smul_eq_iff.mpr hga.symm] at this
    rw [mul_smul, mul_smul, ht.2 _ hc', smul_inv_smul]

instance suborbitKer_normal_self (x y : Ω) :
    ((suborbitKer G x y x).subgroupOf (stabilizer G x ⊓ stabilizer G y)).Normal :=
  suborbitKer_normal

/-- **Equivariance:** `T(g • a) = g T(a) g⁻¹`. -/
theorem suborbitKer_smul (x y a : Ω) (g : G) :
    suborbitKer G x y (g • a) = (suborbitKer G x y a).map (MulAut.conj g).toMonoidHom := by
  have hs : g • insert a {b | (a, b) ∈ orbit G (x, y)} =
      insert (g • a) {b | (g • a, b) ∈ orbit G (x, y)} := by
    ext b
    rw [Set.mem_smul_set_iff_inv_smul_mem, Set.mem_insert_iff, Set.mem_insert_iff,
      Set.mem_ofPred_eq, Set.mem_ofPred_eq, inv_smul_eq_iff]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · right
        have := smul_mem_orbit_pair h g
        rwa [smul_inv_smul] at this
    · rintro (h | h)
      · exact Or.inl h
      · right
        have := smul_mem_orbit_pair h g⁻¹
        rwa [inv_smul_smul] at this
  rw [suborbitKer, suborbitKer, SubMulAction.fixingSubgroup_map_conj_eq hs]

/-- `G_{g a} ∩ G_{g b} = g (G_a ∩ G_b) g⁻¹`. -/
theorem stabilizer_inf_smul (a b : Ω) (g : G) :
    stabilizer G (g • a) ⊓ stabilizer G (g • b) =
      (stabilizer G a ⊓ stabilizer G b).map (MulAut.conj g).toMonoidHom := by
  rw [map_inf _ _ _ (MulAut.conj g).injective, stabilizer_smul_eq_stabilizer_map_conj,
    stabilizer_smul_eq_stabilizer_map_conj]

/-- **A chain does not change the residual:** `SChain S A L → resid S A = resid S L`. -/
theorem resid_eq_of_schain [Finite G] {S : Set ℕ} {A L : Subgroup G} (h : SChain S A L) :
    resid S A = resid S L := by
  induction h with
  | refl => rfl
  | step _ hle hS ih => exact ih.trans (resid_eq_of_step hle hS)

/-- **Wielandt's Lemma 4, self-paired form.** For a faithful primitive action of a finite group,
`x ≠ y`, and the orbital of `(x, y)` self-paired, `compA T(x) ⊆ compA (G_{xy} ⧸ T(x))`. -/
theorem compA_suborbitKer_subset [Finite G] [IsPreprimitive G Ω] (hf : Faithful G Ω) {x y : Ω}
    (hxy : x ≠ y) (hsp : (y, x) ∈ orbit G (x, y)) :
    compA (suborbitKer G x y x) ⊆
      compA (↥(stabilizer G x ⊓ stabilizer G y) ⧸
        (suborbitKer G x y x).subgroupOf (stabilizer G x ⊓ stabilizer G y)) := by
  set S := compA (↥(stabilizer G x ⊓ stabilizer G y) ⧸
    (suborbitKer G x y x).subgroupOf (stabilizer G x ⊓ stabilizer G y))
  set T : Ω → Subgroup G := suborbitKer G x y
  have h1 : SChain S (stabilizer G x ⊓ stabilizer G y) (T x) :=
    .step .refl (suborbitKer_le (mem_orbit_self (x, y))) subset_rfl
  obtain ⟨h, hh⟩ := hsp
  have hx : h • x = y := (Prod.ext_iff.mp hh).1
  have hy : h • y = x := (Prod.ext_iff.mp hh).2
  have h2 : SChain S (stabilizer G x ⊓ stabilizer G y) (T y) := by
    have := h1.map (MulAut.conj h)
    rwa [← stabilizer_inf_smul, hx, hy, inf_comm, ← suborbitKer_smul, hx] at this
  have hR : resid S (T x) = resid S (T y) :=
    (resid_eq_of_schain h1).symm.trans (resid_eq_of_schain h2)
  have hstep : ∀ a b, (a, b) ∈ orbit G (x, y) → resid S (T a) = resid S (T b) := by
    rintro a b ⟨g, hg⟩
    have ha : g • x = a := (Prod.ext_iff.mp hg).1
    have hb : g • y = b := (Prod.ext_iff.mp hg).2
    rw [← ha, ← hb]
    change resid S (suborbitKer G x y (g • x)) = resid S (suborbitKer G x y (g • y))
    rw [suborbitKer_smul, suborbitKer_smul, resid_map, resid_map]
    exact congrArg _ hR
  have hall := eq_univ_of_closed hxy (F := {a | resid S (T a) = resid S (T x)}) rfl
    (fun a b ha hab => (hstep a b hab).symm.trans ha)
  have hbot : resid S (T x) = ⊥ := by
    rw [eq_bot_iff]
    intro r hr
    rw [mem_bot]
    apply hf
    intro a
    have ha : a ∈ {a | resid S (T a) = resid S (T x)} := hall ▸ Set.mem_univ a
    have hr' : r ∈ T a := resid_le_of_schain .refl (show r ∈ resid S (T a) by rw [ha]; exact hr)
    exact (mem_suborbitKer.mp hr').1
  exact compA_subset_of_resid_eq_bot hbot

/-- The kernel of `G_x → Perm Δ(x)` is `T(x)`. -/
theorem ker_toPermHom_suborbit (x y : Ω) :
    (toPermHom (stabilizer G x) (orbit (stabilizer G x) y)).ker =
      (suborbitKer G x y x).subgroupOf (stabilizer G x) := by
  ext g
  rw [MonoidHom.mem_ker, mem_subgroupOf, mem_suborbitKer]
  constructor
  · intro h
    refine ⟨g.2, fun b hb => ?_⟩
    have hb' := mem_orbit_stabilizer_iff.mpr hb
    exact congrArg (fun σ : Equiv.Perm (orbit (stabilizer G x) y) => ((σ ⟨b, hb'⟩ : _) : Ω)) h
  · rintro ⟨-, h⟩
    apply Equiv.ext
    rintro ⟨b, hb⟩
    exact Subtype.ext (h b (mem_orbit_stabilizer_iff.mp hb))

/-- **The corollary of Wielandt's lemma** (Pyber's `(∗)`): for a faithful primitive action of a
finite group, `x ≠ y`, and the orbital of `(x, y)` self-paired,
`compA G_x ⊆ compA P ∪ compA P_y`, where `P` is the image of `G_x` in `Perm Δ(x)` and `P_y` the
stabilizer of `y` in `P`. -/
theorem compA_stabilizer_subset [Finite G] [IsPreprimitive G Ω] (hf : Faithful G Ω) {x y : Ω}
    (hxy : x ≠ y) (hsp : (y, x) ∈ orbit G (x, y)) :
    compA (stabilizer G x) ⊆
      compA (toPermHom (stabilizer G x) (orbit (stabilizer G x) y)).range ∪
        compA (stabilizer (toPermHom (stabilizer G x) (orbit (stabilizer G x) y)).range
          (⟨y, mem_orbit_self y⟩ : orbit (stabilizer G x) y)) := by
  set Δ := orbit (stabilizer G x) y
  set φ := toPermHom (stabilizer G x) Δ
  set y' : Δ := ⟨y, mem_orbit_self y⟩
  have hT : suborbitKer G x y x ≤ stabilizer G x := fun g hg => (mem_suborbitKer.mp hg).1
  -- `compA G_x ⊆ compA T(x) ∪ compA P`
  have h1 := compA_subset_union_of_hom φ.rangeRestrict (by
    rw [MonoidHom.range_eq_top.mpr φ.rangeRestrict_surjective]
    exact IsSubnormal.top)
  rw [compA_eq_of_mulEquiv (MulEquiv.subgroupCongr ((MonoidHom.ker_rangeRestrict φ).trans
    (ker_toPermHom_suborbit x y))), compA_eq_of_mulEquiv (subgroupOfEquivOfLe hT)] at h1
  -- `G_{xy} ⧸ T(x)` maps onto `P_y`
  set f0 : ↥(stabilizer G x ⊓ stabilizer G y) →* φ.range :=
    φ.rangeRestrict.comp (inclusion inf_le_left)
  have hf0 : ∀ g, f0 g ∈ stabilizer φ.range y' := fun g =>
    Subtype.ext (show (g : G) • y = y from (mem_inf.mp g.2).2)
  set f := f0.codRestrict (stabilizer φ.range y') hf0
  have hker : f.ker = (suborbitKer G x y x).subgroupOf (stabilizer G x ⊓ stabilizer G y) := by
    ext g
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    have h2 : f g = 1 ↔ inclusion inf_le_left g ∈ φ.ker := by
      rw [MonoidHom.mem_ker]
      constructor
      · intro h
        exact congrArg (fun σ : stabilizer φ.range y' => ((σ : φ.range) : Equiv.Perm Δ)) h
      · intro h
        exact Subtype.ext (Subtype.ext h)
    rw [h2, ker_toPermHom_suborbit, mem_subgroupOf]
    rfl
  have hsurj : Function.Surjective f := by
    rintro ⟨⟨σ, ⟨g, rfl⟩⟩, hσ⟩
    have hgy : (g : G) • y = y := congrArg Subtype.val hσ
    exact ⟨⟨g, mem_inf.mpr ⟨g.2, hgy⟩⟩, rfl⟩
  have h3 := compA_quot_subset_of_hom f _ hker (by
    rw [MonoidHom.range_eq_top.mpr hsurj]
    exact IsSubnormal.top)
  have h4 := compA_suborbitKer_subset hf hxy hsp
  rw [Set.union_comm] at h1
  exact h1.trans (Set.union_subset_union_right _ (h4.trans h3))

end GraphIso.Pyber
