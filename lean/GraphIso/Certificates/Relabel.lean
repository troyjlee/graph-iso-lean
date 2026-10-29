module

public import GraphIso.Certificates.Local

/-!
# Canonicity of the local certificates

Babai, Thm. 10.1.3 ("the families are canonical") and Prop. 10.1.8 (v). For `σ ∈ G`, the beard
of `(σ • x, φ(σ) • A)` is the beard of `(x, A)` moved by `σ`: the windows are translated by `σ`
and the groups conjugated by `σ` (as subgroups of `G`). Hence giant-ness, fullness and the
certificates of fullness are canonical, and the certificate of non-fullness `M` is conjugated by
the bijection `A → φ(σ) • A` (`certM_relabel`).

The proof transports along `conjStab φ σ A : G_A ≃* G_{φ(σ) • A}`, `g ↦ σ g σ⁻¹`, under which
`ψ` becomes conjugation by the bijection `conjEquivA φ σ A : A → φ(σ) • A` (`psiA_conjStab`),
stabilizers and pointwise stabilizers of `σ • i` and `σ • s` correspond to those of `i` and `s`,
the affected points move by `σ` (`aff_conjStab`), and the window groups of `σ • x` on `σ • W`
correspond to those of `x` on `W` (`autW_conjStab`); induction on the step gives
`beard_conjStab`.
-/

@[expose] public section

namespace GraphIso.Certificates

open Equiv MulAction Pointwise GraphIso.AltQuot

variable {Ω Γ : Type} [Fintype Ω] [DecidableEq Ω] [Fintype Γ] [DecidableEq Γ]
variable {G : Subgroup (Perm Ω)} (φ : G →* Perm Γ) {L : Type*}

/-! ### Conjugation between the stabilizers -/

omit [Fintype Ω] [DecidableEq Ω] [Fintype Γ] in
theorem conj_mem_stabA (σ : G) {A : Finset Γ} (g : stabA φ A) :
    MulAut.conj σ (g : G) ∈ stabA φ (φ σ • A) := by
  have h : φ g • A = A := g.2
  change φ (σ * g * σ⁻¹) • φ σ • A = φ σ • A
  rw [map_mul, map_mul, mul_smul, mul_smul, map_inv, inv_smul_smul, h]

omit [Fintype Ω] [DecidableEq Ω] [Fintype Γ] in
theorem conj_inv_mem_stabA (σ : G) {A : Finset Γ} (g : stabA φ (φ σ • A)) :
    MulAut.conj σ⁻¹ (g : G) ∈ stabA φ A := by
  have h : φ g • φ σ • A = φ σ • A := g.2
  change φ (σ⁻¹ * g * σ⁻¹⁻¹) • A = A
  rw [inv_inv, map_mul, map_mul, mul_smul, mul_smul, h, map_inv, inv_smul_smul]

/-- Conjugation by `σ`, as an isomorphism `G_A ≃* G_{φ(σ) • A}`. -/
def conjStab (σ : G) (A : Finset Γ) : stabA φ A ≃* stabA φ (φ σ • A) where
  toFun g := ⟨MulAut.conj σ (g : G), conj_mem_stabA φ σ g⟩
  invFun g := ⟨MulAut.conj σ⁻¹ (g : G), conj_inv_mem_stabA φ σ g⟩
  left_inv g := Subtype.ext <| by simp [mul_assoc]
  right_inv g := Subtype.ext <| by simp [mul_assoc]
  map_mul' g h := Subtype.ext <| by simp [mul_assoc]

omit [Fintype Ω] [DecidableEq Ω] [Fintype Γ] in
theorem coe_conjStab (σ : G) (A : Finset Γ) (g : stabA φ A) :
    (conjStab φ σ A g : G) = σ * g * σ⁻¹ := rfl

omit [Fintype Ω] [DecidableEq Ω] [Fintype Γ] in
theorem coe_conjStab_symm (σ : G) (A : Finset Γ) (g : stabA φ (φ σ • A)) :
    ((conjStab φ σ A).symm g : G) = σ⁻¹ * g * σ := by
  change σ⁻¹ * (g : G) * σ⁻¹⁻¹ = _
  rw [inv_inv]

omit [Fintype Ω] [DecidableEq Ω] [Fintype Γ] in
/-- In `G`, transporting along `conjStab` is conjugation by `σ`. -/
theorem map_conjStab_subtype (σ : G) (A : Finset Γ) (H : Subgroup (stabA φ A)) :
    (H.map (conjStab φ σ A).toMonoidHom).map (stabA φ (φ σ • A)).subtype =
      (H.map (stabA φ A).subtype).map (MulAut.conj σ).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  rfl

/-- The bijection `A → φ(σ) • A`, `a ↦ φ(σ) a`. -/
def conjEquivA (σ : G) (A : Finset Γ) : A ≃ (φ σ • A : Finset Γ) :=
  (φ σ).subtypeEquiv fun _ => (Finset.smul_mem_smul_finset_iff (φ σ)).symm

omit [Fintype Ω] [DecidableEq Ω] [Fintype Γ] in
/-- `ψ` intertwines conjugation by `σ` and conjugation by `A → φ(σ) • A`. -/
theorem psiA_conjStab (σ : G) (A : Finset Γ) (g : stabA φ A) :
    psiA φ (φ σ • A) (conjStab φ σ A g) = (conjEquivA φ σ A).permCongr (psiA φ A g) := by
  ext b
  simp [psiA, conjStab, conjEquivA, Equiv.permCongr_apply, Perm.inv_def]

omit [Fintype Ω] [DecidableEq Ω] in
/-- Conjugation preserves the alternating group. -/
theorem alternatingGroup_le_map_permCongr {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] (e : α ≃ β) (K : Subgroup (Perm α)) :
    alternatingGroup β ≤ K.map e.permCongrHom.toMonoidHom ↔ alternatingGroup α ≤ K := by
  have h : (alternatingGroup α).map e.permCongrHom.toMonoidHom = alternatingGroup β := by
    simp [Subgroup.ext_iff, Subgroup.map_equiv_eq_comap_symm]
  rw [← h, Subgroup.map_le_map_iff_of_injective e.permCongrHom.injective]

omit [Fintype Ω] [DecidableEq Ω] [Fintype Γ] in
/-- `ψ` maps the transported group to the conjugate of the image. -/
theorem map_conjStab_psiA (σ : G) (A : Finset Γ) (H : Subgroup (stabA φ A)) :
    (H.map (conjStab φ σ A).toMonoidHom).map (psiA φ (φ σ • A)) =
      (H.map (psiA φ A)).map (conjEquivA φ σ A).permCongrHom.toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  exact MonoidHom.ext fun g => psiA_conjStab φ σ A g

omit [Fintype Ω] [DecidableEq Ω] [Fintype Γ] in
theorem isGiantOn_conjStab (σ : G) (A : Finset Γ) (H : Subgroup (stabA φ A)) :
    IsGiantOn φ (φ σ • A) (H.map (conjStab φ σ A).toMonoidHom) ↔ IsGiantOn φ A H := by
  rw [IsGiantOn, IsGiantOn, map_conjStab_psiA, alternatingGroup_le_map_permCongr]

omit [Fintype Ω] [DecidableEq Ω] [Fintype Γ] in
theorem conjStab_symm_smul (σ : G) (A : Finset Γ) (g : stabA φ (φ σ • A)) (i : Ω) :
    (conjStab φ σ A).symm g • i = σ⁻¹ • g • σ • i := by
  rw [Subgroup.smul_def, coe_conjStab_symm, mul_smul, mul_smul]
  rfl

omit [Fintype Ω] [DecidableEq Ω] [Fintype Γ] in
theorem stabilizer_conjStab (σ : G) (A : Finset Γ) (i : Ω) :
    stabilizer (stabA φ (φ σ • A)) (σ • i) =
      (stabilizer (stabA φ A) i).map (conjStab φ σ A).toMonoidHom := by
  ext g
  rw [Subgroup.mem_map_equiv, mem_stabilizer_iff, mem_stabilizer_iff, conjStab_symm_smul,
    inv_smul_eq_iff]

omit [Fintype Ω] [DecidableEq Ω] [Fintype Γ] in
theorem fixingSubgroup_conjStab (σ : G) (A : Finset Γ) (s : Set Ω) :
    fixingSubgroup (stabA φ (φ σ • A)) (σ • s) =
      (fixingSubgroup (stabA φ A) s).map (conjStab φ σ A).toMonoidHom := by
  ext g
  rw [Subgroup.mem_map_equiv, mem_fixingSubgroup_iff, mem_fixingSubgroup_iff]
  constructor
  · intro h i hi
    rw [conjStab_symm_smul, h _ (Set.smul_mem_smul_set hi), inv_smul_smul]
  · intro h j hj
    obtain ⟨i, hi, rfl⟩ := Set.mem_smul_set.1 hj
    have := h i hi
    rwa [conjStab_symm_smul, inv_smul_eq_iff] at this

omit [Fintype Ω] [DecidableEq Ω] [Fintype Γ] in
theorem aff_conjStab (σ : G) (A : Finset Γ) (H : Subgroup (stabA φ A)) :
    aff φ (φ σ • A) (H.map (conjStab φ σ A).toMonoidHom) = σ • aff φ A H := by
  ext i
  obtain ⟨j, rfl⟩ : ∃ j, i = σ • j := ⟨σ⁻¹ • i, (smul_inv_smul σ i).symm⟩
  rw [Set.smul_mem_smul_set_iff]
  change ¬ _ ↔ ¬ _
  rw [stabilizer_conjStab, ← Subgroup.map_inf _ _ _ (conjStab φ σ A).injective]
  exact not_congr (isGiantOn_conjStab φ σ A _)

omit [Fintype Ω] [DecidableEq Ω] [Fintype Γ] in
theorem autW_conjStab (σ : G) (A : Finset Γ) (H : Subgroup (stabA φ A)) (W : Set Ω)
    (x : Ω → L) :
    autW (H.map (conjStab φ σ A).toMonoidHom) (σ • W) (smulStr σ x) =
      (autW H W x).map (conjStab φ σ A).toMonoidHom := by
  ext g
  have mem : ∀ {M : Type} [Group M] [MulAction M Ω] (K : Subgroup M) (V : Set Ω) (y : Ω → L)
      (h : M), h ∈ autW K V y ↔ h ∈ K ∧ h • V = V ∧ ∀ i ∈ V, y (h • i) = y i :=
    fun _ _ _ _ => Iff.rfl
  rw [Subgroup.mem_map_equiv, mem, mem]
  simp only [smulStr]
  have hW : (conjStab φ σ A).symm g • W = σ⁻¹ • g • σ • W := by
    rw [← Set.image_smul, ← Set.image_smul, ← Set.image_smul, ← Set.image_smul,
      Set.image_image, Set.image_image]
    exact Set.image_congr fun i _ => conjStab_symm_smul φ σ A g i
  rw [Subgroup.mem_map_equiv, hW, inv_smul_eq_iff]
  refine and_congr Iff.rfl (and_congr Iff.rfl ⟨fun h i hi => ?_, fun h j hj => ?_⟩)
  · have := h _ (Set.smul_mem_smul_set hi)
    rwa [inv_smul_smul, ← conjStab_symm_smul] at this
  · obtain ⟨i, hi, rfl⟩ := Set.mem_smul_set.1 hj
    have := h i hi
    rw [conjStab_symm_smul] at this
    rwa [inv_smul_smul]

/-! ### The beard under conjugation -/

omit [Fintype Ω] [DecidableEq Ω] [Fintype Γ] in
theorem beardStep_conjStab (σ : G) (A : Finset Γ) (x : Ω → L) (W : Set Ω)
    (H : Subgroup (stabA φ A)) :
    beardStep φ (φ σ • A) (smulStr σ x) (σ • W, H.map (conjStab φ σ A).toMonoidHom) =
      (σ • (beardStep φ A x (W, H)).1,
        (beardStep φ A x (W, H)).2.map (conjStab φ σ A).toMonoidHom) := by
  have hW : σ • W ∪ {i | IsGiantOn φ (φ σ • A) (H.map (conjStab φ σ A).toMonoidHom) ∧
        i ∈ aff φ (φ σ • A) (H.map (conjStab φ σ A).toMonoidHom)} =
      σ • (W ∪ {i | IsGiantOn φ A H ∧ i ∈ aff φ A H}) := by
    rw [isGiantOn_conjStab, aff_conjStab, Set.smul_set_union]
    congr 1
    ext i
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    exact and_congr Iff.rfl Set.mem_smul_set_iff_inv_smul_mem
  simp only [beardStep, hW, autW_conjStab]

omit [Fintype Ω] [DecidableEq Ω] [Fintype Γ] in
/-- The beard of `(σ • x, φ(σ) • A)` is the beard of `(x, A)` transported by `σ`. -/
theorem beard_conjStab (σ : G) (A : Finset Γ) (x : Ω → L) (n : ℕ) :
    beard φ (φ σ • A) (smulStr σ x) n =
      (σ • (beard φ A x n).1, (beard φ A x n).2.map (conjStab φ σ A).toMonoidHom) := by
  induction n with
  | zero =>
    change ((∅ : Set Ω), (⊤ : Subgroup _)) = (σ • (∅ : Set Ω), (⊤ : Subgroup _).map _)
    rw [Set.smul_set_empty, Subgroup.map_top_of_surjective _ (conjStab φ σ A).surjective]
  | succ n ih =>
    have hs : ∀ (B : Finset Γ) (y : Ω → L),
        beard φ B y (n + 1) = beardStep φ B y (beard φ B y n) :=
      fun _ _ => Function.iterate_succ_apply' _ _ _
    rw [hs, ih, beardStep_conjStab, ← hs]

omit [DecidableEq Ω] [Fintype Γ] in
theorem beardH_conjStab (σ : G) (A : Finset Γ) (x : Ω → L) :
    beardH φ (φ σ • A) (smulStr σ x) = (beardH φ A x).map (conjStab φ σ A).toMonoidHom :=
  congrArg Prod.snd (beard_conjStab φ σ A x _)

omit [DecidableEq Ω] [Fintype Γ] in
theorem beardW_conjStab (σ : G) (A : Finset Γ) (x : Ω → L) :
    beardW φ (φ σ • A) (smulStr σ x) = σ • beardW φ A x :=
  congrArg Prod.fst (beard_conjStab φ σ A x _)

/-! ### Canonicity -/

omit [Fintype Ω] [DecidableEq Ω] [Fintype Γ] in
/-- **The beard is canonical.** -/
theorem beard_relabel (σ : G) (A : Finset Γ) (x : Ω → L) (n : ℕ) :
    (beard φ (φ σ • A) (smulStr σ x) n).1 = σ • (beard φ A x n).1 ∧
      ((beard φ (φ σ • A) (smulStr σ x) n).2).map (stabA φ (φ σ • A)).subtype =
        (((beard φ A x n).2).map (stabA φ A).subtype).map (MulAut.conj σ).toMonoidHom := by
  rw [beard_conjStab]
  exact ⟨rfl, map_conjStab_subtype φ σ A _⟩

omit [DecidableEq Ω] [Fintype Γ] in
/-- **Giant-ness of the final group is canonical.** -/
theorem isGiantOn_relabel (σ : G) (A : Finset Γ) (x : Ω → L) :
    IsGiantOn φ (φ σ • A) (beardH φ (φ σ • A) (smulStr σ x)) ↔
      IsGiantOn φ A (beardH φ A x) := by
  rw [beardH_conjStab, isGiantOn_conjStab]

omit [Fintype Ω] [DecidableEq Ω] [Fintype Γ] in
/-- **Fullness is canonical.** -/
theorem isFull_relabel (σ : G) (A : Finset Γ) (x : Ω → L) :
    IsFull φ (φ σ • A) (smulStr σ x) ↔ IsFull φ A x := by
  have h : autW (⊤ : Subgroup (stabA φ (φ σ • A))) Set.univ (smulStr σ x) =
      (autW (⊤ : Subgroup (stabA φ A)) Set.univ x).map (conjStab φ σ A).toMonoidHom := by
    rw [← autW_conjStab, Set.smul_set_univ,
      Subgroup.map_top_of_surjective _ (conjStab φ σ A).surjective]
  change IsGiantOn φ (φ σ • A) _ ↔ IsGiantOn φ A _
  rw [h, isGiantOn_conjStab]

omit [DecidableEq Ω] [Fintype Γ] in
/-- **The certificate of fullness is canonical.** -/
theorem certK_relabel (σ : G) (A : Finset Γ) (x : Ω → L) :
    (certK φ (φ σ • A) (smulStr σ x)).map (stabA φ (φ σ • A)).subtype =
      ((certK φ A x).map (stabA φ A).subtype).map (MulAut.conj σ).toMonoidHom := by
  rw [← map_conjStab_subtype, certK, certK, beardH_conjStab, beardW_conjStab, ← Set.smul_set_compl,
    fixingSubgroup_conjStab, ← Subgroup.map_inf _ _ _ (conjStab φ σ A).injective]

omit [DecidableEq Ω] [Fintype Γ] in
/-- **The certificate of non-fullness is canonical**: `M` is conjugated by the bijection
`A → φ(σ) • A`. -/
theorem certM_relabel (σ : G) (A : Finset Γ) (x : Ω → L) :
    certM φ (φ σ • A) (smulStr σ x) =
      (certM φ A x).map (conjEquivA φ σ A).permCongrHom.toMonoidHom := by
  rw [certM, certM, beardH_conjStab, map_conjStab_psiA]

end GraphIso.Certificates
