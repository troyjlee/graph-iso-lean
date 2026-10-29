module

public import Mathlib.RepresentationTheory.Maschke
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Data.Finite.Perm
public import Mathlib.RingTheory.IntegralDomain
public import Mathlib.Algebra.Field.ZMod

/-!
# Linear `r`-groups in characteristic `p ≠ r`

* `card_le_of_isPGroup`: if `r ≠ p` and `R` is an `r`-subgroup of `GL(V)` for a nonzero finite
  `ZMod p`-vector space `V`, then `2 |R| ≤ |V|³`.
* `card_le_of_isPGroup'`: `|R| ≤ |V|³`, also for `V = 0`.

The proof is by strong induction on `|V|`. Let `A` be a maximal abelian normal subgroup of `R`,
and `B ⊆ End(V)` the algebra it generates: commutative, and reduced by Maschke's theorem
(`isReduced_adjoin_range`), so a product of fields over its maximal ideals. Its idempotents
split `V` into the subspaces `V_𝔪` killed by the maximal ideals (`card_eq_prod_zeroSpace`), and
`R` permutes the maximal ideals by conjugation (`apply_mem_zeroSpace_maxAct`).

* With at least two maximal ideals, the kernel of the permutation action embeds in
  `∏ GL(V_𝔪)`, bounded by induction; the image in `Sym(t)` is an `r`-group of order at most
  `2^{t-1}` (`card_le_two_pow_of_isPGroup_perm`).
* With one, `B` is a field, so `A` is cyclic of order `< |V|`; `A` is self-centralizing
  (`centralizer_le_of_maximal`), so `|R| ≤ |A| |Aut A| ≤ |A|²`.
-/

@[expose] public section

namespace GraphIso.Groups

open LinearMap
open scoped IsMulCommutative

universe u

/-- `r ≤ 2 ^ (r - 1)`. -/
theorem le_two_pow_pred (r : ℕ) : r ≤ 2 ^ (r - 1) := by
  have := Nat.lt_two_pow_self (n := r - 1)
  omega

/-- **`r`-subgroups of `Sym(t)`** have order at most `2 ^ (t - 1)`, by Legendre's formula. -/
theorem card_le_two_pow_of_isPGroup_perm {r : ℕ} [hr : Fact r.Prime] {X : Type*} [Finite X]
    (P : Subgroup (Equiv.Perm X)) (hP : IsPGroup r P) :
    Nat.card P ≤ 2 ^ (Nat.card X - 1) := by
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 hP
  have hdvd : r ^ a ∣ (Nat.card X).factorial := by
    rw [← ha, ← Nat.card_perm]
    exact P.card_subgroup_dvd_card
  have hv : a ≤ padicValNat r (Nat.card X).factorial :=
    (padicValNat_dvd_iff_le (Nat.factorial_ne_zero _)).1 hdvd
  have hleg := sub_one_mul_padicValNat_factorial (p := r) (Nat.card X)
  have hle : (r - 1) * a ≤ Nat.card X - 1 := by
    rcases Nat.eq_zero_or_pos (Nat.card X) with h0 | hpos
    · rw [h0] at hdvd
      have : r ^ a ≤ 1 := Nat.le_of_dvd one_pos (by simpa using hdvd)
      have ha0 : a = 0 := by
        by_contra hne
        have : r ≤ r ^ a := Nat.le_self_pow hne r
        have := hr.out.two_le
        omega
      simp [ha0]
    · have hsum : 1 ≤ (r.digits (Nat.card X)).sum := by
        have hne : r.digits (Nat.card X) ≠ [] := Nat.digits_ne_nil_iff_ne_zero.2 (by omega)
        have hlast := Nat.getLast_digit_ne_zero r (show Nat.card X ≠ 0 by omega)
        have hmem : (r.digits (Nat.card X)).getLast hne ∈ r.digits (Nat.card X) :=
          List.getLast_mem hne
        have := List.le_sum_of_mem hmem
        omega
      calc (r - 1) * a ≤ (r - 1) * padicValNat r (Nat.card X).factorial :=
            Nat.mul_le_mul_left _ hv
        _ ≤ Nat.card X - 1 := by omega
  calc Nat.card P = r ^ a := ha
    _ ≤ (2 ^ (r - 1)) ^ a := Nat.pow_le_pow_left (le_two_pow_pred r) a
    _ = 2 ^ ((r - 1) * a) := by rw [← pow_mul]
    _ ≤ 2 ^ (Nat.card X - 1) := Nat.pow_le_pow_right (by norm_num) hle

/-- A nontrivial normal subgroup of a finite `r`-group contains a nontrivial central element. -/
theorem exists_mem_center_of_normal {r : ℕ} [Fact r.Prime] {Q : Type*} [Group Q] [Finite Q]
    (hQ : IsPGroup r Q) (D : Subgroup Q) [D.Normal] (hD : D ≠ ⊥) :
    ∃ d ∈ D, d ≠ 1 ∧ d ∈ Subgroup.center Q := by
  let _ : MulAction Q D := MulAction.compHom D (MulAut.conjNormal (H := D))
  have hdvd : r ∣ Nat.card D :=
    ((hQ.to_subgroup D).card_eq_or_dvd).resolve_left fun h => hD (Subgroup.card_eq_one.1 h)
  have h1 : (1 : D) ∈ MulAction.fixedPoints Q D := by
    intro q
    apply Subtype.ext
    change q * 1 * q⁻¹ = 1
    group
  obtain ⟨b, hb, hne⟩ := hQ.exists_fixed_point_of_prime_dvd_card_of_fixed_point D hdvd h1
  refine ⟨b, b.2, fun h => hne (Subtype.ext h.symm), ?_⟩
  rw [Subgroup.mem_center_iff]
  intro q
  have := congrArg Subtype.val (hb q)
  change q * b * q⁻¹ = b at this
  calc q * (b : Q) = q * b * q⁻¹ * q := by group
    _ = b * q := by rw [this]

/-- **A maximal abelian normal subgroup of a finite `r`-group is self-centralizing.** -/
theorem centralizer_le_of_maximal {r : ℕ} [Fact r.Prime] {G : Type*} [Group G] [Finite G]
    (hG : IsPGroup r G) (A : Subgroup G) [hAn : A.Normal]
    (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hmax : ∀ A' : Subgroup G, A'.Normal → (∀ x ∈ A', ∀ y ∈ A', x * y = y * x) → A ≤ A' →
      A' ≤ A) :
    Subgroup.centralizer (A : Set G) ≤ A := by
  by_contra hC
  set π := QuotientGroup.mk' A
  set D := (Subgroup.centralizer (A : Set G)).map π
  have : D.Normal := Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective A)
  have hD : D ≠ ⊥ := by
    obtain ⟨x, hxC, hxA⟩ := Set.not_subset.1 hC
    intro h
    have : π x ∈ D := Subgroup.mem_map_of_mem π hxC
    rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    exact hxA this
  obtain ⟨d, hdD, hd1, hdc⟩ := exists_mem_center_of_normal (hG.to_quotient A) D hD
  obtain ⟨x, hxC, rfl⟩ := Subgroup.mem_map.1 hdD
  set A' := (Subgroup.zpowers (π x)).comap π
  have hA'n : A'.Normal := by
    refine Subgroup.Normal.comap ⟨fun n hn g => ?_⟩ π
    have hnc : n ∈ Subgroup.center (G ⧸ A) :=
      Subgroup.zpowers_le.2 hdc hn
    rw [Subgroup.mem_center_iff] at hnc
    rw [hnc g, mul_inv_cancel_right]
    exact hn
  -- elements of `A'` are `x ^ i * a` with `a ∈ A`
  have hdec : ∀ y ∈ A', ∃ i : ℤ, ∃ a ∈ A, y = x ^ i * a := by
    intro y hy
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (Subgroup.mem_comap.1 hy)
    refine ⟨i, (x ^ i)⁻¹ * y, ?_, by group⟩
    have : π ((x ^ i)⁻¹ * y) = 1 := by rw [map_mul, map_inv, map_zpow, hi, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff _).1 this
  have hxa : ∀ a ∈ A, ∀ i : ℤ, a * x ^ i = x ^ i * a := by
    intro a ha i
    have hc : Commute a x := Subgroup.mem_centralizer_iff.1 hxC a ha
    exact (hc.zpow_right i).eq
  have hA'c : ∀ y ∈ A', ∀ z ∈ A', y * z = z * y := by
    intro y hy z hz
    obtain ⟨i, a, ha, rfl⟩ := hdec y hy
    obtain ⟨j, b, hb, rfl⟩ := hdec z hz
    calc x ^ i * a * (x ^ j * b) = x ^ i * (a * x ^ j) * b := by group
      _ = x ^ i * (x ^ j * a) * b := by rw [hxa a ha j]
      _ = x ^ (i + j) * (a * b) := by rw [zpow_add]; group
      _ = x ^ (j + i) * (b * a) := by rw [add_comm, hAc a ha b hb]
      _ = x ^ j * (b * x ^ i) * a := by
          rw [zpow_add, hxa b hb i]; group
      _ = x ^ j * b * (x ^ i * a) := by group
  have hAA' : A ≤ A' := by
    intro a ha
    refine Subgroup.mem_comap.2 ?_
    rw [show π a = 1 from (QuotientGroup.eq_one_iff a).2 ha]
    exact Subgroup.one_mem _
  have hxA' : x ∈ A' := Subgroup.mem_comap.2 (Subgroup.mem_zpowers _)
  have hxA : x ∈ A := hmax A' hA'n hA'c hAA' hxA'
  exact hd1 ((QuotientGroup.eq_one_iff x).2 hxA)

/-- An element whose conjugation action on a normal subgroup is trivial centralizes it. -/
theorem mem_centralizer_of_conjNormal_eq_one {G : Type*} [Group G] {N : Subgroup G} [N.Normal]
    {g : G} (h : MulAut.conjNormal (H := N) g = 1) : g ∈ Subgroup.centralizer (N : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro n hn
  have := congrArg Subtype.val (DFunLike.congr_fun h ⟨n, hn⟩)
  simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
  calc n * g = g * n * g⁻¹ * g := by rw [this]
    _ = g * n := by group

section Field

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]

/-- **The algebra generated by a group of order invertible in `F` with commuting image is
reduced**: it is a quotient of the group algebra, semisimple by Maschke's theorem. -/
theorem isReduced_adjoin_range {A : Type*} [Group A] [Finite A] [NeZero (Nat.card A : F)]
    (f : A →* Module.End F V) (hf : (Set.range f).Pairwise Commute) :
    IsReduced (Algebra.adjoin F (Set.range f)) := by
  have := Algebra.isMulCommutative_adjoin F hf
  set B := Algebra.adjoin F (Set.range f)
  let f' : A →* B :=
    { toFun := fun a => ⟨f a, Algebra.subset_adjoin ⟨a, rfl⟩⟩
      map_one' := Subtype.ext (map_one f)
      map_mul' := fun a b => Subtype.ext (map_mul f a b) }
  let φ := MonoidAlgebra.lift F B A f'
  have hsurj : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      exact ⟨MonoidAlgebra.of F A a, by simp [φ, f']⟩
    | algebraMap c => exact ⟨algebraMap F _ c, by rw [AlgHom.commutes]; rfl⟩
    | add x y hx hy ihx ihy =>
      obtain ⟨u, hu⟩ := ihx
      obtain ⟨w, hw⟩ := ihy
      exact ⟨u + w, by rw [map_add, hu, hw]; rfl⟩
    | mul x y hx hy ihx ihy =>
      obtain ⟨u, hu⟩ := ihx
      obtain ⟨w, hw⟩ := ihy
      exact ⟨u * w, by rw [map_mul, hu, hw]; rfl⟩
  have : IsSemisimpleRing B := RingHom.isSemisimpleRing_of_surjective φ.toRingHom hsurj
  infer_instance

section Decomposition

variable (B : Subalgebra F (Module.End F V)) [IsMulCommutative B]

/-- The subspace killed by an ideal of `B`. -/
def zeroSpace (I : Ideal B) : Submodule F V where
  carrier := {v | ∀ b ∈ I, (b : Module.End F V) v = 0}
  add_mem' {v w} hv hw b hb := by
    simp only [Set.mem_ofPred_eq] at hv hw ⊢
    rw [map_add, hv b hb, hw b hb, add_zero]
  zero_mem' b _ := map_zero _
  smul_mem' c v hv b hb := by
    simp only [Set.mem_ofPred_eq] at hv ⊢
    rw [map_smul, hv b hb, smul_zero]

omit [IsMulCommutative B] in
theorem mem_zeroSpace {I : Ideal B} {v : V} :
    v ∈ zeroSpace B I ↔ ∀ b ∈ I, (b : Module.End F V) v = 0 := Iff.rfl

/-- **Idempotents of a reduced finite commutative algebra**, one for each maximal ideal. -/
theorem exists_idempotents [Finite B] [IsReduced B] [Fintype (MaximalSpectrum B)] :
    ∃ e : MaximalSpectrum B → B, (∀ I J, I ≠ J → e I * e J = 0) ∧ ∑ I, e I = 1 ∧
      (∀ I, ∀ b ∈ I.asIdeal, b * e I = 0) ∧ (∀ I, 1 - e I ∈ I.asIdeal) ∧ ∀ I, e I ≠ 0 := by
  classical
  set φ := IsArtinianRing.equivPi B
  refine ⟨fun I => φ.symm (Pi.single I 1), fun I J hIJ => ?_, ?_, fun I b hb => ?_,
    fun I => ?_, fun I => ?_⟩
  · have h0 : (Pi.single I 1 : ∀ K : MaximalSpectrum B, B ⧸ K.asIdeal) * Pi.single J 1 = 0 := by
      funext K
      rw [Pi.mul_apply, Pi.zero_apply]
      by_cases hK : K = I
      · subst hK
        rw [Pi.single_eq_of_ne hIJ, mul_zero]
      · rw [Pi.single_eq_of_ne hK, zero_mul]
    simp only
    rw [← map_mul, h0, map_zero]
  · rw [← map_sum, Finset.univ_sum_single (fun _ => (1 : B ⧸ _)), ← Pi.one_def, map_one]
  · apply φ.injective
    rw [map_mul, AlgEquiv.apply_symm_apply, map_zero]
    funext J
    rw [Pi.mul_apply, Pi.zero_apply]
    by_cases h : J = I
    · subst h
      rw [IsArtinianRing.equivPi_apply, Ideal.Quotient.eq_zero_iff_mem.2 hb, zero_mul]
    · rw [Pi.single_eq_of_ne h, mul_zero]
  · rw [← Ideal.Quotient.eq_zero_iff_mem]
    have := congrFun (φ.apply_symm_apply (Pi.single I 1)) I
    rw [IsArtinianRing.equivPi_apply] at this
    rw [map_sub, map_one, this, Pi.single_eq_same, sub_self]
  · intro h
    simp only at h
    have := congrFun (φ.apply_symm_apply (Pi.single I 1)) I
    rw [h, map_zero, Pi.zero_apply, Pi.single_eq_same] at this
    exact zero_ne_one this

variable {B} [Fintype (MaximalSpectrum B)] {e : MaximalSpectrum B → B}

theorem idem_apply_idem (h1 : ∀ I J, I ≠ J → e I * e J = 0) (h2 : ∑ I, e I = 1)
    (I : MaximalSpectrum B) (v : V) :
    (e I : Module.End F V) ((e I : Module.End F V) v) = (e I : Module.End F V) v := by
  classical
  have : e I * e I = e I := by
    calc e I * e I = ∑ J, e I * e J := by
          rw [Finset.sum_eq_single I (fun J _ hJ => h1 I J (Ne.symm hJ)) (by simp)]
      _ = e I := by rw [← Finset.mul_sum, h2, mul_one]
  rw [← Module.End.mul_apply, ← Subalgebra.coe_mul, this]

omit [Fintype (MaximalSpectrum B)] in
theorem apply_mem_zeroSpace (h3 : ∀ I, ∀ b ∈ I.asIdeal, b * e I = 0) (I : MaximalSpectrum B)
    (v : V) : (e I : Module.End F V) v ∈ zeroSpace B I.asIdeal := by
  intro b hb
  rw [← Module.End.mul_apply, ← Subalgebra.coe_mul, h3 I b hb]
  rfl

omit [Fintype (MaximalSpectrum B)] in
theorem mem_zeroSpace_iff (h3 : ∀ I, ∀ b ∈ I.asIdeal, b * e I = 0)
    (h4 : ∀ I, 1 - e I ∈ I.asIdeal) {I : MaximalSpectrum B} {v : V} :
    v ∈ zeroSpace B I.asIdeal ↔ (e I : Module.End F V) v = v := by
  constructor
  · intro hv
    have := hv _ (h4 I)
    rw [Subalgebra.coe_sub, Subalgebra.coe_one, LinearMap.sub_apply, Module.End.one_apply,
      sub_eq_zero] at this
    exact this.symm
  · intro hv
    rw [← hv]
    exact apply_mem_zeroSpace h3 I v

theorem sum_idem_apply (h2 : ∑ I, e I = 1) (v : V) : ∑ I, (e I : Module.End F V) v = v := by
  have hs : ((∑ I, e I : B) : Module.End F V) = ∑ I, (e I : Module.End F V) :=
    map_sum B.val _ _
  calc ∑ I, (e I : Module.End F V) v = (∑ I, (e I : Module.End F V)) v :=
        (LinearMap.sum_apply _ _ _).symm
    _ = ((∑ I, e I : B) : Module.End F V) v := by rw [hs]
    _ = v := by rw [h2]; rfl

omit [Fintype (MaximalSpectrum B)] in
theorem idem_apply_eq_zero (h1 : ∀ I J, I ≠ J → e I * e J = 0)
    (h3 : ∀ I, ∀ b ∈ I.asIdeal, b * e I = 0) (h4 : ∀ I, 1 - e I ∈ I.asIdeal)
    {I J : MaximalSpectrum B} (hIJ : I ≠ J) {v : V} (hv : v ∈ zeroSpace B J.asIdeal) :
    (e I : Module.End F V) v = 0 := by
  rw [← (mem_zeroSpace_iff h3 h4).1 hv, ← Module.End.mul_apply, ← Subalgebra.coe_mul,
    h1 I J hIJ]
  rfl

omit [Fintype (MaximalSpectrum B)] in
theorem zeroSpace_ne_bot (h3 : ∀ I, ∀ b ∈ I.asIdeal, b * e I = 0) (h5 : ∀ I, e I ≠ 0)
    (I : MaximalSpectrum B) : zeroSpace B I.asIdeal ≠ ⊥ := by
  intro hbot
  apply h5 I
  apply Subtype.ext
  ext v
  have := apply_mem_zeroSpace h3 I v
  rw [hbot, Submodule.mem_bot] at this
  exact this

/-- **The decomposition `V = ⊕ V_𝔪`**, counted: `|V| = ∏ |V_𝔪|`. -/
theorem card_eq_prod_zeroSpace [Finite V] (h1 : ∀ I J, I ≠ J → e I * e J = 0)
    (h2 : ∑ I, e I = 1) (h3 : ∀ I, ∀ b ∈ I.asIdeal, b * e I = 0)
    (h4 : ∀ I, 1 - e I ∈ I.asIdeal) :
    Nat.card V = ∏ I : MaximalSpectrum B, Nat.card (zeroSpace B I.asIdeal) := by
  classical
  let φ : V ≃ ∀ I : MaximalSpectrum B, zeroSpace B I.asIdeal :=
    { toFun := fun v I => ⟨(e I : Module.End F V) v, apply_mem_zeroSpace h3 I v⟩
      invFun := fun w => ∑ I, (w I : V)
      left_inv := fun v => sum_idem_apply h2 v
      right_inv := fun w => by
        funext I
        apply Subtype.ext
        simp only
        rw [map_sum, Finset.sum_eq_single I
          (fun J _ hJ => idem_apply_eq_zero h1 h3 h4 (Ne.symm hJ) (w J).2) (by simp)]
        exact (mem_zeroSpace_iff h3 h4).1 (w I).2 }
  rw [Nat.card_congr φ, Nat.card_pi]

end Decomposition

section Conjugation

variable {R : Subgroup (GeneralLinearGroup F V)} (A : Subgroup R)

/-- The elements of `A` as endomorphisms of `V`. -/
def gensOf : A →* Module.End F V :=
  (Units.coeHom (Module.End F V)).comp (R.subtype.comp A.subtype)

/-- The algebra generated by `A`. -/
abbrev algOf : Subalgebra F (Module.End F V) := Algebra.adjoin F (Set.range (gensOf A))

theorem pairwise_commute_gensOf (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) :
    (Set.range (gensOf A)).Pairwise Commute := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ _
  change gensOf A a * gensOf A b = gensOf A b * gensOf A a
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (hAc a a.2 b b.2)

/-- Conjugation by an element of `GL(V)`, on endomorphisms. -/
def conjEnd (g : GeneralLinearGroup F V) : Module.End F V →ₐ[F] Module.End F V :=
  (LinearEquiv.conjAlgEquiv F (GeneralLinearGroup.toLinearEquiv g)).toAlgHom

theorem conjEnd_apply (g : GeneralLinearGroup F V) (x : Module.End F V) :
    conjEnd g x = (g : Module.End F V) * x * ((g⁻¹ : GeneralLinearGroup F V) : Module.End F V) :=
  rfl

variable {A}

theorem conjEnd_mem_algOf [A.Normal] (g : R) {x : Module.End F V} (hx : x ∈ algOf A) :
    conjEnd (g : GeneralLinearGroup F V) x ∈ algOf A := by
  have hS : conjEnd (g : GeneralLinearGroup F V) '' Set.range (gensOf A) ⊆
      Set.range (gensOf A) := by
    rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    refine ⟨⟨g * a * g⁻¹, Subgroup.Normal.conj_mem inferInstance _ a.2 g⟩, ?_⟩
    rw [conjEnd_apply]
    simp [gensOf, Units.val_mul]
  have : (algOf A).map (conjEnd (g : GeneralLinearGroup F V)) ≤ algOf A := by
    rw [AlgHom.map_adjoin]
    exact Algebra.adjoin_mono hS
  exact this ⟨x, hx, rfl⟩

/-- Conjugation by an element of `R`, on the algebra generated by `A`. -/
def conjB [A.Normal] (g : R) : algOf A →ₐ[F] algOf A :=
  ((conjEnd (g : GeneralLinearGroup F V)).comp (algOf A).val).codRestrict (algOf A)
    fun b => conjEnd_mem_algOf g b.2

theorem coe_conjB [A.Normal] (g : R) (b : algOf A) :
    (conjB g b : Module.End F V) = ((g : GeneralLinearGroup F V) : Module.End F V) * b *
      (((g : GeneralLinearGroup F V))⁻¹ : GeneralLinearGroup F V) :=
  rfl

theorem conjB_mul [A.Normal] (g h : R) (b : algOf A) : conjB (g * h) b = conjB g (conjB h b) := by
  apply Subtype.ext
  simp only [coe_conjB, Subgroup.coe_mul, mul_inv_rev, Units.val_mul, mul_assoc]

theorem conjB_one [A.Normal] (b : algOf A) : conjB 1 b = b := by
  apply Subtype.ext
  simp [coe_conjB]

theorem conjB_inv_conjB [A.Normal] (g : R) (b : algOf A) : conjB g⁻¹ (conjB g b) = b := by
  rw [← conjB_mul, inv_mul_cancel, conjB_one]

variable [A.Normal] [IsMulCommutative (algOf A)]

/-- The action of `R` on the maximal ideals of `B`, by conjugation. -/
def maxAct (g : R) (I : MaximalSpectrum (algOf A)) : MaximalSpectrum (algOf A) :=
  ⟨I.asIdeal.comap (conjB g⁻¹).toRingHom, by
    have := I.isMaximal
    exact Ideal.comap_isMaximal_of_surjective _
      fun b => ⟨conjB g b, conjB_inv_conjB g b⟩⟩

theorem maxAct_one (I : MaximalSpectrum (algOf A)) : maxAct 1 I = I := by
  apply MaximalSpectrum.ext
  ext b
  simp [maxAct, conjB_one]

theorem maxAct_mul (g h : R) (I : MaximalSpectrum (algOf A)) :
    maxAct (g * h) I = maxAct g (maxAct h I) := by
  apply MaximalSpectrum.ext
  ext b
  simp [maxAct, conjB_mul]

/-- The conjugation action as a `MulAction`. -/
@[instance_reducible]
def maxAction : MulAction R (MaximalSpectrum (algOf A)) where
  smul := maxAct
  one_smul := maxAct_one
  mul_smul := maxAct_mul

theorem apply_mem_zeroSpace_maxAct (g : R) {I : MaximalSpectrum (algOf A)} {v : V}
    (hv : v ∈ zeroSpace (algOf A) I.asIdeal) :
    ((g : GeneralLinearGroup F V) : Module.End F V) v ∈
      zeroSpace (algOf A) (maxAct g I).asIdeal := by
  intro b hb
  have h := hv _ (show conjB g⁻¹ b ∈ I.asIdeal from hb)
  rw [coe_conjB] at h
  simp only [InvMemClass.coe_inv, inv_inv, Module.End.mul_apply] at h
  have hgg : ∀ w : V, ((g : GeneralLinearGroup F V) : Module.End F V)
      (((((g : GeneralLinearGroup F V))⁻¹ : GeneralLinearGroup F V) : Module.End F V) w) =
        w := by
    intro w
    rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Module.End.one_apply]
  rw [← hgg ((b : Module.End F V) _), h, map_zero]

end Conjugation

section Restriction

variable {R : Subgroup (GeneralLinearGroup F V)} (A : Subgroup R) [A.Normal]
  [IsMulCommutative (algOf A)]

/-- The elements of `R` fixing every maximal ideal of `B`. -/
def fixSub : Subgroup R where
  carrier := {k | ∀ I : MaximalSpectrum (algOf A), maxAct k I = I}
  mul_mem' {a b} ha hb I := by
    simp only [Set.mem_ofPred_eq] at ha hb
    rw [maxAct_mul, hb, ha]
  one_mem' I := maxAct_one I
  inv_mem' {a} ha I := by
    simp only [Set.mem_ofPred_eq] at ha
    conv_lhs => rw [← ha I]
    rw [← maxAct_mul, inv_mul_cancel, maxAct_one]

variable {A}

theorem mem_zeroSpace_of_fix {k : R} (hk : k ∈ fixSub A) {I : MaximalSpectrum (algOf A)}
    {v : V} (hv : v ∈ zeroSpace (algOf A) I.asIdeal) :
    ((k : GeneralLinearGroup F V) : Module.End F V) v ∈ zeroSpace (algOf A) I.asIdeal := by
  have := apply_mem_zeroSpace_maxAct k hv
  rwa [show maxAct k I = I from hk I] at this

variable (A)

/-- An element fixing the maximal ideals, restricted to `V_𝔪`. -/
def resGL (I : MaximalSpectrum (algOf A)) :
    fixSub A →* GeneralLinearGroup F (zeroSpace (algOf A) I.asIdeal) where
  toFun k :=
    { val := ((k : R) : GeneralLinearGroup F V).val.restrict fun _ hv =>
        mem_zeroSpace_of_fix k.2 hv
      inv := (((k⁻¹ : fixSub A) : R) : GeneralLinearGroup F V).val.restrict fun _ hv =>
        mem_zeroSpace_of_fix (k⁻¹).2 hv
      val_inv := by
        ext v
        simp only [Module.End.mul_apply, LinearMap.restrict_apply, Module.End.one_apply]
        rw [← Module.End.mul_apply, ← Units.val_mul]
        simp
      inv_val := by
        ext v
        simp only [Module.End.mul_apply, LinearMap.restrict_apply, Module.End.one_apply]
        rw [← Module.End.mul_apply, ← Units.val_mul]
        simp }
  map_one' := by
    ext v
    simp
  map_mul' a b := by
    ext v
    simp [Module.End.mul_apply]

theorem coe_resGL_apply (I : MaximalSpectrum (algOf A)) (k : fixSub A)
    (v : zeroSpace (algOf A) I.asIdeal) :
    ((resGL A I k : Module.End F (zeroSpace (algOf A) I.asIdeal)) v : V) =
      (((k : R) : GeneralLinearGroup F V) : Module.End F V) v :=
  rfl

end Restriction

end Field

section Step

variable {p r : ℕ} [Fact p.Prime] [Fact r.Prime] {V : Type u} [AddCommGroup V]
  [Module (ZMod p) V]

/-- `|G| = |ker f| |range f|`. -/
theorem card_eq_card_ker_mul_card_range {G G' : Type*} [Group G] [Group G'] (f : G →* G') :
    Nat.card G = Nat.card f.ker * Nat.card f.range := by
  rw [← f.ker.card_mul_index, Subgroup.index_ker]

omit [Fact r.Prime] in
theorem finite_moduleEnd [Finite V] : Finite (Module.End (ZMod p) V) :=
  Finite.of_injective _ (DFunLike.coe_injective (F := Module.End (ZMod p) V))

omit [Fact r.Prime] in
theorem nontrivial_subalgebra_end [Nontrivial V] (B : Subalgebra (ZMod p) (Module.End (ZMod p) V)) :
    Nontrivial B := by
  refine ⟨⟨0, 1, fun h => ?_⟩⟩
  have h' := congrArg (fun b : B => (b : Module.End (ZMod p) V)) h
  simp only [ZeroMemClass.coe_zero, OneMemClass.coe_one] at h'
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  exact hv (by simpa using (LinearMap.congr_fun h' v).symm)

/-- **The induction step with at least two maximal ideals.** -/
theorem card_le_of_two_le_card [Finite V] {R : Subgroup (GeneralLinearGroup (ZMod p) V)}
    (hR : IsPGroup r R) (A : Subgroup R) [A.Normal] [IsMulCommutative (algOf (F := ZMod p) A)]
    [IsReduced (algOf (F := ZMod p) A)]
    (ht : 2 ≤ Nat.card (MaximalSpectrum (algOf (F := ZMod p) A)))
    (ih : ∀ (W : Type u) [AddCommGroup W] [Module (ZMod p) W] [Finite W] [Nontrivial W],
      Nat.card W < Nat.card V → ∀ R' : Subgroup (GeneralLinearGroup (ZMod p) W),
        IsPGroup r R' → 2 * Nat.card R' ≤ Nat.card W ^ 3) :
    2 * Nat.card R ≤ Nat.card V ^ 3 := by
  classical
  have := finite_moduleEnd (p := p) (V := V)
  set B := algOf (F := ZMod p) A
  set X := MaximalSpectrum B
  have : Fintype X := Fintype.ofFinite X
  obtain ⟨e, h1, h2, h3, h4, h5⟩ := exists_idempotents B
  set W : X → Submodule (ZMod p) V := fun I => zeroSpace B I.asIdeal
  have hcard : Nat.card V = ∏ I, Nat.card (W I) := card_eq_prod_zeroSpace h1 h2 h3 h4
  have hW2 : ∀ I, 2 ≤ Nat.card (W I) := by
    intro I
    have : Nontrivial (W I) := (Submodule.nontrivial_iff_ne_bot).2 (zeroSpace_ne_bot h3 h5 I)
    exact Finite.one_lt_card
  have hlt : ∀ I, Nat.card (W I) < Nat.card V := by
    intro I
    have : Nontrivial X := Finite.one_lt_card_iff_nontrivial.1 (by omega)
    obtain ⟨J, hJ⟩ := exists_ne I
    rw [hcard, ← Finset.mul_prod_erase _ _ (Finset.mem_univ I)]
    have hJm : J ∈ Finset.univ.erase I := Finset.mem_erase.2 ⟨hJ, Finset.mem_univ J⟩
    have : Nat.card (W J) ≤ ∏ K ∈ Finset.univ.erase I, Nat.card (W K) :=
      Finset.single_le_prod (fun K _ => le_trans (by norm_num) (hW2 K)) hJm
    have := hW2 J
    have := hW2 I
    nlinarith
  -- the kernel of the permutation action
  let _ : MulAction R X := maxAction
  set π := MulAction.toPermHom R X
  have hker : π.ker = fixSub (F := ZMod p) A := by
    ext k
    rw [MonoidHom.mem_ker]
    constructor
    · intro hk I
      exact congrArg (fun σ : Equiv.Perm X => σ I) hk
    · intro hk
      exact Equiv.ext fun I => hk I
  have hK : IsPGroup r (fixSub (F := ZMod p) A) := hR.to_subgroup _
  -- the kernel embeds in the product of its restrictions
  let Φ : fixSub (F := ZMod p) A → ∀ I : X, (resGL (F := ZMod p) A I).range :=
    fun k I => ⟨resGL (F := ZMod p) A I k, k, rfl⟩
  have hΦ : Function.Injective Φ := by
    intro k k' hkk'
    have hv : ∀ I, ∀ v ∈ W I, (((k : R) : GeneralLinearGroup (ZMod p) V) :
        Module.End (ZMod p) V) v = (((k' : R) : GeneralLinearGroup (ZMod p) V) :
          Module.End (ZMod p) V) v := by
      intro I v hv
      have := congrArg (fun x : (resGL (F := ZMod p) A I).range =>
        ((x : GeneralLinearGroup (ZMod p) (W I)) : Module.End (ZMod p) (W I)) ⟨v, hv⟩)
        (congrFun hkk' I)
      exact congrArg Subtype.val this
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    ext v
    rw [← sum_idem_apply h2 v, map_sum, map_sum]
    exact Finset.sum_congr rfl fun I _ => hv I _ (apply_mem_zeroSpace h3 I v)
  have hfin : ∀ I, Finite (resGL (F := ZMod p) A I).range := fun I =>
    Finite.of_surjective _ (resGL (F := ZMod p) A I).rangeRestrict_surjective
  have hKcard : Nat.card (fixSub (F := ZMod p) A) ≤
      ∏ I, Nat.card (resGL (F := ZMod p) A I).range := by
    rw [← Nat.card_pi]
    exact Nat.card_le_card_of_injective Φ hΦ
  have hres : ∀ I, 2 * Nat.card (resGL (F := ZMod p) A I).range ≤ Nat.card (W I) ^ 3 := by
    intro I
    have : Nontrivial (W I) := (Submodule.nontrivial_iff_ne_bot).2 (zeroSpace_ne_bot h3 h5 I)
    exact ih (W I) (hlt I) _ (hK.of_surjective _ (resGL (F := ZMod p) A I).rangeRestrict_surjective)
  have hprod : 2 ^ Nat.card X * Nat.card (fixSub (F := ZMod p) A) ≤ Nat.card V ^ 3 := by
    calc 2 ^ Nat.card X * Nat.card (fixSub (F := ZMod p) A)
        ≤ 2 ^ Nat.card X * ∏ I, Nat.card (resGL (F := ZMod p) A I).range :=
          Nat.mul_le_mul_left _ hKcard
      _ = ∏ I, 2 * Nat.card (resGL (F := ZMod p) A I).range := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Nat.card_eq_fintype_card]
      _ ≤ ∏ I, Nat.card (W I) ^ 3 := Finset.prod_le_prod fun I _ => hres I
      _ = Nat.card V ^ 3 := by rw [Finset.prod_pow, hcard]
  -- the image in `Sym(t)`
  have hπ : Nat.card π.range ≤ 2 ^ (Nat.card X - 1) :=
    card_le_two_pow_of_isPGroup_perm _ (hR.of_surjective _ π.rangeRestrict_surjective)
  have hR' : Nat.card R = Nat.card (fixSub (F := ZMod p) A) * Nat.card π.range := by
    rw [card_eq_card_ker_mul_card_range π, hker]
  have h2t : 2 * 2 ^ (Nat.card X - 1) = 2 ^ Nat.card X := by
    rw [← pow_succ']
    congr 1
    omega
  calc 2 * Nat.card R = Nat.card (fixSub (F := ZMod p) A) * (2 * Nat.card π.range) := by
        rw [hR']; ring
    _ ≤ Nat.card (fixSub (F := ZMod p) A) * (2 * 2 ^ (Nat.card X - 1)) := by gcongr
    _ = 2 ^ Nat.card X * Nat.card (fixSub (F := ZMod p) A) := by rw [h2t, mul_comm]
    _ ≤ Nat.card V ^ 3 := hprod

/-- **The induction step with one maximal ideal**: `B` is a field, `A` is cyclic of order
`< |V|`, and `|R| ≤ |A|²`. -/
theorem card_le_of_card_eq_one [Finite V] [Nontrivial V]
    {R : Subgroup (GeneralLinearGroup (ZMod p) V)} (hR : IsPGroup r R) (A : Subgroup R)
    [A.Normal] (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hAmax : ∀ A' : Subgroup R, A'.Normal → (∀ x ∈ A', ∀ y ∈ A', x * y = y * x) → A ≤ A' →
      A' ≤ A)
    [IsMulCommutative (algOf (F := ZMod p) A)] [IsReduced (algOf (F := ZMod p) A)]
    (ht : Nat.card (MaximalSpectrum (algOf (F := ZMod p) A)) = 1) :
    2 * Nat.card R ≤ Nat.card V ^ 3 := by
  classical
  have := finite_moduleEnd (p := p) (V := V)
  set B := algOf (F := ZMod p) A
  set X := MaximalSpectrum B
  have : Subsingleton X := (Nat.card_eq_one_iff_unique.1 ht).1
  obtain ⟨I⟩ : Nonempty X := (Nat.card_eq_one_iff_unique.1 ht).2
  -- `B` is a field
  have hbot : I.asIdeal = ⊥ := by
    rw [eq_bot_iff]
    intro b hb
    rw [Ideal.mem_bot]
    apply (IsArtinianRing.equivPi B).injective
    funext J
    rw [Subsingleton.elim J I, IsArtinianRing.equivPi_apply, map_zero, Pi.zero_apply,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hb
  have : Nontrivial B := nontrivial_subalgebra_end B
  have hfield : IsField B := Ring.isField_iff_maximal_bot.2 (hbot ▸ I.isMaximal)
  let _ : Field B := hfield.toField
  -- `A` embeds in `B`, so it is cyclic of order `< |B| ≤ |V|`
  let g : A →* B :=
    { toFun := fun a => ⟨gensOf A a, Algebra.subset_adjoin ⟨a, rfl⟩⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun a b => Subtype.ext (map_mul _ a b) }
  have hg : Function.Injective g := by
    intro a b hab
    have := congrArg (fun x : B => (x : Module.End (ZMod p) V)) hab
    exact Subtype.ext (Subtype.ext (Units.ext this))
  have hcyc : IsCyclic A := isCyclic_of_injective_ringHom g hg
  have hne : ∀ a, g a ≠ 0 := by
    intro a h
    have := map_mul g a a⁻¹
    rw [mul_inv_cancel, map_one, h, zero_mul] at this
    exact zero_ne_one this.symm
  have hAB : Nat.card A + 1 ≤ Nat.card B := by
    have hinj : Function.Injective (fun o : Option A => o.elim (0 : B) g) := by
      rintro (_ | a) (_ | b) h
      · rfl
      · exact absurd h.symm (hne b)
      · exact absurd h (hne a)
      · exact congrArg some (hg h)
    have := Nat.card_le_card_of_injective _ hinj
    rwa [Finite.card_option] at this
  have hBV : Nat.card B ≤ Nat.card V := by
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    apply Nat.card_le_card_of_injective (fun b : B => (b : Module.End (ZMod p) V) v)
    intro b b' h
    by_contra hbb
    obtain ⟨c, hc⟩ := (sub_ne_zero.2 hbb).isUnit.exists_left_inv
    apply hv
    have h0 : ((b - b' : B) : Module.End (ZMod p) V) v = 0 := by
      simp only [Subalgebra.coe_sub, LinearMap.sub_apply]
      exact sub_eq_zero.2 h
    calc v = ((c * (b - b') : B) : Module.End (ZMod p) V) v := by rw [hc]; rfl
      _ = (c : Module.End (ZMod p) V) (((b - b' : B) : Module.End (ZMod p) V) v) := rfl
      _ = 0 := by rw [h0, map_zero]
  -- `|R| ≤ |A| |Aut A| ≤ |A|²`
  have hcent := centralizer_le_of_maximal hR A hAc hAmax
  let c : R →* MulAut A := MulAut.conjNormal
  have hker : c.ker ≤ A := fun x hx =>
    hcent (mem_centralizer_of_conjNormal_eq_one (MonoidHom.mem_ker.1 hx))
  have hR1 : Nat.card R = Nat.card c.ker * Nat.card c.range := card_eq_card_ker_mul_card_range c
  have hk : Nat.card c.ker ≤ Nat.card A := Subgroup.card_le_of_le hker
  have hr : Nat.card c.range ≤ Nat.card A := by
    refine (Subgroup.card_le_card_group _).trans ?_
    rw [IsCyclic.card_mulAut]
    exact Nat.totient_le _
  have hV2 : 2 ≤ Nat.card V := Finite.one_lt_card
  have hAV : Nat.card A + 1 ≤ Nat.card V := hAB.trans hBV
  calc 2 * Nat.card R ≤ 2 * (Nat.card A * Nat.card A) := by
        rw [hR1]
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul hk hr)
    _ ≤ 2 * (Nat.card V * Nat.card V) := by
        have : Nat.card A ≤ Nat.card V := by omega
        gcongr
    _ ≤ Nat.card V * (Nat.card V * Nat.card V) := Nat.mul_le_mul_right _ hV2
    _ = Nat.card V ^ 3 := by ring

/-- **Linear `r`-groups in characteristic `p ≠ r` are small**: `2 |R| ≤ |V|³`. -/
theorem card_le_of_isPGroup (hpr : p ≠ r) [Finite V] [Nontrivial V]
    (R : Subgroup (GeneralLinearGroup (ZMod p) V)) (hR : IsPGroup r R) :
    2 * Nat.card R ≤ Nat.card V ^ 3 := by
  suffices h : ∀ n, ∀ (V : Type u) [AddCommGroup V] [Module (ZMod p) V] [Finite V]
      [Nontrivial V], Nat.card V = n → ∀ R : Subgroup (GeneralLinearGroup (ZMod p) V),
        IsPGroup r R → 2 * Nat.card R ≤ Nat.card V ^ 3 from h _ V rfl R hR
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ _ _ hn R hR
  have := finite_moduleEnd (p := p) (V := V)
  -- a maximal abelian normal subgroup
  obtain ⟨A, ⟨hAn, hAc⟩, hAmax⟩ := (Set.toFinite {A : Subgroup R |
    A.Normal ∧ ∀ x ∈ A, ∀ y ∈ A, x * y = y * x}).exists_maximal
      ⟨⊥, inferInstance, fun x hx y hy => by
        rw [Subgroup.mem_bot] at hx hy
        rw [hx, hy]⟩
  have hAmax' : ∀ A' : Subgroup R, A'.Normal → (∀ x ∈ A', ∀ y ∈ A', x * y = y * x) →
      A ≤ A' → A' ≤ A := fun A' hn hc hle => hAmax ⟨hn, hc⟩ hle
  have hcomm := pairwise_commute_gensOf A hAc
  have : IsMulCommutative (algOf (F := ZMod p) A) := Algebra.isMulCommutative_adjoin _ hcomm
  have : NeZero (Nat.card A : ZMod p) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 (hR.to_subgroup A)
    refine ⟨fun h => hpr ?_⟩
    rw [hk, ZMod.natCast_eq_zero_iff] at h
    exact (Nat.prime_dvd_prime_iff_eq Fact.out Fact.out).1
      ((Nat.Prime.dvd_of_dvd_pow Fact.out h))
  have : IsReduced (algOf (F := ZMod p) A) := isReduced_adjoin_range (gensOf A) hcomm
  have : Nontrivial (algOf (F := ZMod p) A) := nontrivial_subalgebra_end _
  have hX : 1 ≤ Nat.card (MaximalSpectrum (algOf (F := ZMod p) A)) := by
    obtain ⟨M, hM⟩ := Ideal.exists_maximal (algOf (F := ZMod p) A)
    have : Nonempty (MaximalSpectrum (algOf (F := ZMod p) A)) := ⟨⟨M, hM⟩⟩
    exact Nat.one_le_iff_ne_zero.2 Nat.card_pos.ne'
  rcases Nat.lt_or_ge 1 (Nat.card (MaximalSpectrum (algOf (F := ZMod p) A))) with ht | ht
  · exact card_le_of_two_le_card hR A ht fun W _ _ _ _ hW R' hR' =>
      ih _ (hn ▸ hW) W rfl R' hR'
  · exact card_le_of_card_eq_one hR A hAc hAmax' (by omega)

/-- **Linear `r`-groups in characteristic `p ≠ r`**: `|R| ≤ |V|³`. -/
theorem card_le_of_isPGroup' (hpr : p ≠ r) [Finite V]
    (R : Subgroup (GeneralLinearGroup (ZMod p) V)) (hR : IsPGroup r R) :
    Nat.card R ≤ Nat.card V ^ 3 := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · have : Subsingleton (GeneralLinearGroup (ZMod p) V) :=
      ⟨fun a b => Units.ext (LinearMap.ext fun v => Subsingleton.elim _ _)⟩
    have : Nat.card R ≤ 1 := Finite.card_le_one_iff_subsingleton.2 inferInstance
    have : 1 ≤ Nat.card V ^ 3 := Nat.one_le_pow _ _ Nat.card_pos
    omega
  · have := card_le_of_isPGroup hpr R hR
    omega

end Step

end GraphIso.Groups
