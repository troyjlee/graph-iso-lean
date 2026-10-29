module

public import GraphIso.Groups.FactorAction
public import Mathlib.GroupTheory.NoncommPiCoprod
public import Mathlib.Data.Nat.Factorization.Basic

/-!
# Groups with no abelian normal subgroup

Relative to a subgroup `Y` of a finite group `X` with bounded sections:

* `NoAbelianNormal Y`: every abelian subgroup normalized by `Y` (and lying in `Y`) is trivial.
* `NoAbelianNormal.centralizer`: the property passes to the centralizer in `Y` of a normal
  subgroup `M`. A minimal nontrivial abelian subgroup normalized by the centralizer has
  conjugates under `Y` that pairwise coincide or meet trivially, hence commute; they generate an
  abelian subgroup normalized by `Y`.
* `exists_card_le_of_noAbelianNormal`: then `|Y| ≤ (k! 2^k)^t` with `2^t` at most the `p′`-part
  of `|Y|`, for any prime `p`. A minimal normal subgroup `M` is nonabelian, the product of `j`
  simple factors; `|Y| ≤ |C_Y(M)| (k! 2^k)^j` (`card_le_of_factors`); `M` meets `C_Y(M)`
  trivially, so `|M| |C_Y(M)|` divides `|Y|`; each factor, being nonabelian simple, is not a
  `p`-group, so the `p′`-part of `|M|` is at least `2^j`; and induction applies to `C_Y(M)`.
-/

@[expose] public section

namespace GraphIso.Groups

variable {X : Type*} [Group X]

/-- `Y` has no nontrivial abelian normal subgroup. -/
def NoAbelianNormal (Y : Subgroup X) : Prop :=
  ∀ A : Subgroup X, NNormal Y A → (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) → A = ⊥

/-- The centralizer in `Y` of a normal subgroup is normal. -/
theorem nnormal_centralizer {Y M : Subgroup X} (hM : NNormal Y M) :
    NNormal Y (Y ⊓ Subgroup.centralizer (M : Set X)) := by
  refine ⟨inf_le_left, fun y hy c hc =>
    Subgroup.mem_inf.2 ⟨Y.mul_mem (Y.mul_mem hy hc.1) (Y.inv_mem hy), ?_⟩⟩
  rw [Subgroup.mem_centralizer_iff]
  intro m hm
  have hm' : y⁻¹ * m * y ∈ M := by simpa using hM.2 y⁻¹ (Y.inv_mem hy) m hm
  have := Subgroup.mem_centralizer_iff.1 hc.2 _ hm'
  calc m * (y * c * y⁻¹) = y * ((y⁻¹ * m * y) * c) * y⁻¹ := by group
    _ = y * (c * (y⁻¹ * m * y)) * y⁻¹ := by rw [this]
    _ = y * c * y⁻¹ * m := by group

/-- Conjugates of abelian subgroups are abelian. -/
theorem comm_cj {B : Subgroup X} (hB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (g : X) :
    ∀ x ∈ cj g B, ∀ z ∈ cj g B, x * z = z * x := fun x hx z hz => by
  have := hB _ (mem_cj.1 hx) _ (mem_cj.1 hz)
  calc x * z = g * ((g⁻¹ * x * g) * (g⁻¹ * z * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * z * g) * (g⁻¹ * x * g)) * g⁻¹ := by rw [this]
    _ = z * x := by group

/-- **The property passes to centralizers of normal subgroups.** -/
theorem NoAbelianNormal.centralizer [Finite X] {Y M : Subgroup X} (hY : NoAbelianNormal Y)
    (hM : NNormal Y M) : NoAbelianNormal (Y ⊓ Subgroup.centralizer (M : Set X)) := by
  classical
  set C := Y ⊓ Subgroup.centralizer (M : Set X)
  have hC : NNormal Y C := nnormal_centralizer hM
  intro A hA hAc
  by_contra hAb
  -- a minimal nontrivial abelian subgroup normalized by `C`
  have hex : ∃ m, ∃ B : Subgroup X, NNormal C B ∧ B ≠ ⊥ ∧
      (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) ∧ Nat.card B = m := ⟨_, A, hA, hAb, hAc, rfl⟩
  obtain ⟨B, hB, hBb, hBc, hBm⟩ := Nat.find_spec hex
  have hmin : ∀ D : Subgroup X, NNormal C D → D ≠ ⊥ → (∀ x ∈ D, ∀ y ∈ D, x * y = y * x) →
      Nat.card B ≤ Nat.card D := fun D hD hDb hDc =>
    hBm ▸ Nat.find_min' hex ⟨D, hD, hDb, hDc, rfl⟩
  -- its conjugates under `Y` commute
  have hcjn : ∀ y ∈ Y, NNormal C (cj y B) := fun y hy => hC.cj hB hy
  have hcomm : ∀ y ∈ Y, ∀ y' ∈ Y, ∀ x ∈ cj y B, ∀ z ∈ cj y' B, x * z = z * x := by
    intro y hy y' hy' x hx z hz
    by_cases heq : cj y B = cj y' B
    · exact comm_cj hBc y' x (heq ▸ hx) z hz
    · have hinf : cj y B ⊓ cj y' B = ⊥ := by
        by_contra hne
        have h1 := hmin _ ((hcjn y hy).inf (hcjn y' hy')) hne fun a ha b hb =>
          comm_cj hBc y a ha.1 b hb.1
        have h2 : cj y B ⊓ cj y' B = cj y B :=
          Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [card_cj]; exact h1)
        exact heq (Subgroup.eq_of_le_of_card_ge (h2 ▸ inf_le_right) (by rw [card_cj, card_cj]))
      have h1 : x * z * x⁻¹ * z⁻¹ ∈ cj y B := by
        have := (hcjn y hy).2 z ((hcjn y' hy').1 hz) x⁻¹ ((cj y B).inv_mem hx)
        have := (cj y B).mul_mem hx this
        simpa [mul_assoc] using this
      have h2 : x * z * x⁻¹ * z⁻¹ ∈ cj y' B :=
        (cj y' B).mul_mem ((hcjn y' hy').2 x ((hcjn y hy).1 hx) z hz) ((cj y' B).inv_mem hz)
      have : x * z * x⁻¹ * z⁻¹ ∈ cj y B ⊓ cj y' B := ⟨h1, h2⟩
      rw [hinf, Subgroup.mem_bot] at this
      calc x * z = x * z * x⁻¹ * z⁻¹ * (z * x) := by group
        _ = z * x := by rw [this, one_mul]
  -- they generate an abelian subgroup normalized by `Y`
  let D : Subgroup X := ⨆ y : Y, cj (y : X) B
  have hDn : NNormal Y D := by
    refine ⟨iSup_le fun y => (hcjn y y.2).1.trans hC.1, fun g hg x hx => ?_⟩
    have hle : D ≤ cj g⁻¹ D := by
      refine iSup_le fun y z hz => mem_cj.2 ?_
      have : g * z * g⁻¹ ∈ cj (g * y) B := by
        rw [← cj_mul]
        exact mem_cj.2 (by simpa [mul_assoc] using hz)
      simpa using Subgroup.mem_iSup_of_mem (⟨g * y, Y.mul_mem hg y.2⟩ : Y) this
    simpa using mem_cj.1 (hle hx)
  have hDc : ∀ x ∈ D, ∀ z ∈ D, x * z = z * x := by
    have hcen : D ≤ Subgroup.centralizer (D : Set X) := by
      refine iSup_le fun y => ?_
      rw [Subgroup.le_centralizer_iff]
      refine iSup_le fun y' => fun z hz => Subgroup.mem_centralizer_iff.2 fun x hx => ?_
      exact hcomm y y.2 y' y'.2 x hx z hz
    intro x hx z hz
    exact Subgroup.mem_centralizer_iff.1 (hcen hz) x hx
  have hBD : B ≤ D := by
    have := le_iSup (fun y : Y => cj (y : X) B) ⟨1, Y.one_mem⟩
    rwa [show ((⟨1, Y.one_mem⟩ : Y) : X) = 1 from rfl, cj_one] at this
  exact hBb (le_bot_iff.1 (hY D hDn hDc ▸ hBD))

/-- A nonabelian simple group has order with `p′`-part at least `2`. -/
theorem two_le_ordCompl_of_simple [Finite X] {p : ℕ} [hp : Fact p.Prime] {A : Subgroup X}
    (hA : IsSimpleGroup A) (hna : ∃ x ∈ A, ∃ y ∈ A, x * y ≠ y * x) :
    2 ≤ ordCompl[p] (Nat.card A) := by
  have hpos := Nat.ordCompl_pos p (Nat.card_pos (α := A)).ne'
  by_contra hlt
  have h1 : ordCompl[p] (Nat.card A) = 1 := by omega
  have hcard : Nat.card A = p ^ (Nat.card A).factorization p := by
    have := Nat.ordProj_mul_ordCompl_eq_self (Nat.card A) p
    rw [h1, mul_one] at this
    exact this.symm
  have hpA : IsPGroup p A := IsPGroup.of_card hcard
  have : Nontrivial (Subgroup.center A) := hpA.center_nontrivial
  have hcen : Subgroup.center A = ⊤ := by
    rcases (Subgroup.center A).normal_of_characteristic.eq_bot_or_eq_top with h | h
    · rw [h] at this
      exact absurd this (not_nontrivial _)
    · exact h
  obtain ⟨x, hx, y, hy, hxy⟩ := hna
  have : (⟨y, hy⟩ : A) ∈ Subgroup.center A := hcen ▸ Subgroup.mem_top _
  have := Subgroup.mem_center_iff.1 this ⟨x, hx⟩
  exact hxy (congrArg Subtype.val this)

/-- **Groups with no abelian normal subgroup.** -/
theorem exists_card_le_of_noAbelianNormal [Finite X] {k p : ℕ} [Fact p.Prime]
    (hk : BoundedSections k X) (Y : Subgroup X) (hY : NoAbelianNormal Y) :
    ∃ t : ℕ, Nat.card Y ≤ (k.factorial * 2 ^ k) ^ t ∧ 2 ^ t ≤ ordCompl[p] (Nat.card Y) := by
  classical
  induction hn : Nat.card Y using Nat.strong_induction_on generalizing Y with
  | _ n ih =>
  by_cases hYb : Y = ⊥
  · subst hYb
    subst hn
    refine ⟨0, ?_, ?_⟩ <;> simp
  subst hn
  obtain ⟨M, hM⟩ := exists_isMinNormal hYb
  have hMna : ∃ x ∈ M, ∃ y ∈ M, x * y ≠ y * x := by
    by_contra h
    push Not at h
    exact hM.2.1 (hY M hM.1 h)
  obtain ⟨F, -, hFs, hFna, hFcomm, hFind, hFN, hcjF, -⟩ := exists_simple_factors hM hMna
  set C := Y ⊓ Subgroup.centralizer (M : Set X)
  have hFk : ∀ A ∈ F, Nat.card A ≤ k := fun A hA => by
    have := hFs A hA
    exact hk.card_le A (MonoidHom.id A) Function.surjective_id
  have hYC := card_le_of_factors hk F hFk hFN hcjF
  -- `M` meets `C` trivially
  have hMC : M ⊓ C = ⊥ := by
    rcases hM.2.2 (M ⊓ C) (hM.1.inf (nnormal_centralizer hM.1)) inf_le_left with h | h
    · exact h
    · exfalso
      obtain ⟨x, hx, y, hy, hxy⟩ := hMna
      have hyC : y ∈ M ⊓ C := h.symm ▸ hy
      exact hxy (Subgroup.mem_centralizer_iff.1 hyC.2.2 x hx)
  have hCY : C < Y := by
    refine lt_of_le_of_ne inf_le_left fun h => ?_
    have hMC' : M ≤ M ⊓ C := le_inf le_rfl (h ▸ hM.1.1)
    rw [hMC] at hMC'
    exact hM.2.1 (le_bot_iff.1 hMC')
  have hCcard : Nat.card C < Nat.card Y := Subgroup.card_lt_of_lt hCY
  obtain ⟨t, ht1, ht2⟩ := ih _ hCcard C (hY.centralizer hM.1) rfl
  refine ⟨F.card + t, ?_, ?_⟩
  · calc Nat.card Y ≤ Nat.card C * (k.factorial * 2 ^ k) ^ F.card := hYC
      _ ≤ (k.factorial * 2 ^ k) ^ t * (k.factorial * 2 ^ k) ^ F.card :=
          Nat.mul_le_mul_right _ ht1
      _ = (k.factorial * 2 ^ k) ^ (F.card + t) := by rw [pow_add, mul_comm]
  -- `|M| |C|` divides `|Y|`
  have hdvd : Nat.card M * Nat.card C ∣ Nat.card Y := by
    let μ : M × C →* X :=
      { toFun := fun x => (x.1 : X) * x.2
        map_one' := by simp
        map_mul' := fun x y => by
          simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
          have : (x.2 : X) * y.1 = y.1 * x.2 :=
            (Subgroup.mem_centralizer_iff.1 x.2.2.2 _ y.1.2).symm
          simp only [mul_assoc]
          rw [← mul_assoc (x.2 : X) (y.1 : X), this, mul_assoc] }
    have hμ : Function.Injective μ := by
      refine (injective_iff_map_eq_one μ).2 fun x hx => ?_
      have hx' : (x.1 : X) * x.2 = 1 := hx
      have h1 : (x.1 : X) ∈ M ⊓ C := by
        refine ⟨x.1.2, ?_⟩
        rw [eq_inv_of_mul_eq_one_left hx']
        exact C.inv_mem x.2.2
      rw [hMC, Subgroup.mem_bot] at h1
      rw [h1, one_mul] at hx'
      exact Prod.ext (Subtype.ext h1) (Subtype.ext hx')
    have hle : μ.range ≤ Y := by
      rintro _ ⟨x, rfl⟩
      exact Y.mul_mem (hM.1.1 x.1.2) x.2.2.1
    rw [← Nat.card_prod, Nat.card_congr (MonoidHom.ofInjective hμ).toEquiv]
    exact Subgroup.card_dvd_of_le hle
  -- the `p′`-part of `|M|`
  have hMcard : 2 ^ F.card ≤ ordCompl[p] (Nat.card M) := by
    have hcomm' : Pairwise fun A B : F => ∀ x y : X, x ∈ (A : Subgroup X) →
        y ∈ (B : Subgroup X) → Commute x y := fun A B hAB x y hx hy =>
      hFcomm A A.2 B B.2 (fun h => hAB (Subtype.ext h)) x hx y hy
    have hinj := Subgroup.injective_noncommPiCoprod_of_iSupIndep (hcomm := hcomm') hFind
    have hrange : (Subgroup.noncommPiCoprod hcomm').range = M := by
      rw [Subgroup.noncommPiCoprod_range, hFN]
    have hprod : Nat.card M = ∏ A : F, Nat.card (A : Subgroup X) := by
      rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_pi]
    rw [hprod]
    have key : ∀ s : Finset F, 2 ^ s.card ≤ ordCompl[p] (∏ A ∈ s, Nat.card (A : Subgroup X)) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | insert a s ha ih =>
        rw [Finset.prod_insert ha, Nat.ordCompl_mul, Finset.card_insert_of_notMem ha, pow_succ,
          mul_comm]
        exact Nat.mul_le_mul (two_le_ordCompl_of_simple (hFs a a.2) (hFna a a.2)) ih
    simpa using key Finset.univ
  calc 2 ^ (F.card + t) = 2 ^ F.card * 2 ^ t := pow_add _ _ _
    _ ≤ ordCompl[p] (Nat.card M) * ordCompl[p] (Nat.card C) := Nat.mul_le_mul hMcard ht2
    _ = ordCompl[p] (Nat.card M * Nat.card C) := (Nat.ordCompl_mul _ _ _).symm
    _ ≤ ordCompl[p] (Nat.card Y) :=
        Nat.le_of_dvd (Nat.ordCompl_pos p Nat.card_pos.ne')
          (Nat.ordCompl_dvd_ordCompl_of_dvd hdvd p)

end GraphIso.Groups
