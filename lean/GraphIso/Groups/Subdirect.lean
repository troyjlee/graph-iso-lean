module

public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.Algebra.Group.Pi.Lemmas
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.Group
public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-!
# Subgroups of products of simple groups containing no factor

`two_pow_mul_card_sq_le`: let `T i` (`i ∈ ι`, finite) be nonabelian simple groups, all of the
same order `m`, and `H ≤ ∏ T i` a subgroup containing none of the factors. Then
`2^{|ι|} |H|² ≤ m^{2 |ι|}`: the index of `H` is at least `2^{|ι| / 2}`.

The proof is by induction on the support. Kill a coordinate `a`: `|H| ≤ |P| |K|`, where `P` is
the image of `H` and `K < T a` the part of `H` in `T a`, so `2 |K| ≤ m`. If `P` contains no
factor, induction applies to `P`. Otherwise `P` contains some factor `T b`; then `H` meets `T b`
trivially (its part there is normal in the simple `T b`), so the elements of `H` supported on
`{a, b}` map injectively to `T a`, and onto `T b`, hence onto `T a` as `|T a| = |T b|`. If `P`
contained two factors `T b` and `T c`, commutators of such lifts would put `[T a, T a]` in the
part of `H` in `T a`, which is normal in `T a`, hence trivial, and `T a` would be abelian. So
killing `b` as well leaves an image containing no factor, and induction applies to it.
-/

@[expose] public section

namespace GraphIso.Groups

variable {ι : Type*} [DecidableEq ι] {T : ι → Type*} [∀ i, Group (T i)]

/-- Kill the coordinate `a`. -/
def killAt (a : ι) : (∀ i, T i) →* ∀ i, T i where
  toFun x i := if i = a then 1 else x i
  map_one' := by
    funext i
    split_ifs <;> rfl
  map_mul' x y := by
    funext i
    by_cases h : i = a <;> simp [h]

theorem killAt_apply (a : ι) (x : ∀ i, T i) (i : ι) :
    killAt a x i = if i = a then 1 else x i := rfl

/-- The elements trivial outside `s`. -/
def suppOn (s : Finset ι) : Subgroup (∀ i, T i) where
  carrier := {x | ∀ i, i ∉ s → x i = 1}
  mul_mem' := fun {x y} hx hy i hi => by simp [hx i hi, hy i hi]
  one_mem' := fun _ _ => rfl
  inv_mem' := fun {x} hx i hi => by simp [hx i hi]

/-- `H` contains the factor `T i`. -/
def HasFactor (H : Subgroup (∀ i, T i)) (i : ι) : Prop := ∀ t : T i, Pi.mulSingle i t ∈ H

variable [Finite ι] [∀ i, Finite (T i)]

omit [Finite ι] in
/-- Killing a coordinate: `|H| ≤ |P| |K|`. -/
theorem card_le_card_map_killAt_mul (H : Subgroup (∀ i, T i)) (a : ι) :
    Nat.card H ≤ Nat.card (H.map (killAt a)) * Nat.card (H.comap (MonoidHom.mulSingle T a)) := by
  let f : H →* ∀ i, T i := (killAt a).comp H.subtype
  have h1 : Nat.card H = Nat.card f.ker * Nat.card f.range := by
    rw [← f.ker.card_mul_index, Subgroup.index_ker]
  have h2 : f.range = H.map (killAt a) := by
    ext x
    simp [f, MonoidHom.mem_range, Subgroup.mem_map]
  have h3 : Nat.card f.ker ≤ Nat.card (H.comap (MonoidHom.mulSingle T a)) := by
    have hform : ∀ g : f.ker, ((g : H) : ∀ i, T i) =
        Pi.mulSingle a (((g : H) : ∀ i, T i) a) := by
      intro g
      funext i
      by_cases hi : i = a
      · subst hi
        simp
      · have := congrFun (MonoidHom.mem_ker.1 g.2) i
        simp only [f, MonoidHom.coe_comp, Subgroup.coe_subtype, Function.comp_apply,
          killAt_apply, hi, ite_false, Pi.one_apply] at this
        rw [this, Pi.mulSingle_eq_of_ne hi]
    refine Nat.card_le_card_of_injective
      (fun g => ⟨((g : H) : ∀ i, T i) a, ?_⟩) fun g h hgh => ?_
    · change Pi.mulSingle a _ ∈ H
      rw [← hform g]
      exact (g : H).2
    · have : ((g : H) : ∀ i, T i) a = ((h : H) : ∀ i, T i) a :=
        congrArg (fun z : H.comap (MonoidHom.mulSingle T a) => (z : T a)) hgh
      refine Subtype.ext (Subtype.ext ?_)
      rw [hform g, hform h, this]
  rw [h1, h2]
  exact Nat.mul_le_mul_right _ h3 |>.trans_eq (mul_comm _ _)

/-- **Lifting through a factor of the image.** If killing `a` leaves an image containing `T b`,
`H` contains no `T b` and `|T a| ≤ |T b|`, every element of `T a` lifts to an element of `H`
supported on `{a, b}`. -/
theorem exists_lift {H : Subgroup (∀ i, T i)} {a b : ι} (hab : a ≠ b)
    (hcard : Nat.card (T a) ≤ Nat.card (T b)) (hsb : IsSimpleGroup (T b))
    (hHb : ¬ HasFactor H b) (hPb : HasFactor (H.map (killAt a)) b) (x : T a) :
    ∃ h ∈ H, h a = x ∧ ∀ i, i ≠ a → i ≠ b → h i = 1 := by
  classical
  -- `H` meets `T b` trivially
  have hKb : ∀ β : T b, Pi.mulSingle b β ∈ H → β = 1 := by
    let Kb : Subgroup (T b) := H.comap (MonoidHom.mulSingle T b)
    have hKn : Kb.Normal := by
      refine ⟨fun κ hκ β => ?_⟩
      obtain ⟨h, hh, hhb⟩ := hPb β
      have hb' : h b = β := by
        have := congrFun hhb b
        simpa [killAt_apply, Ne.symm hab] using this
      have : h * Pi.mulSingle b κ * h⁻¹ = Pi.mulSingle b (β * κ * β⁻¹) := by
        funext i
        by_cases hi : i = b
        · subst hi
          simp [hb']
        · simp [hi]
      change Pi.mulSingle b (β * κ * β⁻¹) ∈ H
      rw [← this]
      exact H.mul_mem (H.mul_mem hh hκ) (H.inv_mem hh)
    rcases hKn.eq_bot_or_eq_top with h | h
    · intro β hβ
      have : β ∈ Kb := hβ
      rw [h] at this
      exact this
    · exact absurd (fun t => (h ▸ Subgroup.mem_top t : t ∈ Kb)) hHb
  -- the elements of `H` supported on `{a, b}`
  let L := {h : ∀ i, T i // h ∈ H ∧ ∀ i, i ≠ a → i ≠ b → h i = 1}
  let ea : L → T a := fun h => h.1 a
  have hinj : Function.Injective ea := by
    intro g h hgh
    have hm : h.1⁻¹ * g.1 ∈ H := H.mul_mem (H.inv_mem h.2.1) g.2.1
    have hform : h.1⁻¹ * g.1 = Pi.mulSingle b ((h.1⁻¹ * g.1) b) := by
      funext i
      by_cases hib : i = b
      · subst hib
        simp
      · rw [Pi.mulSingle_eq_of_ne hib]
        by_cases hia : i = a
        · subst hia
          have : h.1 i = g.1 i := hgh.symm
          simp [this]
        · simp [g.2.2 i hia hib, h.2.2 i hia hib]
    have h1 := hKb _ (hform ▸ hm)
    rw [h1, Pi.mulSingle_one] at hform
    exact Subtype.ext (inv_mul_eq_one.1 hform).symm
  have hsurj : Function.Surjective (fun h : L => h.1 b) := by
    intro β
    obtain ⟨h, hh, hhb⟩ := hPb β
    refine ⟨⟨h, hh, fun i hia hib => ?_⟩, ?_⟩
    · have := congrFun hhb i
      simpa [killAt_apply, hia, hib] using this
    · have := congrFun hhb b
      simpa [killAt_apply, Ne.symm hab] using this
  have hbij : Function.Bijective ea := (Nat.bijective_iff_injective_and_card ea).2
    ⟨hinj, le_antisymm (Nat.card_le_card_of_injective ea hinj)
      (hcard.trans (Nat.card_le_card_of_surjective _ hsurj))⟩
  obtain ⟨h, hh⟩ := hbij.2 x
  exact ⟨h.1, h.2.1, hh, h.2.2⟩

/-- **At most one factor in the image.** -/
theorem not_hasFactor_two {H : Subgroup (∀ i, T i)} {a b c : ι} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (hb : Nat.card (T a) ≤ Nat.card (T b)) (hc : Nat.card (T a) ≤ Nat.card (T c))
    (hsa : IsSimpleGroup (T a)) (hsb : IsSimpleGroup (T b)) (hsc : IsSimpleGroup (T c))
    (hna : ∃ x y : T a, x * y ≠ y * x) (hHa : ¬ HasFactor H a) (hHb : ¬ HasFactor H b)
    (hHc : ¬ HasFactor H c) (hPb : HasFactor (H.map (killAt a)) b)
    (hPc : HasFactor (H.map (killAt a)) c) : False := by
  classical
  -- `H` meets `T a` trivially
  have hKa : ∀ κ : T a, Pi.mulSingle a κ ∈ H → κ = 1 := by
    let Ka : Subgroup (T a) := H.comap (MonoidHom.mulSingle T a)
    have hKn : Ka.Normal := by
      refine ⟨fun κ hκ x => ?_⟩
      obtain ⟨h, hh, hha, -⟩ := exists_lift hab hb hsb hHb hPb x
      have : h * Pi.mulSingle a κ * h⁻¹ = Pi.mulSingle a (x * κ * x⁻¹) := by
        funext i
        by_cases hi : i = a
        · subst hi
          simp [hha]
        · simp [hi]
      change Pi.mulSingle a (x * κ * x⁻¹) ∈ H
      rw [← this]
      exact H.mul_mem (H.mul_mem hh hκ) (H.inv_mem hh)
    rcases hKn.eq_bot_or_eq_top with h | h
    · intro κ hκ
      have : κ ∈ Ka := hκ
      rw [h] at this
      exact this
    · exact absurd (fun t => (h ▸ Subgroup.mem_top t : t ∈ Ka)) hHa
  obtain ⟨x, y, hxy⟩ := hna
  obtain ⟨h, hh, hha, hh1⟩ := exists_lift hab hb hsb hHb hPb x
  obtain ⟨h', hh', hha', hh1'⟩ := exists_lift hac hc hsc hHc hPc y
  have hform : h * h' * h⁻¹ * h'⁻¹ = Pi.mulSingle a (x * y * x⁻¹ * y⁻¹) := by
    funext i
    by_cases hia : i = a
    · subst hia
      simp [hha, hha']
    · rw [Pi.mulSingle_eq_of_ne hia]
      by_cases hib : i = b
      · subst hib
        simp [hh1' _ hia hbc]
      · simp [hh1 i hia hib]
  have h1 := hKa _ (hform ▸ H.mul_mem (H.mul_mem (H.mul_mem hh hh') (H.inv_mem hh))
    (H.inv_mem hh'))
  exact hxy (calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
    _ = y * x := by rw [h1, one_mul])

/-- **Subgroups containing no factor have index at least `2^{|ι| / 2}`.** -/
theorem two_pow_mul_card_sq_le [Fintype ι] {m : ℕ} (hm : ∀ i, Nat.card (T i) = m)
    (hs : ∀ i, IsSimpleGroup (T i)) (hna : ∀ i, ∃ x y : T i, x * y ≠ y * x)
    (H : Subgroup (∀ i, T i)) (hH : ∀ i, ¬ HasFactor H i) :
    2 ^ Fintype.card ι * Nat.card H ^ 2 ≤ m ^ (2 * Fintype.card ι) := by
  classical
  have key : ∀ n, ∀ s : Finset ι, s.card = n → ∀ H : Subgroup (∀ i, T i), H ≤ suppOn s →
      (∀ i ∈ s, ¬ HasFactor H i) → 2 ^ n * Nat.card H ^ 2 ≤ m ^ (2 * n) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro s hsn H hHs hHf
    rcases s.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
    · subst hsn
      have : H = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        rw [Subgroup.mem_bot]
        funext i
        exact hHs hx i (Finset.notMem_empty i)
      simp [this]
    -- kill `a`
    set K := H.comap (MonoidHom.mulSingle T a)
    set P := H.map (killAt a)
    have hHP := card_le_card_map_killAt_mul H a
    have hK : 2 * Nat.card K ≤ m := by
      have hKt : K ≠ ⊤ := fun h => hHf a ha fun t => (h ▸ Subgroup.mem_top t : t ∈ K)
      have hdvd : Nat.card K ∣ m := hm a ▸ Subgroup.card_subgroup_dvd_card K
      have hne : Nat.card K ≠ m := fun h => hKt (Subgroup.card_eq_iff_eq_top K |>.1
        (h.trans (hm a).symm))
      have hm0 : m ≠ 0 := by rw [← hm a]; exact Nat.card_pos.ne'
      obtain ⟨c, hc⟩ := hdvd
      rcases c with _ | _ | c
      · simp at hc
        exact absurd hc hm0
      · simp at hc
        exact absurd hc.symm hne
      · rw [hc]
        nlinarith
    have hPs : P ≤ suppOn (s.erase a) := by
      rintro _ ⟨x, hx, rfl⟩ i hi
      rw [killAt_apply]
      split_ifs with hia
      · rfl
      · exact hHs hx i fun his => hi (Finset.mem_erase.2 ⟨hia, his⟩)
    have hcard1 : (s.erase a).card = n - 1 := by rw [Finset.card_erase_of_mem ha, hsn]
    have hn1 : 1 ≤ n := by rw [← hsn]; exact Finset.card_pos.2 ⟨a, ha⟩
    by_cases hb : ∃ b ∈ s.erase a, HasFactor P b
    · obtain ⟨b, hb, hPb⟩ := hb
      have hba : b ≠ a := (Finset.mem_erase.1 hb).1
      set P' := P.map (killAt b)
      have hPP := card_le_card_map_killAt_mul P b
      have hK' : Nat.card (P.comap (MonoidHom.mulSingle T b)) ≤ m :=
        hm b ▸ Subgroup.card_le_card_group _
      have hP's : P' ≤ suppOn ((s.erase a).erase b) := by
        rintro _ ⟨x, hx, rfl⟩ i hi
        rw [killAt_apply]
        split_ifs with hib
        · rfl
        · exact hPs hx i fun his => hi (Finset.mem_erase.2 ⟨hib, his⟩)
      have hP'f : ∀ c ∈ (s.erase a).erase b, ¬ HasFactor P' c := by
        intro c hc hP'c
        have hcb : c ≠ b := (Finset.mem_erase.1 hc).1
        have hca : c ≠ a := (Finset.mem_erase.1 (Finset.mem_erase.1 hc).2).1
        have hcs : c ∈ s := (Finset.mem_erase.1 (Finset.mem_erase.1 hc).2).2
        have hbs : b ∈ s := (Finset.mem_erase.1 hb).2
        -- `P` contains `T c` as well
        have hPc : HasFactor P c := by
          intro t
          obtain ⟨p, hp, hpt⟩ := hP'c t
          have : Pi.mulSingle c t = p * (Pi.mulSingle b (p b))⁻¹ := by
            funext i
            by_cases hib : i = b
            · subst hib
              simp [Pi.mulSingle_eq_of_ne hcb.symm]
            · have := congrFun hpt i
              simp only [killAt_apply, hib, ite_false] at this
              simp [hib, this]
          rw [this]
          exact P.mul_mem hp (P.inv_mem (hPb _))
        exact not_hasFactor_two hba.symm hca.symm hcb.symm (by rw [hm, hm]) (by rw [hm, hm])
          (hs a) (hs b) (hs c) (hna a) (hHf a ha) (hHf b hbs) (hHf c hcs) hPb hPc
      have hcard2 : ((s.erase a).erase b).card = n - 2 := by
        rw [Finset.card_erase_of_mem hb, hcard1]
        omega
      have hn2 : 2 ≤ n := by
        have : 1 ≤ (s.erase a).card := Finset.card_pos.2 ⟨b, hb⟩
        omega
      have hih := ih (n - 2) (by omega) _ hcard2 P' hP's hP'f
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 2 := ⟨n - 2, by omega⟩
      simp only [Nat.add_sub_cancel] at hih
      have hH : Nat.card H ≤ Nat.card P' * m * Nat.card K :=
        hHP.trans (Nat.mul_le_mul_right _ (hPP.trans (Nat.mul_le_mul_left _ hK')))
      calc 2 ^ (n' + 2) * Nat.card H ^ 2
          ≤ 2 ^ (n' + 2) * (Nat.card P' * m * Nat.card K) ^ 2 :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hH 2)
        _ = (2 ^ n' * Nat.card P' ^ 2) * m ^ 2 * (2 * Nat.card K) ^ 2 := by ring
        _ ≤ m ^ (2 * n') * m ^ 2 * m ^ 2 :=
            Nat.mul_le_mul (Nat.mul_le_mul_right _ hih) (Nat.pow_le_pow_left hK 2)
        _ = m ^ (2 * (n' + 2)) := by ring
    · push Not at hb
      have hih := ih (n - 1) (by omega) _ hcard1 P hPs hb
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      simp only [Nat.add_sub_cancel] at hih
      calc 2 ^ (n' + 1) * Nat.card H ^ 2
          ≤ 2 ^ (n' + 1) * (Nat.card P * Nat.card K) ^ 2 :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hHP 2)
        _ = (2 ^ n' * Nat.card P ^ 2) * (2 * Nat.card K ^ 2) := by ring
        _ ≤ m ^ (2 * n') * m ^ 2 := by
            refine Nat.mul_le_mul hih ?_
            have := Nat.pow_le_pow_left hK 2
            nlinarith
        _ = m ^ (2 * (n' + 1)) := by ring
  exact key _ Finset.univ Finset.card_univ H (fun x _ i hi => absurd (Finset.mem_univ i) hi)
    fun i _ => hH i

end GraphIso.Groups
