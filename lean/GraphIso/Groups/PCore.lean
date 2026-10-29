module

public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.Data.Set.Finite.Lemmas

/-!
# The `p′`-core

* `not_dvd_card_sup`: the join of two subgroups of order prime to `p`, one of them normal, has
  order prime to `p`.
* `exists_pcore`: a finite group has a normal subgroup of order prime to `p` that contains
  every such normal subgroup.
* `exists_normal_isPGroup_le`: in a solvable group with no nontrivial normal subgroup of
  order prime to `p`, every nontrivial normal subgroup contains a nontrivial normal
  `p`-subgroup: the Sylow `p`-subgroup of the last nontrivial term of its derived series.
* `centralizer_le_of_pcore`: if `H` is solvable with no nontrivial normal `p`-subgroup, the
  centralizer of its `p′`-core lies in the core.
-/

@[expose] public section

namespace GraphIso.Groups

open Subgroup
open scoped commutatorElement

/-- The join of two subgroups of order prime to `p`, one of them normal, has order prime to
`p`: its order is `|N|` times the index of `M ⊓ N` in `M`. -/
theorem not_dvd_card_sup {p : ℕ} (hp : p.Prime) {G : Type*} [Group G] [Finite G]
    {M N : Subgroup G} [N.Normal] (hM : ¬ p ∣ Nat.card M) (hN : ¬ p ∣ Nat.card N) :
    ¬ p ∣ Nat.card (M ⊔ N : Subgroup G) := by
  have h := relIndex_mul_card (H := N) (K := M ⊔ N)
  rw [inf_of_le_left le_sup_right, relIndex_sup_right] at h
  rw [← h]
  intro hd
  rcases hp.dvd_mul.mp hd with h1 | h1
  · exact hM (h1.trans (relIndex_dvd_card N M))
  · exact hN h1

/-- **The `p′`-core**: a normal subgroup of order prime to `p` containing every such. -/
theorem exists_pcore (p : ℕ) [Fact p.Prime] (H : Type*) [Group H] [Finite H] :
    ∃ N : Subgroup H, N.Normal ∧ ¬ p ∣ Nat.card N ∧
      ∀ M : Subgroup H, M.Normal → ¬ p ∣ Nat.card M → M ≤ N := by
  have hp : p.Prime := Fact.out
  let S : Set (Subgroup H) := {N | N.Normal ∧ ¬ p ∣ Nat.card N}
  have hne : S.Nonempty := ⟨⊥, inferInstance, by simpa using hp.not_dvd_one⟩
  obtain ⟨N, ⟨hN, hNp⟩, hmax⟩ :=
    S.exists_max_image (fun N : Subgroup H => Nat.card N) S.toFinite hne
  refine ⟨N, hN, hNp, fun M hM hMp => ?_⟩
  have hle : Nat.card (M ⊔ N : Subgroup H) ≤ Nat.card N :=
    hmax _ ⟨inferInstance, not_dvd_card_sup hp hMp hNp⟩
  have heq : N = M ⊔ N := eq_of_le_of_card_ge le_sup_right hle
  exact heq ▸ le_sup_left

/-- A nontrivial group has a term of its derived series that is nontrivial and whose successor
is trivial, if the series reaches `⊥`. -/
theorem exists_derivedSeries_last {G : Type*} [Group G] [Group.IsSolvable G] [Nontrivial G] :
    ∃ k, derivedSeries G k ≠ ⊥ ∧ derivedSeries G (k + 1) = ⊥ := by
  classical
  have hex : ∃ n, derivedSeries G n = ⊥ := Group.IsSolvable.solvable
  have h0 : Nat.find hex ≠ 0 := by
    intro h
    have h' := Nat.find_spec hex
    rw [h, derivedSeries_zero] at h'
    exact top_ne_bot h'
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero h0
  refine ⟨k, Nat.find_min hex (by omega), ?_⟩
  rw [← Nat.succ_eq_add_one, ← hk]
  exact Nat.find_spec hex

/-- **A nontrivial normal `p`-subgroup.** In a solvable group with no nontrivial normal
subgroup of order prime to `p`, every nontrivial normal subgroup `X` contains a nontrivial
normal `p`-subgroup. -/
theorem exists_normal_isPGroup_le {p : ℕ} [Fact p.Prime] {Q : Type*} [Group Q] [Finite Q]
    [Group.IsSolvable Q] {X : Subgroup Q} [X.Normal] (hX : X ≠ ⊥)
    (h : ∀ T : Subgroup Q, T.Normal → ¬ p ∣ Nat.card T → T = ⊥) :
    ∃ P : Subgroup Q, P.Normal ∧ IsPGroup p P ∧ P ≠ ⊥ ∧ P ≤ X := by
  have : Nontrivial X := (nontrivial_iff_ne_bot X).mpr hX
  obtain ⟨k, hk, hk1⟩ := exists_derivedSeries_last (G := X)
  set A := derivedSeries X k
  -- `A` is abelian
  have hcomm : ∀ a b : A, a * b = b * a := by
    intro a b
    have hab : ⁅(a : X), (b : X)⁆ ∈ ⁅A, A⁆ := commutator_mem_commutator a.2 b.2
    rw [← derivedSeries_succ, hk1, mem_bot, commutatorElement_eq_one_iff_mul_comm] at hab
    exact Subtype.ext hab
  by_cases hpA : p ∣ Nat.card A
  · obtain ⟨S⟩ : Nonempty (Sylow p A) := Sylow.nonempty
    have hSn : (S : Subgroup A).Normal :=
      ⟨fun s hs g => by rwa [hcomm g s, mul_inv_cancel_right]⟩
    have := Sylow.characteristic_of_normal S hSn
    refine ⟨((S : Subgroup A).map A.subtype).map X.subtype, inferInstance,
      (S.isPGroup'.map _).map _, ?_, map_subtype_le _⟩
    intro hbot
    rw [Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective,
      Subgroup.map_eq_bot_iff_of_injective _ A.subtype_injective] at hbot
    have hd := S.dvd_card_of_dvd_card hpA
    rw [hbot, card_bot] at hd
    exact (Fact.out : p.Prime).not_dvd_one hd
  · exfalso
    apply hk
    have hT := h (A.map X.subtype) inferInstance
      (by rwa [card_map_of_injective X.subtype_injective])
    rwa [Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective] at hT

/-- In `H ⧸ N`, for the `p′`-core `N`, every normal subgroup of order prime to `p` is trivial:
its preimage is a normal subgroup of order prime to `p`. -/
theorem eq_bot_of_pcore_quotient {p : ℕ} [Fact p.Prime] {H : Type*} [Group H] [Finite H]
    {N : Subgroup H} [N.Normal] (hNp : ¬ p ∣ Nat.card N)
    (hmax : ∀ M : Subgroup H, M.Normal → ¬ p ∣ Nat.card M → M ≤ N)
    (T : Subgroup (H ⧸ N)) (hT : T.Normal) (hTp : ¬ p ∣ Nat.card T) : T = ⊥ := by
  have hp : p.Prime := Fact.out
  set π := QuotientGroup.mk' N
  have hT' : ¬ p ∣ Nat.card (T.comap π) := by
    intro hd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hd
    have hxH : orderOf (x : H) = p := by rw [Subgroup.orderOf_coe]; exact hx
    have hdvd : orderOf (π x) ∣ p := hxH ▸ orderOf_map_dvd π (x : H)
    rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | h1
    · have hxN : (x : H) ∈ N := by
        rw [orderOf_eq_one_iff] at h1
        exact (QuotientGroup.eq_one_iff (x : H)).mp h1
      apply hNp
      have h2 : orderOf (⟨x, hxN⟩ : N) = p := by rw [← Subgroup.orderOf_coe]; exact hxH
      exact h2 ▸ orderOf_dvd_natCard (⟨x, hxN⟩ : N)
    · apply hTp
      have h2 : orderOf (⟨π x, x.2⟩ : T) = p := by rw [← Subgroup.orderOf_coe]; exact h1
      exact h2 ▸ orderOf_dvd_natCard (⟨π x, x.2⟩ : T)
  have hle := hmax _ (hT.comap π) hT'
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N y
  exact (QuotientGroup.eq_one_iff x).mpr (hle hy)

/-- **The centralizer of the `p′`-core** of a solvable group with no nontrivial normal
`p`-subgroup lies in the core. -/
theorem centralizer_le_of_pcore {p : ℕ} [Fact p.Prime] {H : Type*} [Group H] [Finite H]
    [Group.IsSolvable H] (hp : ∀ Q : Subgroup H, Q.Normal → IsPGroup p Q → Q = ⊥)
    {N : Subgroup H} (hN : N.Normal) (hNp : ¬ p ∣ Nat.card N)
    (hmax : ∀ M : Subgroup H, M.Normal → ¬ p ∣ Nat.card M → M ≤ N) :
    Subgroup.centralizer (N : Set H) ≤ N := by
  have hp' : p.Prime := Fact.out
  set C := Subgroup.centralizer (N : Set H)
  by_contra hCN
  set π := QuotientGroup.mk' N
  -- the image of `C` in `H ⧸ N` is a nontrivial normal subgroup
  have hX : C.map π ≠ ⊥ := by
    intro h
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    exact hCN h
  have : (C.map π).Normal :=
    (Subgroup.normal_centralizer (H := N)).map π (QuotientGroup.mk'_surjective N)
  obtain ⟨P, hPn, hPp, hP0, hPX⟩ :=
    exists_normal_isPGroup_le hX (eq_bot_of_pcore_quotient hNp hmax)
  -- its preimage `L` lies in `C ⊔ N`
  set L := P.comap π
  have hNL : N ≤ L := fun x hx => by
    change π x ∈ P
    rw [show π x = 1 from (QuotientGroup.eq_one_iff x).mpr hx]
    exact P.one_mem
  have hLC : ∀ x ∈ L, ∃ c ∈ C, c⁻¹ * x ∈ N := by
    intro x hx
    obtain ⟨c, hc, hcx⟩ := hPX hx
    exact ⟨c, hc, QuotientGroup.eq.mp hcx⟩
  -- `D = L ⊓ C` is nilpotent: a central extension of `D ⊓ N` by a subgroup of `P`
  set D := L ⊓ C
  have : L.Normal := hPn.comap π
  have : D.Normal := inferInstance
  let f : D →* P := (π.comp D.subtype).codRestrict P fun d => d.2.1
  have hker : f.ker ≤ center D := by
    intro d hd
    have hdN : (d : H) ∈ N := by
      have h1 : π d = 1 := congrArg Subtype.val hd
      exact (QuotientGroup.eq_one_iff (d : H)).mp h1
    rw [mem_center_iff]
    intro e
    exact Subtype.ext ((mem_centralizer_iff.mp e.2.2) d hdN).symm
  have : Group.IsNilpotent P := hPp.isNilpotent
  have : Group.IsNilpotent D := Subgroup.isNilpotent_of_ker_le_center f hker
  -- its Sylow `p`-subgroup is normal in `H`, hence trivial, so `D` has order prime to `p`
  obtain ⟨S⟩ : Nonempty (Sylow p D) := Sylow.nonempty
  have hSn : (S : Subgroup D).Normal := inferInstance
  have := Sylow.characteristic_of_normal S hSn
  have hS1 := hp ((S : Subgroup D).map D.subtype) inferInstance (S.isPGroup'.map _)
  rw [Subgroup.map_eq_bot_iff_of_injective _ D.subtype_injective] at hS1
  have hDp : ¬ p ∣ Nat.card D := by
    intro hd
    have h1 := S.dvd_card_of_dvd_card hd
    rw [hS1, card_bot] at h1
    exact hp'.not_dvd_one h1
  have hDN : D ≤ N := le_sup_left.trans (hmax _ inferInstance (not_dvd_card_sup hp' hDp hNp))
  -- so `L ≤ N`, and `P` is trivial
  have hLN : L ≤ N := by
    intro x hx
    obtain ⟨c, hc, hcx⟩ := hLC x hx
    have hcL : c ∈ L := by
      have := L.mul_mem hx (L.inv_mem (hNL hcx))
      rwa [mul_inv_rev, inv_inv, mul_inv_cancel_left] at this
    rw [show x = c * (c⁻¹ * x) by group]
    exact N.mul_mem (hDN ⟨hcL, hc⟩) hcx
  apply hP0
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N y
  exact (QuotientGroup.eq_one_iff x).mpr (hLN hy)

end GraphIso.Groups
