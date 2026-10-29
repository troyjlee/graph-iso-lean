module

public import GraphIso.SplitJohnson.BipartiteBasic
public import GraphIso.Coherent.RCW
public import GraphIso.Coherent.Design
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Logic.Equiv.Fintype

/-!
# Bipartite Split-or-Johnson: the Johnson test and the `d`-ary structure

Under the invariant `BInv`, let `V₁'` be the points without twins of a degree `d₁` with more
than `t` of them. Their neighbourhoods (complemented if `2d₁ > |V₂|`) are distinct
`s`-subsets of `V₂` with `2 ≤ s ≤ |V₂|/2`.

* `johnson_valid`: if every `s`-subset occurs, `V₁'` is a Johnson scheme `J(|V₂|, s)`.
* `bigTwins_card_lt`: otherwise, outside the base case, the `d`-ary structure `daryCol` on `V₂`
  is not invariant under all of `Sym(V₂)`, so its twin class of more than half of `V₂` (if any)
  is a proper subset. For `d = s` the structure is the hypergraph itself; for `d = 6j < s` a
  constant structure would make the neighbourhoods a `d`-design, and Ray-Chaudhuri–Wilson would
  give `|V₁'| ≥ C(v, 3j) > v^j ≥ |V₁'|` (using `v² > 27 j³`).
* `exists_dlGood`: without a large twin class the Design Lemma (with threshold `⌊2v/3⌋`) gives a
  good list of fewer than `d` points.
-/

@[expose] public section

namespace GraphIso.SplitJohnson

open Finset Pointwise GraphIso.Coherent

variable {α : Type*} [DecidableEq α]

/-! ### Twins of a `k`-ary structure -/

section Twins

variable {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}

omit [Fintype V] in
/-- Twins compose: if `u` and `w` are both twins of `z`, they are twins. -/
theorem isTwin_of_isTwin_of_isTwin {c : (Fin k → V) → ℕ} {u w z : V} (huz : IsTwin c u z)
    (hwz : IsTwin c w z) : IsTwin c u w := by
  by_cases huw : u = w
  · subst huw
    intro x
    rw [Equiv.swap_self]
    rfl
  by_cases hw : w = z
  · subst hw
    exact huz
  intro x
  have e := Equiv.swap_mul_swap_mul_swap (x := w) (y := z) (z := u) hw (Ne.symm huw)
  rw [← e, Equiv.Perm.coe_mul, Equiv.Perm.coe_mul]
  have h1 : ∀ y : Fin k → V, c (⇑(Equiv.swap z u) ∘ y) = c y := fun y => by
    rw [Equiv.swap_comm]
    exact huz y
  simp only [Function.comp_assoc]
  rw [h1, hwz, h1]

/-- If all points are pairwise twins, the structure is invariant under every permutation. -/
theorem invariant_of_forall_isTwin {c : (Fin k → V) → ℕ} (h : ∀ u w, IsTwin c u w)
    (π : Equiv.Perm V) (x : Fin k → V) : c (⇑π ∘ x) = c x := by
  induction π using Equiv.Perm.swap_induction_on generalizing x with
  | one => rfl
  | swap_mul f a b _ ih =>
    rw [Equiv.Perm.coe_mul, Function.comp_assoc, h a b, ih]

end Twins

/-! ### Enumerations and counts -/

section Counts

theorem exists_enum {β : Type*} [DecidableEq β] (D : Finset β) :
    ∃ x : Fin D.card → β, Function.Injective x ∧ univ.image x = D := by
  refine ⟨fun i => (D.equivFin.symm i).val, fun i j hij => ?_, ?_⟩
  · exact D.equivFin.symm.injective (Subtype.ext hij)
  · ext b
    simp only [mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact (D.equivFin.symm i).2
    · intro hb
      exact ⟨D.equivFin ⟨b, hb⟩, by simp⟩

theorem exists_enum_of_card {β : Type*} [DecidableEq β] {D : Finset β} {d : ℕ} (hD : D.card = d) :
    ∃ x : Fin d → β, Function.Injective x ∧ univ.image x = D := by
  subst hD
  exact exists_enum D

theorem card_filter_univ_coe {β : Type*} (s : Finset β) (P : β → Prop) [DecidablePred P] :
    (univ.filter fun b : s => P b.val).card = (s.filter P).card := by
  rw [← card_map (Function.Embedding.subtype _)]
  congr 1
  ext b
  simp [and_comm]

/-- The colour of an injective tuple. -/
theorem daryCol_of_injective {V₂ : Finset (Finset α)} {H : Finset (Finset (Finset α))} {d : ℕ}
    {x : Fin d → V₂} (hx : Function.Injective x) :
    daryCol V₂ H d x =
      1 + (H.filter fun e => (univ.image x).map (Function.Embedding.subtype _) ⊆ e).card := by
  have himg : (univ.image fun i => (x i).val) =
      (univ.image x).map (Function.Embedding.subtype _) := by
    ext b
    simp
  have hcard : (univ.image fun i => (x i).val).card = d := by
    rw [card_image_of_injective _
      (show Function.Injective fun i => (x i).val from Subtype.val_injective.comp hx),
      card_univ, Fintype.card_fin]
  unfold daryCol
  rw [himg] at hcard ⊢
  simp only [hcard, ↓reduceIte]

/-- A structure invariant under all permutations counts the sets of `H` above every `d`-subset
of `V₂` the same. -/
theorem cnt_eq_of_invariant {V₂ : Finset (Finset α)} {H : Finset (Finset (Finset α))} {d : ℕ}
    (hinv : ∀ (π : Equiv.Perm V₂) (x : Fin d → V₂), daryCol V₂ H d (⇑π ∘ x) = daryCol V₂ H d x)
    {D D' : Finset V₂} (hD : D.card = d) (hD' : D'.card = d) :
    (H.filter fun e => D.map (Function.Embedding.subtype _) ⊆ e).card =
      (H.filter fun e => D'.map (Function.Embedding.subtype _) ⊆ e).card := by
  classical
  obtain ⟨x, hxi, hxD⟩ := exists_enum_of_card hD
  let e : D ≃ D' := Fintype.equivOfCardEq (by rw [Fintype.card_coe, Fintype.card_coe, hD, hD'])
  let π : Equiv.Perm V₂ := Equiv.extendSubtype e
  have hπ : ∀ i, π (x i) = (e ⟨x i, hxD ▸ mem_image_of_mem x (mem_univ i)⟩).val := fun i => by
    simp only [π]
    rw [Equiv.extendSubtype_apply_of_mem]
  have hyi : Function.Injective (⇑π ∘ x) := π.injective.comp hxi
  have hyD : univ.image (⇑π ∘ x) = D' := by
    refine eq_of_subset_of_card_le ?_ ?_
    · intro b hb
      obtain ⟨i, -, rfl⟩ := mem_image.1 hb
      simp only [Function.comp_apply, hπ]
      exact (e _).2
    · rw [card_image_of_injective _ hyi, card_univ, Fintype.card_fin, hD']
  have h1 := daryCol_of_injective (H := H) hxi
  have h2 := daryCol_of_injective (H := H) hyi
  rw [hxD] at h1
  rw [hyD] at h2
  have := hinv π x
  omega

end Counts

/-! ### The points without twins of a large degree -/

section Large

variable {t : ℕ} {V₁ : Finset α} {V₂ : Finset (Finset α)} {A : α → Finset α → Bool}

omit [DecidableEq α] in
theorem mem_tfDeg {d : ℕ} {x : α} :
    x ∈ tfDeg V₁ V₂ A d ↔ x ∈ V₁ ∧ tw V₁ V₂ A x = 1 ∧ deg V₂ A x = d := by
  simp [tfDeg]

omit [DecidableEq α] in
theorem nbr_subset (x : α) : nbr V₂ A x ⊆ V₂ := filter_subset _ _

omit [DecidableEq α] in
/-- Points without twins have distinct neighbourhoods. -/
theorem nbr_injOn (d : ℕ) : Set.InjOn (nbr V₂ A) (tfDeg V₁ V₂ A d) := by
  intro x hx y hy hxy
  rw [Finset.mem_coe, mem_tfDeg] at hx hy
  have hmem : y ∈ twinCls V₁ V₂ A x := by
    rw [mem_twinCls]
    refine ⟨hy.1, fun s hs => ?_⟩
    have := congrArg (s ∈ ·) hxy
    simp only [nbr, mem_filter, hs, true_and, eq_iff_iff] at this
    exact Bool.eq_iff_iff.2 this
  obtain ⟨a, ha⟩ := card_eq_one.1 hx.2.1
  have hx' := self_mem_twinCls (V₂ := V₂) (A := A) hx.1
  rw [ha, mem_singleton] at hmem hx'
  rw [hmem, hx']

theorem choose_le_of_extreme {v d : ℕ} (h : d < 2 ∨ v < d + 2) : v.choose d ≤ max v 1 := by
  rcases h with h | h
  · obtain rfl | rfl : d = 0 ∨ d = 1 := by omega
    · simp
    · simp
  · rcases lt_trichotomy v d with h' | rfl | h'
    · rw [Nat.choose_eq_zero_of_lt h']
      omega
    · simp
    · obtain rfl : v = d + 1 := by omega
      rw [Nat.choose_succ_self_right]
      omega

/-- **The degree of the large class**: `2 ≤ d₁ ≤ |V₂| − 2`. -/
theorem bounds_of_mem_bigDegs (h : BInv t V₁ V₂ A) {d₁ : ℕ} (hd : d₁ ∈ bigDegs t V₁ V₂ A) :
    2 ≤ d₁ ∧ d₁ + 2 ≤ V₂.card := by
  have ht := (mem_filter.1 hd).2
  have hle : (tfDeg V₁ V₂ A d₁).card ≤ V₂.card.choose d₁ := by
    rw [← card_image_of_injOn (nbr_injOn d₁), ← card_powersetCard]
    refine card_le_card fun e he => ?_
    obtain ⟨x, hx, rfl⟩ := mem_image.1 he
    rw [mem_tfDeg] at hx
    exact mem_powersetCard.2 ⟨nbr_subset x, hx.2.2⟩
  by_contra hne
  have := choose_le_of_extreme (v := V₂.card) (d := d₁) (by omega)
  have h1 := h.v_le
  have h2 := h.v₁_le
  omega

theorem sOf_bounds {v d₁ : ℕ} (h1 : 2 ≤ d₁) (h2 : d₁ + 2 ≤ v) :
    2 ≤ sOf v d₁ ∧ 2 * sOf v d₁ ≤ v := by
  unfold sOf
  split_ifs <;> omega

theorem fOf_mem {d₁ : ℕ} {x : α} (hx : x ∈ tfDeg V₁ V₂ A d₁) :
    fOf V₂ A d₁ x ∈ V₂.powersetCard (sOf V₂.card d₁) := by
  rw [mem_tfDeg] at hx
  have hc : (nbr V₂ A x).card = d₁ := hx.2.2
  rw [mem_powersetCard]
  unfold fOf sOf
  split_ifs
  · exact ⟨sdiff_subset, by rw [card_sdiff_of_subset (nbr_subset x), hc]⟩
  · exact ⟨nbr_subset x, hc⟩

theorem fOf_injOn (d₁ : ℕ) : Set.InjOn (fOf V₂ A d₁) (tfDeg V₁ V₂ A d₁) := by
  intro x hx y hy hxy
  refine nbr_injOn d₁ hx hy ?_
  unfold fOf at hxy
  split_ifs at hxy
  · rw [← Finset.sdiff_sdiff_eq_self (nbr_subset (V₂ := V₂) (A := A) x),
      ← Finset.sdiff_sdiff_eq_self (nbr_subset (V₂ := V₂) (A := A) y), hxy]
  · exact hxy

theorem card_image_fOf (d₁ : ℕ) :
    ((tfDeg V₁ V₂ A d₁).image (fOf V₂ A d₁)).card = (tfDeg V₁ V₂ A d₁).card :=
  card_image_of_injOn (fOf_injOn d₁)

omit [DecidableEq α] in
theorem six_le_of_not_isBase (h : BInv t V₁ V₂ A) (hb : ¬ IsBase t V₂.card) : 6 ≤ V₂.card := by
  have h1 := h.v₁_le
  have hL : 1 ≤ Nat.clog 2 (2 * t) := Nat.clog_pos (by norm_num) (by omega)
  have hL3 : 1 ≤ Nat.clog 2 (2 * t) ^ 3 := Nat.one_le_pow _ _ hL
  unfold IsBase at hb
  by_contra hv
  have : V₂.card ^ 2 ≤ 5 ^ 2 := Nat.pow_le_pow_left (by omega) 2
  omega

end Large

/-! ### Arithmetic -/

/-- `v^k ≤ C(v, k) k^k` for `k ≤ v`. -/
theorem pow_le_choose_mul_pow {v k : ℕ} (hk : k ≤ v) : v ^ k ≤ v.choose k * k ^ k := by
  have hfac : k.factorial = ∏ i ∈ range k, (k - i) := by
    rw [Nat.factorial_eq_prod_range_add_one, ← prod_range_reflect]
    refine prod_congr rfl fun i hi => ?_
    have := mem_range.1 hi
    omega
  have key : k.factorial * v ^ k ≤ k.factorial * (v.choose k * k ^ k) := by
    rw [← mul_assoc, ← Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_prod_range,
      hfac, show v ^ k = ∏ _i ∈ range k, v by rw [prod_const, card_range],
      show k ^ k = ∏ _i ∈ range k, k by rw [prod_const, card_range], ← prod_mul_distrib,
      ← prod_mul_distrib]
    refine prod_le_prod fun i hi => ?_
    have hi := mem_range.1 hi
    obtain ⟨a, rfl⟩ : ∃ a, k = i + a := ⟨k - i, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, v = i + a + b := ⟨v - (i + a), by omega⟩
    rw [show i + a - i = a by omega, show i + a + b - i = a + b by omega]
    nlinarith
  exact Nat.le_of_mul_le_mul_left key (Nat.factorial_pos k)

/-- The contradiction of the design case: `C(v, 3j) ≤ n₁ ≤ v^j` is impossible when
`27 j³ < v²`. -/
theorem choose_gt_of_cube {v j n₁ : ℕ} (hj : 1 ≤ j) (hn : n₁ ≤ v ^ j) (hjv : 27 * j ^ 3 < v ^ 2)
    (h3 : 3 * j ≤ v) : n₁ < v.choose (3 * j) := by
  by_contra hc
  rw [not_lt] at hc
  have hv : 0 < v := by omega
  have e1 : v ^ (3 * j) ≤ v.choose (3 * j) * (3 * j) ^ (3 * j) := pow_le_choose_mul_pow h3
  have e2 : (3 * j) ^ (3 * j) < v ^ (2 * j) := by
    rw [pow_mul, pow_mul, show (3 * j) ^ 3 = 27 * j ^ 3 by ring]
    exact Nat.pow_lt_pow_left hjv (by omega)
  have e3 : v.choose (3 * j) * (3 * j) ^ (3 * j) ≤ v ^ j * (3 * j) ^ (3 * j) :=
    Nat.mul_le_mul_right _ (hc.trans hn)
  have e4 : v ^ j * (3 * j) ^ (3 * j) < v ^ j * v ^ (2 * j) :=
    Nat.mul_lt_mul_of_pos_left e2 (pow_pos hv j)
  rw [← pow_add, show j + 2 * j = 3 * j by ring] at e4
  omega

/-! ### Lists of bounded length -/

theorem mem_tuples_length {β : Type*} [DecidableEq β] {S : Finset β} :
    ∀ x : List β, (∀ a ∈ x, a ∈ S) → x ∈ tuples S x.length
  | [], _ => by simp [tuples]
  | a :: l, h => by
    show a :: l ∈ tuples S (l.length + 1)
    simp only [tuples, mem_image, mem_product, Prod.exists]
    exact ⟨a, l, ⟨h a (by simp), mem_tuples_length l fun b hb => h b (by simp [hb])⟩, rfl⟩

theorem mem_tuplesLt_of {β : Type*} [DecidableEq β] {S : Finset β} {d : ℕ} {x : List β}
    (hx : x.length < d) (h : ∀ a ∈ x, a ∈ S) : x ∈ tuplesLt S d :=
  mem_biUnion.2 ⟨x.length, mem_range.2 hx, mem_tuples_length x h⟩

/-- **The Johnson case.** -/
theorem johnson_valid {t : ℕ} {V₁ : Finset α} {V₂ : Finset (Finset α)}
    {A : α → Finset α → Bool} (h : BInv t V₁ V₂ A) {d₁ : ℕ} (hd : d₁ ∈ bigDegs t V₁ V₂ A)
    (hJ : (tfDeg V₁ V₂ A d₁).card = V₂.card.choose (sOf V₂.card d₁)) :
    IsJohnson V₁ t ⟨tfDeg V₁ V₂ A d₁, V₂, sOf V₂.card d₁, fOf V₂ A d₁⟩ := by
  obtain ⟨hd2, hdv⟩ := bounds_of_mem_bigDegs h hd
  obtain ⟨hs2, hsv⟩ := sOf_bounds hd2 hdv
  have hsub : (tfDeg V₁ V₂ A d₁).image (fOf V₂ A d₁) ⊆ V₂.powersetCard (sOf V₂.card d₁) := by
    intro e he
    obtain ⟨x, hx, rfl⟩ := mem_image.1 he
    exact fOf_mem hx
  have heq := eq_of_subset_of_card_le hsub (by rw [card_powersetCard, card_image_fOf, hJ])
  refine ⟨fun x hx => (mem_tfDeg.1 hx).1, (mem_filter.1 hd).2, hs2, hsv, h.cells_ne,
    h.cells_disj, fun x hx => fOf_mem hx,
    fun x hx y hy hxy => fOf_injOn d₁ (mem_coe.2 hx) (mem_coe.2 hy) hxy, fun T hT => ?_⟩
  rw [← heq] at hT
  obtain ⟨x, hx, rfl⟩ := mem_image.1 hT
  exact ⟨x, hx, rfl⟩

/-- The arity is at least two. -/
theorem two_le_arity {t : ℕ} {V₁ : Finset α} {V₂ : Finset (Finset α)}
    {A : α → Finset α → Bool} (h : BInv t V₁ V₂ A) (hb : ¬ IsBase t V₂.card) {d₁ : ℕ}
    (hd : d₁ ∈ bigDegs t V₁ V₂ A) :
    2 ≤ arity V₂.card (sOf V₂.card d₁) (tfDeg V₁ V₂ A d₁).card := by
  obtain ⟨hd2, hdv⟩ := bounds_of_mem_bigDegs h hd
  obtain ⟨hs2, -⟩ := sOf_bounds hd2 hdv
  have hv := six_le_of_not_isBase h hb
  have ht := (mem_filter.1 hd).2
  have hvt := h.v_le
  have hj : 0 < Nat.clog V₂.card (tfDeg V₁ V₂ A d₁).card := Nat.clog_pos (by omega) (by omega)
  unfold arity
  omega

/-- **The `d`-ary structure is not symmetric**: its large twin class is a proper subset. -/
theorem bigTwins_card_lt {t : ℕ} {V₁ : Finset α} {V₂ : Finset (Finset α)}
    {A : α → Finset α → Bool} (h : BInv t V₁ V₂ A) (hb : ¬ IsBase t V₂.card) {d₁ : ℕ}
    (hd : d₁ ∈ bigDegs t V₁ V₂ A)
    (hJ : (tfDeg V₁ V₂ A d₁).card ≠ V₂.card.choose (sOf V₂.card d₁)) :
    (bigTwins V₂ (daryCol V₂ ((tfDeg V₁ V₂ A d₁).image (fOf V₂ A d₁))
      (arity V₂.card (sOf V₂.card d₁) (tfDeg V₁ V₂ A d₁).card))).card < V₂.card := by
  obtain ⟨hd2, hdv⟩ := bounds_of_mem_bigDegs h hd
  obtain ⟨hs2, hsv⟩ := sOf_bounds hd2 hdv
  have hv6 := six_le_of_not_isBase h hb
  have ht := (mem_filter.1 hd).2
  have hvt := h.v_le
  have h1 := h.v₁_le
  have hn₁ : (tfDeg V₁ V₂ A d₁).card ≤ 2 * t := by
    have := card_le_card (fun x hx => (mem_tfDeg.1 hx).1 : tfDeg V₁ V₂ A d₁ ⊆ V₁)
    omega
  have hHcard := card_image_fOf (V₁ := V₁) (V₂ := V₂) (A := A) d₁
  set V' := tfDeg V₁ V₂ A d₁ with hV'
  set H := V'.image (fOf V₂ A d₁) with hH
  have hHmem : ∀ e ∈ H, e ⊆ V₂ ∧ e.card = sOf V₂.card d₁ := by
    intro e he
    obtain ⟨x, hx, rfl⟩ := mem_image.1 he
    exact mem_powersetCard.1 (fOf_mem hx)
  set j := Nat.clog V₂.card V'.card with hjdef
  have hj : 1 ≤ j := Nat.clog_pos (by omega) (by omega)
  set d := arity V₂.card (sOf V₂.card d₁) V'.card with hddef
  set cd := daryCol V₂ H d with hcd
  by_contra hlt
  rw [not_lt] at hlt
  -- all points of `V₂` are twins
  have hall : ∀ u w : V₂, IsTwin cd u w := by
    have hfilt : (univ.filter fun u : V₂ =>
        V₂.card < 2 * (univ.filter fun w => IsTwin cd u w).card) = univ := by
      apply eq_univ_of_card
      refine le_antisymm (card_le_univ _) ?_
      rw [Fintype.card_coe]
      unfold bigTwins at hlt
      rwa [card_map] at hlt
    have hbig : ∀ u : V₂, V₂.card < 2 * (univ.filter fun w => IsTwin cd u w).card := by
      intro u
      have := mem_univ u
      rw [← hfilt] at this
      exact (mem_filter.1 this).2
    intro u w
    have hu := hbig u
    have hw := hbig w
    have hinter : ((univ.filter fun z => IsTwin cd u z) ∩
        (univ.filter fun z => IsTwin cd w z)).Nonempty := by
      rw [← card_pos]
      have := card_union_add_card_inter (univ.filter fun z => IsTwin cd u z)
        (univ.filter fun z => IsTwin cd w z)
      have := card_le_univ ((univ.filter fun z => IsTwin cd u z) ∪
        (univ.filter fun z => IsTwin cd w z))
      rw [Fintype.card_coe] at this
      omega
    obtain ⟨z, hz⟩ := hinter
    rw [mem_inter, mem_filter, mem_filter] at hz
    exact isTwin_of_isTwin_of_isTwin hz.1.2 hz.2.2
  have hinv := invariant_of_forall_isTwin hall
  -- so the number of sets of `H` above a `d`-subset of `V₂` is a constant `l ≥ 1`
  have hconst : ∀ T T' : Finset (Finset α), T ⊆ V₂ → T' ⊆ V₂ → T.card = d → T'.card = d →
      (H.filter fun e => T ⊆ e).card = (H.filter fun e => T' ⊆ e).card := by
    intro T T' hT hT' hTc hT'c
    have key : ∀ T : Finset (Finset α), T ⊆ V₂ →
        (T.subtype (· ∈ V₂)).map (Function.Embedding.subtype _) = T ∧
          (T.subtype (· ∈ V₂)).card = T.card := fun T hT =>
      ⟨subtype_map_of_mem fun x hx => hT hx,
        by rw [card_subtype, filter_true_of_mem fun x hx => hT hx]⟩
    obtain ⟨e1, c1⟩ := key T hT
    obtain ⟨e2, c2⟩ := key T' hT'
    have := cnt_eq_of_invariant (H := H) hinv (D := T.subtype (· ∈ V₂))
      (D' := T'.subtype (· ∈ V₂)) (by rw [c1, hTc]) (by rw [c2, hT'c])
    rwa [e1, e2] at this
  obtain ⟨x₀, hx₀⟩ : V'.Nonempty := card_pos.1 (by omega)
  have he₀ := hHmem _ (mem_image_of_mem _ hx₀)
  have hds : d ≤ sOf V₂.card d₁ := min_le_left _ _
  obtain ⟨T₀, hT₀e, hT₀c⟩ := exists_subset_card_eq (s := fOf V₂ A d₁ x₀) (n := d)
    (by rw [he₀.2]; exact hds)
  have hl : 1 ≤ (H.filter fun e => T₀ ⊆ e).card :=
    card_pos.2 ⟨_, mem_filter.2 ⟨mem_image_of_mem _ hx₀, hT₀e⟩⟩
  have hreg : ∀ T ⊆ V₂, T.card = d →
      (H.filter fun e => T ⊆ e).card = (H.filter fun e => T₀ ⊆ e).card := fun T hT hTc =>
    hconst T T₀ hT (hT₀e.trans he₀.1) hTc hT₀c
  by_cases hsj : sOf V₂.card d₁ ≤ 6 * j
  · -- `d = s`: every `s`-subset of `V₂` is a neighbourhood
    have hd' : d = sOf V₂.card d₁ := min_eq_left hsj
    have hsubH : V₂.powersetCard (sOf V₂.card d₁) ⊆ H := by
      intro T hT
      rw [mem_powersetCard] at hT
      have hpos := (hreg T hT.1 (by rw [hT.2, hd'])).symm ▸ hl
      obtain ⟨e, he⟩ := card_pos.1 hpos
      rw [mem_filter] at he
      have : T = e := eq_of_subset_of_card_le he.2 (by rw [(hHmem e he.1).2, hT.2])
      rw [this]
      exact he.1
    have hHsub : H ⊆ V₂.powersetCard (sOf V₂.card d₁) := fun e he =>
      mem_powersetCard.2 (hHmem e he)
    apply hJ
    rw [← hHcard, ← card_powersetCard]
    exact le_antisymm (card_le_card hHsub) (card_le_card hsubH)
  · -- `d = 6j < s`: a `6j`-design, against Ray-Chaudhuri–Wilson
    have hd' : d = 6 * j := min_eq_right (by omega)
    have hrcw := ray_chaudhuri_wilson (B := H) V₂ (fun b => b.val) (s := 3 * j) (t := 6 * j)
      (u := sOf V₂.card d₁) (l := (H.filter fun e => T₀ ⊆ e).card)
      (fun b => (hHmem b.1 b.2).1) (fun b => (hHmem b.1 b.2).2)
      (fun T hT hTc => by
        rw [card_filter_univ_coe H (fun e => T ⊆ e)]
        exact hreg T hT (by rw [hTc, hd']))
      hl (by omega) (by omega) (by omega)
    rw [Fintype.card_coe, hHcard] at hrcw
    have hjL : j ≤ Nat.clog 2 (2 * t) :=
      (Nat.clog_anti_left (by norm_num) (by omega)).trans (Nat.clog_mono_right 2 hn₁)
    have hjv : 27 * j ^ 3 < V₂.card ^ 2 := by
      unfold IsBase at hb
      have := Nat.pow_le_pow_left hjL 3
      omega
    have := choose_gt_of_cube hj (Nat.le_pow_clog (by omega) V'.card) hjv (by omega)
    omega

/-- **The Design Lemma's choice exists** when no twin class has more than half of `V₂`. -/
theorem exists_dlGood {V₂ : Finset (Finset α)} {d : ℕ} (hd : 2 ≤ d) (hv : 2 ≤ V₂.card)
    (cd : (Fin d → V₂) → ℕ) (hS : bigTwins V₂ cd = ∅) :
    ∃ x ∈ tuplesLt univ d, DLGood (wlOn d cd) (2 * V₂.card / 3) x := by
  have hsmall : ∀ u : V₂, 2 * (univ.filter fun w => IsTwin cd u w).card ≤ V₂.card := by
    intro u
    unfold bigTwins at hS
    have hu := filter_eq_empty_iff.1 (map_eq_empty.1 hS) (mem_univ u)
    simpa using hu
  have hcard : Fintype.card V₂ = V₂.card := Fintype.card_coe V₂
  obtain ⟨x, hx, hgood⟩ := design_lemma (V := V₂) (t := 2 * V₂.card / 3) hd
    (wlOn_isCoherent cd) (by rw [hcard]; omega) (by
      intro T hT
      rcases T.eq_empty_or_nonempty with rfl | ⟨u, hu⟩
      · simp
      · have hsub : T ⊆ univ.filter fun w => IsTwin cd u w := fun w hw =>
          mem_filter.2 ⟨mem_univ _, (isTwin_wlOn_iff cd u w).1 (hT u hu w hw)⟩
        have := card_le_card hsub
        have := hsmall u
        omega)
  exact ⟨x, mem_tuplesLt_of hx fun a _ => mem_univ a, hgood⟩

end GraphIso.SplitJohnson
