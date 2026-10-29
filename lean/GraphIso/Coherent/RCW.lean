module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Rat.Defs
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Data.Finset.Powerset

/-!
# The Ray-Chaudhuri–Wilson inequality

**Ray-Chaudhuri–Wilson** (Helfgott, Prop. 2.20; D. K. Ray-Chaudhuri, R. M. Wilson, *On
t-designs*, Osaka J. Math. 12 (1975)): let `A : B → Finset P` be a family of `u`-subsets of
`V`, repeated blocks allowed, in which every `t`-subset of `V` lies in exactly `l ≥ 1` blocks.
If `2s ≤ t ≤ u` and `s + u ≤ |V|`, there are at least `C(|V|, s)` blocks
(`ray_chaudhuri_wilson`).

The proof is the linear-algebra one, in the style of Fisher's inequality.
* Let `cnt T` be the number of blocks containing `T`, and `lam I J` the number containing `I`
  and disjoint from `J`. By double counting, `cnt T` depends only on `|T|` for `|T| ≤ t`
  (`cnt_eq_of_card`), and then `lam I J` only on `|I|` and `|J|` for `|I| + |J| ≤ t`
  (`lam_eq_of_card`). Write `c i` for the value with `|I| + |J| = 2s` and `|J| = i`.
* Splitting the blocks containing `S ∪ S'` by their trace on a set of `|S ∩ S'|` points outside
  `S ∪ S'` gives `cnt (S ∪ S') = Σ_{i ≤ s} c i · C(|S ∩ S'|, i)` for `s`-subsets `S`, `S'`.
* So the `ℚ`-linear map `x ↦ (b ↦ Σ_{S ⊆ A b} x S)` on functions on the `s`-subsets of `V`
  satisfies `Σ_b (Σ_{S ⊆ A b} x S)² = Σ_{i ≤ s} c i Σ_{|I| = i} (Σ_{S ⊇ I} x S)²`. All terms are
  nonnegative and `c s ≥ 1` (a block containing an `s`-set `I` misses some `s`-set `J`), and the
  term `i = s` is `Σ_S (x S)²`. So the map is injective, and the number of `s`-subsets is at most
  the number of blocks.
-/

@[expose] public section

namespace GraphIso.Coherent

open Finset

section RCW

variable {P B : Type*} [DecidableEq P] [Fintype B] (A : B → Finset P)

/-- The number of blocks containing `T`. -/
def rcwCnt (T : Finset P) : ℕ := (univ.filter fun b => T ⊆ A b).card

/-- The number of blocks containing `I` and disjoint from `J`. -/
def rcwLam (I J : Finset P) : ℕ := (univ.filter fun b => I ⊆ A b ∧ Disjoint (A b) J).card

/-- Double counting the pairs `(b, x)` with `T ⊆ A b` and `x ∈ A b \ T`. -/
theorem sub_mul_rcwCnt {V : Finset P} {u : ℕ} (hA : ∀ b, A b ⊆ V) (hu : ∀ b, (A b).card = u)
    (T : Finset P) : (u - T.card) * rcwCnt A T = ∑ x ∈ V \ T, rcwCnt A (insert x T) := by
  simp only [rcwCnt]
  simp_rw [card_filter]
  rw [sum_comm, mul_sum]
  refine sum_congr rfl fun b _ => ?_
  by_cases hT : T ⊆ A b
  · simp only [hT, ↓reduceIte, mul_one]
    rw [← card_filter]
    have e : (V \ T).filter (fun x => insert x T ⊆ A b) = A b \ T := by
      ext x
      simp only [mem_filter, mem_sdiff, insert_subset_iff]
      exact ⟨fun h => ⟨h.2.1, h.1.2⟩, fun h => ⟨⟨hA b h.1, h.2⟩, h.1, hT⟩⟩
    rw [e, card_sdiff_of_subset hT, hu]
  · simp only [hT, ↓reduceIte, mul_zero]
    refine (sum_eq_zero fun x _ => ?_).symm
    have : ¬ insert x T ⊆ A b := fun h => hT ((subset_insert x T).trans h)
    simp only [this, ↓reduceIte]

/-- **`cnt T` depends only on `|T|`** for `|T| ≤ t`: downward double counting from the
`t`-subsets. -/
theorem rcwCnt_eq_of_card {V : Finset P} {u t l : ℕ} (hA : ∀ b, A b ⊆ V)
    (hu : ∀ b, (A b).card = u) (hreg : ∀ T ⊆ V, T.card = t → rcwCnt A T = l) (htu : t ≤ u)
    (huV : u ≤ V.card) :
    ∀ d, ∀ T T' : Finset P, T ⊆ V → T' ⊆ V → T.card + d = t → T'.card + d = t →
      rcwCnt A T = rcwCnt A T' := by
  intro d
  induction d with
  | zero =>
    intro T T' hT hT' h h'
    rw [hreg T hT (by omega), hreg T' hT' (by omega)]
  | succ d ih =>
    intro T T' hT hT' h h'
    have hne : (V \ T).Nonempty := by
      rw [nonempty_iff_ne_empty, ne_eq, sdiff_eq_empty_iff_subset]
      intro hV
      have := card_le_card hV
      omega
    obtain ⟨x₀, hx₀⟩ := hne
    have key : ∀ T'' : Finset P, T'' ⊆ V → T''.card + (d + 1) = t →
        (u - T''.card) * rcwCnt A T'' = (V.card - T''.card) * rcwCnt A (insert x₀ T) := by
      intro T'' h1 h2
      rw [sub_mul_rcwCnt A hA hu, ← card_sdiff_of_subset h1, ← smul_eq_mul, ← sum_const]
      refine sum_congr rfl fun x hx => ?_
      have hx' := mem_sdiff.1 hx
      have hx₀' := mem_sdiff.1 hx₀
      refine ih _ _ (insert_subset hx'.1 h1) (insert_subset hx₀'.1 hT) ?_ ?_
      · rw [card_insert_of_notMem hx'.2]
        omega
      · rw [card_insert_of_notMem hx₀'.2]
        omega
    have e1 := key T hT h
    have e2 := key T' hT' h'
    have hc : T.card = T'.card := by omega
    rw [hc] at e1
    exact Nat.eq_of_mul_eq_mul_left (by omega) (e1.trans e2.symm)

/-- Splitting by whether a point `x` is in the block. -/
theorem rcwLam_split (I J : Finset P) {x : P} :
    rcwLam A I J = rcwLam A I (insert x J) + rcwLam A (insert x I) J := by
  unfold rcwLam
  rw [← card_filter_add_card_filter_not (s := univ.filter fun b => I ⊆ A b ∧ Disjoint (A b) J)
    (fun b => x ∈ A b), filter_filter, filter_filter, add_comm]
  congr 2
  · ext b
    simp only [mem_filter, mem_univ, true_and, disjoint_insert_right]
    tauto
  · ext b
    simp only [mem_filter, mem_univ, true_and, insert_subset_iff]
    tauto

/-- **`lam I J` depends only on `|I|` and `|J|`** for `|I| + |J| ≤ t`. -/
theorem rcwLam_eq_of_card {V : Finset P} {u t l : ℕ} (hA : ∀ b, A b ⊆ V)
    (hu : ∀ b, (A b).card = u) (hreg : ∀ T ⊆ V, T.card = t → rcwCnt A T = l) (htu : t ≤ u)
    (huV : u ≤ V.card) :
    ∀ m, ∀ I J I' J' : Finset P, I ⊆ V → J ⊆ V → I' ⊆ V → J' ⊆ V → Disjoint I J →
      Disjoint I' J' → J.card = m → J'.card = m → I.card = I'.card → I.card + m ≤ t →
      rcwLam A I J = rcwLam A I' J' := by
  intro m
  induction m with
  | zero =>
    intro I J I' J' hI _ hI' _ _ _ hJ hJ' hII' ht
    rw [card_eq_zero] at hJ hJ'
    subst hJ hJ'
    have e : ∀ K : Finset P, rcwLam A K ∅ = rcwCnt A K := fun K => by
      unfold rcwLam rcwCnt
      simp only [disjoint_empty_right, and_true]
    rw [e, e]
    exact rcwCnt_eq_of_card A hA hu hreg htu huV (t - I.card) I I' hI hI' (by omega)
      (by omega)
  | succ m ih =>
    intro I J I' J' hI hJ hI' hJ' hIJ hIJ' hJc hJc' hII' ht
    obtain ⟨x, hx⟩ := card_pos.1 (show 0 < J.card by omega)
    obtain ⟨x', hx'⟩ := card_pos.1 (show 0 < J'.card by omega)
    have hJe : J = insert x (J.erase x) := (insert_erase hx).symm
    have hJe' : J' = insert x' (J'.erase x') := (insert_erase hx').symm
    have s1 := rcwLam_split A I (J.erase x) (x := x)
    have s2 := rcwLam_split A I' (J'.erase x') (x := x')
    rw [← hJe] at s1
    rw [← hJe'] at s2
    have hxI : x ∉ I := fun h => disjoint_left.1 hIJ h hx
    have hxI' : x' ∉ I' := fun h => disjoint_left.1 hIJ' h hx'
    have c1 : rcwLam A I (J.erase x) = rcwLam A I' (J'.erase x') := by
      refine ih I _ I' _ hI ((erase_subset _ _).trans hJ) hI' ((erase_subset _ _).trans hJ')
        (disjoint_of_subset_right (erase_subset _ _) hIJ)
        (disjoint_of_subset_right (erase_subset _ _) hIJ') ?_ ?_ hII' (by omega)
      · rw [card_erase_of_mem hx]
        omega
      · rw [card_erase_of_mem hx']
        omega
    have c2 : rcwLam A (insert x I) (J.erase x) = rcwLam A (insert x' I') (J'.erase x') := by
      refine ih _ _ _ _ (insert_subset (hJ hx) hI) ((erase_subset _ _).trans hJ)
        (insert_subset (hJ' hx') hI') ((erase_subset _ _).trans hJ') ?_ ?_ ?_ ?_ ?_ ?_
      · rw [disjoint_insert_left]
        exact ⟨notMem_erase x J, disjoint_of_subset_right (erase_subset _ _) hIJ⟩
      · rw [disjoint_insert_left]
        exact ⟨notMem_erase x' J', disjoint_of_subset_right (erase_subset _ _) hIJ'⟩
      · rw [card_erase_of_mem hx]
        omega
      · rw [card_erase_of_mem hx']
        omega
      · rw [card_insert_of_notMem hxI, card_insert_of_notMem hxI', hII']
      · rw [card_insert_of_notMem hxI]
        omega
    omega

end RCW

section Squares

variable {X Q : Type*}

/-- Expanding a sum of squares of partial sums. -/
theorem sum_sq_partial (𝒳 : Finset X) (𝒮 : Finset Q) (p : X → Q → Prop)
    [∀ a S, Decidable (p a S)] (y : Q → ℚ) :
    ∑ a ∈ 𝒳, (∑ S ∈ 𝒮, if p a S then y S else 0) ^ 2 =
      ∑ S ∈ 𝒮, ∑ S' ∈ 𝒮, y S * y S' * ((𝒳.filter fun a => p a S ∧ p a S').card : ℚ) := by
  have h1 : ∀ a, (∑ S ∈ 𝒮, if p a S then y S else 0) ^ 2 =
      ∑ S ∈ 𝒮, ∑ S' ∈ 𝒮, if p a S ∧ p a S' then y S * y S' else 0 := by
    intro a
    rw [sq, sum_mul_sum]
    refine sum_congr rfl fun S _ => sum_congr rfl fun S' _ => ?_
    by_cases h : p a S <;> by_cases h' : p a S' <;> simp [h, h']
  simp_rw [h1]
  rw [sum_comm]
  refine sum_congr rfl fun S _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun S' _ => ?_
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]

end Squares

/-- **The Ray-Chaudhuri–Wilson inequality** (Helfgott, Prop. 2.20). -/
theorem ray_chaudhuri_wilson {P B : Type*} [DecidableEq P] [Fintype B] (V : Finset P)
    (A : B → Finset P) {s t u l : ℕ} (hA : ∀ b, A b ⊆ V) (hu : ∀ b, (A b).card = u)
    (hreg : ∀ T ⊆ V, T.card = t → (univ.filter fun b => T ⊆ A b).card = l)
    (hl : 1 ≤ l) (hst : 2 * s ≤ t) (htu : t ≤ u) (hsu : s + u ≤ V.card) :
    V.card.choose s ≤ Fintype.card B := by
  have hreg' : ∀ T ⊆ V, T.card = t → rcwCnt A T = l := hreg
  have huV : u ≤ V.card := by omega
  -- the constants `c i`
  have hc : ∀ i, ∃ c : ℕ, ∀ I J : Finset P, I ⊆ V → J ⊆ V → Disjoint I J → J.card = i →
      I.card + i = 2 * s → rcwLam A I J = c := by
    intro i
    by_cases hi : i ≤ 2 * s
    · obtain ⟨W, hWV, hWc⟩ := exists_subset_card_eq (show 2 * s ≤ V.card by omega)
      obtain ⟨J₀, hJ₀W, hJ₀c⟩ := exists_subset_card_eq (show i ≤ W.card by omega)
      refine ⟨rcwLam A (W \ J₀) J₀, fun I J hI hJ hIJ hJc hIc => ?_⟩
      refine rcwLam_eq_of_card A hA hu hreg' htu huV i I J (W \ J₀) J₀ hI hJ
        (sdiff_subset.trans hWV) (hJ₀W.trans hWV) hIJ sdiff_disjoint hJc hJ₀c ?_ (by omega)
      rw [card_sdiff_of_subset hJ₀W]
      omega
    · exact ⟨0, fun I J _ _ _ hJc hIc => absurd hIc (by omega)⟩
  choose c hc using hc
  -- `c s ≥ 1`
  have hcs : 1 ≤ c s := by
    obtain ⟨I, hIV, hIc⟩ := exists_subset_card_eq (show s ≤ V.card by omega)
    obtain ⟨T, hIT, hTV, hTc⟩ := exists_subsuperset_card_eq hIV (show I.card ≤ t by omega)
      (show t ≤ V.card by omega)
    have hT := hreg T hTV hTc
    obtain ⟨b, hb⟩ := card_pos.1 (show 0 < (univ.filter fun b => T ⊆ A b).card by omega)
    have hTb : T ⊆ A b := (mem_filter.1 hb).2
    obtain ⟨J, hJ, hJc⟩ := exists_subset_card_eq (show s ≤ (V \ A b).card by
      rw [card_sdiff_of_subset (hA b), hu]
      omega)
    have hJV : J ⊆ V := hJ.trans sdiff_subset
    have hdisj : Disjoint (A b) J :=
      disjoint_of_subset_right hJ disjoint_sdiff
    rw [← hc s I J hIV hJV (disjoint_of_subset_left (hIT.trans hTb) hdisj) hJc (by omega)]
    exact card_pos.2 ⟨b, mem_filter.2 ⟨mem_univ _, hIT.trans hTb, hdisj⟩⟩
  -- the number of blocks containing `S ∪ S'`
  set 𝒮 := V.powersetCard s with h𝒮
  have hpair : ∀ S ∈ 𝒮, ∀ S' ∈ 𝒮,
      rcwCnt A (S ∪ S') = ∑ i ∈ range (s + 1), c i * (S ∩ S').card.choose i := by
    intro S hS S' hS'
    obtain ⟨hSV, hSc⟩ := mem_powersetCard.1 hS
    obtain ⟨hS'V, hS'c⟩ := mem_powersetCard.1 hS'
    set X := S ∪ S' with hX
    set k := (S ∩ S').card with hk
    have hXk : X.card + k = 2 * s := by
      rw [hX, hk, card_union_add_card_inter, hSc, hS'c]
      ring
    have hks : k ≤ s := by
      rw [hk, ← hSc]
      exact card_le_card inter_subset_left
    have hXV : X ⊆ V := union_subset hSV hS'V
    obtain ⟨Y, hY, hYc⟩ := exists_subset_card_eq (show k ≤ (V \ X).card by
      rw [card_sdiff_of_subset hXV]
      omega)
    have hYV : Y ⊆ V := hY.trans sdiff_subset
    have hXY : Disjoint X Y := disjoint_of_subset_right hY disjoint_sdiff
    -- split the blocks containing `X` by their trace on `Y`
    have hsplit : rcwCnt A X = ∑ Z ∈ Y.powerset, rcwLam A (X ∪ Z) (Y \ Z) := by
      unfold rcwCnt
      rw [card_eq_sum_card_fiberwise (f := fun b => A b ∩ Y) (t := Y.powerset)
        fun b _ => mem_powerset.2 inter_subset_right]
      refine sum_congr rfl fun Z hZ => ?_
      have hZY := mem_powerset.1 hZ
      unfold rcwLam
      rw [filter_filter]
      congr 1
      ext b
      simp only [mem_filter, mem_univ, true_and, union_subset_iff]
      constructor
      · rintro ⟨hXb, rfl⟩
        refine ⟨⟨hXb, inter_subset_left⟩, disjoint_left.2 fun w hw hw' => ?_⟩
        exact (mem_sdiff.1 hw').2 (mem_inter.2 ⟨hw, (mem_sdiff.1 hw').1⟩)
      · rintro ⟨⟨hXb, hZb⟩, hd⟩
        refine ⟨hXb, ?_⟩
        ext w
        simp only [mem_inter]
        constructor
        · rintro ⟨hw, hwY⟩
          by_contra hwZ
          exact disjoint_left.1 hd hw (mem_sdiff.2 ⟨hwY, hwZ⟩)
        · intro hwZ
          exact ⟨hZb hwZ, hZY hwZ⟩
    have hterm : ∀ Z ∈ Y.powerset, rcwLam A (X ∪ Z) (Y \ Z) = c (k - Z.card) := by
      intro Z hZ
      have hZY := mem_powerset.1 hZ
      have hXZ : Disjoint X Z := disjoint_of_subset_right hZY hXY
      refine hc _ _ _ (union_subset hXV (hZY.trans hYV)) (sdiff_subset.trans hYV)
        (disjoint_union_left.2 ⟨disjoint_of_subset_right sdiff_subset hXY, disjoint_sdiff⟩)
        (by rw [card_sdiff_of_subset hZY, hYc]) ?_
      rw [card_union_of_disjoint hXZ]
      have := card_le_card hZY
      omega
    rw [hsplit, sum_congr rfl hterm]
    rw [sum_powerset_apply_card (fun m => c (k - m)), hYc]
    simp only [smul_eq_mul]
    have hrefl := sum_range_reflect (fun j => k.choose j * c j) (k + 1)
    simp only [Nat.add_sub_cancel] at hrefl
    rw [← sum_congr rfl (fun j hj => by
      rw [Nat.choose_symm (Nat.lt_succ_iff.1 (mem_range.1 hj))] :
        ∀ j ∈ range (k + 1), k.choose (k - j) * c (k - j) = k.choose j * c (k - j))]
    rw [hrefl]
    rw [← sum_subset (range_subset_range.2 (show k + 1 ≤ s + 1 by omega)) fun i _ hi => by
      rw [Nat.choose_eq_zero_of_lt (by simpa using hi), mul_zero]]
    exact sum_congr rfl fun i _ => mul_comm _ _
  -- the key: a function on the `s`-subsets killed by every block vanishes
  have hkey : ∀ y : Finset P → ℚ, (∀ b, ∑ S ∈ 𝒮, (if S ⊆ A b then y S else 0) = 0) →
      ∀ S ∈ 𝒮, y S = 0 := by
    intro y hy
    let Qi : ℕ → ℚ := fun i =>
      ∑ I ∈ V.powersetCard i, (∑ S ∈ 𝒮, if I ⊆ S then y S else 0) ^ 2
    have hQ : ∀ i, Qi i = ∑ S ∈ 𝒮, ∑ S' ∈ 𝒮, y S * y S' * ((S ∩ S').card.choose i : ℚ) := by
      intro i
      simp only [Qi]
      rw [sum_sq_partial]
      refine sum_congr rfl fun S hS => sum_congr rfl fun S' _ => ?_
      congr 2
      have hSV := (mem_powersetCard.1 hS).1
      have e : (V.powersetCard i).filter (fun I => I ⊆ S ∧ I ⊆ S') =
          (S ∩ S').powersetCard i := by
        ext I
        simp only [mem_filter, mem_powersetCard, subset_inter_iff]
        constructor
        · rintro ⟨⟨_, hIc⟩, h1, h2⟩
          exact ⟨⟨h1, h2⟩, hIc⟩
        · rintro ⟨⟨h1, h2⟩, hIc⟩
          exact ⟨⟨h1.trans hSV, hIc⟩, h1, h2⟩
      rw [e, card_powersetCard]
    have h1 : ∑ b, (∑ S ∈ 𝒮, if S ⊆ A b then y S else 0) ^ 2 =
        ∑ i ∈ range (s + 1), (c i : ℚ) * Qi i := by
      calc ∑ b, (∑ S ∈ 𝒮, if S ⊆ A b then y S else 0) ^ 2
          = ∑ S ∈ 𝒮, ∑ S' ∈ 𝒮, ∑ i ∈ range (s + 1),
              (c i : ℚ) * (y S * y S' * ((S ∩ S').card.choose i : ℚ)) := by
            rw [sum_sq_partial]
            refine sum_congr rfl fun S hS => sum_congr rfl fun S' hS' => ?_
            have e : (univ.filter fun b => S ⊆ A b ∧ S' ⊆ A b) =
                univ.filter fun b => S ∪ S' ⊆ A b := by
              simp only [union_subset_iff]
            rw [e]
            have h := congrArg (fun n : ℕ => (n : ℚ)) (hpair S hS S' hS')
            simp only [rcwCnt, Nat.cast_sum, Nat.cast_mul] at h
            rw [h, mul_sum]
            refine sum_congr rfl fun i _ => ?_
            ring
        _ = ∑ S ∈ 𝒮, ∑ i ∈ range (s + 1), ∑ S' ∈ 𝒮,
              (c i : ℚ) * (y S * y S' * ((S ∩ S').card.choose i : ℚ)) :=
            sum_congr rfl fun S _ => sum_comm
        _ = ∑ i ∈ range (s + 1), ∑ S ∈ 𝒮, ∑ S' ∈ 𝒮,
              (c i : ℚ) * (y S * y S' * ((S ∩ S').card.choose i : ℚ)) := sum_comm
        _ = ∑ i ∈ range (s + 1), (c i : ℚ) * Qi i := by
            refine sum_congr rfl fun i _ => ?_
            rw [hQ, mul_sum]
            exact sum_congr rfl fun S _ => (mul_sum _ _ _).symm
    have h0 : ∑ i ∈ range (s + 1), (c i : ℚ) * Qi i = 0 := by
      rw [← h1]
      simp [hy]
    have hnn : ∀ i ∈ range (s + 1), 0 ≤ (c i : ℚ) * Qi i := fun i _ =>
      mul_nonneg (Nat.cast_nonneg _) (sum_nonneg fun I _ => sq_nonneg _)
    have hQs : (c s : ℚ) * Qi s = 0 :=
      (sum_eq_zero_iff_of_nonneg hnn).1 h0 s (mem_range.2 (Nat.lt_succ_self s))
    have hcs' : (c s : ℚ) ≠ 0 := by
      have : (1 : ℚ) ≤ c s := by exact_mod_cast hcs
      linarith
    have hQs' : Qi s = 0 := (mul_eq_zero.1 hQs).resolve_left hcs'
    have hdiag : ∀ I ∈ 𝒮, (∑ S ∈ 𝒮, if I ⊆ S then y S else 0) = y I := by
      intro I hI
      rw [sum_eq_single I]
      · simp
      · intro S hS hSI
        have : ¬ I ⊆ S := fun hIS => hSI (eq_of_subset_of_card_le hIS (by
          rw [(mem_powersetCard.1 hS).2, (mem_powersetCard.1 hI).2])).symm
        simp only [this, ↓reduceIte]
      · intro hI'
        exact absurd hI hI'
    have hsq : ∑ I ∈ 𝒮, y I ^ 2 = 0 := by
      rw [← hQs']
      simp only [Qi]
      rw [← h𝒮]
      exact sum_congr rfl fun I hI => by rw [hdiag I hI]
    intro S hS
    have := (sum_eq_zero_iff_of_nonneg fun I _ => sq_nonneg (y I)).1 hsq S hS
    exact (pow_eq_zero_iff two_ne_zero).1 this
  -- the linear map on functions on the `s`-subsets is injective
  let f : (𝒮 → ℚ) →ₗ[ℚ] (B → ℚ) :=
    { toFun := fun x b => ∑ S : 𝒮, if (S : Finset P) ⊆ A b then x S else 0
      map_add' := fun x y => by
        funext b
        simp only [Pi.add_apply, ← sum_add_distrib]
        refine sum_congr rfl fun S _ => ?_
        split_ifs <;> simp
      map_smul' := fun a x => by
        funext b
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sum]
        refine sum_congr rfl fun S _ => ?_
        split_ifs <;> simp }
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    let y : Finset P → ℚ := fun S => if h : S ∈ 𝒮 then x ⟨S, h⟩ else 0
    have hy : ∀ b, ∑ S ∈ 𝒮, (if S ⊆ A b then y S else 0) = 0 := by
      intro b
      have hb := congrFun hx b
      rw [← sum_coe_sort 𝒮]
      refine Eq.trans (sum_congr rfl fun S _ => ?_) hb
      simp [y, S.2]
    funext S
    have := hkey y hy S S.2
    simpa [y, S.2] using this
  have := LinearMap.finrank_le_finrank_of_injective hinj
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe, h𝒮,
    card_powersetCard] at this
  exact this

end GraphIso.Coherent
