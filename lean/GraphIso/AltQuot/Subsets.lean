module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Nat.Choose.Vandermonde
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# The effect of a colouring on `t`-subsets

Babai §5.2. A colouring of `Γ` (`|Γ| = m`) colours each `t`-subset `T` by its intersection
numbers `|T ∩ Δ_i|` with the colour classes `Δ_i`.
* `choose_mul_choose_le` (Babai, Prop. 5.2.3): if `t₁, t₂ ≥ 1` and `2 (t₁ + t₂) ≤ m₁ + m₂`, then
  `3 C(m₁, t₁) C(m₂, t₂) ≤ 2 C(m₁ + m₂, t₁ + t₂)`.
* `card_sameCounts_le` (Lemma 5.2.1 (a)): if `2t ≤ m` and `T` meets two colour classes, the
  `t`-subsets with the intersection numbers of `T` are at most `(2/3) C(m, t)`.
* `choose_mul_pow_le` (Lemma 5.2.1 (b)): `C(d, t) m^t ≤ d^t C(m, t)` for `d ≤ m`: a class
  of `d` points has at most `(d/m)^t C(m, t)` of the `t`-subsets.
* `card_sameCounts_le_of_le` (Cor. 5.2.2): if every colour class has at most `a` points and
  `1 ≤ t`, `2t ≤ m`, every class of `t`-subsets has `3·size ≤ 2 C(m, t)` or `m·size ≤ a C(m, t)`.

Prop. 5.2.3 follows Babai: with `a_s = C(m₁, s) C(m₂, t − s)`, Vandermonde gives
`Σ_s a_s = C(m, t)`; in the interior `a_s ≤ 2 (a_{s−1} + a_{s+1})` by
`C(n, k)² ≤ 4 C(n, k − 1) C(n, k + 1)` (`choose_mul_choose_le_four`, Claim 5.2.4), and on the
boundary (`t₁ = m₁` or `t₂ = m₂`) a single neighbour is at least `a_s` (`choose_le_choose_succ`).
Lemma 5.2.1 (a) injects a class into pairs of subsets inside and outside one colour class;
Cor. 5.2.2 uses `m C(d, t) ≤ d C(m, t)` (`mul_choose_le_mul_choose`) for monochromatic classes.
-/

@[expose] public section

namespace GraphIso.AltQuot

open Finset

/-- `C(n, k)² ≤ 4 C(n, k − 1) C(n, k + 1)` for `1 ≤ k < n` (Babai, Claim 5.2.4). -/
theorem choose_mul_choose_le_four {n k : ℕ} (hk : 1 ≤ k) (hkn : k + 1 ≤ n) :
    n.choose k * n.choose k ≤ 4 * (n.choose (k - 1) * n.choose (k + 1)) := by
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, n = k + 2 + j := ⟨n - (k + 2), by omega⟩
  rw [Nat.add_sub_cancel]
  have h1 := Nat.choose_succ_right_eq (k + 2 + j) (k + 1)
  have h2 := Nat.choose_succ_right_eq (k + 2 + j) k
  rw [show k + 2 + j - (k + 1) = j + 1 by omega] at h1
  rw [show k + 2 + j - k = j + 2 by omega] at h2
  set A := (k + 2 + j).choose (k + 1)
  set B := (k + 2 + j).choose k
  set D := (k + 2 + j).choose (k + 1 + 1)
  have key : A * A * ((k + 1) * (j + 1)) = B * D * ((j + 2) * (k + 1 + 1)) := by
    calc A * A * ((k + 1) * (j + 1)) = (A * (k + 1)) * (A * (j + 1)) := by ring
      _ = (B * (j + 2)) * (D * (k + 1 + 1)) := by rw [h2, ← h1]
      _ = B * D * ((j + 2) * (k + 1 + 1)) := by ring
  have hpos : 0 < (j + 2) * (k + 1 + 1) := by positivity
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc A * A * ((j + 2) * (k + 1 + 1)) ≤ A * A * (4 * ((k + 1) * (j + 1))) :=
        Nat.mul_le_mul_left _ (by nlinarith)
    _ = 4 * (A * A * ((k + 1) * (j + 1))) := by ring
    _ = 4 * (B * D) * ((j + 2) * (k + 1 + 1)) := by rw [key]; ring

/-- `C(n, k) ≤ C(n, k + 1)` when `2k + 1 ≤ n`. -/
theorem choose_le_choose_succ {n k : ℕ} (h : 2 * k + 1 ≤ n) : n.choose k ≤ n.choose (k + 1) := by
  have e := Nat.choose_succ_right_eq n k
  refine Nat.le_of_mul_le_mul_right ?_ (Nat.succ_pos k)
  rw [e]
  exact Nat.mul_le_mul_left _ (by omega)

/-- **The binomial inequality** (Babai, Prop. 5.2.3). -/
theorem choose_mul_choose_le {m₁ m₂ t₁ t₂ : ℕ} (h : 2 * (t₁ + t₂) ≤ m₁ + m₂) (h₁ : 1 ≤ t₁)
    (h₂ : 1 ≤ t₂) :
    3 * (m₁.choose t₁ * m₂.choose t₂) ≤ 2 * (m₁ + m₂).choose (t₁ + t₂) := by
  set F : ℕ × ℕ → ℕ := fun p => m₁.choose p.1 * m₂.choose p.2 with hF
  have hV : (m₁ + m₂).choose (t₁ + t₂) = ∑ p ∈ antidiagonal (t₁ + t₂), F p :=
    Nat.add_choose_eq _ _ _
  have two : ∀ p ∈ antidiagonal (t₁ + t₂), ∀ q ∈ antidiagonal (t₁ + t₂), p ≠ q →
      F p + F q ≤ (m₁ + m₂).choose (t₁ + t₂) := by
    intro p hp q hq hpq
    rw [hV, ← sum_pair hpq]
    refine sum_le_sum_of_subset fun x hx => ?_
    rcases mem_insert.1 hx with rfl | hx
    · exact hp
    · rw [mem_singleton.1 hx]
      exact hq
  have three : ∀ p ∈ antidiagonal (t₁ + t₂), ∀ q ∈ antidiagonal (t₁ + t₂),
      ∀ r ∈ antidiagonal (t₁ + t₂), p ≠ q → p ≠ r → q ≠ r →
      F p + F q + F r ≤ (m₁ + m₂).choose (t₁ + t₂) := by
    intro p hp q hq r hr hpq hpr hqr
    have e : F p + F q + F r = ∑ x ∈ {p, q, r}, F x := by
      rw [sum_insert (by simp [hpq, hpr]), sum_pair hqr]
      ring
    rw [hV, e]
    refine sum_le_sum_of_subset fun x hx => ?_
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have mem : ∀ a b, a + b = t₁ + t₂ → (a, b) ∈ antidiagonal (t₁ + t₂) := fun a b e =>
    mem_antidiagonal.2 e
  have hFst : F (t₁, t₂) = m₁.choose t₁ * m₂.choose t₂ := rfl
  rcases Nat.lt_or_ge m₁ t₁ with hs | hs
  · simp [Nat.choose_eq_zero_of_lt hs]
  rcases Nat.lt_or_ge m₂ t₂ with hu | hu
  · simp [Nat.choose_eq_zero_of_lt hu]
  rcases Nat.eq_or_lt_of_le hs with hs' | hs'
  · -- `t₁ = m₁`: compare with `(t₁ − 1, t₂ + 1)`
    subst hs'
    have hle : F (t₁, t₂) ≤ F (t₁ - 1, t₂ + 1) := by
      simp only [hF, Nat.choose_self, one_mul]
      calc m₂.choose t₂ ≤ m₂.choose (t₂ + 1) := choose_le_choose_succ (by omega)
        _ ≤ t₁.choose (t₁ - 1) * m₂.choose (t₂ + 1) :=
          Nat.le_mul_of_pos_left _ (Nat.choose_pos (by omega))
    have := two _ (mem _ _ rfl) _ (mem (t₁ - 1) (t₂ + 1) (by omega))
      (by simp only [ne_eq, Prod.mk.injEq]; omega)
    rw [← hFst]
    omega
  rcases Nat.eq_or_lt_of_le hu with hu' | hu'
  · -- `t₂ = m₂`: compare with `(t₁ + 1, t₂ − 1)`
    subst hu'
    have hle : F (t₁, t₂) ≤ F (t₁ + 1, t₂ - 1) := by
      simp only [hF, Nat.choose_self, mul_one]
      calc m₁.choose t₁ ≤ m₁.choose (t₁ + 1) := choose_le_choose_succ (by omega)
        _ ≤ m₁.choose (t₁ + 1) * t₂.choose (t₂ - 1) :=
          Nat.le_mul_of_pos_right _ (Nat.choose_pos (by omega))
    have := two _ (mem _ _ rfl) _ (mem (t₁ + 1) (t₂ - 1) (by omega))
      (by simp only [ne_eq, Prod.mk.injEq]; omega)
    rw [← hFst]
    omega
  · -- interior: `F (t₁, t₂) ≤ 2 (F (t₁ − 1, t₂ + 1) + F (t₁ + 1, t₂ − 1))`
    have c₁ := choose_mul_choose_le_four (n := m₁) h₁ (by omega)
    have c₂ := choose_mul_choose_le_four (n := m₂) h₂ (by omega)
    set a := F (t₁, t₂)
    set x := F (t₁ - 1, t₂ + 1)
    set y := F (t₁ + 1, t₂ - 1)
    have hsq : a * a ≤ 16 * (x * y) := by
      have := Nat.mul_le_mul c₁ c₂
      calc a * a = (m₁.choose t₁ * m₁.choose t₁) * (m₂.choose t₂ * m₂.choose t₂) := by
            simp only [a, hF]; ring
        _ ≤ 4 * (m₁.choose (t₁ - 1) * m₁.choose (t₁ + 1)) *
            (4 * (m₂.choose (t₂ - 1) * m₂.choose (t₂ + 1))) := this
        _ = 16 * (x * y) := by simp only [x, y, hF]; ring
    have hax : a ≤ 2 * (x + y) := by
      by_contra hc
      have hc' := Nat.lt_of_not_le hc
      have := Nat.mul_le_mul hc' hc'
      nlinarith [sq_nonneg ((x : ℤ) - y)]
    have := three _ (mem _ _ rfl) _ (mem (t₁ - 1) (t₂ + 1) (by omega)) _
      (mem (t₁ + 1) (t₂ - 1) (by omega)) (by simp only [ne_eq, Prod.mk.injEq]; omega)
      (by simp only [ne_eq, Prod.mk.injEq]; omega) (by simp only [ne_eq, Prod.mk.injEq]; omega)
    rw [← hFst]
    omega

variable {α : Type*} [DecidableEq α]

/-- `T'` has the intersection numbers of `T` with the colour classes of `col` on `Γ`. -/
def SameCounts (Γ : Finset α) (col : α → ℕ) (T T' : Finset α) : Prop :=
  ∀ i ∈ Γ.image col, (T'.filter fun x => col x = i).card = (T.filter fun x => col x = i).card

instance (Γ : Finset α) (col : α → ℕ) (T T' : Finset α) : Decidable (SameCounts Γ col T T') := by
  unfold SameCounts
  infer_instance

/-- **Mixed subsets** (Babai, Lemma 5.2.1 (a)). -/
theorem card_sameCounts_le (Γ : Finset α) (col : α → ℕ) {t : ℕ} (ht : 2 * t ≤ Γ.card)
    {T : Finset α} (hT : T ∈ Γ.powersetCard t) (hmix : ∃ x ∈ T, ∃ y ∈ T, col x ≠ col y) :
    3 * ((Γ.powersetCard t).filter (SameCounts Γ col T)).card ≤ 2 * Γ.card.choose t := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hmix
  obtain ⟨hTΓ, hTc⟩ := mem_powersetCard.1 hT
  set S := (Γ.powersetCard t).filter (SameCounts Γ col T)
  set c := col x
  set t₁ := (T.filter fun z => col z = c).card with ht₁def
  have ht₁ : 1 ≤ t₁ := card_pos.2 ⟨x, mem_filter.2 ⟨hx, rfl⟩⟩
  have ht₁t : t₁ < t := by
    rw [← hTc]
    exact card_lt_card (filter_ssubset.2 ⟨y, hy, fun h => hxy h.symm⟩)
  set Δ := Γ.filter fun z => col z = c
  set Δ' := Γ.filter fun z => ¬ col z = c
  have hm : Δ.card + Δ'.card = Γ.card := card_filter_add_card_filter_not (s := Γ) _
  have hc : c ∈ Γ.image col := mem_image_of_mem _ (hTΓ hx)
  have hinj : S.card ≤ (Δ.powersetCard t₁ ×ˢ Δ'.powersetCard (t - t₁)).card := by
    refine card_le_card_of_injOn
      (fun T' => (T'.filter fun z => col z = c, T'.filter fun z => ¬ col z = c)) ?_ ?_
    · intro T' hT'
      obtain ⟨hT'1, hT'2⟩ := mem_filter.1 (mem_coe.1 hT')
      obtain ⟨hT'Γ, hT'c⟩ := mem_powersetCard.1 hT'1
      have hsame : (T'.filter fun z => col z = c).card = t₁ := hT'2 c hc
      have hsplit := card_filter_add_card_filter_not (s := T') (fun z => col z = c)
      simp only [coe_product, Set.mem_prod, mem_coe, mem_powersetCard]
      exact ⟨⟨filter_subset_filter _ hT'Γ, hsame⟩, ⟨filter_subset_filter _ hT'Γ, by omega⟩⟩
    · intro T₁ _ T₂ _ he
      simp only [Prod.mk.injEq] at he
      rw [← filter_union_filter_not_eq (p := fun z => col z = c) T₁,
        ← filter_union_filter_not_eq (p := fun z => col z = c) T₂, he.1, he.2]
  rw [card_product, card_powersetCard, card_powersetCard] at hinj
  have hb := choose_mul_choose_le (m₁ := Δ.card) (m₂ := Δ'.card) (t₁ := t₁) (t₂ := t - t₁)
    (by omega) ht₁ (by omega)
  rw [hm, show t₁ + (t - t₁) = t by omega] at hb
  exact (Nat.mul_le_mul_left 3 hinj).trans hb

/-- **Monochromatic subsets** (Babai, Lemma 5.2.1 (b)). -/
theorem choose_mul_pow_le {d m : ℕ} (hdm : d ≤ m) (t : ℕ) :
    d.choose t * m ^ t ≤ d ^ t * m.choose t := by
  induction t with
  | zero => simp
  | succ t ih =>
    have e₁ := Nat.choose_succ_right_eq d t
    have e₂ := Nat.choose_succ_right_eq m t
    have hdt : (d - t) * m ≤ d * (m - t) := by
      rcases Nat.lt_or_ge d t with h | h
      · rw [Nat.sub_eq_zero_of_le h.le, zero_mul]
        exact Nat.zero_le _
      · obtain ⟨a, rfl⟩ : ∃ a, d = t + a := ⟨d - t, by omega⟩
        obtain ⟨b, rfl⟩ : ∃ b, m = t + a + b := ⟨m - (t + a), by omega⟩
        rw [show t + a - t = a by omega, show t + a + b - t = a + b by omega]
        nlinarith
    refine Nat.le_of_mul_le_mul_right ?_ (Nat.succ_pos t)
    calc d.choose (t + 1) * m ^ (t + 1) * (t + 1)
        = d.choose (t + 1) * (t + 1) * m ^ t * m := by ring
      _ = d.choose t * m ^ t * ((d - t) * m) := by rw [e₁]; ring
      _ ≤ d ^ t * m.choose t * (d * (m - t)) := Nat.mul_le_mul ih hdt
      _ = d ^ (t + 1) * (m.choose t * (m - t)) := by ring
      _ = d ^ (t + 1) * m.choose (t + 1) * (t + 1) := by rw [← e₂]; ring

/-- `m C(d, t) ≤ d C(m, t)` for `d ≤ m` and `t ≥ 1`. -/
theorem mul_choose_le_mul_choose {d m t : ℕ} (hdm : d ≤ m) (ht : 1 ≤ t) (hm : 0 < m) :
    m * d.choose t ≤ d * m.choose t := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  have h := choose_mul_pow_le hdm (s + 1)
  refine Nat.le_of_mul_le_mul_right ?_ (pow_pos hm s)
  calc m * d.choose (s + 1) * m ^ s = d.choose (s + 1) * m ^ (s + 1) := by ring
    _ ≤ d ^ (s + 1) * m.choose (s + 1) := h
    _ = d * m.choose (s + 1) * d ^ s := by ring
    _ ≤ d * m.choose (s + 1) * m ^ s := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hdm s)

/-- **Colourings without large classes** (Babai, Cor. 5.2.2). -/
theorem card_sameCounts_le_of_le (Γ : Finset α) (col : α → ℕ) {a t : ℕ}
    (ha : ∀ x ∈ Γ, (Γ.filter fun y => col y = col x).card ≤ a) (h1 : 1 ≤ t)
    (ht : 2 * t ≤ Γ.card) {T : Finset α} (hT : T ∈ Γ.powersetCard t) :
    3 * ((Γ.powersetCard t).filter (SameCounts Γ col T)).card ≤ 2 * Γ.card.choose t ∨
      Γ.card * ((Γ.powersetCard t).filter (SameCounts Γ col T)).card ≤ a * Γ.card.choose t := by
  by_cases hmix : ∃ x ∈ T, ∃ y ∈ T, col x ≠ col y
  · exact Or.inl (card_sameCounts_le Γ col ht hT hmix)
  right
  have hmono : ∀ x ∈ T, ∀ y ∈ T, col x = col y := fun x hx y hy => by
    by_contra hne
    exact hmix ⟨x, hx, y, hy, hne⟩
  obtain ⟨hTΓ, hTc⟩ := mem_powersetCard.1 hT
  obtain ⟨x, hx⟩ : T.Nonempty := card_pos.1 (by omega)
  set S := (Γ.powersetCard t).filter (SameCounts Γ col T)
  set c := col x
  set Δ := Γ.filter fun z => col z = c
  have hd : Δ.card ≤ a := ha x (hTΓ hx)
  have hdm : Δ.card ≤ Γ.card := card_filter_le _ _
  have hc : c ∈ Γ.image col := mem_image_of_mem _ (hTΓ hx)
  have hTt : (T.filter fun z => col z = c).card = t := by
    rw [filter_true_of_mem fun z hz => hmono z hz x hx, hTc]
  have hsub : S ⊆ Δ.powersetCard t := by
    intro T' hT'
    obtain ⟨hT'1, hT'2⟩ := mem_filter.1 hT'
    obtain ⟨hT'Γ, hT'c⟩ := mem_powersetCard.1 hT'1
    have hsame : (T'.filter fun z => col z = c).card = T'.card := by
      rw [hT'2 c hc, hTt, hT'c]
    have hall := card_filter_eq_iff.1 hsame
    exact mem_powersetCard.2 ⟨fun z hz => mem_filter.2 ⟨hT'Γ hz, hall z hz⟩, hT'c⟩
  have hS : S.card ≤ Δ.card.choose t := by
    simpa only [card_powersetCard] using card_le_card hsub
  calc Γ.card * S.card ≤ Γ.card * Δ.card.choose t := Nat.mul_le_mul_left _ hS
    _ ≤ Δ.card * Γ.card.choose t := mul_choose_le_mul_choose hdm h1 (by omega)
    _ ≤ a * Γ.card.choose t := Nat.mul_le_mul_right _ hd

end GraphIso.AltQuot
