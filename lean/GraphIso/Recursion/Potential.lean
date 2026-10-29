module

public import Mathlib.Data.Nat.Log
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Algebra.BigOperators.Ring.List
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# The potential

The cost analysis of the recursion (`PLAN-14.md` §2.4, §5 items 7–8). An instance on a window
of `n` points carrying a hint with base of `m` points is charged
`pot Q b n m = n² (m + 1) Q^{b (κ(m) + 4 (λ(n) + 6)²)}`, with `κ(m) = ⌊log₂ m⁵⌋` and
`λ(n) = ⌊log₂ n⌋`. An instance without a hint is charged `pot0 Q b n = pot Q b n (2n + 1)`. Here
`Q` bounds both the work of one macro-step and its branching factor.

* `pot_step`: a macro-step with branching factor `c ≤ Q²` is paid for. Its children (counted
  with multiplicity, `Σ nᵢ ≤ c n`) keep the hint with `4 mᵢ ≤ 3 m`, or drop it on windows of at
  most `n/2` points.
* `pot_free`: a step without branching is paid for (`Σ nᵢ ≤ n`). Its children keep the hint
  with a smaller base or a smaller window, or drop it on windows of at most `n/2` points.
  Creating a hint (`m ≤ 2n`) is a special case.
* `pot0_le`: the bound in closed form, `Q^{O((log n)²)}`.
* **The label invariant.** `s_le_lam` and `johnson_step_label` show that a Johnson step from a
  base of `m` points into a base of `m' > ℓ` points with parameter `s` keeps
  `t (⌊log₂ m⌋ + 1)²` from growing, although labels grow by the factor `s`.
-/

@[expose] public section

namespace GraphIso.Recursion

/-- `κ(m) = ⌊log₂ m⁵⌋`. -/
def kap (m : ℕ) : ℕ := Nat.log 2 (m ^ 5)

/-- `λ(n) = ⌊log₂ n⌋`. -/
def lam (n : ℕ) : ℕ := Nat.log 2 n

/-- The potential of an instance with a hint. -/
def pot (Q b n m : ℕ) : ℕ := n ^ 2 * (m + 1) * Q ^ (b * (kap m + 4 * (lam n + 6) ^ 2))

/-- The potential of an instance: `none` means no hint. -/
def potO (Q b n : ℕ) : Option ℕ → ℕ
  | none => pot Q b n (2 * n + 1)
  | some m => pot Q b n m

/-! ### Logarithms -/

theorem lam_mono {a a' : ℕ} (h : a ≤ a') : lam a ≤ lam a' := Nat.log_mono_right h

theorem kap_mono {a a' : ℕ} (h : a ≤ a') : kap a ≤ kap a' :=
  Nat.log_mono_right (Nat.pow_le_pow_left h 5)

/-- `κ(x) ≤ 5 λ(x) + 4`. -/
theorem kap_le (x : ℕ) : kap x ≤ 5 * lam x + 4 := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp [kap, lam]
  have h1 : x < 2 ^ (lam x + 1) := Nat.lt_pow_succ_log_self (by norm_num) x
  have h2 : x ^ 5 < 2 ^ (5 * lam x + 5) := by
    calc x ^ 5 < (2 ^ (lam x + 1)) ^ 5 := Nat.pow_lt_pow_left h1 (by norm_num)
      _ = 2 ^ (5 * lam x + 5) := by rw [← pow_mul]; ring_nf
  have : kap x < 5 * lam x + 5 := Nat.log_lt_of_lt_pow (by positivity) h2
  omega

/-- `λ(2x + 1) ≤ λ(x) + 1`. -/
theorem lam_two_mul_add_one_le (x : ℕ) : lam (2 * x + 1) ≤ lam x + 1 := by
  have h1 : x < 2 ^ (lam x + 1) := Nat.lt_pow_succ_log_self (by norm_num) x
  have h2 : 2 * x + 1 < 2 ^ (lam x + 2) := by
    rw [pow_succ]; omega
  have : lam (2 * x + 1) < lam x + 2 := Nat.log_lt_of_lt_pow (by omega) h2
  omega

/-- If `2x ≤ n` and `1 ≤ x`, then `λ(x) + 1 ≤ λ(n)`. -/
theorem lam_add_one_le {x n : ℕ} (hx : 1 ≤ x) (h : 2 * x ≤ n) : lam x + 1 ≤ lam n := by
  have : lam (x * 2) = lam x + 1 := Nat.log_mul_base (by norm_num) (by omega)
  rw [← this]
  exact lam_mono (by omega)

/-- The exponent of a child without a hint on at most half of the window drops by `35`. -/
theorem exp_dropped {x n : ℕ} (hx : 1 ≤ x) (h : 2 * x ≤ n) :
    kap (2 * x + 1) + 4 * (lam x + 6) ^ 2 + 35 ≤ 4 * (lam n + 6) ^ 2 := by
  have hl := lam_add_one_le hx h
  have hk : kap (2 * x + 1) ≤ 5 * lam n + 9 := by
    have := kap_le (2 * x + 1)
    have := lam_two_mul_add_one_le x
    omega
  have hp : (lam x + 6) ^ 2 ≤ (lam n + 5) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hq : (lam n + 6) ^ 2 = (lam n + 5) ^ 2 + 2 * lam n + 11 := by ring
  omega

/-- **`κ` drops by two when the base shrinks to three quarters.** -/
theorem kap_add_two_le {m m' : ℕ} (hm : 2 ≤ m) (h : 4 * m' ≤ 3 * m) : kap m' + 2 ≤ kap m := by
  have h32 : 32 ≤ m ^ 5 := by
    calc 32 = 2 ^ 5 := by norm_num
      _ ≤ m ^ 5 := Nat.pow_le_pow_left hm 5
  rcases Nat.eq_zero_or_pos m' with rfl | hm'
  · have : 5 ≤ kap m := Nat.le_log_of_pow_le (by norm_num) (by simpa using h32)
    simp only [kap, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Nat.log_zero_right]
    exact le_trans (by norm_num) this
  have h4 : 4 * m' ^ 5 ≤ m ^ 5 := by
    have : (4 * m') ^ 5 ≤ (3 * m) ^ 5 := Nat.pow_le_pow_left h 5
    have e1 : (4 * m') ^ 5 = 1024 * m' ^ 5 := by ring
    have e2 : (3 * m) ^ 5 = 243 * m ^ 5 := by ring
    omega
  have hp : 2 ^ kap m' ≤ m' ^ 5 := Nat.pow_log_le_self 2 (by positivity)
  apply Nat.le_log_of_pow_le (by norm_num)
  calc 2 ^ (kap m' + 2) = 4 * 2 ^ kap m' := by ring
    _ ≤ 4 * m' ^ 5 := Nat.mul_le_mul_left 4 hp
    _ ≤ m ^ 5 := h4

theorem le_pot {Q b n m : ℕ} (hQ : 2 ≤ Q) (hb : 1 ≤ b) (hn : 1 ≤ n) : Q ≤ pot Q b n m := by
  unfold pot
  have he : 1 ≤ b * (kap m + 4 * (lam n + 6) ^ 2) := by
    have : 1 ≤ kap m + 4 * (lam n + 6) ^ 2 := by
      have : 1 ≤ (lam n + 6) ^ 2 := Nat.one_le_pow _ _ (by omega)
      omega
    exact le_trans this (Nat.le_mul_of_pos_left _ (by omega))
  have h1 : Q ≤ Q ^ (b * (kap m + 4 * (lam n + 6) ^ 2)) := by
    calc Q = Q ^ 1 := (pow_one Q).symm
      _ ≤ _ := Nat.pow_le_pow_right (by omega) he
  have h2 : 1 ≤ n ^ 2 * (m + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
  calc Q ≤ Q ^ (b * (kap m + 4 * (lam n + 6) ^ 2)) := h1
    _ ≤ n ^ 2 * (m + 1) * Q ^ (b * (kap m + 4 * (lam n + 6) ^ 2)) :=
      Nat.le_mul_of_pos_left _ h2

/-! ### Children -/

/-- A child without a hint, on at most half of the window, is tiny. -/
theorem pot_dropped_le {Q b n x : ℕ} (hx : 1 ≤ x) (hxn : 2 * x ≤ n) (hQ : n + 2 ≤ Q) :
    pot Q b x (2 * x + 1) * Q ^ (35 * b) ≤ x * Q ^ (2 + b * (4 * (lam n + 6) ^ 2)) := by
  unfold pot
  have hQ1 : 1 ≤ Q := by omega
  have he := exp_dropped hx hxn
  have hpow : Q ^ (b * (kap (2 * x + 1) + 4 * (lam x + 6) ^ 2)) * Q ^ (35 * b) ≤
      Q ^ (b * (4 * (lam n + 6) ^ 2)) := by
    rw [← pow_add]
    apply Nat.pow_le_pow_right hQ1
    calc b * (kap (2 * x + 1) + 4 * (lam x + 6) ^ 2) + 35 * b
        = b * (kap (2 * x + 1) + 4 * (lam x + 6) ^ 2 + 35) := by ring
      _ ≤ b * (4 * (lam n + 6) ^ 2) := Nat.mul_le_mul_left b he
  have hx2 : x ^ 2 * (2 * x + 1 + 1) ≤ x * (Q * Q) := by
    have h1 : x ≤ Q := by omega
    have h2 : 2 * x + 1 + 1 ≤ Q := by omega
    calc x ^ 2 * (2 * x + 1 + 1) = x * (x * (2 * x + 1 + 1)) := by ring
      _ ≤ x * (Q * Q) := Nat.mul_le_mul_left x (Nat.mul_le_mul h1 h2)
  calc x ^ 2 * (2 * x + 1 + 1) * Q ^ (b * (kap (2 * x + 1) + 4 * (lam x + 6) ^ 2)) *
        Q ^ (35 * b)
      = x ^ 2 * (2 * x + 1 + 1) * (Q ^ (b * (kap (2 * x + 1) + 4 * (lam x + 6) ^ 2)) *
        Q ^ (35 * b)) := by ring
    _ ≤ x * (Q * Q) * Q ^ (b * (4 * (lam n + 6) ^ 2)) := Nat.mul_le_mul hx2 hpow
    _ = x * Q ^ (2 + b * (4 * (lam n + 6) ^ 2)) := by ring

/-- A child without a hint, in the form used by both inequalities: `Q⁶ · pot ≤ x Q² Q^{bE}`. -/
theorem pot_dropped_le' {Q b n m x : ℕ} (hb : 1 ≤ b) (hxn : 2 * x ≤ n) (hQ : n + 2 ≤ Q) :
    Q ^ 6 * pot Q b x (2 * x + 1) ≤
      x * (Q ^ 2 * Q ^ (b * (kap m + 4 * (lam n + 6) ^ 2))) := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp [pot]
  have hQ1 : 1 ≤ Q := by omega
  have h := pot_dropped_le (b := b) hx hxn hQ
  have h6 : Q ^ 6 ≤ Q ^ (35 * b) := Nat.pow_le_pow_right hQ1 (by omega)
  have hE : Q ^ (2 + b * (4 * (lam n + 6) ^ 2)) ≤
      Q ^ 2 * Q ^ (b * (kap m + 4 * (lam n + 6) ^ 2)) := by
    rw [← pow_add]
    exact Nat.pow_le_pow_right hQ1
      (Nat.add_le_add_left (Nat.mul_le_mul_left b (Nat.le_add_left _ _)) 2)
  calc Q ^ 6 * pot Q b x (2 * x + 1) ≤ pot Q b x (2 * x + 1) * Q ^ (35 * b) := by
        rw [mul_comm]; exact Nat.mul_le_mul_left _ h6
    _ ≤ x * Q ^ (2 + b * (4 * (lam n + 6) ^ 2)) := h
    _ ≤ x * (Q ^ 2 * Q ^ (b * (kap m + 4 * (lam n + 6) ^ 2))) := Nat.mul_le_mul_left x hE

/-- A child keeping the hint with a base of three quarters. -/
theorem pot_kept_step {Q b n m x m' : ℕ} (hb : 2 ≤ b) (hm : 2 ≤ m) (hm' : 4 * m' ≤ 3 * m)
    (hx : x ≤ n) (hQ : 1 ≤ Q) :
    Q ^ 4 * pot Q b x m' ≤ x * (n * (m + 1) * Q ^ (b * (kap m + 4 * (lam n + 6) ^ 2))) := by
  unfold pot
  have hk := kap_add_two_le hm hm'
  have hl : (lam x + 6) ^ 2 ≤ (lam n + 6) ^ 2 := Nat.pow_le_pow_left (by
    have := lam_mono hx; omega) 2
  have hpow : Q ^ 4 * Q ^ (b * (kap m' + 4 * (lam x + 6) ^ 2)) ≤
      Q ^ (b * (kap m + 4 * (lam n + 6) ^ 2)) := by
    rw [← pow_add]
    apply Nat.pow_le_pow_right hQ
    have h1 : kap m' + 4 * (lam x + 6) ^ 2 + 2 ≤ kap m + 4 * (lam n + 6) ^ 2 := by omega
    have h2 := Nat.mul_le_mul_left b h1
    rw [Nat.mul_add] at h2
    omega
  have hx2 : x ^ 2 * (m' + 1) ≤ x * (n * (m + 1)) := by
    calc x ^ 2 * (m' + 1) = x * (x * (m' + 1)) := by ring
      _ ≤ x * (n * (m + 1)) := Nat.mul_le_mul_left x (Nat.mul_le_mul hx (by omega))
  calc Q ^ 4 * (x ^ 2 * (m' + 1) * Q ^ (b * (kap m' + 4 * (lam x + 6) ^ 2)))
      = x ^ 2 * (m' + 1) * (Q ^ 4 * Q ^ (b * (kap m' + 4 * (lam x + 6) ^ 2))) := by ring
    _ ≤ x * (n * (m + 1)) * Q ^ (b * (kap m + 4 * (lam n + 6) ^ 2)) := Nat.mul_le_mul hx2 hpow
    _ = x * (n * (m + 1) * Q ^ (b * (kap m + 4 * (lam n + 6) ^ 2))) := by ring

/-- The exponent of the potential is at least `3` when `b ≥ 1`. -/
theorem three_le_exp {b n m : ℕ} (hb : 1 ≤ b) : 3 ≤ b * (kap m + 4 * (lam n + 6) ^ 2) := by
  have h36 : 36 ≤ (lam n + 6) ^ 2 := by
    calc 36 = 6 ^ 2 := by norm_num
      _ ≤ (lam n + 6) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  calc 3 ≤ 1 * (kap m + 4 * (lam n + 6) ^ 2) := by omega
    _ ≤ b * (kap m + 4 * (lam n + 6) ^ 2) := Nat.mul_le_mul_right _ hb

/-- **A macro-step with branching.** -/
theorem pot_step {Q b n m c : ℕ} (hb : 2 ≤ b) (hn : 1 ≤ n) (hm : 2 ≤ m) (hQ : n + 2 ≤ Q)
    (hc : c ≤ Q ^ 2) (ch : List (ℕ × Option ℕ)) (hsum : (ch.map Prod.fst).sum ≤ c * n)
    (hch : ∀ x ∈ ch, x.1 ≤ n ∧
      ((∃ m', x.2 = some m' ∧ 4 * m' ≤ 3 * m) ∨ (x.2 = none ∧ 2 * x.1 ≤ n))) :
    (ch.map fun x => potO Q b x.1 x.2).sum + Q ≤ pot Q b n m := by
  have hQ1 : 1 ≤ Q := by omega
  have hQ3 : 3 ≤ Q := by omega
  have hchild : ∀ x ∈ ch, Q ^ 4 * potO Q b x.1 x.2 ≤
      x.1 * (n * (m + 1) * Q ^ (b * (kap m + 4 * (lam n + 6) ^ 2))) := by
    intro x hx
    obtain ⟨hxn, hk | ⟨he, h2⟩⟩ := hch x hx
    · obtain ⟨m', hm'e, hm'⟩ := hk
      rw [hm'e]
      exact pot_kept_step hb hm hm' hxn hQ1
    · rw [he]
      have h := pot_dropped_le' (b := b) (m := m) (by omega) h2 hQ
      have h2' : Q ^ 2 * (Q ^ 4 * potO Q b x.1 none) ≤
          Q ^ 2 * (x.1 * Q ^ (b * (kap m + 4 * (lam n + 6) ^ 2))) := by
        calc Q ^ 2 * (Q ^ 4 * potO Q b x.1 none) = Q ^ 6 * pot Q b x.1 (2 * x.1 + 1) := by
              simp only [potO]; ring
          _ ≤ x.1 * (Q ^ 2 * Q ^ (b * (kap m + 4 * (lam n + 6) ^ 2))) := h
          _ = Q ^ 2 * (x.1 * Q ^ (b * (kap m + 4 * (lam n + 6) ^ 2))) := by ring
      have h3 := Nat.le_of_mul_le_mul_left h2' (by positivity)
      exact le_trans h3 (Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by positivity)))
  have hK3 : Q ^ 3 ≤ Q ^ (b * (kap m + 4 * (lam n + 6) ^ 2)) :=
    Nat.pow_le_pow_right hQ1 (three_le_exp (by omega))
  have hpot : pot Q b n m = n ^ 2 * (m + 1) * Q ^ (b * (kap m + 4 * (lam n + 6) ^ 2)) := rfl
  rw [hpot]
  generalize Q ^ (b * (kap m + 4 * (lam n + 6) ^ 2)) = K at hchild hK3 ⊢
  have hsum' : Q ^ 4 * (ch.map fun x => potO Q b x.1 x.2).sum ≤
      (ch.map Prod.fst).sum * (n * (m + 1) * K) := by
    rw [← List.sum_map_mul_left, ← List.sum_map_mul_right]
    exact List.sum_le_sum hchild
  generalize (ch.map fun x => potO Q b x.1 x.2).sum = S at hsum' ⊢
  generalize (ch.map Prod.fst).sum = s at hsum hsum'
  have h1 : Q ^ 2 * (Q ^ 2 * S) ≤ Q ^ 2 * (n ^ 2 * (m + 1) * K) := by
    calc Q ^ 2 * (Q ^ 2 * S) = Q ^ 4 * S := by ring
      _ ≤ s * (n * (m + 1) * K) := hsum'
      _ ≤ c * n * (n * (m + 1) * K) := Nat.mul_le_mul_right _ hsum
      _ ≤ Q ^ 2 * n * (n * (m + 1) * K) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hc)
      _ = Q ^ 2 * (n ^ 2 * (m + 1) * K) := by ring
  have h2 : Q ^ 2 * S ≤ n ^ 2 * (m + 1) * K := Nat.le_of_mul_le_mul_left h1 (by positivity)
  have hQ9 : 9 ≤ Q ^ 2 := by
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ Q ^ 2 := Nat.pow_le_pow_left hQ3 2
  have h3 : 4 * S ≤ n ^ 2 * (m + 1) * K := le_trans (Nat.mul_le_mul_right S (by omega)) h2
  have h4 : 4 * Q ≤ n ^ 2 * (m + 1) * K := by
    calc 4 * Q ≤ Q ^ 2 * Q := Nat.mul_le_mul_right Q (by omega)
      _ = Q ^ 3 := by ring
      _ ≤ K := hK3
      _ ≤ n ^ 2 * (m + 1) * K := Nat.le_mul_of_pos_left _ (by positivity)
  omega

/-- **A step without branching.** -/
theorem pot_free {Q b n m : ℕ} (hb : 2 ≤ b) (hn : 1 ≤ n) (hQ : n + 2 ≤ Q)
    (ch : List (ℕ × Option ℕ)) (hsum : (ch.map Prod.fst).sum ≤ n)
    (hch : ∀ x ∈ ch, (∃ m', x.2 = some m' ∧ m' ≤ m ∧ (m' < m ∨ x.1 < n)) ∨
      (x.2 = none ∧ 2 * x.1 ≤ n)) :
    (ch.map fun x => potO Q b x.1 x.2).sum + Q ≤ pot Q b n m := by
  have hQ1 : 1 ≤ Q := by omega
  have hchild : ∀ x ∈ ch, potO Q b x.1 x.2 + x.1 * Q ^ (b * (kap m + 4 * (lam n + 6) ^ 2)) ≤
      x.1 * (n * (m + 1) * Q ^ (b * (kap m + 4 * (lam n + 6) ^ 2))) := by
    intro x hx
    have hxn : x.1 ≤ n := le_trans (List.le_sum_of_mem (List.mem_map.2 ⟨x, hx, rfl⟩)) hsum
    rcases hch x hx with ⟨m', hm'e, hm'm, hlt⟩ | ⟨he, h2⟩
    · rw [hm'e]
      simp only [potO, pot]
      have hl : (lam x.1 + 6) ^ 2 ≤ (lam n + 6) ^ 2 := Nat.pow_le_pow_left (by
        have := lam_mono hxn; omega) 2
      have hpow : Q ^ (b * (kap m' + 4 * (lam x.1 + 6) ^ 2)) ≤
          Q ^ (b * (kap m + 4 * (lam n + 6) ^ 2)) :=
        Nat.pow_le_pow_right hQ1 (Nat.mul_le_mul_left b (by have := kap_mono hm'm; omega))
      generalize Q ^ (b * (kap m + 4 * (lam n + 6) ^ 2)) = K at hpow ⊢
      generalize Q ^ (b * (kap m' + 4 * (lam x.1 + 6) ^ 2)) = K' at hpow ⊢
      rcases hlt with hlt | hlt
      · -- a smaller base
        have hx2 : x.1 ^ 2 * (m' + 1) ≤ x.1 * (n * m) := by
          calc x.1 ^ 2 * (m' + 1) = x.1 * (x.1 * (m' + 1)) := by ring
            _ ≤ x.1 * (n * m) := Nat.mul_le_mul_left _ (Nat.mul_le_mul hxn (by omega))
        have hnm : n * m + 1 ≤ n * (m + 1) := by
          rw [Nat.mul_add, mul_one]; omega
        calc x.1 ^ 2 * (m' + 1) * K' + x.1 * K
            ≤ x.1 * (n * m) * K + x.1 * K := Nat.add_le_add_right (Nat.mul_le_mul hx2 hpow) _
          _ = x.1 * (n * m + 1) * K := by ring
          _ ≤ x.1 * (n * (m + 1)) * K := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hnm)
          _ = x.1 * (n * (m + 1) * K) := by ring
      · -- a smaller window
        have hx2 : x.1 ^ 2 * (m' + 1) ≤ x.1 * (x.1 * (m + 1)) := by
          calc x.1 ^ 2 * (m' + 1) = x.1 * (x.1 * (m' + 1)) := by ring
            _ ≤ x.1 * (x.1 * (m + 1)) :=
                Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
        have hxm : x.1 * (m + 1) + 1 ≤ n * (m + 1) := by
          calc x.1 * (m + 1) + 1 ≤ x.1 * (m + 1) + (m + 1) := by omega
            _ = (x.1 + 1) * (m + 1) := by ring
            _ ≤ n * (m + 1) := Nat.mul_le_mul_right _ (by omega)
        calc x.1 ^ 2 * (m' + 1) * K' + x.1 * K
            ≤ x.1 * (x.1 * (m + 1)) * K + x.1 * K :=
              Nat.add_le_add_right (Nat.mul_le_mul hx2 hpow) _
          _ = x.1 * (x.1 * (m + 1) + 1) * K := by ring
          _ ≤ x.1 * (n * (m + 1)) * K := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hxm)
          _ = x.1 * (n * (m + 1) * K) := by ring
    · rw [he]
      rcases Nat.eq_zero_or_pos x.1 with h0 | hx0
      · simp [potO, pot, h0]
      have h := pot_dropped_le' (b := b) (m := m) (by omega) h2 hQ
      have h6 : Q ^ 2 ≤ Q ^ 6 := Nat.pow_le_pow_right hQ1 (by omega)
      have hn2 : 2 ≤ n * (m + 1) :=
        le_trans (by omega : 2 ≤ n) (Nat.le_mul_of_pos_right _ (by omega))
      generalize Q ^ (b * (kap m + 4 * (lam n + 6) ^ 2)) = K at h ⊢
      have h2' : Q ^ 6 * potO Q b x.1 none ≤ Q ^ 6 * (x.1 * K) := by
        calc Q ^ 6 * potO Q b x.1 none = Q ^ 6 * pot Q b x.1 (2 * x.1 + 1) := rfl
          _ ≤ x.1 * (Q ^ 2 * K) := h
          _ ≤ x.1 * (Q ^ 6 * K) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h6)
          _ = Q ^ 6 * (x.1 * K) := by ring
      have h3 := Nat.le_of_mul_le_mul_left h2' (by positivity)
      calc potO Q b x.1 none + x.1 * K ≤ x.1 * K + x.1 * K := Nat.add_le_add_right h3 _
        _ = x.1 * (2 * K) := by ring
        _ ≤ x.1 * (n * (m + 1) * K) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hn2)
  have hKQ : Q ≤ Q ^ (b * (kap m + 4 * (lam n + 6) ^ 2)) := by
    calc Q = Q ^ 1 := (pow_one Q).symm
      _ ≤ _ := Nat.pow_le_pow_right hQ1 (le_trans (by norm_num) (three_le_exp (by omega)))
  have hpot : pot Q b n m = n ^ 2 * (m + 1) * Q ^ (b * (kap m + 4 * (lam n + 6) ^ 2)) := rfl
  have hsum' : (ch.map fun x => potO Q b x.1 x.2).sum +
      (ch.map Prod.fst).sum * Q ^ (b * (kap m + 4 * (lam n + 6) ^ 2)) ≤
      (ch.map Prod.fst).sum * (n * (m + 1) * Q ^ (b * (kap m + 4 * (lam n + 6) ^ 2))) := by
    have := List.sum_le_sum hchild
    rw [List.sum_map_add, List.sum_map_mul_right, List.sum_map_mul_right] at this
    exact this
  rw [hpot]
  generalize Q ^ (b * (kap m + 4 * (lam n + 6) ^ 2)) = K at hKQ hsum' ⊢
  generalize (ch.map fun x => potO Q b x.1 x.2).sum = S at hsum' ⊢
  generalize (ch.map Prod.fst).sum = s at hsum hsum'
  have hKA : K ≤ n * (m + 1) * K := Nat.le_mul_of_pos_left _ (by positivity)
  obtain ⟨d, hd⟩ : ∃ d, n = s + d := ⟨n - s, by omega⟩
  have hnA : n ^ 2 * (m + 1) * K = s * (n * (m + 1) * K) + d * (n * (m + 1) * K) := by
    calc n ^ 2 * (m + 1) * K = n * (n * (m + 1) * K) := by ring
      _ = (s + d) * (n * (m + 1) * K) := by rw [← hd]
      _ = s * (n * (m + 1) * K) + d * (n * (m + 1) * K) := by ring
  rw [hnA]
  rcases Nat.eq_zero_or_pos d with h0 | hd0
  · subst h0
    have : K ≤ s * K := Nat.le_mul_of_pos_left _ (by omega)
    simp only [zero_mul, add_zero]
    omega
  · have : n * (m + 1) * K ≤ d * (n * (m + 1) * K) := Nat.le_mul_of_pos_left _ hd0
    omega

/-- **The bound in closed form.** -/
theorem pot0_le (Q b n : ℕ) :
    potO Q b n none ≤ (2 * n + 2) * n ^ 2 * Q ^ (b * (5 * lam n + 9 + 4 * (lam n + 6) ^ 2)) := by
  simp only [potO, pot]
  have hk : kap (2 * n + 1) ≤ 5 * lam n + 9 := by
    have := kap_le (2 * n + 1)
    have := lam_two_mul_add_one_le n
    omega
  have hpow : Q ^ (b * (kap (2 * n + 1) + 4 * (lam n + 6) ^ 2)) ≤
      Q ^ (b * (5 * lam n + 9 + 4 * (lam n + 6) ^ 2)) := by
    rcases Nat.eq_zero_or_pos Q with rfl | hQ
    · rcases Nat.eq_zero_or_pos b with rfl | hb
      · simp
      · have : 0 < b * (kap (2 * n + 1) + 4 * (lam n + 6) ^ 2) := by positivity
        rw [zero_pow this.ne']
        exact Nat.zero_le _
    · exact Nat.pow_le_pow_right hQ (Nat.mul_le_mul_left b (by omega))
  calc n ^ 2 * (2 * n + 1 + 1) * Q ^ (b * (kap (2 * n + 1) + 4 * (lam n + 6) ^ 2))
      ≤ n ^ 2 * (2 * n + 1 + 1) * Q ^ (b * (5 * lam n + 9 + 4 * (lam n + 6) ^ 2)) :=
        Nat.mul_le_mul_left _ hpow
    _ = (2 * n + 2) * n ^ 2 * Q ^ (b * (5 * lam n + 9 + 4 * (lam n + 6) ^ 2)) := by ring

/-! ### The label invariant -/

/-- `(n/k)^k ≤ C(n, k)`, in the form `n^k ≤ k^k C(n, k)`, for `k ≤ n`. -/
theorem pow_le_pow_mul_choose {n k : ℕ} (h : k ≤ n) : n ^ k ≤ k ^ k * n.choose k := by
  have e1 : n ^ k * k.factorial = ∏ i ∈ Finset.range k, (n * (k - i)) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← Nat.descFactorial_self,
      Nat.descFactorial_eq_prod_range]
  have e2 : k ^ k * n.descFactorial k = ∏ i ∈ Finset.range k, (k * (n - i)) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
      Nat.descFactorial_eq_prod_range]
  have hle : n ^ k * k.factorial ≤ k ^ k * n.descFactorial k := by
    rw [e1, e2]
    apply Finset.prod_le_prod
    intro i _
    rw [Nat.mul_sub, Nat.mul_sub, mul_comm k n]
    exact Nat.sub_le_sub_left (Nat.mul_le_mul_right i h) _
  rw [Nat.descFactorial_eq_factorial_mul_choose] at hle
  have hf : 0 < k.factorial := Nat.factorial_pos k
  have : n ^ k * k.factorial ≤ k ^ k * n.choose k * k.factorial := by
    calc n ^ k * k.factorial ≤ k ^ k * (k.factorial * n.choose k) := hle
      _ = k ^ k * n.choose k * k.factorial := by ring
  exact Nat.le_of_mul_le_mul_right this hf

/-- The Johnson parameter is at most `⌊log₂ m⌋`: `2^s ≤ C(2s, s) ≤ C(m', s) ≤ m`. -/
theorem s_le_lam {m m' s : ℕ} (hC : m'.choose s ≤ m) (hs : 2 * s ≤ m') : s ≤ lam m := by
  rcases Nat.eq_zero_or_pos s with rfl | hs0
  · exact Nat.zero_le _
  have h1 : (2 * s) ^ s ≤ s ^ s * (2 * s).choose s := pow_le_pow_mul_choose (by omega)
  have h2 : 2 ^ s ≤ (2 * s).choose s := by
    have hss : 0 < s ^ s := by positivity
    have : 2 ^ s * s ^ s ≤ (2 * s).choose s * s ^ s := by
      calc 2 ^ s * s ^ s = (2 * s) ^ s := by rw [mul_pow]
        _ ≤ s ^ s * (2 * s).choose s := h1
        _ = (2 * s).choose s * s ^ s := by ring
    exact Nat.le_of_mul_le_mul_right this hss
  have h3 : (2 * s).choose s ≤ m'.choose s := Nat.choose_le_choose s hs
  exact Nat.le_log_of_pow_le (by norm_num) (le_trans h2 (le_trans h3 hC))

/-- `C(n, 2) ≤ C(n, s)` for `2 ≤ s ≤ n/2`. -/
theorem choose_two_le_choose {n s : ℕ} (hs : 2 ≤ s) (hsn : 2 * s ≤ n) :
    n.choose 2 ≤ n.choose s := by
  induction s, hs using Nat.le_induction with
  | base => exact le_rfl
  | succ s hs ih =>
    have h1 : n.choose s ≤ n.choose (s + 1) :=
      Nat.choose_le_succ_of_lt_half_left (by
        rw [Nat.lt_div_iff_mul_lt (by norm_num)]; omega)
    exact le_trans (ih (by omega)) h1

/-- **The label invariant across a Johnson step** into a base of more than
`ℓ ≥ max(2¹¹, (⌊log₂ n₀⌋ + 1)³)` points. -/
theorem johnson_step_label {n₀ m m' s ℓ : ℕ} (hC : m'.choose s ≤ m) (hs : 2 ≤ s)
    (hs' : 2 * s ≤ m') (hm' : ℓ < m') (hℓ : 2 ^ 11 ≤ ℓ) (hℓ' : (lam n₀ + 1) ^ 3 ≤ ℓ)
    (hm : m ≤ n₀) : s * (lam m' + 1) ^ 2 ≤ (lam m + 1) ^ 2 := by
  set L := lam m with hL
  set L' := lam m' with hL'
  -- (i) `s ≤ L ≤ λ(n₀)`
  have hsL : s ≤ L := s_le_lam hC hs'
  have hLA : L ≤ lam n₀ := lam_mono hm
  -- (ii) `11 ≤ L'` and `2^L' ≤ m' < 2^(L'+1)`
  have hm'0 : m' ≠ 0 := by omega
  have h11 : 11 ≤ L' := Nat.le_log_of_pow_le (by norm_num) (by omega)
  have hlow : 2 ^ L' ≤ m' := Nat.pow_log_le_self 2 hm'0
  have hhigh : m' < 2 ^ (L' + 1) := Nat.lt_pow_succ_log_self (by norm_num) m'
  -- `m ≥ C(m', s) ≥ 1`, so `m < 2^(L+1)`
  have hm0 : m ≠ 0 := by
    have : 0 < m'.choose s := Nat.choose_pos (by omega)
    omega
  have hmhigh : m < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) m
  -- (iii) `s³ < 2^(L'+1)`
  have hs3 : s ^ 3 < 2 ^ (L' + 1) := by
    have : s ^ 3 ≤ (lam n₀ + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    omega
  -- (iv) `2^(L' s) < s^s 2^(L+1)`
  have hA : 2 ^ (L' * s) < s ^ s * 2 ^ (L + 1) := by
    have h1 : 2 ^ (L' * s) ≤ m' ^ s := by
      rw [pow_mul]; exact Nat.pow_le_pow_left hlow s
    have h2 : m' ^ s ≤ s ^ s * m'.choose s := pow_le_pow_mul_choose (by omega)
    have h3 : s ^ s * m'.choose s ≤ s ^ s * m := Nat.mul_le_mul_left _ hC
    have h4 : s ^ s * m < s ^ s * 2 ^ (L + 1) :=
      Nat.mul_lt_mul_of_pos_left hmhigh (by positivity)
    omega
  -- (v) `3 L' s < (L' + 1) s + 3 (L + 1)`
  have h8 : 3 * (L' * s) < (L' + 1) * s + 3 * (L + 1) := by
    have h1 : (2 ^ (L' * s)) ^ 3 < (s ^ s * 2 ^ (L + 1)) ^ 3 :=
      Nat.pow_lt_pow_left hA (by norm_num)
    have h2 : (s ^ s * 2 ^ (L + 1)) ^ 3 = (s ^ 3) ^ s * 2 ^ (3 * (L + 1)) := by
      rw [mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, mul_comm s 3, mul_comm (L + 1) 3]
    have h3 : (s ^ 3) ^ s ≤ (2 ^ (L' + 1)) ^ s := Nat.pow_le_pow_left hs3.le s
    have h4 : 2 ^ (3 * (L' * s)) < 2 ^ ((L' + 1) * s + 3 * (L + 1)) := by
      calc 2 ^ (3 * (L' * s)) = (2 ^ (L' * s)) ^ 3 := by rw [← pow_mul, mul_comm]
        _ < (s ^ 3) ^ s * 2 ^ (3 * (L + 1)) := by rw [← h2]; exact h1
        _ ≤ (2 ^ (L' + 1)) ^ s * 2 ^ (3 * (L + 1)) := Nat.mul_le_mul_right _ h3
        _ = 2 ^ ((L' + 1) * s + 3 * (L + 1)) := by rw [← pow_mul, ← pow_add]
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 h4
  -- (vi) `2 L' ≤ L + 2`, from `C(m', 2) ≤ C(m', s) ≤ m`
  have h9 : 2 * L' ≤ L + 2 := by
    have hc2 : m'.choose 2 ≤ m := le_trans (choose_two_le_choose hs hs') hC
    obtain ⟨p, rfl⟩ : ∃ p, m' = p + 1 := ⟨m' - 1, by omega⟩
    have e : (p + 1) * p = (p + 1).choose 2 * 2 := by
      have := Nat.add_one_mul_choose_eq p 1
      simpa using this
    have hlow' : 2 ^ (L' - 1) ≤ p := by
      have : 2 ^ L' = 2 * 2 ^ (L' - 1) := by
        rw [← pow_succ']; congr 1; omega
      omega
    have h1 : 2 ^ (L' + (L' - 1)) ≤ (p + 1) * p := by
      rw [pow_add]; exact Nat.mul_le_mul hlow hlow'
    have h2 : 2 ^ (L' + (L' - 1)) < 2 ^ (L + 2) := by
      calc 2 ^ (L' + (L' - 1)) ≤ (p + 1) * p := h1
        _ = (p + 1).choose 2 * 2 := e
        _ ≤ m * 2 := Nat.mul_le_mul_right 2 hc2
        _ < 2 ^ (L + 1) * 2 := Nat.mul_lt_mul_of_pos_right hmhigh (by norm_num)
        _ = 2 ^ (L + 2) := by ring
    have := (Nat.pow_lt_pow_iff_right (by norm_num)).1 h2
    omega
  -- (vii) the conclusion, with `D = 2 L' - 1`
  obtain ⟨D, hD⟩ : ∃ D, D + 1 = 2 * L' := ⟨2 * L' - 1, by omega⟩
  have hDs : D * s < 3 * (L + 1) := by
    have e : (L' + 1) * s = L' * s + s := by ring
    have e2 : 2 * (L' * s) = D * s + s := by
      rw [show 2 * (L' * s) = (2 * L') * s by ring, ← hD]; ring
    omega
  have hDL : D ≤ L + 1 := by omega
  have hD21 : 21 ≤ D := by omega
  have hsq : 3 * (L' + 1) ^ 2 ≤ D ^ 2 := by
    have e : 4 * (3 * (L' + 1) ^ 2) = 3 * (D + 3) ^ 2 := by
      have : 2 * (L' + 1) = D + 3 := by omega
      calc 4 * (3 * (L' + 1) ^ 2) = 3 * (2 * (L' + 1)) ^ 2 := by ring
        _ = 3 * (D + 3) ^ 2 := by rw [this]
    have : 3 * (D + 3) ^ 2 ≤ 4 * D ^ 2 := by nlinarith
    omega
  have hD0 : 0 < D := by omega
  have key : D * (s * (L' + 1) ^ 2) < D * (L + 1) ^ 2 := by
    calc D * (s * (L' + 1) ^ 2) = D * s * (L' + 1) ^ 2 := by ring
      _ < 3 * (L + 1) * (L' + 1) ^ 2 := Nat.mul_lt_mul_of_pos_right hDs (by positivity)
      _ = (L + 1) * (3 * (L' + 1) ^ 2) := by ring
      _ ≤ (L + 1) * D ^ 2 := Nat.mul_le_mul_left _ hsq
      _ = D * (D * (L + 1)) := by ring
      _ ≤ D * ((L + 1) * (L + 1)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hDL)
      _ = D * (L + 1) ^ 2 := by ring
  exact (Nat.lt_of_mul_lt_mul_left key).le

end GraphIso.Recursion
