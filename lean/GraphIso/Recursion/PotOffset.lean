module

public import GraphIso.Recursion.Potential

/-!
# The potential with an offset

Stage 14j-6c-1 (`PLAN-14.md` §14.13 item 4). The recursion is charged `potO Q b n bo + Q`: an
empty window has potential `0` but a positive cost, and M5's counted calls may be on empty
windows. A recursive call costs one more than the body's run, so a child is charged
`potO + R` with `R = Q + 1`. For a step whose work is at most `Q`, the sum of `potO + R` over the
children (and the counted calls), plus the work, is at most the parent's potential plus `Q`,
for any `R ≤ 2Q`:

* `pot_step_off`: with branching, under `pot_step`'s hypotheses, for at most `Q³` children;
* `pot_free_off`: without branching, under `pot_free`'s hypotheses, for children with nonempty
  windows;
* `pot_chain_off`: the chain rule. An instance without a hint whose children have no hint and
  nonempty windows, each smaller than the parent's and summing to at most it.

They come from the room in `pot_step` and `pot_free`. With branching the children's potentials
sum to at most `pot / Q²` (`pot_step_mul`), and the potential is at least `Q⁸` for `b ≥ 2`
(`pow_le_pot`). Without branching each child leaves `x · Q^{bE}` (`pot_free_child`).
-/

@[expose] public section

namespace GraphIso.Recursion

/-- **The potential is at least `Q⁸`** for `b ≥ 2`. -/
theorem pow_le_pot {Q b n m : ℕ} (hb : 2 ≤ b) (hn : 1 ≤ n) (hQ : 1 ≤ Q) :
    Q ^ 8 ≤ pot Q b n m := by
  unfold pot
  have h36 : 36 ≤ (lam n + 6) ^ 2 := by
    calc 36 = 6 ^ 2 := by norm_num
      _ ≤ (lam n + 6) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have he : 8 ≤ b * (kap m + 4 * (lam n + 6) ^ 2) := by
    calc 8 = 2 * 4 := by norm_num
      _ ≤ b * (kap m + 4 * (lam n + 6) ^ 2) := Nat.mul_le_mul hb (by omega)
  calc Q ^ 8 ≤ Q ^ (b * (kap m + 4 * (lam n + 6) ^ 2)) := Nat.pow_le_pow_right hQ he
    _ ≤ n ^ 2 * (m + 1) * Q ^ (b * (kap m + 4 * (lam n + 6) ^ 2)) :=
      Nat.le_mul_of_pos_left _ (by positivity)

/-- **The children of a step with branching** have potentials summing to at most `pot / Q²`. -/
theorem pot_step_mul {Q b n m c : ℕ} (hb : 2 ≤ b) (hn : 1 ≤ n) (hm : 2 ≤ m) (hQ : n + 2 ≤ Q)
    (hc : c ≤ Q ^ 2) (ch : List (ℕ × Option ℕ)) (hsum : (ch.map Prod.fst).sum ≤ c * n)
    (hch : ∀ x ∈ ch, x.1 ≤ n ∧
      ((∃ m', x.2 = some m' ∧ 4 * m' ≤ 3 * m) ∨ (x.2 = none ∧ 2 * x.1 ≤ n))) :
    Q ^ 2 * (ch.map fun x => potO Q b x.1 x.2).sum ≤ pot Q b n m := by
  have hQ1 : 1 ≤ Q := by omega
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
  have hpot : pot Q b n m = n ^ 2 * (m + 1) * Q ^ (b * (kap m + 4 * (lam n + 6) ^ 2)) := rfl
  rw [hpot]
  generalize Q ^ (b * (kap m + 4 * (lam n + 6) ^ 2)) = K at hchild ⊢
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
  exact Nat.le_of_mul_le_mul_left h1 (by positivity)

/-- The sum of a constant over a list. -/
theorem sum_map_add_const {α : Type} (l : List α) (f : α → ℕ) (Q : ℕ) :
    (l.map fun x => f x + Q).sum = (l.map f).sum + l.length * Q := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
    ring

/-- **A step with branching, with the offset**: at most `Q³` children (and counted calls) under
`pot_step`'s hypotheses, an offset `R ≤ 2Q` per child, and work at most `Q`. -/
theorem pot_step_off {Q b n m c R W : ℕ} (hb : 2 ≤ b) (hn : 1 ≤ n) (hm : 2 ≤ m)
    (hQ : n + 2 ≤ Q) (hc : c ≤ Q ^ 2) (ch : List (ℕ × Option ℕ))
    (hsum : (ch.map Prod.fst).sum ≤ c * n)
    (hch : ∀ x ∈ ch, x.1 ≤ n ∧
      ((∃ m', x.2 = some m' ∧ 4 * m' ≤ 3 * m) ∨ (x.2 = none ∧ 2 * x.1 ≤ n)))
    (hlen : ch.length ≤ Q ^ 3) (hR : R ≤ 2 * Q) (hW : W ≤ Q) :
    (ch.map fun x => potO Q b x.1 x.2 + R).sum + W ≤ pot Q b n m + Q := by
  have hQ1 : 1 ≤ Q := by omega
  have h1 := pot_step_mul hb hn hm hQ hc ch hsum hch
  have h2 := pow_le_pot (m := m) hb hn hQ1
  have h9 : 9 ≤ Q ^ 2 := by
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ Q ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have h5 : 4 * Q ^ 4 ≤ Q ^ 8 := by
    calc 4 * Q ^ 4 ≤ Q ^ 4 * Q ^ 4 :=
          Nat.mul_le_mul_right _ (le_trans (by norm_num) (Nat.pow_le_pow_left (by omega : 3 ≤ Q) 4))
      _ = Q ^ 8 := by ring
  have hL : ch.length * R ≤ 2 * Q ^ 4 :=
    (Nat.mul_le_mul hlen hR).trans_eq (by ring)
  rw [sum_map_add_const]
  generalize (ch.map fun x => potO Q b x.1 x.2).sum = S at h1 ⊢
  generalize pot Q b n m = P at h1 h2 ⊢
  have h9S : 9 * S ≤ P := le_trans (Nat.mul_le_mul_right S h9) h1
  generalize Q ^ 4 = X at h5 hL
  generalize Q ^ 8 = Y at h2 h5
  omega

/-- **A child of a step without branching** leaves `x · Q^{bE}` of its share of the parent's
potential (the bound in the proof of `pot_free`). -/
theorem pot_free_child {Q b n m : ℕ} (hb : 2 ≤ b) (hn : 1 ≤ n) (hQ : n + 2 ≤ Q)
    {x : ℕ × Option ℕ} (hxn : x.1 ≤ n)
    (hx : (∃ m', x.2 = some m' ∧ m' ≤ m ∧ (m' < m ∨ x.1 < n)) ∨ (x.2 = none ∧ 2 * x.1 ≤ n)) :
    potO Q b x.1 x.2 + x.1 * Q ^ (b * (kap m + 4 * (lam n + 6) ^ 2)) ≤
      x.1 * (n * (m + 1) * Q ^ (b * (kap m + 4 * (lam n + 6) ^ 2))) := by
  have hQ1 : 1 ≤ Q := by omega
  rcases hx with ⟨m', hm'e, hm'm, hlt⟩ | ⟨he, h2⟩
  · rw [hm'e]
    simp only [potO, pot]
    have hpow : Q ^ (b * (kap m' + 4 * (lam x.1 + 6) ^ 2)) ≤
        Q ^ (b * (kap m + 4 * (lam n + 6) ^ 2)) := by
      have hl : (lam x.1 + 6) ^ 2 ≤ (lam n + 6) ^ 2 := Nat.pow_le_pow_left (by
        have := lam_mono hxn; omega) 2
      exact Nat.pow_le_pow_right hQ1 (Nat.mul_le_mul_left b (by have := kap_mono hm'm; omega))
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

/-- `2Q ≤ Q^e` for `Q ≥ 2` and `e ≥ 2`. -/
theorem two_mul_le_pow {Q e : ℕ} (hQ : 2 ≤ Q) (he : 2 ≤ e) : 2 * Q ≤ Q ^ e :=
  calc 2 * Q ≤ Q * Q := Nat.mul_le_mul_right Q hQ
    _ = Q ^ 2 := (sq Q).symm
    _ ≤ Q ^ e := Nat.pow_le_pow_right (by omega) he

/-- **A step without branching, with the offset**: under `pot_free`'s hypotheses, with
nonempty windows, an offset `R ≤ 2Q` per child, and work at most `Q`. -/
theorem pot_free_off {Q b n m R W : ℕ} (hb : 2 ≤ b) (hn : 1 ≤ n) (hQ : n + 2 ≤ Q)
    (ch : List (ℕ × Option ℕ)) (hsum : (ch.map Prod.fst).sum ≤ n)
    (hch : ∀ x ∈ ch, (∃ m', x.2 = some m' ∧ m' ≤ m ∧ (m' < m ∨ x.1 < n)) ∨
      (x.2 = none ∧ 2 * x.1 ≤ n))
    (hpos : ∀ x ∈ ch, 1 ≤ x.1) (hR : R ≤ 2 * Q) (hW : W ≤ Q) :
    (ch.map fun x => potO Q b x.1 x.2 + R).sum + W ≤ pot Q b n m + Q := by
  have hKQ : R ≤ Q ^ (b * (kap m + 4 * (lam n + 6) ^ 2)) :=
    hR.trans (two_mul_le_pow (by omega) (le_trans (by norm_num) (three_le_exp (by omega))))
  have hchild : ∀ x ∈ ch, potO Q b x.1 x.2 + R ≤
      x.1 * (n * (m + 1) * Q ^ (b * (kap m + 4 * (lam n + 6) ^ 2))) := by
    intro x hx
    have hxn : x.1 ≤ n := le_trans (List.le_sum_of_mem (List.mem_map.2 ⟨x, hx, rfl⟩)) hsum
    have h := pot_free_child hb hn hQ hxn (hch x hx)
    have : R ≤ x.1 * Q ^ (b * (kap m + 4 * (lam n + 6) ^ 2)) :=
      le_trans hKQ (Nat.le_mul_of_pos_left _ (hpos x hx))
    omega
  have hs := List.sum_le_sum hchild
  rw [List.sum_map_mul_right] at hs
  have hpot : pot Q b n m = n * (n * (m + 1) * Q ^ (b * (kap m + 4 * (lam n + 6) ^ 2))) := by
    unfold pot; ring
  rw [hpot]
  have := Nat.mul_le_mul_right (n * (m + 1) * Q ^ (b * (kap m + 4 * (lam n + 6) ^ 2))) hsum
  omega

/-- **The chain rule, with the offset**: an instance without a hint, children without a hint
on nonempty windows smaller than the parent's, summing to at most it, an offset `R ≤ 2Q` per
child, and work at most `Q`. -/
theorem pot_chain_off {Q b n R W : ℕ} (hb : 1 ≤ b) (hQ : 2 ≤ Q)
    (ch : List (ℕ × Option ℕ)) (hsum : (ch.map Prod.fst).sum ≤ n)
    (hch : ∀ x ∈ ch, x.2 = none ∧ x.1 < n) (hpos : ∀ x ∈ ch, 1 ≤ x.1) (hR : R ≤ 2 * Q)
    (hW : W ≤ Q) :
    (ch.map fun x => potO Q b x.1 x.2 + R).sum + W ≤ potO Q b n none + Q := by
  have hKQ : R ≤ Q ^ (b * (kap (2 * n + 1) + 4 * (lam n + 6) ^ 2)) :=
    hR.trans (two_mul_le_pow hQ (le_trans (by norm_num) (three_le_exp hb)))
  have hQ1 : 1 ≤ Q := by omega
  generalize hK : Q ^ (b * (kap (2 * n + 1) + 4 * (lam n + 6) ^ 2)) = K at hKQ
  have hchild : ∀ x ∈ ch, potO Q b x.1 x.2 + R ≤ x.1 * ((2 * (n - 1) * n + 1) * K) := by
    intro x hx
    obtain ⟨he, hlt⟩ := hch x hx
    rw [he]
    simp only [potO, pot]
    have hpow : Q ^ (b * (kap (2 * x.1 + 1) + 4 * (lam x.1 + 6) ^ 2)) ≤ K := by
      rw [← hK]
      have hk := kap_mono (show 2 * x.1 + 1 ≤ 2 * n + 1 by omega)
      have hl := Nat.pow_le_pow_left (Nat.add_le_add_right (lam_mono (show x.1 ≤ n by omega)) 6) 2
      exact Nat.pow_le_pow_right hQ1 (Nat.mul_le_mul_left b (by omega))
    have hx2 : x.1 ^ 2 * (2 * x.1 + 1 + 1) ≤ x.1 * (2 * (n - 1) * n) := by
      have h1 : x.1 ≤ n - 1 := by omega
      have h2 : x.1 + 1 ≤ n := by omega
      calc x.1 ^ 2 * (2 * x.1 + 1 + 1) = x.1 * (2 * x.1 * (x.1 + 1)) := by ring
        _ ≤ x.1 * (2 * (n - 1) * n) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.mul_le_mul_left 2 h1) h2)
    have hQx : R ≤ x.1 * K := le_trans hKQ (Nat.le_mul_of_pos_left _ (hpos x hx))
    calc x.1 ^ 2 * (2 * x.1 + 1 + 1) * Q ^ (b * (kap (2 * x.1 + 1) + 4 * (lam x.1 + 6) ^ 2)) +
          R ≤ x.1 * (2 * (n - 1) * n) * K + x.1 * K :=
          Nat.add_le_add (Nat.mul_le_mul hx2 hpow) hQx
      _ = x.1 * ((2 * (n - 1) * n + 1) * K) := by ring
  have hs := List.sum_le_sum hchild
  rw [List.sum_map_mul_right] at hs
  have hpot : potO Q b n none = n ^ 2 * (2 * n + 1 + 1) * K := by
    simp only [potO, pot, hK]
  have hfin : n * ((2 * (n - 1) * n + 1) * K) ≤ n ^ 2 * (2 * n + 1 + 1) * K := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    obtain ⟨d, rfl⟩ : ∃ d, n = d + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    have : (d + 1) * (2 * d * (d + 1) + 1) ≤ (d + 1) ^ 2 * (2 * (d + 1) + 1 + 1) := by
      nlinarith
    calc (d + 1) * ((2 * d * (d + 1) + 1) * K) = (d + 1) * (2 * d * (d + 1) + 1) * K := by ring
      _ ≤ (d + 1) ^ 2 * (2 * (d + 1) + 1 + 1) * K := Nat.mul_le_mul_right _ this
  rw [hpot]
  have := Nat.mul_le_mul_right ((2 * (n - 1) * n + 1) * K) hsum
  omega

end GraphIso.Recursion
