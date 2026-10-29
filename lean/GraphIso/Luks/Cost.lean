module

public import GraphIso.Solver.Cost
public import Mathlib.Algebra.Order.Ring.Basic

/-!
# The cost bound of Luks's strategy

`luksBound Q c m = 2 Q m ^ (c + 1) − Q` for a window of size `m ≥ 1` (and `Q` for the empty
window), where `Q` is the per-invocation unit and `c` the exponent of the bound on primitive
sections. The two recursive steps:

* `luks_seq_arith`: at least two nonempty orbits, whose sizes add up to `m`; the bound is
  superadditive, since `Σ |o| ^ (c + 1) ≤ (Σ |o|) ^ (c + 1)` (`sum_pow_le`);
* `luks_block_arith`: `R ≤ k ^ c` branches, each solving `k ≥ 2` blocks of size `b`; then
  `R k b ^ (c + 1) ≤ (k b) ^ (c + 1)`.

In both, the overheads are absorbed because at least two recursive calls are made, as in
`branch_arith` and `seq_arith` for the default strategy.
-/

@[expose] public section

namespace GraphIso.Luks

open Solver

/-- The cost bound of Luks's strategy for a window of size `m`. -/
def luksBound (Q c m : ℕ) : ℕ := if m = 0 then Q else 2 * Q * m ^ (c + 1) - Q

theorem luksBound_pos {Q c m : ℕ} (hm : m ≠ 0) : luksBound Q c m + Q = 2 * Q * m ^ (c + 1) := by
  simp only [luksBound, hm, ↓reduceIte]
  have : Q ≤ 2 * Q * m ^ (c + 1) := by
    have : 1 ≤ m ^ (c + 1) := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero hm)
    nlinarith
  omega

theorem le_luksBound_of_le {Q c m x : ℕ} (hm : m ≠ 0) (hx : x ≤ Q) : x ≤ luksBound Q c m := by
  have h := luksBound_pos (Q := Q) (c := c) hm
  have : 1 ≤ m ^ (c + 1) := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero hm)
  nlinarith

/-- Powers of a sum dominate sums of powers. -/
theorem sum_pow_le (p : ℕ) (hp : p ≠ 0) : ∀ l : List ℕ, (l.map (· ^ p)).sum ≤ l.sum ^ p
  | [] => by simp [Nat.zero_pow (Nat.pos_of_ne_zero hp)]
  | x :: l => by
    have ih := sum_pow_le p hp l
    have := pow_add_pow_le (Nat.zero_le x) (Nat.zero_le l.sum) hp
    simp only [List.map_cons, List.sum_cons]
    omega

theorem sum_luksBound {Q c : ℕ} :
    ∀ os : List (List ℕ), (∀ o ∈ os, 0 < o.length) →
      (os.map fun o => luksBound Q c o.length).sum + os.length * Q =
        2 * Q * (os.map fun o => o.length ^ (c + 1)).sum
  | [], _ => by simp
  | o :: os, h => by
    have ih := sum_luksBound (Q := Q) (c := c) os fun o' ho' => h o' (List.mem_cons_of_mem _ ho')
    have ho := luksBound_pos (Q := Q) (c := c) (m := o.length)
      (Nat.pos_iff_ne_zero.1 (h o List.mem_cons_self))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    nlinarith

/-- **Arithmetic of the orbit step.** At least two nonempty windows whose sizes add up to the
window size, each with overhead at most `E`. -/
theorem luks_seq_arith {Q P E self c : ℕ} (hQ : P + 2 * E ≤ Q) (hself : self ≤ P)
    {os : List (List ℕ)} (hlen : 2 ≤ os.length) (hpos : ∀ o ∈ os, 0 < o.length)
    {f : List ℕ → ℕ} (hf : ∀ o ∈ os, f o ≤ E + luksBound Q c o.length) :
    self + (os.map f).sum ≤ luksBound Q c (os.map List.length).sum := by
  have hsum := sum_luksBound (Q := Q) (c := c) os hpos
  have hle : (os.map f).sum ≤ os.length * E + (os.map fun o => luksBound Q c o.length).sum := by
    have := sum_map_le_sum_map os f (fun o => E + luksBound Q c o.length) hf
    simpa [List.sum_map_add, sum_map_const] using this
  have hm : (os.map List.length).sum ≠ 0 := by
    obtain ⟨o, ho⟩ : ∃ o, o ∈ os := List.exists_mem_of_length_pos (by omega)
    have := le_sum_of_mem_nat (List.mem_map_of_mem (f := List.length) ho)
    have := hpos o ho
    omega
  have htot := luksBound_pos (Q := Q) (c := c) hm
  have hpow : (os.map fun o => o.length ^ (c + 1)).sum ≤ (os.map List.length).sum ^ (c + 1) := by
    have := sum_pow_le (c + 1) (Nat.succ_ne_zero c) (os.map List.length)
    simpa [List.map_map, Function.comp_def] using this
  have h4 : P + os.length * E + Q ≤ os.length * Q := by nlinarith
  have h5 : 2 * Q * (os.map fun o => o.length ^ (c + 1)).sum ≤
      2 * Q * (os.map List.length).sum ^ (c + 1) := Nat.mul_le_mul_left _ hpow
  nlinarith

/-- **Arithmetic of the block step.** `R ≤ k ^ c` branches, each solving `k ≥ 2` blocks of size
`b ≥ 1` with overhead `E` per block and `E'` per branch. -/
theorem luks_block_arith {Q P E E' self R k b c : ℕ} (hQ : P + 2 * (E + E') ≤ Q)
    (hself : self ≤ P) (hR : R ≤ k ^ c) (hR1 : 1 ≤ R) (hk : 2 ≤ k) (hb : 1 ≤ b) :
    self + R * (E' + k * (E + luksBound Q c b)) ≤ luksBound Q c (k * b) := by
  have hb0 : b ≠ 0 := by omega
  have hkb : k * b ≠ 0 := Nat.mul_ne_zero (by omega) hb0
  have h₁ := luksBound_pos (Q := Q) (c := c) hb0
  have h₂ := luksBound_pos (Q := Q) (c := c) hkb
  -- `R k b ^ (c + 1) ≤ (k b) ^ (c + 1)`
  have hpow : R * k * b ^ (c + 1) ≤ (k * b) ^ (c + 1) := by
    rw [mul_pow, pow_succ k c]
    have : R * k ≤ k ^ c * k := Nat.mul_le_mul_right _ hR
    exact Nat.mul_le_mul_right _ this
  -- at least two recursive calls
  have hx : 2 ≤ R * k := by nlinarith
  have h₃ : P + R * k * E + R * E' + Q ≤ R * k * Q := by
    have : R * E' ≤ R * k * E' := by
      have : R * 1 ≤ R * k := Nat.mul_le_mul_left _ (by omega)
      nlinarith
    nlinarith
  have e : R * (E' + k * (E + luksBound Q c b)) =
      R * E' + R * k * E + R * k * luksBound Q c b := by ring
  rw [e]
  have h₄ : R * k * luksBound Q c b + R * k * Q = 2 * Q * (R * k * b ^ (c + 1)) := by
    have : R * k * (luksBound Q c b + Q) = R * k * (2 * Q * b ^ (c + 1)) := by rw [h₁]
    nlinarith
  have h₅ : 2 * Q * (R * k * b ^ (c + 1)) ≤ 2 * Q * (k * b) ^ (c + 1) :=
    Nat.mul_le_mul_left _ hpow
  omega

end GraphIso.Luks
