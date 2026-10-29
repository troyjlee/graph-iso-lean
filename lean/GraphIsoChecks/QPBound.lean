module

public import GraphIso.Main.QPBound
import all Init.Data.Array.Basic
import all Init.Data.List.Sort.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Mathlib.Data.List.Sort

/-!
# Checks of stage 14j-6c-2: the closed bound

`PLAN-14.md` §14.14 item 6.

* **The small parameters' constants**, by kernel `decide`, at `n₀ = 0, 30, 1000, 2¹⁶`. These are
  instances of `kQP_le`, `ℓQP_le` and `jMaxQ_le` (with `C = 1`, `C' = 3`), which are proved for
  every `n₀`.
* **The magnitude of `Q`** against the closed form, by kernel `decide`:
  `QQP 1 3 4 ≤ 2^{36 (λ(4) + 1)⁶}` and `QQP 1 3 16 ≤ 2^{7 (λ(16) + 1)⁶}`. The constant of
  `QQP_le_exp` is not explicit; these values only show the bound's shape at small `n₀`.
* **Negative controls**, as proofs:
  - `not_qpb_two_pow`: `2^n` is not in `QPB λ 6`, so the class excludes exponential growth;
  - `not_qpb_pow_self`: neither is `(m + 1)^m`, the growth of `c2bRU`, which `Q` does not read;
  - `not_qpb_self_pow`: neither is `n^n`, so the growth step `x^y ∈ QPB λ (e + 1)` needs its
    premise `y ∈ PLB λ e` (here `y = n` is only in `QPB λ 1`).
-/

@[expose] public section

namespace GraphIsoChecks.QPBound

open GraphIso GraphIso.Main GraphIso.Growth GraphIso.Recursion

/-! ### The small parameters' constants -/

example : kQP 1 0 ≤ 39 * (lam 0 + 1) ^ 5 ∧ kQP 1 30 ≤ 39 * (lam 30 + 1) ^ 5 ∧
    kQP 1 1000 ≤ 39 * (lam 1000 + 1) ^ 5 ∧ kQP 1 65536 ≤ 39 * (lam 65536 + 1) ^ 5 := by
  decide +kernel

example : ℓQP 1 3 0 ≤ (4 * 39 + 8 + 2048 + ℓT 3) * (lam 0 + 1) ^ 5 ∧
    ℓQP 1 3 30 ≤ (4 * 39 + 8 + 2048 + ℓT 3) * (lam 30 + 1) ^ 5 ∧
    ℓQP 1 3 65536 ≤ (4 * 39 + 8 + 2048 + ℓT 3) * (lam 65536 + 1) ^ 5 := by
  decide +kernel

example : jMaxQ 3 30 ≤ 6 * (lam 30 + 1) ∧ jMaxQ 3 65536 ≤ 6 * (lam 65536 + 1) ∧
    uMaxQ 65536 = 2 * (lam 65536 + 1) ^ 2 := by
  decide +kernel

/-! ### The magnitude of `Q` -/

example : QQP 1 3 4 ≤ 2 ^ (36 * (lam 4 + 1) ^ 6) := by decide +kernel

example : QQP 1 3 16 ≤ 2 ^ (7 * (lam 16 + 1) ^ 6) := by decide +kernel

/-! ### Negative controls -/

theorem sq_le_two_pow {t : ℕ} (ht : 4 ≤ t) : t ^ 2 ≤ 2 ^ t := by
  induction t, ht using Nat.le_induction with
  | base => norm_num
  | succ t ht ih =>
    rw [pow_succ 2]
    nlinarith

/-- **Exponential growth is not quasi-polynomial**: for every `c` some `n` has
`2^n > 2^{c (λ(n) + 1)⁶}`, namely `n = 2^{2^{c + 7}}`. -/
theorem not_qpb_two_pow : ¬ QPB lam 6 (fun n => 2 ^ n) := by
  rintro ⟨c, hc⟩
  set t := c + 7 with htdef
  have ht := sq_le_two_pow (t := t) (by omega)
  set m := 2 ^ t with hmdef
  have h := hc (2 ^ m)
  have hlam : lam (2 ^ m) = m := Nat.log_pow (by norm_num) m
  rw [hlam] at h
  have h1 : 2 ^ m ≤ c * (m + 1) ^ 6 := (Nat.pow_le_pow_iff_right (by norm_num)).1 h
  have h2 : m + 1 ≤ 2 ^ (t + 1) := by
    have := Nat.one_le_two_pow (n := t)
    rw [pow_succ]
    omega
  have h3 : (m + 1) ^ 6 ≤ 2 ^ (6 * (t + 1)) := by
    rw [pow_mul']
    exact Nat.pow_le_pow_left h2 6
  have h4 : c < 2 ^ c := Nat.lt_two_pow_self
  have h5 : 2 ^ m < 2 ^ (c + 6 * (t + 1)) := by
    calc 2 ^ m ≤ c * (m + 1) ^ 6 := h1
      _ ≤ c * 2 ^ (6 * (t + 1)) := Nat.mul_le_mul_left _ h3
      _ < 2 ^ c * 2 ^ (6 * (t + 1)) := Nat.mul_lt_mul_of_pos_right h4 (by positivity)
      _ = 2 ^ (c + 6 * (t + 1)) := (pow_add _ _ _).symm
  have h6 : m < c + 6 * (t + 1) := (Nat.pow_lt_pow_iff_right (by norm_num)).1 h5
  nlinarith

/-- **`c2bRU`'s growth `(m + 1)^m` is not quasi-polynomial.** -/
theorem not_qpb_pow_self : ¬ QPB lam 6 (fun m => (m + 1) ^ m) := fun h =>
  not_qpb_two_pow (h.mono fun m => by
    rcases m with _ | m
    · simp
    · exact Nat.pow_le_pow_left (by omega) _)

/-- **The growth step needs a polylogarithmic exponent**: `n^n` is not quasi-polynomial, though
`n ∈ QPB λ 1`. -/
theorem not_qpb_self_pow : ¬ QPB lam 6 (fun n => n ^ n) := fun h =>
  not_qpb_two_pow ((QPB.mul (QPB.const 2) h).mono fun n => by
    rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n <;> norm_num
    · exact (Nat.pow_le_pow_left hn n).trans (Nat.le_mul_of_pos_left _ (by norm_num)))

end GraphIsoChecks.QPBound
