module

public import GraphIso.Main.GrowthCosts
public import GraphIso.Main.FullPot

/-!
# The closed bound

Stage 14j-6c-2 (`PLAN-14.md` §14.14, items 3–5). Here the index is `n₀ : ℕ` and the size is
`λ = ⌊log₂⌋` (`lam`).

* **The small parameters** (item 3): `n₀ ∈ QPB λ 1` (`id_qpb`), `qpL ∈ PLB λ 1`, and in
  `PLB λ 5` the certificate size `kQP C`, the base threshold `ℓQP C C'`, `min(ℓ, 2n₀)` (`mLQ`),
  `uMaxQ` and `jMaxQ C'`. The constants are explicit, with `X = λ(n₀) + 1`:
  - `qpL ≤ 2X` (`qpL_le`) and `kQP C ≤ (32 C + 7) X⁵` (`kQP_le`);
  - `ℓQP C C' ≤ (4 (32 C + 7) + 2056 + ℓT C') X⁵` (`ℓQP_le`);
  - `uMaxQ = 2X²` and `jMaxQ C' ≤ 2 C' X` (`jMaxQ_le`).
* **`Q`'s parts**: the tests (`qpTest`), M4 maximized over its depth (`qpM4`), M5 (`qpM5`),
  every case (`qpCases`) and the factors and counted calls (`qpFac`) are in `QPB λ 6`. These
  lemmas are generated like `GrowthCosts.lean`'s. M3's factorial `(N − n)!` is at
  `N − n = 2n₀ − (2n₀ − min(ℓ, 2n₀)) ≤ min(ℓ, 2n₀)` (`m3_sub_plb`).
* **`QQP_le_exp`** (item 4): for all `C`, `C'` there is `c` with
  `QQP C C' n₀ ≤ 2^{c (λ(n₀) + 1)⁶}` for every `n₀`.
* **`mainSolve_qp_exp`** (item 5): for all `C`, `C'` there is `c` such that, under
  `QPHyp K T C C'` for any `K` and `T`, `mainEntry (thrQP C C')` returns a correct answer on every
  valid plain instance within `genCost N |gs| + 2^{c (λ(N) + 1)⁸}`. The constant depends only on
  `C` and `C'`. The proof is `mainSolve_qp_closed`: `Q`'s exponent there is
  `2 (5 λ(N) + 9 + 4 (λ(N) + 6)²) ≤ 306 (λ(N) + 1)²`.

`QPHyp` is not shown satisfiable. **Historical:** milestones 15 (Pyber) and 16 (Wielandt) were
to supply `K` and `T` with its growth bounds; milestone 16 gives only a quadratic `T`, for which
`QPHyp` fails (`not_qpHyp_Tq`). The unconditional bound is `mainSolve_qp_expJ`
(`GraphIso/Main/QPJ.lean`) under the generalized `QPHypJ`, discharged by `qpHypJ_final`:
`mainSolve_final` (`GraphIso/Wielandt/Final.lean`).
-/

@[expose] public section

namespace GraphIso.Growth

open GraphIso.Main GraphIso.Recursion

/-! ### The small parameters -/

/-- `n ≤ 2^(λ(n) + 1)`. -/
theorem id_qpb : QPB lam 1 (fun n => n) :=
  ⟨1, fun n => by
    rw [one_mul, pow_one]
    exact (Nat.lt_pow_succ_log_self (by norm_num) n).le⟩

/-- `n < 2^(λ(n) + 1)`. -/
theorem lt_two_pow_lam (n : ℕ) : n < 2 ^ (lam n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n

/-- `qpL n₀ = ⌈log₂(n₀ + 2)⌉ ≤ 2 (λ(n₀) + 1)`. -/
theorem qpL_le (n : ℕ) : qpL n ≤ 2 * (lam n + 1) := by
  have h := lt_two_pow_lam n
  have h2 : n + 2 ≤ 2 ^ (lam n + 2) := by rw [pow_succ]; omega
  exact (Nat.clog_le_of_le_pow h2).trans (by omega)

/-- **The certificate size**: `k = C L⁵ + L + 5 ≤ (32 C + 7) (λ(n₀) + 1)⁵`. -/
theorem kQP_le (C n : ℕ) : kQP C n ≤ (32 * C + 7) * (lam n + 1) ^ 5 := by
  have hL := qpL_le n
  have hX : 1 ≤ lam n + 1 := by omega
  have hZ : lam n + 1 ≤ (lam n + 1) ^ 5 :=
    (pow_one (lam n + 1)).symm.le.trans (Nat.pow_le_pow_right hX (by norm_num))
  have h5 : qpL n * qpL n * qpL n * qpL n * qpL n ≤ 32 * (lam n + 1) ^ 5 := by
    calc qpL n * qpL n * qpL n * qpL n * qpL n = qpL n ^ 5 := by ring
      _ ≤ (2 * (lam n + 1)) ^ 5 := Nat.pow_le_pow_left hL 5
      _ = 32 * (lam n + 1) ^ 5 := by ring
  unfold kQP
  calc C * (qpL n * qpL n * qpL n * qpL n * qpL n) + qpL n + 5
      ≤ C * (32 * (lam n + 1) ^ 5) + 7 * (lam n + 1) ^ 5 := by
        have := Nat.mul_le_mul_left C h5
        omega
    _ = (32 * C + 7) * (lam n + 1) ^ 5 := by ring

/-- **The base threshold**: `ℓ = 4k + L³ + 2048 + ℓT C' ≤ c_ℓ (λ(n₀) + 1)⁵` with
`c_ℓ = 4 (32 C + 7) + 8 + 2048 + ℓT C'`. -/
theorem ℓQP_le (C C' n : ℕ) :
    ℓQP C C' n ≤ (4 * (32 * C + 7) + 8 + 2048 + ℓT C') * (lam n + 1) ^ 5 := by
  have hk := kQP_le C n
  have hL := qpL_le n
  have hX : 1 ≤ lam n + 1 := by omega
  have hZ1 : 1 ≤ (lam n + 1) ^ 5 := Nat.one_le_pow _ _ (by omega)
  have h3 : qpL n * qpL n * qpL n ≤ 8 * (lam n + 1) ^ 5 := by
    calc qpL n * qpL n * qpL n = qpL n ^ 3 := by ring
      _ ≤ (2 * (lam n + 1)) ^ 3 := Nat.pow_le_pow_left hL 3
      _ = 8 * (lam n + 1) ^ 3 := by ring
      _ ≤ 8 * (lam n + 1) ^ 5 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hX (by norm_num))
  have hT : ℓT C' ≤ ℓT C' * (lam n + 1) ^ 5 := Nat.le_mul_of_pos_right _ hZ1
  unfold ℓQP
  rw [Nat.add_mul, Nat.add_mul, Nat.add_mul, Nat.mul_assoc 4]
  omega

/-- `jMax = C' (λ(2n₀) + 1) ≤ 2 C' (λ(n₀) + 1)`. -/
theorem jMaxQ_le (C' n : ℕ) : jMaxQ C' n ≤ 2 * C' * (lam n + 1) := by
  have h : lam (2 * n) ≤ lam n + 1 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [lam]
    · have := lt_two_pow_lam n
      have h2 : 2 * n < 2 ^ (lam n + 2) := by rw [pow_succ]; omega
      exact Nat.lt_succ_iff.1 (Nat.log_lt_of_lt_pow (by omega) h2)
  unfold jMaxQ
  calc C' * (lam (2 * n) + 1) ≤ C' * (2 * (lam n + 1)) := Nat.mul_le_mul_left _ (by omega)
    _ = 2 * C' * (lam n + 1) := by ring

theorem lam_plb : PLB lam 1 lam := ⟨1, fun n => by rw [one_mul, pow_one]; omega⟩

theorem qpL_plb : PLB lam 1 qpL := ⟨2, fun n => by rw [pow_one]; exact qpL_le n⟩

theorem kQP_plb (C : ℕ) : PLB lam 5 (kQP C) := ⟨_, kQP_le C⟩

theorem ℓQP_plb (C C' : ℕ) : PLB lam 5 (fun n => ℓQP C C' n) := ⟨_, ℓQP_le C C'⟩

/-- `min(ℓ, 2n₀)`. -/
theorem mLQ_plb (C C' : ℕ) : PLB lam 5 (fun n => mLQ C C' n) :=
  (ℓQP_plb C C').mono fun _ => Nat.min_le_left _ _

/-- `uMax = 2 (λ(n₀) + 1)²`. -/
theorem uMaxQ_plb : PLB lam 5 (fun n => uMaxQ n) :=
  ⟨2, fun n => Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by norm_num))⟩

theorem jMaxQ_plb (C' : ℕ) : PLB lam 5 (fun n => jMaxQ C' n) :=
  ⟨2 * C', fun n => (jMaxQ_le C' n).trans (Nat.mul_le_mul_left _
    ((pow_one (lam n + 1)).symm.le.trans (Nat.pow_le_pow_right (by omega) (by norm_num))))⟩

/-- **M3's factorial** at its corner: `2n₀ − (2n₀ − min(ℓ, 2n₀)) ≤ min(ℓ, 2n₀)`. -/
theorem m3_sub_plb (C C' : ℕ) :
    PLB lam 5 (fun n₀ => 2 * n₀ - (2 * n₀ - mLQ C C' n₀)) :=
  (mLQ_plb C C').mono fun _ => by omega

/-! ### `Q`'s parts -/

theorem Main.qpTest_qpb (C : ℕ) :
    QPB lam 6 (fun n₀ => GraphIso.Main.qpTest C n₀) := by
  unfold GraphIso.Main.qpTest
  exact (Main.mainTestCost_qpb (id_qpb.lift (by norm_num))
    (QPB.add (id_qpb.lift (by norm_num)) (QPB.mul (QPB.const _) (id_qpb.lift (by norm_num))))
    (id_qpb.lift (by norm_num)) (Main.sGQ_qpb (id_qpb.lift (by norm_num)))
    (Main.sGQ_qpb (id_qpb.lift (by norm_num)))
    (Main.cTQP_qpb (QPB.const _) (id_qpb.lift (by norm_num))))

theorem Main.qpM4_qpb (C' : ℕ) :
    QPB lam 6 (fun n₀ => GraphIso.Main.qpM4 C' n₀) := by
  unfold GraphIso.Main.qpM4
  exact (QPB.supTo
    (Main.m4PtNsL_qpb (QPB.lift (id_qpb.comp _) (by norm_num))
      (QPB.mul (QPB.const _) (id_qpb.comp _)) (PLB.bvar_le (jMaxQ_plb C'))
      (QPB.lift (id_qpb.comp _) (by norm_num))
      (Main.sGQ_qpb (QPB.lift (id_qpb.comp _) (by norm_num)))
      (QPB.lift (id_qpb.comp _) (by norm_num))
      (Main.sGQ_qpb (QPB.lift (id_qpb.comp _) (by norm_num)))
      (Main.ssLgM4Ns_qpb
        (QPB.add (QPB.mul (QPB.const _) (id_qpb.comp _)) (PLB.qpb (PLB.comp (jMaxQ_plb C') _)))
        (PLB.comp (jMaxQ_plb C') _) (uMaxQ_plb.comp _)
        (Main.sGQ_qpb (QPB.lift (id_qpb.comp _) (by norm_num)))) (uMaxQ_plb.comp _)))

theorem Main.qpM5_qpb (C C' : ℕ) :
    QPB lam 6 (fun n₀ => GraphIso.Main.qpM5 C C' n₀) := by
  unfold GraphIso.Main.qpM5
  exact (QPB.add
    (Main.rbOverSS_qpb
      (QPB.mul (QPB.const _) (id_qpb.lift (by norm_num))) (id_qpb.lift (by norm_num))
      (QPB.mul (QPB.const _) (id_qpb.lift (by norm_num))) (Main.sGQ_qpb (id_qpb.lift (by norm_num)))
      (Main.sGQ_qpb (id_qpb.lift (by norm_num))))
    (Main.m5WorkUB_qpb id_qpb (QPB.mul (QPB.const _) id_qpb) (kQP_plb C) (id_qpb.lift (by norm_num))
      (Main.sGQ_qpb (id_qpb.lift (by norm_num))) (Main.sGQ_qpb (id_qpb.lift (by norm_num)))
      (Main.ssLgM5Ns_qpb (QPB.mul (QPB.const _) id_qpb) (kQP_plb C) uMaxQ_plb (jMaxQ_plb C')
        (Main.sGQ_qpb (id_qpb.lift (by norm_num)))) uMaxQ_plb (jMaxQ_plb C')))

theorem Main.qpCases_qpb (C C' : ℕ) :
    QPB lam 6 (fun n₀ => GraphIso.Main.qpCases C C' n₀) := by
  unfold GraphIso.Main.qpCases
  exact (QPB.add
    (QPB.add
      (QPB.add
        (QPB.add
          (QPB.add
            (QPB.add
              (QPB.add
                (QPB.add
                  (Main.fixedStepCost_qpb (id_qpb.lift (by norm_num)))
                  (Main.chainCost_qpb
                    (QPB.mul (QPB.const _) (id_qpb.lift (by norm_num))) (id_qpb.lift (by norm_num))
                    (id_qpb.lift (by norm_num))))
                (Main.m0WorkSS_qpb (id_qpb.lift (by norm_num))
                  (QPB.mul (QPB.const _) (id_qpb.lift (by norm_num))) (id_qpb.lift (by norm_num))
                  (Main.sGQ_qpb (id_qpb.lift (by norm_num)))
                  (Main.sGQ_qpb (id_qpb.lift (by norm_num)))))
              (Main.m1WorkSS_qpb (id_qpb.lift (by norm_num))
                (QPB.mul (QPB.const _) (id_qpb.lift (by norm_num))) (id_qpb.lift (by norm_num))
                (Main.sGQ_qpb (id_qpb.lift (by norm_num)))
                (Main.sGQ_qpb (id_qpb.lift (by norm_num)))))
            (Main.m2aWorkSS_qpb (id_qpb.lift (by norm_num))
              (QPB.mul (QPB.const _) (id_qpb.lift (by norm_num))) (id_qpb.lift (by norm_num))
              (Main.sGQ_qpb (id_qpb.lift (by norm_num))) (Main.sGQ_qpb (id_qpb.lift (by norm_num)))
              (id_qpb.lift (by norm_num))))
          (Main.m2bWorkSS_qpb (id_qpb.lift (by norm_num))
            (QPB.mul (QPB.const _) (id_qpb.lift (by norm_num))) (id_qpb.lift (by norm_num))
            (Main.sGQ_qpb (id_qpb.lift (by norm_num))) (id_qpb.lift (by norm_num))
            (Main.sGQ_qpb (id_qpb.lift (by norm_num)))))
        (Main.m3WorkSS_qpb
          (QPB.mul (QPB.const _) (id_qpb.lift (by norm_num))) (id_qpb.lift (by norm_num))
          (Main.sGQ_qpb (id_qpb.lift (by norm_num))) (Main.sGQ_qpb (id_qpb.lift (by norm_num)))
          (m3_sub_plb C C'))) (Main.qpM4_qpb C')) (Main.qpM5_qpb C C'))

theorem Main.qpWork_qpb (C C' : ℕ) :
    QPB lam 6 (fun n₀ => GraphIso.Main.qpWork C C' n₀) := by
  unfold GraphIso.Main.qpWork
  exact (QPB.add (Main.qpTest_qpb C) (Main.qpCases_qpb C C'))

theorem Main.qpFac_qpb (C C' : ℕ) :
    QPB lam 6 (fun n₀ => GraphIso.Main.qpFac C C' n₀) := by
  unfold GraphIso.Main.qpFac
  exact (QPB.add
    (QPB.add
      (QPB.add
        (QPB.add
          (QPB.add
            (QPB.add
              (QPB.mul (QPB.const _) (id_qpb.lift (by norm_num))) (QPB.factorial (mLQ_plb C C')))
            (QPB.mul
              (Main.m4R_qpb
                (QPB.add (QPB.mul (QPB.const _) id_qpb) (PLB.qpb (jMaxQ_plb C'))) (jMaxQ_plb C'))
              (QPB.max
                (QPB.mul (QPB.const _) (id_qpb.lift (by norm_num))) (QPB.factorial uMaxQ_plb))))
          (Main.m5FBns_qpb (QPB.mul (QPB.const _) id_qpb) (kQP_plb C) uMaxQ_plb (jMaxQ_plb C')))
        (QPB.add
          (QPB.mul (QPB.const _)
            (Main.certCount_qpb
              (QPB.add id_qpb (QPB.mul (QPB.const _) id_qpb)) (id_qpb.lift (by norm_num))
              (kQP_plb C)))
          (QPB.mul (QPB.const _)
            (Main.c3Count_qpb (QPB.mul (QPB.const _) id_qpb) (kQP_plb C)
              (id_qpb.lift (by norm_num))))))
      (QPB.mul
        (QPB.add (Main.sGQ_qpb (id_qpb.lift (by norm_num))) (QPB.const _))
        (id_qpb.lift (by norm_num)))) (QPB.const _))

theorem Main.QQP_qpb (C C' : ℕ) :
    QPB lam 6 (fun n₀ => GraphIso.Main.QQP C C' n₀) := by
  unfold GraphIso.Main.QQP
  exact (QPB.add
    (QPB.add (QPB.add (id_qpb.lift (by norm_num)) (QPB.const _)) (Main.qpWork_qpb C C'))
    (Main.qpFac_qpb C C'))

end GraphIso.Growth

namespace GraphIso.Main

open Cost GraphIso GraphIso.Recursion Sims

/-- **The closed bound** (`PLAN-14.md` §14.14 item 4): `Q(n₀) ≤ 2^{c (λ(n₀) + 1)⁶}`, with `c`
depending only on `C` and `C'`. -/
theorem QQP_le_exp (C C' : ℕ) : ∃ c, ∀ n₀, QQP C C' n₀ ≤ 2 ^ (c * (lam n₀ + 1) ^ 6) :=
  Growth.Main.QQP_qpb C C'

/-- `Q`'s exponent in `mainSolve_qp_closed` is at most `306 (λ + 1)²`. -/
theorem qp_exponent_le (l : ℕ) : 2 * (5 * l + 9 + 4 * (l + 6) ^ 2) ≤ 306 * (l + 1) ^ 2 := by
  nlinarith

/-- **The closed form of the headline**: `17 + (2N + 2) N² Q^E + Q ≤ 2^{c (λ(N) + 1)⁸}` when
`Q ≤ 2^{c₀ (λ(N) + 1)⁶}`, with `c = 306 c₀ + 7`. -/
theorem qp_closed_le {N Q c₀ : ℕ} (hQ : Q ≤ 2 ^ (c₀ * (lam N + 1) ^ 6)) :
    17 + (2 * N + 2) * N ^ 2 * Q ^ (2 * (5 * lam N + 9 + 4 * (lam N + 6) ^ 2)) + Q ≤
      2 ^ ((306 * c₀ + 7) * (lam N + 1) ^ 8) := by
  set X := lam N + 1 with hX
  set Y := X ^ 8 with hY
  have hX1 : 1 ≤ X := by omega
  have hXY : X ≤ Y := by
    calc X = X ^ 1 := (pow_one X).symm
      _ ≤ X ^ 8 := Nat.pow_le_pow_right hX1 (by norm_num)
  have h6Y : X ^ 6 ≤ Y := Nat.pow_le_pow_right hX1 (by norm_num)
  have hY1 : 1 ≤ Y := hX1.trans hXY
  have hN : N + 1 ≤ 2 ^ X := Nat.lt_pow_succ_log_self (by norm_num) N
  set B := (306 * c₀ + 5) * Y with hB
  -- the three terms are each at most `2^B`
  have t1 : 17 ≤ 2 ^ B := by
    calc 17 ≤ 2 ^ 5 := by norm_num
      _ ≤ 2 ^ B := Nat.pow_le_pow_right (by norm_num) (by rw [hB]; nlinarith)
  have hE := qp_exponent_le (lam N)
  have hQE : Q ^ (2 * (5 * lam N + 9 + 4 * (lam N + 6) ^ 2)) ≤ 2 ^ (306 * c₀ * Y) := by
    calc Q ^ (2 * (5 * lam N + 9 + 4 * (lam N + 6) ^ 2))
        ≤ (2 ^ (c₀ * X ^ 6)) ^ (2 * (5 * lam N + 9 + 4 * (lam N + 6) ^ 2)) :=
          Nat.pow_le_pow_left hQ _
      _ = 2 ^ (c₀ * X ^ 6 * (2 * (5 * lam N + 9 + 4 * (lam N + 6) ^ 2))) := (pow_mul _ _ _).symm
      _ ≤ 2 ^ (306 * c₀ * Y) := by
          refine Nat.pow_le_pow_right (by norm_num) ?_
          calc c₀ * X ^ 6 * (2 * (5 * lam N + 9 + 4 * (lam N + 6) ^ 2))
              ≤ c₀ * X ^ 6 * (306 * X ^ 2) := Nat.mul_le_mul_left _ hE
            _ = 306 * c₀ * Y := by rw [hY]; ring
  have h2N : 2 * N + 2 ≤ 2 ^ (2 * Y) := by
    calc 2 * N + 2 = 2 * (N + 1) := by ring
      _ ≤ 2 * 2 ^ X := Nat.mul_le_mul_left _ hN
      _ = 2 ^ (X + 1) := by rw [pow_succ]; ring
      _ ≤ 2 ^ (2 * Y) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hN2 : N ^ 2 ≤ 2 ^ (2 * Y) := by
    calc N ^ 2 ≤ (2 ^ X) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      _ = 2 ^ (2 * X) := by rw [← pow_mul, mul_comm]
      _ ≤ 2 ^ (2 * Y) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have t2 : (2 * N + 2) * N ^ 2 * Q ^ (2 * (5 * lam N + 9 + 4 * (lam N + 6) ^ 2)) ≤ 2 ^ B := by
    calc (2 * N + 2) * N ^ 2 * Q ^ (2 * (5 * lam N + 9 + 4 * (lam N + 6) ^ 2))
        ≤ 2 ^ (2 * Y) * 2 ^ (2 * Y) * 2 ^ (306 * c₀ * Y) :=
          Nat.mul_le_mul (Nat.mul_le_mul h2N hN2) hQE
      _ = 2 ^ (2 * Y + 2 * Y + 306 * c₀ * Y) := by rw [pow_add, pow_add]
      _ ≤ 2 ^ B := Nat.pow_le_pow_right (by norm_num) (by rw [hB]; nlinarith)
  have t3 : Q ≤ 2 ^ B :=
    hQ.trans (Nat.pow_le_pow_right (by norm_num) (by rw [hB]; nlinarith))
  calc 17 + (2 * N + 2) * N ^ 2 * Q ^ (2 * (5 * lam N + 9 + 4 * (lam N + 6) ^ 2)) + Q
      ≤ 2 ^ B * 4 := by omega
    _ = 2 ^ (B + 2) := by rw [pow_add]; norm_num
    _ ≤ 2 ^ ((306 * c₀ + 7) * Y) := Nat.pow_le_pow_right (by norm_num) (by rw [hB]; nlinarith)

/-- **The headline with the closed bound** (`PLAN-14.md` §14.14 item 5). For all `C`, `C'`
there is `c` such that for all `K` and `T` with `QPHyp K T C C'`, on every valid plain instance
(as in `mainSolve_qp`), `mainEntry (thrQP C C')` returns a correct answer (`AnsOK`) within
`genCost N |gs| + 2^{c (λ(N) + 1)⁸}`. The constant `c` depends only on `C` and `C'`.

`QPHyp` is not shown satisfiable; see the module docstring. The unconditional version is
`mainSolve_final`, through `QPHypJ`. -/
theorem mainSolve_qp_exp (C C' : ℕ) :
    ∃ c, ∀ {K T : ℕ → ℕ}, QPHyp K T C C' →
      ∀ {xy : StrData × StrData} {w : WinData} {σd : PermData} {N : ℕ} {gs : GensData},
        w.Valid N → σd.Valid N → GensData.AllValid N gs →
        IsInvariant (GensData.denote N gs) (w.denote N) →
        ∃ ans : AnswerData Ty.unit,
          RunsWithin ssCtx (mainBody (thrQP C C') Ty.denote)
            (mainEntry Ty.unit Ty.denote (xy, w, σd, N, gs)) ans
            (genCost N gs.length + 2 ^ (c * (lam N + 1) ^ 8)) ∧
          AnsOK ssDV N (w.denote N) (σd.denote N) (gs.denote N) (xy.1.denote N)
            (xy.2.denote N) ans := by
  obtain ⟨c₀, hc₀⟩ := QQP_le_exp C C'
  refine ⟨306 * c₀ + 7, fun hQ xy w σd N gs hw hσ hgs hinv => ?_⟩
  obtain ⟨ans, hrun, hok⟩ := mainSolve_qp_closed hQ (xy := xy) hw hσ hgs hinv
  refine ⟨ans, hrun.mono ?_, hok⟩
  have := qp_closed_le (hc₀ N)
  omega

end GraphIso.Main
