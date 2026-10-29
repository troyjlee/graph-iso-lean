module

public import GraphIso.Solver.ValenceAll
public import GraphIso.Valence.Bounded

/-!
# Isomorphism of graphs of every bounded valence with the Schreier–Sims backend

Luks's theorem: for every `Δ ≥ 2`, isomorphism of graphs of maximum degree at most `Δ` in time
polynomial in `n`. The checked entries `giBoundedChecked Δ` (connected graphs,
`GraphIso/Solver/Valence.lean`) and `giBoundedAllChecked Δ` (all graphs,
`GraphIso/Solver/ValenceAll.lean`) run milestone 7's algorithm for maximum degree `Δ`; for
every `k ≥ 2` with `(Δ − 1)! ≤ k` the layer groups have simple sections of order at most `k`
(`Valence.boundedSections_autR`), so every string-isomorphism call has milestone 8's constant
`c = 3 k³ + 3 k² + 12 k + 1` (`Valence.layerPrim_bounded`), and `3 c + 5 = 9k³ + 9k² + 36k + 8`.

**The closed forms**, for every `Δ ≥ 2` and `c ≥ 1`. With `K = N + 2` and `T = K^Δ`, a layer
domain has fewer than `T` points (`pow_add_succ_le`), there are at most `T²` generators, and
`Δ, N ≤ T`; every term of a layer step other than the solver's `6640 (D + 1)^{3c + 5}` is a
polynomial of degree at most six in `T`. So:

* `layerCost_le_pow`: one layer step costs at most `7300 (N + 2)^{Δ (3c + 5)}`;
* `edgeCost_le_pow`, `mainCost_le_pow`: the edge test and the loop over the edges of `Y` add the
  factors `2n + 2` and `Δ (2n + 2)`: `mainCost Δ c n ≤ 7700 Δ (2n + 2)^{Δ (3c + 5) + 2}`;
* `checkedCostB_le_pow`: the checked entry for connected graphs costs at most
  `8100 Δ (2n + 2)^{Δ (3c + 5) + 2}`; `allCheckedCostB_le_pow`: the one for all graphs, at most
  `n²` connected tests, at most `2300 Δ (2n + 2)^{Δ (3c + 5) + 4}`.

**The concrete theorems**, for every `Δ ≥ 2` and `k ≥ 2` with `(Δ − 1)! ≤ k`, with no assumed
oracle:

* **`gi_bounded_checked`**: on every input the connected entry returns `none` exactly when the
  input is not valid connected data of maximum degree at most `Δ` (`GIValidB`), and otherwise a
  correct answer (`GIAnswer`), at cost at most `8100 Δ (2n + 2)^{Δ (9k³ + 9k² + 36k + 8) + 2}`;
  `gi_bounded_simpleGraph'` for connected simple graphs on `Fin n` with every degree at most `Δ`;
* **`gi_bounded_all_checked`**: the same for all graphs (`GIValidAllB`), at cost at most
  `2300 Δ (2n + 2)^{Δ (9k³ + 9k² + 36k + 8) + 4}`; `gi_bounded_all_simpleGraph'` for any simple
  graphs on `Fin n` with every degree at most `Δ`.

The exponent is enormous (`k = 120` for `Δ = 6`) but does not depend on `n`. For `Δ ≤ 5` milestone
7's bounds (`gi5_checked`, `gi5_all_checked`) are far better: there `c = 13`.
-/

@[expose] public section

namespace GraphIso.Graph

open Equiv Cost Programs Sims Luks

/-! ### The closed form for every `Δ` -/

section ClosedForm

/-- **A layer domain has fewer than `(N + 2)^Δ` points** for `Δ ≥ 2`. -/
theorem pow_add_succ_le {N : ℕ} : ∀ {Δ : ℕ}, 2 ≤ Δ → (N + 1) ^ Δ + N + 1 ≤ (N + 2) ^ Δ
  | 0, h => absurd h (by norm_num)
  | 1, h => absurd h (by norm_num)
  | 2, _ => by nlinarith
  | Δ + 3, _ => by
    have ih := pow_add_succ_le (N := N) (Δ := Δ + 2) (by omega)
    have h1 : N + 1 ≤ (N + 1) * (N + 1) := Nat.le_mul_self _
    calc (N + 1) ^ (Δ + 3) + N + 1 = (N + 1) * (N + 1) ^ (Δ + 2) + (N + 1) := by ring
      _ ≤ (N + 1) * ((N + 1) ^ (Δ + 2) + N + 1) := by nlinarith
      _ ≤ (N + 2) * (N + 2) ^ (Δ + 2) := Nat.mul_le_mul (by omega) ih
      _ = (N + 2) ^ (Δ + 3) := by ring

/-- The bounds by `T = (N + 2)^Δ`. -/
theorem le_pow_facts {N Δ : ℕ} (hΔ : 2 ≤ Δ) :
    (N + 1) ^ Δ + N + 1 ≤ (N + 2) ^ Δ ∧ N + 2 ≤ (N + 2) ^ Δ ∧ Δ ≤ (N + 2) ^ Δ :=
  ⟨pow_add_succ_le hΔ, Nat.le_self_pow (by omega) _,
    Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_left (by omega) Δ)⟩

/-- `N² ≤ (N + 1)^Δ` for `Δ ≥ 2`. -/
theorem sq_le_pow {N Δ : ℕ} (hΔ : 2 ≤ Δ) : N * N ≤ (N + 1) ^ Δ :=
  calc N * N ≤ (N + 1) ^ 2 := by nlinarith
    _ ≤ (N + 1) ^ Δ := Nat.pow_le_pow_right (by omega) hΔ

/-- At most `T²` generators. -/
theorem genBound_le_sq {N Δ T : ℕ} (hΔ : 2 ≤ Δ) (hT : (N + 1) ^ Δ + N + 1 ≤ T) :
    Valence.genBound Δ N ≤ T * T := by
  have hNN := sq_le_pow (N := N) hΔ
  have hD : Valence.domBound Δ N + 1 ≤ T := by unfold Valence.domBound; omega
  have h := Nat.mul_le_mul hD hD
  unfold Valence.genBound
  unfold Valence.domBound at h ⊢
  nlinarith

/-- A polynomial of degree at most six in `T ≥ 1` with coefficient sum `a` is at most
`a T⁶`: the monomials. -/
theorem pow_le_six {T : ℕ} (hT : 1 ≤ T) :
    1 ≤ T ^ 6 ∧ T ≤ T ^ 6 ∧ T ^ 2 ≤ T ^ 6 ∧ T ^ 3 ≤ T ^ 6 ∧ T ^ 4 ≤ T ^ 6 ∧ T ^ 5 ≤ T ^ 6 :=
  ⟨Nat.one_le_pow _ _ hT, by simpa using Nat.pow_le_pow_right hT (show 1 ≤ 6 by norm_num),
    Nat.pow_le_pow_right hT (by norm_num), Nat.pow_le_pow_right hT (by norm_num),
    Nat.pow_le_pow_right hT (by norm_num), Nat.pow_le_pow_right hT (by norm_num)⟩

/-- The instance of a layer step. -/
theorem inputCost_le_pow {Δ N T : ℕ} (hΔ : 2 ≤ Δ) (hT : (N + 1) ^ Δ + N + 1 ≤ T)
    (hΔT : Δ ≤ T) : Valence.inputCost Δ N (Valence.genBound Δ N) ≤ 251 * T ^ 6 := by
  have hL := genBound_le_sq hΔ hT
  have hT1 : 1 ≤ T := by omega
  obtain ⟨q0, q1, q2, q3, q4, q5⟩ := pow_le_six hT1
  unfold Valence.inputCost Valence.subsCost Valence.indArrCost Valence.xSubCost Valence.cE
    Valence.cF
  generalize Valence.genBound Δ N = L at *
  generalize (N + 1) ^ Δ = m at *
  have hmT : m ≤ T := by omega
  have hNT : N ≤ T := by omega
  calc _ ≤ T * (T * (T + 12) + 7) + 4 + T * T * (2 * (T * (T * (6 * T * T + 6 * T + 10 + 1) +
          4 * T + 11) + 3 * T + 5) + 6) + T * (T * (6 * T * T + 12 * T + 6 + 5) + 3 * T + 15 +
          20) + 22 * T + 40 := by gcongr
    _ ≤ 251 * T ^ 6 := by ring_nf; omega

/-- The output of a layer step. -/
theorem outCost_le_pow {Δ N T : ℕ} (hT : (N + 1) ^ Δ + N + 1 ≤ T) (hΔT : Δ ≤ T) :
    Valence.outCost Δ N (Valence.domBound Δ N * Valence.domBound Δ N) ≤ 342 * T ^ 6 := by
  have hT1 : 1 ≤ T := by omega
  obtain ⟨q0, q1, q2, q3, q4, q5⟩ := pow_le_six hT1
  have hD : Valence.domBound Δ N ≤ T := by unfold Valence.domBound; omega
  have hNT : N ≤ T := by omega
  unfold Valence.outCost Valence.liftCost Valence.twinsCost Valence.cL Valence.cT Valence.cE
  generalize Valence.domBound Δ N = D at *
  calc _ ≤ T * T * (11 * T + (2 * (T * ((2 * (6 * T * T + 12 * T + 6) + 28) * T + 10 * T + 22 +
          3) + 2 * T + 4) + 3) + 17) + (T * (T * (10 * T + 6 * T * T + 12 * T + 15 + 1) + 6 * T +
          4) + 1) + 7 * T + 15 := by gcongr
    _ ≤ 342 * T ^ 6 := by ring_nf; omega

/-- **One layer step costs at most `7300 (N + 2)^{Δ (3c + 5)}`.** -/
theorem layerCost_le_pow {Δ c N : ℕ} (hΔ : 2 ≤ Δ) (hc : 1 ≤ c) :
    Valence.layerCost Δ c N ≤ 7300 * (N + 2) ^ (Δ * (3 * c + 5)) := by
  obtain ⟨hm, -, hΔT⟩ := le_pow_facts (N := N) hΔ
  have hin := inputCost_le_pow hΔ hm hΔT
  have hout := outCost_le_pow hm hΔT
  have hL := genBound_le_sq hΔ hm
  rw [pow_mul]
  generalize (N + 2) ^ Δ = T at *
  have hT1 : 1 ≤ T := by omega
  have hD : Valence.domBound Δ N + 1 ≤ T := by unfold Valence.domBound; omega
  have hP : (Valence.domBound Δ N + 1) ^ (3 * c + 5) ≤ T ^ (3 * c + 5) :=
    Nat.pow_le_pow_left hD _
  have h6 : T ^ 6 ≤ T ^ (3 * c + 5) := Nat.pow_le_pow_right hT1 (by omega)
  have h4 : 60 * Valence.genBound Δ N * (Valence.domBound Δ N + 1) ^ 2 ≤ 60 * T ^ 6 := by
    have h2 : (Valence.domBound Δ N + 1) ^ 2 ≤ T ^ 2 := Nat.pow_le_pow_left hD 2
    have h := Nat.mul_le_mul hL h2
    have e : T * T * T ^ 2 = T ^ 4 := by ring
    have h46 : T ^ 4 ≤ T ^ 6 := Nat.pow_le_pow_right hT1 (by norm_num)
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ (by omega)
  unfold Valence.layerCost Valence.stepCost
  generalize Valence.inputCost Δ N (Valence.genBound Δ N) = A at *
  generalize Valence.outCost Δ N (Valence.domBound Δ N * Valence.domBound Δ N) = B at *
  generalize 60 * Valence.genBound Δ N * (Valence.domBound Δ N + 1) ^ 2 = C at *
  generalize (Valence.domBound Δ N + 1) ^ (3 * c + 5) = E at *
  generalize T ^ (3 * c + 5) = P at *
  generalize T ^ 6 = Q at *
  omega

/-- The levels from at most four roots. -/
theorem levelsCost_le_pow {Δ N k T : ℕ} (hk : k ≤ 4) (hΔT : Δ ≤ T) (hNT : N ≤ T) (hT1 : 1 ≤ T) :
    Valence.levelsCost Δ N k ≤ 92 * T ^ 4 := by
  have p14 : T ≤ T ^ 4 := by simpa using Nat.pow_le_pow_right hT1 (show 1 ≤ 4 by norm_num)
  have p24 : T ^ 2 ≤ T ^ 4 := Nat.pow_le_pow_right hT1 (by norm_num)
  have p34 : T ^ 3 ≤ T ^ 4 := Nat.pow_le_pow_right hT1 (by norm_num)
  have p04 : 1 ≤ T ^ 4 := Nat.one_le_pow _ _ hT1
  unfold Valence.levelsCost
  calc _ ≤ T * (3 * 4 + 6) + 2 * T + 4 + (T * T + 1) * ((6 * T + 13) * T + 15) := by gcongr
    _ ≤ 92 * T ^ 4 := by ring_nf; omega

/-- **The edge test costs at most `7600 (2n + 2)^{Δ (3c + 5) + 1}`.** -/
theorem edgeCost_le_pow {Δ c n : ℕ} (hΔ : 2 ≤ Δ) (hc : 1 ≤ c) :
    Valence.edgeCost Δ c n ≤ 7600 * (2 * n + 2) ^ (Δ * (3 * c + 5) + 1) := by
  have hl := layerCost_le_pow (N := 2 * n) hΔ hc
  obtain ⟨hm, hNT, hΔT⟩ := le_pow_facts (N := 2 * n) hΔ
  have hL := genBound_le_sq hΔ hm
  have hlev := levelsCost_le_pow (N := 2 * n) (k := 4) le_rfl hΔT (by omega) (by omega)
  rw [pow_succ, pow_mul]
  rw [pow_mul] at hl
  generalize (2 * n + 2) ^ Δ = T at *
  have hT1 : 1 ≤ T := by omega
  have h3 : T ^ 4 ≤ T ^ (3 * c + 5) := Nat.pow_le_pow_right hT1 (by omega)
  have h2 : T * T ≤ T ^ (3 * c + 5) := by
    rw [← pow_two]
    exact Nat.pow_le_pow_right hT1 (by omega)
  have h0 : 1 ≤ T ^ (3 * c + 5) := Nat.one_le_pow _ _ hT1
  generalize T ^ (3 * c + 5) = P at *
  have hKP : 2 * n + 2 ≤ P * (2 * n + 2) := Nat.le_mul_of_pos_left _ h0
  have hPK : P ≤ P * (2 * n + 2) := Nat.le_mul_of_pos_right _ (by omega)
  have hmul : 2 * n * (Valence.layerCost Δ c (2 * n) + 1) ≤ 7300 * (P * (2 * n + 2)) +
      (2 * n + 2) := by
    have := Nat.mul_le_mul (show 2 * n ≤ 2 * n + 2 by omega)
      (show Valence.layerCost Δ c (2 * n) + 1 ≤ 7300 * P + 1 by omega)
    have e : (2 * n + 2) * (7300 * P + 1) = 7300 * (P * (2 * n + 2)) + (2 * n + 2) := by ring
    omega
  unfold Valence.edgeCost
  generalize 2 * n * (Valence.layerCost Δ c (2 * n) + 1) = A at *
  generalize P * (2 * n + 2) = B at *
  generalize T ^ 4 = d at *
  omega

/-- **The algorithm costs at most `7700 Δ (2n + 2)^{Δ (3c + 5) + 2}`.** -/
theorem mainCost_le_pow {Δ c n : ℕ} (hΔ : 2 ≤ Δ) (hc : 1 ≤ c) :
    Valence.mainCost Δ c n ≤ 7700 * Δ * (2 * n + 2) ^ (Δ * (3 * c + 5) + 2) := by
  have he := edgeCost_le_pow (n := n) hΔ hc
  have h1Q : 1 ≤ (2 * n + 2) ^ (Δ * (3 * c + 5) + 1) := Nat.one_le_pow _ _ (by omega)
  rw [show Δ * (3 * c + 5) + 2 = Δ * (3 * c + 5) + 1 + 1 by ring, pow_succ]
  generalize (2 * n + 2) ^ (Δ * (3 * c + 5) + 1) = Q at *
  generalize hK : 2 * n + 2 = K at *
  have hnK : n ≤ K := by omega
  have h1 : n * (Valence.edgeCost Δ c n + 4) ≤ 7600 * (Q * K) + 4 * K := by
    have := Nat.mul_le_mul hnK (show Valence.edgeCost Δ c n + 4 ≤ 7600 * Q + 4 by omega)
    have e : K * (7600 * Q + 4) = 7600 * (Q * K) + 4 * K := by ring
    omega
  have h2 : Δ * (n * (Valence.edgeCost Δ c n + 4)) ≤ 7600 * (Δ * (Q * K)) + 4 * (Δ * K) := by
    have := Nat.mul_le_mul_left Δ h1
    have e : Δ * (7600 * (Q * K) + 4 * K) = 7600 * (Δ * (Q * K)) + 4 * (Δ * K) := by ring
    omega
  have hKW : Δ * K ≤ Δ * (Q * K) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ h1Q)
  have hΔn : Δ * n ≤ Δ * K := Nat.mul_le_mul_left _ hnK
  have h2K : 2 * K ≤ Δ * K := Nat.mul_le_mul_right _ hΔ
  have hΔ2 : Δ * 2 ≤ Δ * K := Nat.mul_le_mul_left _ (by omega)
  have e1 : Valence.mainCost Δ c n =
      Δ * (n * (Valence.edgeCost Δ c n + 4)) + 7 * (Δ * n) + 16 * n + 20 := by
    unfold Valence.mainCost
    ring
  have e2 : 7700 * Δ * (Q * K) = 7700 * (Δ * (Q * K)) := by ring
  rw [e1, e2]
  generalize Δ * (n * (Valence.edgeCost Δ c n + 4)) = A at *
  generalize Δ * (Q * K) = Z at *
  generalize Δ * K = Y at *
  generalize Δ * n = X at *
  omega

/-- The input checks. -/
theorem validCost_le_pow {Δ n T : ℕ} (hΔT : Δ ≤ T) (hnT : n ≤ T) (hT1 : 1 ≤ T) :
    Valence.validCost Δ n ≤ 47 * T ^ 3 := by
  have p13 : T ≤ T ^ 3 := by simpa using Nat.pow_le_pow_right hT1 (show 1 ≤ 3 by norm_num)
  have p23 : T ^ 2 ≤ T ^ 3 := Nat.pow_le_pow_right hT1 (by norm_num)
  have p03 : 1 ≤ T ^ 3 := Nat.one_le_pow _ _ hT1
  unfold Valence.validCost Valence.cN
  calc _ ≤ (T + (T * (9 * T + 17) + 4) + 8) * T + 8 := by gcongr
    _ ≤ 47 * T ^ 3 := by ring_nf; omega

/-- The sub-data of a component. -/
theorem subGCost_le_pow {Δ n T : ℕ} (hΔT : Δ ≤ T) (hnT : n ≤ T) (hT1 : 1 ≤ T) :
    Valence.subGCost Δ n ≤ 27 * T ^ 3 := by
  have p13 : T ≤ T ^ 3 := by simpa using Nat.pow_le_pow_right hT1 (show 1 ≤ 3 by norm_num)
  have p23 : T ^ 2 ≤ T ^ 3 := Nat.pow_le_pow_right hT1 (by norm_num)
  have p03 : 1 ≤ T ^ 3 := Nat.one_le_pow _ _ hT1
  unfold Valence.subGCost
  calc _ ≤ T * (T * (9 * T + 7) + 7) + 4 := by gcongr
    _ ≤ 27 * T ^ 3 := by ring_nf; omega

/-- The gluing of the matched isomorphisms. -/
theorem glueCost_le_pow {n T : ℕ} (hnT : n ≤ T) (hT1 : 1 ≤ T) : glueCost n ≤ 58 * T ^ 3 := by
  have p13 : T ≤ T ^ 3 := by simpa using Nat.pow_le_pow_right hT1 (show 1 ≤ 3 by norm_num)
  have p23 : T ^ 2 ≤ T ^ 3 := Nat.pow_le_pow_right hT1 (by norm_num)
  have p03 : 1 ≤ T ^ 3 := Nat.one_le_pow _ _ hT1
  unfold glueCost
  calc _ ≤ T * (T * (22 * T + 16) + 9) + T * T + 2 * T + 8 := by gcongr
    _ ≤ 58 * T ^ 3 := by ring_nf; omega

/-- The components. -/
theorem compsCost_le_pow {Δ n T : ℕ} (hΔT : Δ ≤ T) (hnT : n ≤ T) (hT1 : 1 ≤ T) :
    Valence.compsCost Δ n ≤ 131 * T ^ 5 := by
  have hl := levelsCost_le_pow (N := n) (k := 1) (by norm_num) hΔT hnT hT1
  have p15 : T ≤ T ^ 4 := by simpa using Nat.pow_le_pow_right hT1 (show 1 ≤ 4 by norm_num)
  have p04 : 1 ≤ T ^ 4 := Nat.one_le_pow _ _ hT1
  have p45 : T * T ^ 4 = T ^ 5 := by ring
  have p5 : T ≤ T ^ 5 := by simpa using Nat.pow_le_pow_right hT1 (show 1 ≤ 5 by norm_num)
  have p05 : 1 ≤ T ^ 5 := Nat.one_le_pow _ _ hT1
  unfold Valence.compsCost Valence.compStepCost
  have h : n * (Valence.levelsCost Δ n 1 + 12 * n + 20 + 1) ≤ T * (125 * T ^ 4) :=
    Nat.mul_le_mul hnT (by omega)
  rw [show T * (125 * T ^ 4) = 125 * T ^ 5 by ring] at h
  omega

/-- **The checked entry for connected graphs costs at most
`8100 Δ (2n + 2)^{Δ (3c + 5) + 2}`.** -/
theorem checkedCostB_le_pow {Δ c n : ℕ} (hΔ : 2 ≤ Δ) (hc : 1 ≤ c) :
    checkedCostB Δ c n ≤ 8100 * Δ * (2 * n + 2) ^ (Δ * (3 * c + 5) + 2) := by
  have hm := mainCost_le_pow (n := n) hΔ hc
  obtain ⟨-, hNT, hΔT⟩ := le_pow_facts (N := 2 * n) hΔ
  have hv := validCost_le_pow (n := n) hΔT (by omega) (by omega)
  have hlev := levelsCost_le_pow (N := n) (k := 1) (by norm_num) hΔT (by omega) (by omega)
  have hT4 : ((2 * n + 2) ^ Δ) ^ 4 ≤ (2 * n + 2) ^ (Δ * (3 * c + 5) + 2) := by
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by omega) (by nlinarith)
  rw [Nat.mul_assoc] at hm ⊢
  generalize (2 * n + 2) ^ (Δ * (3 * c + 5) + 2) = W at *
  generalize (2 * n + 2) ^ Δ = T at *
  have hT1 : 1 ≤ T := by omega
  have p34 : T ^ 3 ≤ T ^ 4 := Nat.pow_le_pow_right hT1 (by norm_num)
  have p14 : T ≤ T ^ 4 := by simpa using Nat.pow_le_pow_right hT1 (show 1 ≤ 4 by norm_num)
  have p04 : 1 ≤ T ^ 4 := Nat.one_le_pow _ _ hT1
  have hWZ : 2 * W ≤ Δ * W := Nat.mul_le_mul_right _ hΔ
  unfold checkedCostB Valence.connCost
  generalize Δ * W = Z at *
  generalize T ^ 4 = a at *
  generalize T ^ 3 = b at *
  omega

/-- **The checked entry for all graphs costs at most `2300 Δ (2n + 2)^{Δ (3c + 5) + 4}`**, with
the bound `7700 Δ (2n + 2)^{Δ (3c + 5) + 2}` on the connected test. -/
theorem allCheckedCostB_le_pow {Δ c n : ℕ} (hΔ : 2 ≤ Δ) :
    allCheckedCostB Δ (7700 * Δ * (2 * n + 2) ^ (Δ * (3 * c + 5) + 2)) n ≤
      2300 * Δ * (2 * n + 2) ^ (Δ * (3 * c + 5) + 4) := by
  obtain ⟨-, hNT, hΔT⟩ := le_pow_facts (N := 2 * n) hΔ
  have hnT : n ≤ (2 * n + 2) ^ Δ := by omega
  have hT1 : 1 ≤ (2 * n + 2) ^ Δ := by omega
  have hv := validCost_le_pow hΔT hnT hT1
  have hs := subGCost_le_pow hΔT hnT hT1
  have hg := glueCost_le_pow hnT hT1
  have hcs := compsCost_le_pow hΔT hnT hT1
  have hT5 : ((2 * n + 2) ^ Δ) ^ 5 ≤ (2 * n + 2) ^ (Δ * (3 * c + 5) + 4) := by
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by omega) (by nlinarith)
  have hKn : 4 * (n * n) ≤ (2 * n + 2) * (2 * n + 2) := by nlinarith
  rw [show Δ * (3 * c + 5) + 4 = Δ * (3 * c + 5) + 2 + 2 by ring,
    pow_add (2 * n + 2) (Δ * (3 * c + 5) + 2) 2] at hT5 ⊢
  generalize (2 * n + 2) ^ (Δ * (3 * c + 5) + 2) = W at *
  generalize 2 * n + 2 = K at *
  generalize K ^ Δ = T at *
  -- the expanded cost
  have e : allCheckedCostB Δ (7700 * Δ * W) n = 2 * Valence.validCost Δ n +
      2 * Valence.compsCost Δ n + n * Valence.subGCost Δ n + n * n * Valence.subGCost Δ n +
      n * n * (7700 * Δ * W) + 2 * (n * n * n) + 17 * (n * n) + 17 * n + glueCost n + 26 := by
    unfold allCheckedCostB Valence.allCost Valence.matchCost Valence.partnerCost
    ring
  -- the connected tests
  have hB : 4 * (n * n * (7700 * Δ * W)) ≤ 7700 * (Δ * (W * K ^ 2)) := by
    have := Nat.mul_le_mul_right (7700 * Δ * W) hKn
    calc _ = 4 * (n * n) * (7700 * Δ * W) := by ring
      _ ≤ K * K * (7700 * Δ * W) := this
      _ = _ := by ring
  -- the other terms
  have h1 : n * Valence.subGCost Δ n ≤ 27 * T ^ 5 := by
    have := Nat.mul_le_mul hnT hs
    have p : T ^ 4 ≤ T ^ 5 := Nat.pow_le_pow_right hT1 (by norm_num)
    rw [show T * (27 * T ^ 3) = 27 * T ^ 4 by ring] at this
    omega
  have h2 : n * n * Valence.subGCost Δ n ≤ 27 * T ^ 5 := by
    have := Nat.mul_le_mul (Nat.mul_le_mul hnT hnT) hs
    rwa [show T * T * (27 * T ^ 3) = 27 * T ^ 5 by ring] at this
  have h3 : n * n * n ≤ T ^ 5 := by
    have := Nat.mul_le_mul (Nat.mul_le_mul hnT hnT) hnT
    have p : T ^ 3 ≤ T ^ 5 := Nat.pow_le_pow_right hT1 (by norm_num)
    rw [show T * T * T = T ^ 3 by ring] at this
    omega
  have h4 : n * n ≤ T ^ 5 := by
    have := Nat.mul_le_mul hnT hnT
    have p : T ^ 2 ≤ T ^ 5 := Nat.pow_le_pow_right hT1 (by norm_num)
    rw [show T * T = T ^ 2 by ring] at this
    omega
  have p35 : T ^ 3 ≤ T ^ 5 := Nat.pow_le_pow_right hT1 (by norm_num)
  have p15 : T ≤ T ^ 5 := by simpa using Nat.pow_le_pow_right hT1 (show 1 ≤ 5 by norm_num)
  have p05 : 1 ≤ T ^ 5 := Nat.one_le_pow _ _ hT1
  have hWZ : 2 * (W * K ^ 2) ≤ Δ * (W * K ^ 2) := Nat.mul_le_mul_right _ hΔ
  rw [e, show 2300 * Δ * (W * K ^ 2) = 2300 * (Δ * (W * K ^ 2)) by ring]
  generalize n * n * (7700 * Δ * W) = X at *
  generalize Δ * (W * K ^ 2) = Z at *
  generalize W * K ^ 2 = V at *
  generalize T ^ 5 = a at *
  generalize T ^ 3 = b at *
  omega

end ClosedForm

/-! ### The concrete theorems -/

/-- The exponent of milestone 8's constant `c = 3 k³ + 3 k² + 12 k + 1`: `3 c + 5`. -/
theorem three_mul_bcp_add_five (k : ℕ) :
    3 * (3 * k ^ 3 + 3 * k ^ 2 + 12 * k + 1) + 5 = 9 * k ^ 3 + 9 * k ^ 2 + 36 * k + 8 := by
  ring

/-- **Isomorphism of connected graphs of maximum degree `Δ` in polynomial time, for every
`Δ ≥ 2`.** The checked entry for `Δ` with the Schreier–Sims backend substituted, run inside
`luksSolver`, with no assumed oracle: on every input `(n, X, Y)` the result is `none` exactly
when `X` and `Y` are not valid connected graph data of maximum degree at most `Δ` on `n` points
(connected in the sense of `Conn`, which holds vacuously for `n = 0`), and otherwise a correct
answer. For every `k ≥ 2` with `(Δ − 1)! ≤ k` the cost is at most
`8100 Δ (2n + 2)^{Δ (9k³ + 9k² + 36k + 8) + 2}`: the layer groups have simple sections of order
at most `k` (`Valence.boundedSections_autR`). -/
theorem gi_bounded_checked {Δ k : ℕ} (hΔ : 2 ≤ Δ) (hk2 : 2 ≤ k) (hk : (Δ - 1).factorial ≤ k)
    (n : ℕ) (X Y : GraphData) :
    ∃ (r : Option (Option (Array ℕ))) (tr : Trace Signature.empty),
      Runs Ctx.empty.O (luksSolver.proc Ty.denote)
        ((Graph.giBoundedChecked Δ Ty.unit Ty.denote (n, X, Y)).subst ssImpl) r tr ∧
      Trace.localCost tr ≤
        8100 * Δ * (2 * n + 2) ^ (Δ * (9 * k ^ 3 + 9 * k ^ 2 + 36 * k + 8) + 2) ∧
      (r = none ↔ ¬ GIValidB Δ n X Y) ∧ ∀ res, r = some res → GIAnswer n X Y res := by
  obtain ⟨r, ⟨tr, hr, hc, hpre⟩, hnone, hsome⟩ :=
    RunsWithin.giBoundedChecked hΔ (Valence.layerPrim_bounded hk2 hk) (by omega) n X Y
  obtain ⟨tr', hr', hc'⟩ := Runs.subst ssImpl_implements hr hpre
  refine ⟨r, tr', hr', ?_, hnone, hsome⟩
  rw [Trace.cost_empty] at hc'
  have hb := checkedCostB_le_pow (n := n) (c := 3 * k ^ 3 + 3 * k ^ 2 + 12 * k + 1) hΔ
    (by omega)
  rw [three_mul_bcp_add_five] at hb
  exact hc'.trans (hc.trans hb)

/-- **The statement for simple graphs given as data.** For valid data of maximum degree `Δ`
whose simple graphs are connected, the checked entry returns `some none` exactly when the
simple graphs are not isomorphic, and `some (some arr)` only when `arr` lists the `n` values of
an isomorphism of the simple graphs. -/
theorem gi_bounded_simpleGraph {Δ k n : ℕ} (hΔ : 2 ≤ Δ) (hk2 : 2 ≤ k)
    (hk : (Δ - 1).factorial ≤ k) {X Y : GraphData} (hX : X.ValidD Δ n) (hY : Y.ValidD Δ n)
    (hcX : (X.toSimpleGraph n).Connected) (hcY : (Y.toSimpleGraph n).Connected) :
    ∃ (res : Option (Array ℕ)) (tr : Trace Signature.empty),
      Runs Ctx.empty.O (luksSolver.proc Ty.denote)
        ((Graph.giBoundedChecked Δ Ty.unit Ty.denote (n, X, Y)).subst ssImpl) (some res) tr ∧
      Trace.localCost tr ≤
        8100 * Δ * (2 * n + 2) ^ (Δ * (9 * k ^ 3 + 9 * k ^ 2 + 36 * k + 8) + 2) ∧
      (res = none ↔ IsEmpty (X.toSimpleGraph n ≃g Y.toSimpleGraph n)) ∧
      ∀ arr, res = some arr → arr.size = n ∧ ∃ e : X.toSimpleGraph n ≃g Y.toSimpleGraph n,
        ∀ v : Fin n, get arr v = e v := by
  have hn : 0 < n := Fin.pos_iff_nonempty.2 hcX.nonempty
  obtain ⟨r, tr, hr, hc, hnone, hsome⟩ := gi_bounded_checked hΔ hk2 hk n X Y
  have hvalid : GIValidB Δ n X Y :=
    ⟨hX, hY, (conn_iff_connected hX hn).2 hcX, (conn_iff_connected hY hn).2 hcY⟩
  rcases r with _ | res
  · exact absurd (hnone.1 rfl) (not_not.2 hvalid)
  obtain ⟨h₁, h₂⟩ := hsome res rfl
  refine ⟨res, tr, hr, hc, ?_, fun arr harr => ?_⟩
  · rw [h₁, ← nonempty_iso_iff hX hY, not_nonempty_iff]
  · obtain ⟨hs, φ, hφ, hv⟩ := h₂ arr harr
    exact ⟨hs, isoOfIsIso hX hY hφ, fun v => by rw [hv v v.2, act_of_lt _ v.2]; rfl⟩

/-- **Isomorphism of connected simple graphs of maximum degree `Δ` in polynomial time, for every
`Δ ≥ 2`.** For connected simple graphs `G` and `H` on `Fin n` with every degree at most `Δ`, the
checked entry for `Δ` on their adjacency lists returns `some none` exactly when `G` and `H` are
not isomorphic, and `some (some arr)` only when `arr` lists the `n` values of an isomorphism
`G ≃g H`; for every `k ≥ 2` with `(Δ − 1)! ≤ k` the cost is at most
`8100 Δ (2n + 2)^{Δ (9k³ + 9k² + 36k + 8) + 2}`. -/
theorem gi_bounded_simpleGraph' {Δ k n : ℕ} (hΔ : 2 ≤ Δ) (hk2 : 2 ≤ k)
    (hk : (Δ - 1).factorial ≤ k) {G H : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    [DecidableRel H.Adj] (hdG : ∀ v, G.degree v ≤ Δ) (hdH : ∀ v, H.degree v ≤ Δ)
    (hcG : G.Connected) (hcH : H.Connected) :
    ∃ (res : Option (Array ℕ)) (tr : Trace Signature.empty),
      Runs Ctx.empty.O (luksSolver.proc Ty.denote)
        ((Graph.giBoundedChecked Δ Ty.unit Ty.denote
          (n, GraphData.ofSimpleGraph G, GraphData.ofSimpleGraph H)).subst ssImpl) (some res) tr ∧
      Trace.localCost tr ≤
        8100 * Δ * (2 * n + 2) ^ (Δ * (9 * k ^ 3 + 9 * k ^ 2 + 36 * k + 8) + 2) ∧
      (res = none ↔ IsEmpty (G ≃g H)) ∧
      ∀ arr, res = some arr → arr.size = n ∧ ∃ e : G ≃g H, ∀ v : Fin n, get arr v = e v := by
  have h := gi_bounded_simpleGraph hΔ hk2 hk (valid_ofSimpleGraph hdG) (valid_ofSimpleGraph hdH)
    (by rwa [toSimpleGraph_ofSimpleGraph]) (by rwa [toSimpleGraph_ofSimpleGraph])
  rw [toSimpleGraph_ofSimpleGraph, toSimpleGraph_ofSimpleGraph] at h
  exact h

/-- **Isomorphism of all graphs of maximum degree `Δ` in polynomial time, for every `Δ ≥ 2`.**
The checked entry for `Δ` with the Schreier–Sims backend substituted, run inside `luksSolver`,
with no assumed oracle: on every input `(n, X, Y)` the result is `none` exactly when `X` or `Y`
is not valid graph data of maximum degree at most `Δ` on `n` points, and otherwise a correct
answer. For every `k ≥ 2` with `(Δ − 1)! ≤ k` the cost is at most
`2300 Δ (2n + 2)^{Δ (9k³ + 9k² + 36k + 8) + 4}`. -/
theorem gi_bounded_all_checked {Δ k : ℕ} (hΔ : 2 ≤ Δ) (hk2 : 2 ≤ k)
    (hk : (Δ - 1).factorial ≤ k) (n : ℕ) (X Y : GraphData) :
    ∃ (r : Option (Option (Array ℕ))) (tr : Trace Signature.empty),
      Runs Ctx.empty.O (luksSolver.proc Ty.denote)
        ((Graph.giBoundedAllChecked Δ Ty.unit Ty.denote (n, X, Y)).subst ssImpl) r tr ∧
      Trace.localCost tr ≤
        2300 * Δ * (2 * n + 2) ^ (Δ * (9 * k ^ 3 + 9 * k ^ 2 + 36 * k + 8) + 4) ∧
      (r = none ↔ ¬ GIValidAllB Δ n X Y) ∧ ∀ res, r = some res → GIAnswer n X Y res := by
  have hc1 : 1 ≤ 3 * k ^ 3 + 3 * k ^ 2 + 12 * k + 1 := by omega
  have hBm : ∀ j ≤ n, Valence.mainCost Δ (3 * k ^ 3 + 3 * k ^ 2 + 12 * k + 1) j ≤
      7700 * Δ * (2 * n + 2) ^ (Δ * (3 * (3 * k ^ 3 + 3 * k ^ 2 + 12 * k + 1) + 5) + 2) :=
    fun j hj => (mainCost_le_pow hΔ hc1).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
  obtain ⟨r, ⟨tr, hr, hc, hpre⟩, hnone, hsome⟩ :=
    RunsWithin.giBoundedAllChecked hΔ (Valence.layerPrim_bounded hk2 hk) hc1 n hBm X Y
  obtain ⟨tr', hr', hc'⟩ := Runs.subst ssImpl_implements hr hpre
  refine ⟨r, tr', hr', ?_, hnone, hsome⟩
  rw [Trace.cost_empty] at hc'
  have hb := allCheckedCostB_le_pow (n := n) (c := 3 * k ^ 3 + 3 * k ^ 2 + 12 * k + 1) hΔ
  refine hc'.trans (hc.trans (hb.trans (le_of_eq ?_)))
  rw [three_mul_bcp_add_five]

/-- **The statement for simple graphs given as data.** For valid data of maximum degree `Δ`,
connected or not, the checked entry returns `some none` exactly when the simple graphs are not
isomorphic, and `some (some arr)` only when `arr` lists the `n` values of an isomorphism of the
simple graphs. -/
theorem gi_bounded_all_simpleGraph {Δ k n : ℕ} (hΔ : 2 ≤ Δ) (hk2 : 2 ≤ k)
    (hk : (Δ - 1).factorial ≤ k) {X Y : GraphData} (hX : X.ValidD Δ n) (hY : Y.ValidD Δ n) :
    ∃ (res : Option (Array ℕ)) (tr : Trace Signature.empty),
      Runs Ctx.empty.O (luksSolver.proc Ty.denote)
        ((Graph.giBoundedAllChecked Δ Ty.unit Ty.denote (n, X, Y)).subst ssImpl) (some res) tr ∧
      Trace.localCost tr ≤
        2300 * Δ * (2 * n + 2) ^ (Δ * (9 * k ^ 3 + 9 * k ^ 2 + 36 * k + 8) + 4) ∧
      (res = none ↔ IsEmpty (X.toSimpleGraph n ≃g Y.toSimpleGraph n)) ∧
      ∀ arr, res = some arr → arr.size = n ∧ ∃ e : X.toSimpleGraph n ≃g Y.toSimpleGraph n,
        ∀ v : Fin n, get arr v = e v := by
  obtain ⟨r, tr, hr, hc, hnone, hsome⟩ := gi_bounded_all_checked hΔ hk2 hk n X Y
  rcases r with _ | res
  · exact absurd (hnone.1 rfl) (not_not.2 ⟨hX, hY⟩)
  obtain ⟨h₁, h₂⟩ := hsome res rfl
  refine ⟨res, tr, hr, hc, ?_, fun arr harr => ?_⟩
  · rw [h₁, ← nonempty_iso_iff hX hY, not_nonempty_iff]
  · obtain ⟨hs, φ, hφ, hv⟩ := h₂ arr harr
    exact ⟨hs, isoOfIsIso hX hY hφ, fun v => by rw [hv v v.2, act_of_lt _ v.2]; rfl⟩

/-- **Isomorphism of all simple graphs of maximum degree `Δ` in polynomial time, for every
`Δ ≥ 2`.** For any simple graphs `G` and `H` on `Fin n` with every degree at most `Δ`,
connected or not, the checked entry for `Δ` on their adjacency lists returns `some none` exactly
when `G` and `H` are not isomorphic, and `some (some arr)` only when `arr` lists the `n` values
of an isomorphism `G ≃g H`; for every `k ≥ 2` with `(Δ − 1)! ≤ k` the cost is at most
`2300 Δ (2n + 2)^{Δ (9k³ + 9k² + 36k + 8) + 4}`. -/
theorem gi_bounded_all_simpleGraph' {Δ k n : ℕ} (hΔ : 2 ≤ Δ) (hk2 : 2 ≤ k)
    (hk : (Δ - 1).factorial ≤ k) {G H : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    [DecidableRel H.Adj] (hdG : ∀ v, G.degree v ≤ Δ) (hdH : ∀ v, H.degree v ≤ Δ) :
    ∃ (res : Option (Array ℕ)) (tr : Trace Signature.empty),
      Runs Ctx.empty.O (luksSolver.proc Ty.denote)
        ((Graph.giBoundedAllChecked Δ Ty.unit Ty.denote
          (n, GraphData.ofSimpleGraph G, GraphData.ofSimpleGraph H)).subst ssImpl) (some res) tr ∧
      Trace.localCost tr ≤
        2300 * Δ * (2 * n + 2) ^ (Δ * (9 * k ^ 3 + 9 * k ^ 2 + 36 * k + 8) + 4) ∧
      (res = none ↔ IsEmpty (G ≃g H)) ∧
      ∀ arr, res = some arr → arr.size = n ∧ ∃ e : G ≃g H, ∀ v : Fin n, get arr v = e v := by
  have h := gi_bounded_all_simpleGraph hΔ hk2 hk (valid_ofSimpleGraph hdG)
    (valid_ofSimpleGraph hdH)
  rw [toSimpleGraph_ofSimpleGraph, toSimpleGraph_ofSimpleGraph] at h
  exact h

end GraphIso.Graph
