module

public import GraphIso.Valence.Validate
public import GraphIso.Solver.Graph

/-!
# Isomorphism of connected graphs of maximum degree `Δ` with the Schreier–Sims backend

`giBoundedChecked Δ D` takes `(n, X, Y)`, checks that `X` and `Y` are valid graph data on `n`
points of maximum degree at most `Δ` and connected, and then runs `Valence.mainProg Δ`. It is
well-formed (`giBoundedChecked_wf`).

* `RunsWithin.giBoundedChecked`: for `Δ ≥ 2` and a constant `c ≥ 1` with `LayerPrim Δ c`,
  against the Schreier–Sims context, on **every** input, the result is `none` exactly when the
  input is invalid (`GIValidB Δ`), and otherwise a correct answer (`GIAnswer`), at cost at most
  `checkedCostB Δ c n`. Connectivity is milestone 4's `Conn`, vacuous on no points. Every
  bounded `Δ` is milestone 9 (`GraphIso/Solver/ValenceBounded.lean`).
* `gi5Checked` is the entry for `Δ = 5` (`gi5Checked_wf`); `RunsWithin.gi5Checked` is the case
  `c = 13` (`Valence.layerPrim_solvable`), at cost at most `checkedCost5 n`.
* `checkedCost5_le`: **`checkedCost5 n ≤ 28600 (2n + 2)²²²`**. One layer instance has at most
  `(N + 2)⁵` points for `N = 2n`, and the solvable bound `6640 (D + 1)⁴⁴` dominates.
* **`gi5_checked`**: the same for the closed program after substituting the Schreier–Sims
  implementations, run inside `luksSolver`, with no assumed oracle.
* `gi5_simpleGraph'`: the statement for mathlib's simple graphs: for connected simple graphs on
  `Fin n` with every degree at most five, given by their adjacency lists, the result is
  `some none` exactly when there is no isomorphism, and `some (some arr)` lists the values of an
  isomorphism. `gi5_simpleGraph` states the same for valid data through their simple graphs.
-/

@[expose] public section

namespace GraphIso.Graph

open Equiv Cost Programs Sims Luks

/-! ### The checked entry -/

/-- Valid connected input of maximum degree `Δ`. On no points it holds for empty data, as
`Conn 0` holds vacuously. -/
def GIValidB (Δ n : ℕ) (X Y : GraphData) : Prop :=
  X.ValidD Δ n ∧ Y.ValidD Δ n ∧ Conn n X ∧ Conn n Y

/-- **The checked entry** for connected graphs of maximum degree `Δ`. -/
def giBoundedChecked (Δ : ℕ) (D : Ty) : (var : Ty → Type) → var Ty.giInput →
    Prog (groupSig D) (Solver.Rec D) var (.option Ty.giOutput) := fun _ inp =>
  .bind (.op1 .fst inp) fun n => .bind (.op1 .snd inp) fun XY =>
  .bind (.op1 .fst XY) fun X => .bind (.op1 .snd XY) fun Y =>
  .bind (Valence.validGraphProg Δ n X) fun vX => .bind (Valence.validGraphProg Δ n Y) fun vY =>
  .bind (.op2 .and vX vY) fun v =>
  .ite v
    (.bind (connProg n X) fun cX => .bind (connProg n Y) fun cY => .bind (.op2 .and cX cY)
      fun c => .ite c (.bind (Valence.mainProg Δ n X Y) fun res => .op1 .some res) (.op0 .none))
    (.op0 .none)

/-- The cost bound of the checked entry, for the constant `c` of the layer steps. -/
def checkedCostB (Δ c n : ℕ) : ℕ :=
  2 * Valence.validCost Δ n + 2 * Valence.connCost Δ n + Valence.mainCost Δ c n + 12

theorem giBoundedChecked_wf (Δ : ℕ) {D : Ty} {var₁ var₂ : Ty → Type} (x₁ : var₁ Ty.giInput)
    (x₂ : var₂ Ty.giInput) :
    Prog.Wf true [⟨Ty.giInput, x₁, x₂⟩] (giBoundedChecked Δ D var₁ x₁)
      (giBoundedChecked Δ D var₂ x₂) := by
  unfold giBoundedChecked
  exact .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun n₁ n₂ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun xy₁ xy₂ =>
    .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun X₁ X₂ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun Y₁ Y₂ =>
    .bind (Valence.wf_validGraphProg Δ (by simp) (by simp)) fun _ _ =>
    .bind (Valence.wf_validGraphProg Δ (by simp) (by simp)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) (.cons (List.Mem.head _) .nil))) fun _ _ =>
    .ite (List.Mem.head _)
      (.bind (wf_connProg (by simp) (by simp)) fun _ _ =>
        .bind (wf_connProg (by simp) (by simp)) fun _ _ =>
        .bind (.prim _ (.cons (by simp) (.cons (List.Mem.head _) .nil))) fun _ _ =>
        .ite (List.Mem.head _)
          (.bind (Valence.wf_mainProg Δ (by simp) (by simp) (by simp)) fun _ _ =>
          .prim _ (.cons (List.Mem.head _) .nil)) (.prim _ .nil))
      (.prim _ .nil)

/-- **The checked entry against the Schreier–Sims context, on every input**, for `Δ ≥ 2` and a
constant `c ≥ 1` with `LayerPrim Δ c`. -/
theorem RunsWithin.giBoundedChecked {Δ c : ℕ} (hΔ₂ : 2 ≤ Δ) (hc : Valence.LayerPrim Δ c)
    (hc1 : 1 ≤ c) (n : ℕ) (X Y : GraphData) :
    ∃ r, RunsWithin ssCtx (luksBody Ty.unit Ty.denote)
        (Graph.giBoundedChecked Δ Ty.unit Ty.denote (n, X, Y)) r (checkedCostB Δ c n) ∧
      (r = none ↔ ¬ GIValidB Δ n X Y) ∧ ∀ res, r = some res → GIAnswer n X Y res := by
  have hvX := Valence.RunsWithin.validGraphProg (X := ssCtx) (body := luksBody Ty.unit Ty.denote)
    Δ n X
  have hvY := Valence.RunsWithin.validGraphProg (X := ssCtx) (body := luksBody Ty.unit Ty.denote)
    Δ n Y
  by_cases hv : (Valence.validGB Δ n X && Valence.validGB Δ n Y) = true
  · rw [Bool.and_eq_true, Valence.validGB_iff, Valence.validGB_iff] at hv
    obtain ⟨hX, hY⟩ := hv
    have hcX := Valence.RunsWithin.connProg (X := ssCtx) (body := luksBody Ty.unit Ty.denote) hX
    have hcY := Valence.RunsWithin.connProg (X := ssCtx) (body := luksBody Ty.unit Ty.denote) hY
    by_cases hc : (connB n X && connB n Y) = true
    · rw [Bool.and_eq_true, connB_iff, connB_iff] at hc
      obtain ⟨hcX', hcY'⟩ := hc
      obtain ⟨res, hrun, h₁, h₂⟩ :=
        Valence.RunsWithin.mainProg hX hY hΔ₂ hc hc1 hcX' hcY'
      refine ⟨some res, ?_, ⟨fun h => absurd h (by simp), fun h => absurd ⟨hX, hY, hcX', hcY'⟩ h⟩,
        fun res' h => ?_⟩
      · apply RunsWithin.mono
        case h =>
          run_step (RunsWithin.prim _ _)
          run_step (RunsWithin.prim _ _)
          run_step (RunsWithin.prim _ _)
          run_step (RunsWithin.prim _ _)
          run_step hvX
          run_step hvY
          run_step (RunsWithin.prim _ _)
          run_with RunsWithin.ite_pos (by
            simp [Prim.eval, (Valence.validGB_iff (n := n) (G := X)).2 hX,
              (Valence.validGB_iff (n := n) (G := Y)).2 hY]) _
          run_step hcX
          run_step hcY
          run_step (RunsWithin.prim _ _)
          run_with RunsWithin.ite_pos (by
            simp [Prim.eval, (connB_iff (n := n) (G := X)).2 hcX',
              (connB_iff (n := n) (G := Y)).2 hcY']) _
          run_step hrun
          exact RunsWithin.prim_le rfl le_rfl
        case hc =>
          simp only [Prim.cost, checkedCostB]
          omega
      · cases h
        exact ⟨h₁, h₂⟩
    · refine ⟨none, ?_, ⟨fun _ ⟨_, _, hcX', hcY'⟩ => hc (by
        rw [Bool.and_eq_true, connB_iff, connB_iff]
        exact ⟨hcX', hcY'⟩), fun _ => rfl⟩, fun res h => absurd h (by simp)⟩
      apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step hvX
        run_step hvY
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.ite_pos (by
          simp [Prim.eval, (Valence.validGB_iff (n := n) (G := X)).2 hX,
            (Valence.validGB_iff (n := n) (G := Y)).2 hY]) _
        run_step hcX
        run_step hcY
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.ite_neg (by simpa [Prim.eval] using hc) _
        exact RunsWithin.prim_le rfl le_rfl
      case hc =>
        simp only [Prim.cost, checkedCostB]
        omega
  · refine ⟨none, ?_, ⟨fun _ ⟨hX, hY, _, _⟩ => hv (by
      rw [Bool.and_eq_true, Valence.validGB_iff, Valence.validGB_iff]
      exact ⟨hX, hY⟩), fun _ => rfl⟩, fun res h => absurd h (by simp)⟩
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step hvX
      run_step hvY
      run_step (RunsWithin.prim _ _)
      run_with RunsWithin.ite_neg (by simpa [Prim.eval] using hv) _
      exact RunsWithin.prim_le rfl le_rfl
    case hc =>
      simp only [Prim.cost, checkedCostB]
      omega

/-! ### Maximum degree five -/

/-- Valid connected input of maximum degree five. On no points it holds for empty data, as
`Conn 0` holds vacuously. -/
def GIValid5 (n : ℕ) (X Y : GraphData) : Prop :=
  X.ValidD 5 n ∧ Y.ValidD 5 n ∧ Conn n X ∧ Conn n Y

/-- **The checked entry** for connected graphs of maximum degree five. -/
def gi5Checked (D : Ty) : (var : Ty → Type) → var Ty.giInput →
    Prog (groupSig D) (Solver.Rec D) var (.option Ty.giOutput) := fun _ inp =>
  .bind (.op1 .fst inp) fun n => .bind (.op1 .snd inp) fun XY =>
  .bind (.op1 .fst XY) fun X => .bind (.op1 .snd XY) fun Y =>
  .bind (Valence.validGraphProg 5 n X) fun vX => .bind (Valence.validGraphProg 5 n Y) fun vY =>
  .bind (.op2 .and vX vY) fun v =>
  .ite v
    (.bind (connProg n X) fun cX => .bind (connProg n Y) fun cY => .bind (.op2 .and cX cY)
      fun c => .ite c (.bind (Valence.mainProg 5 n X Y) fun res => .op1 .some res) (.op0 .none))
    (.op0 .none)

/-- The cost bound of the checked entry. -/
def checkedCost5 (n : ℕ) : ℕ :=
  2 * Valence.validCost 5 n + 2 * Valence.connCost 5 n + Valence.mainCost 5 13 n + 12

theorem gi5Checked_wf {D : Ty} {var₁ var₂ : Ty → Type} (x₁ : var₁ Ty.giInput)
    (x₂ : var₂ Ty.giInput) :
    Prog.Wf true [⟨Ty.giInput, x₁, x₂⟩] (gi5Checked D var₁ x₁) (gi5Checked D var₂ x₂) :=
  giBoundedChecked_wf 5 x₁ x₂

/-- **The checked entry against the Schreier–Sims context, on every input**: the solvable layer
groups give `LayerPrim 5 13`. -/
theorem RunsWithin.gi5Checked (n : ℕ) (X Y : GraphData) :
    ∃ r, RunsWithin ssCtx (luksBody Ty.unit Ty.denote)
        (Graph.gi5Checked Ty.unit Ty.denote (n, X, Y)) r (checkedCost5 n) ∧
      (r = none ↔ ¬ GIValid5 n X Y) ∧ ∀ res, r = some res → GIAnswer n X Y res :=
  RunsWithin.giBoundedChecked (by norm_num) (Valence.layerPrim_solvable le_rfl) (by norm_num)
    n X Y

/-! ### The closed form -/

section ClosedForm

/-! Powers are abstracted (`generalize`) before `omega`, which handles them only as atoms. -/

theorem pow_le_pow_of_two_le {K a b : ℕ} (hK : 2 ≤ K) (h : a ≤ b) : K ^ a ≤ K ^ b :=
  Nat.pow_le_pow_right (by omega) h

theorem le_pow_of_two_le {K b : ℕ} (hK : 2 ≤ K) (h : 1 ≤ b) : K ≤ K ^ b := by
  have := pow_le_pow_of_two_le hK h
  rwa [pow_one] at this

theorem two_mul_le_sq {K : ℕ} (hK : 2 ≤ K) : 2 * K ≤ K ^ 2 := by
  rw [pow_two]
  exact Nat.mul_le_mul_right _ hK

theorem two_mul_sq_le_cube {K : ℕ} (hK : 2 ≤ K) : 2 * K ^ 2 ≤ K ^ 3 :=
  calc 2 * K ^ 2 ≤ K * K ^ 2 := Nat.mul_le_mul_right _ hK
    _ = K ^ 3 := by ring

/-- A layer domain has at most `(N + 2)⁵ − 1` points. -/
theorem domBound_five_succ_le (N : ℕ) : Valence.domBound 5 N + 1 ≤ (N + 2) ^ 5 := by
  have e : (N + 2) ^ 5 = (N + 1) ^ 5 + 5 * (N + 1) ^ 4 + 10 * (N + 1) ^ 3 +
      10 * (N + 1) ^ 2 + 5 * (N + 1) + 1 := by ring
  unfold Valence.domBound
  rw [e]
  generalize (N + 1) ^ 5 = a
  generalize (N + 1) ^ 4 = b
  generalize (N + 1) ^ 3 = c
  generalize (N + 1) ^ 2 = d
  omega

theorem genBound_five_le (N : ℕ) : Valence.genBound 5 N ≤ (N + 2) ^ 10 := by
  have hD := domBound_five_succ_le N
  have hNN : N * N ≤ (N + 1) ^ 5 := by
    calc N * N ≤ (N + 1) ^ 2 := by nlinarith
      _ ≤ (N + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hDN : (N + 1) ^ 5 ≤ Valence.domBound 5 N := by unfold Valence.domBound; omega
  have h : (Valence.domBound 5 N + 1) * (Valence.domBound 5 N + 1) ≤ (N + 2) ^ 5 * (N + 2) ^ 5 :=
    Nat.mul_le_mul hD hD
  rw [show (N + 2) ^ 5 * (N + 2) ^ 5 = (N + 2) ^ 10 by ring] at h
  have hsq : (Valence.domBound 5 N + 1) * (Valence.domBound 5 N + 1) =
      Valence.domBound 5 N * Valence.domBound 5 N + 2 * Valence.domBound 5 N + 1 := by ring
  unfold Valence.genBound
  generalize (N + 2) ^ 10 = c at *
  generalize (N + 1) ^ 5 = b at *
  omega

/-- The levels cost at most `100 K³` for `N + 2 ≤ K` and at most four roots. -/
theorem levelsCost_five_le {N k K : ℕ} (hNK : N + 2 ≤ K) (hk : k ≤ 4) :
    Valence.levelsCost 5 N k ≤ 100 * K ^ 3 := by
  have hK2 : 2 ≤ K := by omega
  have k3 := two_mul_sq_le_cube hK2
  have k2 := two_mul_le_sq hK2
  have h0 : N * N + 1 ≤ K ^ 2 := by
    rw [pow_two]
    nlinarith
  have h1 : (N * N + 1) * ((6 * 5 + 13) * N + 15) ≤ K ^ 2 * (43 * K + 15) :=
    Nat.mul_le_mul h0 (by omega)
  have h2 : K ^ 2 * (43 * K + 15) = 43 * K ^ 3 + 15 * K ^ 2 := by ring
  have h3 : N * (3 * k + 6) ≤ K * 18 := Nat.mul_le_mul (by omega) (by omega)
  unfold Valence.levelsCost
  rw [h2] at h1
  generalize (N * N + 1) * ((6 * 5 + 13) * N + 15) = x at *
  generalize N * (3 * k + 6) = y at *
  generalize K ^ 3 = c at *
  generalize K ^ 2 = b at *
  omega

/-- The cost of the lifts per answer generator, for `N + 2 ≤ K`. -/
theorem lift_five_le {N K : ℕ} (hNK : N + 2 ≤ K) :
    11 * N + (2 * (N * ((2 * (6 * 5 * 5 + 12 * 5 + 6) + 28) * N + 10 * 5 + 22 + 3) +
      2 * N + 4) + 3) + 17 ≤ 1113 * K ^ 2 := by
  have hK2 : 2 ≤ K := by omega
  have k2 := two_mul_le_sq hK2
  have h1 : N * ((2 * (6 * 5 * 5 + 12 * 5 + 6) + 28) * N + 10 * 5 + 22 + 3) ≤
      K * (460 * K + 75) := Nat.mul_le_mul (by omega) (by omega)
  have h2 : K * (460 * K + 75) = 460 * K ^ 2 + 75 * K := by ring
  rw [h2] at h1
  generalize N * ((2 * (6 * 5 * 5 + 12 * 5 + 6) + 28) * N + 10 * 5 + 22 + 3) = x at *
  generalize K ^ 2 = b at *
  omega

/-- The cost of the twin transpositions, for `N + 2 ≤ K`. -/
theorem twins_five_le {N K : ℕ} (hNK : N + 2 ≤ K) :
    N * (N * (10 * N + 6 * 5 * 5 + 12 * 5 + 15 + 1) + 6 * 5 + 4) + 1 ≤ 270 * K ^ 3 := by
  have hK2 : 2 ≤ K := by omega
  have k2 := two_mul_le_sq hK2
  have k3 := two_mul_sq_le_cube hK2
  have h0 : N * (10 * N + 6 * 5 * 5 + 12 * 5 + 15 + 1) ≤ K * (10 * K + 226) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h3 : N * (N * (10 * N + 6 * 5 * 5 + 12 * 5 + 15 + 1) + 6 * 5 + 4) ≤
      K * (K * (10 * K + 226) + 34) := Nat.mul_le_mul (by omega) (by omega)
  have h4 : K * (K * (10 * K + 226) + 34) = 10 * K ^ 3 + 226 * K ^ 2 + 34 * K := by ring
  rw [h4] at h3
  generalize N * (N * (10 * N + 6 * 5 * 5 + 12 * 5 + 15 + 1) + 6 * 5 + 4) = X at h3 ⊢
  generalize K ^ 3 = C at *
  generalize K ^ 2 = B at *
  omega

/-- The instance of a layer step, for `N + 2 ≤ K`. -/
theorem inputCost_five_le {N : ℕ} :
    Valence.inputCost 5 N (Valence.genBound 5 N) ≤ 800 * (N + 2) ^ 20 := by
  set K := N + 2 with hK
  have hK2 : 2 ≤ K := by omega
  have hNK : N ≤ K := by omega
  have hM : (N + 1) ^ 5 ≤ K ^ 5 := Nat.pow_le_pow_left (by omega) 5
  have hL : Valence.genBound 5 N ≤ K ^ 10 := genBound_five_le N
  have e6 : K * K ^ 5 = K ^ 6 := by ring
  have e10 : K ^ 5 * K ^ 5 = K ^ 10 := by ring
  have e20 : K ^ 10 * K ^ 10 = K ^ 20 := by ring
  have p56 : K ^ 5 ≤ K ^ 6 := pow_le_pow_of_two_le hK2 (by norm_num)
  have p16 : K ≤ K ^ 6 := le_pow_of_two_le hK2 (by norm_num)
  have p610 : K ^ 6 ≤ K ^ 10 := pow_le_pow_of_two_le hK2 (by norm_num)
  have p1020 : K ^ 10 ≤ K ^ 20 := pow_le_pow_of_two_le hK2 (by norm_num)
  have p06 : 1 ≤ K ^ 6 := Nat.one_le_pow _ _ (by omega)
  -- the sublists
  have ha : Valence.subsCost 5 N ≤ 28 * K ^ 6 := by
    unfold Valence.subsCost
    have h1 : N * ((N + 1) ^ 5 * (5 + 12) + 7) ≤ K * (K ^ 5 * 17 + 7) :=
      Nat.mul_le_mul hNK (by omega)
    have h2 : K * (K ^ 5 * 17 + 7) = 17 * (K * K ^ 5) + 7 * K := by ring
    rw [h2, e6] at h1
    generalize N * ((N + 1) ^ 5 * (5 + 12) + 7) = x at *
    generalize K ^ 6 = c at *
    omega
  -- one induced array
  have hb : Valence.indArrCost 5 N ((N + 1) ^ 5) ≤ 230 * K ^ 10 := by
    unfold Valence.indArrCost Valence.cF
    have h1 : (N + 1) ^ 5 * ((N + 1) ^ 5 * (6 * 5 * 5 + 6 * 5 + 10 + 1) + 4 * 5 + 11) ≤
        K ^ 5 * (K ^ 5 * 191 + 31) := Nat.mul_le_mul hM (by omega)
    have h2 : K ^ 5 * (K ^ 5 * 191 + 31) = 191 * (K ^ 5 * K ^ 5) + 31 * K ^ 5 := by ring
    rw [h2, e10] at h1
    have p510 : K ^ 5 ≤ K ^ 10 := pow_le_pow_of_two_le hK2 (by norm_num)
    generalize (N + 1) ^ 5 * ((N + 1) ^ 5 * (6 * 5 * 5 + 6 * 5 + 10 + 1) + 4 * 5 + 11) = x at *
    generalize K ^ 10 = c at *
    generalize K ^ 6 = d at *
    generalize K ^ 5 = e at *
    omega
  -- the induced generators
  have hc : Valence.genBound 5 N * (2 * Valence.indArrCost 5 N ((N + 1) ^ 5) + 6) ≤
      466 * K ^ 20 := by
    have h1 : Valence.genBound 5 N * (2 * Valence.indArrCost 5 N ((N + 1) ^ 5) + 6) ≤
        K ^ 10 * (460 * K ^ 10 + 6) := Nat.mul_le_mul hL (by omega)
    have h2 : K ^ 10 * (460 * K ^ 10 + 6) = 460 * (K ^ 10 * K ^ 10) + 6 * K ^ 10 := by ring
    rw [h2, e20] at h1
    generalize Valence.genBound 5 N * (2 * Valence.indArrCost 5 N ((N + 1) ^ 5) + 6) = x at *
    generalize K ^ 20 = c at *
    generalize K ^ 10 = d at *
    omega
  -- the layer string
  have hd : (N + 1) ^ 5 * (Valence.xSubCost 5 N + 20) ≤ 271 * K ^ 6 := by
    unfold Valence.xSubCost Valence.cE
    have h1 : (N + 1) ^ 5 * (N * (6 * 5 * 5 + 12 * 5 + 6 + 5) + 3 * 5 + 15 + 20) ≤
        K ^ 5 * (221 * K + 50) := Nat.mul_le_mul hM (by omega)
    have h2 : K ^ 5 * (221 * K + 50) = 221 * (K * K ^ 5) + 50 * K ^ 5 := by ring
    rw [h2, e6] at h1
    generalize (N + 1) ^ 5 * (N * (6 * 5 * 5 + 12 * 5 + 6 + 5) + 3 * 5 + 15 + 20) = x at *
    generalize K ^ 6 = c at *
    generalize K ^ 5 = e at *
    omega
  unfold Valence.inputCost
  generalize Valence.subsCost 5 N = A at *
  generalize Valence.genBound 5 N * (2 * Valence.indArrCost 5 N ((N + 1) ^ 5) + 6) = B at *
  generalize (N + 1) ^ 5 * (Valence.xSubCost 5 N + 20) = C at *
  generalize K ^ 20 = c at *
  generalize K ^ 10 = d at *
  generalize K ^ 6 = e at *
  omega

/-- The output of a layer step, for `N + 2 ≤ K`. -/
theorem outCost_five_le {N : ℕ} :
    Valence.outCost 5 N (Valence.domBound 5 N * Valence.domBound 5 N) ≤ 1405 * (N + 2) ^ 12 := by
  set K := N + 2 with hK
  have hK2 : 2 ≤ K := by omega
  have hD : Valence.domBound 5 N + 1 ≤ K ^ 5 := domBound_five_succ_le N
  have hDD : Valence.domBound 5 N * Valence.domBound 5 N ≤ K ^ 10 := by
    have := Nat.mul_le_mul (show Valence.domBound 5 N ≤ K ^ 5 by omega)
      (show Valence.domBound 5 N ≤ K ^ 5 by omega)
    rwa [show K ^ 5 * K ^ 5 = K ^ 10 by ring] at this
  unfold Valence.outCost Valence.liftCost Valence.twinsCost Valence.cL Valence.cT Valence.cE
  have hl := lift_five_le (N := N) (K := K) (by omega)
  have h1 := Nat.mul_le_mul hDD hl
  rw [show K ^ 10 * (1113 * K ^ 2) = 1113 * K ^ 12 by ring] at h1
  have ht := twins_five_le (N := N) (K := K) (by omega)
  have p3 : K ^ 3 ≤ K ^ 12 := pow_le_pow_of_two_le hK2 (by norm_num)
  have p1 : K ≤ K ^ 12 := le_pow_of_two_le hK2 (by norm_num)
  generalize Valence.domBound 5 N * Valence.domBound 5 N *
    (11 * N + (2 * (N * ((2 * (6 * 5 * 5 + 12 * 5 + 6) + 28) * N + 10 * 5 + 22 + 3) +
      2 * N + 4) + 3) + 17) = x at *
  generalize N * (N * (10 * N + 6 * 5 * 5 + 12 * 5 + 15 + 1) + 6 * 5 + 4) = y at *
  generalize K ^ 12 = c at *
  generalize K ^ 3 = d at *
  omega

/-- One layer step, against any `P ≥ (N + 2)²²⁰`. -/
theorem layerCost_five_le' {N P : ℕ} (h20 : (N + 2) ^ 20 ≤ P) (h12 : (N + 2) ^ 12 ≤ P)
    (h44 : (Valence.domBound 5 N + 1) ^ 44 ≤ P) : Valence.layerCost 5 13 N ≤ 9000 * P := by
  have hin := inputCost_five_le (N := N)
  have hout := outCost_five_le (N := N)
  have hL : Valence.genBound 5 N ≤ (N + 2) ^ 10 := genBound_five_le N
  have hD : Valence.domBound 5 N + 1 ≤ (N + 2) ^ 5 := domBound_five_succ_le N
  have hf : 60 * Valence.genBound 5 N * (Valence.domBound 5 N + 1) ^ 2 ≤ 60 * (N + 2) ^ 20 := by
    have h1 : (Valence.domBound 5 N + 1) ^ 2 ≤ (N + 2) ^ 10 := by
      calc (Valence.domBound 5 N + 1) ^ 2 ≤ ((N + 2) ^ 5) ^ 2 := Nat.pow_le_pow_left hD 2
        _ = (N + 2) ^ 10 := by rw [← pow_mul]
    have h2 : Valence.genBound 5 N * (Valence.domBound 5 N + 1) ^ 2 ≤ (N + 2) ^ 10 * (N + 2) ^ 10 :=
      Nat.mul_le_mul hL h1
    rw [show (N + 2) ^ 10 * (N + 2) ^ 10 = (N + 2) ^ 20 by rw [← pow_add]] at h2
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ h2
  unfold Valence.layerCost Valence.stepCost
  rw [show 3 * 13 + 5 = 44 from rfl]
  generalize Valence.inputCost 5 N (Valence.genBound 5 N) = A at *
  generalize Valence.outCost 5 N (Valence.domBound 5 N * Valence.domBound 5 N) = B at *
  generalize 60 * Valence.genBound 5 N * (Valence.domBound 5 N + 1) ^ 2 = C at *
  generalize (Valence.domBound 5 N + 1) ^ 44 = E at *
  generalize (N + 2) ^ 20 = c at *
  generalize (N + 2) ^ 12 = d at *
  omega

/-- **One layer step costs at most `9000 (N + 2)²²⁰`.** -/
theorem layerCost_five_le (N : ℕ) : Valence.layerCost 5 13 N ≤ 9000 * (N + 2) ^ 220 :=
  layerCost_five_le' (pow_le_pow_of_two_le (by omega) (by norm_num))
    (pow_le_pow_of_two_le (by omega) (by norm_num))
    (calc (Valence.domBound 5 N + 1) ^ 44 ≤ ((N + 2) ^ 5) ^ 44 :=
          Nat.pow_le_pow_left (domBound_five_succ_le N) 44
      _ = (N + 2) ^ 220 := by rw [← pow_mul])

/-- The edge test, against `P = (2n + 2)²²⁰` and any `Q ≥ (2n + 2) P`. -/
theorem edgeCost_five_le' {n P Q : ℕ} (hP : P = (2 * n + 2) ^ 220) (hQ : (2 * n + 2) * P ≤ Q) :
    Valence.edgeCost 5 13 n ≤ 9300 * Q := by
  have hK2 : 2 ≤ 2 * n + 2 := by omega
  have hl : Valence.layerCost 5 13 (2 * n) ≤ 9000 * P := by
    rw [hP]
    exact layerCost_five_le (2 * n)
  have hlev : Valence.levelsCost 5 (2 * n) 4 ≤ 100 * (2 * n + 2) ^ 3 :=
    levelsCost_five_le (by omega) le_rfl
  have hgb : Valence.genBound 5 (2 * n) ≤ (2 * n + 2) ^ 10 := genBound_five_le (2 * n)
  have hKP : (2 * n + 2) ^ 10 ≤ P := by rw [hP]; exact pow_le_pow_of_two_le hK2 (by norm_num)
  have h1P : 1 ≤ P := by rw [hP]; exact Nat.one_le_pow _ _ (by omega)
  have p3 : (2 * n + 2) ^ 3 ≤ (2 * n + 2) ^ 10 := pow_le_pow_of_two_le hK2 (by norm_num)
  have hmul : 2 * n * (Valence.layerCost 5 13 (2 * n) + 1) ≤ 9000 * ((2 * n + 2) * P) +
      (2 * n + 2) := by
    have := Nat.mul_le_mul (show 2 * n ≤ 2 * n + 2 by omega)
      (show Valence.layerCost 5 13 (2 * n) + 1 ≤ 9000 * P + 1 by omega)
    have e : (2 * n + 2) * (9000 * P + 1) = 9000 * ((2 * n + 2) * P) + (2 * n + 2) := by ring
    omega
  have hKKP : 2 * n + 2 ≤ (2 * n + 2) * P := Nat.le_mul_of_pos_right _ h1P
  have hPKP : P ≤ (2 * n + 2) * P := Nat.le_mul_of_pos_left _ (by omega)
  unfold Valence.edgeCost
  generalize 2 * n * (Valence.layerCost 5 13 (2 * n) + 1) = A at *
  generalize (2 * n + 2) * P = B at *
  generalize (2 * n + 2) ^ 10 = c at *
  generalize (2 * n + 2) ^ 3 = d at *
  omega

/-- **The edge test costs at most `9300 (2n + 2)²²¹`.** -/
theorem edgeCost_five_le (n : ℕ) : Valence.edgeCost 5 13 n ≤ 9300 * (2 * n + 2) ^ 221 :=
  edgeCost_five_le' rfl (le_of_eq (by rw [Nat.mul_comm]; exact (pow_succ _ 220).symm))

/-- The algorithm, against `Q = (2n + 2)²²¹` and any `R ≥ (2n + 2) Q`. -/
theorem mainCost_five_le' {n Q R : ℕ} (hQ : Q = (2 * n + 2) ^ 221) (hR : (2 * n + 2) * Q ≤ R) :
    Valence.mainCost 5 13 n ≤ 28000 * R := by
  have he : Valence.edgeCost 5 13 n ≤ 9300 * Q := by
    rw [hQ]
    exact edgeCost_five_le n
  have h1Q : 1 ≤ Q := by rw [hQ]; exact Nat.one_le_pow _ _ (by omega)
  have hmul : 5 * n * (Valence.edgeCost 5 13 n + 4) ≤ 27900 * ((2 * n + 2) * Q) +
      12 * (2 * n + 2) := by
    have := Nat.mul_le_mul (show 5 * n ≤ 3 * (2 * n + 2) by omega)
      (show Valence.edgeCost 5 13 n + 4 ≤ 9300 * Q + 4 by omega)
    have e : 3 * (2 * n + 2) * (9300 * Q + 4) = 27900 * ((2 * n + 2) * Q) + 12 * (2 * n + 2) := by
      ring
    omega
  have hKKQ : 2 * n + 2 ≤ (2 * n + 2) * Q := Nat.le_mul_of_pos_right _ h1Q
  unfold Valence.mainCost
  generalize 5 * n * (Valence.edgeCost 5 13 n + 4) = A at *
  generalize (2 * n + 2) * Q = B at *
  omega

/-- **The algorithm costs at most `28000 (2n + 2)²²²`.** -/
theorem mainCost_five_le (n : ℕ) : Valence.mainCost 5 13 n ≤ 28000 * (2 * n + 2) ^ 222 :=
  mainCost_five_le' rfl (le_of_eq (by rw [Nat.mul_comm]; exact (pow_succ _ 221).symm))

/-- **The checked entry costs at most `28600 (2n + 2)²²²` on every input.** -/
theorem checkedCost5_le (n : ℕ) : checkedCost5 n ≤ 28600 * (2 * n + 2) ^ 222 := by
  have hK2 : 2 ≤ 2 * n + 2 := by omega
  have hm := mainCost_five_le n
  have hv : Valence.validCost 5 n ≤ 170 * (2 * n + 2) := by
    unfold Valence.validCost Valence.cN
    omega
  have hc : Valence.connCost 5 n ≤ 106 * (2 * n + 2) ^ 3 := by
    have := levelsCost_five_le (N := n) (k := 1) (K := 2 * n + 2) (by omega) (by norm_num)
    have : 6 * n + 6 ≤ 6 * (2 * n + 2) ^ 3 := by
      have := le_pow_of_two_le hK2 (show 1 ≤ 3 by norm_num)
      omega
    unfold Valence.connCost
    omega
  have p3 : (2 * n + 2) ^ 3 ≤ (2 * n + 2) ^ 222 := pow_le_pow_of_two_le hK2 (by norm_num)
  have p1 : 2 * n + 2 ≤ (2 * n + 2) ^ 222 := le_pow_of_two_le hK2 (by norm_num)
  unfold checkedCost5
  generalize (2 * n + 2) ^ 222 = R at *
  generalize (2 * n + 2) ^ 3 = c at *
  omega

end ClosedForm

/-! ### The concrete theorems -/

/-- **Isomorphism of connected graphs of maximum degree five in polynomial time.** The checked
entry with the Schreier–Sims backend substituted, run inside `luksSolver`, with no assumed
oracle: on every input `(n, X, Y)` the result is `none` exactly when `X` and `Y` are not valid
connected graph data of maximum degree at most five on `n` points (connected in the sense of
`Conn`, which holds vacuously for `n = 0`), and otherwise a correct answer; the cost is at most
`28600 (2n + 2)²²²`. -/
theorem gi5_checked (n : ℕ) (X Y : GraphData) :
    ∃ (r : Option (Option (Array ℕ))) (tr : Trace Signature.empty),
      Runs Ctx.empty.O (luksSolver.proc Ty.denote)
        ((Graph.gi5Checked Ty.unit Ty.denote (n, X, Y)).subst ssImpl) r tr ∧
      Trace.localCost tr ≤ 28600 * (2 * n + 2) ^ 222 ∧
      (r = none ↔ ¬ GIValid5 n X Y) ∧ ∀ res, r = some res → GIAnswer n X Y res := by
  obtain ⟨r, ⟨tr, hr, hc, hpre⟩, hnone, hsome⟩ := RunsWithin.gi5Checked n X Y
  obtain ⟨tr', hr', hc'⟩ := Runs.subst ssImpl_implements hr hpre
  refine ⟨r, tr', hr', ?_, hnone, hsome⟩
  rw [Trace.cost_empty] at hc'
  exact hc'.trans (hc.trans (checkedCost5_le n))

/-- **The statement for simple graphs given as data.** For valid data of maximum degree five
whose simple graphs are connected, the checked entry returns `some none` exactly when the
simple graphs are not isomorphic, and `some (some arr)` only when `arr` lists the `n` values of
an isomorphism of the simple graphs. -/
theorem gi5_simpleGraph {n : ℕ} {X Y : GraphData} (hX : X.ValidD 5 n) (hY : Y.ValidD 5 n)
    (hcX : (X.toSimpleGraph n).Connected) (hcY : (Y.toSimpleGraph n).Connected) :
    ∃ (res : Option (Array ℕ)) (tr : Trace Signature.empty),
      Runs Ctx.empty.O (luksSolver.proc Ty.denote)
        ((Graph.gi5Checked Ty.unit Ty.denote (n, X, Y)).subst ssImpl) (some res) tr ∧
      Trace.localCost tr ≤ 28600 * (2 * n + 2) ^ 222 ∧
      (res = none ↔ IsEmpty (X.toSimpleGraph n ≃g Y.toSimpleGraph n)) ∧
      ∀ arr, res = some arr → arr.size = n ∧ ∃ e : X.toSimpleGraph n ≃g Y.toSimpleGraph n,
        ∀ v : Fin n, get arr v = e v := by
  have hn : 0 < n := Fin.pos_iff_nonempty.2 hcX.nonempty
  obtain ⟨r, tr, hr, hc, hnone, hsome⟩ := gi5_checked n X Y
  have hvalid : GIValid5 n X Y :=
    ⟨hX, hY, (conn_iff_connected hX hn).2 hcX, (conn_iff_connected hY hn).2 hcY⟩
  rcases r with _ | res
  · exact absurd (hnone.1 rfl) (not_not.2 hvalid)
  obtain ⟨h₁, h₂⟩ := hsome res rfl
  refine ⟨res, tr, hr, hc, ?_, fun arr harr => ?_⟩
  · rw [h₁, ← nonempty_iso_iff hX hY, not_nonempty_iff]
  · obtain ⟨hs, φ, hφ, hv⟩ := h₂ arr harr
    exact ⟨hs, isoOfIsIso hX hY hφ, fun v => by rw [hv v v.2, act_of_lt _ v.2]; rfl⟩

/-- **Isomorphism of connected simple graphs of maximum degree five in polynomial time.** For
connected simple graphs `G` and `H` on `Fin n` with every degree at most five, the checked
entry on their adjacency lists returns `some none` exactly when `G` and `H` are not isomorphic,
and `some (some arr)` only when `arr` lists the `n` values of an isomorphism `G ≃g H`; the cost
is at most `28600 (2n + 2)²²²`. -/
theorem gi5_simpleGraph' {n : ℕ} {G H : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    [DecidableRel H.Adj] (hdG : ∀ v, G.degree v ≤ 5) (hdH : ∀ v, H.degree v ≤ 5)
    (hcG : G.Connected) (hcH : H.Connected) :
    ∃ (res : Option (Array ℕ)) (tr : Trace Signature.empty),
      Runs Ctx.empty.O (luksSolver.proc Ty.denote)
        ((Graph.gi5Checked Ty.unit Ty.denote
          (n, GraphData.ofSimpleGraph G, GraphData.ofSimpleGraph H)).subst ssImpl) (some res) tr ∧
      Trace.localCost tr ≤ 28600 * (2 * n + 2) ^ 222 ∧
      (res = none ↔ IsEmpty (G ≃g H)) ∧
      ∀ arr, res = some arr → arr.size = n ∧ ∃ e : G ≃g H, ∀ v : Fin n, get arr v = e v := by
  have h := gi5_simpleGraph (valid_ofSimpleGraph hdG) (valid_ofSimpleGraph hdH)
    (by rwa [toSimpleGraph_ofSimpleGraph]) (by rwa [toSimpleGraph_ofSimpleGraph])
  rw [toSimpleGraph_ofSimpleGraph, toSimpleGraph_ofSimpleGraph] at h
  exact h

end GraphIso.Graph
