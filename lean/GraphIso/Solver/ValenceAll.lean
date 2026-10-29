module

public import GraphIso.Valence.All
public import GraphIso.Solver.GraphAll

/-!
# Isomorphism of all graphs of maximum degree `Δ` with the Schreier–Sims backend

`giBoundedAllChecked Δ D` takes `(n, X, Y)`, checks that `X` and `Y` are valid graph data on
`n` points of maximum degree at most `Δ`, connected or not, and then runs `Valence.allProg Δ`.
It is well-formed (`giBoundedAllChecked_wf`).

* `RunsWithin.giBoundedAllChecked`: for `Δ ≥ 2`, a constant `c ≥ 1` with `LayerPrim Δ c` and a
  bound `B` on the connected test on at most `n` points, against the Schreier–Sims context, on
  **every** input, the result is `none` exactly when the input is invalid (`GIValidAllB Δ`),
  and otherwise a correct answer (`GIAnswer`), at cost at most `allCheckedCostB Δ B n`.
* `gi5AllChecked` is the entry for `Δ = 5`; `RunsWithin.gi5AllChecked` is the case `c = 13`,
  `B = mainBound n`, at cost at most `allCheckedCost5 n`.
* `allCheckedCost5_le`: **`allCheckedCost5 n ≤ 7200 (2n + 2)²²⁴`**: at most `n²` candidate
  pairs of components, each bounded by the connected test's `28000 (2n + 2)²²²`.
* **`gi5_all_checked`**: the same for the closed program after substituting the Schreier–Sims
  implementations, run inside `luksSolver`, with no assumed oracle.
* **`gi5_all_simpleGraph'`**: for **any** simple graphs on `Fin n` with every degree at most
  five, given by their adjacency lists, the result is `some none` exactly when there is no
  isomorphism, and `some (some arr)` lists the values of an isomorphism. `gi5_all_simpleGraph`
  states the same for valid data through their simple graphs.
-/

@[expose] public section

namespace GraphIso.Graph

open Equiv Cost Programs Sims Luks

/-! ### The checked entry -/

/-- Valid input: graph data of maximum degree `Δ`, connected or not. -/
def GIValidAllB (Δ n : ℕ) (X Y : GraphData) : Prop := X.ValidD Δ n ∧ Y.ValidD Δ n

/-- **The checked entry for all graphs of maximum degree `Δ`.** -/
def giBoundedAllChecked (Δ : ℕ) (D : Ty) : (var : Ty → Type) → var Ty.giInput →
    Prog (groupSig D) (Solver.Rec D) var (.option Ty.giOutput) := fun _ inp =>
  .bind (.op1 .fst inp) fun n => .bind (.op1 .snd inp) fun XY =>
  .bind (.op1 .fst XY) fun X => .bind (.op1 .snd XY) fun Y =>
  .bind (Valence.validGraphProg Δ n X) fun vX => .bind (Valence.validGraphProg Δ n Y) fun vY =>
  .bind (.op2 .and vX vY) fun v =>
  .ite v (.bind (Valence.allProg Δ n X Y) fun res => .op1 .some res) (.op0 .none)

/-- The cost bound of the checked entry, for a bound `B` on the connected test. -/
def allCheckedCostB (Δ B n : ℕ) : ℕ := 2 * Valence.validCost Δ n + Valence.allCost Δ B n + 10

theorem giBoundedAllChecked_wf (Δ : ℕ) {D : Ty} {var₁ var₂ : Ty → Type} (x₁ : var₁ Ty.giInput)
    (x₂ : var₂ Ty.giInput) :
    Prog.Wf true [⟨Ty.giInput, x₁, x₂⟩] (giBoundedAllChecked Δ D var₁ x₁)
      (giBoundedAllChecked Δ D var₂ x₂) := by
  unfold giBoundedAllChecked
  exact .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (Valence.wf_validGraphProg Δ (by simp) (by simp)) fun _ _ =>
    .bind (Valence.wf_validGraphProg Δ (by simp) (by simp)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) (.cons (List.Mem.head _) .nil))) fun _ _ =>
    .ite (List.Mem.head _)
      (.bind (Valence.wf_allProg Δ (by simp) (by simp) (by simp)) fun _ _ =>
        .prim _ (.cons (List.Mem.head _) .nil))
      (.prim _ .nil)

/-- **The checked entry against the Schreier–Sims context, on every input**, for `Δ ≥ 2`, a
constant `c ≥ 1` with `LayerPrim Δ c`, and a bound `B` on the connected test on at most `n`
points. -/
theorem RunsWithin.giBoundedAllChecked {Δ c B : ℕ} (hΔ₂ : 2 ≤ Δ) (hc : Valence.LayerPrim Δ c)
    (hc1 : 1 ≤ c) (n : ℕ) (hBm : ∀ k ≤ n, Valence.mainCost Δ c k ≤ B) (X Y : GraphData) :
    ∃ r, RunsWithin ssCtx (luksBody Ty.unit Ty.denote)
        (Graph.giBoundedAllChecked Δ Ty.unit Ty.denote (n, X, Y)) r (allCheckedCostB Δ B n) ∧
      (r = none ↔ ¬ GIValidAllB Δ n X Y) ∧ ∀ res, r = some res → GIAnswer n X Y res := by
  have hvX := Valence.RunsWithin.validGraphProg (X := ssCtx) (body := luksBody Ty.unit Ty.denote)
    Δ n X
  have hvY := Valence.RunsWithin.validGraphProg (X := ssCtx) (body := luksBody Ty.unit Ty.denote)
    Δ n Y
  by_cases hv : (Valence.validGB Δ n X && Valence.validGB Δ n Y) = true
  · rw [Bool.and_eq_true, Valence.validGB_iff, Valence.validGB_iff] at hv
    obtain ⟨hX, hY⟩ := hv
    obtain ⟨res, hrun, h₁, h₂⟩ := Valence.RunsWithin.allProg hX hY hΔ₂ hc hc1 hBm
    refine ⟨some res, ?_, ⟨fun h => absurd h (by simp), fun h => absurd ⟨hX, hY⟩ h⟩,
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
        run_step hrun
        exact RunsWithin.prim_le rfl le_rfl
      case hc =>
        simp only [Prim.cost, allCheckedCostB]
        omega
    · cases h
      exact ⟨h₁, h₂⟩
  · refine ⟨none, ?_, ⟨fun _ ⟨hX, hY⟩ => hv (by
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
      simp only [Prim.cost, allCheckedCostB]
      omega

/-! ### Maximum degree five -/

/-- Valid input: graph data of maximum degree five, connected or not. -/
def GIValidAll5 (n : ℕ) (X Y : GraphData) : Prop := X.ValidD 5 n ∧ Y.ValidD 5 n

/-- **The checked entry for all graphs of maximum degree five.** -/
def gi5AllChecked (D : Ty) : (var : Ty → Type) → var Ty.giInput →
    Prog (groupSig D) (Solver.Rec D) var (.option Ty.giOutput) := fun _ inp =>
  .bind (.op1 .fst inp) fun n => .bind (.op1 .snd inp) fun XY =>
  .bind (.op1 .fst XY) fun X => .bind (.op1 .snd XY) fun Y =>
  .bind (Valence.validGraphProg 5 n X) fun vX => .bind (Valence.validGraphProg 5 n Y) fun vY =>
  .bind (.op2 .and vX vY) fun v =>
  .ite v (.bind (Valence.allProg 5 n X Y) fun res => .op1 .some res) (.op0 .none)

/-- The cost bound of the checked entry. -/
def allCheckedCost5 (n : ℕ) : ℕ :=
  2 * Valence.validCost 5 n + Valence.allCost 5 (Valence.mainBound n) n + 10

theorem gi5AllChecked_wf {D : Ty} {var₁ var₂ : Ty → Type} (x₁ : var₁ Ty.giInput)
    (x₂ : var₂ Ty.giInput) :
    Prog.Wf true [⟨Ty.giInput, x₁, x₂⟩] (gi5AllChecked D var₁ x₁) (gi5AllChecked D var₂ x₂) :=
  giBoundedAllChecked_wf 5 x₁ x₂

/-- **The checked entry against the Schreier–Sims context, on every input**: `LayerPrim 5 13`
and the connected test's bound `mainBound n`. -/
theorem RunsWithin.gi5AllChecked (n : ℕ) (X Y : GraphData) :
    ∃ r, RunsWithin ssCtx (luksBody Ty.unit Ty.denote)
        (Graph.gi5AllChecked Ty.unit Ty.denote (n, X, Y)) r (allCheckedCost5 n) ∧
      (r = none ↔ ¬ GIValidAll5 n X Y) ∧ ∀ res, r = some res → GIAnswer n X Y res :=
  RunsWithin.giBoundedAllChecked (by norm_num) (Valence.layerPrim_solvable le_rfl) (by norm_num)
    n (fun _ hk => Valence.mainCost_le_mainBound hk) X Y

/-! ### The closed form -/

section ClosedForm

/-- The algorithm, against `P = (2n + 2)²²²` and any `R ≥ (2n + 2)² P` with `R ≥ (2n + 2)⁴`. -/
theorem allCost_five_le' {n P R : ℕ} (hP : P = (2 * n + 2) ^ 222)
    (hR : (2 * n + 2) ^ 2 * P ≤ R) (hR4 : (2 * n + 2) ^ 4 ≤ R) :
    Valence.allCost 5 (Valence.mainBound n) n ≤ 7100 * R := by
  have hmb : Valence.mainBound n = 28000 * P := by
    unfold Valence.mainBound
    rw [hP]
  -- the expanded cost
  have e : Valence.allCost 5 (Valence.mainBound n) n = 2 * Valence.compsCost 5 n +
      n * Valence.subGCost 5 n + n * n * (Valence.subGCost 5 n + 2 * n + 17) +
      28000 * (n * n * P) + 17 * n + glueCost n + 16 := by
    unfold Valence.allCost Valence.matchCost Valence.partnerCost
    rw [hmb]
    ring
  have eC : Valence.compsCost 5 n = 43 * n ^ 4 + 15 * n ^ 3 + 66 * n ^ 2 + 42 * n + 4 := by
    unfold Valence.compsCost Valence.compStepCost Valence.levelsCost
    ring
  have eS : Valence.subGCost 5 n = 45 * n ^ 2 + 42 * n + 4 := by
    unfold Valence.subGCost
    ring
  have eG : glueCost n = 22 * n ^ 3 + 17 * n ^ 2 + 11 * n + 8 := by
    unfold glueCost
    ring
  have e1 : n * (45 * n ^ 2 + 42 * n + 4) = 45 * n ^ 3 + 42 * n ^ 2 + 4 * n := by ring
  have e2 : n * n * (45 * n ^ 2 + 42 * n + 4 + 2 * n + 17) = 45 * n ^ 4 + 44 * n ^ 3 + 21 * n ^ 2 :=
    by ring
  have e4 : (2 * n + 2) ^ 4 = 16 * n ^ 4 + 64 * n ^ 3 + 96 * n ^ 2 + 64 * n + 16 := by ring
  -- the connected tests
  have hsq : 4 * (n * n) ≤ (2 * n + 2) ^ 2 := by
    rw [show (2 * n + 2) ^ 2 = 4 * (n * n) + 8 * n + 4 by ring]
    omega
  have hB : 4 * (n * n * P) ≤ R :=
    calc 4 * (n * n * P) = 4 * (n * n) * P := by ring
      _ ≤ (2 * n + 2) ^ 2 * P := Nat.mul_le_mul_right _ hsq
      _ ≤ R := hR
  rw [e, eC, eS, eG, e1, e2]
  rw [e4] at hR4
  clear e eC eS eG e1 e2 e4 hmb hP hR hsq
  generalize n * n * P = C at *
  generalize n ^ 4 = a at *
  generalize n ^ 3 = b at *
  generalize n ^ 2 = c at *
  omega

/-- **The algorithm costs at most `7100 (2n + 2)²²⁴`.** -/
theorem allCost_five_le (n : ℕ) :
    Valence.allCost 5 (Valence.mainBound n) n ≤ 7100 * (2 * n + 2) ^ 224 :=
  allCost_five_le' rfl (le_of_eq (by rw [← pow_add]))
    (pow_le_pow_of_two_le (by omega) (by norm_num))

/-- **The checked entry costs at most `7200 (2n + 2)²²⁴`.** -/
theorem allCheckedCost5_le (n : ℕ) : allCheckedCost5 n ≤ 7200 * (2 * n + 2) ^ 224 := by
  have h := allCost_five_le n
  have p4 : (2 * n + 2) ^ 4 ≤ (2 * n + 2) ^ 224 := pow_le_pow_of_two_le (by omega) (by norm_num)
  have e4 : (2 * n + 2) ^ 4 = 16 * n ^ 4 + 64 * n ^ 3 + 96 * n ^ 2 + 64 * n + 16 := by ring
  have hv : Valence.validCost 5 n ≤ 170 * (2 * n + 2) := by
    unfold Valence.validCost Valence.cN
    omega
  unfold allCheckedCost5
  rw [e4] at p4
  clear e4
  generalize (2 * n + 2) ^ 224 = R at *
  generalize n ^ 4 = a at *
  generalize n ^ 3 = b at *
  generalize n ^ 2 = c at *
  omega

end ClosedForm

/-! ### The concrete theorems -/

/-- **Isomorphism of all graphs of maximum degree five in polynomial time.** The checked entry
with the Schreier–Sims backend substituted, run inside `luksSolver`, with no assumed oracle: on
every input `(n, X, Y)` the result is `none` exactly when `X` or `Y` is not valid graph data of
maximum degree at most five on `n` points, and otherwise a correct answer; the cost is at most
`7200 (2n + 2)²²⁴`. -/
theorem gi5_all_checked (n : ℕ) (X Y : GraphData) :
    ∃ (r : Option (Option (Array ℕ))) (tr : Trace Signature.empty),
      Runs Ctx.empty.O (luksSolver.proc Ty.denote)
        ((Graph.gi5AllChecked Ty.unit Ty.denote (n, X, Y)).subst ssImpl) r tr ∧
      Trace.localCost tr ≤ 7200 * (2 * n + 2) ^ 224 ∧
      (r = none ↔ ¬ GIValidAll5 n X Y) ∧ ∀ res, r = some res → GIAnswer n X Y res := by
  obtain ⟨r, ⟨tr, hr, hc, hpre⟩, hnone, hsome⟩ := RunsWithin.gi5AllChecked n X Y
  obtain ⟨tr', hr', hc'⟩ := Runs.subst ssImpl_implements hr hpre
  refine ⟨r, tr', hr', ?_, hnone, hsome⟩
  rw [Trace.cost_empty] at hc'
  exact hc'.trans (hc.trans (allCheckedCost5_le n))

/-- **The statement for simple graphs given as data.** For valid data of maximum degree five,
connected or not, the checked entry returns `some none` exactly when the simple graphs are not
isomorphic, and `some (some arr)` only when `arr` lists the `n` values of an isomorphism of the
simple graphs. -/
theorem gi5_all_simpleGraph {n : ℕ} {X Y : GraphData} (hX : X.ValidD 5 n) (hY : Y.ValidD 5 n) :
    ∃ (res : Option (Array ℕ)) (tr : Trace Signature.empty),
      Runs Ctx.empty.O (luksSolver.proc Ty.denote)
        ((Graph.gi5AllChecked Ty.unit Ty.denote (n, X, Y)).subst ssImpl) (some res) tr ∧
      Trace.localCost tr ≤ 7200 * (2 * n + 2) ^ 224 ∧
      (res = none ↔ IsEmpty (X.toSimpleGraph n ≃g Y.toSimpleGraph n)) ∧
      ∀ arr, res = some arr → arr.size = n ∧ ∃ e : X.toSimpleGraph n ≃g Y.toSimpleGraph n,
        ∀ v : Fin n, get arr v = e v := by
  obtain ⟨r, tr, hr, hc, hnone, hsome⟩ := gi5_all_checked n X Y
  rcases r with _ | res
  · exact absurd (hnone.1 rfl) (not_not.2 ⟨hX, hY⟩)
  obtain ⟨h₁, h₂⟩ := hsome res rfl
  refine ⟨res, tr, hr, hc, ?_, fun arr harr => ?_⟩
  · rw [h₁, ← nonempty_iso_iff hX hY, not_nonempty_iff]
  · obtain ⟨hs, φ, hφ, hv⟩ := h₂ arr harr
    exact ⟨hs, isoOfIsIso hX hY hφ, fun v => by rw [hv v v.2, act_of_lt _ v.2]; rfl⟩

/-- **Isomorphism of all simple graphs of maximum degree five in polynomial time.** For any
simple graphs `G` and `H` on `Fin n` with every degree at most five, connected or not, the
checked entry on their adjacency lists returns `some none` exactly when `G` and `H` are not
isomorphic, and `some (some arr)` only when `arr` lists the `n` values of an isomorphism
`G ≃g H`; the cost is at most `7200 (2n + 2)²²⁴`. -/
theorem gi5_all_simpleGraph' {n : ℕ} {G H : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    [DecidableRel H.Adj] (hdG : ∀ v, G.degree v ≤ 5) (hdH : ∀ v, H.degree v ≤ 5) :
    ∃ (res : Option (Array ℕ)) (tr : Trace Signature.empty),
      Runs Ctx.empty.O (luksSolver.proc Ty.denote)
        ((Graph.gi5AllChecked Ty.unit Ty.denote
          (n, GraphData.ofSimpleGraph G, GraphData.ofSimpleGraph H)).subst ssImpl) (some res) tr ∧
      Trace.localCost tr ≤ 7200 * (2 * n + 2) ^ 224 ∧
      (res = none ↔ IsEmpty (G ≃g H)) ∧
      ∀ arr, res = some arr → arr.size = n ∧ ∃ e : G ≃g H, ∀ v : Fin n, get arr v = e v := by
  have h := gi5_all_simpleGraph (valid_ofSimpleGraph hdG) (valid_ofSimpleGraph hdH)
  rw [toSimpleGraph_ofSimpleGraph, toSimpleGraph_ofSimpleGraph] at h
  exact h

end GraphIso.Graph
