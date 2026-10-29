module

public import GraphIso.Graph.All

/-!
# Isomorphism of all graphs of maximum degree three with the Schreier–Sims backend

`gi3AllChecked D` takes `(n, X, Y)`, checks that `X` and `Y` are valid graph data on `n` points
of maximum degree at most three, connected or not, and then runs `allProg`. It is well-formed
(`gi3AllChecked_wf`).

* `RunsWithin.gi3AllChecked`: against the Schreier–Sims context, on **every** input, the
  result is `none` exactly when the input is invalid (`GIValidAll`), and otherwise a correct
  answer (`GIAnswer`), at cost at most `allCheckedCost n`.
* `allCheckedCost_le`: **`allCheckedCost n ≤ 5100 (2n + 1)²⁸`**.
* **`gi3_all_checked`**: the same for the closed program after substituting the Schreier–Sims
  implementations, run inside `luksSolver`, with no assumed oracle.
* **`gi3_all_simpleGraph'`**: for **any** simple graphs on `Fin n` with every degree at most
  three, given by their adjacency lists (`GraphData.ofSimpleGraph`), the result is `some none`
  exactly when there is no isomorphism, and `some (some arr)` lists the values of an
  isomorphism. `gi3_all_simpleGraph` states the same for valid data through their simple
  graphs (`GraphData.toSimpleGraph`).
-/

@[expose] public section

namespace GraphIso.Graph

open Equiv Cost Programs Sims Luks

/-! ### The checked entry -/

/-- Valid input: graph data of maximum degree three, connected or not. -/
def GIValidAll (n : ℕ) (X Y : GraphData) : Prop := X.Valid n ∧ Y.Valid n

/-- **The checked entry for all graphs of maximum degree three.** -/
def gi3AllChecked (D : Ty) : (var : Ty → Type) → var Ty.giInput →
    Prog (groupSig D) (Solver.Rec D) var (.option Ty.giOutput) := fun _ inp =>
  .bind (.op1 .fst inp) fun n => .bind (.op1 .snd inp) fun XY =>
  .bind (.op1 .fst XY) fun X => .bind (.op1 .snd XY) fun Y =>
  .bind (validGraphProg n X) fun vX => .bind (validGraphProg n Y) fun vY =>
  .bind (.op2 .and vX vY) fun v =>
  .ite v (.bind (allProg n X Y) fun res => .op1 .some res) (.op0 .none)

/-- The cost bound of the checked entry. -/
def allCheckedCost (n : ℕ) : ℕ := 2 * (151 * n + 8) + allCost n + 10

theorem gi3AllChecked_wf {D : Ty} {var₁ var₂ : Ty → Type} (x₁ : var₁ Ty.giInput)
    (x₂ : var₂ Ty.giInput) :
    Prog.Wf true [⟨Ty.giInput, x₁, x₂⟩] (gi3AllChecked D var₁ x₁) (gi3AllChecked D var₂ x₂) := by
  unfold gi3AllChecked
  exact .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (wf_validGraphProg (by simp) (by simp)) fun _ _ =>
    .bind (wf_validGraphProg (by simp) (by simp)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) (.cons (List.Mem.head _) .nil))) fun _ _ =>
    .ite (List.Mem.head _)
      (.bind (wf_allProg (by simp) (by simp) (by simp)) fun _ _ =>
        .prim _ (.cons (List.Mem.head _) .nil))
      (.prim _ .nil)

/-- **The checked entry against the Schreier–Sims context, on every input.** -/
theorem RunsWithin.gi3AllChecked (n : ℕ) (X Y : GraphData) :
    ∃ r, RunsWithin ssCtx (luksBody Ty.unit Ty.denote)
        (Graph.gi3AllChecked Ty.unit Ty.denote (n, X, Y)) r (allCheckedCost n) ∧
      (r = none ↔ ¬ GIValidAll n X Y) ∧ ∀ res, r = some res → GIAnswer n X Y res := by
  have hvX := RunsWithin.validGraphProg (X := ssCtx) (body := luksBody Ty.unit Ty.denote) n X
  have hvY := RunsWithin.validGraphProg (X := ssCtx) (body := luksBody Ty.unit Ty.denote) n Y
  by_cases hv : (validGB n X && validGB n Y) = true
  · rw [Bool.and_eq_true, validGB_iff, validGB_iff] at hv
    obtain ⟨hX, hY⟩ := hv
    obtain ⟨res, hrun, h₁, h₂⟩ := RunsWithin.allProg hX hY
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
          simp [Prim.eval, (validGB_iff (n := n) (G := X)).2 hX,
            (validGB_iff (n := n) (G := Y)).2 hY]) _
        run_step hrun
        exact RunsWithin.prim_le rfl le_rfl
      case hc =>
        simp only [Prim.cost, allCheckedCost]
        omega
    · cases h
      exact ⟨h₁, h₂⟩
  · refine ⟨none, ?_, ⟨fun _ ⟨hX, hY⟩ => hv (by
      rw [Bool.and_eq_true, validGB_iff, validGB_iff]
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
      simp only [Prim.cost, allCheckedCost]
      omega

/-! ### The closed form -/

theorem allCost_eq (n : ℕ) :
    allCost n = 89 * n ^ 4 + 109 * n ^ 3 + 174 * n ^ 2 + 116 * n + 32 +
      16900 * (n * n) * (2 * n + 1) ^ 26 := by
  unfold allCost compsCost compStepCost levelsCost matchCost partnerCost subGCost glueCost
  ring

/-- **The algorithm costs at most `4750 (2n + 1)²⁸`.** -/
theorem allCost_le (n : ℕ) : allCost n ≤ 4750 * (2 * n + 1) ^ 28 := by
  rw [allCost_eq]
  set K := 2 * n + 1 with hK
  have hK1 : 1 ≤ K := by omega
  have hnK : n ≤ K := by omega
  have h4 : 4 * (n * n) ≤ K ^ 2 := by
    rw [hK]
    nlinarith
  have hmain : 16900 * (n * n) * K ^ 26 ≤ 4225 * K ^ 28 := by
    calc 16900 * (n * n) * K ^ 26 = 4225 * (4 * (n * n) * K ^ 26) := by ring
      _ ≤ 4225 * (K ^ 2 * K ^ 26) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h4)
      _ = 4225 * K ^ 28 := by ring
  have p4 : K ^ 4 ≤ K ^ 28 := Nat.pow_le_pow_right hK1 (by omega)
  have hn4 : n ^ 4 ≤ K ^ 4 := Nat.pow_le_pow_left hnK 4
  have hn3 : n ^ 3 ≤ K ^ 4 :=
    (Nat.pow_le_pow_left hnK 3).trans (Nat.pow_le_pow_right hK1 (by omega))
  have hn2 : n ^ 2 ≤ K ^ 4 :=
    (Nat.pow_le_pow_left hnK 2).trans (Nat.pow_le_pow_right hK1 (by omega))
  have hn1 : n ≤ K ^ 4 := by
    have := Nat.pow_le_pow_right hK1 (show 1 ≤ 4 by omega)
    rw [pow_one] at this
    omega
  have h1 : 1 ≤ K ^ 4 := Nat.one_le_pow _ _ hK1
  omega

/-- **The checked entry costs at most `5100 (2n + 1)²⁸`.** -/
theorem allCheckedCost_le (n : ℕ) : allCheckedCost n ≤ 5100 * (2 * n + 1) ^ 28 := by
  have h := allCost_le n
  have hK1 : 1 ≤ 2 * n + 1 := by omega
  have p1 : 2 * n + 1 ≤ (2 * n + 1) ^ 28 := by
    have := Nat.pow_le_pow_right hK1 (show 1 ≤ 28 by omega)
    rwa [pow_one] at this
  unfold allCheckedCost
  omega

/-! ### The concrete theorems -/

/-- **Isomorphism of all graphs of maximum degree three in polynomial time.** The checked
entry with the Schreier–Sims backend substituted, run inside `luksSolver`, with no assumed
oracle: on every input `(n, X, Y)` the result is `none` exactly when `X` or `Y` is not valid
graph data of maximum degree three on `n` points, and otherwise a correct answer; the cost is
at most `5100 (2n + 1)²⁸`. -/
theorem gi3_all_checked (n : ℕ) (X Y : GraphData) :
    ∃ (r : Option (Option (Array ℕ))) (tr : Trace Signature.empty),
      Runs Ctx.empty.O (luksSolver.proc Ty.denote)
        ((Graph.gi3AllChecked Ty.unit Ty.denote (n, X, Y)).subst ssImpl) r tr ∧
      Trace.localCost tr ≤ 5100 * (2 * n + 1) ^ 28 ∧
      (r = none ↔ ¬ GIValidAll n X Y) ∧ ∀ res, r = some res → GIAnswer n X Y res := by
  obtain ⟨r, ⟨tr, hr, hc, hpre⟩, hnone, hsome⟩ := RunsWithin.gi3AllChecked n X Y
  obtain ⟨tr', hr', hc'⟩ := Runs.subst ssImpl_implements hr hpre
  refine ⟨r, tr', hr', ?_, hnone, hsome⟩
  rw [Trace.cost_empty] at hc'
  exact hc'.trans (hc.trans (allCheckedCost_le n))

/-- **The statement for simple graphs given as data.** For valid data of maximum degree three,
connected or not, the checked entry returns `some none` exactly when the simple graphs are not
isomorphic, and `some (some arr)` only when `arr` lists the `n` values of an isomorphism of the
simple graphs. -/
theorem gi3_all_simpleGraph {n : ℕ} {X Y : GraphData} (hX : X.Valid n) (hY : Y.Valid n) :
    ∃ (res : Option (Array ℕ)) (tr : Trace Signature.empty),
      Runs Ctx.empty.O (luksSolver.proc Ty.denote)
        ((Graph.gi3AllChecked Ty.unit Ty.denote (n, X, Y)).subst ssImpl) (some res) tr ∧
      Trace.localCost tr ≤ 5100 * (2 * n + 1) ^ 28 ∧
      (res = none ↔ IsEmpty (X.toSimpleGraph n ≃g Y.toSimpleGraph n)) ∧
      ∀ arr, res = some arr → arr.size = n ∧ ∃ e : X.toSimpleGraph n ≃g Y.toSimpleGraph n,
        ∀ v : Fin n, get arr v = e v := by
  obtain ⟨r, tr, hr, hc, hnone, hsome⟩ := gi3_all_checked n X Y
  rcases r with _ | res
  · exact absurd (hnone.1 rfl) (not_not.2 ⟨hX, hY⟩)
  obtain ⟨h₁, h₂⟩ := hsome res rfl
  refine ⟨res, tr, hr, hc, ?_, fun arr harr => ?_⟩
  · rw [h₁, ← nonempty_iso_iff hX hY, not_nonempty_iff]
  · obtain ⟨hs, φ, hφ, hv⟩ := h₂ arr harr
    exact ⟨hs, isoOfIsIso hX hY hφ, fun v => by rw [hv v v.2, act_of_lt _ v.2]; rfl⟩

/-- **Isomorphism of simple graphs of maximum degree three in polynomial time.** For any simple
graphs `G` and `H` on `Fin n` with every degree at most three, connected or not, the checked
entry on their adjacency lists returns `some none` exactly when `G` and `H` are not
isomorphic, and `some (some arr)` only when `arr` lists the `n` values of an isomorphism
`G ≃g H`; the cost is at most `5100 (2n + 1)²⁸`. -/
theorem gi3_all_simpleGraph' {n : ℕ} {G H : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    [DecidableRel H.Adj] (hdG : ∀ v, G.degree v ≤ 3) (hdH : ∀ v, H.degree v ≤ 3) :
    ∃ (res : Option (Array ℕ)) (tr : Trace Signature.empty),
      Runs Ctx.empty.O (luksSolver.proc Ty.denote)
        ((Graph.gi3AllChecked Ty.unit Ty.denote
          (n, GraphData.ofSimpleGraph G, GraphData.ofSimpleGraph H)).subst ssImpl) (some res) tr ∧
      Trace.localCost tr ≤ 5100 * (2 * n + 1) ^ 28 ∧
      (res = none ↔ IsEmpty (G ≃g H)) ∧
      ∀ arr, res = some arr → arr.size = n ∧ ∃ e : G ≃g H, ∀ v : Fin n, get arr v = e v := by
  have h := gi3_all_simpleGraph (valid_ofSimpleGraph hdG) (valid_ofSimpleGraph hdH)
  rw [toSimpleGraph_ofSimpleGraph, toSimpleGraph_ofSimpleGraph] at h
  exact h

end GraphIso.Graph
