module

public import GraphIso.Graph.SimpleGraph

/-!
# Isomorphism of graphs of maximum degree three with the Schreier–Sims backend

`gi3Checked D` takes `(n, X, Y)`, checks that `X` and `Y` are valid graph data on `n` points of
maximum degree at most three and connected, and then runs `mainProg`. It is well-formed
(`gi3Checked_wf`).

* `RunsWithin.gi3Checked`: against the Schreier–Sims context, on **every** input, the result is
  `none` exactly when the input is invalid, and otherwise a correct answer (`GIAnswer`), at
  cost at most `checkedCost n`. Connectivity is `Conn`, which holds vacuously on no points:
  the empty input `(0, #[], #[])` is valid, with answer `some #[]`, although mathlib's graphs
  on `Fin 0` are not connected. For `n > 0`, `Conn` is `SimpleGraph.Connected`.
* `checkedCost_le`: **`checkedCost n ≤ 17500 (2n + 1)²⁶`**.
* **`gi3_checked`**: the same for the closed program after substituting the Schreier–Sims
  implementations, run inside `luksSolver`, with no assumed oracle.
* `gi3_simpleGraph'`: the statement for mathlib's simple graphs: for connected simple graphs on
  `Fin n` with every degree at most three, given by their adjacency lists
  (`GraphData.ofSimpleGraph`), the result is `some none` exactly when there is no isomorphism,
  and `some (some arr)` lists the values of an isomorphism. `gi3_simpleGraph` states the same
  for valid data through their simple graphs (`GraphData.toSimpleGraph`).
-/

@[expose] public section

namespace GraphIso.Graph

open Equiv Cost Programs Sims Luks

/-! ### The checked entry -/

/-- Valid connected input. On no points it holds for empty data, as `Conn 0` holds vacuously.
-/
def GIValid (n : ℕ) (X Y : GraphData) : Prop :=
  X.Valid n ∧ Y.Valid n ∧ Conn n X ∧ Conn n Y

/-- A correct answer: `none` exactly when there is no isomorphism, and otherwise the `n` values
of an isomorphism. -/
def GIAnswer (n : ℕ) (X Y : GraphData) (res : Option (Array ℕ)) : Prop :=
  (res = none ↔ ¬ ∃ φ, IsIso n X Y φ) ∧
    ∀ arr, res = some arr → arr.size = n ∧
      ∃ φ : Perm (Fin n), IsIso n X Y φ ∧ ∀ v < n, get arr v = act φ v

/-- **The checked entry.** -/
def gi3Checked (D : Ty) : (var : Ty → Type) → var Ty.giInput →
    Prog (groupSig D) (Solver.Rec D) var (.option Ty.giOutput) := fun _ inp =>
  .bind (.op1 .fst inp) fun n => .bind (.op1 .snd inp) fun XY =>
  .bind (.op1 .fst XY) fun X => .bind (.op1 .snd XY) fun Y =>
  .bind (validGraphProg n X) fun vX => .bind (validGraphProg n Y) fun vY =>
  .bind (.op2 .and vX vY) fun v =>
  .ite v
    (.bind (connProg n X) fun cX => .bind (connProg n Y) fun cY => .bind (.op2 .and cX cY)
      fun c => .ite c (.bind (mainProg n X Y) fun res => .op1 .some res) (.op0 .none))
    (.op0 .none)

/-- The cost bound of the checked entry. -/
def checkedCost (n : ℕ) : ℕ := 2 * (151 * n + 8) + 2 * connCost n + mainCost n + 12

theorem gi3Checked_wf {D : Ty} {var₁ var₂ : Ty → Type} (x₁ : var₁ Ty.giInput)
    (x₂ : var₂ Ty.giInput) :
    Prog.Wf true [⟨Ty.giInput, x₁, x₂⟩] (gi3Checked D var₁ x₁) (gi3Checked D var₂ x₂) := by
  unfold gi3Checked
  exact .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun n₁ n₂ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun xy₁ xy₂ =>
    .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun X₁ X₂ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun Y₁ Y₂ =>
    .bind (wf_validGraphProg (by simp) (by simp)) fun _ _ =>
    .bind (wf_validGraphProg (by simp) (by simp)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) (.cons (List.Mem.head _) .nil))) fun _ _ =>
    .ite (List.Mem.head _)
      (.bind (wf_connProg (by simp) (by simp)) fun _ _ =>
        .bind (wf_connProg (by simp) (by simp)) fun _ _ =>
        .bind (.prim _ (.cons (by simp) (.cons (List.Mem.head _) .nil))) fun _ _ =>
        .ite (List.Mem.head _) (.bind (wf_mainProg (by simp) (by simp) (by simp)) fun _ _ =>
          .prim _ (.cons (List.Mem.head _) .nil)) (.prim _ .nil))
      (.prim _ .nil)

/-- **The checked entry against the Schreier–Sims context, on every input.** -/
theorem RunsWithin.gi3Checked (n : ℕ) (X Y : GraphData) :
    ∃ r, RunsWithin ssCtx (luksBody Ty.unit Ty.denote)
        (Graph.gi3Checked Ty.unit Ty.denote (n, X, Y)) r (checkedCost n) ∧
      (r = none ↔ ¬ GIValid n X Y) ∧ ∀ res, r = some res → GIAnswer n X Y res := by
  have hvX := RunsWithin.validGraphProg (X := ssCtx) (body := luksBody Ty.unit Ty.denote) n X
  have hvY := RunsWithin.validGraphProg (X := ssCtx) (body := luksBody Ty.unit Ty.denote) n Y
  by_cases hv : (validGB n X && validGB n Y) = true
  · rw [Bool.and_eq_true, validGB_iff, validGB_iff] at hv
    obtain ⟨hX, hY⟩ := hv
    have hcX := RunsWithin.connProg (X := ssCtx) (body := luksBody Ty.unit Ty.denote) hX
    have hcY := RunsWithin.connProg (X := ssCtx) (body := luksBody Ty.unit Ty.denote) hY
    by_cases hc : (connB n X && connB n Y) = true
    · rw [Bool.and_eq_true, connB_iff, connB_iff] at hc
      obtain ⟨hcX', hcY'⟩ := hc
      obtain ⟨res, hrun, h₁, h₂⟩ := RunsWithin.mainProg hX hY hcX' hcY'
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
            simp [Prim.eval, (validGB_iff (n := n) (G := X)).2 hX,
              (validGB_iff (n := n) (G := Y)).2 hY]) _
          run_step hcX
          run_step hcY
          run_step (RunsWithin.prim _ _)
          run_with RunsWithin.ite_pos (by
            simp [Prim.eval, (connB_iff (n := n) (G := X)).2 hcX',
              (connB_iff (n := n) (G := Y)).2 hcY']) _
          run_step hrun
          exact RunsWithin.prim_le rfl le_rfl
        case hc =>
          simp only [Prim.cost, checkedCost]
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
          simp [Prim.eval, (validGB_iff (n := n) (G := X)).2 hX,
            (validGB_iff (n := n) (G := Y)).2 hY]) _
        run_step hcX
        run_step hcY
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.ite_neg (by simpa [Prim.eval] using hc) _
        exact RunsWithin.prim_le rfl le_rfl
      case hc =>
        simp only [Prim.cost, checkedCost]
        omega
  · refine ⟨none, ?_, ⟨fun _ ⟨hX, hY, _, _⟩ => hv (by
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
      simp only [Prim.cost, checkedCost]
      omega

/-! ### The closed form -/

section ClosedForm

theorem domBound_succ_le (N : ℕ) : domBound N + 1 ≤ (N + 1) ^ 3 := by
  have hK3 : (N + 1) ^ 3 = N * N * N + 3 * (N * N) + 3 * N + 1 := by ring
  unfold domBound
  rw [hK3]
  omega

theorem genBound_le (N : ℕ) : genBound N ≤ (N + 1) ^ 6 := by
  have hM := domBound_succ_le N
  have hNN : N * N ≤ 2 * domBound N + 1 := by
    unfold domBound
    nlinarith
  have h : (domBound N + 1) * (domBound N + 1) ≤ (N + 1) ^ 3 * (N + 1) ^ 3 :=
    Nat.mul_le_mul hM hM
  rw [show (N + 1) ^ 3 * (N + 1) ^ 3 = (N + 1) ^ 6 by ring] at h
  have hsq : (domBound N + 1) * (domBound N + 1) = domBound N * domBound N + 2 * domBound N + 1 :=
    by ring
  unfold genBound
  omega

/-- **One layer step costs at most `8100 (N + 1)²⁴`.** -/
theorem layerCost_le (N : ℕ) : layerCost N ≤ 8100 * (N + 1) ^ 24 := by
  set K := N + 1 with hK
  have hK1 : 1 ≤ K := by omega
  have hNK : N ≤ K := by omega
  have hK3 : (N + 1) ^ 3 = N * N * N + 3 * (N * N) + 3 * N + 1 := by ring
  have hM : domBound N + 1 ≤ K ^ 3 := by
    unfold domBound
    rw [hK, hK3]
    omega
  have hMM : domBound N * domBound N ≤ K ^ 6 := by
    have : domBound N * domBound N ≤ K ^ 3 * K ^ 3 := Nat.mul_le_mul (by omega) (by omega)
    rw [← pow_add] at this
    exact this
  have hNN : N * N ≤ 2 * domBound N + 1 := by
    unfold domBound
    nlinarith
  have hL : genBound N ≤ K ^ 6 := by
    have : (domBound N + 1) * (domBound N + 1) ≤ K ^ 3 * K ^ 3 := Nat.mul_le_mul hM hM
    rw [← pow_add] at this
    unfold genBound
    nlinarith
  have h8 : (domBound N + 1) ^ 8 ≤ K ^ 24 := by
    calc (domBound N + 1) ^ 8 ≤ (K ^ 3) ^ 8 := Nat.pow_le_pow_left hM 8
      _ = K ^ 24 := by rw [← pow_mul]
  have h2 : (domBound N + 1) ^ 2 ≤ K ^ 6 := by
    calc (domBound N + 1) ^ 2 ≤ (K ^ 3) ^ 2 := Nat.pow_le_pow_left hM 2
      _ = K ^ 6 := by rw [← pow_mul]
  have hLM : genBound N * (domBound N + 1) ^ 2 ≤ K ^ 12 := by
    calc genBound N * (domBound N + 1) ^ 2 ≤ K ^ 6 * K ^ 6 := Nat.mul_le_mul hL h2
      _ = K ^ 12 := by rw [← pow_add]
  have hL3 : genBound N * K ^ 3 ≤ K ^ 9 := by
    calc genBound N * K ^ 3 ≤ K ^ 6 * K ^ 3 := Nat.mul_le_mul_right _ hL
      _ = K ^ 9 := by rw [← pow_add]
  have hq : 440 * N * N + 141 * N + 28 ≤ 609 * K ^ 2 := by
    rw [hK]
    nlinarith
  have hout₁ : domBound N * domBound N * (440 * N * N + 141 * N + 28) ≤ 609 * K ^ 8 := by
    calc domBound N * domBound N * (440 * N * N + 141 * N + 28) ≤ K ^ 6 * (609 * K ^ 2) :=
          Nat.mul_le_mul hMM hq
      _ = 609 * K ^ 8 := by ring
  have hout₂ : N * (N * (10 * N + 107) + 22) ≤ 139 * K ^ 3 := by
    rw [hK]
    nlinarith
  have p4 := Nat.pow_le_pow_right hK1 (show 4 ≤ 24 by omega)
  have p3 := Nat.pow_le_pow_right hK1 (show 3 ≤ 24 by omega)
  have p8 := Nat.pow_le_pow_right hK1 (show 8 ≤ 24 by omega)
  have p9 := Nat.pow_le_pow_right hK1 (show 9 ≤ 24 by omega)
  have p12 := Nat.pow_le_pow_right hK1 (show 12 ≤ 24 by omega)
  have p1 : K ≤ K ^ 24 := by
    have := Nat.pow_le_pow_right hK1 (show 1 ≤ 24 by omega)
    rwa [pow_one] at this
  unfold layerCost stepCost inputCost outCost
  rw [← hK]
  have e : 100 * genBound N * K ^ 3 = 100 * (genBound N * K ^ 3) := by ring
  have e' : 60 * genBound N * (domBound N + 1) ^ 2 = 60 * (genBound N * (domBound N + 1) ^ 2) := by
    ring
  rw [e, e']
  omega

/-- **The edge test costs at most `8400 (2n + 1)²⁵`.** -/
theorem edgeCost_le (n : ℕ) : edgeCost n ≤ 8400 * (2 * n + 1) ^ 25 := by
  set K := 2 * n + 1 with hK
  have hK1 : 1 ≤ K := by omega
  have hl := layerCost_le (2 * n)
  rw [← hK] at hl
  have hlev : levelsCost (2 * n) 4 ≤ 70 * K ^ 3 := by
    unfold levelsCost
    rw [hK]
    nlinarith
  have hgb : genBound (2 * n) ≤ K ^ 6 := genBound_le (2 * n)
  have h25 : 2 * n * (8100 * K ^ 24) ≤ 8100 * K ^ 25 := by
    calc 2 * n * (8100 * K ^ 24) = 8100 * (2 * n * K ^ 24) := by ring
      _ ≤ 8100 * (K * K ^ 24) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))
      _ = 8100 * K ^ 25 := by ring
  have hmul : 2 * n * (layerCost (2 * n) + 1) ≤ 2 * n * (8100 * K ^ 24) + 2 * n := by
    rw [Nat.mul_add, Nat.mul_one]
    exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hl) _
  have p3 := Nat.pow_le_pow_right hK1 (show 3 ≤ 25 by omega)
  have p6 := Nat.pow_le_pow_right hK1 (show 6 ≤ 25 by omega)
  have p1 : K ≤ K ^ 25 := by
    have := Nat.pow_le_pow_right hK1 (show 1 ≤ 25 by omega)
    rwa [pow_one] at this
  unfold edgeCost
  omega

/-- **The algorithm costs at most `16900 (2n + 1)²⁶`.** -/
theorem mainCost_le (n : ℕ) : mainCost n ≤ 16900 * (2 * n + 1) ^ 26 := by
  set K := 2 * n + 1 with hK
  have hK1 : 1 ≤ K := by omega
  have he := edgeCost_le n
  rw [← hK] at he
  have h26 : 3 * n * (8400 * K ^ 25) ≤ 16800 * K ^ 26 := by
    calc 3 * n * (8400 * K ^ 25) = 8400 * (3 * n * K ^ 25) := by ring
      _ ≤ 8400 * (2 * K * K ^ 25) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))
      _ = 16800 * K ^ 26 := by ring
  have hmul : 3 * n * (edgeCost n + 4) ≤ 3 * n * (8400 * K ^ 25) + 12 * n := by
    rw [Nat.mul_add]
    have := Nat.mul_le_mul_left (3 * n) he
    omega
  have p1 : K ≤ K ^ 26 := by
    have := Nat.pow_le_pow_right hK1 (show 1 ≤ 26 by omega)
    rwa [pow_one] at this
  unfold mainCost
  omega

/-- **The checked entry costs at most `17500 (2n + 1)²⁶` on every input.** -/
theorem checkedCost_le (n : ℕ) : checkedCost n ≤ 17500 * (2 * n + 1) ^ 26 := by
  set K := 2 * n + 1 with hK
  have hK1 : 1 ≤ K := by omega
  have hm := mainCost_le n
  rw [← hK] at hm
  have hc : connCost n ≤ 70 * K ^ 3 := by
    unfold connCost levelsCost
    rw [hK]
    nlinarith
  have p3 := Nat.pow_le_pow_right hK1 (show 3 ≤ 26 by omega)
  have p1 : K ≤ K ^ 26 := by
    have := Nat.pow_le_pow_right hK1 (show 1 ≤ 26 by omega)
    rwa [pow_one] at this
  unfold checkedCost
  omega

end ClosedForm

/-! ### The concrete theorems -/

/-- **Isomorphism of graphs of maximum degree three in polynomial time.** The checked entry
with the Schreier–Sims backend substituted, run inside `luksSolver`, with no assumed oracle:
on every input `(n, X, Y)` the result is `none` exactly when `X` and `Y` are not valid
connected graph data of maximum degree three on `n` points (connected in the sense of `Conn`,
which holds vacuously for `n = 0`), and otherwise a correct answer; the cost is at most
`17500 (2n + 1)²⁶`. -/
theorem gi3_checked (n : ℕ) (X Y : GraphData) :
    ∃ (r : Option (Option (Array ℕ))) (tr : Trace Signature.empty),
      Runs Ctx.empty.O (luksSolver.proc Ty.denote)
        ((Graph.gi3Checked Ty.unit Ty.denote (n, X, Y)).subst ssImpl) r tr ∧
      Trace.localCost tr ≤ 17500 * (2 * n + 1) ^ 26 ∧
      (r = none ↔ ¬ GIValid n X Y) ∧ ∀ res, r = some res → GIAnswer n X Y res := by
  obtain ⟨r, ⟨tr, hr, hc, hpre⟩, hnone, hsome⟩ := RunsWithin.gi3Checked n X Y
  obtain ⟨tr', hr', hc'⟩ := Runs.subst ssImpl_implements hr hpre
  refine ⟨r, tr', hr', ?_, hnone, hsome⟩
  rw [Trace.cost_empty] at hc'
  exact hc'.trans (hc.trans (checkedCost_le n))

/-- **The statement for simple graphs given as data.** For valid data of maximum degree three
whose simple graphs are connected, the checked entry returns `some none` exactly when the
simple graphs are not isomorphic, and `some (some arr)` only when `arr` lists the `n` values of
an isomorphism of the simple graphs. -/
theorem gi3_simpleGraph {n : ℕ} {X Y : GraphData} (hX : X.Valid n) (hY : Y.Valid n)
    (hcX : (X.toSimpleGraph n).Connected) (hcY : (Y.toSimpleGraph n).Connected) :
    ∃ (res : Option (Array ℕ)) (tr : Trace Signature.empty),
      Runs Ctx.empty.O (luksSolver.proc Ty.denote)
        ((Graph.gi3Checked Ty.unit Ty.denote (n, X, Y)).subst ssImpl) (some res) tr ∧
      Trace.localCost tr ≤ 17500 * (2 * n + 1) ^ 26 ∧
      (res = none ↔ IsEmpty (X.toSimpleGraph n ≃g Y.toSimpleGraph n)) ∧
      ∀ arr, res = some arr → arr.size = n ∧ ∃ e : X.toSimpleGraph n ≃g Y.toSimpleGraph n,
        ∀ v : Fin n, get arr v = e v := by
  have hn : 0 < n := Fin.pos_iff_nonempty.2 hcX.nonempty
  obtain ⟨r, tr, hr, hc, hnone, hsome⟩ := gi3_checked n X Y
  have hvalid : GIValid n X Y :=
    ⟨hX, hY, (conn_iff_connected hX hn).2 hcX, (conn_iff_connected hY hn).2 hcY⟩
  rcases r with _ | res
  · exact absurd (hnone.1 rfl) (not_not.2 hvalid)
  obtain ⟨h₁, h₂⟩ := hsome res rfl
  refine ⟨res, tr, hr, hc, ?_, fun arr harr => ?_⟩
  · rw [h₁, ← nonempty_iso_iff hX hY, not_nonempty_iff]
  · obtain ⟨hs, φ, hφ, hv⟩ := h₂ arr harr
    exact ⟨hs, isoOfIsIso hX hY hφ, fun v => by rw [hv v v.2, act_of_lt _ v.2]; rfl⟩

/-- **Isomorphism of connected simple graphs of maximum degree three in polynomial time.** For
connected simple graphs `G` and `H` on `Fin n` with every degree at most three, the checked
entry on their adjacency lists returns `some none` exactly when `G` and `H` are not isomorphic,
and `some (some arr)` only when `arr` lists the `n` values of an isomorphism `G ≃g H`; the cost
is at most `17500 (2n + 1)²⁶`. -/
theorem gi3_simpleGraph' {n : ℕ} {G H : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    [DecidableRel H.Adj] (hdG : ∀ v, G.degree v ≤ 3) (hdH : ∀ v, H.degree v ≤ 3)
    (hcG : G.Connected) (hcH : H.Connected) :
    ∃ (res : Option (Array ℕ)) (tr : Trace Signature.empty),
      Runs Ctx.empty.O (luksSolver.proc Ty.denote)
        ((Graph.gi3Checked Ty.unit Ty.denote
          (n, GraphData.ofSimpleGraph G, GraphData.ofSimpleGraph H)).subst ssImpl) (some res) tr ∧
      Trace.localCost tr ≤ 17500 * (2 * n + 1) ^ 26 ∧
      (res = none ↔ IsEmpty (G ≃g H)) ∧
      ∀ arr, res = some arr → arr.size = n ∧ ∃ e : G ≃g H, ∀ v : Fin n, get arr v = e v := by
  have h := gi3_simpleGraph (valid_ofSimpleGraph hdG) (valid_ofSimpleGraph hdH)
    (by rwa [toSimpleGraph_ofSimpleGraph]) (by rwa [toSimpleGraph_ofSimpleGraph])
  rw [toSimpleGraph_ofSimpleGraph, toSimpleGraph_ofSimpleGraph] at h
  exact h

end GraphIso.Graph
