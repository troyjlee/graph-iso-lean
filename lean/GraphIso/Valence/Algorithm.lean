module

public import GraphIso.Valence.EdgeProg
public import GraphIso.Graph.Algorithm

/-!
# Isomorphism of connected graphs of maximum degree `Δ`

`mainProg Δ n X Y` decides isomorphism of graph data `X` and `Y` on `n` points. As milestone 4's
`mainProg`, it roots `X` at the edge `{0, b}` with `b` the first neighbour of `0`, and runs the
edge test `edgeProg Δ` for every directed edge `(a', b')` of `Y` until one succeeds. If `0` has
no neighbour it returns the identity (then `n ≤ 1` for connected data).

* `RunsWithin.edgesProg`: the directed edges of `Y` cost at most `(3 Δ + 3) n + 2`; there are at
  most `Δ n` of them (`length_edgesB_le`).
* **`RunsWithin.mainProg`**: with the Schreier–Sims backend, for valid connected data of maximum
  degree `Δ ≥ 2`, and a constant `c ≥ 1` with `LayerPrim Δ c`, the result is `none` exactly
  when `X` and `Y` are not isomorphic, and otherwise lists the values of an isomorphism; the
  cost is at most `mainCost Δ c n`.
-/

@[expose] public section

namespace GraphIso.Graph.Valence

open Equiv Cost Programs Sims Luks

/-! ### Programs -/

section Prog

variable {var : Ty → Type}

/-- One edge test, unless an isomorphism was found. -/
def edgeStepProg (Δ : ℕ) {D : Ty} (n N : var .nat) (Z : var Ty.graph) (a b : var .nat)
    (acc : var (.option (.array .nat))) (e : var (.prod .nat .nat)) :
    Prog (groupSig D) (Solver.Rec D) var (.option (.array .nat)) :=
  .caseOption acc (.bind (.op1 .fst e) fun a' => .bind (.op1 .snd e) fun b' =>
    edgeProg Δ n N Z a b a' b') fun _ => .ret acc

/-- **Isomorphism of connected graphs of maximum degree `Δ`.** -/
def mainProg (Δ : ℕ) {D : Ty} (n : var .nat) (X Y : var Ty.graph) :
    Prog (groupSig D) (Solver.Rec D) var (.option (.array .nat)) :=
  .bind (.op2 .add n n) fun N =>
  .bind (unionProg n X Y) fun Z =>
  .bind (.op0 (.natLit 0)) fun a =>
  .bind (.op2 .arrayGet X a) fun nsa =>
  .caseList nsa
    (.bind (.op1 .range n) fun rn => .bind (.op1 .arrayOfList rn) fun arr => .op1 .some arr)
    fun b _ =>
      .bind (edgesProg n Y) fun es => .bind (.op0 .none) fun nn =>
      .foldList es nn fun acc e => edgeStepProg Δ n N Z a b acc e

end Prog

/-! ### Specifications -/

section Specs

variable {S : Signature} {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

theorem RunsWithin.edgesProg {Δ n : ℕ} {Y : GraphData} (hYd : ∀ u, (nbrs Y u).length ≤ Δ) :
    RunsWithin X body (Graph.edgesProg n Y) (edgesB n Y) ((3 * Δ + 3) * n + 2) := by
  have hin : ∀ (u : ℕ) (acc : List (ℕ × ℕ)), RunsWithin X body
      (.bind (.op2 .arrayGet Y u) fun ns =>
        .foldList (a := .nat) (b := .list (.prod .nat .nat)) ns acc fun acc v =>
          .bind (.op2 .pair u v) fun uv => .op2 .cons uv acc)
      ((nbrs Y u).foldl (fun acc v => (u, v) :: acc) acc) (3 * Δ + 1) := by
    intro u acc
    have hfold := RunsWithin.foldList_of (X := X) (body := body) (a' := .nat)
      (b' := .list (.prod .nat .nat)) (cf := fun _ => 2) (F := fun acc v => (u, v) :: acc)
      (f := fun acc v => .bind (.op2 .pair u v) fun uv => .op2 .cons uv acc) (nbrs Y u) acc
      fun acc v _ => RunsWithin.bind_le (RunsWithin.prim _ _) (RunsWithin.prim_le rfl le_rfl)
        le_rfl
    rw [sum_map_const] at hfold
    have := hYd u
    exact (RunsWithin.bind (RunsWithin.prim _ _) hfold).mono (by simp only [Prim.cost]; omega)
  have hfold := RunsWithin.foldList_of (X := X) (body := body) (a' := .nat)
    (b' := .list (.prod .nat .nat)) (cf := fun _ => 3 * Δ + 1)
    (F := fun acc u => (nbrs Y u).foldl (fun acc v => (u, v) :: acc) acc) (List.range n) []
    fun acc u _ => hin u acc
  rw [sum_map_const, List.length_range] at hfold
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact hfold
  case hc =>
    simp only [Prim.cost, Args.head_cons]
    have : n * (3 * Δ + 1 + 1) + n = (3 * Δ + 3) * n := by ring
    omega

end Specs

/-! ### The algorithm -/

/-- The cost bound of the algorithm on `n` points. -/
def mainCost (Δ c n : ℕ) : ℕ := Δ * n * (edgeCost Δ c n + 4) + (7 * Δ + 16) * n + 20

section Main

variable {Δ c n : ℕ} {X Y : GraphData} (hX : X.ValidD Δ n) (hY : Y.ValidD Δ n) (hΔ₂ : 2 ≤ Δ)
  (hc : LayerPrim Δ c) (hc1 : 1 ≤ c) (hcX : Conn n X) (hcY : Conn n Y)

include hX hY hΔ₂ hc hc1 hcX hcY in
/-- **Isomorphism of connected graphs of maximum degree `Δ`.** With the Schreier–Sims backend,
for valid connected data, the result is `none` exactly when `X` and `Y` are not isomorphic, and
otherwise lists the values of an isomorphism. -/
theorem RunsWithin.mainProg :
    ∃ res, RunsWithin ssCtx (luksBody Ty.unit Ty.denote) (Valence.mainProg Δ n X Y) res
        (mainCost Δ c n) ∧
      (res = none ↔ ¬ ∃ φ, IsIso n X Y φ) ∧
      ∀ arr, res = some arr → arr.size = n ∧
        ∃ φ : Perm (Fin n), IsIso n X Y φ ∧ ∀ v < n, get arr v = act φ v := by
  have hunion := RunsWithin.unionProg (X := ssCtx) (body := luksBody Ty.unit Ty.denote) hX hY
  rcases hnb : nbrs X 0 with _ | ⟨b, rest⟩
  · -- `0` has no neighbour: at most one point
    have hn : n ≤ 1 := by
      by_contra h
      exact nbrs_zero_ne_nil hX hcX (by omega) hnb
    refine ⟨some (List.range n).toArray, ?_, ⟨fun h => absurd h (by simp),
      fun h => absurd ⟨1, isIso_one_of_le hX hY hn⟩ h⟩, fun arr harr => ?_⟩
    · apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step hunion
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        rw [show Prim.eval (Prim.arrayGet (a := .list .nat))
          (.cons X (.cons ((Prim.natLit 0).eval .nil) .nil)) = ([] : List ℕ) from hnb]
        run_with RunsWithin.caseList_nil _
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        exact RunsWithin.prim_le rfl le_rfl
      case hc =>
        simp only [Prim.cost, Prim.eval, Args.head_cons, List.length_range, mainCost]
        have e₁ : (4 * Δ + 13) * n + 2 * n = (4 * Δ + 15) * n := by ring
        have e₂ : (4 * Δ + 15) * n ≤ (7 * Δ + 16) * n := Nat.mul_le_mul_right _ (by omega)
        omega
    · cases harr
      exact ⟨by simp, 1, isIso_one_of_le hX hY hn, fun v hv => by simp [get, hv]⟩
  · have hb : Adj X 0 b := by rw [Adj, hnb]; exact List.mem_cons_self
    have hes := RunsWithin.edgesProg (X := ssCtx) (body := luksBody Ty.unit Ty.denote) (n := n)
      hY.deg
    have hlen := length_edgesB_le (n := n) hY.deg
    -- the fold over the edges
    obtain ⟨res, hfold, hI⟩ := RunsWithin.foldList_exists (X := ssCtx)
      (body := luksBody Ty.unit Ty.denote) (a' := .prod .nat .nat) (b' := .option (.array .nat))
      (c := edgeCost Δ c n + 3)
      (f := fun acc e => Valence.edgeStepProg Δ n (n + n) (GraphData.union n X Y) 0 b acc e)
      (I := fun pre acc =>
        (acc = none → ∀ e ∈ pre, ¬ ∃ φ, IsIso n X Y φ ∧ SendsEdge n 0 b e.1 e.2 φ) ∧
        ∀ arr, acc = some arr → arr.size = n ∧ ∃ φ : Perm (Fin n), IsIso n X Y φ ∧
          ∀ v < n, get arr v = act φ v)
      (edgesB n Y) [] none (fun pre acc e he ⟨h₁, h₂⟩ => by
        rcases acc with _ | arr
        · obtain ⟨a', b'⟩ := e
          obtain ⟨ha', hab'⟩ := mem_edgesB.1 he
          obtain ⟨r, hr, hnone, hsome⟩ := RunsWithin.edgeProg hX hY hΔ₂ hc hc1 hb hab'
            (reach_union hX hY hcX hcY ha') (N := n + n) (by omega)
          refine ⟨r, ?_, fun hr0 e' he' => ?_, hsome⟩
          · apply RunsWithin.mono
            case h =>
              run_with RunsWithin.caseOption_none _
              run_step (RunsWithin.prim _ _)
              run_step (RunsWithin.prim _ _)
              exact hr
            case hc =>
              simp only [Prim.cost]
              omega
          · rcases List.mem_append.1 he' with he' | he'
            · exact h₁ rfl e' he'
            · rw [List.mem_singleton] at he'
              subst he'
              exact hnone.1 hr0
        · refine ⟨some arr, ?_, fun h => absurd h (by simp), h₂⟩
          apply RunsWithin.mono
          case h =>
            run_with RunsWithin.caseOption_some _
            exact RunsWithin.ret _
          case hc =>
            omega)
      ⟨fun _ e he => absurd he (List.not_mem_nil), fun arr h => absurd h (by simp)⟩
    obtain ⟨hnone, hsome⟩ := hI
    refine ⟨res, ?_, ⟨fun hr ⟨φ, hφ⟩ => ?_, fun h => ?_⟩, hsome⟩
    · apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step hunion
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        rw [show Prim.eval (Prim.arrayGet (a := .list .nat))
          (.cons X (.cons ((Prim.natLit 0).eval .nil) .nil)) = b :: rest from hnb]
        run_with RunsWithin.caseList_cons _
        run_step hes
        run_step (RunsWithin.prim _ _)
        exact hfold
      case hc =>
        simp only [Prim.cost, mainCost]
        have : (edgesB n Y).length * (edgeCost Δ c n + 3 + 1) ≤ Δ * n * (edgeCost Δ c n + 4) :=
          Nat.mul_le_mul hlen le_rfl
        have e₁ : (4 * Δ + 13) * n + (3 * Δ + 3) * n = (7 * Δ + 16) * n := by ring
        omega
    · have h0 : (0 : ℕ) < n := hX.lt_left hb
      have hb' : b < n := hX.lt 0 b hb
      have hadj : Adj Y (act φ 0) (act φ b) := (hφ 0 b h0 hb').2 hb
      exact hnone hr (act φ 0, act φ b) (by simpa using mem_edgesB.2 ⟨act_lt φ h0, hadj⟩)
        ⟨φ, hφ, Or.inl ⟨rfl, rfl⟩⟩
    · rcases res with _ | arr
      · rfl
      · obtain ⟨-, φ, hφ, -⟩ := hsome arr rfl
        exact absurd ⟨φ, hφ⟩ h

end Main

end GraphIso.Graph.Valence
