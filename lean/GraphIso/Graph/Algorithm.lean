module

public import GraphIso.Graph.EdgeProg

/-!
# Isomorphism of connected graphs of maximum degree three

`mainProg n X Y` decides isomorphism of graph data `X` and `Y` on `n` points. It roots `X` at
the edge `{0, b}` with `b` the first neighbour of `0`, and runs the edge test `edgeProg` for
every directed edge `(a', b')` of `Y` until one succeeds. If `0` has no neighbour it returns
the identity (then `n ≤ 1` for connected data).

* `Conn n G`: every point has level below `n` from the root `0`: the connectivity read by the
  algorithm. For the union rooted at `{0, b}` and `{a', b'}`, every point is then reached
  (`reach_union`): a point of `X` within its level from `0`, a point of `Y` within the sum of
  the levels of `a'` and of the point.
* **`RunsWithin.mainProg`**: with the Schreier–Sims backend, for valid connected data, the
  result is `none` exactly when `X` and `Y` are not isomorphic, and otherwise lists the values
  of an isomorphism; the cost is at most `mainCost n`.
-/

@[expose] public section

namespace GraphIso.Graph

open Equiv Cost Programs Sims Luks

/-! ### Connectivity -/

/-- Every point has level below `n` from the root `0`. This holds vacuously for `n = 0`; for
`n > 0` it is `SimpleGraph.Connected` (`conn_iff_connected`). -/
def Conn (n : ℕ) (G : GraphData) : Prop := ∀ v < n, get (levels n G [0]) v < n

section Reach

variable {Δ N N' : ℕ} {H G : GraphData} {r₀ : ℕ} {roots : List ℕ} {L M : Array ℕ}

/-- Levels along an embedding: a point of level `k` from `r₀` is within `k` of the image of
`r₀`, in both directions. -/
theorem lev_embed (hH : H.ValidD Δ N') (hL : IsLevels N' H [r₀] L) (hM : IsLevels N G roots M)
    {e : ℕ → ℕ} (he : ∀ u v, Adj H u v → Adj G (e u) (e v)) :
    ∀ k v, v < N' → get L v = k → k < N' →
      get M (e v) ≤ get M (e r₀) + k ∧ get M (e r₀) ≤ get M (e v) + k := by
  intro k
  induction k with
  | zero =>
    intro v hv hk _
    have := (hL.zero_iff v hv).1 hk
    simp only [List.mem_singleton] at this
    subst this
    omega
  | succ k ih =>
    intro v hv hk hkN
    obtain ⟨u, huv, hlu⟩ := hL.wit v hv (by omega) (by omega)
    have hu : u < N' := hH.lt v u huv
    obtain ⟨h₁, h₂⟩ := ih u hu (by omega) (by omega)
    have a₁ := hM.adj_le _ _ (he v u huv)
    have a₂ := hM.adj_le _ _ (he u v (hH.symm v u huv))
    omega

variable {n : ℕ} {X Y : GraphData}

/-- **Every point of the union is reached** from the roots `{0, b}` and `{a', b'}`. -/
theorem reach_union (hX : X.ValidD Δ n) (hY : Y.ValidD Δ n) (hcX : Conn n X) (hcY : Conn n Y)
    {b a' b' : ℕ} (ha' : a' < n) :
    ∀ v < 2 * n, get (unionLev n X Y 0 b a' b') v < 2 * n := by
  have hM := isLevels_union (a := 0) (b := b) (a' := a') (b' := b') hX hY
  have hLX := levels_spec (roots := [0]) hX
  have hLY := levels_spec (roots := [0]) hY
  have hadj := fun u v => adj_union_iff (u := u) (v := v) (Y := Y) hX
  intro v hv
  by_cases hvn : v < n
  · obtain ⟨h₁, -⟩ := lev_embed hX hLX hM (e := id)
      (fun u w huw => (hadj u w).2 (Or.inl ⟨hX.lt_left huw, hX.lt u w huw, huw⟩))
      _ v hvn rfl (hcX v hvn)
    have h0 : get (unionLev n X Y 0 b a' b') 0 = 0 :=
      (hM.zero_iff 0 (by omega)).2 (by simp)
    simp only [id] at h₁
    have := hcX v hvn
    omega
  · have he : ∀ u w, Adj Y u w → Adj (GraphData.union n X Y) (n + u) (n + w) := fun u w huw =>
      (hadj _ _).2 (Or.inr ⟨by omega, by omega, by simpa using huw⟩)
    obtain ⟨h₁, -⟩ := lev_embed hY hLY hM (e := (n + ·)) he _ (v - n) (by omega) rfl
      (hcY (v - n) (by omega))
    obtain ⟨-, h₂⟩ := lev_embed hY hLY hM (e := (n + ·)) he _ a' ha' rfl (hcY a' ha')
    have hroot : get (unionLev n X Y 0 b a' b') (n + a') = 0 :=
      (hM.zero_iff _ (by omega)).2 (by simp)
    have e₁ : n + (v - n) = v := by omega
    simp only [e₁] at h₁
    have := hcY (v - n) (by omega)
    have := hcY a' ha'
    omega

/-- A graph with all levels below `n` and at least two points has an edge at `0`. -/
theorem nbrs_zero_ne_nil {G : GraphData} (hG : G.ValidD Δ n) (hc : Conn n G) (hn : 2 ≤ n) :
    nbrs G 0 ≠ [] := by
  have hL := levels_spec (roots := [0]) hG
  have key : ∀ k v, v < n → get (levels n G [0]) v = k + 1 → nbrs G 0 ≠ [] := by
    intro k
    induction k with
    | zero =>
      intro v hv hk
      obtain ⟨u, huv, hlu⟩ := hL.wit v hv (by omega) (by have := hc v hv; omega)
      have hu0 := (hL.zero_iff u (hG.lt v u huv)).1 (by omega)
      simp only [List.mem_singleton] at hu0
      subst hu0
      exact List.ne_nil_of_mem (hG.symm v 0 huv)
    | succ k ih =>
      intro v hv hk
      obtain ⟨u, huv, hlu⟩ := hL.wit v hv (by omega) (by have := hc v hv; omega)
      exact ih u (hG.lt v u huv) (by omega)
  have h1 : get (levels n G [0]) 1 ≠ 0 := fun h => by
    have := (hL.zero_iff 1 (by omega)).1 h
    simp at this
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero h1
  exact key k 1 (by omega) hk

end Reach

/-! ### The edges of `Y` -/

/-- The directed edges `(u, v)`, `u < n`. -/
def edgesB (n : ℕ) (Y : GraphData) : List (ℕ × ℕ) :=
  (List.range n).foldl (fun acc u => (nbrs Y u).foldl (fun acc v => (u, v) :: acc) acc) []

theorem mem_edgesB {n : ℕ} {Y : GraphData} {u v : ℕ} :
    (u, v) ∈ edgesB n Y ↔ u < n ∧ Adj Y u v := by
  have hin : ∀ (w : ℕ) (l : List ℕ) (acc : List (ℕ × ℕ)),
      (u, v) ∈ l.foldl (fun acc v => (w, v) :: acc) acc ↔ (u, v) ∈ acc ∨ (u = w ∧ v ∈ l) := by
    intro w l
    induction l with
    | nil => simp
    | cons x l ih =>
      intro acc
      rw [List.foldl_cons, ih]
      simp only [List.mem_cons, Prod.mk.injEq]
      tauto
  have hout : ∀ (l : List ℕ) (acc : List (ℕ × ℕ)),
      (u, v) ∈ l.foldl (fun acc u => (nbrs Y u).foldl (fun acc v => (u, v) :: acc) acc) acc ↔
        (u, v) ∈ acc ∨ (u ∈ l ∧ v ∈ nbrs Y u) := by
    intro l
    induction l with
    | nil => simp
    | cons x l ih =>
      intro acc
      rw [List.foldl_cons, ih, hin]
      simp only [List.mem_cons]
      constructor
      · rintro ((h | ⟨rfl, h⟩) | ⟨h₁, h₂⟩)
        · exact Or.inl h
        · exact Or.inr ⟨Or.inl rfl, h⟩
        · exact Or.inr ⟨Or.inr h₁, h₂⟩
      · rintro (h | ⟨rfl | h₁, h₂⟩)
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr ⟨rfl, h₂⟩)
        · exact Or.inr ⟨h₁, h₂⟩
  rw [edgesB, hout]
  simp [Adj]

theorem length_edgesB_le {Δ n : ℕ} {Y : GraphData} (hY3 : ∀ u, (nbrs Y u).length ≤ Δ) :
    (edgesB n Y).length ≤ Δ * n := by
  have hin : ∀ (w : ℕ) (l : List ℕ) (acc : List (ℕ × ℕ)),
      (l.foldl (fun acc v => (w, v) :: acc) acc).length = acc.length + l.length := by
    intro w l
    induction l with
    | nil => simp
    | cons x l ih => intro acc; rw [List.foldl_cons, ih]; simp; omega
  have hout : ∀ (k : ℕ) (acc : List (ℕ × ℕ)),
      ((List.range k).foldl (fun acc u => (nbrs Y u).foldl (fun acc v => (u, v) :: acc) acc)
        acc).length ≤ acc.length + Δ * k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro acc
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [hin, Nat.mul_succ]
      have := hY3 k
      have := ih acc
      omega
  simpa [edgesB] using hout n []

/-! ### Programs -/

section Prog

variable {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- The directed edges of `Y`. -/
def edgesProg (n : var .nat) (Y : var Ty.graph) : Prog S rec var (.list (.prod .nat .nat)) :=
  .bind (.op1 .range n) fun rn => .bind (.op0 .nil) fun nl =>
  .foldList rn nl fun acc u => .bind (.op2 .arrayGet Y u) fun ns =>
    .foldList ns acc fun acc v => .bind (.op2 .pair u v) fun uv => .op2 .cons uv acc

/-- One edge test, unless an isomorphism was found. -/
def edgeStepProg {D : Ty} (n N : var .nat) (Z : var Ty.graph) (a b : var .nat)
    (acc : var (.option (.array .nat))) (e : var (.prod .nat .nat)) :
    Prog (groupSig D) (Solver.Rec D) var (.option (.array .nat)) :=
  .caseOption acc (.bind (.op1 .fst e) fun a' => .bind (.op1 .snd e) fun b' =>
    edgeProg n N Z a b a' b') fun _ => .ret acc

/-- **Isomorphism of connected graphs of maximum degree three.** -/
def mainProg {D : Ty} (n : var .nat) (X Y : var Ty.graph) :
    Prog (groupSig D) (Solver.Rec D) var (.option (.array .nat)) :=
  .bind (.op2 .add n n) fun N =>
  .bind (unionProg n X Y) fun Z =>
  .bind (.op0 (.natLit 0)) fun a =>
  .bind (.op2 .arrayGet X a) fun nsa =>
  .caseList nsa
    (.bind (.op1 .range n) fun rn => .bind (.op1 .arrayOfList rn) fun arr => .op1 .some arr)
    fun b _ =>
      .bind (edgesProg n Y) fun es => .bind (.op0 .none) fun nn =>
      .foldList es nn fun acc e => edgeStepProg n N Z a b acc e

end Prog

/-! ### Specifications -/

section Specs

variable {S : Signature} {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

theorem RunsWithin.edgesProg {n : ℕ} {Y : GraphData} (hY3 : ∀ u, (nbrs Y u).length ≤ 3) :
    RunsWithin X body (Graph.edgesProg n Y) (edgesB n Y) (12 * n + 2) := by
  have hin : ∀ (u : ℕ) (acc : List (ℕ × ℕ)), RunsWithin X body
      (.bind (.op2 .arrayGet Y u) fun ns =>
        .foldList (a := .nat) (b := .list (.prod .nat .nat)) ns acc fun acc v =>
          .bind (.op2 .pair u v) fun uv => .op2 .cons uv acc)
      ((nbrs Y u).foldl (fun acc v => (u, v) :: acc) acc) 10 := by
    intro u acc
    have hfold := RunsWithin.foldList_of (X := X) (body := body) (a' := .nat)
      (b' := .list (.prod .nat .nat)) (cf := fun _ => 2) (F := fun acc v => (u, v) :: acc)
      (f := fun acc v => .bind (.op2 .pair u v) fun uv => .op2 .cons uv acc) (nbrs Y u) acc
      fun acc v _ => RunsWithin.bind_le (RunsWithin.prim _ _) (RunsWithin.prim_le rfl le_rfl)
        le_rfl
    rw [sum_map_const] at hfold
    have := hY3 u
    exact (RunsWithin.bind (RunsWithin.prim _ _) hfold).mono (by simp only [Prim.cost]; omega)
  have hfold := RunsWithin.foldList_of (X := X) (body := body) (a' := .nat)
    (b' := .list (.prod .nat .nat)) (cf := fun _ => 10)
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
    omega

/-- A fold whose body keeps an invariant `I` of the processed prefix within cost `c`, with
results given existentially. -/
theorem RunsWithin.foldList_exists {a' b' : Ty}
    {f : b'.denote → a'.denote → Prog S (a, b) Ty.denote b'}
    {I : List a'.denote → b'.denote → Prop} {c : ℕ} :
    ∀ (xs pre : List a'.denote) (init : b'.denote),
      (∀ pre' acc x, x ∈ xs → I pre' acc →
        ∃ v, RunsWithin X body (f acc x) v c ∧ I (pre' ++ [x]) v) →
      I pre init →
      ∃ v, RunsWithin X body (.foldList xs init f) v (xs.length * (c + 1)) ∧ I (pre ++ xs) v
  | [], pre, init, _, h => ⟨init, by simpa using RunsWithin.foldList_nil, by simpa using h⟩
  | x :: xs, pre, init, hf, h => by
    obtain ⟨v₁, h₁, hI₁⟩ := hf pre init x List.mem_cons_self h
    obtain ⟨v, h₂, hI⟩ := foldList_exists xs (pre ++ [x]) v₁
      (fun pre' acc y hy => hf pre' acc y (List.mem_cons_of_mem _ hy)) hI₁
    refine ⟨v, (RunsWithin.foldList_cons h₁ h₂).mono ?_, by simpa using hI⟩
    simp only [List.length_cons, Nat.succ_mul]
    omega

end Specs

/-! ### The algorithm -/

/-- The cost bound of the algorithm on `n` points. -/
def mainCost (n : ℕ) : ℕ := 3 * n * (edgeCost n + 4) + 40 * n + 20

section Main

variable {n : ℕ} {X Y : GraphData} (hX : X.Valid n) (hY : Y.Valid n) (hcX : Conn n X)
  (hcY : Conn n Y)

omit hX hY in
/-- On at most one point every permutation is an isomorphism of valid data. -/
theorem isIso_one_of_le {Δ : ℕ} (hX : X.ValidD Δ n) (hY : Y.ValidD Δ n) (hn : n ≤ 1) :
    IsIso n X Y 1 := by
  intro u v hu hv
  have hu0 : u = 0 := by omega
  have hv0 : v = 0 := by omega
  subst hu0 hv0
  rw [act_one]
  exact iff_of_false (hY.irrefl 0) (hX.irrefl 0)

include hX hY hcX hcY in
/-- **Isomorphism of connected graphs of maximum degree three.** With the Schreier–Sims
backend, for valid connected data, the result is `none` exactly when `X` and `Y` are not
isomorphic, and otherwise lists the values of an isomorphism. -/
theorem RunsWithin.mainProg :
    ∃ res, RunsWithin ssCtx (luksBody Ty.unit Ty.denote) (Graph.mainProg n X Y) res
        (mainCost n) ∧
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
        nlinarith
    · cases harr
      exact ⟨by simp, 1, isIso_one_of_le hX hY hn, fun v hv => by simp [get, hv]⟩
  · have hb : Adj X 0 b := by rw [Adj, hnb]; exact List.mem_cons_self
    have hes := RunsWithin.edgesProg (X := ssCtx) (body := luksBody Ty.unit Ty.denote) (n := n)
      hY.deg
    have hlen := length_edgesB_le (n := n) hY.deg
    -- the fold over the edges
    obtain ⟨res, hfold, hI⟩ := RunsWithin.foldList_exists (X := ssCtx)
      (body := luksBody Ty.unit Ty.denote) (a' := .prod .nat .nat) (b' := .option (.array .nat))
      (c := edgeCost n + 3)
      (f := fun acc e => Graph.edgeStepProg n (n + n) (GraphData.union n X Y) 0 b acc e)
      (I := fun pre acc =>
        (acc = none → ∀ e ∈ pre, ¬ ∃ φ, IsIso n X Y φ ∧ SendsEdge n 0 b e.1 e.2 φ) ∧
        ∀ arr, acc = some arr → arr.size = n ∧ ∃ φ : Perm (Fin n), IsIso n X Y φ ∧
          ∀ v < n, get arr v = act φ v)
      (edgesB n Y) [] none (fun pre acc e he ⟨h₁, h₂⟩ => by
        rcases acc with _ | arr
        · obtain ⟨a', b'⟩ := e
          obtain ⟨ha', hab'⟩ := mem_edgesB.1 he
          obtain ⟨r, hr, hnone, hsome⟩ := RunsWithin.edgeProg hX hY hb hab'
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
        have : (edgesB n Y).length * (edgeCost n + 3 + 1) ≤ 3 * n * (edgeCost n + 4) :=
          Nat.mul_le_mul hlen le_rfl
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

end GraphIso.Graph
