module

public import GraphIso.Solver.Basic
public import Mathlib.Tactic.Linarith

/-!
# The solver's cost bound

For a backend whose charges on the calls the solver makes are bounded (`BackendBounds`), one
invocation of the solver body costs at most `nodeCost` besides its recursive calls, and each
recursive call carries an overhead of at most `edgeCost`. Every branching or splitting
invocation has at least two recursive calls, and the branching step divides the group order
by the orbit length. Hence a window of size `m ≥ 1` with group order `N` is solved in at most
`2 m N - 1` invocations, and the cost is at most

  `solveBound Q m N = 2 m N Q - Q`,  with `Q = nodeCost + 2 edgeCost`

(`Q` for the empty window). This file defines the bounds and proves the arithmetic of the two
recursive steps; `GraphIso/Solver/Correctness.lean` proves that the solver meets them.
-/

@[expose] public section

namespace GraphIso.Solver

open Equiv Cost Programs

variable {D : Ty}

/-- The operations the solver calls. -/
def solverOps (op : GroupOp) : Prop :=
  op = .orbits ∨ op = .stabilizer ∨ op = .orbitTransversal ∨ op = .generate

/-- Bounds on a group backend at degree `n`, for subgroups of an ambient group `G₀` given by at
most `s` generators: charges of the calls the solver makes, and generator counts of the groups
it returns. Every group in a solver run on an instance with group `G₀` is a subgroup of `G₀`,
so bounds may depend on `|G₀|`. -/
structure BackendBounds (X : Ctx (groupSig D)) (DV : ℕ → GensData → D.denote → Prop)
    (n s : ℕ) (G₀ : Subgroup (Equiv.Perm (Fin n))) where
  /-- Bound on an `orbits` charge. -/
  Borb : ℕ
  /-- Bound on a `stabilizer` charge. -/
  Bstab : ℕ
  /-- Bound on an `orbitTransversal` charge. -/
  Btr : ℕ
  /-- Bound on a `generate` charge, for at most `n (s + 1)` input generators. -/
  Bgen : ℕ
  orbits : ∀ (gs : GensData) (d : D.denote) (w : WinData), gs.length ≤ s →
    GensData.denote n gs ≤ G₀ → GroupPre DV .orbits ((n, gs, d), w) →
    X.B.call .orbits ((n, gs, d), w) (X.O.run .orbits ((n, gs, d), w)) ≤ Borb
  stabilizer : ∀ (gs : GensData) (d : D.denote) (u : ℕ), gs.length ≤ s →
    GensData.denote n gs ≤ G₀ → GroupPre DV .stabilizer ((n, gs, d), u) →
    X.B.call .stabilizer ((n, gs, d), u) (X.O.run .stabilizer ((n, gs, d), u)) ≤ Bstab
  transversal : ∀ (gs : GensData) (d : D.denote) (u : ℕ), gs.length ≤ s →
    GensData.denote n gs ≤ G₀ → GroupPre DV .orbitTransversal ((n, gs, d), u) →
    X.B.call .orbitTransversal ((n, gs, d), u) (X.O.run .orbitTransversal ((n, gs, d), u)) ≤ Btr
  generate : ∀ gs : GensData, GensData.AllValid n gs → gs.length ≤ n * (s + 1) →
    GensData.denote n gs ≤ G₀ → X.B.call .generate (n, gs) (X.O.run .generate (n, gs)) ≤ Bgen
  /-- Stabilizers have at most `s` generators. -/
  stabOut : ∀ (gs : GensData) (d : D.denote) (u : ℕ), GensData.denote n gs ≤ G₀ →
    GroupPre DV .stabilizer ((n, gs, d), u) → (X.O.run .stabilizer ((n, gs, d), u)).2.1.length ≤ s
  /-- Generated groups have at most `s` generators. -/
  genOut : ∀ gs : GensData, GensData.AllValid n gs → GensData.denote n gs ≤ G₀ →
    (X.O.run .generate (n, gs)).2.1.length ≤ s

/-- Local work and backend charges of one solver invocation, besides its recursive calls. -/
def nodeCost (n s Borb Bstab Btr Bgen : ℕ) : ℕ :=
  s * (5 * n + 3) + 7 * n + Borb + Bstab + Btr + Bgen + 40

/-- Overhead of one recursive call inside a reduction. -/
def edgeCost (n s : ℕ) : ℕ := 24 * n + s + 50

/-- The cost bound of an empty window, and the per-invocation unit. -/
def solveQ (n s Borb Bstab Btr Bgen : ℕ) : ℕ :=
  nodeCost n s Borb Bstab Btr Bgen + 2 * edgeCost n s

/-- The cost bound for a window of size `m` and group order `N`. -/
def solveBound (Q m N : ℕ) : ℕ := if m = 0 then Q else 2 * m * N * Q - Q

theorem solveBound_pos {Q m N : ℕ} (hm : m ≠ 0) (hN : 0 < N) :
    solveBound Q m N + Q = 2 * m * N * Q := by
  simp only [solveBound, hm, ↓reduceIte]
  have : Q ≤ 2 * m * N * Q := by
    have : 1 ≤ 2 * m * N := by
      have := Nat.pos_of_ne_zero hm
      nlinarith
    nlinarith
  omega

theorem solveBound_mono {Q m N N' : ℕ} (hN : N' ≤ N) : solveBound Q m N' ≤ solveBound Q m N := by
  unfold solveBound
  split
  · exact le_rfl
  · have : 2 * m * N' * Q ≤ 2 * m * N * Q := by
      apply Nat.mul_le_mul_right
      exact Nat.mul_le_mul_left _ hN
    omega

theorem le_solveBound_of_le {Q m N c : ℕ} (hm : m ≠ 0) (hN : 0 < N) (hc : c ≤ Q) :
    c ≤ solveBound Q m N := by
  have h := solveBound_pos (Q := Q) hm hN
  have : 2 * Q ≤ 2 * m * N * Q := by
    have : 1 ≤ m * N := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hm (by omega))
    nlinarith
  omega

/-- **Arithmetic of the branching step.** `k ≥ 2` branches over a subgroup of order `N'`, with
`k N' = N`. -/
theorem branch_arith {Q P E self m k N' : ℕ} (hQ : P + 2 * E ≤ Q) (hself : self ≤ P)
    (hk : 2 ≤ k) (hm : m ≠ 0) (hN' : 0 < N') :
    self + k * (E + solveBound Q m N') ≤ solveBound Q m (k * N') := by
  have h1 := solveBound_pos (Q := Q) hm hN'
  have h2 := solveBound_pos (Q := Q) hm (Nat.mul_pos (by omega) hN' : 0 < k * N')
  have e : 2 * m * (k * N') * Q = k * (2 * m * N' * Q) := by ring
  rw [e] at h2
  -- `k T' + k Q = k (2 m N' Q) = T + Q`
  have h3 : k * solveBound Q m N' + k * Q = solveBound Q m (k * N') + Q := by
    rw [h2, ← h1]; ring
  have h4 : P + k * E + Q ≤ k * Q := by nlinarith
  nlinarith

theorem sum_map_le_sum_map {α : Type} (l : List α) (f g : α → ℕ) (h : ∀ x ∈ l, f x ≤ g x) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons]
    have := h x List.mem_cons_self
    have := ih fun y hy => h y (List.mem_cons_of_mem _ hy)
    omega

/-- Sum of the bounds of a list of nonempty windows. -/
theorem sum_solveBound {Q N : ℕ} (hN : 0 < N) :
    ∀ os : List (List ℕ), (∀ o ∈ os, 0 < o.length) →
      (os.map fun o => solveBound Q o.length N).sum + os.length * Q =
        2 * (os.map List.length).sum * N * Q
  | [], _ => by simp
  | o :: os, h => by
    have ih := sum_solveBound (Q := Q) hN os fun o' ho' => h o' (List.mem_cons_of_mem _ ho')
    have ho := solveBound_pos (Q := Q) (m := o.length) (Nat.pos_iff_ne_zero.1 (h o
      List.mem_cons_self)) hN
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    nlinarith

/-- **Arithmetic of the sequential step.** At least two nonempty windows whose sizes add up to
`m`, each with overhead at most `E`. -/
theorem seq_arith {Q P E self N : ℕ} (hQ : P + 2 * E ≤ Q) (hself : self ≤ P) (hN : 0 < N)
    {os : List (List ℕ)} (hlen : 2 ≤ os.length) (hpos : ∀ o ∈ os, 0 < o.length)
    {f : List ℕ → ℕ} (hf : ∀ o ∈ os, f o ≤ E + solveBound Q o.length N) :
    self + (os.map f).sum ≤ solveBound Q (os.map List.length).sum N := by
  have hsum := sum_solveBound (Q := Q) hN os hpos
  have hle : (os.map f).sum ≤ os.length * E + (os.map fun o => solveBound Q o.length N).sum := by
    have := sum_map_le_sum_map os f (fun o => E + solveBound Q o.length N) hf
    simpa [List.sum_map_add, sum_map_const] using this
  have hm : (os.map List.length).sum ≠ 0 := by
    obtain ⟨o, ho⟩ : ∃ o, o ∈ os := List.exists_mem_of_length_pos (by omega)
    have := le_sum_of_mem_nat (List.mem_map_of_mem (f := List.length) ho)
    have := hpos o ho
    omega
  have htot := solveBound_pos (Q := Q) hm hN
  have h4 : P + os.length * E + Q ≤ os.length * Q := by nlinarith
  nlinarith

end GraphIso.Solver
