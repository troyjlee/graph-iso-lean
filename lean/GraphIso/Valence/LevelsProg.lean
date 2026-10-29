module

public import GraphIso.Graph.LevelsProg

/-!
# Costs of the levels and the union for maximum degree `Δ`

The programs `levelsProg` and `unionProg` of `GraphIso/Graph/LevelsProg.lean` do not depend on
the degree; their cost bounds there are for maximum degree three. These are the bounds for
maximum degree `Δ`:

* a relaxation at one point costs at most `6 Δ + 2`, a pass `(6 Δ + 13) N + 14`;
* the levels cost at most `levelsCost Δ N k` for `k` roots;
* the union of two graphs on `n` points costs at most `(4 Δ + 13) n + 6`.
-/

@[expose] public section

namespace GraphIso.Graph.Valence

open Equiv Cost Programs Sims

section Specs

variable {S : Signature} {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

theorem RunsWithin.relaxAtProg {Δ : ℕ} {G : GraphData} (hGd : ∀ u, (nbrs G u).length ≤ Δ)
    (lev : Array ℕ) (v : ℕ) :
    RunsWithin X body (Graph.relaxAtProg G lev v) (relaxAt G lev v) (6 * Δ + 2) := by
  have hfold := RunsWithin.foldList_of (X := X) (body := body) (a' := .nat) (b' := .nat)
    (cf := fun _ => 5) (F := fun m u => if get lev u + 1 < m then get lev u + 1 else m)
    (nbrs G v) (get lev v) fun m u _ => RunsWithin.minStepProg lev m u
  rw [sum_map_const, ← relaxAt_eq] at hfold
  have := hGd v
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact hfold
  case hc =>
    simp only [Prim.cost]
    omega

theorem RunsWithin.levStepProg {Δ N : ℕ} {G : GraphData} (hGd : ∀ u, (nbrs G u).length ≤ Δ)
    (lev : Array ℕ) :
    RunsWithin X body (Graph.levStepProg N G lev) (levStep N G lev) ((6 * Δ + 13) * N + 14) := by
  have hsize := size_relaxPass (N := N) (G := G) lev
  by_cases h : relaxPass N G lev = lev
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.mapList_le fun v _ => RunsWithin.relaxAtProg hGd lev v)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.arrayNatBeq _ _)
      run_with RunsWithin.ite_pos (show (relaxPass N G lev == lev) = true by simp [h]) _
      exact RunsWithin.prim_le (by simp [Prim.eval, levStep, h]) le_rfl
    case hc =>
      simp only [Prim.cost, Prim.eval, Args.head_cons, List.length_map, List.length_range,
        List.size_toArray]
      ring_nf
      omega
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.mapList_le fun v _ => RunsWithin.relaxAtProg hGd lev v)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.arrayNatBeq _ _)
      run_with RunsWithin.ite_neg (show (relaxPass N G lev == lev) = false by simpa using h) _
      exact RunsWithin.prim_le (show some (relaxPass N G lev) = _ by simp [levStep, h]) le_rfl
    case hc =>
      simp only [Prim.cost, Prim.eval, Args.head_cons, List.length_map, List.length_range,
        List.size_toArray]
      ring_nf
      omega

/-- The cost bound of the levels for `k` roots and maximum degree `Δ`. -/
def levelsCost (Δ N k : ℕ) : ℕ :=
  N * (3 * k + 6) + 2 * N + 4 + (N * N + 1) * ((6 * Δ + 13) * N + 15)

theorem RunsWithin.levelsProg {Δ N : ℕ} {G : GraphData} (hG : G.ValidD Δ N) (roots : List ℕ) :
    RunsWithin X body (Graph.levelsProg N G roots) (levels N G roots)
      (levelsCost Δ N roots.length) := by
  have hN : ∀ u v, Adj G u v → v < N := hG.lt
  have hloop := RunsWithin.loop_pot (X := X) (body := body) (f := Graph.levStepProg N G)
    (F := levStep N G) (I := LInv N G roots)
    (Φ := fun lev => (levPot N lev + 1) * ((6 * Δ + 13) * N + 15))
    (fun lev hI => ⟨(6 * Δ + 13) * N + 14, RunsWithin.levStepProg hG.deg lev,
      fun _ => le_trans (by omega) (Nat.le_mul_of_pos_left _ (Nat.succ_pos _)), fun lev' hs => by
        have he : relaxPass N G lev ≠ lev := fun e => by simp [levStep, e] at hs
        have hl' : lev' = relaxPass N G lev := by
          simp only [levStep, he, ↓reduceIte, Option.some.injEq] at hs
          exact hs.symm
        subst hl'
        obtain ⟨hI', hle⟩ := hI.pass hN
        have := levPot_lt (size_relaxPass lev) hI.size hle he
        have h1 := Nat.mul_le_mul_right ((6 * Δ + 13) * N + 15)
          (show levPot N (relaxPass N G lev) + 1 + 1 ≤ levPot N lev + 1 by omega)
        rw [Nat.add_mul, one_mul] at h1
        exact ⟨hI', by omega⟩⟩)
    (N * N + 1 + (levPot N (initLev N roots) + 1) * ((6 * Δ + 13) * N + 15)) (initLev N roots)
    linv_init (by nlinarith)
  have hpot : levPot N (initLev N roots) < N * N + 1 :=
    Nat.lt_succ_of_le (levPot_le (linv_init (G := G)).le)
  obtain ⟨-, hfix⟩ := iter_levStep hN (N * N + 1) _ linv_init hpot
  rw [iter_eq_of_fix (N * N + 1) _ hfix _ (by omega)] at hloop
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.initLevProg N roots)
    exact hloop
  case hc =>
    unfold levelsCost
    have : (levPot N (initLev N roots) + 1) * ((6 * Δ + 13) * N + 15) ≤
        (N * N + 1) * ((6 * Δ + 13) * N + 15) :=
      Nat.mul_le_mul_right _ (by omega)
    omega

theorem RunsWithin.unionProg {Δ n : ℕ} {X' Y : GraphData} (hX : X'.ValidD Δ n)
    (hY : Y.ValidD Δ n) :
    RunsWithin X body (Graph.unionProg n X' Y) (GraphData.union n X' Y) ((4 * Δ + 13) * n + 6) := by
  have hYl : ∀ l ∈ Y.toList, l.length ≤ Δ := by
    intro l hl
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hl
    have := hY.deg i
    simp only [Array.length_toList] at hi
    simpa [nbrs, Array.getD_eq_getD_getElem?, hi] using this
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.mapList_le (c := 4 * Δ + 2) fun l hl =>
      (RunsWithin.shiftProg n l).mono (by have := hYl l hl; omega))
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le (union_eq n X' Y) le_rfl
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head_cons, List.length_append, List.length_map,
      Array.length_toList, hX.size, hY.size]
    ring_nf
    omega

end Specs

end GraphIso.Graph.Valence
