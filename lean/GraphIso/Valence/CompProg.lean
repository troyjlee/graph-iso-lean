module

public import GraphIso.Valence.Validate
public import GraphIso.Graph.CompProg

/-!
# Costs of the component programs for maximum degree `Δ`

The component programs of `GraphIso/Graph/CompProg.lean` (`compsProg`, `subGProg`, `glueProg`)
do not depend on the degree. These are the cost bounds of the components and of the
component data for maximum degree `Δ` (gluing is degree-free):

* one step of the component fold costs at most `compStepCost Δ N`, the components
  `compsCost Δ N`;
* the component data on `k` points cost at most `subGCost Δ k = k (Δ (9 k + 7) + 7) + 4`.
-/

@[expose] public section

namespace GraphIso.Graph.Valence

open Equiv Cost Programs Sims

/-- The cost bound of one step of the component fold. -/
def compStepCost (Δ N : ℕ) : ℕ := levelsCost Δ N 1 + 12 * N + 20

/-- The cost bound of the components. -/
def compsCost (Δ N : ℕ) : ℕ := N * (compStepCost Δ N + 1) + 2 * N + 4

/-- The cost bound of the component data on `k` points. -/
def subGCost (Δ k : ℕ) : ℕ := k * (Δ * (9 * k + 7) + 7) + 4

section Specs

variable {S : Signature} {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

theorem RunsWithin.compStepProg {Δ N : ℕ} {G : GraphData} (hG : G.ValidD Δ N)
    (acc : List (List ℕ)) {u : ℕ} (hu : u ≤ N) :
    RunsWithin X body (Graph.compStepProg N G acc u) (compStep N G acc u)
      (compStepCost Δ N) := by
  have hany := RunsWithin.anyList_le (X := X) (body := body) (a' := .nat) (c := 2)
    (xs := List.range u)
    (P := fun v => decide (get (levels N G [u]) v < N)) fun v _ =>
      RunsWithin.levLtProg _ N v
  by_cases hb : ((List.range u).any fun v => decide (get (levels N G [u]) v < N)) = true
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.levelsProg hG _)
      run_step (RunsWithin.prim _ _)
      run_step hany
      run_with RunsWithin.ite_pos hb _
      exact (RunsWithin.ret (t := .list (.list .nat)) acc).of_eq
        (by simp only [compStep, hb, ↓reduceIte])
    case hc =>
      simp only [Prim.cost, Prim.eval, Args.head_cons, List.length_range, List.length_cons,
        List.length_nil, Nat.zero_add, compStepCost]
      omega
  · have hb' : ((List.range u).any fun v => decide (get (levels N G [u]) v < N)) = false := by
      simpa using hb
    have hfil := Luks.RunsWithin.filterList (X := X) (body := body) (a' := .nat) (c := 2)
      (xs := List.range N)
      (P := fun v => decide (get (levels N G [u]) v < N)) fun v _ =>
        RunsWithin.levLtProg _ N v
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.levelsProg hG _)
      run_step (RunsWithin.prim _ _)
      run_step hany
      run_with RunsWithin.ite_neg hb' _
      run_step (RunsWithin.prim _ _)
      run_step hfil
      exact RunsWithin.prim_le (by simp only [Prim.eval, compStep, hb']; rfl) le_rfl
    case hc =>
      simp only [Prim.cost, Prim.eval, Args.head_cons, List.length_range, List.length_cons,
        List.length_nil, Nat.zero_add, compStepCost]
      omega

theorem RunsWithin.compsProg {Δ N : ℕ} {G : GraphData} (hG : G.ValidD Δ N) :
    RunsWithin X body (Graph.compsProg N G) (comps N G) (compsCost Δ N) := by
  have hfold := RunsWithin.foldList_of (X := X) (body := body) (a' := .nat)
    (b' := .list (.list .nat)) (cf := fun _ => compStepCost Δ N) (F := compStep N G)
    (List.range N) [] fun acc u hu =>
      RunsWithin.compStepProg hG acc (Nat.le_of_lt (List.mem_range.1 hu))
  rw [sum_map_const, List.length_range] at hfold
  have hlen : ((List.range N).foldl (compStep N G) []).length ≤ N := by
    rw [← List.length_reverse, comps_eq_fold]
    exact length_comps_le
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step hfold
    exact RunsWithin.prim_le (comps_eq_fold N G) le_rfl
  case hc =>
    simp only [Prim.cost, Args.head_cons, compsCost]
    omega

theorem RunsWithin.subRowProg {Δ : ℕ} {G : GraphData} (hGd : ∀ u, (nbrs G u).length ≤ Δ)
    (cs : List ℕ) (u : ℕ) :
    RunsWithin X body (Graph.subRowProg G cs u) ((nbrs G u).map cs.idxOf)
      (Δ * (9 * cs.length + 7) + 3) := by
  have hmap := RunsWithin.mapList_le (X := X) (body := body) (a' := .nat) (b' := .nat)
    (xs := nbrs G u)
    (c := 9 * cs.length + 4) (F := cs.idxOf) fun w _ => RunsWithin.idxOfProg cs w
  have h : (nbrs G u).length * (9 * cs.length + 4 + 3) ≤ Δ * (9 * cs.length + 7) :=
    Nat.mul_le_mul (hGd u) (by omega)
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    exact hmap
  case hc =>
    simp only [Prim.cost]
    omega

theorem RunsWithin.subGProg {Δ : ℕ} {G : GraphData} (hGd : ∀ u, (nbrs G u).length ≤ Δ)
    (cs : List ℕ) :
    RunsWithin X body (Graph.subGProg G cs) (subG G cs) (subGCost Δ cs.length) := by
  have hmap := RunsWithin.mapList_le (X := X) (body := body) (a' := .nat) (b' := .list .nat)
    (xs := cs)
    (c := Δ * (9 * cs.length + 7) + 3) (F := fun u => (nbrs G u).map cs.idxOf) fun u _ =>
      RunsWithin.subRowProg hGd cs u
  apply RunsWithin.mono
  case h =>
    run_step hmap
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, Args.head_cons, List.length_map, subGCost]
    have : cs.length * (Δ * (9 * cs.length + 7) + 3 + 3) + cs.length =
        cs.length * (Δ * (9 * cs.length + 7) + 7) := by ring
    omega

end Specs

theorem subGCost_mono {Δ k n : ℕ} (h : k ≤ n) : subGCost Δ k ≤ subGCost Δ n := by
  unfold subGCost
  gcongr

end GraphIso.Graph.Valence
