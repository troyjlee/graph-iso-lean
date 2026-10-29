module

public import GraphIso.Valence.Step
public import GraphIso.Graph.EdgeProg

/-!
# The test for one pair of edges, for maximum degree `Δ`

For edges `{a, b}` of `X` and `{a', b'}` of `Y`, `edgeProg Δ` computes the levels of the union
from the four roots, the generators of `A₀`, then `2n` layer steps (`stepProg Δ`), giving
generators of `A_{2n}`. It looks for a generator moving `a` to the other side and reads off the
isomorphism `v ↦ g v − n`. Apart from the layer step, it is milestone 4's `edgeProg`.

**`RunsWithin.edgeProg`**: with the Schreier–Sims backend, for valid graph data of maximum
degree `Δ ≥ 2` with every point reached, and a constant `c ≥ 1` with `LayerPrim Δ c` for the
string-isomorphism calls, the result is `none` exactly when no isomorphism sends `{a, b}` to
`{a', b'}`, and otherwise lists the values of an isomorphism; the cost is at most
`edgeCost Δ c n`.
-/

@[expose] public section

namespace GraphIso.Graph.Valence

open Equiv Cost Programs Sims Luks

/-! ### The program -/

section Prog

variable {var : Ty → Type}

/-- **The test for the edges `{a, b}` and `{a', b'}`**, on the union `Z` of `N = 2n` points. -/
def edgeProg (Δ : ℕ) {D : Ty} (n N : var .nat) (Z : var Ty.graph) (a b a' b' : var .nat) :
    Prog (groupSig D) (Solver.Rec D) var (.option (.array .nat)) :=
  .bind (.op2 .add n a') fun c => .bind (.op2 .add n b') fun d =>
  .bind (.op0 .nil) fun nl => .bind (.op2 .cons d nl) fun l₁ => .bind (.op2 .cons c l₁) fun l₂ =>
  .bind (.op2 .cons b l₂) fun l₃ => .bind (.op2 .cons a l₃) fun roots =>
  .bind (levelsProg N Z roots) fun lev =>
  .bind (gens0Prog N a b c d) fun gs₀ =>
  .bind (.op1 .range N) fun rN =>
  .bind (.foldList rN gs₀ fun gs r => stepProg Δ N Z lev r gs) fun gsN =>
  .bind (findProg a b gsN) fun found =>
  .caseOption found (.op0 .none) fun g => .bind (isoArrProg n g) fun arr => .op1 .some arr

end Prog

/-! ### The edge test -/

/-- The cost bound of one layer step with at most `genBound Δ N` generators. -/
def layerCost (Δ c N : ℕ) : ℕ := stepCost Δ c N (genBound Δ N)

/-- The cost bound of the edge test on `2n` points. -/
def edgeCost (Δ c n : ℕ) : ℕ :=
  levelsCost Δ (2 * n) 4 + 52 * (2 * n) + 2 * n * (layerCost Δ c (2 * n) + 1) +
    10 * genBound Δ (2 * n) + 9 * n + 60

section Edge

variable {Δ c n : ℕ} {X Y : GraphData} {a b a' b' : ℕ} (hX : X.ValidD Δ n) (hY : Y.ValidD Δ n)
  (hΔ₂ : 2 ≤ Δ) (hc : LayerPrim Δ c) (hc1 : 1 ≤ c) (hab : Adj X a b) (hab' : Adj Y a' b')
  (hreach : ∀ v < 2 * n, get (unionLev n X Y a b a' b') v < 2 * n)

include hX hY hΔ₂ hc hc1 hab hab' hreach in
/-- **The test for one pair of edges.** -/
theorem RunsWithin.edgeProg {N : ℕ} (hN : N = 2 * n) :
    ∃ res, RunsWithin ssCtx (luksBody Ty.unit Ty.denote)
        (Valence.edgeProg Δ n N (GraphData.union n X Y) a b a' b') res (edgeCost Δ c n) ∧
      (res = none ↔ ¬ ∃ φ, IsIso n X Y φ ∧ SendsEdge n a b a' b' φ) ∧
      ∀ arr, res = some arr → arr.size = n ∧
        ∃ φ : Perm (Fin n), IsIso n X Y φ ∧ ∀ v < n, get arr v = act φ v := by
  subst hN
  have hZ := layered_union hX hY hab hab' hreach hΔ₂
  have hR := roots4_union hX hY hab hab'
  have hvalid := valid_union hX hY
  have ha := hX.lt_left hab
  have hb := hX.lt a b hab
  have ha' := hY.lt_left hab'
  have hb' := hY.lt a' b' hab'
  obtain ⟨hv₀, hd₀⟩ := gens0Data_spec hR hvalid
  have hgb : (gens0Data (2 * n) a b (n + a') (n + b')).length ≤ genBound Δ (2 * n) := by
    have h1 : 1 ≤ (2 * n + 1) ^ Δ := Nat.one_le_pow _ _ (by omega)
    simp only [gens0Data, List.length_cons, List.length_nil, genBound, domBound]
    nlinarith
  -- the layer steps
  obtain ⟨gsN, hloop, hvN, hdN, hlN⟩ := RunsWithin.foldList_range_exists (X := ssCtx)
    (body := luksBody Ty.unit Ty.denote) (b' := Ty.gens)
    (f := fun gs r => Valence.stepProg Δ (2 * n) (GraphData.union n X Y)
      (unionLev n X Y a b a' b') r gs)
    (I := fun r gs => GensData.AllValid (2 * n) gs ∧
      GensData.denote (2 * n) gs = AutR (2 * n) _ (unionLev n X Y a b a' b') r ∧
      gs.length ≤ genBound Δ (2 * n)) (c := layerCost Δ c (2 * n))
    (fun r gs ⟨hv, hd, hl⟩ => by
      obtain ⟨gs', hrun, hv', hd', hl'⟩ := RunsWithin.stepProg hZ hR hc hc1 hv hd
      exact ⟨gs', hrun.mono (stepCost_mono hl), hv', hd', hl'⟩)
    (2 * n) 0 _ ⟨hv₀, hd₀, hgb⟩
  rw [Nat.zero_add] at hdN
  rw [← List.range_eq_range'] at hloop
  have hcrit := iso_iff_exists_gen hX hY hab hab' hreach (gens := GensData.denoteSet (2 * n) gsN)
    hdN
  have hfind := RunsWithin.findProg (X := ssCtx) (body := luksBody Ty.unit Ty.denote) a b gsN
  have haN : a < 2 * n := by omega
  rcases hfound : findB a b gsN with _ | g
  · refine ⟨none, ?_, ⟨fun _ => ?_, fun _ => rfl⟩, fun arr h => absurd h (by simp)⟩
    · rw [hfound] at hfind
      apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.levelsProg hvalid _)
        run_step (RunsWithin.gens0Prog (2 * n) a b (n + a') (n + b') haN (by omega) (by omega)
          (by omega))
        run_step (RunsWithin.prim _ _)
        run_step hloop
        run_step hfind
        run_with RunsWithin.caseOption_none _
        exact RunsWithin.prim_le rfl le_rfl
      case hc =>
        simp only [Prim.cost, Prim.eval, Args.head_cons, List.length_cons, List.length_nil,
          edgeCost, Nat.zero_add, Nat.reduceAdd]
        omega
    · rw [hcrit]
      rintro ⟨π, ⟨g, hg, rfl⟩, hE⟩
      have := findB_none hfound g hg
      rw [← Bool.not_eq_true, testB_iff (hvN g hg) haN] at this
      exact this hE
  · obtain ⟨hgm, hgt⟩ := findB_some hfound
    have hgA : PermData.denote (2 * n) g ∈ AutR (2 * n) _ (unionLev n X Y a b a' b') (2 * n) :=
      hdN ▸ GensData.mem_denote_of_mem hgm
    have hE := (testB_iff (hvN g hgm) haN).1 hgt
    obtain ⟨φ, hφ, hiso, hsend⟩ := exists_iso_of_swap hX hY hab hab' hreach hgA hE
    refine ⟨some (isoArr n g), ?_, ⟨fun h => absurd h (by simp),
      fun h => absurd ⟨φ, hiso, hsend⟩ h⟩, fun arr harr => ?_⟩
    · rw [hfound] at hfind
      apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.levelsProg hvalid _)
        run_step (RunsWithin.gens0Prog (2 * n) a b (n + a') (n + b') haN (by omega) (by omega)
          (by omega))
        run_step (RunsWithin.prim _ _)
        run_step hloop
        run_step hfind
        run_with RunsWithin.caseOption_some _
        run_step (RunsWithin.isoArrProg n g)
        exact RunsWithin.prim_le rfl le_rfl
      case hc =>
        simp only [Prim.cost, Prim.eval, Args.head_cons, List.length_cons, List.length_nil,
          edgeCost, Nat.zero_add, Nat.reduceAdd]
        omega
    · cases harr
      refine ⟨by simp [isoArr], φ, hiso, fun v hv => ?_⟩
      rw [hφ v hv, ← get_fst_of_valid (hvN g hgm) (by omega)]
      simp [isoArr, get, hv]

end Edge

end GraphIso.Graph.Valence
