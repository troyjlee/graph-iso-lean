module

public import GraphIso.Valence.StepProg

/-!
# Costs of the lifts and twin swaps for maximum degree `Δ`

The lift and twin programs of `GraphIso/Graph/LiftProg.lean` (`classProg`, `liftBProg`,
`liftArrProg`, `liftProg`, `twinInnerProg`, `twinsProg`) do not depend on the degree, and their
values are given there (`liftDataB`, `twinGens`). These are their cost bounds for maximum
degree `Δ`, with `M` points of level `r + 1`:

* the lift at one point costs at most `cL Δ M = (2 cE Δ + 28) M + 10 Δ + 22`;
* one step of the twin fold costs at most `cT Δ N = 10 N + 6 Δ² + 12 Δ + 15`.
-/

@[expose] public section

namespace GraphIso.Graph.Valence

open Equiv Cost Programs Sims

/-- The cost bound of the lift at one point, with `M` points of level `r + 1`. -/
def cL (Δ M : ℕ) : ℕ := (2 * cE Δ + 28) * M + 10 * Δ + 22

/-- The cost bound of one step of the inner twin fold. -/
def cT (Δ N : ℕ) : ℕ := 10 * N + 6 * Δ * Δ + 12 * Δ + 15

/-- The cost bound of the lift data. -/
def liftCost (Δ N M : ℕ) : ℕ := 2 * (N * (cL Δ M + 3) + 2 * N + 4) + 3

/-- The cost bound of the twin transpositions. -/
def twinsCost (Δ N M : ℕ) : ℕ := M * (M * (cT Δ N + 1) + 6 * Δ + 4) + 1

section Specs

variable {S : Signature} {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

variable {Δ : ℕ} {G : GraphData} (hGd : ∀ u, (nbrs G u).length ≤ Δ)
include hGd

theorem RunsWithin.classProg (lev : Array ℕ) (r : ℕ) (New : List ℕ) {T : List ℕ}
    (hT : T.length ≤ Δ) :
    RunsWithin X body (Graph.classProg G lev r New T) (classB G lev r New T)
      (New.length * (cE Δ + 4) + 2) :=
  Luks.RunsWithin.filterList (a' := .nat) fun u _ => RunsWithin.nbEqProg hGd lev r hT u

theorem RunsWithin.liftBProg (lev : Array ℕ) (r : ℕ) (New : List ℕ) (f : Array ℕ) (w : ℕ) :
    RunsWithin X body (Graph.liftBProg G lev r New f w) (liftB G lev r New f w)
      (cL Δ New.length) := by
  have h₁ := hGd w
  have h₂ := length_nbL_le G lev r w
  by_cases hl : get lev w = r + 1
  · have hT : (mapGet f (nbL G lev r w)).length ≤ Δ := by
      simp only [mapGet, List.length_map]
      omega
    have c₁ := length_classB_le G lev r New (mapGet f (nbL G lev r w))
    have c₂ := length_classB_le G lev r New (nbL G lev r w)
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_with RunsWithin.ite_pos (show (get lev w == r + 1) = true by simp [hl]) _
      run_step (RunsWithin.nbLProg G lev r w)
      run_step (RunsWithin.mapGetProg f _)
      run_step (RunsWithin.classProg hGd lev r New hT)
      run_step (RunsWithin.classProg hGd lev r New (by omega))
      run_step (RunsWithin.idxOfProg _ w)
      exact (RunsWithin.getDProg _ _ w).of_eq (by simp [liftB, hl])
    case hc =>
      simp only [Prim.cost, cL]
      nlinarith
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_with RunsWithin.ite_neg (show (get lev w == r + 1) = false by simpa using hl) _
      exact RunsWithin.prim_le (show get f w = _ by simp [liftB, hl]) le_rfl
    case hc =>
      simp only [Prim.cost, cL]
      omega

theorem RunsWithin.liftArrProg (lev : Array ℕ) (N r : ℕ) (New : List ℕ) (f : Array ℕ) :
    RunsWithin X body (Graph.liftArrProg G lev N r New f)
      ((List.range N).map (liftB G lev r New f)).toArray
      (N * (cL Δ New.length + 3) + 2 * N + 4) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.mapList_le fun w _ => RunsWithin.liftBProg hGd lev r New f w)
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head_cons, List.length_map, List.length_range]
    omega

theorem RunsWithin.liftProg (lev : Array ℕ) (N r : ℕ) (New : List ℕ) (d : PermData) :
    RunsWithin X body (Graph.liftProg G lev N r New d) (liftDataB G lev N r New d)
      (liftCost Δ N New.length) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.liftArrProg hGd lev N r New d.1)
    run_step (RunsWithin.liftArrProg hGd lev N r New d.2)
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, liftCost]
    omega

theorem RunsWithin.twinInnerProg (lev : Array ℕ) (N r w : ℕ) (acc : GensData) (w' : ℕ) :
    RunsWithin X body (Graph.twinInnerProg G lev N r w (nbL G lev r w) acc w')
      (twinInner G lev N r w acc w') (cT Δ N) := by
  have h₁ := hGd w
  have h₂ := length_nbL_le G lev r w
  have h₃ := hGd w'
  have h₄ := length_nbL_le G lev r w'
  have hse := seteq_cost_le (l₁ := nbL G lev r w) (l₂ := nbL G lev r w') (h₂.trans h₁)
    (h₄.trans h₃)
  by_cases he : w = w'
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_with RunsWithin.ite_pos (by simp [Prim.eval, he]) _
      exact (RunsWithin.ret _).of_eq (by simp [twinInner, he])
    case hc =>
      simp only [Prim.cost, cT]
      omega
  · cases hb : seteqB (nbL G lev r w) (nbL G lev r w')
    · apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.ite_neg (by simp [Prim.eval, he]) _
        run_step (RunsWithin.nbLProg G lev r w')
        run_step (RunsWithin.seteqProg _ _)
        rw [hb]
        run_with RunsWithin.ite_neg rfl _
        exact (RunsWithin.ret _).of_eq (by simp [twinInner, he, hb])
      case hc =>
        simp only [Prim.cost, cT]
        omega
    · apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.ite_neg (by simp [Prim.eval, he]) _
        run_step (RunsWithin.nbLProg G lev r w')
        run_step (RunsWithin.seteqProg _ _)
        rw [hb]
        run_with RunsWithin.ite_pos rfl _
        run_step (RunsWithin.swapProg N w w')
        exact RunsWithin.prim_le (by simp [Prim.eval, twinInner, he, hb]) le_rfl
      case hc =>
        simp only [Prim.cost, cT]
        omega

theorem RunsWithin.twinsProg (lev : Array ℕ) (N r : ℕ) (New : List ℕ) :
    RunsWithin X body (Graph.twinsProg G lev N r New) (twinGens G lev N r New)
      (twinsCost Δ N New.length) := by
  have hin : ∀ (w : ℕ) (acc : GensData), RunsWithin X body
      (.bind (Graph.nbLProg G lev r w) fun nw => .foldList (a := .nat) New acc fun acc w' =>
        Graph.twinInnerProg G lev N r w nw acc w')
      (New.foldl (twinInner G lev N r w) acc) (New.length * (cT Δ N + 1) + 6 * Δ + 3) := by
    intro w acc
    have hfold := RunsWithin.foldList_of (X := X) (body := body) (a' := .nat) (b' := Ty.gens)
      (cf := fun _ => cT Δ N) (F := twinInner G lev N r w) New acc
      fun acc w' _ => RunsWithin.twinInnerProg hGd lev N r w acc w'
    rw [sum_map_const] at hfold
    have h₁ := hGd w
    refine RunsWithin.bind_le (RunsWithin.nbLProg G lev r w) hfold ?_
    omega
  have hfold := RunsWithin.foldList_of (X := X) (body := body) (a' := .nat) (b' := Ty.gens)
    (cf := fun _ => New.length * (cT Δ N + 1) + 6 * Δ + 3)
    (F := fun acc w => New.foldl (twinInner G lev N r w) acc) New []
    fun acc w _ => hin w acc
  rw [sum_map_const] at hfold
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    exact hfold
  case hc =>
    simp only [Prim.cost, twinsCost]
    have : New.length * (New.length * (cT Δ N + 1) + 6 * Δ + 3 + 1) =
        New.length * (New.length * (cT Δ N + 1) + 6 * Δ + 4) := by ring
    omega

end Specs

end GraphIso.Graph.Valence
