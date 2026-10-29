module

public import GraphIso.Graph.Step

/-!
# Programs for the levels and the union

* `levelsProg N G roots` computes `levels N G roots` (`RunsWithin.levelsProg`): the initial
  levels, then a loop of relaxation passes until a fixpoint. Each pass costs at most
  `31 N + 14` for graph data of maximum degree three, and the loop is paid by the potential
  `(levPot + 1) · (31 N + 15)`, since every pass that changes the levels lowers their sum.
* `unionProg n X Y` computes the disjoint union `GraphData.union n X Y`.
-/

@[expose] public section

namespace GraphIso.Graph

open Equiv Cost Programs Sims

/-! ### Programs -/

section Prog

variable {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- One relaxation by the neighbour `u`. -/
def minStepProg (lev : var (.array .nat)) (m u : var .nat) : Prog S rec var .nat :=
  .bind (.op2 .arrayGet lev u) fun lu => .bind (.op0 (.natLit 1)) fun one =>
  .bind (.op2 .add lu one) fun x => .bind (.op2 .natLt x m) fun lt => .ite lt (.ret x) (.ret m)

/-- The relaxation at `v`. -/
def relaxAtProg (G : var Ty.graph) (lev : var (.array .nat)) (v : var .nat) :
    Prog S rec var .nat :=
  .bind (.op2 .arrayGet G v) fun ns => .bind (.op2 .arrayGet lev v) fun lv =>
  .foldList ns lv fun m u => minStepProg lev m u

/-- One relaxation pass, or `none` at a fixpoint. -/
def levStepProg (N : var .nat) (G : var Ty.graph) (lev : var (.array .nat)) :
    Prog S rec var (.option (.array .nat)) :=
  .bind (.op1 .range N) fun rN => .bind (mapList rN fun v => relaxAtProg G lev v) fun l =>
  .bind (.op1 .arrayOfList l) fun lev' => .bind (arrayNatBeq lev' lev) fun same =>
  .ite same (.op0 .none) (.op1 .some lev')

/-- The initial level of `v`. -/
def initAtProg (N : var .nat) (roots : var (.list .nat)) (v : var .nat) : Prog S rec var .nat :=
  .bind (memProg roots v) fun b => .ite b (.op0 (.natLit 0)) (.ret N)

/-- The initial levels. -/
def initLevProg (N : var .nat) (roots : var (.list .nat)) : Prog S rec var (.array .nat) :=
  .bind (.op1 .range N) fun rN => .bind (mapList rN fun v => initAtProg N roots v) fun l =>
  .op1 .arrayOfList l

/-- **The levels from the roots.** -/
def levelsProg (N : var .nat) (G : var Ty.graph) (roots : var (.list .nat)) :
    Prog S rec var (.array .nat) :=
  .bind (initLevProg N roots) fun l₀ => .loop l₀ fun lev => levStepProg N G lev

/-- Shift a list by `n`. -/
def shiftProg (n : var .nat) (l : var (.list .nat)) : Prog S rec var (.list .nat) :=
  mapList l fun x => .op2 .add x n

/-- **The disjoint union.** -/
def unionProg (n : var .nat) (X Y : var Ty.graph) : Prog S rec var Ty.graph :=
  .bind (.op1 .arrayToList X) fun Xl => .bind (.op1 .arrayToList Y) fun Yl =>
  .bind (mapList Yl fun l => shiftProg n l) fun Yl' =>
  .bind (.op2 .append Xl Yl') fun Zl => .op1 .arrayOfList Zl

end Prog

/-! ### Models -/

theorem min_eq_ite (m x : ℕ) : min m x = if x < m then x else m := by
  split <;> omega

theorem relaxAt_eq (G : GraphData) (lev : Array ℕ) (v : ℕ) :
    relaxAt G lev v = (nbrs G v).foldl (fun m u => if get lev u + 1 < m then get lev u + 1 else m)
      (get lev v) := by
  unfold relaxAt
  congr 1
  funext m u
  exact min_eq_ite _ _

theorem union_eq (n : ℕ) (X Y : GraphData) :
    (X.toList ++ Y.toList.map (·.map (· + n))).toArray = GraphData.union n X Y := by
  apply Array.ext'
  simp [GraphData.union]

/-! ### Specifications -/

section Specs

variable {S : Signature} {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

theorem RunsWithin.minStepProg (lev : Array ℕ) (m u : ℕ) :
    RunsWithin X body (Graph.minStepProg lev m u)
      (if get lev u + 1 < m then get lev u + 1 else m) 5 := by
  by_cases h : get lev u + 1 < m
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_with RunsWithin.ite_pos (show decide (get lev u + 1 < m) = true by simpa using h) _
      exact (RunsWithin.ret _).of_eq (by simp [h]; rfl)
    case hc =>
      simp [Prim.cost]
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_with RunsWithin.ite_neg (show decide (get lev u + 1 < m) = false by simpa using h) _
      exact (RunsWithin.ret _).of_eq (by simp [h])
    case hc =>
      simp [Prim.cost]

theorem RunsWithin.relaxAtProg {G : GraphData} (hG3 : ∀ u, (nbrs G u).length ≤ 3)
    (lev : Array ℕ) (v : ℕ) :
    RunsWithin X body (Graph.relaxAtProg G lev v) (relaxAt G lev v) 20 := by
  have hfold := RunsWithin.foldList_of (X := X) (body := body) (a' := .nat) (b' := .nat)
    (cf := fun _ => 5) (F := fun m u => if get lev u + 1 < m then get lev u + 1 else m)
    (nbrs G v) (get lev v) fun m u _ => RunsWithin.minStepProg lev m u
  rw [sum_map_const, ← relaxAt_eq] at hfold
  have := hG3 v
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact hfold
  case hc =>
    simp only [Prim.cost]
    omega

theorem RunsWithin.levStepProg {N : ℕ} {G : GraphData} (hG3 : ∀ u, (nbrs G u).length ≤ 3)
    (lev : Array ℕ) :
    RunsWithin X body (Graph.levStepProg N G lev) (levStep N G lev) (31 * N + 14) := by
  have hsize := size_relaxPass (N := N) (G := G) lev
  by_cases h : relaxPass N G lev = lev
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.mapList_le fun v _ => RunsWithin.relaxAtProg hG3 lev v)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.arrayNatBeq _ _)
      run_with RunsWithin.ite_pos (show (relaxPass N G lev == lev) = true by simp [h]) _
      exact RunsWithin.prim_le (by simp [Prim.eval, levStep, h]) le_rfl
    case hc =>
      simp only [Prim.cost, Prim.eval, Args.head_cons, List.length_map, List.length_range,
        List.size_toArray]
      omega
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.mapList_le fun v _ => RunsWithin.relaxAtProg hG3 lev v)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.arrayNatBeq _ _)
      run_with RunsWithin.ite_neg (show (relaxPass N G lev == lev) = false by simpa using h) _
      exact RunsWithin.prim_le (show some (relaxPass N G lev) = _ by simp [levStep, h]) le_rfl
    case hc =>
      simp only [Prim.cost, Prim.eval, Args.head_cons, List.length_map, List.length_range,
        List.size_toArray]
      omega

theorem RunsWithin.initAtProg (N : ℕ) (roots : List ℕ) (v : ℕ) :
    RunsWithin X body (Graph.initAtProg N roots v) (if v ∈ roots then 0 else N)
      (3 * roots.length + 3) := by
  by_cases h : v ∈ roots
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.memProg roots v)
      run_with RunsWithin.ite_pos (any_beq_iff.2 h) _
      exact RunsWithin.prim_le (by simp [Prim.eval, h]) le_rfl
    case hc =>
      simp only [Prim.cost]
      omega
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.memProg roots v)
      run_with RunsWithin.ite_neg (by
        rw [Bool.eq_false_iff]
        exact fun h' => h (any_beq_iff.1 h')) _
      exact (RunsWithin.ret _).of_eq (by simp [h])
    case hc =>
      omega

theorem RunsWithin.initLevProg (N : ℕ) (roots : List ℕ) :
    RunsWithin X body (Graph.initLevProg N roots) (initLev N roots)
      (N * (3 * roots.length + 6) + 2 * N + 4) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.mapList_le fun v _ => RunsWithin.initAtProg N roots v)
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head_cons, List.length_map, List.length_range]
    ring_nf
    omega

/-- The cost bound of the levels for `k` roots. -/
def levelsCost (N k : ℕ) : ℕ := N * (3 * k + 6) + 2 * N + 4 + (N * N + 1) * (31 * N + 15)

theorem RunsWithin.levelsProg {N : ℕ} {G : GraphData} (hG : G.Valid N) (roots : List ℕ) :
    RunsWithin X body (Graph.levelsProg N G roots) (levels N G roots)
      (levelsCost N roots.length) := by
  have hN : ∀ u v, Adj G u v → v < N := hG.lt
  have hloop := RunsWithin.loop_pot (X := X) (body := body) (f := Graph.levStepProg N G)
    (F := levStep N G) (I := LInv N G roots) (Φ := fun lev => (levPot N lev + 1) * (31 * N + 15))
    (fun lev hI => ⟨31 * N + 14, RunsWithin.levStepProg hG.deg lev, fun _ => by nlinarith,
      fun lev' hs => by
        have he : relaxPass N G lev ≠ lev := fun e => by simp [levStep, e] at hs
        have hl' : lev' = relaxPass N G lev := by
          simp only [levStep, he, ↓reduceIte, Option.some.injEq] at hs
          exact hs.symm
        subst hl'
        obtain ⟨hI', hle⟩ := hI.pass hN
        have := levPot_lt (size_relaxPass lev) hI.size hle he
        exact ⟨hI', by nlinarith⟩⟩)
    (N * N + 1 + (levPot N (initLev N roots) + 1) * (31 * N + 15)) (initLev N roots) linv_init
    (by nlinarith)
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
    have : (levPot N (initLev N roots) + 1) * (31 * N + 15) ≤ (N * N + 1) * (31 * N + 15) :=
      Nat.mul_le_mul_right _ (by omega)
    omega

theorem RunsWithin.shiftProg (n : ℕ) (l : List ℕ) :
    RunsWithin X body (Graph.shiftProg n l) (l.map (· + n)) (4 * l.length + 2) :=
  (RunsWithin.mapList_le (c := 1) fun x _ => RunsWithin.prim_le rfl le_rfl).mono (by omega)

theorem RunsWithin.unionProg {n : ℕ} {X' Y : GraphData} (hX : X'.Valid n) (hY : Y.Valid n) :
    RunsWithin X body (Graph.unionProg n X' Y) (GraphData.union n X' Y) (25 * n + 6) := by
  have hYl : ∀ l ∈ Y.toList, l.length ≤ 3 := by
    intro l hl
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hl
    have := hY.deg i
    simp only [Array.length_toList] at hi
    simpa [nbrs, Array.getD_eq_getD_getElem?, hi] using this
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.mapList_le (c := 14) fun l hl =>
      (RunsWithin.shiftProg n l).mono (by have := hYl l hl; omega))
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le (union_eq n X' Y) le_rfl
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head_cons, List.length_append, List.length_map,
      Array.length_toList, hX.size, hY.size]
    omega

end Specs

/-! ### Well-formedness -/

section Wf

variable {S : Signature} {rec : Ty × Ty} {var₁ var₂ : Ty → Type} {r : Bool}
  {Γ : WfCtx var₁ var₂}

theorem wf_levelsProg {N₁ : var₁ .nat} {N₂ : var₂ .nat} {G₁ : var₁ Ty.graph}
    {G₂ : var₂ Ty.graph} {R₁ : var₁ (.list .nat)} {R₂ : var₂ (.list .nat)}
    (hN : ⟨.nat, N₁, N₂⟩ ∈ Γ) (hG : ⟨Ty.graph, G₁, G₂⟩ ∈ Γ) (hR : ⟨.list .nat, R₁, R₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (levelsProg N₁ G₁ R₁) (levelsProg N₂ G₂ R₂) := by
  unfold levelsProg initLevProg initAtProg memProg levStepProg relaxAtProg minStepProg
    arrayNatBeq anyList allList mapList
  prog_wf

theorem wf_unionProg {n₁ : var₁ .nat} {n₂ : var₂ .nat} {X₁ Y₁ : var₁ Ty.graph}
    {X₂ Y₂ : var₂ Ty.graph} (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (hX : ⟨Ty.graph, X₁, X₂⟩ ∈ Γ)
    (hY : ⟨Ty.graph, Y₁, Y₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (unionProg n₁ X₁ Y₁) (unionProg n₂ X₂ Y₂) := by
  unfold unionProg shiftProg mapList
  prog_wf

end Wf

end GraphIso.Graph
