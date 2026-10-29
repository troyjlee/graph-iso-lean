module

public import GraphIso.Graph.LevelsProg

/-!
# The test for one pair of edges

For edges `{a, b}` of `X` and `{a', b'}` of `Y`, `edgeProg` computes the levels of the union
from the four roots, the generators of `A₀`, then `2n` layer steps, giving generators of
`A_{2n}`. It looks for a generator moving `a` to the other side and reads off the isomorphism
`v ↦ g v − n`.

**`RunsWithin.edgeProg`**: with the Schreier–Sims backend, for valid graph data with every
point reached, the result is `none` exactly when no isomorphism sends `{a, b}` to `{a', b'}`,
and otherwise lists the values of an isomorphism; the cost is at most `edgeCost n`.
-/

@[expose] public section

namespace GraphIso.Graph

open Equiv Cost Programs Sims Luks

/-! ### Models -/

/-- The generators of `A₀`. -/
def gens0Data (N a b c d : ℕ) : GensData :=
  [swapData N a b, swapData N c d, PermData.mul (swapData N a c) (swapData N b d)]

/-- The swap test: `g` moves `a` off the edge `{a, b}`. -/
def testB (a b : ℕ) (g : PermData) : Bool := !((get g.1 a == a) || (get g.1 a == b))

/-- One step of the search for a swapping generator. -/
def findStep (a b : ℕ) (acc : Option PermData) (g : PermData) : Option PermData :=
  match acc with
  | some _ => acc
  | none => if testB a b g then some g else none

/-- The first swapping generator. -/
def findB (a b : ℕ) (gs : GensData) : Option PermData := gs.foldl (findStep a b) none

/-- The values `g v − n` for `v < n`. -/
def isoArr (n : ℕ) (g : PermData) : Array ℕ := ((List.range n).map fun v => get g.1 v - n).toArray

theorem findStep_some (a b : ℕ) {g : PermData} :
    ∀ gs : GensData, gs.foldl (findStep a b) (some g) = some g
  | [] => rfl
  | _ :: gs => by rw [List.foldl_cons]; exact findStep_some a b gs

theorem findB_some {a b : ℕ} : ∀ {gs : GensData} {g : PermData}, findB a b gs = some g →
    g ∈ gs ∧ testB a b g = true
  | [], _, h => by simp [findB] at h
  | g' :: gs, g, h => by
    unfold findB at h
    rw [List.foldl_cons] at h
    by_cases ht : testB a b g' = true
    · rw [show findStep a b none g' = some g' by simp [findStep, ht], findStep_some] at h
      cases h
      exact ⟨List.mem_cons_self, ht⟩
    · rw [show findStep a b none g' = none by simp [findStep, ht]] at h
      obtain ⟨hm, ht'⟩ := findB_some h
      exact ⟨List.mem_cons_of_mem _ hm, ht'⟩

theorem findB_none {a b : ℕ} : ∀ {gs : GensData}, findB a b gs = none →
    ∀ g ∈ gs, testB a b g = false
  | [], _, g, hg => absurd hg (List.not_mem_nil)
  | g' :: gs, h, g, hg => by
    unfold findB at h
    rw [List.foldl_cons] at h
    by_cases ht : testB a b g' = true
    · rw [show findStep a b none g' = some g' by simp [findStep, ht], findStep_some] at h
      cases h
    · rw [show findStep a b none g' = none by simp [findStep, ht]] at h
      rcases List.mem_cons.1 hg with rfl | hg
      · simpa using ht
      · exact findB_none h g hg

theorem testB_iff {N a b : ℕ} {g : PermData} (hg : g.Valid N) (ha : a < N) :
    testB a b g = true ↔ ¬ EPar a b (PermData.denote N g) := by
  unfold testB EPar
  rw [get_fst_of_valid hg ha]
  simp

/-! ### Programs -/

section Prog

variable {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- The generators of `A₀`. -/
def gens0Prog (N a b c d : var .nat) : Prog S rec var Ty.gens :=
  .bind (swapProg N a b) fun s₁ => .bind (swapProg N c d) fun s₂ =>
  .bind (swapProg N a c) fun s₃ => .bind (swapProg N b d) fun s₄ =>
  .bind (permMul s₃ s₄) fun s₅ =>
  .bind (.op0 .nil) fun nl => .bind (.op2 .cons s₅ nl) fun l₁ => .bind (.op2 .cons s₂ l₁)
    fun l₂ => .op2 .cons s₁ l₂

/-- The swap test. -/
def testProg (a b : var .nat) (g : var Ty.perm) : Prog S rec var .bool :=
  .bind (permApply g a) fun ga => .bind (.op2 .natEq ga a) fun e₁ =>
  .bind (.op2 .natEq ga b) fun e₂ => .bind (.op2 .or e₁ e₂) fun o => .op1 .not o

/-- One step of the search. -/
def findStepProg (a b : var .nat) (acc : var (.option Ty.perm)) (g : var Ty.perm) :
    Prog S rec var (.option Ty.perm) :=
  .caseOption acc (.bind (testProg a b g) fun t => .ite t (.op1 .some g) (.ret acc))
    fun _ => .ret acc

/-- The first swapping generator. -/
def findProg (a b : var .nat) (gs : var Ty.gens) : Prog S rec var (.option Ty.perm) :=
  .bind (.op0 .none) fun nn => .foldList gs nn fun acc g => findStepProg a b acc g

/-- The values `g v − n`. -/
def isoArrProg (n : var .nat) (g : var Ty.perm) : Prog S rec var (.array .nat) :=
  .bind (.op1 .fst g) fun g₁ => .bind (.op1 .range n) fun rn =>
  .bind (mapList rn fun v => .bind (.op2 .arrayGet g₁ v) fun gv => .op2 .sub gv n) fun l =>
  .op1 .arrayOfList l

/-- **The test for the edges `{a, b}` and `{a', b'}`**, on the union `Z` of `N = 2n` points. -/
def edgeProg {D : Ty} (n N : var .nat) (Z : var Ty.graph) (a b a' b' : var .nat) :
    Prog (groupSig D) (Solver.Rec D) var (.option (.array .nat)) :=
  .bind (.op2 .add n a') fun c => .bind (.op2 .add n b') fun d =>
  .bind (.op0 .nil) fun nl => .bind (.op2 .cons d nl) fun l₁ => .bind (.op2 .cons c l₁) fun l₂ =>
  .bind (.op2 .cons b l₂) fun l₃ => .bind (.op2 .cons a l₃) fun roots =>
  .bind (levelsProg N Z roots) fun lev =>
  .bind (gens0Prog N a b c d) fun gs₀ =>
  .bind (.op1 .range N) fun rN =>
  .bind (.foldList rN gs₀ fun gs r => stepProg N Z lev r gs) fun gsN =>
  .bind (findProg a b gsN) fun found =>
  .caseOption found (.op0 .none) fun g => .bind (isoArrProg n g) fun arr => .op1 .some arr

end Prog

/-! ### Specifications -/

section Specs

variable {S : Signature} {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

theorem RunsWithin.gens0Prog (N a' b' c d : ℕ) (ha : a' < N) (hb : b' < N) (hc : c < N)
    (hd : d < N) :
    RunsWithin X body (Graph.gens0Prog N a' b' c d) (gens0Data N a' b' c d) (52 * N + 37) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.swapProg N a' b')
    run_step (RunsWithin.swapProg N c d)
    run_step (RunsWithin.swapProg N a' c)
    run_step (RunsWithin.swapProg N b' d)
    run_step (RunsWithin.permMul (valid_swapData ha hc) (valid_swapData hb hd))
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost]
    omega

theorem RunsWithin.testProg (a' b' : ℕ) (g : PermData) :
    RunsWithin X body (Graph.testProg a' b' g) (testB a' b' g) 6 := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.permApply g a')
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp [Prim.cost]

theorem RunsWithin.findStepProg (a' b' : ℕ) (acc : Option PermData) (g : PermData) :
    RunsWithin X body (Graph.findStepProg a' b' acc g) (findStep a' b' acc g) 9 := by
  rcases acc with _ | h
  · cases ht : testB a' b' g
    · apply RunsWithin.mono
      case h =>
        run_with RunsWithin.caseOption_none _
        run_step (RunsWithin.testProg a' b' g)
        rw [ht]
        run_with RunsWithin.ite_neg rfl _
        exact (RunsWithin.ret _).of_eq (by simp [findStep, ht])
      case hc =>
        omega
    · apply RunsWithin.mono
      case h =>
        run_with RunsWithin.caseOption_none _
        run_step (RunsWithin.testProg a' b' g)
        rw [ht]
        run_with RunsWithin.ite_pos rfl _
        exact RunsWithin.prim_le (by simp [Prim.eval, findStep, ht]) le_rfl
      case hc =>
        simp only [Prim.cost]
        omega
  · apply RunsWithin.mono
    case h =>
      run_with RunsWithin.caseOption_some _
      exact (RunsWithin.ret _).of_eq (by simp [findStep])
    case hc =>
      omega

theorem RunsWithin.findProg (a' b' : ℕ) (gs : GensData) :
    RunsWithin X body (Graph.findProg a' b' gs) (findB a' b' gs) (10 * gs.length + 1) := by
  have hfold := RunsWithin.foldList_of (X := X) (body := body) (a' := Ty.perm)
    (b' := .option Ty.perm) (cf := fun _ => 9) (F := findStep a' b') gs none
    fun acc g _ => RunsWithin.findStepProg a' b' acc g
  rw [sum_map_const] at hfold
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    exact hfold
  case hc =>
    simp only [Prim.cost]
    omega

theorem RunsWithin.isoArrProg (n : ℕ) (g : PermData) :
    RunsWithin X body (Graph.isoArrProg n g) (isoArr n g) (7 * n + 5) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.mapList_le (c := 2) fun v _ =>
      RunsWithin.bind_le (RunsWithin.prim _ _) (RunsWithin.prim_le rfl le_rfl) le_rfl)
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head_cons, List.length_map, List.length_range]
    omega

/-- A fold over `s, …, s + k − 1` whose body keeps an indexed invariant `I` within cost `c`, with
results given existentially. -/
theorem RunsWithin.foldList_range_exists {b' : Ty}
    {f : b'.denote → ℕ → Prog S (a, b) Ty.denote b'} {I : ℕ → b'.denote → Prop} {c : ℕ}
    (hf : ∀ j acc, I j acc → ∃ v, RunsWithin X body (f acc j) v c ∧ I (j + 1) v) :
    ∀ (k s : ℕ) (init : b'.denote), I s init →
      ∃ v, RunsWithin X body (.foldList (a := .nat) (List.range' s k) init f) v (k * (c + 1)) ∧
        I (s + k) v
  | 0, s, init, h => ⟨init, by simpa using RunsWithin.foldList_nil, h⟩
  | k + 1, s, init, h => by
    obtain ⟨v₁, h₁, hI₁⟩ := hf s init h
    obtain ⟨v, h₂, hI⟩ := foldList_range_exists hf k (s + 1) v₁ hI₁
    refine ⟨v, ?_, by rw [show s + (k + 1) = s + 1 + k by omega]; exact hI⟩
    rw [List.range'_succ]
    exact (RunsWithin.foldList_cons h₁ h₂).mono (by rw [Nat.succ_mul]; omega)

end Specs

/-! ### The initial generators -/

theorem gens0Data_spec {N : ℕ} {G : GraphData} {lev : Array ℕ} {a b c d : ℕ}
    (hR : Roots4 N G lev a b c d) {Δ : ℕ} (hG : G.ValidD Δ N) :
    GensData.AllValid N (gens0Data N a b c d) ∧
      GensData.denote N (gens0Data N a b c d) = AutR N G lev 0 := by
  have hac := valid_swapData hR.lt_a hR.lt_c
  have hbd := valid_swapData hR.lt_b hR.lt_d
  refine ⟨?_, ?_⟩
  · intro g hg
    simp only [gens0Data, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl
    · exact valid_swapData hR.lt_a hR.lt_b
    · exact valid_swapData hR.lt_c hR.lt_d
    · exact hac.mul hbd
  · rw [← closure_gens0 hR hG, GensData.denote]
    congr 1
    ext π
    simp only [GensData.denoteSet, gens0Data, List.mem_cons, List.not_mem_nil, or_false,
      Set.mem_ofPred_eq, gens0, Set.mem_insert_iff, Set.mem_singleton_iff]
    rw [← denote_swapData hR.lt_a hR.lt_b, ← denote_swapData hR.lt_c hR.lt_d,
      ← denote_swapData hR.lt_a hR.lt_c, ← denote_swapData hR.lt_b hR.lt_d,
      ← PermData.denote_mul hac hbd]
    constructor
    · rintro ⟨g, rfl | rfl | rfl, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    · rintro (rfl | rfl | rfl)
      · exact ⟨_, Or.inl rfl, rfl⟩
      · exact ⟨_, Or.inr (Or.inl rfl), rfl⟩
      · exact ⟨_, Or.inr (Or.inr rfl), rfl⟩

/-! ### The edge test -/

/-- The cost bound of one layer step with at most `genBound N` generators. -/
def layerCost (N : ℕ) : ℕ := stepCost N (genBound N)

/-- The cost bound of the edge test on `2n` points. -/
def edgeCost (n : ℕ) : ℕ :=
  levelsCost (2 * n) 4 + 52 * (2 * n) + 2 * n * (layerCost (2 * n) + 1) +
    10 * genBound (2 * n) + 9 * n + 60

theorem stepCost_mono {N L L' : ℕ} (h : L ≤ L') : stepCost N L ≤ stepCost N L' := by
  unfold stepCost inputCost
  gcongr

section Edge

variable {n : ℕ} {X Y : GraphData} {a b a' b' : ℕ} (hX : X.Valid n) (hY : Y.Valid n)
  (hab : Adj X a b) (hab' : Adj Y a' b')
  (hreach : ∀ v < 2 * n, get (unionLev n X Y a b a' b') v < 2 * n)

include hX hY hab hab' hreach in
/-- **The test for one pair of edges.** -/
theorem RunsWithin.edgeProg {N : ℕ} (hN : N = 2 * n) :
    ∃ res, RunsWithin ssCtx (luksBody Ty.unit Ty.denote)
        (Graph.edgeProg n N (GraphData.union n X Y) a b a' b') res (edgeCost n) ∧
      (res = none ↔ ¬ ∃ φ, IsIso n X Y φ ∧ SendsEdge n a b a' b' φ) ∧
      ∀ arr, res = some arr → arr.size = n ∧
        ∃ φ : Perm (Fin n), IsIso n X Y φ ∧ ∀ v < n, get arr v = act φ v := by
  subst hN
  have hZ := layered_union hX hY hab hab' hreach (by norm_num)
  have hR := roots4_union hX hY hab hab'
  have hvalid := valid_union hX hY
  have ha := hX.lt_left hab
  have hb := hX.lt a b hab
  have ha' := hY.lt_left hab'
  have hb' := hY.lt a' b' hab'
  obtain ⟨hv₀, hd₀⟩ := gens0Data_spec hR hvalid
  have hgb : (gens0Data (2 * n) a b (n + a') (n + b')).length ≤ genBound (2 * n) := by
    simp only [gens0Data, List.length_cons, List.length_nil, genBound, domBound]
    nlinarith
  -- the layer steps
  obtain ⟨gsN, hloop, hvN, hdN, hlN⟩ := RunsWithin.foldList_range_exists (X := ssCtx)
    (body := luksBody Ty.unit Ty.denote) (b' := Ty.gens)
    (f := fun gs r => Graph.stepProg (2 * n) (GraphData.union n X Y)
      (unionLev n X Y a b a' b') r gs)
    (I := fun r gs => GensData.AllValid (2 * n) gs ∧
      GensData.denote (2 * n) gs = AutR (2 * n) _ (unionLev n X Y a b a' b') r ∧
      gs.length ≤ genBound (2 * n)) (c := layerCost (2 * n))
    (fun r gs ⟨hv, hd, hl⟩ => by
      obtain ⟨gs', hrun, hv', hd', hl'⟩ := RunsWithin.stepProg hZ hR hv hd
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

end GraphIso.Graph
