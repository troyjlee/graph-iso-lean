module

public import GraphIso.Graph.LiftProg
public import GraphIso.Solver.Luks

/-!
# One layer step

`stepProg N G lev r gs` runs inside the procedure `luksBody`:

1. `stepInputProg` builds the string-isomorphism instance on `D = N + m` points, `m` the number
   of nonempty subsets of level `r` with at most three points: the layer string `xArr` as both
   strings, the window of the subsets, the identity, and the induced generators (`stepInput`).
2. `solveEntry` solves it with Luks's strategy.
3. `stepOutProg` truncates the answer's generators to the first `N` points, lifts them, and adds
   the twin transpositions.

**`RunsWithin.stepProg`**: with the Schreier–Sims backend, if `gs` generates `A_r` then the
step returns valid generators of `A_{r+1}`, at most `genBound N` of them, at cost at most
`stepCost N |gs|`.
-/

@[expose] public section

namespace GraphIso.Graph

open Equiv Cost Programs Sims Luks

/-! ### Programs -/

section Prog

variable {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- The string-isomorphism instance of the layer step. -/
def stepInputProg (N : var .nat) (G : var Ty.graph) (lev : var (.array .nat)) (r : var .nat)
    (gs : var Ty.gens) : Prog S rec var Solver.Ty.input :=
  .bind (levListProg N lev r) fun Lr =>
  .bind (.op0 (.natLit 1)) fun one => .bind (.op2 .add r one) fun r1 =>
  .bind (levListProg N lev r1) fun New =>
  .bind (.op1 .length Lr) fun ℓ =>
  .bind (mulProg ℓ ℓ) fun ℓ2 =>
  .bind (mulProg ℓ2 ℓ) fun ℓ3 =>
  .bind (multsProg ℓ ℓ2) fun off₁ =>
  .bind (multsProg ℓ ℓ) fun off₂ =>
  .bind (subsProg ℓ) fun Sb =>
  .bind (.op1 .arrayOfList Lr) fun LA =>
  .bind (ptsProg LA Sb) fun P =>
  .bind (posProg N Lr) fun pos =>
  .bind (cidxProg ℓ3 off₁ off₂ Sb) fun cidx =>
  .bind (mapList gs fun g => indProg N pos off₁ off₂ cidx P g) fun gs' =>
  .bind (xArrProg G lev N r New P) fun x =>
  .bind (.op1 .length P) fun m =>
  .bind (.op2 .add N m) fun D =>
  .bind (.op1 .range m) fun rk =>
  .bind (mapList rk fun t => .op2 .add N t) fun pts =>
  .bind (mkWindow D pts) fun w =>
  .bind (permOne D) fun σ =>
  .bind (.op2 .pair x x) fun xy =>
  .bind (.op2 .pair D gs') fun ng => .bind (.op2 .pair σ ng) fun σng =>
  .bind (.op2 .pair w σng) fun wσ => .op2 .pair xy wσ

/-- The generators of the next layer group from the answer. -/
def stepOutProg {D : Ty} (N : var .nat) (G : var Ty.graph) (lev : var (.array .nat))
    (r : var .nat) (gs : var Ty.gens) (ans : var (Ty.answer D)) : Prog S rec var Ty.gens :=
  .caseOption ans (.ret gs) fun c =>
    .bind (.op1 .snd c) fun H => .bind (.op1 .snd H) fun H' => .bind (.op1 .fst H') fun ks =>
    .bind (mapList ks fun k => truncProg N k) fun hs =>
    .bind (.op0 (.natLit 1)) fun one => .bind (.op2 .add r one) fun r1 =>
    .bind (levListProg N lev r1) fun New =>
    .bind (mapList hs fun h => liftProg G lev N r New h) fun lifts =>
    .bind (twinsProg G lev N r New) fun tw =>
    .op2 .append lifts tw

/-- **One layer step.** -/
def stepProg {D : Ty} (N : var .nat) (G : var Ty.graph) (lev : var (.array .nat))
    (r : var .nat) (gs : var Ty.gens) : Prog (groupSig D) (Solver.Rec D) var Ty.gens :=
  .bind (stepInputProg N G lev r gs) fun inp =>
  .bind (Solver.solveEntry D var inp) fun ans =>
  stepOutProg N G lev r gs ans

end Prog

/-! ### Models and costs -/

/-- The string-isomorphism instance of the layer step. -/
def stepInput (N : ℕ) (G : GraphData) (lev : Array ℕ) (r : ℕ) (gs : GensData) :
    (StrData × StrData) × WinData × PermData × ℕ × GensData :=
  ((xArr G lev N r (levList lev N r), xArr G lev N r (levList lev N r)),
    tripWin N (levList lev N r), PermData.one (domSize N (levList lev N r)),
    domSize N (levList lev N r), gs.map (indData N (levList lev N r)))

/-- The next generators from the answer's generators `ks`. -/
def stepOut (N : ℕ) (G : GraphData) (lev : Array ℕ) (r : ℕ) (ks : GensData) : GensData :=
  (ks.map (PermData.truncTo N)).map (liftDataB G lev N r (levList lev N (r + 1))) ++
    twinGens G lev N r (levList lev N (r + 1))

/-- The cost bound of building the instance, for `L` generators. -/
def inputCost (N L : ℕ) : ℕ := 500 * (N + 1) ^ 4 + 100 * L * (N + 1) ^ 3

/-- The cost bound of the output, for `K` answer generators. -/
def outCost (N K : ℕ) : ℕ := K * (440 * N * N + 141 * N + 28) + N * (N * (10 * N + 107) + 22) +
  7 * N + 15

/-- The largest domain of a layer step. -/
def domBound (N : ℕ) : ℕ := N + N * N * N

/-- The bound on the number of generators of a layer group. -/
def genBound (N : ℕ) : ℕ := domBound N * domBound N + N * N

/-- The cost bound of one layer step, for `L` input generators. -/
def stepCost (N L : ℕ) : ℕ :=
  inputCost N L + (6640 * (domBound N + 1) ^ 8 + 60 * L * (domBound N + 1) ^ 2) +
    outCost N (domBound N * domBound N)

theorem length_levList_le (lev : Array ℕ) (N r : ℕ) : (levList lev N r).length ≤ N := by
  have := List.length_filter_le (fun v => decide (get lev v = r)) (List.range N)
  simpa [levList] using this

theorem lt_of_mem_levList {lev : Array ℕ} {N r x : ℕ} (hx : x ∈ levList lev N r) : x < N :=
  (mem_levList.1 hx).1

theorem domSize_le (lev : Array ℕ) (N r : ℕ) : domSize N (levList lev N r) ≤ domBound N := by
  have h := length_levList_le lev N r
  simp only [domSize, domBound, nsub]
  have : (levList lev N r).length * (levList lev N r).length ≤ N * N := Nat.mul_le_mul h h
  have := Nat.mul_le_mul this h
  have := length_subsL_le (levList lev N r).length
  omega

/-! ### Specifications -/

section Specs

variable {S : Signature} {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

theorem RunsWithin.stepInputProg {N : ℕ} {G : GraphData} (hG3 : ∀ u, (nbrs G u).length ≤ 3)
    (lev : Array ℕ) (r : ℕ) {gs : GensData} (hgs : GensData.AllValid N gs)
    (hm : ∀ g ∈ gs, MapsL (levList lev N r) (PermData.denote N g)) :
    RunsWithin X body (Graph.stepInputProg N G lev r gs) (stepInput N G lev r gs)
      (inputCost N gs.length) := by
  set Lr := levList lev N r with hLr
  have hnd : Lr.Nodup := nodup_levList r
  have hlt : ∀ x ∈ Lr, x < N := fun x hx => lt_of_mem_levList hx
  have hℓ : Lr.length ≤ N := length_levList_le lev N r
  have hnew : (levList lev N (r + 1)).length ≤ N := length_levList_le lev N (r + 1)
  have hind : gs.map (indDataB N (posArr N Lr) (multsArr Lr.length (Lr.length * Lr.length))
      (multsArr Lr.length Lr.length) (cidxOf Lr) (ptrips Lr)) = gs.map (indData N Lr) :=
    List.map_congr_left fun g hg => indDataB_eq hnd hlt (hgs g hg) (hm g hg)
  have hP := length_ptrips Lr
  have hm₁ := length_subsL_le Lr.length
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.levListProg N lev r)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.levListProg N lev (r + 1))
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.mulProg Lr.length Lr.length)
    run_step (RunsWithin.mulProg (Lr.length * Lr.length) Lr.length)
    run_step (RunsWithin.multsProg Lr.length (Lr.length * Lr.length))
    run_step (RunsWithin.multsProg Lr.length Lr.length)
    run_step (RunsWithin.subsProg Lr.length)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.ptsProg Lr)
    run_step (RunsWithin.posProg N Lr)
    run_step (RunsWithin.cidxProg _ _ _ _)
    run_step (RunsWithin.mapList_le fun g hg => RunsWithin.indProg (N := N) _ _ _ _ _ (hgs g hg))
    run_step (RunsWithin.xArrProg hG3 lev r hnew Lr)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.mapList_le (c := 1) fun t _ => RunsWithin.prim_le rfl le_rfl)
    run_step (RunsWithin.mkWindow _ _)
    run_step (RunsWithin.permOne _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    refine RunsWithin.prim_le ?_ le_rfl
    simp only [Prim.eval, stepInput, ← hLr, hind, hP, domSize, tripWin, blockWin, blockPts]
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head_cons, List.length_map, List.length_range, hP,
      inputCost, nsub]
    have h1 : Lr.length * Lr.length ≤ N * N := Nat.mul_le_mul hℓ hℓ
    have h2 : Lr.length * Lr.length * Lr.length ≤ N * N * N := Nat.mul_le_mul h1 hℓ
    have hmN : (subsL Lr.length).length ≤ N * N * N := hm₁.trans h2
    have h3 : (subsL Lr.length).length * N ≤ N * N * N * N := Nat.mul_le_mul_right _ hmN
    have h4 : gs.length * (subsL Lr.length).length ≤ gs.length * (N * N * N) :=
      Nat.mul_le_mul_left _ hmN
    nlinarith

theorem RunsWithin.stepOutProg {D : Ty} {N : ℕ} {G : GraphData}
    (hG3 : ∀ u, (nbrs G u).length ≤ 3) (lev : Array ℕ) (r : ℕ) (gs : GensData)
    (c : CosetData D) :
    RunsWithin X body (Graph.stepOutProg (D := D) N G lev r gs (some c))
      (stepOut N G lev r c.2.gens) (outCost N c.2.gens.length) := by
  have hnew : (levList lev N (r + 1)).length ≤ N := length_levList_le lev N (r + 1)
  have htw : (levList lev N (r + 1)).length * ((levList lev N (r + 1)).length * (10 * N + 107) +
      22) ≤ N * (N * (10 * N + 107) + 22) := Nat.mul_le_mul hnew (by nlinarith)
  have hl : 2 * (N * (220 * (levList lev N (r + 1)).length + 63) + 2 * N + 4) + 3 ≤
      440 * N * N + 130 * N + 11 := by nlinarith
  apply RunsWithin.mono
  case h =>
    run_with RunsWithin.caseOption_some _
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.mapList_le fun k _ => RunsWithin.truncProg N k)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.levListProg N lev (r + 1))
    run_step (RunsWithin.mapList_le fun h _ => RunsWithin.liftProg hG3 lev N r _ h)
    run_step (RunsWithin.twinsProg hG3 lev N r _)
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head_cons, List.length_map, outCost, GroupData.gens]
    have := Nat.mul_le_mul_left c.2.2.1.length hl
    nlinarith

end Specs

/-! ### The step -/

section Main

variable {N : ℕ} {G : GraphData} {roots : List ℕ} {lev : Array ℕ} {a b c d : ℕ}
  (hZ : Layered N G roots lev) (hR : Roots4 N G lev a b c d)

include hZ hR in
/-- **One layer step.** With the Schreier–Sims backend, from valid generators of `A_r` the step
returns valid generators of `A_{r+1}`, at most `genBound N` of them, at cost at most
`stepCost N |gs|`. -/
theorem RunsWithin.stepProg {r : ℕ} {gs : GensData} (hgs : GensData.AllValid N gs)
    (hden : GensData.denote N gs = AutR N G lev r) :
    ∃ gs', RunsWithin ssCtx (luksBody Ty.unit Ty.denote) (Graph.stepProg N G lev r gs) gs'
        (stepCost N gs.length) ∧ GensData.AllValid N gs' ∧
      GensData.denote N gs' = AutR N G lev (r + 1) ∧ gs'.length ≤ genBound N := by
  have hG3 : ∀ u, (nbrs G u).length ≤ 3 := hZ.valid.deg
  have hnd : (levList lev N r).Nodup := nodup_levList r
  have hP : ∀ g ∈ AutR N G lev r, MapsL (levList lev N r) g := fun _ h => mapsL_of_autR h
  have hm : ∀ g ∈ gs, MapsL (levList lev N r) (PermData.denote N g) := fun g hg =>
    hP _ (hden ▸ GensData.mem_denote_of_mem hg)
  have hin := RunsWithin.stepInputProg (X := ssCtx) (body := luksBody Ty.unit Ty.denote) hG3 lev
    r hgs hm
  have hgs' : GensData.AllValid (domSize N (levList lev N r))
      (gs.map (indData N (levList lev N r))) :=
    allValid_map_indData hnd fun g hg => hP g (hden ▸ hg)
  have hrange : GensData.denote (domSize N (levList lev N r))
      (gs.map (indData N (levList lev N r))) = (indHom hnd hP).range :=
    denote_map_indData' hnd hP hden
  have hW : IsInvariant (GensData.denote _ (gs.map (indData N (levList lev N r))))
      ((tripWin N (levList lev N r)).denote (domSize N (levList lev N r))) := by
    rw [hrange]
    exact isInvariant_tripWin hnd hP
  have hnil : Group.IsNilpotent
      (GensData.denote (domSize N (levList lev N r)) (gs.map (indData N (levList lev N r)))) := by
    rw [hrange]
    exact isNilpotent_indHom hnd hP (isPGroup_autR hZ hR r)
  obtain ⟨ans, hrun, hok, hgl⟩ := luksEntry_spec (X := ssCtx) (DV := ssDV)
    (fun op x _ hx => ssOracle_meets op x hx) (fun _ _ _ hx => hx)
    (ssLuksBounds _ (domSize N (levList lev N r) ^ 1) _) (primBounded_of_isNilpotent hnil) le_rfl
    (valid_tripWin N (levList lev N r)) (PermData.valid_one _) hgs' hW
    (xy := (xArr G lev N r (levList lev N r), xArr G lev N r (levList lev N r)))
  -- the answer is a coset
  rcases ans with _ | c'
  · exfalso
    have hone : (1 : Perm (Fin (domSize N (levList lev N r)))) ∈ iso
        ((tripWin N (levList lev N r)).denote _)
        (PermData.denote _ (PermData.one (domSize N (levList lev N r))))
        (GensData.denote _ (gs.map (indData N (levList lev N r))))
        (StrData.denote _ (xArr G lev N r (levList lev N r)))
        (StrData.denote _ (xArr G lev N r (levList lev N r))) := by
      rw [PermData.denote_one, mem_iso, inv_mul_cancel]
      exact ⟨one_mem _, fun _ _ => rfl⟩
    have h : iso _ _ _ _ _ = ∅ := hok
    rw [h] at hone
    exact hone
  obtain ⟨τ, H⟩ := c'
  have hHv := hok.2.2.1.1
  have hHden := hok.eq_aut hW
  obtain ⟨hhs, hhsden⟩ := readback hZ.valid hrange hW hHv hHden
  obtain ⟨hnext, hnextden⟩ := nextGens_spec hZ hhs hhsden
  have hks : H.gens.length ≤ _ := hgl (τ, H) rfl
  refine ⟨stepOut N G lev r H.gens, ?_, hnext, hnextden, ?_⟩
  · have hluks : 11 + ssCtx.B.call .generate (domSize N (levList lev N r),
        gs.map (indData N (levList lev N r)))
        (ssCtx.O.run .generate (domSize N (levList lev N r),
          gs.map (indData N (levList lev N r)))) +
        luksBound (luksQ (domSize N (levList lev N r))
          (domSize N (levList lev N r) * domSize N (levList lev N r))
          (ssLuksBounds _ (domSize N (levList lev N r) ^ 1)
            (GensData.denote _ (gs.map (indData N (levList lev N r))))).Borb
          (ssLuksBounds _ (domSize N (levList lev N r) ^ 1)
            (GensData.denote _ (gs.map (indData N (levList lev N r))))).Bge
          (ssLuksBounds _ (domSize N (levList lev N r) ^ 1)
            (GensData.denote _ (gs.map (indData N (levList lev N r))))).Bke
          (ssLuksBounds _ (domSize N (levList lev N r) ^ 1)
            (GensData.denote _ (gs.map (indData N (levList lev N r))))).Bgt
          (ssLuksBounds _ (domSize N (levList lev N r) ^ 1)
            (GensData.denote _ (gs.map (indData N (levList lev N r))))).sKe
          (ssLuksBounds _ (domSize N (levList lev N r) ^ 1)
            (GensData.denote _ (gs.map (indData N (levList lev N r))))).Bcr
          (ssLuksBounds _ (domSize N (levList lev N r) ^ 1)
            (GensData.denote _ (gs.map (indData N (levList lev N r))))).Bgen) 1
          (tripWin N (levList lev N r)).1.length ≤
        6640 * (domSize N (levList lev N r) + 1) ^ 8 +
          60 * (gs.map (indData N (levList lev N r))).length *
            (domSize N (levList lev N r) + 1) ^ 2 :=
      luksSimsCost_one_le (WinData.length_le (valid_tripWin N (levList lev N r)))
    have hD := domSize_le lev N r
    have h8 : (domSize N (levList lev N r) + 1) ^ 8 ≤ (domBound N + 1) ^ 8 :=
      Nat.pow_le_pow_left (by omega) 8
    have h2 : (domSize N (levList lev N r) + 1) ^ 2 ≤ (domBound N + 1) ^ 2 :=
      Nat.pow_le_pow_left (by omega) 2
    have hDD : domSize N (levList lev N r) * domSize N (levList lev N r) ≤
        domBound N * domBound N := Nat.mul_le_mul hD hD
    have hout : outCost N H.gens.length ≤ outCost N (domBound N * domBound N) := by
      unfold outCost
      have := hks.trans hDD
      gcongr
    rw [List.length_map] at hluks
    have hgs2 : gs.length * (domSize N (levList lev N r) + 1) ^ 2 ≤
        gs.length * (domBound N + 1) ^ 2 := Nat.mul_le_mul_left _ h2
    apply RunsWithin.mono
    case h =>
      run_step hin
      run_step hrun
      exact RunsWithin.stepOutProg hG3 lev r gs (τ, H)
    case hc =>
      unfold stepCost
      nlinarith
  · have hnew := length_levList_le lev N (r + 1)
    have htw := length_twinGens_le (G := G) (lev := lev) (N := N) (r := r)
      (levList lev N (r + 1))
    have hD := domSize_le lev N r
    have hDD : domSize N (levList lev N r) * domSize N (levList lev N r) ≤
        domBound N * domBound N := Nat.mul_le_mul hD hD
    have hNN : (levList lev N (r + 1)).length * (levList lev N (r + 1)).length ≤ N * N :=
      Nat.mul_le_mul hnew hnew
    simp only [stepOut, List.length_append, List.length_map, genBound]
    omega

end Main

end GraphIso.Graph
