module

public import GraphIso.Valence.LiftProg
public import GraphIso.Valence.Solvable
public import GraphIso.Graph.Step
public import GraphIso.Luks.Solvable

/-!
# One layer step for maximum degree `Δ`

`stepProg Δ N G lev r gs` runs inside the procedure `luksBody`:

1. `stepInputProg Δ` builds the string-isomorphism instance on `D = N + m` points, `m` the
   number of subsets of level `r` with at most `Δ` points: the layer string `xArr Δ` as both
   strings, the window of the subsets, the identity, and the induced generators (`stepInput`).
2. `solveEntry` solves it with Luks's strategy.
3. milestone 4's `stepOutProg` truncates the answer's generators to the first `N` points, lifts
   them, and adds the twin transpositions.

**`RunsWithin.stepProg`**: with the Schreier–Sims backend, if `gs` generates `A_r` then the
step returns valid generators of `A_{r+1}`, at most `genBound Δ N` of them, at cost at most
`stepCost Δ c N |gs|`. The constant `c` is a parameter: `LayerPrim Δ c` says that every
homomorphic image of every layer group has `PrimBounded _ c`, which bounds the solver by
`6640 (D + 1)^{3c + 5} + 60 L (D + 1)²` (`luksSimsCost_le_pow`).

* `layerPrim_solvable`: for `Δ ≤ 5` the layer groups are solvable and their orders have at
  most the prime divisors `2` and `3` (`GraphIso/Valence/Solvable.lean`), so
  `primBounded_of_isSolvable` with `s = 1` gives `LayerPrim Δ 13` (exponent `44`).
* For every `Δ`, the layer groups have bounded simple sections, which gives `LayerPrim` with
  milestone 8's constant (`GraphIso/Valence/Bounded.lean`).
-/

@[expose] public section

namespace GraphIso.Graph.Valence

open Equiv Cost Programs Sims Luks

/-! ### Programs -/

section Prog

variable {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- The string-isomorphism instance of the layer step. -/
def stepInputProg (Δ : ℕ) (N : var .nat) (G : var Ty.graph) (lev : var (.array .nat))
    (r : var .nat) (gs : var Ty.gens) : Prog S rec var Solver.Ty.input :=
  .bind (levListProg N lev r) fun Lr =>
  .bind (.op0 (.natLit 1)) fun one => .bind (.op2 .add r one) fun r1 =>
  .bind (levListProg N lev r1) fun New =>
  .bind (subsProg Δ Lr) fun Sb =>
  .bind (mapList gs fun g => indProg N Sb g) fun gs' =>
  .bind (xArrProg Δ G lev N r New Sb) fun x =>
  .bind (.op1 .length Sb) fun m =>
  .bind (.op2 .add N m) fun D =>
  .bind (.op1 .range m) fun rk =>
  .bind (mapList rk fun t => .op2 .add N t) fun pts =>
  .bind (mkWindow D pts) fun w =>
  .bind (permOne D) fun σ =>
  .bind (.op2 .pair x x) fun xy =>
  .bind (.op2 .pair D gs') fun ng => .bind (.op2 .pair σ ng) fun σng =>
  .bind (.op2 .pair w σng) fun wσ => .op2 .pair xy wσ

/-- **One layer step.** -/
def stepProg (Δ : ℕ) {D : Ty} (N : var .nat) (G : var Ty.graph) (lev : var (.array .nat))
    (r : var .nat) (gs : var Ty.gens) : Prog (groupSig D) (Solver.Rec D) var Ty.gens :=
  .bind (stepInputProg Δ N G lev r gs) fun inp =>
  .bind (Solver.solveEntry D var inp) fun ans =>
  Graph.stepOutProg N G lev r gs ans

end Prog

/-! ### Models and costs -/

/-- The string-isomorphism instance of the layer step. -/
def stepInput (Δ N : ℕ) (G : GraphData) (lev : Array ℕ) (r : ℕ) (gs : GensData) :
    (StrData × StrData) × WinData × PermData × ℕ × GensData :=
  ((xArr Δ G lev N r (levList lev N r), xArr Δ G lev N r (levList lev N r)),
    subWin Δ N (levList lev N r), PermData.one (domSize Δ N (levList lev N r)),
    domSize Δ N (levList lev N r), gs.map (indData Δ N (levList lev N r)))

/-- The largest domain of a layer step. -/
def domBound (Δ N : ℕ) : ℕ := N + (N + 1) ^ Δ

/-- The bound on the number of generators of a layer group. -/
def genBound (Δ N : ℕ) : ℕ := domBound Δ N * domBound Δ N + N * N

/-- The cost bound of building the instance, for `L` generators. -/
def inputCost (Δ N L : ℕ) : ℕ :=
  subsCost Δ N + L * (2 * indArrCost Δ N ((N + 1) ^ Δ) + 6) +
    (N + 1) ^ Δ * (xSubCost Δ N + 20) + 22 * N + 40

/-- The cost bound of the output, for `K` answer generators. -/
def outCost (Δ N K : ℕ) : ℕ :=
  K * (11 * N + liftCost Δ N N + 17) + twinsCost Δ N N + 7 * N + 15

/-- The cost bound of one layer step, for `L` input generators, when the string-isomorphism
call has the constant `c`. -/
def stepCost (Δ c N L : ℕ) : ℕ :=
  inputCost Δ N L + (6640 * (domBound Δ N + 1) ^ (3 * c + 5) + 60 * L * (domBound Δ N + 1) ^ 2) +
    outCost Δ N (domBound Δ N * domBound Δ N)

theorem nsub_le (Δ : ℕ) (lev : Array ℕ) (N r : ℕ) :
    nsub Δ (levList lev N r) ≤ (N + 1) ^ Δ :=
  (length_subsR_le Δ (nodup_levList r)).trans
    (Nat.pow_le_pow_left (by have := length_levList_le lev N r; omega) Δ)

theorem domSize_le (Δ : ℕ) (lev : Array ℕ) (N r : ℕ) :
    domSize Δ N (levList lev N r) ≤ domBound Δ N := by
  have := nsub_le Δ lev N r
  simp only [domSize, domBound]
  omega

theorem stepCost_mono {Δ c N L L' : ℕ} (h : L ≤ L') : stepCost Δ c N L ≤ stepCost Δ c N L' := by
  unfold stepCost inputCost
  gcongr

/-! ### Specifications -/

section Specs

variable {S : Signature} {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

theorem RunsWithin.stepInputProg {Δ N : ℕ} {G : GraphData} (hGd : ∀ u, (nbrs G u).length ≤ Δ)
    (lev : Array ℕ) (r : ℕ) {gs : GensData} (hgs : GensData.AllValid N gs) :
    RunsWithin X body (Valence.stepInputProg Δ N G lev r gs) (stepInput Δ N G lev r gs)
      (inputCost Δ N gs.length) := by
  set Lr := levList lev N r with hLr
  have hnd : Lr.Nodup := nodup_levList r
  have hlt : ∀ x ∈ Lr, x < N := fun x hx => lt_of_mem_levList hx
  have hℓ : Lr.length ≤ N := length_levList_le lev N r
  have hnew : (levList lev N (r + 1)).length ≤ N := length_levList_le lev N (r + 1)
  have hm : nsub Δ Lr ≤ (N + 1) ^ Δ := nsub_le Δ lev N r
  have hSb : ∀ u ∈ subsR Δ Lr, u.length ≤ Δ := fun u hu => (mem_subsR.1 hu).2
  have hind : gs.map (indDataB N (subsR Δ Lr)) = gs.map (indData Δ N Lr) :=
    List.map_congr_left fun g hg => indDataB_eq hlt (hgs g hg)
  have hsubs : subsCost Δ Lr.length ≤ subsCost Δ N := by
    unfold subsCost
    gcongr
  have hia : indArrCost Δ N (subsR Δ Lr).length ≤ indArrCost Δ N ((N + 1) ^ Δ) := by
    unfold indArrCost
    gcongr
  have hia' : gs.length * (2 * indArrCost Δ N (subsR Δ Lr).length + 3 + 3) ≤
      gs.length * (2 * indArrCost Δ N ((N + 1) ^ Δ) + 6) :=
    Nat.mul_le_mul_left _ (by omega)
  have hxa : nsub Δ Lr * (xSubCost Δ N + 4) ≤ (N + 1) ^ Δ * (xSubCost Δ N + 4) :=
    Nat.mul_le_mul_right _ hm
  have hxa' : (N + 1) ^ Δ * (xSubCost Δ N + 4) + 16 * (N + 1) ^ Δ =
      (N + 1) ^ Δ * (xSubCost Δ N + 20) := by ring
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.levListProg N lev r)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.levListProg N lev (r + 1))
    run_step (RunsWithin.subsProg Δ hnd)
    run_step (RunsWithin.mapList_le fun g hg => RunsWithin.indProg (N := N) hSb (hgs g hg))
    run_step (RunsWithin.xArrProg hGd lev r hnew Lr)
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
    simp only [Prim.eval, stepInput, ← hLr, hind, domSize, subWin, blockWin, blockPts]
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head_cons, List.length_map, List.length_range,
      inputCost]
    simp only [← hLr]
    have : (subsR Δ Lr).length = nsub Δ Lr := rfl
    omega

theorem RunsWithin.stepOutProg {D : Ty} {Δ N : ℕ} {G : GraphData}
    (hGd : ∀ u, (nbrs G u).length ≤ Δ) (lev : Array ℕ) (r : ℕ) (gs : GensData)
    (c : CosetData D) :
    RunsWithin X body (Graph.stepOutProg (D := D) N G lev r gs (some c))
      (stepOut N G lev r c.2.gens) (outCost Δ N c.2.gens.length) := by
  have hnew : (levList lev N (r + 1)).length ≤ N := length_levList_le lev N (r + 1)
  have hl : liftCost Δ N (levList lev N (r + 1)).length ≤ liftCost Δ N N := by
    unfold liftCost cL
    gcongr
  have htw : twinsCost Δ N (levList lev N (r + 1)).length ≤ twinsCost Δ N N := by
    unfold twinsCost
    gcongr
  have hK : c.2.2.1.length * (11 * N + 10 + 3) + c.2.2.1.length *
      (liftCost Δ N (levList lev N (r + 1)).length + 3) + c.2.2.1.length ≤
      c.2.2.1.length * (11 * N + liftCost Δ N N + 17) := by
    have := Nat.mul_le_mul_left c.2.2.1.length hl
    nlinarith
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
    run_step (RunsWithin.mapList_le fun h _ => RunsWithin.liftProg hGd lev N r _ h)
    run_step (RunsWithin.twinsProg hGd lev N r _)
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head_cons, List.length_map, outCost, GroupData.gens]
    omega

end Specs

/-! ### Bounded primitive sections of the layer groups -/

/-- **Bounded primitive sections of the layer groups**: for every layered graph of maximum
degree `Δ` rooted at two edges, every homomorphic image of every layer group `A_r` has
`PrimBounded _ c`. -/
def LayerPrim (Δ c : ℕ) : Prop :=
  ∀ {N : ℕ} {G : GraphData} {roots : List ℕ} {lev : Array ℕ} {a b c' d : ℕ},
    LayeredD Δ N G roots lev → Roots4 N G lev a b c' d →
    ∀ (r D : ℕ) (f : AutR N G lev r →* Perm (Fin D)), PrimBounded f.range c

/-- **Maximum degree at most five**: the layer groups are solvable and their orders have at
most the prime divisors `2` and `3`, so their images have `PrimBounded _ 13`. -/
theorem layerPrim_solvable {Δ : ℕ} (hΔ : Δ ≤ 5) : LayerPrim Δ 13 := by
  intro N G roots lev a b c d hZ hR r D f
  have := isSolvable_autR hZ hR hΔ r
  have hsol : Group.IsSolvable f.range :=
    Group.isSolvable_of_surjective f.rangeRestrict_surjective
  have hdvd : Nat.card f.range ∣ Nat.card (AutR N G lev r) := Subgroup.card_range_dvd _
  have hsub := Nat.primeFactors_mono hdvd Nat.card_pos.ne'
  exact primBounded_of_isSolvable (s := 1) hsol
    ((Finset.card_le_card hsub).trans (card_primeFactors_autR_le hZ hR hΔ r))

/-! ### The step -/

section Main

variable {Δ c N : ℕ} {G : GraphData} {roots : List ℕ} {lev : Array ℕ} {a b c' d : ℕ}
  (hZ : LayeredD Δ N G roots lev) (hR : Roots4 N G lev a b c' d) (hc : LayerPrim Δ c)
  (hc1 : 1 ≤ c)

include hZ hR hc hc1 in
/-- **One layer step.** With the Schreier–Sims backend, from valid generators of `A_r` the step
returns valid generators of `A_{r+1}`, at most `genBound Δ N` of them, at cost at most
`stepCost Δ c N |gs|`. -/
theorem RunsWithin.stepProg {r : ℕ} {gs : GensData} (hgs : GensData.AllValid N gs)
    (hden : GensData.denote N gs = AutR N G lev r) :
    ∃ gs', RunsWithin ssCtx (luksBody Ty.unit Ty.denote) (Valence.stepProg Δ N G lev r gs) gs'
        (stepCost Δ c N gs.length) ∧ GensData.AllValid N gs' ∧
      GensData.denote N gs' = AutR N G lev (r + 1) ∧ gs'.length ≤ genBound Δ N := by
  have hGd : ∀ u, (nbrs G u).length ≤ Δ := hZ.valid.deg
  have hLr := pairwise_levList lev N r
  have hP : ∀ g ∈ AutR N G lev r, MapsL (levList lev N r) g := fun _ h => mapsL_of_autR h
  have hin := RunsWithin.stepInputProg (X := ssCtx) (body := luksBody Ty.unit Ty.denote) hGd lev
    r hgs
  have hgs' : GensData.AllValid (domSize Δ N (levList lev N r))
      (gs.map (indData Δ N (levList lev N r))) :=
    allValid_map_indData hLr fun g hg => hP g (hden ▸ hg)
  have hrange : GensData.denote (domSize Δ N (levList lev N r))
      (gs.map (indData Δ N (levList lev N r))) = (indHom Δ hLr hP).range :=
    denote_map_indData' hLr hP hden
  have hW : IsInvariant (GensData.denote _ (gs.map (indData Δ N (levList lev N r))))
      ((subWin Δ N (levList lev N r)).denote (domSize Δ N (levList lev N r))) := by
    rw [hrange]
    exact isInvariant_subWin hLr hP
  have hprim : PrimBounded (GensData.denote (domSize Δ N (levList lev N r))
      (gs.map (indData Δ N (levList lev N r)))) c := by
    rw [hrange]
    exact hc hZ hR r _ (indHom Δ hLr hP)
  obtain ⟨ans, hrun, hok, hgl⟩ := luksEntry_spec (X := ssCtx) (DV := ssDV)
    (fun op x _ hx => ssOracle_meets op x hx) (fun _ _ _ hx => hx)
    (ssLuksBounds _ (domSize Δ N (levList lev N r) ^ c) _) (c := c) hprim le_rfl
    (valid_subWin (Δ := Δ) (N := N) (Lr := levList lev N r)) (PermData.valid_one _) hgs' hW
    (xy := (xArr Δ G lev N r (levList lev N r), xArr Δ G lev N r (levList lev N r)))
  -- the answer is a coset
  rcases ans with _ | c'
  · exfalso
    have hone : (1 : Perm (Fin (domSize Δ N (levList lev N r)))) ∈ iso
        ((subWin Δ N (levList lev N r)).denote _)
        (PermData.denote _ (PermData.one (domSize Δ N (levList lev N r))))
        (GensData.denote _ (gs.map (indData Δ N (levList lev N r))))
        (StrData.denote _ (xArr Δ G lev N r (levList lev N r)))
        (StrData.denote _ (xArr Δ G lev N r (levList lev N r))) := by
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
  · have hluks := luksSimsCost_le_pow (n := domSize Δ N (levList lev N r))
      (L := (gs.map (indData Δ N (levList lev N r))).length) (c := c) hc1
      (WinData.length_le (valid_subWin (Δ := Δ) (N := N) (Lr := levList lev N r)))
    have hrun' := hrun.mono (le_trans le_rfl hluks)
    have hD := domSize_le Δ lev N r
    have h44 : (domSize Δ N (levList lev N r) + 1) ^ (3 * c + 5) ≤
        (domBound Δ N + 1) ^ (3 * c + 5) :=
      Nat.pow_le_pow_left (by omega) _
    have h2 : (domSize Δ N (levList lev N r) + 1) ^ 2 ≤ (domBound Δ N + 1) ^ 2 :=
      Nat.pow_le_pow_left (by omega) 2
    have hDD : domSize Δ N (levList lev N r) * domSize Δ N (levList lev N r) ≤
        domBound Δ N * domBound Δ N := Nat.mul_le_mul hD hD
    have hout : outCost Δ N H.gens.length ≤ outCost Δ N (domBound Δ N * domBound Δ N) := by
      unfold outCost
      have := hks.trans hDD
      gcongr
    have hgs2 : 60 * gs.length * (domSize Δ N (levList lev N r) + 1) ^ 2 ≤
        60 * gs.length * (domBound Δ N + 1) ^ 2 := Nat.mul_le_mul_left _ h2
    apply RunsWithin.mono
    case h =>
      run_step hin
      run_step hrun'
      exact RunsWithin.stepOutProg hGd lev r gs (τ, H)
    case hc =>
      unfold stepCost
      rw [List.length_map]
      dsimp only
      generalize (domSize Δ N (levList lev N r) + 1) ^ (3 * c + 5) = A at *
      generalize (domBound Δ N + 1) ^ (3 * c + 5) = B at *
      omega
  · have hnew := length_levList_le lev N (r + 1)
    have htw := length_twinGens_le (G := G) (lev := lev) (N := N) (r := r)
      (levList lev N (r + 1))
    have hD := domSize_le Δ lev N r
    have hDD : domSize Δ N (levList lev N r) * domSize Δ N (levList lev N r) ≤
        domBound Δ N * domBound Δ N := Nat.mul_le_mul hD hD
    have hNN : (levList lev N (r + 1)).length * (levList lev N (r + 1)).length ≤ N * N :=
      Nat.mul_le_mul hnew hnew
    simp only [stepOut, List.length_append, List.length_map, genBound]
    omega

end Main

end GraphIso.Graph.Valence
