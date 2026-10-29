module

public import GraphIso.Sims.OpsProg

/-!
# The orbit searches in the cost language

* `orbitBFSProg n gs u` computes `orbitBFS n gs u` (`orbitTransversal`) at cost at most
  `transCost n L`: at most `n` iterations, each visiting the images of one point under the
  `L` generators; a new point costs one composition and one mask update.
* `orbitsProg n gs w` computes `orbitsModel n gs w` (`orbits`) at cost at most
  `orbitsCost n L m`: one search for each of the `m` window points not yet seen.
-/

@[expose] public section

namespace GraphIso

namespace Cost.Ty

/-- Search states: visited mask, queue, found pairs. -/
abbrev ostate : Ty := .prod (.array .bool) (.prod (.list Ty.item) (.list Ty.item))

end Cost.Ty

namespace Sims

open Equiv Cost Programs

section Prog

variable {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- Visit the image of `v` (reached by `r`) under `g`. -/
def visitBody (v : var .nat) (r : var Ty.perm) (acc : var Ty.ostate) (g : var Ty.perm) :
    Prog S rec var Ty.ostate :=
  .bind (.op1 .fst acc) fun mask => .bind (.op1 .snd acc) fun qf =>
  .bind (permApply g v) fun x => .bind (.op2 .arrayGet mask x) fun mx =>
  .ite mx (.ret acc)
    (.bind (.op1 .fst qf) fun q => .bind (.op1 .snd qf) fun f =>
      .bind (.op0 (.boolLit true)) fun t => .bind (.op2 .pair x t) fun wr =>
      .bind (.op0 .nil) fun nl => .bind (.op2 .cons wr nl) fun ws =>
      .bind (.op2 .arrayUpdate mask ws) fun mask' =>
      .bind (permMul g r) fun gr => .bind (.op2 .pair x gr) fun p =>
      .bind (.op2 .cons p q) fun q' => .bind (.op2 .cons p f) fun f' =>
      .bind (.op2 .pair q' f') fun qf' => .op2 .pair mask' qf')

/-- One iteration of the search. -/
def orbitStepBody (gs : var Ty.gens) (st : var Ty.ostate) : Prog S rec var (.option Ty.ostate) :=
  .bind (.op1 .fst st) fun mask => .bind (.op1 .snd st) fun qf =>
  .bind (.op1 .fst qf) fun q => .bind (.op1 .snd qf) fun f =>
  .caseList q (.op0 .none) fun p rest =>
    .bind (.op1 .fst p) fun v => .bind (.op1 .snd p) fun r =>
    .bind (.op2 .pair rest f) fun qf₀ => .bind (.op2 .pair mask qf₀) fun st₀ =>
    .bind (.foldList gs st₀ fun acc g => visitBody v r acc g) fun st' => .op1 .some st'

/-- The search from `u`. -/
def orbitBFSProg (n : var .nat) (gs : var Ty.gens) (u : var .nat) :
    Prog S rec var (.list Ty.item) :=
  .bind (.op0 (.boolLit false)) fun f => .bind (.op2 .arrayMk n f) fun m₀ =>
  .bind (.op0 (.boolLit true)) fun t => .bind (.op2 .pair u t) fun wr =>
  .bind (.op0 .nil) fun nl => .bind (.op2 .cons wr nl) fun ws =>
  .bind (.op2 .arrayUpdate m₀ ws) fun mask =>
  .bind (permOne n) fun e => .bind (.op2 .pair u e) fun p =>
  .bind (.op0 .nil) fun nl' => .bind (.op2 .cons p nl') fun l =>
  .bind (.op2 .pair l l) fun qf => .bind (.op2 .pair mask qf) fun st₀ =>
  .bind (.loop st₀ fun st => orbitStepBody gs st) fun fin =>
  .bind (.op1 .snd fin) fun qf' => .op1 .snd qf'

/-- Record the orbit of `p` unless it was seen. -/
def orbitsBody (n : var .nat) (gs : var Ty.gens)
    (acc : var (.prod (.array .bool) (.list (.list .nat))))
    (p : var .nat) : Prog S rec var (.prod (.array .bool) (.list (.list .nat))) :=
  .bind (.op1 .fst acc) fun seen => .bind (.op1 .snd acc) fun os =>
  .bind (.op2 .arrayGet seen p) fun sp =>
  .ite sp (.ret acc)
    (.bind (orbitBFSProg n gs p) fun prs => .bind (mapList prs fun q => .op1 .fst q) fun o =>
      .bind (.op0 (.boolLit true)) fun t => .bind (mapList o fun i => .op2 .pair i t) fun ws =>
      .bind (.op2 .arrayUpdate seen ws) fun seen' => .bind (.op2 .cons o os) fun os' =>
      .op2 .pair seen' os')

/-- The orbits of the window points. -/
def orbitsProg (n : var .nat) (gs : var Ty.gens) (w : var Ty.win) :
    Prog S rec var (.list (.list .nat)) :=
  .bind (.op0 (.boolLit false)) fun f => .bind (.op2 .arrayMk n f) fun seen₀ =>
  .bind (.op0 .nil) fun nl => .bind (.op2 .pair seen₀ nl) fun acc₀ =>
  .bind (.op1 .fst w) fun pts =>
  .bind (.foldList pts acc₀ fun acc p => orbitsBody n gs acc p) fun fin => .op1 .snd fin

end Prog

/-! ### Costs -/

/-- The cost bound of the search from a point, for `L` generators. -/
def transCost (n L : ℕ) : ℕ := n * (L * (13 * n + 33) + 11) + 4 * n + 30

/-- The cost bound of the orbits of a window of `m` points, for `L` generators. -/
def orbitsCost (n L m : ℕ) : ℕ := m * (transCost n L + 10 * n + 15) + n + 8

theorem orbitBFS_length_le {n : ℕ} {gs : GensData} {u : ℕ} (hu : u < n)
    (hgs : GensData.AllValid n gs) : (orbitBFS n gs u).length ≤ n := by
  obtain ⟨hnd, hiff, -⟩ := orbitBFS_spec hu hgs
  have hsub : ((orbitBFS n gs u).map Prod.fst).toFinset ⊆ Finset.range n := by
    intro j hj
    obtain ⟨_, hj', _⟩ := (hiff j).1 (List.mem_toFinset.1 hj)
    exact Finset.mem_range.2 hj'
  have := Finset.card_le_card hsub
  rwa [List.toFinset_card_of_nodup hnd, List.length_map, Finset.card_range] at this

section Specs

variable {S : Signature} {a b' : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b') Ty.denote b'}
  {n : ℕ} {gs : GensData}

theorem RunsWithin.visitBody {v : ℕ} {r g : PermData} (hr : r.Valid n) (hg : g.Valid n)
    {acc : OState} (hsize : acc.1.size = n) :
    RunsWithin X body (Sims.visitBody v r acc g) (visitStep v r acc g) (13 * n + 32) := by
  by_cases hm : getB acc.1 (get g.1 v) = true
  · have hF : visitStep v r acc g = acc := by simp [visitStep, hm]
    rw [hF]
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.permApply _ _)
      run_step (RunsWithin.prim _ _)
      exact RunsWithin.ite_pos hm (RunsWithin.ret _)
    case hc =>
      simp only [Prim.cost]
      omega
  · have hF : visitStep v r acc g = (acc.1.setIfInBounds (get g.1 v) true,
        (get g.1 v, g.mul r) :: acc.2.1, (get g.1 v, g.mul r) :: acc.2.2) := by
      simp [visitStep, hm]
    rw [hF]
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.permApply _ _)
      run_step (RunsWithin.prim _ _)
      run_with RunsWithin.ite_neg (Bool.eq_false_iff.2 hm : getB acc.1 (get g.1 v) = false) _
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.permMul hg hr)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      exact RunsWithin.prim_le rfl le_rfl
    case hc =>
      simp only [Prim.cost, Prim.eval, Args.head_cons, Args.tail_cons, List.length_cons,
        List.length_nil, hsize]
      omega

theorem RunsWithin.orbitStepBody (hgs : GensData.AllValid n gs) {st : OState}
    (hsize : st.1.size = n) (hq : ∀ p ∈ st.2.1, p.2.Valid n) :
    RunsWithin X body (Sims.orbitStepBody gs st) (orbitStep gs st)
      (if st.2.1 = [] then 6 else gs.length * (13 * n + 33) + 10) := by
  obtain ⟨mask, q, f⟩ := st
  simp only at hsize hq ⊢
  rcases q with _ | ⟨p, rest⟩
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      exact RunsWithin.caseList_nil (RunsWithin.prim _ _)
    case hc =>
      simp [Prim.cost]
  · have hp := hq p List.mem_cons_self
    have hfold := (RunsWithin.foldList_inv (X := X) (body := body) (a' := Ty.perm)
      (b' := Ty.ostate) (f := fun acc g => Sims.visitBody p.1 p.2 acc g)
      (F := visitStep p.1 p.2) (I := fun acc : OState => acc.1.size = n) (c := 13 * n + 32)
      gs (mask, rest, f) (fun acc hacc g hg => ⟨RunsWithin.visitBody hp (hgs g hg) hacc, by
        unfold visitStep
        split
        · exact hacc
        · simp [hacc]⟩) hsize).1
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_with RunsWithin.caseList_cons _
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step hfold
      exact RunsWithin.prim _ _
    case hc =>
      simp only [Prim.cost, reduceCtorEq, ↓reduceIte, show 13 * n + 32 + 1 = 13 * n + 33 by omega]
      omega

/-- The potential of the search loop. -/
def bfsPot (n L : ℕ) (st : OState) : ℕ := opot n st * (L * (13 * n + 33) + 11) + 7

/-- **The search from a point costs at most `transCost n L`.** -/
theorem RunsWithin.orbitBFSProg (hgs : GensData.AllValid n gs) {u : ℕ} (hu : u < n) :
    RunsWithin X body (Sims.orbitBFSProg n gs u) (orbitBFS n gs u) (transCost n gs.length) := by
  have hI₀ := orbitInit_inv (gs := gs) hu
  have hloop := RunsWithin.loop_pot (X := X) (body := body) (f := Sims.orbitStepBody gs)
    (F := orbitStep gs) (I := OInv n gs u) (Φ := bfsPot n gs.length)
    (fun st hst => ⟨_, RunsWithin.orbitStepBody hgs hst.size
      (fun p hp => (hst.pair p (hst.queue_sub p hp)).2.1), fun hF => by
        rcases hq : st.2.1 with _ | ⟨p, rest⟩
        · simp [bfsPot]
        · simp [orbitStep, hq] at hF, fun st' hF => by
        rcases hq : st.2.1 with _ | ⟨p, rest⟩
        · simp [orbitStep, hq] at hF
        · obtain ⟨st'', hstep, hI', hpot⟩ := orbitStep_spec hu hgs hst hq
          have e : st' = st'' := Option.some.inj (hF.symm.trans hstep)
          subst e
          refine ⟨hI', ?_⟩
          simp only [reduceCtorEq, ↓reduceIte, bfsPot]
          have : opot n st' * (gs.length * (13 * n + 33) + 11) + (gs.length * (13 * n + 33) + 11)
              ≤ opot n st * (gs.length * (13 * n + 33) + 11) := by
            rw [← Nat.succ_mul]
            exact Nat.mul_le_mul_right _ hpot
          omega⟩)
    (bfsPot n gs.length (orbitInit n u) + 1) (orbitInit n u) hI₀ (Nat.lt_succ_self _)
  have hpot₀ : opot n (orbitInit n u) = n := by
    simp only [opot, orbitInit, List.length_singleton]
    omega
  have hdone := iter_orbitStep hu hgs (n + 1) (orbitInit n u) hI₀ (by omega)
  have hfix : orbitStep gs (iter (orbitStep gs) (n + 1) (orbitInit n u)) = none := by
    simp [orbitStep, hdone.2]
  have h₁ := iter_eq_of_fix _ _ hfix (bfsPot n gs.length (orbitInit n u) + 1) (by
    simp only [bfsPot, hpot₀]
    have : n ≤ n * (gs.length * (13 * n + 33) + 11) := Nat.le_mul_of_pos_right _ (by omega)
    omega)
  rw [h₁] at hloop
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.permOne n)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step hloop
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head_cons, Args.tail_cons, Array.size_replicate,
      List.length_cons, List.length_nil, bfsPot, hpot₀, transCost]
    omega

theorem RunsWithin.orbitsBody (hgs : GensData.AllValid n gs) {acc : Array Bool × List (List ℕ)}
    (hsize : acc.1.size = n) {p : ℕ} (hp : p < n) :
    RunsWithin X body (Sims.orbitsBody n gs acc p) (orbitsStep n gs acc p)
      (transCost n gs.length + 10 * n + 14) := by
  by_cases hs : getB acc.1 p = true
  · have hF : orbitsStep n gs acc p = acc := by simp [orbitsStep, hs]
    rw [hF]
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      exact RunsWithin.ite_pos hs (RunsWithin.ret _)
    case hc =>
      simp only [Prim.cost]
      omega
  · have hF : orbitsStep n gs acc p = (Cost.Prim.applyWrites (a := .bool) acc.1
        (((orbitBFS n gs p).map Prod.fst).map fun i => (i, true)),
        ((orbitBFS n gs p).map Prod.fst) :: acc.2) := by simp [orbitsStep, hs]
    rw [hF]
    have hlen := orbitBFS_length_le hp hgs
    have hfst := RunsWithin.mapList_le (X := X) (body := body) (a' := Ty.item) (b' := .nat)
      (xs := orbitBFS n gs p) (f := fun q => .op1 .fst q) (F := Prod.fst) (c := 1)
      fun q _ => RunsWithin.prim_le rfl le_rfl
    have hws := RunsWithin.mapList_le (X := X) (body := body) (a' := .nat) (b' := .prod .nat .bool)
      (xs := (orbitBFS n gs p).map Prod.fst) (f := fun i => .op2 .pair i true)
      (F := fun i => (i, true)) (c := 1) fun i _ => RunsWithin.prim_le rfl le_rfl
    rw [List.length_map] at hws
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_with RunsWithin.ite_neg (Bool.eq_false_iff.2 hs : getB acc.1 p = false) _
      run_step (RunsWithin.orbitBFSProg hgs hp)
      run_step hfst
      run_step (RunsWithin.prim _ _)
      run_step hws
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      exact RunsWithin.prim_le rfl le_rfl
    case hc =>
      simp only [Prim.cost, Prim.eval, Args.head_cons, Args.tail_cons, List.length_map, hsize]
      omega

/-- **The orbits of a window cost at most `orbitsCost n L m`.** -/
theorem RunsWithin.orbitsProg (hgs : GensData.AllValid n gs) {w : WinData} (hw : w.Valid n) :
    RunsWithin X body (Sims.orbitsProg n gs w) (orbitsModel n gs w)
      (orbitsCost n gs.length w.1.length) := by
  have hfold := (RunsWithin.foldList_inv (X := X) (body := body) (a' := .nat)
    (b' := .prod (.array .bool) (.list (.list .nat))) (f := fun acc p => Sims.orbitsBody n gs acc p)
    (F := orbitsStep n gs) (I := fun acc : Array Bool × List (List ℕ) => acc.1.size = n)
    (c := transCost n gs.length + 10 * n + 14) w.1 (Array.replicate n false, [])
    (fun acc hacc p hp => ⟨RunsWithin.orbitsBody hgs hacc (hw.lt p hp), by
      unfold orbitsStep
      split
      · exact hacc
      · exact (getB_applyWrites_true _ _ hacc).1⟩) (by simp)).1
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step hfold
    exact RunsWithin.prim _ _
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head_cons, orbitsCost,
      show transCost n gs.length + 10 * n + 14 + 1 = transCost n gs.length + 10 * n + 15 by omega]
    omega

end Specs

end Sims

end GraphIso
