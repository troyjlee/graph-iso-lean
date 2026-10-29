module

public import GraphIso.Sims.OrbitsProg

/-!
# The coset search in the cost language

`cosetRepsProg n gs ks` builds the complete table of `K = ⟨ks⟩`, then searches the left cosets
of `K` in `G = ⟨gs⟩`; it computes `cosetRepsModel n gs ks` (`RunsWithin.cosetRepsProg`) at cost
at most `repsCost n L L' I` for `L` and `L'` generators and the index `I = |G| / |K|`: at most `I`
iterations, each visiting `L` products and testing each against at most `I` found
representatives by one sift.
-/

@[expose] public section

namespace GraphIso.Sims

open Equiv Cost Programs

section Prog

variable {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- Is `x` in the left coset of a found representative? -/
def coveredProg (n : var .nat) (b : var (.array .nat)) (TK : var Ty.table) (reps : var Ty.gens)
    (x : var Ty.perm) : Prog S rec var .bool :=
  anyList reps fun r' =>
    .bind (permInv r') fun ri => .bind (permMul ri x) fun y =>
    .bind (.op0 (.natLit 0)) fun z => .bind (siftProg n b TK z y) fun res =>
    .bind (.op1 .fst res) fun k => .op2 .natEq k n

/-- Visit `g r`. -/
def repsVisitBody (n : var .nat) (b : var (.array .nat)) (TK : var Ty.table) (r : var Ty.perm)
    (acc : var (.prod Ty.gens Ty.gens)) (g : var Ty.perm) :
    Prog S rec var (.prod Ty.gens Ty.gens) :=
  .bind (.op1 .fst acc) fun reps => .bind (.op1 .snd acc) fun q =>
  .bind (permMul g r) fun x => .bind (coveredProg n b TK reps x) fun c =>
  .ite c (.ret acc)
    (.bind (.op2 .cons x reps) fun reps' => .bind (.op2 .cons x q) fun q' => .op2 .pair reps' q')

/-- One iteration of the coset search. -/
def repsStepBody (n : var .nat) (b : var (.array .nat)) (TK : var Ty.table) (gs : var Ty.gens)
    (st : var (.prod Ty.gens Ty.gens)) : Prog S rec var (.option (.prod Ty.gens Ty.gens)) :=
  .bind (.op1 .fst st) fun reps => .bind (.op1 .snd st) fun q =>
  .caseList q (.op0 .none) fun r rest =>
    .bind (.op2 .pair reps rest) fun st₀ =>
    .bind (.foldList gs st₀ fun acc g => repsVisitBody n b TK r acc g) fun st' => .op1 .some st'

/-- Left coset representatives of `⟨ks⟩` in `⟨gs⟩`. -/
def cosetRepsProg (n : var .nat) (gs ks : var Ty.gens) : Prog S rec var Ty.gens :=
  .bind (emptyWinProg n) fun w => .bind (frontBaseProg n w) fun b =>
  .bind (buildProg n b ks) fun stK => .bind (.op1 .fst stK) fun TK =>
  .bind (permOne n) fun e => .bind (.op0 .nil) fun nl => .bind (.op2 .cons e nl) fun l =>
  .bind (.op2 .pair l l) fun st₀ =>
  .bind (.loop st₀ fun st => repsStepBody n b TK gs st) fun fin => .op1 .fst fin

end Prog

/-! ### Costs -/

/-- The cost bound of one visit with at most `I` found representatives. -/
def repsVisitCost (n I : ℕ) : ℕ := I * (siftCost n + 12 * n + 21) + 12 * n + 21

/-- The cost bound of the coset search: `L` and `L'` generators, index `I`. -/
def repsCost (n L L' I : ℕ) : ℕ :=
  buildCost n L' + I * (L * (repsVisitCost n I + 1) + 6) + 10 * n + 30

section Specs

variable {S : Signature} {a b' : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b') Ty.denote b'}
  {n : ℕ} {gs ks : GensData}

theorem RunsWithin.coveredProg (hks : GensData.AllValid n ks) {reps : List PermData}
    (hreps : ∀ r ∈ reps, r.Valid n) {x : PermData} (hx : x.Valid n) :
    RunsWithin X body
      (Sims.coveredProg n (frontBase n (emptyWin n)) (tableFor n (emptyWin n) ks).1 reps x)
      (coveredB n (tableFor n (emptyWin n) ks).1 reps x)
      (reps.length * (siftCost n + 12 * n + 21) + 1) := by
  have hT : SlotsValid n (tableFor n (emptyWin n) ks).1 :=
    (tableFor_inv (emptyWin_valid n) hks).wf.slotsValid
  have := RunsWithin.anyList_le (X := X) (body := body) (a' := Ty.perm) (xs := reps)
    (p := fun r' => .bind (permInv r') fun ri => .bind (permMul ri x) fun y =>
      .bind (.op0 (.natLit 0)) fun z =>
      .bind (Sims.siftProg n (frontBase n (emptyWin n)) (tableFor n (emptyWin n) ks).1 z y)
        fun res =>
      .bind (.op1 .fst res) fun k => .op2 .natEq k n)
    (P := fun r' : PermData => (sift n (frontBase n (emptyWin n)) (tableFor n (emptyWin n) ks).1 0
      (r'.inv.mul x)).1 == n) (c := siftCost n + 12 * n + 19) fun r' hr' => by
      apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.permInv r')
        run_step (RunsWithin.permMul (hreps r' hr').inv hx)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.siftProg hT (Nat.zero_le n) ((hreps r' hr').inv.mul hx))
        run_step (RunsWithin.prim _ _)
        exact RunsWithin.prim_le rfl le_rfl
      case hc =>
        simp only [Prim.cost]
        omega
  exact this.mono (by
    rw [show siftCost n + 12 * n + 19 + 2 = siftCost n + 12 * n + 21 by omega])

theorem RunsWithin.repsVisitBody (hks : GensData.AllValid n ks) {r g : PermData}
    (hr : r.Valid n) (hg : g.Valid n) {acc : List PermData × List PermData}
    (hacc : ∀ r' ∈ acc.1, r'.Valid n) {I : ℕ} (hI : acc.1.length ≤ I) :
    RunsWithin X body
      (Sims.repsVisitBody n (frontBase n (emptyWin n)) (tableFor n (emptyWin n) ks).1 r acc g)
      (repsVisit n (tableFor n (emptyWin n) ks).1 r acc g) (repsVisitCost n I) := by
  have hx : (g.mul r).Valid n := hg.mul hr
  have hcov := RunsWithin.coveredProg (X := X) (body := body) hks hacc hx
  have hle : acc.1.length * (siftCost n + 12 * n + 21) ≤ I * (siftCost n + 12 * n + 21) :=
    Nat.mul_le_mul_right _ hI
  by_cases hc : coveredB n (tableFor n (emptyWin n) ks).1 acc.1 (g.mul r) = true
  · have hF : repsVisit n (tableFor n (emptyWin n) ks).1 r acc g = acc := by
      simp [repsVisit, hc]
    rw [hF]
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.permMul hg hr)
      run_step hcov
      exact RunsWithin.ite_pos hc (RunsWithin.ret _)
    case hc =>
      simp only [Prim.cost, repsVisitCost]
      omega
  · have hF : repsVisit n (tableFor n (emptyWin n) ks).1 r acc g =
        (g.mul r :: acc.1, g.mul r :: acc.2) := by
      simp [repsVisit, hc]
    rw [hF]
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.permMul hg hr)
      run_step hcov
      run_with RunsWithin.ite_neg (Bool.eq_false_iff.2 hc :
        coveredB n (tableFor n (emptyWin n) ks).1 acc.1 (g.mul r) = false) _
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      exact RunsWithin.prim_le rfl le_rfl
    case hc =>
      simp only [Prim.cost, repsVisitCost]
      omega

theorem RunsWithin.repsStepBody (hgs : GensData.AllValid n gs) (hks : GensData.AllValid n ks)
    (hK : GensData.denote n ks ≤ GensData.denote n gs) {st : List PermData × List PermData}
    (hst : RBInv n (GensData.denote n gs) (GensData.denote n ks) st) :
    RunsWithin X body
      (Sims.repsStepBody n (frontBase n (emptyWin n)) (tableFor n (emptyWin n) ks).1 gs st)
      (repsStep n (tableFor n (emptyWin n) ks).1 gs st)
      (if st.2 = [] then 4 else gs.length * (repsVisitCost n
        (Nat.card (GensData.denote n gs) / Nat.card (GensData.denote n ks)) + 1) + 5) := by
  obtain ⟨reps, q⟩ := st
  simp only at hst ⊢
  rcases q with _ | ⟨r, rest⟩
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      exact RunsWithin.caseList_nil (RunsWithin.prim _ _)
    case hc =>
      simp [Prim.cost]
  · obtain ⟨hrv, hrG⟩ := hst.valid r (hst.queue_sub r List.mem_cons_self)
    have h₀ : RBInv n (GensData.denote n gs) (GensData.denote n ks) (reps, rest) :=
      ⟨hst.valid, hst.distinct, fun q hq => hst.queue_sub q (List.mem_cons_of_mem _ hq),
        (List.nodup_cons.1 hst.queue_nodup).2⟩
    have hfold := (RunsWithin.foldList_inv (X := X) (body := body) (a' := Ty.perm)
      (b' := .prod Ty.gens Ty.gens)
      (f := fun acc g => Sims.repsVisitBody n (frontBase n (emptyWin n))
        (tableFor n (emptyWin n) ks).1 r acc g)
      (F := repsVisit n (tableFor n (emptyWin n) ks).1 r)
      (I := RBInv n (GensData.denote n gs) (GensData.denote n ks))
      (c := repsVisitCost n (Nat.card (GensData.denote n gs) / Nat.card (GensData.denote n ks)))
      gs (reps, rest) (fun acc hacc g hg =>
        ⟨RunsWithin.repsVisitBody hks hrv (hgs g hg) (fun r' hr' => (hacc.valid r' hr').1)
          (length_le_index hacc.valid hacc.distinct hK),
          (repsVisit_spec hks hrv hrG (hgs g hg) (GensData.mem_denote_of_mem hg) hacc).1⟩) h₀).1
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_with RunsWithin.caseList_cons _
      run_step (RunsWithin.prim _ _)
      run_step hfold
      exact RunsWithin.prim _ _
    case hc =>
      simp only [Prim.cost, reduceCtorEq, ↓reduceIte]
      omega

/-- The potential of the coset search loop. -/
def repsPot (n L I : ℕ) (st : List PermData × List PermData) : ℕ :=
  rpot I st * (L * (repsVisitCost n I + 1) + 6) + 5

/-- **The coset search costs at most `repsCost n L L' I`.** -/
theorem RunsWithin.cosetRepsProg (hgs : GensData.AllValid n gs) (hks : GensData.AllValid n ks)
    (hK : GensData.denote n ks ≤ GensData.denote n gs) :
    RunsWithin X body (Sims.cosetRepsProg n gs ks) (cosetRepsModel n gs ks)
      (repsCost n gs.length ks.length
        (Nat.card (GensData.denote n gs) / Nat.card (GensData.denote n ks))) := by
  set I := Nat.card (GensData.denote n gs) / Nat.card (GensData.denote n ks) with hI_def
  have hI1 : 1 ≤ I := Nat.div_pos (Subgroup.card_le_of_le hK) Nat.card_pos
  have hb := frontBase_base (emptyWin_valid n)
  have hR₀ : RInv n gs ks ([PermData.one n], [PermData.one n]) := by
    refine ⟨⟨fun r hr => ?_, List.pairwise_singleton _ _, fun r hr => hr,
      List.nodup_singleton _⟩, fun r hr hrq => absurd (by simpa using hr) (by simpa using hrq),
      List.mem_singleton_self _⟩
    rw [List.mem_singleton.1 hr]
    exact ⟨PermData.valid_one n, by rw [PermData.denote_one]; exact one_mem _⟩
  have hpot₀ : rpot I ([PermData.one n], [PermData.one n]) = I := by
    simp only [rpot, List.length_singleton]
    omega
  have hloop := RunsWithin.loop_pot (X := X) (body := body)
    (f := Sims.repsStepBody n (frontBase n (emptyWin n)) (tableFor n (emptyWin n) ks).1 gs)
    (F := repsStep n (tableFor n (emptyWin n) ks).1 gs) (I := RInv n gs ks)
    (Φ := repsPot n gs.length I)
    (fun st hst => ⟨_, RunsWithin.repsStepBody hgs hks hK hst.toRBInv, fun hF => by
        rcases hq : st.2 with _ | ⟨r, rest⟩
        · simp [repsPot]
        · simp [repsStep, hq] at hF, fun st' hF => by
        rcases hq : st.2 with _ | ⟨r, rest⟩
        · simp [repsStep, hq] at hF
        · obtain ⟨st'', hstep, hI', hpot⟩ := repsStep_spec hgs hks hK hst hq
          have e : st' = st'' := Option.some.inj (hF.symm.trans hstep)
          subst e
          refine ⟨hI', ?_⟩
          rw [← hI_def] at hpot
          simp only [reduceCtorEq, ↓reduceIte, repsPot, ← hI_def]
          have : rpot I st' * (gs.length * (repsVisitCost n I + 1) + 6) +
              (gs.length * (repsVisitCost n I + 1) + 6) ≤
              rpot I st * (gs.length * (repsVisitCost n I + 1) + 6) := by
            rw [← Nat.succ_mul]
            exact Nat.mul_le_mul_right _ hpot
          omega⟩)
    (repsPot n gs.length I ([PermData.one n], [PermData.one n]) + 1)
    ([PermData.one n], [PermData.one n]) hR₀ (Nat.lt_succ_self _)
  have hdone := iter_repsStep hgs hks hK (I + 1) _ hR₀ (by rw [← hI_def]; omega)
  have hfix : repsStep n (tableFor n (emptyWin n) ks).1 gs (iter (repsStep n
      (tableFor n (emptyWin n) ks).1 gs) (I + 1) ([PermData.one n], [PermData.one n])) = none := by
    simp [repsStep, hdone.2]
  have h₁ := iter_eq_of_fix _ _ hfix
    (repsPot n gs.length I ([PermData.one n], [PermData.one n]) + 1)
    (by
      simp only [repsPot, hpot₀]
      have : I ≤ I * (gs.length * (repsVisitCost n I + 1) + 6) :=
        Nat.le_mul_of_pos_right _ (by omega)
      omega)
  have h₂ := iter_eq_of_fix _ _ hfix (n.factorial + 1) (by
    have := card_le_factorial (GensData.denote n gs)
    have : I ≤ Nat.card (GensData.denote n gs) := Nat.div_le_self _ _
    omega)
  rw [h₁, ← h₂] at hloop
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.emptyWinProg n)
    run_step (RunsWithin.frontBaseProg (emptyWin n))
    run_step (RunsWithin.buildProg hb hks)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.permOne n)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step hloop
    exact RunsWithin.prim _ _
  case hc =>
    simp only [Prim.cost, repsPot, hpot₀, repsCost, emptyWin, List.length_nil]
    omega

end Specs

end GraphIso.Sims
