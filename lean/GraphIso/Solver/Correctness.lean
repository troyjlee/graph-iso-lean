module

public import GraphIso.Solver.Cost
public import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# Correctness and cost of the solver

`solve_spec`: against any backend meeting its contract, with bounded charges and output
generator counts (`BackendBounds`), the solver returns a correct answer for every valid
instance, with output groups of at most `s` generators, at cost at most
`solveBound Q m N` for window size `m` and group order `N`.

The proof is by strong induction on the window size and, inside it, on the group order:
orbit calls have smaller windows, and branch calls keep the window and pass to the point
stabilizer, whose order is `N / k` for the orbit length `k ≥ 2` (`IsLeftTransversal.card_eq`).
-/

@[expose] public section

namespace GraphIso.Solver

open Equiv Pointwise Cost Programs

variable {D : Ty} {X : Ctx (groupSig D)}

/-! ### Peeling the program -/

section Peel

variable {xy : StrData × StrData} {σd : PermData} {G : GroupData D.denote}

theorem run_solveBody {w : WinData} {ans : AnswerData D} {k : ℕ}
    (h : RunsWithin X (solveBody D Ty.denote)
      (Prog.caseList (a := .nat) w.1 (.op1 .some (σd, G))
        fun u _ => nonemptyCase (D := D) xy w w.1 (σd, G) σd G u) ans k) :
    RunsWithin X (solveBody D Ty.denote) (solveBody D Ty.denote (xy, w, σd, G)) ans (7 + k) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact h
  case hc =>
    simp only [Prim.cost]
    omega

theorem run_nonempty_fixed {w : WinData} {u : ℕ} {ans : AnswerData D} {k : ℕ}
    (hfix : GensData.fixesB G.gens w = true)
    (h : RunsWithin X (solveBody D Ty.denote) (fixedCase (D := D) xy w.1 σd (σd, G)) ans k) :
    RunsWithin X (solveBody D Ty.denote) (nonemptyCase (D := D) xy w w.1 (σd, G) σd G u) ans
      (G.gens.length * (5 * w.1.length + 3) + 4 + k) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.fixesProg G.gens w)
    rw [hfix]
    exact RunsWithin.ite_true h
  case hc =>
    simp only [Prim.cost, GroupData.gens]
    omega

theorem run_nonempty_moved {w : WinData} {u : ℕ} {ans : AnswerData D} {k : ℕ}
    (hfix : GensData.fixesB G.gens w = false)
    (h : RunsWithin X (solveBody D Ty.denote) (movedCase (D := D) xy w (σd, G) σd G u) ans k) :
    RunsWithin X (solveBody D Ty.denote) (nonemptyCase (D := D) xy w w.1 (σd, G) σd G u) ans
      (G.gens.length * (5 * w.1.length + 3) + 4 + k) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.fixesProg G.gens w)
    rw [hfix]
    exact RunsWithin.ite_false h
  case hc =>
    simp only [Prim.cost, GroupData.gens]
    omega

theorem run_fixedCase {w : WinData} :
    RunsWithin X (solveBody D Ty.denote) (fixedCase (D := D) xy w.1 σd (σd, G))
      (if matchesB w σd xy.1 xy.2 then some (σd, G) else none) (7 * w.1.length + 5) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.matchesProg w σd xy)
    cases matchesB w σd xy.1 xy.2
    · exact RunsWithin.ite_false (RunsWithin.prim _ _)
    · exact RunsWithin.ite_true (RunsWithin.prim _ _)
  case hc =>
    simp only [Prim.cost]
    omega

/-- The orbit case, given the orbit list returned by the backend. -/
theorem run_movedCase {w : WinData} {u : ℕ} {ans : AnswerData D} {k : ℕ}
    (hk : RunsWithin X (solveBody D Ty.denote)
      (Prog.caseList (a := .list .nat) (X.O.run .orbits (G, w)) (.op0 .none) fun _ orest =>
        Prog.caseList orest (transitiveCase (D := D) xy w σd G u) fun _ _ =>
          seqProg (fun J => .recur J) xy (σd, G) (X.O.run .orbits (G, w))) ans k)
    (hpre : X.Pre .orbits (G, w)) :
    RunsWithin X (solveBody D Ty.denote) (movedCase (D := D) xy w (σd, G) σd G u) ans
      (1 + X.B.call .orbits (G, w) (X.O.run .orbits (G, w)) + k) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.call hpre)
    exact hk
  case hc =>
    simp only [Prim.cost, Prim.eval]
    omega

/-- The transitive case, given the stabilizer and transversal returned by the backend. -/
theorem run_transitiveCase {w : WinData} {u : ℕ} {ans : AnswerData D} {k : ℕ}
    (hk : RunsWithin X (solveBody D Ty.denote)
      (branchProg (fun J => .recur J) xy w σd (X.O.run .stabilizer (G, u))
        ((X.O.run .orbitTransversal (G, u)).map Prod.snd)) ans k)
    (hps : X.Pre .stabilizer (G, u)) (hpt : X.Pre .orbitTransversal (G, u)) :
    RunsWithin X (solveBody D Ty.denote) (transitiveCase (D := D) xy w σd G u) ans
      (1 + X.B.call .stabilizer (G, u) (X.O.run .stabilizer (G, u)) +
        X.B.call .orbitTransversal (G, u) (X.O.run .orbitTransversal (G, u)) +
        (4 * (X.O.run .orbitTransversal (G, u)).length + 2) + k) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.call hps)
    run_step (RunsWithin.call hpt)
    run_step (RunsWithin.mapList_le (c := 1) (F := Prod.snd) fun vr _ => RunsWithin.prim _ _)
    exact hk
  case hc =>
    simp only [Prim.cost, Prim.eval]
    omega

end Peel

end GraphIso.Solver

namespace GraphIso.Solver

open Equiv Pointwise Cost Programs

variable {D : Ty} {X : Ctx (groupSig D)} {DV : ℕ → GensData → D.denote → Prop}

/-- The solver's specification at window size `m` and group order `N`: for every valid
instance of degree `n` with at most `s` generators, the solver returns a correct answer with at
most `s` output generators, at cost at most `solveBound Q m N`. -/
def SolveSpec (X : Ctx (groupSig D)) (DV : ℕ → GensData → D.denote → Prop) (n s : ℕ)
    (G₀ : Subgroup (Perm (Fin n))) (Q m N : ℕ) : Prop :=
  ∀ (xy : StrData × StrData) (w : WinData) (σd : PermData) (gs : GensData) (d : D.denote),
    InstData.Valid (D := D) (xy, w, σd, n, gs, d) DV → gs.length ≤ s →
    GensData.denote n gs ≤ G₀ → w.1.length = m →
    Nat.card (GensData.denote n gs) = N →
    ∃ ans : AnswerData D,
      RunsWithin X (solveBody D Ty.denote) (solveBody D Ty.denote (xy, w, σd, n, gs, d)) ans
        (solveBound Q m N) ∧
      InstData.OK (D := D) (xy, w, σd, n, gs, d) DV ans ∧
      ∀ c : CosetData D, ans = some c → c.2.gens.length ≤ s

/-- **Correctness and cost of the solver.** Only the four operations the solver calls need to
meet their contracts and be allowed by the context. -/
theorem solve_spec (hO : MeetsContractOn DV solverOps X.O)
    (hPre : ∀ op x, solverOps op → GroupPre DV op x → X.Pre op x)
    {n s : ℕ} {G₀ : Subgroup (Perm (Fin n))} (B : BackendBounds X DV n s G₀) :
    ∀ m N, SolveSpec X DV n s G₀ (solveQ n s B.Borb B.Bstab B.Btr B.Bgen) m N := by
  set Q := solveQ n s B.Borb B.Bstab B.Btr B.Bgen with hQ
  set P := nodeCost n s B.Borb B.Bstab B.Btr B.Bgen with hP
  set E := edgeCost n s with hE
  have hPE : P + 2 * E ≤ Q := le_rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ihm =>
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ihN =>
  intro xy w σd gs d hv hs hG₀ hm hN
  have hv' := hv
  obtain ⟨hwv, hσ, hGv, hinv⟩ := hv'
  change WinData.Valid n w at hwv
  change PermData.Valid n σd at hσ
  change GroupValid DV n gs d at hGv
  change IsInvariant (GensData.denote n gs) (WinData.denote n w) at hinv
  have hNpos : 0 < N := hN ▸ Nat.card_pos
  have hmn : m ≤ n := hm ▸ WinData.length_le hwv
  rcases w with ⟨pts, mask⟩
  rcases pts with _ | ⟨u, rest⟩
  · -- the empty window
    have hm0 : m = 0 := by simpa using hm.symm
    refine ⟨some (σd, n, gs, d), ?_, ?_, fun c hc => by cases hc; exact hs⟩
    · refine (run_solveBody (RunsWithin.caseList_nil (RunsWithin.prim _ _))).mono ?_
      simp only [Prim.cost, hm0, solveBound, ↓reduceIte, hQ, solveQ, nodeCost]
      omega
    · have hW : WinData.denote n ([], mask) = ∅ := by
        ext v; simp [WinData.denote]
      change AnsOK DV n (WinData.denote n ([], mask)) _ _ _ _ _
      rw [hW]
      exact AnsOK.empty_window hσ rfl hGv
  · -- a nonempty window
    have hu : u < n := hwv.lt u List.mem_cons_self
    have hm0 : m ≠ 0 := by simp at hm; omega
    have hselfQ : ∀ c, c ≤ P → c ≤ solveBound Q m N := fun c hc =>
      le_solveBound_of_le hm0 hNpos (hc.trans (by omega))
    cases hfix : GensData.fixesB gs (u :: rest, mask)
    · -- the window is moved: ask for the orbits
      have hnfix : ¬ FixesPointwise (GensData.denote n gs) (WinData.denote n (u :: rest, mask)) :=
        fun h => by rw [(GensData.fixesB_iff hGv.1 hwv).2 h] at hfix; cases hfix
      have hpreO : GroupPre DV .orbits ((n, gs, d), (u :: rest, mask)) := ⟨hGv, hwv, hinv⟩
      have hpostO := hO .orbits _ (Or.inl rfl) hpreO
      have hBorb := B.orbits gs d _ hs hG₀ hpreO
      change IsOrbitPartition (GensData.denote n gs) (u :: rest, mask)
        (X.O.run .orbits ((n, gs, d), (u :: rest, mask))) at hpostO
      rcases hos : X.O.run GroupOp.orbits ((n, gs, d), (u :: rest, mask)) with
        _ | ⟨o₀, _ | ⟨o₁, rest'⟩⟩
      · -- no orbits: impossible for a nonempty window
        rw [hos] at hpostO
        exact absurd rfl (hpostO.ne_nil (by simp))
      · -- one orbit: the window is transitive; branch over the stabilizer of `u`
        rw [hos] at hpostO
        have htrans := hpostO.transitive_of_singleton (i := u) List.mem_cons_self
        have hrest : rest ≠ [] := by
          rintro rfl
          exact hnfix (fixesPointwise_of_singleton rfl hinv)
        have hm2 : 2 ≤ m := by
          rw [← hm]
          cases rest with
          | nil => exact absurd rfl hrest
          | cons _ _ => simp
        -- the stabilizer
        have hpreS : GroupPre DV .stabilizer ((n, gs, d), u) := ⟨hGv, hu⟩
        have hBstab := B.stabilizer gs d u hs hG₀ hpreS
        have hsK := B.stabOut gs d u hG₀ hpreS
        have hpostS := hO .stabilizer _ (Or.inr (Or.inl rfl)) hpreS
        rcases hK : X.O.run GroupOp.stabilizer ((n, gs, d), u) with ⟨n', ks, e⟩
        rw [hK] at hpostS hBstab hsK
        obtain ⟨hn', hKv, hKden⟩ := hpostS
        change n' = n at hn'
        subst n'
        have hKden' : GensData.denote n ks = pointStab (GensData.denote n gs) ⟨u, hu⟩ := hKden hu
        -- the transversal
        have hpreT : GroupPre DV .orbitTransversal ((n, gs, d), u) := ⟨hGv, hu⟩
        have hBtr := B.transversal gs d u hs hG₀ hpreT
        have hpostT := hO .orbitTransversal _ (Or.inr (Or.inr (Or.inl rfl))) hpreT
        obtain ⟨trs, htrs⟩ : ∃ trs : List (ℕ × PermData),
            X.O.run GroupOp.orbitTransversal ((n, gs, d), u) = trs := ⟨_, rfl⟩
        rw [htrs] at hpostT hBtr
        obtain ⟨hnd, horb, hrs⟩ := hpostT
        have htl : trs.length = m := by
          rw [← hm]
          exact length_orbitTransversal hwv htrans hnd horb
        have htv := isLeftTransversal_of_orbitTransversal hu hnd horb hrs
        have hKG : GensData.denote n ks ≤ GensData.denote n gs := by
          rw [hKden']
          exact inf_le_left
        have hcard := htv.card_eq (hKden' ▸ hKG)
        simp only [List.length_map, htl] at hcard
        rw [← hKden', hN] at hcard
        set N' := Nat.card (GensData.denote n ks) with hN'
        have hN'pos : 0 < N' := Nat.card_pos
        have hN'lt : N' < N := by rw [hcard]; nlinarith
        -- every branch is solved by a recursive call
        have hsub : SubSolves X (solveBody D Ty.denote) DV (fun J => .recur J)
            (fun I => I.1 = xy ∧ I.2.1 = (u :: rest, mask) ∧ I.2.2.2 = (n, ks, e) ∧
              (∃ r ∈ trs.map Prod.snd, I.2.2.1 = σd.mul r) ∧ I.Valid DV)
            (fun _ => 1 + solveBound Q m N') s := by
          rintro ⟨xy', w', τ, G'⟩ ⟨hxy, hw', hG', -, hval⟩
          simp only at hxy hw' hG'
          subst xy' w' G'
          obtain ⟨ans, hr, hok, hg⟩ := ihN N' hN'lt xy (u :: rest, mask) τ ks e hval hsK
            (hKG.trans hG₀) hm rfl
          exact ⟨ans, RunsWithin.recur hr, hok, hg⟩
        have hrsv : ∀ r ∈ trs.map Prod.snd, PermData.Valid n r := by
          intro r hr
          obtain ⟨vr, hvr, rfl⟩ := List.mem_map.1 hr
          exact (hrs vr hvr).1
        have hgenB : ∀ gs' : GensData, GensData.AllValid n gs' →
            gs'.length ≤ (trs.map Prod.snd).length * (s + 1) →
            GensData.denote n gs' ≤ GensData.denote n gs →
            X.B.call GroupOp.generate (n, gs') (X.O.run GroupOp.generate (n, gs')) ≤ B.Bgen :=
          fun gs' hv' hl hle => B.generate gs' hv' (hl.trans (by
            simp only [List.length_map, htl]
            exact Nat.mul_le_mul_right _ hmn)) (hle.trans hG₀)
        obtain ⟨ans, hr, hok, hg⟩ := RunsWithin.branchProg
          (fun op x hop => hO op x (by subst hop; exact Or.inr (Or.inr (Or.inr rfl))))
          (fun x => hPre .generate x (Or.inr (Or.inr (Or.inr rfl)))) hwv hσ hKv hKG hinv hrsv
          (by rw [← hKden'] at htv; exact htv.toIsLeftCover) hsub hgenB
        refine ⟨ans, ?_, hok, hg s fun gs' hv' hle => B.genOut gs' hv' (hle.trans hG₀)⟩
        have hrun := run_solveBody (xy := xy) (σd := σd) (G := (n, gs, d)) (w := (u :: rest, mask))
          (RunsWithin.caseList_cons (run_nonempty_moved (G := (n, gs, d)) (u := u)
            (w := (u :: rest, mask)) hfix
            (run_movedCase (by
              rw [hos]
              exact RunsWithin.caseList_cons (RunsWithin.caseList_nil
                (run_transitiveCase (by rw [hK, htrs]; exact hr)
                  (hPre _ _ (Or.inr (Or.inl rfl)) hpreS)
                  (hPre _ _ (Or.inr (Or.inr (Or.inl rfl))) hpreT))))
              (hPre _ _ (Or.inl rfl) hpreO))))
        refine hrun.mono ?_
        rw [hcard, hK, htrs]
        have hlenm : rest.length + 1 = m := by simpa using hm
        simp only [List.length_map, htl, GroupData.gens, List.length_cons, hlenm]
        have harith := branch_arith (Q := Q) (P := P) (E := E) (m := m) (k := m) (N' := N')
          (self := gs.length * (5 * m + 3) + B.Borb + B.Bstab + B.Btr + B.Bgen + 37) hPE
          (by
            simp only [hP, nodeCost]
            have : gs.length * (5 * m + 3) ≤ s * (5 * n + 3) :=
              Nat.mul_le_mul hs (by omega)
            omega) hm2 hm0 hN'pos
        simp only [hE, edgeCost] at harith
        nlinarith [harith, hBorb, hBstab, hBtr]
      · -- several orbits: solve them sequentially, each by a recursive call
        rw [hos] at hpostO
        set os := o₀ :: o₁ :: rest' with hos'
        obtain ⟨hseq, hunion⟩ := seqInputs_of_isOrbitPartition hwv hpostO
        have hsub : SeqSub X (solveBody D Ty.denote) DV (fun J => .recur J) xy n os
            (fun o => 1 + solveBound Q o.length N) s (max s gs.length) (GensData.denote n gs) := by
          rintro ⟨xy', w', τ, n'', ks', e'⟩ ⟨hxy, hval, hdeg, ⟨o, ho, hw'⟩, hlen, hle⟩
          simp only at hxy hw' hlen hle
          change n'' = n at hdeg
          subst xy' w' n''
          have hlt : o.length < m := by
            rw [← hm]
            exact hpostO.length_lt ho
          have hcardle : Nat.card (GensData.denote n ks') ≤ N :=
            hN ▸ Subgroup.card_le_of_le hle
          obtain ⟨ans, hr, hok, hg⟩ := ihm o.length hlt (Nat.card (GensData.denote n ks')) xy
            (WinData.ofPoints n o) τ ks' e' hval
            (by simpa [GroupData.gens, max_eq_left hs] using hlen) (hle.trans hG₀) rfl rfl
          exact ⟨ans, (RunsWithin.recur hr).mono (by
            have := solveBound_mono (Q := Q) (m := o.length) hcardle
            simp only [WinData.ofPoints_fst]
            omega), hok, hg⟩
        obtain ⟨ans, hr, hok, hg⟩ := RunsWithin.seqProg (σd := σd) (Gd := (n, gs, d)) rfl hσ hGv
          hseq hsub
        refine ⟨ans, ?_, ?_, fun c hc => (hg c hc).trans (max_le le_rfl hs)⟩
        · have hrun := run_solveBody (xy := xy) (σd := σd) (G := (n, gs, d))
            (w := (u :: rest, mask))
            (RunsWithin.caseList_cons (run_nonempty_moved (G := (n, gs, d)) (u := u)
              (w := (u :: rest, mask)) hfix
              (run_movedCase (by
                rw [hos]
                exact RunsWithin.caseList_cons (RunsWithin.caseList_cons hr))
                (hPre _ _ (Or.inl rfl) hpreO))))
          refine hrun.mono ?_
          have hlen2 : 2 ≤ os.length := by simp [hos']
          have hpos : ∀ o ∈ os, 0 < o.length := fun o ho => hpostO.length_pos ho
          have hsumm : (os.map List.length).sum = m := by rw [← hm]; exact hpostO.length_sum
          have harith := seq_arith (Q := Q) (P := P) (E := E) (N := N)
            (self := gs.length * (5 * m + 3) + B.Borb + 17) hPE
            (by
              simp only [hP, nodeCost]
              have : gs.length * (5 * m + 3) ≤ s * (5 * n + 3) :=
                Nat.mul_le_mul hs (by omega)
              omega) hNpos hlen2 hpos (f := seqCost n fun o => 1 + solveBound Q o.length N)
            (fun o ho => by
              have hon : o.length ≤ n := (hpostO.length_lt ho).le.trans (hm ▸ hmn)
              simp only [seqCost, hE, edgeCost]
              omega)
          rw [hsumm] at harith
          have hlenm : rest.length + 1 = m := by simpa using hm
          simp only [GroupData.gens, GroupData.degree, List.length_cons, hlenm]
          omega
        · change AnsOK DV n (WinData.denote n (u :: rest, mask)) _ _ _ _ _
          rw [← hunion]
          exact hok
    · -- the group fixes the window pointwise
      have hfixS : FixesPointwise (GensData.denote n gs) (WinData.denote n (u :: rest, mask)) :=
        (GensData.fixesB_iff hGv.1 hwv).1 hfix
      refine ⟨if matchesB (u :: rest, mask) σd xy.1 xy.2 then some (σd, n, gs, d) else none,
        ?_, ?_, ?_⟩
      · refine (run_solveBody (RunsWithin.caseList_cons
          (run_nonempty_fixed (G := (n, gs, d)) hfix run_fixedCase))).mono (hselfQ _ ?_)
        simp only [hP, nodeCost, GroupData.gens, List.length_cons] at hm ⊢
        rw [← hm] at hmn
        nlinarith
      · change AnsOK DV n _ _ _ _ _ _
        cases hmat : matchesB (u :: rest, mask) σd xy.1 xy.2
        · have := (matchesB_iff hwv hσ xy.1 xy.2).not.1 (by simp [hmat])
          exact iso_of_fixesPointwise_of_not_matches hfixS this
        · have := (matchesB_iff hwv hσ xy.1 xy.2).1 hmat
          exact ⟨hσ, rfl, hGv, (iso_of_fixesPointwise_of_matches hfixS this).symm⟩
      · intro c hc
        split at hc
        · cases hc; exact hs
        · cases hc

end GraphIso.Solver
