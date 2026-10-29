module

public import GraphIso.Solver.Checked
public import GraphIso.Sims.Wf
public import Mathlib.Tactic.GCongr

/-!
# The solver with the Schreier–Sims backend

`ssImpl` implements all eight group operations by the programs of `GraphIso/Sims/` (over the
empty signature). `ssImpl_implements` proves that they compute the oracle `ssOracle`, which
meets every contract (`ssOracle_meets`), within the schedule `ssB` on every input satisfying
the contract preconditions; `ssImpl_wf` proves them well-formed.

The charges are polynomial in the degree `n`, the generator counts and, for `cosetReps`, the
number of representatives; output groups have at most `n²` generators. So `ssBounds` gives the
solver's backend bounds with `s = n²` for **every** ambient group, independently of its order.

`solve_sims`: the public solver with this backend is a closed, well-formed program; on every
valid input it returns a correct answer at cost at most
`simsCost n L m N = 11 + genCost n L + 2 + solveBound (simsQ n) m N`, where `simsQ n` is an
explicit polynomial in `n` alone. `solve_sims_checked`: the validating entry, on every input.
-/

@[expose] public section

namespace GraphIso.Sims

open Equiv Cost Programs Solver

/-- The Schreier–Sims implementations of the group operations. -/
def ssImpl : Impl (groupSig Ty.unit) Signature.empty := fun op _ _ x =>
  match op, x with
  | .generate, x => .bind (.op1 .fst x) fun n => .bind (.op1 .snd x) fun gs => generateProg n gs
  | .mem, x =>
    .bind (.op1 .fst x) fun G => .bind (.op1 .snd x) fun π =>
    .bind (.op1 .fst G) fun n => .bind (.op1 .snd G) fun gd => .bind (.op1 .fst gd) fun gs =>
    memProg n gs π
  | .orbits, x =>
    .bind (.op1 .fst x) fun G => .bind (.op1 .snd x) fun w =>
    .bind (.op1 .fst G) fun n => .bind (.op1 .snd G) fun gd => .bind (.op1 .fst gd) fun gs =>
    orbitsProg n gs w
  | .stabilizer, x =>
    .bind (.op1 .fst x) fun G => .bind (.op1 .snd x) fun u =>
    .bind (.op1 .fst G) fun n => .bind (.op1 .snd G) fun gd => .bind (.op1 .fst gd) fun gs =>
    stabProg n gs u
  | .orbitTransversal, x =>
    .bind (.op1 .fst x) fun G => .bind (.op1 .snd x) fun u =>
    .bind (.op1 .fst G) fun n => .bind (.op1 .snd G) fun gd => .bind (.op1 .fst gd) fun gs =>
    orbitBFSProg n gs u
  | .cosetReps, x =>
    .bind (.op1 .fst x) fun G => .bind (.op1 .snd x) fun K =>
    .bind (.op1 .fst G) fun n => .bind (.op1 .snd G) fun gd => .bind (.op1 .fst gd) fun gs =>
    .bind (.op1 .snd K) fun kd => .bind (.op1 .fst kd) fun ks =>
    cosetRepsProg n gs ks
  | .kernel, x =>
    .bind (.op1 .fst x) fun G => .bind (.op1 .snd x) fun w =>
    .bind (.op1 .fst G) fun n => .bind (.op1 .snd G) fun gd => .bind (.op1 .fst gd) fun gs =>
    kernelProg n gs w
  | .lift, x =>
    .bind (.op1 .fst x) fun G => .bind (.op1 .snd x) fun wπ =>
    .bind (.op1 .fst wπ) fun w => .bind (.op1 .snd wπ) fun π' =>
    .bind (.op1 .fst G) fun n => .bind (.op1 .snd G) fun gd => .bind (.op1 .fst gd) fun gs =>
    liftProg n gs w π'

/-- The Schreier–Sims implementations are well-formed and make no recursive calls. -/
theorem ssImpl_wf : ssImpl.Wf := by
  intro op rec var₁ var₂ x₁ x₂
  cases op with
  | generate =>
    exact .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun n₁ n₂ =>
      .bind (.prim _ (.cons (.tail _ (.head _)) .nil)) fun g₁ g₂ =>
      wf_generateProg (by simp) (List.Mem.head _)
  | mem =>
    exact .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun G₁ G₂ =>
      .bind (.prim _ (.cons (.tail _ (.head _)) .nil)) fun π₁ π₂ =>
      .bind (.prim _ (.cons (by simp) .nil)) fun n₁ n₂ =>
      .bind (.prim _ (.cons (by simp) .nil)) fun d₁ d₂ =>
      .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun g₁ g₂ =>
      wf_memProg (by simp) (List.Mem.head _) (by simp)
  | orbits =>
    exact .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun G₁ G₂ =>
      .bind (.prim _ (.cons (.tail _ (.head _)) .nil)) fun w₁ w₂ =>
      .bind (.prim _ (.cons (by simp) .nil)) fun n₁ n₂ =>
      .bind (.prim _ (.cons (by simp) .nil)) fun d₁ d₂ =>
      .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun g₁ g₂ =>
      wf_orbitsProg (by simp) (List.Mem.head _) (by simp)
  | stabilizer =>
    exact .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun G₁ G₂ =>
      .bind (.prim _ (.cons (.tail _ (.head _)) .nil)) fun u₁ u₂ =>
      .bind (.prim _ (.cons (by simp) .nil)) fun n₁ n₂ =>
      .bind (.prim _ (.cons (by simp) .nil)) fun d₁ d₂ =>
      .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun g₁ g₂ =>
      wf_stabProg (by simp) (List.Mem.head _) (by simp)
  | orbitTransversal =>
    exact .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun G₁ G₂ =>
      .bind (.prim _ (.cons (.tail _ (.head _)) .nil)) fun u₁ u₂ =>
      .bind (.prim _ (.cons (by simp) .nil)) fun n₁ n₂ =>
      .bind (.prim _ (.cons (by simp) .nil)) fun d₁ d₂ =>
      .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun g₁ g₂ =>
      wf_orbitBFSProg (by simp) (List.Mem.head _) (by simp)
  | cosetReps =>
    exact .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun G₁ G₂ =>
      .bind (.prim _ (.cons (.tail _ (.head _)) .nil)) fun K₁ K₂ =>
      .bind (.prim _ (.cons (by simp) .nil)) fun n₁ n₂ =>
      .bind (.prim _ (.cons (by simp) .nil)) fun d₁ d₂ =>
      .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun g₁ g₂ =>
      .bind (.prim _ (.cons (by simp) .nil)) fun e₁ e₂ =>
      .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun k₁ k₂ =>
      wf_cosetRepsProg (by simp) (by simp) (List.Mem.head _)
  | kernel =>
    exact .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun G₁ G₂ =>
      .bind (.prim _ (.cons (.tail _ (.head _)) .nil)) fun w₁ w₂ =>
      .bind (.prim _ (.cons (by simp) .nil)) fun n₁ n₂ =>
      .bind (.prim _ (.cons (by simp) .nil)) fun d₁ d₂ =>
      .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun g₁ g₂ =>
      wf_kernelProg (by simp) (List.Mem.head _) (by simp)
  | lift =>
    exact .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun G₁ G₂ =>
      .bind (.prim _ (.cons (.tail _ (.head _)) .nil)) fun p₁ p₂ =>
      .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun w₁ w₂ =>
      .bind (.prim _ (.cons (by simp) .nil)) fun π₁ π₂ =>
      .bind (.prim _ (.cons (by simp) .nil)) fun n₁ n₂ =>
      .bind (.prim _ (.cons (by simp) .nil)) fun d₁ d₂ =>
      .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun g₁ g₂ =>
      wf_liftProg (by simp) (List.Mem.head _) (by simp) (by simp)

/-- The Schreier–Sims cost schedule: the proved bound of each implementation on its actual
argument (and, for `cosetReps`, the number of representatives it returns). -/
def ssB : CostSchedule (groupSig Ty.unit) := ⟨fun op x y =>
  match op, x, y with
  | .generate, (n, gs), _ => genCost n gs.length + 2
  | .mem, ((n, gs, _), _), _ => memCost n gs.length + 5
  | .orbits, ((n, gs, _), w), _ => orbitsCost n gs.length w.1.length + 5
  | .stabilizer, ((n, gs, _), _), _ => stabCost n gs.length + 5
  | .orbitTransversal, ((n, gs, _), _), _ => transCost n gs.length + 5
  | .cosetReps, ((n, gs, _), (_, ks, _)), rs => repsCost n gs.length ks.length rs.length + 7
  | .kernel, ((n, gs, _), w), _ => kerCost n gs.length w.1.length + 5
  | .lift, ((n, gs, _), (w, _)), _ => liftCost n gs.length w.1.length + 7⟩

/-- The verification context of the Schreier–Sims backend: every operation is allowed on
inputs satisfying its contract precondition. -/
def ssCtx : Ctx (groupSig Ty.unit) := ⟨ssOracle, ssB, GroupPre ssDV⟩

/-- The number of coset representatives is the index. -/
theorem length_cosetRepsModel {n : ℕ} {gs ks : GensData} (hgs : GensData.AllValid n gs)
    (hks : GensData.AllValid n ks) (hK : GensData.denote n ks ≤ GensData.denote n gs) :
    (cosetRepsModel n gs ks).length =
      Nat.card (GensData.denote n gs) / Nat.card (GensData.denote n ks) := by
  have h := (cosetRepsModel_spec hgs hks hK).2.card_eq hK
  exact (Nat.div_eq_of_eq_mul_left Nat.card_pos h).symm

section Implements

variable {a b : Ty} {body : a.denote → Prog Signature.empty (a, b) Ty.denote b}

/-- **The Schreier–Sims implementations compute the oracle within `ssB`.** -/
theorem ssImpl_implements :
    Implements ssOracle ssB (GroupPre ssDV) ssImpl Ctx.empty.O Ctx.empty.B := by
  intro op x hpre a b body
  suffices h : RunsWithin Ctx.empty body (ssImpl op (a, b) Ty.denote x) (ssOracle.run op x)
      (ssB.call op x (ssOracle.run op x)) by
    obtain ⟨tr, hr, hc, -⟩ := h
    exact ⟨tr, hr, hc⟩
  cases op with
  | generate =>
    obtain ⟨n, gs⟩ := x
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      exact RunsWithin.generateProg (n := n) hpre
    case hc =>
      simp only [Prim.cost, Prim.eval]
      exact le_of_eq (by simp only [ssB]; omega)
  | mem =>
    obtain ⟨⟨n, gs, _⟩, π⟩ := x
    obtain ⟨⟨hgs, -⟩, hπ⟩ := hpre
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      exact RunsWithin.memProg hgs hπ
    case hc =>
      simp only [Prim.cost]
      exact le_of_eq (by simp only [ssB]; omega)
  | orbits =>
    obtain ⟨⟨n, gs, _⟩, w⟩ := x
    obtain ⟨⟨hgs, -⟩, hw, -⟩ := hpre
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      exact RunsWithin.orbitsProg hgs hw
    case hc =>
      simp only [Prim.cost, Prim.eval]
      exact le_of_eq (by simp only [ssB]; omega)
  | stabilizer =>
    obtain ⟨⟨n, gs, _⟩, u⟩ := x
    obtain ⟨⟨hgs, -⟩, hu⟩ := hpre
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      exact RunsWithin.stabProg hgs hu
    case hc =>
      simp only [Prim.cost]
      exact le_of_eq (by simp only [ssB]; omega)
  | orbitTransversal =>
    obtain ⟨⟨n, gs, _⟩, u⟩ := x
    obtain ⟨⟨hgs, -⟩, hu⟩ := hpre
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      exact RunsWithin.orbitBFSProg hgs hu
    case hc =>
      simp only [Prim.cost]
      exact le_of_eq (by simp only [ssB]; omega)
  | cosetReps =>
    obtain ⟨⟨n, gs, _⟩, ⟨n', ks, _⟩⟩ := x
    obtain ⟨⟨hgs, -⟩, ⟨hks, -⟩, hn, hK⟩ := hpre
    change n' = n at hn
    subst hn
    have hlen := length_cosetRepsModel hgs hks hK
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      exact RunsWithin.cosetRepsProg (n := n') (gs := gs) (ks := ks) hgs hks hK
    case hc =>
      simp only [Prim.cost]
      show _ ≤ repsCost n' gs.length ks.length (cosetRepsModel n' gs ks).length + 7
      rw [hlen]
      omega
  | kernel =>
    obtain ⟨⟨n, gs, _⟩, w⟩ := x
    obtain ⟨⟨hgs, -⟩, hw, -⟩ := hpre
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      exact RunsWithin.kernelProg hgs hw
    case hc =>
      simp only [Prim.cost, Prim.eval]
      exact le_of_eq (by simp only [ssB]; omega)
  | lift =>
    obtain ⟨⟨n, gs, _⟩, w, π'⟩ := x
    obtain ⟨⟨hgs, -⟩, hw, -⟩ := hpre
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      exact RunsWithin.liftProg hgs hw π'
    case hc =>
      simp only [Prim.cost]
      exact le_of_eq (by simp only [ssB]; omega)

end Implements

/-! ### Bounds for the solver -/

section Mono

variable {n : ℕ}

theorem buildCost_mono {L L' : ℕ} (h : L ≤ L') : buildCost n L ≤ buildCost n L' := by
  unfold buildCost initCost
  gcongr

theorem genCost_mono {L L' : ℕ} (h : L ≤ L') : genCost n L ≤ genCost n L' := by
  unfold genCost
  gcongr
  exact buildCost_mono h

theorem stabCost_mono {L L' : ℕ} (h : L ≤ L') : stabCost n L ≤ stabCost n L' := by
  unfold stabCost
  gcongr
  exact buildCost_mono h

theorem transCost_mono {L L' : ℕ} (h : L ≤ L') : transCost n L ≤ transCost n L' := by
  unfold transCost
  gcongr

theorem orbitsCost_mono {L L' m m' : ℕ} (hL : L ≤ L') (hm : m ≤ m') :
    orbitsCost n L m ≤ orbitsCost n L' m' := by
  unfold orbitsCost
  gcongr
  exact transCost_mono hL

theorem kerCost_mono {L L' m m' : ℕ} (hL : L ≤ L') (hm : m ≤ m') :
    kerCost n L m ≤ kerCost n L' m' := by
  unfold kerCost
  gcongr
  exact buildCost_mono hL

theorem liftCost_mono {L L' m m' : ℕ} (hL : L ≤ L') (hm : m ≤ m') :
    liftCost n L m ≤ liftCost n L' m' := by
  unfold liftCost
  gcongr
  exact buildCost_mono hL

end Mono

/-- **The Schreier–Sims backend's bounds**, for subgroups of any ambient group `G₀`, with at
most `n²` generators. None depends on `|G₀|`. -/
def ssBounds (n : ℕ) (G₀ : Subgroup (Perm (Fin n))) : BackendBounds ssCtx ssDV n (n * n) G₀ where
  Borb := orbitsCost n (n * n) n + 5
  Bstab := stabCost n (n * n) + 5
  Btr := transCost n (n * n) + 5
  Bgen := genCost n (n * (n * n + 1)) + 2
  orbits gs _ w hs _ hpre := by
    obtain ⟨-, hw, -⟩ := hpre
    exact Nat.add_le_add_right (orbitsCost_mono hs (WinData.length_le hw)) 5
  stabilizer _ _ _ hs _ _ := Nat.add_le_add_right (stabCost_mono hs) 5
  transversal _ _ _ hs _ _ := Nat.add_le_add_right (transCost_mono hs) 5
  generate _ _ hl _ := Nat.add_le_add_right (genCost_mono hl) 2
  stabOut _ _ _ _ hpre := (stabModel_spec hpre.1.1 hpre.2).2.2
  genOut _ hgs _ := (generateModel_spec hgs).2.2

/-- The per-invocation unit of the solver with the Schreier–Sims backend: an explicit
polynomial in the degree `n` alone. -/
def simsQ (n : ℕ) : ℕ :=
  solveQ n (n * n) (orbitsCost n (n * n) n + 5) (stabCost n (n * n) + 5) (transCost n (n * n) + 5)
    (genCost n (n * (n * n + 1)) + 2)

/-- The cost bound of the public solver with the Schreier–Sims backend, for degree `n`, `L`
input generators, window size `m` and group order `N`. -/
def simsCost (n L m N : ℕ) : ℕ := 11 + (genCost n L + 2) + solveBound (simsQ n) m N

/-! ### Closed polynomial bounds -/

/-- `generate` from `L` generators costs `O(n⁶ + L n²)`. -/
theorem genCost_le (n L : ℕ) : genCost n L ≤ 100 * (n + 1) ^ 6 + 60 * L * (n + 1) ^ 2 := by
  simp only [genCost, buildCost, initCost, itemCost, slotCost, insCost, siftCost]
  ring_nf
  have := Nat.zero_le (n * L)
  have := Nat.zero_le (n ^ 2 * L)
  have := Nat.zero_le (n ^ 3)
  have := Nat.zero_le (n ^ 4)
  have := Nat.zero_le (n ^ 5)
  have := Nat.zero_le (n ^ 6)
  omega

/-- **The per-invocation unit is `O(n⁶)`.** -/
theorem simsQ_le (n : ℕ) : simsQ n ≤ 400 * (n + 1) ^ 6 := by
  simp only [simsQ, solveQ, nodeCost, edgeCost, orbitsCost, transCost, stabCost, genCost,
    buildCost, initCost, itemCost, slotCost, insCost, siftCost]
  ring_nf
  omega

theorem solveBound_le_mul {Q m N : ℕ} (hN : 0 < N) : solveBound Q m N ≤ 2 * (m + 1) * N * Q := by
  unfold solveBound
  split
  · have : Q ≤ 2 * (m + 1) * N * Q := Nat.le_mul_of_pos_left _ (by positivity)
    exact this
  · have : 2 * m * N * Q ≤ 2 * (m + 1) * N * Q := by gcongr; omega
    omega

/-- **The solver's cost bound in closed form**: polynomial in the degree `n` and the number of
input generators `L`, times the window size `m` and the group order `N`. -/
theorem simsCost_le (n L m : ℕ) {N : ℕ} (hN : 0 < N) :
    simsCost n L m N ≤
      13 + 100 * (n + 1) ^ 6 + 60 * L * (n + 1) ^ 2 + 800 * (m + 1) * N * (n + 1) ^ 6 := by
  have h₁ := genCost_le n L
  have h₂ : solveBound (simsQ n) m N ≤ 2 * (m + 1) * N * (400 * (n + 1) ^ 6) :=
    (solveBound_le_mul hN).trans (Nat.mul_le_mul_left _ (simsQ_le n))
  unfold simsCost
  have e : 2 * (m + 1) * N * (400 * (n + 1) ^ 6) = 800 * (m + 1) * N * (n + 1) ^ 6 := by ring
  omega

/-- The public solver with the Schreier–Sims backend substituted: a closed program over the
empty signature, inside the substituted solver procedure. -/
def simsSolver : WfProc Signature.empty (Ty.inst Ty.unit) (Ty.answer Ty.unit) :=
  WfProc.subst ⟨solveBody Ty.unit, solveBody_wf⟩ ⟨ssImpl, ssImpl_wf⟩

/-- **The solver with the Schreier–Sims backend: correctness, and a cost bound whose
per-invocation unit is polynomial in the degree, without an assumed group oracle.** -/
theorem solve_sims {n : ℕ} {xy : StrData × StrData} {w : WinData} {σd : PermData}
    {gs : GensData} (hw : w.Valid n) (hσ : σd.Valid n) (hgs : GensData.AllValid n gs)
    (hinv : IsInvariant (GensData.denote n gs) (w.denote n)) :
    ∃ (ans : AnswerData Ty.unit) (tr : Trace Signature.empty),
      Runs Ctx.empty.O (simsSolver.proc Ty.denote)
        ((solveEntry Ty.unit Ty.denote (xy, w, σd, n, gs)).subst ssImpl) ans tr ∧
      Trace.localCost tr ≤ simsCost n gs.length w.1.length (Nat.card (GensData.denote n gs)) ∧
      AnsOK ssDV n (w.denote n) (σd.denote n) (gs.denote n) (xy.1.denote n) (xy.2.denote n)
        ans := by
  obtain ⟨ans, tr, hr, hc, hok⟩ := solve_backend_refinement (X := ssCtx) (DV := ssDV)
    (I := ⟨ssImpl, ssImpl_wf⟩) (fun op x _ hx => ssOracle_meets op x hx) (fun _ _ _ hx => hx)
    ssImpl_implements (ssBounds n _) hw hσ hgs hinv
  refine ⟨ans, tr, hr, ?_, hok⟩
  rw [Trace.cost_empty] at hc
  exact hc

/-- **The checked solver with the Schreier–Sims backend, on every input.** -/
theorem solve_sims_checked (q n : ℕ) (xy : StrData × StrData) (w : WinData) (σd : PermData)
    (gs : GensData) :
    ∃ (r : Option (AnswerData Ty.unit)) (tr : Trace Signature.empty),
      Runs Ctx.empty.O (simsSolver.proc Ty.denote)
        ((solveChecked Ty.unit Ty.denote (q, xy, w, σd, n, gs)).subst ssImpl) r tr ∧
      Trace.localCost tr ≤ validCost n w.1.length gs.length + 4 +
        simsCost n gs.length w.1.length (Nat.card (GensData.denote n gs)) ∧
      (r = none ↔ ¬ InputValid q (xy, w, σd, n, gs)) ∧
      ∀ ans, r = some ans →
        AnsOK ssDV n (w.denote n) (σd.denote n) (gs.denote n) (xy.1.denote n) (xy.2.denote n)
          ans := by
  obtain ⟨r, ⟨tr, hr, hc, hpre⟩, hnone, hsome⟩ := solveChecked_spec (X := ssCtx) (DV := ssDV)
    (q := q) (fun op x _ hx => ssOracle_meets op x hx) (fun _ _ _ hx => hx)
    (ssBounds n (GensData.denote n gs))
  obtain ⟨tr', hr', hc'⟩ := Runs.subst ssImpl_implements hr hpre
  refine ⟨r, tr', hr', ?_, hnone, fun ans h => (hsome ans h).1⟩
  rw [Trace.cost_empty] at hc'
  refine hc'.trans (hc.trans ?_)
  split
  · exact le_rfl
  · exact Nat.add_le_add_left (Nat.zero_le _) _

end GraphIso.Sims
