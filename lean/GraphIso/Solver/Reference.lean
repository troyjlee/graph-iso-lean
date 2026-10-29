module

public import GraphIso.Solver.Checked
public import GraphIso.GroupOps.EnumerationProg
public import Mathlib.Tactic.GCongr

/-!
# The solver with the reference backend

`refImpl` implements the group operations by the programs of
`GraphIso/GroupOps/EnumerationProg.lean` (over the empty signature). `refImpl_implements`
proves that they compute the reference oracle within the schedule `refB`, on every input
satisfying the contract preconditions of the solver's operations; `refImpl_wf` proves them
well-formed, so they cannot call back into the solver.

`refBounds` instantiates the solver's backend bounds for subgroups of an ambient group of
order at most `N₀`, with every group given by all its elements (`s = N₀`).

`solve_reference`: the public solver with the reference implementations substituted is a
closed, well-formed program over the empty signature. On every valid input with group
`G = ⟨gs⟩` of order `N`, it returns a correct answer, and its run costs at most
`referenceCost n N |gs| |W|`: the initial enumeration of `G` plus
`solveBound Q |W| N`, with `Q` explicit in `n` and `N`. No group oracle is assumed. Strings are
read by total decoding (`StrData.denote n`), and their lengths are not checked.

`solve_reference_checked`: the validating entry `solveChecked` with the reference backend has
no hypotheses at all. On every input it returns `none` exactly when the input contract
`InputValid q` fails, and otherwise a correct answer, at cost at most the input check plus
`referenceCost n N |gs| |W|`.
-/

@[expose] public section

namespace GraphIso.Reference

open Equiv Pointwise Cost Programs Enum Solver

/-- The reference implementations of the group operations. `mem`, which no reduction uses,
returns a default value. -/
def refImpl : Impl (groupSig Ty.gens) Signature.empty := fun op _ _ x =>
  match op, x with
  | .generate, x =>
    .bind (.op1 .fst x) fun n => .bind (.op1 .snd x) fun gs =>
    .bind (closureProg n gs) fun el => .bind (.op2 .pair el el) fun ee => .op2 .pair n ee
  | .stabilizer, x =>
    .bind (.op1 .fst x) fun G => .bind (.op1 .snd x) fun u =>
    .bind (.op1 .fst G) fun n => .bind (.op1 .snd G) fun gd => .bind (.op1 .snd gd) fun el =>
    stabProg n el u
  | .orbitTransversal, x =>
    .bind (.op1 .fst x) fun G => .bind (.op1 .snd x) fun u =>
    .bind (.op1 .snd G) fun gd => .bind (.op1 .snd gd) fun el => transProg el u
  | .orbits, x =>
    .bind (.op1 .fst x) fun G => .bind (.op1 .snd x) fun w =>
    .bind (.op1 .snd G) fun gd => .bind (.op1 .snd gd) fun el => .bind (.op1 .fst w) fun pts =>
    orbitsProg el pts
  | .mem, _ => .op0 (.boolLit false)
  | .cosetReps, x =>
    .bind (.op1 .fst x) fun G => .bind (.op1 .snd x) fun K =>
    .bind (.op1 .snd G) fun gd => .bind (.op1 .snd gd) fun el =>
    .bind (.op1 .snd K) fun kd => .bind (.op1 .snd kd) fun kl => repsProg el kl
  | .kernel, x =>
    .bind (.op1 .fst x) fun G => .bind (.op1 .snd x) fun w =>
    .bind (.op1 .fst G) fun n => .bind (.op1 .snd G) fun gd => .bind (.op1 .snd gd) fun el =>
    .bind (.op1 .fst w) fun pts => kerProg n el pts
  | .lift, x =>
    .bind (.op1 .fst x) fun G => .bind (.op1 .snd x) fun wπ =>
    .bind (.op1 .fst wπ) fun w => .bind (.op1 .snd wπ) fun π' =>
    .bind (.op1 .fst G) fun n => .bind (.op1 .snd G) fun gd => .bind (.op1 .snd gd) fun el =>
    liftProg n el w π'

/-- The reference implementations are well-formed and make no recursive calls. -/
theorem refImpl_wf : refImpl.Wf := by
  intro op rec var₁ var₂ x₁ x₂
  cases op <;>
  · simp only [refImpl]
    prog_wf

/-- The reference cost schedule: the proved bound of each implementation on its actual
argument. -/
def refB : CostSchedule (groupSig Ty.gens) := ⟨fun op x y =>
  match op, x, y with
  | .generate, (n, gs), (_, el, _) => closureCost n el.length gs.length + 6
  | .stabilizer, ((_, _, el), _), _ => 7 * el.length + 10
  | .orbitTransversal, ((n, _, el), _), _ => el.length * (4 * n + 7) + 5
  | .orbits, ((n, _, el), w), _ => w.1.length * (el.length * (3 * n + 6) + 4 * n + 10) + 9
  | .kernel, ((_, _, el), w), _ => el.length * (5 * w.1.length + 5) + 11
  | .lift, ((n, _, el), (w, _)), _ =>
    el.length * (8 * w.1.length + 8) + 2 * w.1.length + 2 * n + 16
  | .cosetReps, ((n, _, el), (_, _, kl)), _ =>
    el.length * (el.length * (kl.length * (6 * n + 12) + 12 * n + 19) + 4) + 7
  | _, _, _ => 10⟩

/-- The operations the reference backend implements: all but `mem`. -/
def refOps (op : GroupOp) : Prop := solverOps op ∨ op = .kernel ∨ op = .lift ∨ op = .cosetReps

/-- The calls the reference context allows: the implemented operations, on contract inputs. -/
def refPre (op : GroupOp) (x : ((groupSig Ty.gens).arg op).denote) : Prop :=
  refOps op ∧ GroupPre refDV op x

/-- The reference oracle meets the contracts of all implemented operations. -/
theorem refOracle_meets_refOps : MeetsContractOn refDV refOps refOracle := by
  rintro op x (hop | hop) hpre
  · exact refOracle_meets op x hop hpre
  · exact refOracle_meets_kernel_lift op x hop hpre

/-- The verification context of the reference backend. -/
def refCtx : Ctx (groupSig Ty.gens) := ⟨refOracle, refB, refPre⟩

section Implements

variable {a b : Ty} {body : a.denote → Prog Signature.empty (a, b) Ty.denote b}

/-- **The reference implementations compute the reference oracle within `refB`.** -/
theorem refImpl_implements :
    Implements refOracle refB refPre refImpl Ctx.empty.O Ctx.empty.B := by
  rintro op x ⟨hop, hpre⟩ a b body
  rcases hop with (rfl | rfl | rfl | rfl) | rfl | rfl | rfl
  · -- orbits
    obtain ⟨⟨n, gs, el⟩, w⟩ := x
    obtain ⟨⟨_, hdv⟩, hw, hinv⟩ := hpre
    have h : RunsWithin Ctx.empty body (refImpl .orbits (a, b) Ty.denote ((n, gs, el), w))
        (refOracle.run .orbits ((n, gs, el), w))
        (w.1.length * (el.length * (3 * n + 6) + 4 * n + 10) + 9) := by
      apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        exact RunsWithin.orbitsProg hdv hw hinv
      case hc =>
        simp only [Prim.cost, Prim.eval]
        omega
    obtain ⟨tr, hr, hc, -⟩ := h
    exact ⟨tr, hr, hc⟩
  · -- stabilizer
    obtain ⟨⟨n, gs, el⟩, u⟩ := x
    have h : RunsWithin Ctx.empty body (refImpl .stabilizer (a, b) Ty.denote ((n, gs, el), u))
        (refOracle.run .stabilizer ((n, gs, el), u)) (7 * el.length + 10) := by
      apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        exact RunsWithin.stabProg _ _
      case hc =>
        simp only [Prim.cost, Prim.eval]
        omega
    obtain ⟨tr, hr, hc, -⟩ := h
    exact ⟨tr, hr, hc⟩
  · -- orbit transversal
    obtain ⟨⟨n, gs, el⟩, u⟩ := x
    obtain ⟨⟨_, hdv⟩, hu⟩ := hpre
    have h : RunsWithin Ctx.empty body
        (refImpl .orbitTransversal (a, b) Ty.denote ((n, gs, el), u))
        (refOracle.run .orbitTransversal ((n, gs, el), u)) (el.length * (4 * n + 7) + 5) := by
      apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        exact RunsWithin.transProg hdv.1 hu
      case hc =>
        simp only [Prim.cost]
        omega
    obtain ⟨tr, hr, hc, -⟩ := h
    exact ⟨tr, hr, hc⟩
  · -- generate
    obtain ⟨n, gs⟩ := x
    have hgs : GensData.AllValid n gs := hpre
    have hlen := (enumerate_spec hgs).2
    have h : RunsWithin Ctx.empty body (refImpl .generate (a, b) Ty.denote (n, gs))
        (refOracle.run .generate (n, gs))
        (closureCost n (enumerate n gs).length gs.length + 6) := by
      apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.closureProg (n := n) (gs := gs) hgs)
        run_step (RunsWithin.prim _ _)
        exact RunsWithin.prim _ _
      case hc =>
        simp only [Prim.cost]
        rw [hlen]
        omega
    obtain ⟨tr, hr, hc, -⟩ := h
    exact ⟨tr, hr, hc⟩
  · -- kernel
    obtain ⟨⟨n, gs, el⟩, w⟩ := x
    have h : RunsWithin Ctx.empty body (refImpl .kernel (a, b) Ty.denote ((n, gs, el), w))
        (refOracle.run .kernel ((n, gs, el), w)) (el.length * (5 * w.1.length + 5) + 11) := by
      apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        exact RunsWithin.kerProg _ _
      case hc =>
        simp only [Prim.cost, Prim.eval]
        omega
    obtain ⟨tr, hr, hc, -⟩ := h
    exact ⟨tr, hr, hc⟩
  · -- lift
    obtain ⟨⟨n, gs, el⟩, w, π'⟩ := x
    have h : RunsWithin Ctx.empty body (refImpl .lift (a, b) Ty.denote ((n, gs, el), w, π'))
        (refOracle.run .lift ((n, gs, el), w, π'))
        (el.length * (8 * w.1.length + 8) + 2 * w.1.length + 2 * n + 16) := by
      apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        exact RunsWithin.liftProg _ _ _
      case hc =>
        simp only [Prim.cost, Prim.eval]
        omega
    obtain ⟨tr, hr, hc, -⟩ := h
    exact ⟨tr, hr, hc⟩
  · -- coset representatives
    obtain ⟨⟨n, gs, el⟩, ⟨n', ks, kl⟩⟩ := x
    obtain ⟨⟨_, hdv⟩, ⟨_, hkl⟩, hn', -⟩ := hpre
    change n' = n at hn'
    subst n'
    have h : RunsWithin Ctx.empty body
        (refImpl .cosetReps (a, b) Ty.denote ((n, gs, el), (n, ks, kl)))
        (refOracle.run .cosetReps ((n, gs, el), (n, ks, kl)))
        (el.length * (el.length * (kl.length * (6 * n + 12) + 12 * n + 19) + 4) + 7) := by
      apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        exact RunsWithin.repsProg hdv hkl
      case hc =>
        simp only [Prim.cost, Prim.eval]
        omega
    obtain ⟨tr, hr, hc, -⟩ := h
    exact ⟨tr, hr, hc⟩

end Implements

/-! ### Bounds for subgroups of an ambient group -/

theorem closureCost_mono {n N N' L L' : ℕ} (hN : N ≤ N') (hL : L ≤ L') :
    closureCost n N L ≤ closureCost n N' L' := by
  unfold closureCost iterCost expCost insCost
  gcongr

/-- Backend data of a subgroup of `G₀` has at most `|G₀|` elements. -/
theorem length_data_le {n : ℕ} {G₀ : Subgroup (Perm (Fin n))} {gs : GensData}
    {el : List PermData} (hdv : refDV n gs el) (hle : GensData.denote n gs ≤ G₀) :
    el.length ≤ Nat.card G₀ :=
  (length_le_card hdv.1 hdv.2.1 fun e he => (hdv.2.2 _).2 ⟨e, he, rfl⟩).trans
    (Subgroup.card_le_of_le hle)

/-- The reference backend's bounds for subgroups of `G₀`, given `|G₀| ≤ N₀`; groups are given
by all their elements, so `s = N₀`. -/
def refBounds (n N₀ : ℕ) (G₀ : Subgroup (Perm (Fin n))) (hN₀ : Nat.card G₀ ≤ N₀) :
    BackendBounds refCtx refDV n N₀ G₀ where
  Borb := n * (N₀ * (3 * n + 6) + 4 * n + 10) + 9
  Bstab := 7 * N₀ + 10
  Btr := N₀ * (4 * n + 7) + 5
  Bgen := closureCost n N₀ (n * (N₀ + 1)) + 6
  orbits gs d w _ hle hpre := by
    obtain ⟨⟨_, hdv⟩, hw, _⟩ := hpre
    have hd := (length_data_le hdv hle).trans hN₀
    have hm := WinData.length_le hw
    show w.1.length * (d.length * (3 * n + 6) + 4 * n + 10) + 9 ≤ _
    gcongr
  stabilizer gs d u _ hle hpre := by
    obtain ⟨⟨_, hdv⟩, _⟩ := hpre
    have hd := (length_data_le hdv hle).trans hN₀
    show 7 * d.length + 10 ≤ _
    omega
  transversal gs d u _ hle hpre := by
    obtain ⟨⟨_, hdv⟩, _⟩ := hpre
    have hd := (length_data_le hdv hle).trans hN₀
    show d.length * (4 * n + 7) + 5 ≤ _
    gcongr
  generate gs hgs hl hle := by
    have hlen := (enumerate_spec hgs).2
    show closureCost n (enumerate n gs).length gs.length + 6 ≤ _
    rw [hlen]
    gcongr
    · exact closureCost_mono ((Subgroup.card_le_of_le hle).trans hN₀) hl
  stabOut gs d u hle hpre := by
    obtain ⟨⟨_, hdv⟩, _⟩ := hpre
    show (stabElems d u).length ≤ N₀
    exact (List.length_filter_le _ _).trans ((length_data_le hdv hle).trans hN₀)
  genOut gs hgs hle := by
    show (enumerate n gs).length ≤ N₀
    rw [(enumerate_spec hgs).2]
    exact (Subgroup.card_le_of_le hle).trans hN₀

/-! ### The concrete solver -/

/-- The cost bound of the public solver with the reference backend, for degree `n`, group
order `N`, `L` input generators and window size `m`. -/
def referenceCost (n N L m : ℕ) : ℕ :=
  11 + (closureCost n N L + 6) +
    solveBound (solveQ n N (n * (N * (3 * n + 6) + 4 * n + 10) + 9) (7 * N + 10)
      (N * (4 * n + 7) + 5) (closureCost n N (n * (N + 1)) + 6)) m N

/-- The public solver with the reference backend substituted: a closed program over the empty
signature, inside the substituted solver procedure. -/
def referenceSolver : WfProc Signature.empty (Ty.inst Ty.gens) (Ty.answer Ty.gens) :=
  WfProc.subst ⟨solveBody Ty.gens, solveBody_wf⟩ ⟨refImpl, refImpl_wf⟩

/-- **The solver with the reference backend: correctness and a finite cost bound, without an
assumed group oracle.** -/
theorem solve_reference {n : ℕ} {xy : StrData × StrData} {w : WinData} {σd : PermData}
    {gs : GensData} (hw : w.Valid n) (hσ : σd.Valid n) (hgs : GensData.AllValid n gs)
    (hinv : IsInvariant (GensData.denote n gs) (w.denote n)) :
    ∃ (ans : AnswerData Ty.gens) (tr : Trace Signature.empty),
      Runs Ctx.empty.O (referenceSolver.proc Ty.denote)
        ((solveEntry Ty.gens Ty.denote (xy, w, σd, n, gs)).subst refImpl) ans tr ∧
      Trace.localCost tr ≤
        referenceCost n (Nat.card (GensData.denote n gs)) gs.length w.1.length ∧
      AnsOK refDV n (w.denote n) (σd.denote n) (gs.denote n) (xy.1.denote n) (xy.2.denote n)
        ans := by
  obtain ⟨ans, tr, hr, hc, hok⟩ := solve_backend_refinement (X := refCtx)
    (I := ⟨refImpl, refImpl_wf⟩) refOracle_meets (fun op x hop hx => ⟨Or.inl hop, hx⟩)
    refImpl_implements (refBounds n _ _ le_rfl) hw hσ hgs hinv
  refine ⟨ans, tr, hr, ?_, hok⟩
  rw [Trace.cost_empty] at hc
  refine hc.trans ?_
  have hlen := (enumerate_spec hgs).2
  show 11 + (closureCost n (enumerate n gs).length gs.length + 6) + _ ≤ _
  rw [hlen]
  rfl

/-- **The checked solver with the reference backend, on every input.** -/
theorem solve_reference_checked (q n : ℕ) (xy : StrData × StrData) (w : WinData)
    (σd : PermData) (gs : GensData) :
    ∃ (r : Option (AnswerData Ty.gens)) (tr : Trace Signature.empty),
      Runs Ctx.empty.O (referenceSolver.proc Ty.denote)
        ((solveChecked Ty.gens Ty.denote (q, xy, w, σd, n, gs)).subst refImpl) r tr ∧
      Trace.localCost tr ≤ validCost n w.1.length gs.length + 4 +
        referenceCost n (Nat.card (GensData.denote n gs)) gs.length w.1.length ∧
      (r = none ↔ ¬ InputValid q (xy, w, σd, n, gs)) ∧
      ∀ ans, r = some ans →
        AnsOK refDV n (w.denote n) (σd.denote n) (gs.denote n) (xy.1.denote n) (xy.2.denote n)
          ans := by
  obtain ⟨r, ⟨tr, hr, hc, hpre⟩, hnone, hsome⟩ := solveChecked_spec (X := refCtx) (q := q)
    refOracle_meets (fun op x hop hx => ⟨Or.inl hop, hx⟩)
    (refBounds n _ (GensData.denote n gs) le_rfl)
  obtain ⟨tr', hr', hc'⟩ := Runs.subst refImpl_implements hr hpre
  refine ⟨r, tr', hr', ?_, hnone, fun ans h => (hsome ans h).1⟩
  rw [Trace.cost_empty] at hc'
  refine hc'.trans (hc.trans ?_)
  cases hb : inputValidB q (xy, w, σd, n, gs) with
  | false => simp
  | true =>
    have hlen := (enumerate_spec (inputValidB_iff.1 hb).2.2.2.2.1).2
    simp only [↓reduceIte]
    show _ + (11 + (closureCost n (enumerate n gs).length gs.length + 6) + _) ≤ _
    rw [hlen]
    rfl

end GraphIso.Reference
