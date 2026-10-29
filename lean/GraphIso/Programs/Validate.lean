module

public import GraphIso.Programs.List
public import GraphIso.GroupOps.Interface
public import Mathlib.Tactic.Linarith

/-!
# Validation programs

Programs computing the validity checks of the represented input, for degree `n`, with their
charged costs:

* `strValidProg n q x`: `StrData.validB n q x` (length `n`, symbols below `q`), cost
  `5 n + 5`;
* `permValidProg n σ`: `PermData.validB n σ`, cost `14 n + 10`;
* `gensValidProg n gs`: `GensData.allValidB n gs`, cost `s (14 n + 12) + 1` for `s`
  generators;
* `winValidProg n w`: `WinData.validB n w` for a window listing `m` points, cost
  `(m + 1) (3 m + 9) + n (3 m + 10) + 4 m + 15`. Repetitions are found by comparing each point
  with the later ones, and the mask is compared with membership in the list by scanning;
* `invariantProg gs w`: `GensData.invariantB gs w`, cost `s (4 m + 4) + 3`.

The costs depend on `n` and on list lengths only, never on array sizes, so they also hold for
invalid data.
-/

@[expose] public section

namespace GraphIso.Programs

open Cost

variable {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- Is `x` of length `n` with symbols below `q`? -/
def strValidProg (n q : var .nat) (x : var Ty.str) : Prog S rec var .bool :=
  .bind (.op1 .arraySize x) fun sz => .bind (.op2 .natEq sz n) fun e =>
  .bind (.op1 .range n) fun is =>
  .bind (allList is fun i => .bind (.op2 .arrayGet x i) fun xi => .op2 .natLt xi q) fun ok =>
  .op2 .and e ok

/-- Is `σ` valid permutation data of degree `n`? -/
def permValidProg (n : var .nat) (σ : var Ty.perm) : Prog S rec var .bool :=
  .bind (.op1 .fst σ) fun f => .bind (.op1 .snd σ) fun g =>
  .bind (.op1 .arraySize f) fun sf => .bind (.op2 .natEq sf n) fun ef =>
  .bind (.op1 .arraySize g) fun sg => .bind (.op2 .natEq sg n) fun eg =>
  .bind (.op1 .range n) fun is =>
  .bind (allList is fun i =>
    .bind (.op2 .arrayGet f i) fun fi => .bind (.op2 .arrayGet g i) fun gi =>
    .bind (.op2 .natLt fi n) fun a₁ => .bind (.op2 .natLt gi n) fun a₂ =>
    .bind (.op2 .arrayGet g fi) fun gfi => .bind (.op2 .natEq gfi i) fun a₃ =>
    .bind (.op2 .arrayGet f gi) fun fgi => .bind (.op2 .natEq fgi i) fun a₄ =>
    .bind (.op2 .and a₁ a₂) fun b₁ => .bind (.op2 .and b₁ a₃) fun b₂ => .op2 .and b₂ a₄) fun ok =>
  .bind (.op2 .and ef eg) fun e => .op2 .and e ok

/-- Are all generators valid permutation data of degree `n`? -/
def gensValidProg (n : var .nat) (gs : var Ty.gens) : Prog S rec var .bool :=
  allList gs fun g => permValidProg n g

/-- One step of the repetition check: compare the head of the remaining list with its tail. -/
def nodupStep (st : var (.prod (.list .nat) .bool)) :
    Prog S rec var (.option (.prod (.list .nat) .bool)) :=
  .bind (.op1 .fst st) fun l => .bind (.op1 .snd st) fun ok =>
  .caseList l (.op0 .none) fun x xs =>
    .bind (anyList xs fun y => .op2 .natEq x y) fun dup =>
    .bind (.op1 .not dup) fun fresh => .bind (.op2 .and ok fresh) fun ok' =>
    .bind (.op2 .pair xs ok') fun st' => .op1 .some st'

/-- Are the listed points pairwise distinct? -/
def nodupProg (pts : var (.list .nat)) : Prog S rec var .bool :=
  .bind (.op0 (.boolLit true)) fun t => .bind (.op2 .pair pts t) fun st₀ =>
  .bind (.loop st₀ fun st => nodupStep st) fun fin => .op1 .snd fin

/-- Is `w` valid window data of degree `n`? -/
def winValidProg (n : var .nat) (w : var Ty.win) : Prog S rec var .bool :=
  .bind (.op1 .fst w) fun pts => .bind (.op1 .snd w) fun mask =>
  .bind (.op1 .arraySize mask) fun sz => .bind (.op2 .natEq sz n) fun e =>
  .bind (nodupProg pts) fun nd =>
  .bind (allList pts fun i => .op2 .natLt i n) fun lt =>
  .bind (.op1 .range n) fun is =>
  .bind (allList is fun i =>
    .bind (.op2 .arrayGet mask i) fun b =>
    .bind (anyList pts fun p => .op2 .natEq i p) fun mem =>
    .bind (.op2 .and b mem) fun both =>
    .bind (.op1 .not b) fun nb => .bind (.op1 .not mem) fun nm =>
    .bind (.op2 .and nb nm) fun neither => .op2 .or both neither) fun agree =>
  .bind (.op2 .and e nd) fun r₁ => .bind (.op2 .and r₁ lt) fun r₂ => .op2 .and r₂ agree

/-- Does every generator map every listed window point into the window? -/
def invariantProg (gs : var Ty.gens) (w : var Ty.win) : Prog S rec var .bool :=
  .bind (.op1 .fst w) fun pts => .bind (.op1 .snd w) fun mask =>
  allList gs fun g => .bind (.op1 .fst g) fun f =>
    allList pts fun u => .bind (.op2 .arrayGet f u) fun v => .op2 .arrayGet mask v

/-! ### Values -/

/-- Duplicate-freeness as computed by the repetition check. -/
theorem nodup_iff_steps : ∀ (l : List ℕ) (ok : Bool),
    (ok && decide l.Nodup) =
      match l with
      | [] => ok
      | x :: xs => (ok && !xs.any fun y => x == y) && decide xs.Nodup
  | [], ok => by simp
  | x :: xs, ok => by
    have h : (!xs.any fun y => x == y) = decide (x ∉ xs) := by
      rw [Bool.eq_iff_iff]
      simp only [Bool.not_eq_true', List.any_eq_false, beq_iff_eq, decide_eq_true_eq]
      exact ⟨fun h hx => h x hx rfl, fun h y hy e => h (e ▸ hy)⟩
    simp only [List.nodup_cons, Bool.decide_and, h, Bool.and_assoc]

/-- The window check as the program computes it. -/
theorem winValid_eq (n : ℕ) (w : WinData) :
    ((((w.2.size == n) && decide w.1.Nodup) && w.1.all (fun i => decide (i < n))) &&
        (List.range n).all (fun i =>
          (w.2.getD i false && w.1.any fun p => i == p) ||
            (!w.2.getD i false && !w.1.any fun p => i == p))) =
      WinData.validB n w := by
  unfold WinData.validB getB
  congr 1
  apply List.all_congr rfl
  intro i
  have : (w.1.any fun p => i == p) = decide (i ∈ w.1) := by
    rw [Bool.eq_iff_iff]
    simp [List.any_eq_true]
  rw [this]
  cases w.2.getD i false <;> cases decide (i ∈ w.1) <;> rfl

/-! ### Costs -/

section Specs

variable {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

theorem RunsWithin.strValidProg (n q : ℕ) (x : StrData) :
    RunsWithin X body (Programs.strValidProg n q x) (StrData.validB n q x) (5 * n + 5) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.allList_le (c := 2) fun i _ =>
      RunsWithin.bind_le (RunsWithin.prim _ _) (RunsWithin.prim _ _) (by simp [Prim.cost]))
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head, List.length_range]
    omega

theorem RunsWithin.permValidProg (n : ℕ) (σ : PermData) :
    RunsWithin X body (Programs.permValidProg n σ) (PermData.validB n σ) (14 * n + 10) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.allList_le (c := 11) fun i _ => by
      apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        exact RunsWithin.prim _ _
      case hc => simp [Prim.cost])
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head, List.length_range]
    omega

theorem RunsWithin.gensValidProg (n : ℕ) (gs : GensData) :
    RunsWithin X body (Programs.gensValidProg n gs) (GensData.allValidB n gs)
      (gs.length * (14 * n + 12) + 1) :=
  RunsWithin.allList_le fun g _ => RunsWithin.permValidProg n g

private theorem RunsWithin.nodupLoop (m : ℕ) : ∀ (l : List ℕ) (ok : Bool), l.length ≤ m →
    RunsWithin X body (.loop (l, ok) fun st => Programs.nodupStep st) ([], ok && decide l.Nodup)
      ((l.length + 1) * (3 * m + 9))
  | [], ok, _ => by
    rw [show (ok && decide ([] : List ℕ).Nodup) = ok by simp]
    refine (RunsWithin.loop_none (c := 4) ?_).mono (by simp only [List.length_nil]; omega)
    refine RunsWithin.bind_le (c₂ := 3) (RunsWithin.prim _ _) ?_ (by simp [Prim.cost])
    refine RunsWithin.bind_le (c₂ := 2) (RunsWithin.prim _ _) ?_ (by simp [Prim.cost])
    exact RunsWithin.caseList_nil (RunsWithin.prim _ _)
  | x :: xs, ok, hl => by
    simp only [List.length_cons] at hl
    have ih := RunsWithin.nodupLoop m xs (ok && !xs.any fun y => x == y) (by omega)
    have hstep : RunsWithin X body (Programs.nodupStep (x :: xs, ok))
        (some (xs, ok && !xs.any fun y => x == y)) (3 * xs.length + 8) := by
      refine RunsWithin.bind_le (c₂ := 3 * xs.length + 7) (RunsWithin.prim _ _) ?_
        (by simp [Prim.cost]; omega)
      refine RunsWithin.bind_le (c₂ := 3 * xs.length + 6) (RunsWithin.prim _ _) ?_
        (by simp [Prim.cost]; omega)
      simp only [Prim.eval]
      refine (RunsWithin.caseList_cons (k := 3 * xs.length + 5) ?_).mono (by omega)
      apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.anyList_le (c := 1) fun y _ => RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        exact RunsWithin.prim _ _
      case hc =>
        simp only [Prim.cost]
        omega
    rw [nodup_iff_steps]
    refine (RunsWithin.loop_some hstep ih).mono ?_
    simp only [List.length_cons, Nat.add_one_mul]
    omega

theorem RunsWithin.nodupProg (pts : List ℕ) :
    RunsWithin X body (Programs.nodupProg pts) (decide pts.Nodup)
      ((pts.length + 1) * (3 * pts.length + 9) + 3) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.nodupLoop pts.length pts _ le_rfl)
    exact RunsWithin.prim_le (by simp [Prim.eval]) le_rfl
  case hc =>
    simp only [Prim.cost]
    omega

theorem RunsWithin.winValidProg (n : ℕ) (w : WinData) :
    RunsWithin X body (Programs.winValidProg n w) (WinData.validB n w)
      ((w.1.length + 1) * (3 * w.1.length + 9) + n * (3 * w.1.length + 10) +
        4 * w.1.length + 15) := by
  rw [← winValid_eq]
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.nodupProg _)
    run_step (RunsWithin.allList_le (c := 1) fun i _ => RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.allList_le (c := 3 * w.1.length + 7) fun i _ => by
      apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.anyList_le (c := 1) fun p _ => RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        exact RunsWithin.prim _ _
      case hc =>
        simp only [Prim.cost, Prim.eval]
        omega)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head, List.length_range]
    nlinarith

theorem RunsWithin.invariantProg (gs : GensData) (w : WinData) :
    RunsWithin X body (Programs.invariantProg gs w) (GensData.invariantB gs w)
      (gs.length * (4 * w.1.length + 4) + 3) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.allList_le (c := 4 * w.1.length + 2) fun g _ =>
      RunsWithin.bind_le (c₂ := 4 * w.1.length + 1) (RunsWithin.prim _ _)
        ((RunsWithin.allList_le (c := 2) fun u _ =>
          RunsWithin.bind_le (RunsWithin.prim _ _) (RunsWithin.prim _ _)
            (by simp [Prim.cost])).mono (by simp only [Prim.eval]; omega))
        (by simp only [Prim.cost]; omega)
  case hc =>
    simp only [Prim.cost, Nat.add_assoc, Nat.reduceAdd]
    omega

end Specs

/-! ### Well-formedness -/

section Wf

variable {var₁ var₂ : Ty → Type} {r : Bool} {Γ : WfCtx var₁ var₂}

theorem wf_strValidProg {n₁ q₁ : var₁ .nat} {n₂ q₂ : var₂ .nat} {x₁ : var₁ Ty.str}
    {x₂ : var₂ Ty.str} (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (hq : ⟨.nat, q₁, q₂⟩ ∈ Γ)
    (hx : ⟨Ty.str, x₁, x₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (strValidProg n₁ q₁ x₁) (strValidProg n₂ q₂ x₂) := by
  unfold strValidProg allList
  prog_wf

theorem wf_permValidProg {n₁ : var₁ .nat} {n₂ : var₂ .nat} {σ₁ : var₁ Ty.perm}
    {σ₂ : var₂ Ty.perm} (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (hσ : ⟨Ty.perm, σ₁, σ₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (permValidProg n₁ σ₁) (permValidProg n₂ σ₂) := by
  unfold permValidProg allList
  prog_wf

theorem wf_gensValidProg {n₁ : var₁ .nat} {n₂ : var₂ .nat} {g₁ : var₁ Ty.gens}
    {g₂ : var₂ Ty.gens} (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (hg : ⟨Ty.gens, g₁, g₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (gensValidProg n₁ g₁) (gensValidProg n₂ g₂) := by
  unfold gensValidProg permValidProg allList
  prog_wf

theorem wf_winValidProg {n₁ : var₁ .nat} {n₂ : var₂ .nat} {w₁ : var₁ Ty.win}
    {w₂ : var₂ Ty.win} (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (hw : ⟨Ty.win, w₁, w₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (winValidProg n₁ w₁) (winValidProg n₂ w₂) := by
  unfold winValidProg nodupProg nodupStep allList anyList
  prog_wf

theorem wf_invariantProg {g₁ : var₁ Ty.gens} {g₂ : var₂ Ty.gens} {w₁ : var₁ Ty.win}
    {w₂ : var₂ Ty.win} (hg : ⟨Ty.gens, g₁, g₂⟩ ∈ Γ) (hw : ⟨Ty.win, w₁, w₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (invariantProg g₁ w₁) (invariantProg g₂ w₂) := by
  unfold invariantProg allList
  prog_wf

end Wf

end GraphIso.Programs
