module

public import GraphIso.Main.Mini
public import GraphIso.Main.SimsM5
public import GraphIso.Main.M5CJWf
public import GraphIso.Cost.Local

/-!
# The full procedure: programs

Stage 14j-5d, items 1 and 2 (`PLAN-14.md` §14.9). The dispatcher of the main recursion as a
program of the cost language, with `.recur` as every step's sub-solver.

* `ThrProg`, `ThrWf`, `ThrSpec`: a threshold program computes `(k, ℓ)` from `n₀`; the theorems
  hold for every one that is well formed, local (no backend call and no recursive call,
  `Prog.Local`, so its runs have no backend event: `ThrSpec.calls`) and returns
  `(kf n₀, ℓf n₀)` within `cT n₀`. `thrConst k ℓ` returns two literals.
* `normLabProg`: the labels at the string positions `0, …, n − 1`, as an array of size `n`.
  Only window points (below `n`) are read, so the hint is unchanged; the work of M2a, M2b and M4
  depends on the size of the label array, which the children's predicates do not bound.
* `noStProg`: the structure state with tag `0` (no structure), for M5.
* `m5OkD`, `m4OkD` and their programs: M5's numeric conditions (`5 ≤ k`, `2k ≤ m`, `12 ≤ m`;
  they imply `k + 2 ≤ m`), and M4's (`4 + j ≤ m`, `2j ≤ m` with `j = dg − 1`).
* `bigProg`: the large-base branch. M3 on a base of at most `ℓ` points; otherwise the degree of
  transitivity `dg` of the base action, capped at `m − 2`, which is the giant test of
  `giantProg` (`dg = m − 2`): a giant with M5's conditions gives M5, a non-giant with M4's gives
  M4, and every other case M3.
* `hintProg`: with a hint, the base orbits (more than one gives M1), then the maximal blocks of
  the base: proper blocks give M2a when some window label is not equidistributed over them,
  M2b otherwise; no proper blocks give `bigProg`.
* `mainBody thr`: the base case; without a hint, the chain rule on at least two orbits, else
  M0; with a hint, `hintProg`. `mainEntry` is the mini procedure's entry.
-/

@[expose] public section

namespace GraphIso.Main

open Equiv Cost GraphIso GraphIso.Programs GraphIso.Toolkit GraphIso.Recursion Sims

/-! ### Thresholds -/

section Thresholds

/-- **Threshold programs**: from the original size `n₀`, the pair `(k, ℓ)`. -/
abbrev ThrProg (D : Ty) : Type 1 :=
  (var : Ty → Type) → var .nat → Prog (groupSig D) (hinstTy D, Ty.answer D) var (.prod .nat .nat)

/-- A threshold program is well formed in every context holding its argument. -/
def ThrWf {D : Ty} (thr : ThrProg D) : Prop :=
  ∀ (var₁ var₂ : Ty → Type) (r : Bool) (Γ : WfCtx var₁ var₂) (x₁ : var₁ .nat) (x₂ : var₂ .nat),
    ⟨.nat, x₁, x₂⟩ ∈ Γ → Prog.Wf r Γ (thr var₁ x₁) (thr var₂ x₂)

/-- **The threshold contract**: well formed; local in every variable type (no backend call and
no recursive call); and on every `n₀` (whatever the body) it returns `(kf n₀, ℓf n₀)` at a cost
of at most `cT n₀`. -/
structure ThrSpec (thr : ThrProg Ty.unit) (kf ℓf cT : ℕ → ℕ) : Prop where
  wf : ThrWf thr
  loc : ∀ (var : Ty → Type) (x : var .nat), (thr var x).Local
  run : ∀ (body : HInstData Ty.unit →
      Prog (groupSig Ty.unit) (hinstTy Ty.unit, Ty.answer Ty.unit) Ty.denote (Ty.answer Ty.unit))
    (n₀ : ℕ), RunsWithin ssCtx body (thr Ty.denote n₀) (kf n₀, ℓf n₀) (cT n₀)

/-- **A threshold program performs no backend operation**: under any oracle and any body, every
run of it has no backend event. -/
theorem ThrSpec.calls {thr : ThrProg Ty.unit} {kf ℓf cT : ℕ → ℕ} (h : ThrSpec thr kf ℓf cT)
    {O : Oracle (groupSig Ty.unit)}
    {body : HInstData Ty.unit →
      Prog (groupSig Ty.unit) (hinstTy Ty.unit, Ty.answer Ty.unit) Ty.denote (Ty.answer Ty.unit)}
    {n₀ : ℕ} {v : ℕ × ℕ} {tr : Trace (groupSig Ty.unit)}
    (hr : Runs O body (thr Ty.denote n₀) v tr) : Trace.calls tr = [] :=
  (h.loc Ty.denote n₀).runs_calls hr

/-- **Constant thresholds**: two literals. -/
def thrConst {D : Ty} (k ℓ : ℕ) : ThrProg D := fun _ _ =>
  .bind (.op0 (.natLit k)) fun a => .bind (.op0 (.natLit ℓ)) fun b => .op2 .pair a b

theorem thrConst_spec (k ℓ : ℕ) :
    ThrSpec (thrConst k ℓ) (fun _ => k) (fun _ => ℓ) (fun _ => 3) := by
  refine ⟨fun _ _ _ _ _ _ _ => by unfold thrConst; prog_wf,
    fun _ _ => .bind (.prim _ _) fun _ => .bind (.prim _ _) fun _ => .prim _ _, fun body n₀ => ?_⟩
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim _ _
  case hc => simp [Prim.cost]

end Thresholds

/-! ### Programs -/

section Programs

variable {D : Ty} {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- The labels at the string positions `0, …, n − 1`, as an array of size `n`. -/
def normLabProg (n : var .nat) (L : var (.array (.list .nat))) :
    Prog S rec var (.array (.list .nat)) :=
  .bind (.op1 .range n) fun is =>
  .bind (mapList is fun i => .op2 .arrayGet L i) fun ls => .op1 .arrayOfList ls

/-- The structure state with tag `0`: the default value, read from an empty array. -/
def noStProg : Prog S rec var stTy :=
  .bind (.op0 .nil) fun e => .bind (.op1 .arrayOfList e) fun a =>
  .bind (.op0 (.natLit 0)) fun z => .op2 .arrayGet a z

/-- M5's numeric conditions as a program: `5 ≤ k`, `2k ≤ m` and `12 ≤ m`. -/
def m5OkProg (k m : var .nat) : Prog S rec var .bool :=
  .bind (.op0 (.natLit 4)) fun c4 => .bind (.op2 .natLt c4 k) fun t1 =>
  .bind (.op2 .add k k) fun kk => .bind (.op2 .natLt m kk) fun f2 => .bind (.op1 .not f2) fun t2 =>
  .bind (.op0 (.natLit 11)) fun c11 => .bind (.op2 .natLt c11 m) fun t3 =>
  .bind (.op2 .and t1 t2) fun a => .op2 .and a t3

/-- M4's numeric conditions as a program: `4 + j ≤ m` and `2j ≤ m`, with `j = dg − 1`. -/
def m4OkProg (dg m : var .nat) : Prog S rec var .bool :=
  .bind (.op0 (.natLit 1)) fun c1 => .bind (.op2 .sub dg c1) fun j =>
  .bind (.op0 (.natLit 4)) fun c4 => .bind (.op2 .add c4 j) fun j4 =>
  .bind (.op2 .natLt m j4) fun f1 => .bind (.op1 .not f1) fun t1 =>
  .bind (.op2 .add j j) fun jj => .bind (.op2 .natLt m jj) fun f2 => .bind (.op1 .not f2) fun t2 =>
  .op2 .and t1 t2

/-- **The large-base branch**: M3 on a base of at most `ℓ` points; otherwise the giant test
through the degree of transitivity `dg` (capped at `m − 2`), then M5 or M4 when their numeric
conditions hold, M3 otherwise. -/
def bigProg (thr : ThrProg D) (sub : var (hinstTy D) → Prog (groupSig D) (hinstTy D, Ty.answer D)
      var (Ty.answer D))
    (I : var (hinstTy D)) (L : var (.array (.list .nat))) (n₀ n m : var .nat)
    (G : var (Ty.group D)) : Prog (groupSig D) (hinstTy D, Ty.answer D) var (Ty.answer D) :=
  .bind (thr var n₀) fun kl => .bind (.op1 .fst kl) fun k => .bind (.op1 .snd kl) fun ℓ =>
  .bind (.op2 .natLt ℓ m) fun big =>
  .ite big
    (.bind (.op0 (.natLit 2)) fun two => .bind (.op2 .sub m two) fun cap =>
     .bind (degreeProg n cap G) fun dg => .bind (.op2 .natEq dg cap) fun gi =>
     .ite gi
       (.bind (m5OkProg k m) fun ok =>
        .ite ok (.bind noStProg fun st => m5StepCJProg sub I L k st) (m3Prog sub I))
       (.bind (m4OkProg dg m) fun ok => .ite ok (m4StepProg sub I) (m3Prog sub I)))
    (m3Prog sub I)

/-- **The hinted dispatch.** The labels are normalized to the `n` string positions; then the
base orbits (M1 on more than one), the maximal blocks of the base (M2a or M2b when they are
proper), and the large-base branch. -/
def hintProg (thr : ThrProg D) (sub : var (hinstTy D) → Prog (groupSig D) (hinstTy D, Ty.answer D)
      var (Ty.answer D))
    (I : var (hinstTy D)) (L : var (.array (.list .nat))) :
    Prog (groupSig D) (hinstTy D, Ty.answer D) var (Ty.answer D) :=
  .bind (.op1 .fst I) fun J => .bind (.op1 .snd I) fun r₁ =>
  .bind (.op1 .fst r₁) fun n₀ => .bind (.op1 .snd r₁) fun r₂ => .bind (.op1 .fst r₂) fun n =>
  .bind (.op1 .snd J) fun wc => .bind (.op1 .fst wc) fun w => .bind (.op1 .snd wc) fun c =>
  .bind (.op1 .snd c) fun G => .bind (.op1 .fst G) fun N => .bind (.op2 .sub N n) fun m =>
  .bind (normLabProg n L) fun L' => .bind (.op1 .some L') fun sL =>
  .bind (.op2 .pair n sL) fun q₁ => .bind (.op2 .pair n₀ q₁) fun q₂ =>
  .bind (.op2 .pair J q₂) fun I' =>
  .bind (baseWinProg n N) fun bw => .bind (.op2 .pair G bw) fun gb =>
  .bind (Prog.call (S := groupSig D) GroupOp.orbits gb) fun os => .bind (.op1 .length os) fun no =>
  .bind (.op0 (.natLit 1)) fun one => .bind (.op2 .natLt one no) fun split =>
  .ite split (m1StepProg sub I' L')
    (.bind (baseBlocksProg n G) fun bs => .bind (blkOKProg m bs) fun ok =>
     .ite ok
       (.bind (.op1 .fst w) fun pts => .bind (neqProg n N bs L' pts) fun ne =>
        .ite ne (m2aStepProg sub I' L' bs) (m2bStepProg sub I' bs))
       (bigProg thr sub I' L' n₀ n m G))

/-- **The full procedure.** The base case when the group fixes the window; without a hint, the
chain rule when the window has at least two orbits, else M0; with a hint, `hintProg`. Every
step's sub-solver is the recursive call. -/
def mainBody (thr : ThrProg D) : Proc (groupSig D) (hinstTy D) (Ty.answer D) := fun var I =>
  .bind (fixedTestProg I) fun f =>
  .ite f (fixedStepProg I)
    (.bind (.op1 .snd I) fun r₁ => .bind (.op1 .snd r₁) fun r₂ =>
     .bind (.op1 .snd r₂) fun lab =>
     .caseOption lab
      (.bind (winOrbitsProg I) fun os => .bind (.op1 .length os) fun k =>
       .bind (.op0 (.natLit 1)) fun one => .bind (.op2 .natLt one k) fun many =>
       .ite many (chainProg (fun J => .recur J) I os) (m0StepProg (fun J => .recur J) I))
      (fun L => hintProg (var := var) thr (fun J => .recur J) I L))

/-- **The entry**: the mini procedure's (`miniEntry`), one `generate` and then the recursion on
the instance without a hint, with `n₀ = n = N`. It does not depend on the body. -/
abbrev mainEntry (D : Ty) := miniEntry D

end Programs

/-! ### Well-formedness -/

section Wf

variable {D : Ty}

theorem wf_normLabProg {S : Signature} {rec : Ty × Ty} {var₁ var₂ : Ty → Type} {r : Bool}
    {Γ : WfCtx var₁ var₂} {n₁ : var₁ .nat} {n₂ : var₂ .nat} {L₁ : var₁ (.array (.list .nat))}
    {L₂ : var₂ (.array (.list .nat))} (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ)
    (hL : ⟨.array (.list .nat), L₁, L₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (normLabProg n₁ L₁) (normLabProg n₂ L₂) := by
  unfold normLabProg
  refine .bind (.prim _ (.cons hn .nil)) fun _ _ => ?_
  refine .bind (wf_mapList (List.Mem.head _) fun Γ' hΓ x₁ x₂ hx =>
    .prim _ (.cons (hΓ (List.mem_cons_of_mem _ hL)) (.cons hx .nil))) fun _ _ => ?_
  exact .prim _ (.cons (List.Mem.head _) .nil)

theorem wf_noStProg {S : Signature} {rec : Ty × Ty} {var₁ var₂ : Ty → Type} {r : Bool}
    {Γ : WfCtx var₁ var₂} : Prog.Wf (S := S) (rec := rec) r Γ noStProg noStProg := by
  unfold noStProg
  prog_wf

theorem wf_bigProg {var₁ var₂ : Ty → Type} {r : Bool} {Γ : WfCtx var₁ var₂}
    {thr : ThrProg D} (hthr : ThrWf thr)
    {sub₁ : var₁ (hinstTy D) → Prog (groupSig D) (hinstTy D, Ty.answer D) var₁ (Ty.answer D)}
    {sub₂ : var₂ (hinstTy D) → Prog (groupSig D) (hinstTy D, Ty.answer D) var₂ (Ty.answer D)}
    (hsub : WfFun r Γ sub₁ sub₂) {I₁ : var₁ (hinstTy D)} {I₂ : var₂ (hinstTy D)}
    {L₁ : var₁ (.array (.list .nat))} {L₂ : var₂ (.array (.list .nat))}
    {n₀₁ n₁ m₁ : var₁ .nat} {n₀₂ n₂ m₂ : var₂ .nat} {G₁ : var₁ (Ty.group D)}
    {G₂ : var₂ (Ty.group D)} (hI : ⟨hinstTy D, I₁, I₂⟩ ∈ Γ)
    (hL : ⟨.array (.list .nat), L₁, L₂⟩ ∈ Γ) (hn₀ : ⟨.nat, n₀₁, n₀₂⟩ ∈ Γ)
    (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) (hG : ⟨Ty.group D, G₁, G₂⟩ ∈ Γ) :
    Prog.Wf r Γ (bigProg thr sub₁ I₁ L₁ n₀₁ n₁ m₁ G₁) (bigProg thr sub₂ I₂ L₂ n₀₂ n₂ m₂ G₂) := by
  unfold bigProg
  refine .bind (hthr _ _ _ _ _ _ hn₀) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) (.cons (by simp [hm]) .nil))) fun _ _ => ?_
  refine .ite (List.Mem.head _) ?_ (wf_m3Prog (hsub.mono (by intro x hx; simp [hx]))
    (by simp [hI]))
  refine .bind (.prim _ .nil) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp [hm]) (.cons (List.Mem.head _) .nil))) fun _ _ => ?_
  refine .bind (wf_degreeProg (by simp [hn]) (List.Mem.head _) (by simp [hG])) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) (.cons (by simp) .nil))) fun _ _ => ?_
  refine .ite (List.Mem.head _) ?_ ?_
  · refine .bind (by unfold m5OkProg; prog_wf) fun _ _ => ?_
    refine .ite (List.Mem.head _) ?_ (wf_m3Prog (hsub.mono (by intro x hx; simp [hx]))
      (by simp [hI]))
    refine .bind wf_noStProg fun _ _ => ?_
    exact wf_m5StepCJProg (hsub.mono (by intro x hx; simp [hx])) (by simp [hI]) (by simp [hL])
      (by simp) (List.Mem.head _)
  · refine .bind (by unfold m4OkProg; prog_wf) fun _ _ => ?_
    exact .ite (List.Mem.head _) (wf_m4StepProg (hsub.mono (by intro x hx; simp [hx]))
      (by simp [hI])) (wf_m3Prog (hsub.mono (by intro x hx; simp [hx])) (by simp [hI]))

theorem wf_hintProg {var₁ var₂ : Ty → Type} {r : Bool} {Γ : WfCtx var₁ var₂}
    {thr : ThrProg D} (hthr : ThrWf thr)
    {sub₁ : var₁ (hinstTy D) → Prog (groupSig D) (hinstTy D, Ty.answer D) var₁ (Ty.answer D)}
    {sub₂ : var₂ (hinstTy D) → Prog (groupSig D) (hinstTy D, Ty.answer D) var₂ (Ty.answer D)}
    (hsub : WfFun r Γ sub₁ sub₂) {I₁ : var₁ (hinstTy D)} {I₂ : var₂ (hinstTy D)}
    {L₁ : var₁ (.array (.list .nat))} {L₂ : var₂ (.array (.list .nat))}
    (hI : ⟨hinstTy D, I₁, I₂⟩ ∈ Γ) (hL : ⟨.array (.list .nat), L₁, L₂⟩ ∈ Γ) :
    Prog.Wf r Γ (hintProg thr sub₁ I₁ L₁) (hintProg thr sub₂ I₂ L₂) := by
  unfold hintProg
  refine .bind (.prim _ (.cons hI .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp [hI]) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) (.cons (by simp) .nil))) fun _ _ => ?_
  refine .bind (wf_normLabProg (by simp) (by simp [hL])) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) (.cons (List.Mem.head _) .nil))) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) (.cons (List.Mem.head _) .nil))) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) (.cons (List.Mem.head _) .nil))) fun _ _ => ?_
  refine .bind (wf_baseWinProg (by simp) (by simp)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) (.cons (List.Mem.head _) .nil))) fun _ _ => ?_
  refine .bind (.call _ (List.Mem.head _)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ .nil) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) (.cons (by simp) .nil))) fun _ _ => ?_
  refine .ite (List.Mem.head _) (wf_m1StepProg (hsub.mono (by intro x hx; simp [hx]))
    (by simp) (by simp)) ?_
  refine .bind (wf_baseBlocksProg (by simp) (by simp)) fun _ _ => ?_
  refine .bind (wf_blkOKProg (by simp) (List.Mem.head _)) fun _ _ => ?_
  refine .ite (List.Mem.head _) ?_ (wf_bigProg hthr (hsub.mono (by intro x hx; simp [hx]))
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (wf_neqProg (by simp) (by simp) (by simp) (by simp) (List.Mem.head _))
    fun _ _ => ?_
  exact .ite (List.Mem.head _) (wf_m2aStepProg (hsub.mono (by intro x hx; simp [hx]))
    (by simp) (by simp) (by simp)) (wf_m2bStepProg (hsub.mono (by intro x hx; simp [hx]))
    (by simp) (by simp))

/-- The full procedure is well formed. -/
theorem mainBody_wf {thr : ThrProg D} (hthr : ThrWf thr) : (mainBody thr).Wf := by
  intro var₁ var₂ x₁ x₂
  unfold mainBody
  refine .bind (wf_fixedTestProg (List.Mem.head _)) fun _ _ => ?_
  refine .ite (List.Mem.head _) (wf_fixedStepProg (by simp)) ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .caseOption (List.Mem.head _) ?_ fun _ _ =>
    wf_hintProg hthr wf_recurFun (by simp) (List.Mem.head _)
  refine .bind (wf_winOrbitsProg (by simp)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ .nil) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) (.cons (by simp) .nil))) fun _ _ => ?_
  exact .ite (List.Mem.head _) (wf_chainProg wf_recurFun (by simp) (by simp))
    (wf_m0StepProg wf_recurFun (by simp))

end Wf

end GraphIso.Main
