module

public import GraphIso.Main.DynSeq
public import GraphIso.Main.Transfer
public import GraphIso.Reductions.SubgroupProg

/-!
# The block-stabilizer loop and the M2b step

Stage 14j-2, items 4 (tag 3) and 5 (M2b) of `PLAN-14.md` §14.2. Let `P` (degree `N₁`, string
positions `[0, n)`) be transitive on a window `O` with hint labels, `R` the stabilizer of a
block `B₀` of a block system of `P`'s base action, `reps` a left cover of `P` by cosets of `R`,
and `R'` the re-basing of `R` onto the points of `B₀` (degree `N' = n + |B₀|`) with the labels
`L'` (the old labels intersected with `B₀`), which are valid hint data on every nonempty
`R`-invariant part of `O` (`m2b_hintValid`, `DOutcome.blockStab`).

* **`m2bLoopProg`**: a branch over `reps` (`branchProg`). Each coset `σ r • R` is solved through
  the child group `R'` (`viaChildProg`, which aligns the coset and transfers the answer back)
  by the **dynamic chain** (`dynSeqProg`) over `O` at degree `N'`: the first orbit `O''` of the
  current group `H ≤ R'` on the remaining points is a sub-call
  - with the labels `L'` when they are not constant on `O''` (`H` is transitive on `O''`, and
    the labels are valid hint data for `H`: `DSetting.hintK` for the `R'`-orbit `O_R ⊇ O''`);
  - without a hint otherwise: then `2 |O''| ≤ |O_R| ≤ |O|` (`DSetting.half`, by
    `card_le_of_const` for `R'`, transitive with the hint on `O_R`).
* The sub-calls are `MlChild sIn` instances: at most `sIn` generators, as the dynamic chain's
  handles receive (stage 14j-5a). A hinted sub-call has the labels `L'` (`MlChildL`,
  stage 14j-6a): `RunsWithin.m2bLoopProg_lab` states the loop for that predicate, and
  `RunsWithin.m2bLoopProg` (with `MlChild`) is its corollary. The M2b step and tag `3` of
  reduce-and-derive use it to give their children the label invariant.
* `RunsWithin.m2bLoopProg`: a correct answer for `(O, σ • P)`, at the cost of the children plus
  `m2bLoopCost`. The children are `|reps|` copies of one branch's children (the most expensive
  one), each `M2bChild |O| |B₀|`: at most `|O|` points, with the hint on `|B₀|` base points, or
  without a hint on at most `|O|/2` points.
* **The M2b step** (`m2bStepProg`, `RunsWithin.m2bStepProg`): for a hinted instance whose base
  action is transitive with a proper block system on which a label is equidistributed,
  `m2bProg` (the stabilizer of the first block and its re-basing) then `m2bLoopProg` for the
  group itself. With `2 |B₀| ≤ m` (`m2b_card`), the children are `StepChild |W| m`, with
  `c = |reps| ≤ m`.
-/

@[expose] public section

namespace GraphIso.Main

open Equiv Cost GraphIso GraphIso.Programs GraphIso.Toolkit GraphIso.Recursion

/-! ### The children of the loop -/

/-- **A child of the block-stabilizer loop** on a window of `p` points with the block's `m'`
points: at most `p` points, and the hint on `m'` base points or no hint on at most `p/2`. -/
def M2bChild (p m' : ℕ) (x : ℕ × Option ℕ) : Prop :=
  x.1 ≤ p ∧ (x.2 = some m' ∨ (x.2 = none ∧ 2 * x.1 ≤ p))

/-- A child of the loop is a `StepChild` of a parent with at least `p` window points and at
least `2 m'` base points. -/
theorem M2bChild.stepChild {p m' n m : ℕ} {x : ℕ × Option ℕ} (h : M2bChild p m' x)
    (hp : p ≤ n) (hm : 2 * m' ≤ m) : StepChild n m x := by
  obtain ⟨h1, h2 | ⟨h2, h3⟩⟩ := h
  · exact ⟨by omega, Or.inl ⟨m', h2, by omega⟩⟩
  · exact ⟨by omega, Or.inr ⟨h2, by omega⟩⟩

/-- **Weakening the sub-solver's predicate.** -/
theorem HSubSolves.mono {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
    {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}
    {sub : HInstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)}
    {P Q : HInstData D → Prop} {C : ℕ → Option ℕ → ℕ} {s : ℕ}
    (h : HSubSolves X body DV sub P C s) (hQP : ∀ J, Q J → P J) : HSubSolves X body DV sub Q C s :=
  fun J hJ hQ => h J hJ (hQP J hQ)

/-! ### Programs -/

section Progs

variable {D : Ty} {rec : Ty × Ty} {var : Ty → Type}

/-- **The handle** of the dynamic chain at the re-based degree: the orbit `O` of the current
coset `c`, with the labels `L'` if they are not constant on `O`, and without a hint
otherwise. -/
def mlHandle (sub : var (hinstTy D) → Prog (groupSig D) rec var (Ty.answer D))
    (L' : var (.array (.list .nat))) (n₀ n : var .nat) (xy : var Ty.strs)
    (c : var (Ty.coset D)) (O : var (.list .nat)) : Prog (groupSig D) rec var (Ty.answer D) :=
  .bind (.op1 .snd c) fun H => .bind (.op1 .fst H) fun N =>
  .bind (ncBProg n N L' O) fun nc =>
  .bind (mkWindow N O) fun w => .bind (.op2 .pair w c) fun wc =>
  .bind (.op2 .pair xy wc) fun J =>
  .bind (.ite nc (.op1 .some L') (.op0 .none)) fun lab =>
  .bind (mkHInstProg J n₀ n lab) sub

/-- The child's solver: the dynamic chain on the child instance's window. -/
def mlInner (sub : var (hinstTy D) → Prog (groupSig D) rec var (Ty.answer D))
    (L' : var (.array (.list .nat))) (n₀ n : var .nat) (J : var (hinstTy D)) :
    Prog (groupSig D) rec var (Ty.answer D) :=
  .bind (.op1 .fst J) fun I => .bind (.op1 .fst I) fun xy => .bind (.op1 .snd I) fun wc =>
  .bind (.op1 .fst wc) fun w => .bind (.op1 .snd wc) fun c => .bind (.op1 .fst w) fun pts =>
  dynSeqProg (mlHandle sub L' n₀ n) xy c pts

/-- **One branch**: the coset `σ r • R` of the instance `I`, through the re-based group `R'`. -/
def mlBranch (sub : var (hinstTy D) → Prog (groupSig D) rec var (Ty.answer D))
    (R' : var (Ty.group D)) (L' : var (.array (.list .nat))) (n₀ n : var .nat)
    (I : var (Ty.inst D)) : Prog (groupSig D) rec var (Ty.answer D) :=
  .bind (.op1 .fst I) fun xy => .bind (.op1 .snd I) fun wc =>
  .bind (.op1 .fst wc) fun w => .bind (.op1 .snd wc) fun c =>
  .bind (.op1 .fst c) fun σr => .bind (.op1 .snd c) fun R =>
  .bind (.op1 .fst R') fun N' => .bind (.op1 .fst w) fun pts =>
  .bind (mkWindow N' pts) fun w' => .bind (.op0 .none) fun nl =>
  viaChildProg (mlInner sub L' n₀ n) xy σr R n₀ n R' w' nl

/-- **The block-stabilizer loop**: the cosets `σ r • R` (`r ∈ reps`) of the window `O`, each
through the re-based group `R'` with the labels `L'`. -/
def m2bLoopProg (sub : var (hinstTy D) → Prog (groupSig D) rec var (Ty.answer D))
    (xy : var Ty.strs) (σ : var Ty.perm) (R R' : var (Ty.group D)) (reps : var Ty.gens)
    (O : var (.list .nat)) (L' : var (.array (.list .nat))) (n₀ n : var .nat) :
    Prog (groupSig D) rec var (Ty.answer D) :=
  .bind (.op1 .fst R) fun N₁ => .bind (mkWindow N₁ O) fun w =>
  branchProg (mlBranch sub R' L' n₀ n) xy w σ R reps

/-- **The M2b step** on the hinted instance `I` with the block list `bs` of its base: the
stabilizer of block `0` and its re-basing (`m2bProg`), then the block-stabilizer loop for the
instance's group itself. -/
def m2bStepProg (sub : var (hinstTy D) → Prog (groupSig D) rec var (Ty.answer D))
    (I : var (hinstTy D)) (bs : var (.list (.list .nat))) :
    Prog (groupSig D) rec var (Ty.answer D) :=
  .bind (.op1 .fst I) fun J => .bind (.op1 .snd I) fun r₁ =>
  .bind (.op1 .fst r₁) fun n₀ => .bind (.op1 .snd r₁) fun r₂ =>
  .bind (.op1 .fst r₂) fun n => .bind (.op1 .snd r₂) fun lab =>
  .caseOption lab (.op0 .none) fun L =>
  .bind (.op1 .fst J) fun xy => .bind (.op1 .snd J) fun wc =>
  .bind (.op1 .fst wc) fun w => .bind (.op1 .snd wc) fun c =>
  .bind (.op1 .fst c) fun σ => .bind (.op1 .snd c) fun G =>
  .bind (.op1 .fst G) fun N => .bind (.op1 .snd G) fun gd => .bind (.op1 .fst gd) fun gs =>
  .bind (.op1 .fst w) fun O => .bind (.op0 (.natLit 0)) fun t =>
  .bind (m2bProg n N gs bs t L O) fun res =>
  .bind (.op1 .fst res) fun Hr => .bind (.op1 .fst Hr) fun R => .bind (.op1 .snd Hr) fun reps =>
  .bind (.op1 .snd res) fun hl => .bind (.op1 .fst hl) fun R' => .bind (.op1 .snd hl) fun L' =>
  m2bLoopProg sub xy σ R R' reps O L' n₀ n

end Progs

/-! ### Costs -/

/-- The work of the handle at degree `N'` on an orbit of at most `p` points. -/
def mlHandleCost (n N' p : ℕ) : ℕ := ncBCost n N' p (N' - n) + 2 * N' + 5 * p + 20

/-- The work of one branch beyond its children: the child (degree `N'`), the dynamic chain on
`p` points (`orbits` charge `Bo`, `sIn` generators), and the transfer to degree `N₁`. -/
def mlBranchCost (N₁ N' n p sIn Blift Bgen Bo : ℕ) : ℕ :=
  2 * N' + 5 * p + 30 + viaChildCost N₁ N' n sIn Blift Bgen + p * mlHandleCost n N' p +
    dynSeqCost N' p Bo

/-- **The work of the loop** beyond its children: `r` branches, `sR` branch generators, and the
final `generate` charge `Bgen₂`. -/
def m2bLoopCost (N₁ N' n p r sIn sR Blift Bgen Bo Bgen₂ : ℕ) : ℕ :=
  r * (24 * N₁ + mlBranchCost N₁ N' n p sIn Blift Bgen Bo + sR + 45) + Bgen₂ + 2 * N₁ +
    5 * p + 30

/-- **The cost of the M2b step** beyond its children, on `p` window points with base size
`m = N − n`, the block's `k` points, a label array of size `Ls`, `s` generators, and the
charges of `m2bProg` (`M2bCharges`) and of the loop. -/
def m2bStepCost (n N k p Ls s sS Lt sH sIn sR Bge Bst Btr Bgt Bgen₃ Blift Bgen Bo Bgen₂ : ℕ) :
    ℕ :=
  m2bCost N n (N - n) (N - n) s sS Lt Bge Bst Btr Bgt k sH Bgen₃ p (N - n) Ls +
    m2bLoopCost N (n + k) n p (N - n) sIn sR Blift Bgen Bo Bgen₂ + 30

theorem ml_ncBCost_mono {n N p p' Lb : ℕ} (h : p ≤ p') : ncBCost n N p Lb ≤ ncBCost n N p' Lb := by
  simp only [ncBCost, ncCost]
  have h1 : p * (ncPairCost (N - n) Lb + 2) ≤ p' * (ncPairCost (N - n) Lb + 2) :=
    Nat.mul_le_mul_right _ h
  have h2 : p * (p * (ncPairCost (N - n) Lb + 2) + 3) ≤
      p' * (p' * (ncPairCost (N - n) Lb + 2) + 3) := Nat.mul_le_mul h (by omega)
  omega

/-! ### Facts -/

section Facts

/-- **Invariance of string positions transfers** along an isomorphism with the same action on
`[0, n)`. -/
theorem ml_inv_iff {N₁ N' n : ℕ} {R : Subgroup (Perm (Fin N₁))} {R' : Subgroup (Perm (Fin N'))}
    (θ : ↥R ≃* ↥R')
    (hθ : ∀ (g : ↥R) (j : ℕ) (hj : j < N₁) (hj' : j < N'), j < n →
      ((θ g : Perm (Fin N')) ⟨j, hj'⟩).val = (g.1 ⟨j, hj⟩).val)
    (hn₁ : n ≤ N₁) (hn' : n ≤ N') {S : List ℕ} (hS : ∀ i ∈ S, i < n) :
    IsInvariant R (ptsSet N₁ S) ↔ IsInvariant R' (ptsSet N' S) := by
  constructor
  · intro h g' hg' u hu
    have hun : u.val < n := hS _ hu
    set g := θ.symm ⟨g', hg'⟩ with hg
    have e := hθ g u.val (by omega) u.2 hun
    rw [hg, MulEquiv.apply_symm_apply] at e
    change (g' u).val ∈ S
    have : (g' ⟨u.val, u.2⟩).val = (g' u).val := rfl
    rw [← this, e]
    exact h g.1 g.2 ⟨u.val, by omega⟩ hu
  · intro h g hg u hu
    have hun : u.val < n := hS _ hu
    have e := hθ ⟨g, hg⟩ u.val u.2 (by omega) hun
    change (g u).val ∈ S
    have : (g ⟨u.val, u.2⟩).val = (g u).val := rfl
    rw [← this, ← e]
    exact h _ (θ ⟨g, hg⟩).2 ⟨u.val, by omega⟩ hu

/-- A duplicate-free sublist is no longer than the list. -/
theorem ml_length_le {l l' : List ℕ} (hnd : l.Nodup) (hsub : ∀ i ∈ l, i ∈ l') :
    l.length ≤ l'.length := by
  rw [← List.toFinset_card_of_nodup hnd]
  exact (Finset.card_le_card fun i hi => List.mem_toFinset.2
    (hsub i (List.mem_toFinset.1 hi))).trans (List.toFinset_card_le _)

end Facts

/-! ### The handle -/

section HandleSpec

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}

/-- The predicate on the sub-calls of the loop, with at most `sC` generators. -/
def MlChild (sC n₀ n N' p : ℕ) (J : HInstData D) : Prop :=
  J.n₀ = n₀ ∧ J.n = n ∧ J.inst.degree = N' ∧ J.inst.2.2.2.gens.length ≤ sC ∧
    M2bChild p (N' - n) (J.winSize, J.baseOpt)

/-- **The sub-calls of the loop with their labels** (stage 14j-6a, `PLAN-14.md` §14.10):
`MlChild`, and the hint, if any, is the loop's labels `L'`. -/
def MlChildL (sC n₀ n N' p : ℕ) (L' : LabelData) (J : HInstData D) : Prop :=
  MlChild sC n₀ n N' p J ∧ ∀ L, J.lab = some L → L = L'

/-- **The handle is correct**: on an orbit `O''` of a valid coset `τ • H` (`H ≤ R'`) inside
`O`, the sub-call is on a valid hinted instance (with the labels `L'` exactly when they are
not constant on `O''`) satisfying `MlChild`. -/
theorem ml_handle {sub : HInstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)}
    {C : ℕ → Option ℕ → ℕ} {s sIn : ℕ} {n₀ n N₁ N' : ℕ} {gsR gsR' : GensData}
    {dR' : D.denote} {O : List ℕ} {L' : LabelData}
    (hsub : HSubSolves X body DV sub (MlChildL sIn n₀ n N' O.length L') C s)
    (hn₁ : n ≤ N₁) (hc : ChildRel DV n N₁ gsR N' gsR' dR' (WinData.ofPoints N' O))
    (hhint : ∀ wO : WinData, (∀ i ∈ wO.1, i ∈ O) → wO.1 ≠ [] →
      IsInvariant (GensData.denote N₁ gsR) (wO.denote N₁) → HintValid n N' gsR' wO L')
    (hs : s ≤ sIn) (xy : StrData × StrData) :
    DynHandle X body DV (fun xy c O'' => mlHandle sub L' n₀ n xy c O'') xy N'
      (GensData.denote N' gsR') O sIn (fun _ g => C g.1 g.2 + mlHandleCost n N' O.length)
      (fun O'' g => g.1 = O''.length ∧ 1 ≤ O''.length ∧ M2bChild O.length (N' - n) g) := by
  classical
  intro τ Hd O'' hτ hHd hHv hHs hHle hnd hne hsubO horb
  obtain ⟨Nd, gs, d⟩ := Hd
  change Nd = N' at hHd
  subst hHd
  change GroupValid DV Nd gs d at hHv
  change GensData.denote Nd gs ≤ GensData.denote Nd gsR' at hHle
  obtain ⟨θ, hθ⟩ := hc.iso
  have hOv : (WinData.ofPoints Nd O).Valid Nd := hc.win
  have hOlt : ∀ i ∈ O, i < n := hc.win_lt
  -- the `R'`-orbit of a point of `O''` inside `O`
  obtain ⟨i₀, hi₀⟩ := List.exists_mem_of_ne_nil O'' hne
  set OR := O.filter fun j => decide (SameOrbit (GensData.denote Nd gsR') i₀ j) with hORdef
  have hmemOR : ∀ j, j ∈ OR ↔ j ∈ O ∧ SameOrbit (GensData.denote Nd gsR') i₀ j := by
    intro j
    simp [hORdef]
  have hORnd : OR.Nodup := hOv.nodup.filter _
  have hORsub : ∀ j ∈ OR, j ∈ O := fun j hj => ((hmemOR j).1 hj).1
  have hORlt : ∀ j ∈ OR, j < Nd := fun j hj => by have := hOlt j (hORsub j hj); have := hc.le; omega
  have hsubOR : ∀ j ∈ O'', j ∈ OR := by
    intro j hj
    refine (hmemOR j).2 ⟨hsubO j hj, ?_⟩
    obtain ⟨hi, hj', g, hg, e⟩ := (horb i₀ hi₀ j).1 hj
    exact ⟨hi, hj', g, hHle hg, e⟩
  have hORinv : IsInvariant (GensData.denote Nd gsR') (ptsSet Nd OR) := by
    intro g hg u hu
    obtain ⟨huO, hsame⟩ := (hmemOR u.val).1 hu
    refine (hmemOR _).2 ⟨?_, hsame.trans ⟨u.2, (g u).2, g, hg, rfl⟩⟩
    exact hc.inv g hg u huO
  have hORne : OR ≠ [] := List.ne_nil_of_mem (hsubOR i₀ hi₀)
  have hORv : (WinData.ofPoints Nd OR).Valid Nd := WinData.valid_ofPoints hORnd hORlt
  have hORinvR : IsInvariant (GensData.denote N₁ gsR) ((WinData.ofPoints Nd OR).denote N₁) :=
    (ml_inv_iff θ hθ hn₁ hc.le fun i hi => hOlt i (hORsub i hi)).2 hORinv
  have hLOR : HintValid n Nd gsR' (WinData.ofPoints Nd OR) L' :=
    hhint _ hORsub hORne hORinvR
  have hORtr : IsTransOn (GensData.denote Nd gsR') ((WinData.ofPoints Nd OR).denote Nd) := by
    intro u hu v hv
    obtain ⟨-, hsu⟩ := (hmemOR u.val).1 hu
    obtain ⟨-, hsv⟩ := (hmemOR v.val).1 hv
    obtain ⟨_, _, g, hg, e⟩ := hsu.symm.trans hsv
    exact ⟨g, hg, e⟩
  have hS : DSetting DV n Nd gsR' (WinData.ofPoints Nd OR) L' gs d O'' :=
    ⟨hLOR, hc.valid.1, hORv, hORinv, hORtr, hc.faithful, hHv, hHle, hnd, hsubOR, horb, hne⟩
  -- the label lengths
  have hOne : O ≠ [] := List.ne_nil_of_mem (hsubO i₀ hi₀)
  have hLO : HintValid n Nd gsR' (WinData.ofPoints Nd O) L' :=
    hhint _ (fun i hi => hi) hOne ((ml_inv_iff θ hθ hn₁ hc.le hOlt).2 hc.inv)
  have hLb : ∀ i ∈ O'', (L'.getD i []).length ≤ Nd - n := fun i hi =>
    mf_length_le_of_nodup (hLO.lab_nodup i (hsubO i hi)) (hLO.lab_lt i (hsubO i hi))
  have hlen : O''.length ≤ O.length := ml_length_le hnd hsubO
  have hlenOR : OR.length ≤ O.length := ml_length_le hORnd hORsub
  have hpos : 1 ≤ O''.length := List.length_pos_of_ne_nil hne
  -- the sub-call
  have hrunNc := RunsWithin.ncBProg (X := X) (body := body) n Nd L' O'' hLb
  have hrunC : ∀ (lab : Option LabelData) (ans : AnswerData D) (k : ℕ),
      RunsWithin X body (Prog.ite (t := .option (.array (.list .nat))) (ncBD n Nd L' O'')
        (.op1 .some L') (.op0 .none)) lab 2 →
      RunsWithin X body
        (sub ((((xy, (WinData.ofPoints Nd O'', (τ, (Nd, gs, d)))), (n₀, (n, lab))) :
          HInstData D))) ans k →
      RunsWithin X body (Main.mlHandle sub L' n₀ n xy (τ, (Nd, gs, d)) O'') ans
        (k + (ncBCost n Nd O''.length (Nd - n) + 2 * Nd + 5 * O''.length + 16)) := by
    intro lab ans k hlab h
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step hrunNc
      run_step (RunsWithin.mkWindow _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step hlab
      run_step (RunsWithin.mkHInstProg _ _ _ _)
      exact h
    case hc =>
      simp only [Prim.cost, Prim.eval]
      omega
  have hvalid : ∀ lab : Option LabelData, (∀ L, lab = some L →
      HintValid n Nd gs (WinData.ofPoints Nd O'') L ∧
        IsTransOn (GensData.denote Nd gs) ((WinData.ofPoints Nd O'').denote Nd)) →
      HInstValid DV ((((xy, (WinData.ofPoints Nd O'', (τ, (Nd, gs, d)))), (n₀, (n, lab))) :
        HInstData D)) := fun lab hL =>
    ⟨⟨hS.owin, hτ, hHv, hS.oinv⟩, hc.le, hS.base_inv, hS.win_lt, hS.kfaith, hL⟩
  have hcost : ncBCost n Nd O''.length (Nd - n) + 2 * Nd + 5 * O''.length + 16 ≤
      mlHandleCost n Nd O.length := by
    have := ml_ncBCost_mono (n := n) (N := Nd) (Lb := Nd - n) hlen
    simp only [mlHandleCost]
    omega
  cases hcb : ncBD n Nd L' O''
  · -- the labels are constant on `O''`: no hint
    have hhalf := hS.half hcb
    change 2 * O''.length ≤ OR.length at hhalf
    obtain ⟨ans, hr, hok, hg⟩ := hsub _ (hvalid none fun _ h => by cases h)
      ⟨⟨rfl, rfl, rfl, hHs, hlen, Or.inr ⟨rfl, by change 2 * O''.length ≤ O.length; omega⟩⟩,
        fun _ h => by cases h⟩
    refine ⟨ans, (O''.length, none), ?_, hok, fun c hc => (hg c hc).trans hs,
      rfl, hpos, hlen, Or.inr ⟨rfl, by omega⟩⟩
    have hlab : RunsWithin X body (Prog.ite (t := .option (.array (.list .nat)))
        (ncBD n Nd L' O'') (.op1 .some L') (.op0 .none))
        (none : Option LabelData) 2 := by
      rw [hcb]
      exact RunsWithin.ite_false (RunsWithin.prim _ _)
    exact (hrunC none ans _ hlab hr).mono (by
      change C O''.length none + _ ≤ C O''.length none + _
      omega)
  · -- the labels are not constant on `O''`: the hint `L'`
    have hint := hS.hintK hcb
    obtain ⟨ans, hr, hok, hg⟩ := hsub _ (hvalid (some L') fun L h => by
        cases h
        exact ⟨hint, hS.otrans⟩)
      ⟨⟨rfl, rfl, rfl, hHs, hlen, Or.inl rfl⟩, fun _ h => (Option.some.inj h).symm⟩
    refine ⟨ans, (O''.length, some (Nd - n)), ?_, hok, fun c hc => (hg c hc).trans hs,
      rfl, hpos, hlen, Or.inl rfl⟩
    have hlab : RunsWithin X body (Prog.ite (t := .option (.array (.list .nat)))
        (ncBD n Nd L' O'') (.op1 .some L') (.op0 .none))
        (some L') 2 := by
      rw [hcb]
      exact RunsWithin.ite_true (RunsWithin.prim _ _)
    exact (hrunC (some L') ans _ hlab hr).mono (by
      change C O''.length (some (Nd - n)) + _ ≤ C O''.length (some (Nd - n)) + _
      omega)

end HandleSpec

/-! ### One branch -/

section BranchSpec

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}

/-- The backend operations of the loop. -/
def m2bLoopOps (op : GroupOp) : Prop := op = .lift ∨ op = .generate ∨ op = .orbits

/-- The number of steps of a dynamic chain is at most the number of points. -/
theorem ml_sum_add {α : Type*} (f : α → ℕ) (K : ℕ) (l : List α) :
    (l.map fun s => f s + K).sum = (l.map f).sum + l.length * K := by
  induction l with
  | nil => simp
  | cons s l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih, Nat.succ_mul]
    omega

theorem ml_steps_le {γ : Type} {steps : List (List ℕ × γ)} {p : ℕ}
    (hsum : (steps.map fun s => s.1.length).sum ≤ p) (hQ : ∀ s ∈ steps, 1 ≤ s.1.length) :
    steps.length ≤ p := by
  have : (steps.map fun _ => 1).sum ≤ (steps.map fun s => s.1.length).sum :=
    List.sum_le_sum fun s hs => hQ s hs
  simp only [List.map_const', List.sum_replicate, smul_eq_mul, mul_one] at this
  omega

/-- **One branch of the loop**: the coset `σr • R` of the window `O`, through `R'`. -/
theorem ml_branch (hO : MeetsContractOn DV m2bLoopOps X.O)
    (hPre : ∀ op x, m2bLoopOps op → GroupPre DV op x → X.Pre op x)
    {sub : HInstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)}
    {C : ℕ → Option ℕ → ℕ} {s sIn : ℕ} {n₀ n N₁ N' : ℕ} {gsR gsR' : GensData}
    {dR dR' : D.denote} {O : List ℕ} {L' : LabelData}
    (hsub : HSubSolves X body DV sub (MlChildL sIn n₀ n N' O.length L') C s)
    (hn₁ : n ≤ N₁) (hR : GroupValid DV N₁ gsR dR)
    (hRb : IsInvariant (GensData.denote N₁ gsR) (baseSet n N₁))
    (hc : ChildRel DV n N₁ gsR N' gsR' dR' (WinData.ofPoints N' O))
    (hhint : ∀ wO : WinData, (∀ i ∈ wO.1, i ∈ O) → wO.1 ≠ [] →
      IsInvariant (GensData.denote N₁ gsR) (wO.denote N₁) → HintValid n N' gsR' wO L')
    (hs : s ≤ sIn) (hsR' : gsR'.length ≤ sIn) {σr : PermData} (hσ : σr.Valid N₁)
    (xy : StrData × StrData) {Blift Bgen Bo : ℕ}
    (hBlift : ∀ π' : PermData, π'.Valid n →
      X.B.call GroupOp.lift ((N₁, gsR, dR), (strWin N₁ n, π'))
        (X.O.run GroupOp.lift ((N₁, gsR, dR), (strWin N₁ n, π'))) ≤ Blift)
    (hBgen : ∀ hs : GensData, GensData.AllValid N₁ hs → hs.length ≤ sIn →
      GensData.denote N₁ hs ≤ GensData.denote N₁ gsR →
      X.B.call GroupOp.generate (N₁, hs) (X.O.run GroupOp.generate (N₁, hs)) ≤ Bgen)
    (hBo : ∀ (Hd : GroupData D.denote) (w : WinData), Hd.1 = N' → Hd.2.1.length ≤ sIn →
      GensData.denote N' Hd.2.1 ≤ GensData.denote N' gsR' → GroupPre DV .orbits (Hd, w) →
      X.B.call GroupOp.orbits (Hd, w) (X.O.run GroupOp.orbits (Hd, w)) ≤ Bo) :
    ∃ (ans : AnswerData D) (ch : List (ℕ × Option ℕ)),
      RunsWithin X body
        (Main.mlBranch sub (N', gsR', dR') L' n₀ n
          (xy, (WinData.ofPoints N₁ O, (σr, (N₁, gsR, dR))))) ans
        ((ch.map fun x => C x.1 x.2).sum + mlBranchCost N₁ N' n O.length sIn Blift Bgen Bo) ∧
      AnsOK DV N₁ (ptsSet N₁ O) (PermData.denote N₁ σr) (GensData.denote N₁ gsR)
        (xy.1.denote N₁) (xy.2.denote N₁) ans ∧
      (∀ sGen, (∀ hs, GensData.AllValid N₁ hs →
          GensData.denote N₁ hs ≤ GensData.denote N₁ gsR →
          (X.O.run GroupOp.generate (N₁, hs)).2.1.length ≤ sGen) →
        ∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sGen) ∧
      (ch.map Prod.fst).sum ≤ O.length ∧ (∀ x ∈ ch, M2bChild O.length (N' - n) x) ∧
        ∀ x ∈ ch, 1 ≤ x.1 := by
  have hOo : MeetsContractOn DV (· = .orbits) X.O := fun op x h => hO op x (Or.inr (Or.inr h))
  have hPo : ∀ x, GroupPre DV .orbits x → X.Pre .orbits x :=
    fun x h => hPre _ x (Or.inr (Or.inr rfl)) h
  have hOt : MeetsContractOn DV transferOps X.O := fun op x h => hO op x (by
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h))
  have hPt : ∀ op x, transferOps op → GroupPre DV op x → X.Pre op x := fun op x h hx =>
    hPre op x (by
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)) hx
  -- the dynamic chain on the child
  set x' := padD N' xy.1 with hx'
  set y' := padCompD N' xy.2 σr with hy'
  obtain ⟨ans₁, steps, hr₁, hok₁, hg₁, hsum, hQ⟩ :=
    RunsWithin.dynSeqProg (X := X) (body := body) (handle := fun xy c O'' =>
      Main.mlHandle sub L' n₀ n xy c O'') (xy := (x', y')) (σd := PermData.one N') hOo hPo
      (PermData.valid_one N') hc.valid hsR' hc.win.nodup hc.win.lt hc.inv
      (ml_handle hsub hn₁ hc hhint hs (x', y')) hBo
  have hw1 : (WinData.ofPoints N' O).1 = O := rfl
  rw [hw1] at hr₁ hsum
  set ch := steps.map Prod.snd with hch
  have hlen : steps.length ≤ O.length := ml_steps_le hsum fun s hs => (hQ s hs).2.1
  have hcost₁ : (steps.map fun s => C s.2.1 s.2.2 + mlHandleCost n N' O.length).sum =
      (ch.map fun x => C x.1 x.2).sum + steps.length * mlHandleCost n N' O.length := by
    rw [ml_sum_add (fun s : List ℕ × (ℕ × Option ℕ) => C s.2.1 s.2.2), hch, List.map_map]
    rfl
  -- the child's solver, at the child instance
  set J₀ := childHInst xy.1 xy.2 σr n₀ n (N', gsR', dR') (WinData.ofPoints N' O) none
    with hJ₀
  set K₀ := (ch.map fun x => C x.1 x.2).sum + O.length * mlHandleCost n N' O.length +
    dynSeqCost N' O.length Bo + 6 with hK₀
  have hinner : HSubSolves X body DV
      (Main.mlInner (var := Ty.denote) (rec := (a, b)) (D := D) sub L' n₀ n) (fun J => J = J₀)
      (fun _ _ => K₀) sIn := by
    rintro J - rfl
    refine ⟨ans₁, ?_, hok₁, hg₁⟩
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      exact hr₁
    case hc =>
      have := Nat.mul_le_mul_right (mlHandleCost n N' O.length) hlen
      simp only [Prim.cost]
      omega
  obtain ⟨ans, hr, hok, hg⟩ := RunsWithin.viaChildProg (X := X) (body := body) (n₀ := n₀) hOt
    hPt hinner hR hn₁ hRb hσ xy hc (L' := none) (fun _ h => by cases h) rfl hBlift hBgen
  refine ⟨ans, ch, ?_, hok, hg, ?_, ?_, ?_⟩
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.mkWindow _ _)
      run_step (RunsWithin.prim _ _)
      exact hr
    case hc =>
      have hw2 : (WinData.ofPoints N₁ O).1 = O := rfl
      simp only [Prim.cost, Prim.eval, mlBranchCost, hw2]
      omega
  · have e : (ch.map Prod.fst).sum = (steps.map fun s => s.1.length).sum := by
      rw [hch, List.map_map]
      congr 1
      refine List.map_congr_left fun s hs => ?_
      exact (hQ s hs).1
    omega
  · intro x hx
    rw [hch] at hx
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hx
    exact (hQ s hs).2.2
  · intro x hx
    rw [hch] at hx
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hx
    obtain ⟨h1, h2, -⟩ := hQ s hs
    omega

end BranchSpec

/-! ### The loop -/

section LoopSpec

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}

/-- **The most expensive branch**: among values `P x y` for every `x ∈ l`, one with the largest
`f`, or the default `b₀`. -/
theorem ml_exists_max {α β : Type*} (f : β → ℕ) (b₀ : β) (P : α → β → Prop) :
    ∀ l : List α, (∀ x ∈ l, ∃ y, P x y) →
      ∃ y₀ : β, (y₀ = b₀ ∨ ∃ x ∈ l, P x y₀) ∧ ∀ x ∈ l, ∃ y, P x y ∧ f y ≤ f y₀
  | [], _ => ⟨b₀, Or.inl rfl, by simp⟩
  | x :: l, h => by
    obtain ⟨y₁, hy₁, hmax⟩ := ml_exists_max f b₀ P l fun x' hx' => h x' (List.mem_cons_of_mem _ hx')
    obtain ⟨yx, hyx⟩ := h x List.mem_cons_self
    by_cases hle : f y₁ ≤ f yx
    · refine ⟨yx, Or.inr ⟨x, List.mem_cons_self, hyx⟩, fun x' hx' => ?_⟩
      rcases List.mem_cons.1 hx' with rfl | hx'
      · exact ⟨yx, hyx, le_rfl⟩
      · obtain ⟨y, hy, hfy⟩ := hmax x' hx'
        exact ⟨y, hy, hfy.trans hle⟩
    · refine ⟨y₁, ?_, fun x' hx' => ?_⟩
      · rcases hy₁ with hy₁ | ⟨x', hx', hP⟩
        · exact Or.inl hy₁
        · exact Or.inr ⟨x', List.mem_cons_of_mem _ hx', hP⟩
      · rcases List.mem_cons.1 hx' with rfl | hx'
        · exact ⟨yx, hyx, by omega⟩
        · exact hmax x' hx'

theorem ml_isLeftCover_map {M : ℕ} {G K : Subgroup (Perm (Fin M))} {rs : List PermData}
    (h : IsLeftCover G K fun i : Fin rs.length => PermData.denote M (rs.get i)) :
    IsLeftCover G K fun i : Fin (rs.map (PermData.denote M)).length =>
      (rs.map (PermData.denote M)).get i := by
  refine ⟨fun i => ?_, fun g hg => ?_⟩
  · rw [List.get_eq_getElem, List.getElem_map]
    exact h.mem ⟨i, by simpa using i.2⟩
  · obtain ⟨i, hi⟩ := h.cover g hg
    refine ⟨⟨i, by simp⟩, ?_⟩
    rw [List.get_eq_getElem, List.getElem_map]
    exact hi

theorem ml_sum_replicate {α : Type*} (f : α → ℕ) (l : List α) (r : ℕ) :
    (((List.replicate r l).flatten).map f).sum = r * (l.map f).sum := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [List.replicate_succ, List.flatten_cons, List.map_append, List.sum_append, ih]
    ring

/-- **The block-stabilizer loop, with the children's labels** (`MlChildL`: a hinted child has
the loop's labels `L'`; stage 14j-6a). Let `R ≤ P` (degree `N₁`) with the cover `reps`, `O` a
`P`-invariant window of string positions, and `R'` the re-basing of `R` (`ChildRel`, degree
`N'`) with labels `L'` that are valid hint data on every nonempty `R`-invariant part of `O`.
The result is a correct answer for `(O, σ • P)`, at the cost of the children plus
`m2bLoopCost`. The children (`|reps|` copies of one branch's) are `M2bChild |O| (N' − n)`, and
their windows sum to at most `|reps| · |O|`. -/
theorem RunsWithin.m2bLoopProg_lab (hO : MeetsContractOn DV m2bLoopOps X.O)
    (hPre : ∀ op x, m2bLoopOps op → GroupPre DV op x → X.Pre op x)
    {sub : HInstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)}
    {C : ℕ → Option ℕ → ℕ} {s : ℕ} {n₀ n N₁ N' : ℕ} {gsP gsR gsR' : GensData}
    {dR dR' : D.denote} {O : List ℕ} {L' : LabelData} {reps : List PermData} {sIn sR : ℕ}
    (hsub : HSubSolves X body DV sub (MlChildL sIn n₀ n N' O.length L') C s)
    (hn₁ : n ≤ N₁) (hR : GroupValid DV N₁ gsR dR)
    (hRP : GensData.denote N₁ gsR ≤ GensData.denote N₁ gsP)
    (hRb : IsInvariant (GensData.denote N₁ gsR) (baseSet n N₁))
    (hOP : IsInvariant (GensData.denote N₁ gsP) (ptsSet N₁ O))
    (hreps : ∀ r ∈ reps, PermData.Valid N₁ r)
    (hcov : IsLeftCover (GensData.denote N₁ gsP) (GensData.denote N₁ gsR)
      (fun i : Fin reps.length => PermData.denote N₁ (reps.get i)))
    (hc : ChildRel DV n N₁ gsR N' gsR' dR' (WinData.ofPoints N' O))
    (hhint : ∀ wO : WinData, (∀ i ∈ wO.1, i ∈ O) → wO.1 ≠ [] →
      IsInvariant (GensData.denote N₁ gsR) (wO.denote N₁) → HintValid n N' gsR' wO L')
    (hs : s ≤ sIn) (hsR' : gsR'.length ≤ sIn) {σd : PermData}
    (hσ : σd.Valid N₁) (xy : StrData × StrData) {Blift Bgen Bo Bgen₂ : ℕ}
    (hBlift : ∀ π' : PermData, π'.Valid n →
      X.B.call GroupOp.lift ((N₁, gsR, dR), (strWin N₁ n, π'))
        (X.O.run GroupOp.lift ((N₁, gsR, dR), (strWin N₁ n, π'))) ≤ Blift)
    (hBgen : ∀ hs : GensData, GensData.AllValid N₁ hs → hs.length ≤ sIn →
      GensData.denote N₁ hs ≤ GensData.denote N₁ gsR →
      X.B.call GroupOp.generate (N₁, hs) (X.O.run GroupOp.generate (N₁, hs)) ≤ Bgen)
    (hBo : ∀ (Hd : GroupData D.denote) (w : WinData), Hd.1 = N' → Hd.2.1.length ≤ sIn →
      GensData.denote N' Hd.2.1 ≤ GensData.denote N' gsR' → GroupPre DV .orbits (Hd, w) →
      X.B.call GroupOp.orbits (Hd, w) (X.O.run GroupOp.orbits (Hd, w)) ≤ Bo)
    (hsR : ∀ hs : GensData, GensData.AllValid N₁ hs →
      GensData.denote N₁ hs ≤ GensData.denote N₁ gsR →
      (X.O.run GroupOp.generate (N₁, hs)).2.1.length ≤ sR)
    (hBgen₂ : ∀ gs : GensData, GensData.AllValid N₁ gs → gs.length ≤ reps.length * (sR + 1) →
      GensData.denote N₁ gs ≤ GensData.denote N₁ gsP →
      X.B.call GroupOp.generate (N₁, gs) (X.O.run GroupOp.generate (N₁, gs)) ≤ Bgen₂) :
    ∃ (ans : AnswerData D) (ch : List (ℕ × Option ℕ)),
      RunsWithin X body
        (Main.m2bLoopProg sub xy σd (N₁, gsR, dR) (N', gsR', dR') reps O L' n₀ n) ans
        ((ch.map fun x => C x.1 x.2).sum +
          m2bLoopCost N₁ N' n O.length reps.length sIn sR Blift Bgen Bo Bgen₂) ∧
      AnsOK DV N₁ (ptsSet N₁ O) (PermData.denote N₁ σd) (GensData.denote N₁ gsP)
        (xy.1.denote N₁) (xy.2.denote N₁) ans ∧
      (∀ sGen, (∀ hs, GensData.AllValid N₁ hs →
          GensData.denote N₁ hs ≤ GensData.denote N₁ gsP →
          (X.O.run GroupOp.generate (N₁, hs)).2.1.length ≤ sGen) →
        ∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sGen) ∧
      ChildList O.length reps.length (M2bChild O.length (N' - n)) ch := by
  have hOg : MeetsContractOn DV (· = .generate) X.O := fun op x h => hO op x (Or.inr (Or.inl h))
  have hPg : ∀ x, GroupPre DV .generate x → X.Pre .generate x :=
    fun x h => hPre _ x (Or.inr (Or.inl rfl)) h
  have hOnd : O.Nodup := hc.win.nodup
  have hOlt : ∀ i ∈ O, i < N₁ := fun i hi => by have := hc.win_lt i hi; omega
  have hwv : (WinData.ofPoints N₁ O).Valid N₁ := WinData.valid_ofPoints hOnd hOlt
  set W := mlBranchCost N₁ N' n O.length sIn Blift Bgen Bo with hW
  -- the branches, and the most expensive one
  set Pb : PermData → List (ℕ × Option ℕ) → Prop := fun r ch =>
    (∃ ans : AnswerData D,
      RunsWithin X body
        (Main.mlBranch sub (N', gsR', dR') L' n₀ n
          (xy, (WinData.ofPoints N₁ O, (σd.mul r, (N₁, gsR, dR))))) ans
        ((ch.map fun x => C x.1 x.2).sum + W) ∧
      AnsOK DV N₁ (ptsSet N₁ O) (PermData.denote N₁ (σd.mul r)) (GensData.denote N₁ gsR)
        (xy.1.denote N₁) (xy.2.denote N₁) ans ∧
      ∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sR) ∧
    (ch.map Prod.fst).sum ≤ O.length ∧ (∀ x ∈ ch, M2bChild O.length (N' - n) x) ∧
      ∀ x ∈ ch, 1 ≤ x.1 with hPb
  have hbr : ∀ r ∈ reps, ∃ ch, Pb r ch := by
    intro r hr
    obtain ⟨ans, ch, hrun, hok, hg, hsum, hch, hpos⟩ := ml_branch hO hPre hsub hn₁ hR hRb hc
      hhint hs hsR' (hσ.mul (hreps r hr)) xy hBlift hBgen hBo
    exact ⟨ch, ⟨ans, hrun, hok, hg sR hsR⟩, hsum, hch, hpos⟩
  obtain ⟨ch₀, hch₀, hmax⟩ := ml_exists_max (fun ch : List (ℕ × Option ℕ) =>
    (ch.map fun x => C x.1 x.2).sum) [] Pb reps hbr
  have hgood : (ch₀.map Prod.fst).sum ≤ O.length ∧ (∀ x ∈ ch₀, M2bChild O.length (N' - n) x) ∧
      ∀ x ∈ ch₀, 1 ≤ x.1 := by
    rcases hch₀ with rfl | ⟨r, -, h⟩
    · simp
    · exact h.2
  set Cb := (ch₀.map fun x => C x.1 x.2).sum + W with hCb
  have hsubB : SubSolves X body DV
      (Main.mlBranch (var := Ty.denote) (rec := (a, b)) (D := D) sub (N', gsR', dR') L' n₀ n)
      (fun I => I.1 = xy ∧ I.2.1 = WinData.ofPoints N₁ O ∧ I.2.2.2 = (N₁, gsR, dR) ∧
        (∃ r ∈ reps, I.2.2.1 = σd.mul r) ∧ I.Valid DV) (fun _ => Cb) sR := by
    rintro ⟨xy', w', σ', G'⟩ ⟨h1, h2, h3, ⟨r, hr, h4⟩, -⟩
    change xy' = xy at h1
    change w' = WinData.ofPoints N₁ O at h2
    change G' = (N₁, gsR, dR) at h3
    change σ' = σd.mul r at h4
    subst h1 h2 h3 h4
    obtain ⟨ch, ⟨⟨ans, hrun, hok, hg⟩, -⟩, hle⟩ := hmax r hr
    refine ⟨ans, hrun.mono ?_, hok, hg⟩
    change _ ≤ Cb
    rw [hCb]
    omega
  obtain ⟨ans, hrun, hok, hg⟩ := RunsWithin.branchProg (X := X) (body := body) hOg hPg hwv hσ hR
    hRP hOP hreps (ml_isLeftCover_map hcov) hsubB hBgen₂
  refine ⟨ans, (List.replicate reps.length ch₀).flatten, ?_, hok, hg, ?_, ?_, ?_⟩
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.mkWindow _ _)
      exact hrun
    case hc =>
      rw [ml_sum_replicate]
      have e : reps.length * (24 * N₁ + Cb + sR + 45) =
          reps.length * (ch₀.map fun x => C x.1 x.2).sum +
            reps.length * (24 * N₁ + W + sR + 45) := by
        rw [hCb]
        ring
      simp only [Prim.cost, Prim.eval, m2bLoopCost, ← hW]
      omega
  · rw [ml_sum_replicate]
    exact Nat.mul_le_mul_left _ hgood.1
  · intro x hx
    obtain ⟨l, hl, hxl⟩ := List.mem_flatten.1 hx
    rw [List.eq_of_mem_replicate hl] at hxl
    exact hgood.2.1 x hxl
  · intro x hx
    obtain ⟨l, hl, hxl⟩ := List.mem_flatten.1 hx
    rw [List.eq_of_mem_replicate hl] at hxl
    exact hgood.2.2 x hxl


/-- **The block-stabilizer loop.** Let `R ≤ P` (degree `N₁`) with the cover `reps`, `O` a
`P`-invariant window of string positions, and `R'` the re-basing of `R` (`ChildRel`, degree
`N'`) with labels `L'` that are valid hint data on every nonempty `R`-invariant part of `O`.
The result is a correct answer for `(O, σ • P)`, at the cost of the children plus
`m2bLoopCost`. The children (`|reps|` copies of one branch's) are `M2bChild |O| (N' − n)`, and
their windows sum to at most `|reps| · |O|`. -/
theorem RunsWithin.m2bLoopProg (hO : MeetsContractOn DV m2bLoopOps X.O)
    (hPre : ∀ op x, m2bLoopOps op → GroupPre DV op x → X.Pre op x)
    {sub : HInstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)}
    {C : ℕ → Option ℕ → ℕ} {s : ℕ} {n₀ n N₁ N' : ℕ} {gsP gsR gsR' : GensData}
    {dR dR' : D.denote} {O : List ℕ} {L' : LabelData} {reps : List PermData} {sIn sR : ℕ}
    (hsub : HSubSolves X body DV sub (MlChild sIn n₀ n N' O.length) C s)
    (hn₁ : n ≤ N₁) (hR : GroupValid DV N₁ gsR dR)
    (hRP : GensData.denote N₁ gsR ≤ GensData.denote N₁ gsP)
    (hRb : IsInvariant (GensData.denote N₁ gsR) (baseSet n N₁))
    (hOP : IsInvariant (GensData.denote N₁ gsP) (ptsSet N₁ O))
    (hreps : ∀ r ∈ reps, PermData.Valid N₁ r)
    (hcov : IsLeftCover (GensData.denote N₁ gsP) (GensData.denote N₁ gsR)
      (fun i : Fin reps.length => PermData.denote N₁ (reps.get i)))
    (hc : ChildRel DV n N₁ gsR N' gsR' dR' (WinData.ofPoints N' O))
    (hhint : ∀ wO : WinData, (∀ i ∈ wO.1, i ∈ O) → wO.1 ≠ [] →
      IsInvariant (GensData.denote N₁ gsR) (wO.denote N₁) → HintValid n N' gsR' wO L')
    (hs : s ≤ sIn) (hsR' : gsR'.length ≤ sIn) {σd : PermData}
    (hσ : σd.Valid N₁) (xy : StrData × StrData) {Blift Bgen Bo Bgen₂ : ℕ}
    (hBlift : ∀ π' : PermData, π'.Valid n →
      X.B.call GroupOp.lift ((N₁, gsR, dR), (strWin N₁ n, π'))
        (X.O.run GroupOp.lift ((N₁, gsR, dR), (strWin N₁ n, π'))) ≤ Blift)
    (hBgen : ∀ hs : GensData, GensData.AllValid N₁ hs → hs.length ≤ sIn →
      GensData.denote N₁ hs ≤ GensData.denote N₁ gsR →
      X.B.call GroupOp.generate (N₁, hs) (X.O.run GroupOp.generate (N₁, hs)) ≤ Bgen)
    (hBo : ∀ (Hd : GroupData D.denote) (w : WinData), Hd.1 = N' → Hd.2.1.length ≤ sIn →
      GensData.denote N' Hd.2.1 ≤ GensData.denote N' gsR' → GroupPre DV .orbits (Hd, w) →
      X.B.call GroupOp.orbits (Hd, w) (X.O.run GroupOp.orbits (Hd, w)) ≤ Bo)
    (hsR : ∀ hs : GensData, GensData.AllValid N₁ hs →
      GensData.denote N₁ hs ≤ GensData.denote N₁ gsR →
      (X.O.run GroupOp.generate (N₁, hs)).2.1.length ≤ sR)
    (hBgen₂ : ∀ gs : GensData, GensData.AllValid N₁ gs → gs.length ≤ reps.length * (sR + 1) →
      GensData.denote N₁ gs ≤ GensData.denote N₁ gsP →
      X.B.call GroupOp.generate (N₁, gs) (X.O.run GroupOp.generate (N₁, gs)) ≤ Bgen₂) :
    ∃ (ans : AnswerData D) (ch : List (ℕ × Option ℕ)),
      RunsWithin X body
        (Main.m2bLoopProg sub xy σd (N₁, gsR, dR) (N', gsR', dR') reps O L' n₀ n) ans
        ((ch.map fun x => C x.1 x.2).sum +
          m2bLoopCost N₁ N' n O.length reps.length sIn sR Blift Bgen Bo Bgen₂) ∧
      AnsOK DV N₁ (ptsSet N₁ O) (PermData.denote N₁ σd) (GensData.denote N₁ gsP)
        (xy.1.denote N₁) (xy.2.denote N₁) ans ∧
      (∀ sGen, (∀ hs, GensData.AllValid N₁ hs →
          GensData.denote N₁ hs ≤ GensData.denote N₁ gsP →
          (X.O.run GroupOp.generate (N₁, hs)).2.1.length ≤ sGen) →
        ∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sGen) ∧
      ChildList O.length reps.length (M2bChild O.length (N' - n)) ch :=
  RunsWithin.m2bLoopProg_lab hO hPre (hsub.mono fun _ h => h.1) hn₁ hR hRP hRb hOP hreps hcov hc
    hhint hs hsR' hσ xy hBlift hBgen hBo hsR hBgen₂

end LoopSpec

/-! ### The M2b step -/

section StepSpec

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}

/-- The backend operations of the M2b step. -/
def m2bStepOps (op : GroupOp) : Prop :=
  op = .generate ∨ op = .stabilizer ∨ op = .orbitTransversal ∨ op = .lift ∨ op = .orbits

/-- **The charges of `m2bProg`** on block `0` of `bs` (as in `RunsWithin.m2bProg`), and the
sizes `sS`, `Lt`, `sH` of the stabilizer's results. -/
structure M2bCharges (X : Ctx (groupSig D)) (n N : ℕ) (gs : GensData) (bs : List (List ℕ))
    (Bge Bst Btr Bgt Bgen₃ sS Lt sH : ℕ) : Prop where
  ge : X.B.call GroupOp.generate (N + bs.length, extendGens N bs gs) (extGroup X.O N bs gs) ≤ Bge
  st : X.B.call GroupOp.stabilizer (extGroup X.O N bs gs, N + 0) (bsStab X.O N bs gs 0) ≤ Bst
  tr : X.B.call GroupOp.orbitTransversal (extGroup X.O N bs gs, N + 0)
    (bsTrans X.O N bs gs 0) ≤ Btr
  gt : X.B.call GroupOp.generate (N, (bsStab X.O N bs gs 0).2.1.map (PermData.truncTo N))
    (blockStabModel X.O N bs gs 0).1 ≤ Bgt
  gen3 : X.B.call GroupOp.generate
    (n + ((bs.toArray.getD 0 []).map fun p => [p]).length,
      rebaseGens n N ((bs.toArray.getD 0 []).map fun p => [p])
        (blockStabModel X.O N bs gs 0).1.2.1)
    (rebaseModel X.O n N ((bs.toArray.getD 0 []).map fun p => [p])
      (blockStabModel X.O N bs gs 0).1.2.1) ≤ Bgen₃
  sS : (bsStab X.O N bs gs 0).2.1.length ≤ sS
  Lt : (bsTrans X.O N bs gs 0).length ≤ Lt
  sH : (blockStabModel X.O N bs gs 0).1.2.1.length ≤ sH

/-- The block stabilizer of the M2b step as group data at degree `N`. -/
abbrev m2bRg (O : Oracle (groupSig D)) (N : ℕ) (gs : GensData) (bs : List (List ℕ)) :
    GroupData D.denote :=
  (N, (blockStabModel O N bs gs 0).1.2.1, (blockStabModel O N bs gs 0).1.2.2)

/-- The re-based block stabilizer of the M2b step. -/
abbrev m2bRb (O : Oracle (groupSig D)) (n N : ℕ) (gs : GensData) (bs : List (List ℕ)) :
    GroupData D.denote :=
  rebaseModel O n N ((bs.toArray.getD 0 []).map fun p => [p]) (blockStabModel O N bs gs 0).1.2.1

/-- The run of the M2b step from the runs of `m2bProg` (to any value `v`) and of the loop on
`v`'s parts. -/
theorem ml_step_run {sub : HInstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)}
    {xy : StrData × StrData} {w : WinData} {σd : PermData} {N : ℕ} {gs : GensData}
    {d : D.denote} {n₀ n : ℕ} {L : LabelData} {bs : List (List ℕ)}
    {v : (GroupData D.denote × List PermData) × (GroupData D.denote × LabelData)} {c₃ c₄ : ℕ}
    {ans : AnswerData D} (hrun3 : RunsWithin X body (Main.m2bProg n N gs bs 0 L w.1) v c₃)
    (hloop : RunsWithin X body (Main.m2bLoopProg sub xy σd v.1.1 v.2.1 v.1.2 w.1 v.2.2 n₀ n)
      ans c₄) :
    RunsWithin X body
      (Main.m2bStepProg sub ((((xy, (w, (σd, (N, gs, d)))), (n₀, (n, some L)))) : HInstData D)
        bs) ans (c₃ + c₄ + 24) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    apply RunsWithin.caseOption_some
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
    run_step (RunsWithin.prim _ _)
    run_step hrun3
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact hloop
  case hc =>
    simp only [Prim.cost]
    omega

/-- **The M2b step.** A valid hinted instance `I` (labels `L`, window `w`, degree `N`, base size
`m = N − n`) whose base action is transitive with a block system `bs` of at least two blocks,
on which the label of some window point is equidistributed. The result is a correct answer, at
the cost of the children plus `m2bStepCost`. The children are `StepChild |w| m` (a hint on the
block's at most `m/2` points, or no hint on at most `|w|/2` points), `|reps| ≤ |bs|` copies of
one branch's children (`c = |reps|`). -/
theorem RunsWithin.m2bStepProg (hO : MeetsContractOn DV m2bStepOps X.O)
    (hPre : ∀ op x, m2bStepOps op → GroupPre DV op x → X.Pre op x)
    {sub : HInstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)}
    {C : ℕ → Option ℕ → ℕ} {s : ℕ} {xy : StrData × StrData} {w : WinData} {σd : PermData}
    {N : ℕ} {gs : GensData} {d : D.denote} {n₀ n : ℕ} {L : LabelData}
    (hI : HInstValid DV ((((xy, (w, (σd, (N, gs, d)))), (n₀, (n, some L)))) : HInstData D))
    {bs : List (List ℕ)} (hbs : IsBlockList (WinData.ofPoints N (basePts n N)) bs)
    (hGb : PermutesBlocks (GensData.denote N gs) bs)
    (hΨ : IsBlockSys (baseHom (GensData.denote N gs) n hI.base_inv) (blockFam n N bs))
    (hcard : 2 ≤ (blockFam n N bs).card)
    (htrB : ∀ γ δ : Fin (N - n), ∃ g, baseHom (GensData.denote N gs) n hI.base_inv g γ = δ)
    {u₀ : Fin N} (hu₀ : u₀.val ∈ w.1) (heq : Equidist (blockFam n N bs) (labOf n N L u₀))
    {sIn : ℕ}
    (hsub : HSubSolves X body DV sub
      (fun J => SizeChild sIn ((((xy, (w, (σd, (N, gs, d)))), (n₀, (n, some L)))) : HInstData D)
        J ∧ StepChild w.1.length (N - n) (J.winSize, J.baseOpt)) C s)
    {Bge Bst Btr Bgt Bgen₃ sS Lt sH : ℕ}
    (hB : M2bCharges X n N gs bs Bge Bst Btr Bgt Bgen₃ sS Lt sH)
    {sR Blift Bgen Bo Bgen₂ : ℕ} (hs : s ≤ sIn)
    (hsR' : (m2bRb X.O n N gs bs).2.1.length ≤ sIn)
    (hBlift : ∀ π' : PermData, π'.Valid n →
      X.B.call GroupOp.lift (m2bRg X.O N gs bs, (strWin N n, π'))
        (X.O.run GroupOp.lift (m2bRg X.O N gs bs, (strWin N n, π'))) ≤ Blift)
    (hBgen : ∀ hs : GensData, GensData.AllValid N hs → hs.length ≤ sIn →
      GensData.denote N hs ≤ GensData.denote N (m2bRg X.O N gs bs).2.1 →
      X.B.call GroupOp.generate (N, hs) (X.O.run GroupOp.generate (N, hs)) ≤ Bgen)
    (hBo : ∀ (Hd : GroupData D.denote) (w' : WinData), Hd.1 = (m2bRb X.O n N gs bs).1 →
      Hd.2.1.length ≤ sIn →
      GensData.denote (m2bRb X.O n N gs bs).1 Hd.2.1 ≤
        GensData.denote (m2bRb X.O n N gs bs).1 (m2bRb X.O n N gs bs).2.1 →
      GroupPre DV .orbits (Hd, w') →
      X.B.call GroupOp.orbits (Hd, w') (X.O.run GroupOp.orbits (Hd, w')) ≤ Bo)
    (hsR : ∀ hs : GensData, GensData.AllValid N hs →
      GensData.denote N hs ≤ GensData.denote N (m2bRg X.O N gs bs).2.1 →
      (X.O.run GroupOp.generate (N, hs)).2.1.length ≤ sR)
    (hBgen₂ : ∀ gs' : GensData, GensData.AllValid N gs' →
      gs'.length ≤ (blockStabModel X.O N bs gs 0).2.length * (sR + 1) →
      GensData.denote N gs' ≤ GensData.denote N gs →
      X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ Bgen₂) :
    ∃ (ans : AnswerData D) (ch : List (ℕ × Option ℕ)),
      RunsWithin X body
        (Main.m2bStepProg sub ((((xy, (w, (σd, (N, gs, d)))), (n₀, (n, some L)))) :
          HInstData D) bs) ans
        ((ch.map fun x => C x.1 x.2).sum +
          m2bStepCost n N (bs.toArray.getD 0 []).length w.1.length L.size gs.length sS Lt sH
            sIn sR Bge Bst Btr Bgt Bgen₃ Blift Bgen Bo Bgen₂) ∧
      InstData.OK (D := D) (xy, (w, (σd, (N, gs, d)))) DV ans ∧
      (∀ sGen, (∀ hs, GensData.AllValid N hs → GensData.denote N hs ≤ GensData.denote N gs →
          (X.O.run GroupOp.generate (N, hs)).2.1.length ≤ sGen) →
        ∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sGen) ∧
      ChildList w.1.length (blockStabModel X.O N bs gs 0).2.length
        (StepChild w.1.length (N - n)) ch ∧
      (blockStabModel X.O N bs gs 0).2.length ≤ bs.length := by
  have hn : n ≤ N := hI.le
  have hbase : IsInvariant (GensData.denote N gs) (baseSet n N) := hI.base_inv
  have hv : InstData.Valid (D := D) (xy, (w, (σd, (N, gs, d)))) DV := hI.valid
  have hgs : GensData.AllValid N gs := hv.group.1
  obtain ⟨hL, htrW⟩ := hI.hint L rfl
  have hw : w.Valid N := hv.win
  have hinv : IsInvariant (GensData.denote N gs) (w.denote N) := hv.invariant
  have hOn : ∀ i ∈ w.1, i < n := hI.win_lt
  have hwbv : (WinData.ofPoints N (basePts n N)).Valid N :=
    WinData.valid_ofPoints (basePts_nodup _ _) fun i hi => (mem_basePts.1 hi).2
  have hwbn : ∀ i ∈ (WinData.ofPoints N (basePts n N)).1, n ≤ i :=
    fun i hi => (mem_basePts.1 hi).1
  have hbs0 : 0 < bs.length := by
    have h1 := List.toFinset_card_le (bs.map (baseBlockSet n N))
    rw [List.length_map] at h1
    simp only [blockFam] at hcard
    omega
  have hT1 : ∀ u ∈ w.1, (L.getD u []).length ≤ N - n := fun u hu =>
    mf_length_le_of_nodup (hL.lab_nodup u hu) (hL.lab_lt u hu)
  have hOb : MeetsContractOn DV blockStabOps X.O := fun op x h => hO op x (by
    rcases h with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h)))
  have hPb : ∀ op x, blockStabOps op → GroupPre DV op x → X.Pre op x := fun op x h hx =>
    hPre op x (by
      rcases h with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))) hx
  have hOl : MeetsContractOn DV m2bLoopOps X.O := fun op x h => hO op x (by
    rcases h with h | h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inr h))))
  have hPl : ∀ op x, m2bLoopOps op → GroupPre DV op x → X.Pre op x := fun op x h hx =>
    hPre op x (by
      rcases h with h | h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))) hx
  obtain ⟨hrun3, hHN, hHv, hHden, hrv, hcov, hrl, hdeg3, hval3, hHb, hGb', hw', hden3⟩ :=
    RunsWithin.m2bProg (X := X) (body := body) (DV := DV) hOb hPb hn hbase hwbv hwbn hbs hGb
      hgs hbs0 hB.ge hB.st hB.tr hB.gt hB.gen3 L w.1 hT1
  -- sizes
  set k := (bs.toArray.getD 0 []).length with hk
  have hflat : bs.flatten.length = N - n := by
    rw [hbs.1.length_eq, WinData.ofPoints_fst, length_basePts]
  have hkle : k ≤ N - n := by
    rw [← hflat, hk, mr_getD_toArray', List.getD_eq_getElem _ _ hbs0, List.length_flatten]
    exact List.le_sum_of_mem (List.mem_map.2 ⟨_, List.getElem_mem hbs0, rfl⟩)
  have hbslen : bs.length ≤ N - n := by
    rw [← hflat, List.length_flatten]
    have : (bs.map fun _ => 1).sum ≤ (bs.map List.length).sum :=
      List.sum_le_sum fun b hb => List.length_pos_of_ne_nil (hbs.2 b hb)
    simpa using this
  have hcardk : 2 * k ≤ N - n := m2b_card hbs hΨ htrB hcard hbs0
  have hdegR : (m2bRb X.O n N gs bs).1 = n + k := hdeg3
  -- the block stabilizer and its re-basing
  have hRG : GensData.denote N (blockStabModel X.O N bs gs 0).1.2.1 ≤ GensData.denote N gs := by
    rw [hHden]
    exact Subgroup.map_subtype_le _
  have hT : Transitive ↥(GensData.denote N gs) (winFinset N w) := by
    intro u hu v hv
    rw [mem_winFinset] at hu hv
    obtain ⟨g, hg, e⟩ := htrW u hu v hv
    exact ⟨⟨g, hg⟩, e⟩
  have hhint : ∀ wO : WinData, (∀ i ∈ wO.1, i ∈ w.1) → wO.1 ≠ [] →
      IsInvariant (GensData.denote N (blockStabModel X.O N bs gs 0).1.2.1) (wO.denote N) →
      HintValid n (m2bRb X.O n N gs bs).1 (m2bRb X.O n N gs bs).2.1 wO
        (m2bLabels n N bs 0 L w.1) := by
    intro wO hwO hwO0 hOinv
    rw [hdegR]
    exact m2b_hintValid hL hgs hw hinv hT htrB hbs hΨ hu₀ heq hbs0 hHden hHb hGb' hw' hval3.1
      hden3 hwO hwO0 hOinv
  obtain ⟨hwv', hinv', -, hfa', hiso'⟩ := dv_rebase_facts hn hHb hw' mr_isBlockList_singletons
    hGb' (fun g hg => hI.faithful g (hRG hg)) hden3 hOn hw.nodup (fun g hg => hinv g (hRG hg))
  rw [List.length_map] at hwv' hinv' hfa' hiso'
  have hwne : w.1 ≠ [] := List.ne_nil_of_mem hu₀
  have hLw := hhint w (fun i hi => hi) hwne (fun g hg => hinv g (hRG hg))
  have hc : ChildRel DV n N (blockStabModel X.O N bs gs 0).1.2.1 (m2bRb X.O n N gs bs).1
      (m2bRb X.O n N gs bs).2.1 (m2bRb X.O n N gs bs).2.2
      (WinData.ofPoints (m2bRb X.O n N gs bs).1 w.1) := by
    refine ⟨?_, hLw.le, hLw.base_inv, ?_, hOn, ?_, ?_, ?_⟩
    · rw [hdegR]; exact hval3
    · rw [hdegR]; exact hwv'
    · rw [hdegR]; exact hinv'
    · rw [hdegR]; exact hfa'
    · rw [hdegR]; exact hiso'
  -- the loop
  have hsub' : HSubSolves X body DV sub
      (MlChildL sIn n₀ n (m2bRb X.O n N gs bs).1 w.1.length (m2bLabels n N bs 0 L w.1)) C s := by
    refine hsub.mono fun J hJ => ?_
    obtain ⟨⟨h1, h2, h3, h5, h4⟩, hJL⟩ := hJ
    have hJd : J.inst.degree = n + k := h3.trans hdegR
    refine ⟨⟨h1, h2.le, ?_, h5, fun hI' => hI'.of_le h1 h2.le fun L₁ hL₁ => ⟨L, rfl, ?_, ?_⟩⟩,
      M2bChild.stepChild h4 le_rfl (by omega)⟩
    · show J.inst.degree ≤ max N (2 * n)
      rw [hJd]
      exact le_max_of_le_left (by omega)
    · show J.inst.degree - J.n ≤ N - n
      rw [hJd, h2]
      omega
    · rw [hJL L₁ hL₁]
      exact labLen_m2bLabels_le hw.nodup n N bs 0 L
  obtain ⟨ans, ch, hloop, hok, hg, hch⟩ := RunsWithin.m2bLoopProg_lab (X := X) (body := body)
    (gsP := gs) hOl hPl hsub' hn hHv hRG hHb hinv hrv hcov hc hhint hs hsR' hv.rep xy hBlift
    hBgen hBo hsR hBgen₂
  have e1 : (blockStabModel X.O N bs gs 0).1 = m2bRg X.O N gs bs := Prod.ext hHN rfl
  have hloop' : RunsWithin X body
      (Main.m2bLoopProg sub xy σd (blockStabModel X.O N bs gs 0).1 (m2bRb X.O n N gs bs)
        (blockStabModel X.O N bs gs 0).2 w.1 (m2bLabels n N bs 0 L w.1) n₀ n) ans
      ((ch.map fun x => C x.1 x.2).sum +
        m2bLoopCost N (m2bRb X.O n N gs bs).1 n w.1.length
          (blockStabModel X.O N bs gs 0).2.length sIn sR Blift Bgen Bo Bgen₂) := by
    rw [e1]
    exact hloop
  refine ⟨ans, ch, ?_, hok, hg, ⟨hch.sum_le, fun x hx =>
    M2bChild.stepChild (hch.pred x hx) le_rfl (by omega), hch.pos⟩, by omega⟩
  refine (ml_step_run (v := m2bModel X.O n N gs bs 0 L w.1) hrun3 hloop').mono ?_
  have h3 := m2bCost_mono (n := n) (Bge := Bge) (Bst := Bst) (Btr := Btr) (Bgt := Bgt)
    (B := Bgen₃) (wl := w.1.length) (Ls := L.size) (Ls' := L.size) (le_refl N)
    (show bs.flatten.length ≤ N - n by omega) hbslen (le_refl gs.length) hB.sS hB.Lt
    (le_refl k) hB.sH (show N - n ≤ N - n from le_rfl) le_rfl
  have hl : m2bLoopCost N (m2bRb X.O n N gs bs).1 n w.1.length
      (blockStabModel X.O N bs gs 0).2.length sIn sR Blift Bgen Bo Bgen₂ ≤
      m2bLoopCost N (n + k) n w.1.length (N - n) sIn sR Blift Bgen Bo Bgen₂ := by
    rw [hdegR]
    simp only [m2bLoopCost]
    have h4 : (blockStabModel X.O N bs gs 0).2.length *
          (24 * N + mlBranchCost N (n + k) n w.1.length sIn Blift Bgen Bo + sR + 45) ≤
        (N - n) * (24 * N + mlBranchCost N (n + k) n w.1.length sIn Blift Bgen Bo + sR + 45) :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  simp only [m2bStepCost]
  omega

end StepSpec

/-! ### Well-formedness -/

section Wf

variable {D : Ty} {rec : Ty × Ty} {var₁ var₂ : Ty → Type} {r : Bool} {Γ : WfCtx var₁ var₂}

/-- Membership in a context extended by bound variables. -/
local macro "ml_mem" : tactic =>
  `(tactic| repeat (first | exact List.mem_cons_self | assumption | apply List.mem_cons_of_mem))

theorem wf_mlHandle {sub₁ : var₁ (hinstTy D) → Prog (groupSig D) rec var₁ (Ty.answer D)}
    {sub₂ : var₂ (hinstTy D) → Prog (groupSig D) rec var₂ (Ty.answer D)}
    (hsub : WfFun r Γ sub₁ sub₂) {L₁ : var₁ (.array (.list .nat))}
    {L₂ : var₂ (.array (.list .nat))} {n₀₁ n₁ : var₁ .nat} {n₀₂ n₂ : var₂ .nat}
    {xy₁ : var₁ Ty.strs} {xy₂ : var₂ Ty.strs} {c₁ : var₁ (Ty.coset D)} {c₂ : var₂ (Ty.coset D)}
    {O₁ : var₁ (.list .nat)} {O₂ : var₂ (.list .nat)} (hL : ⟨.array (.list .nat), L₁, L₂⟩ ∈ Γ)
    (hn₀ : ⟨.nat, n₀₁, n₀₂⟩ ∈ Γ) (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (hxy : ⟨Ty.strs, xy₁, xy₂⟩ ∈ Γ)
    (hc : ⟨Ty.coset D, c₁, c₂⟩ ∈ Γ) (hO : ⟨.list .nat, O₁, O₂⟩ ∈ Γ) :
    Prog.Wf r Γ (mlHandle sub₁ L₁ n₀₁ n₁ xy₁ c₁ O₁) (mlHandle sub₂ L₂ n₀₂ n₂ xy₂ c₂ O₂) := by
  unfold mlHandle mkWindow mkHInstProg mapList
  prog_wf
  all_goals first
    | exact wf_ncBProg (by ml_mem) (by ml_mem) (by ml_mem) (by ml_mem)
    | exact hsub _ (fun y hy => by simp [hy]) _ _ (List.Mem.head _)

theorem wf_mlInner {sub₁ : var₁ (hinstTy D) → Prog (groupSig D) rec var₁ (Ty.answer D)}
    {sub₂ : var₂ (hinstTy D) → Prog (groupSig D) rec var₂ (Ty.answer D)}
    (hsub : WfFun r Γ sub₁ sub₂) {L₁ : var₁ (.array (.list .nat))}
    {L₂ : var₂ (.array (.list .nat))} {n₀₁ n₁ : var₁ .nat} {n₀₂ n₂ : var₂ .nat}
    (hL : ⟨.array (.list .nat), L₁, L₂⟩ ∈ Γ) (hn₀ : ⟨.nat, n₀₁, n₀₂⟩ ∈ Γ)
    (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) :
    WfFun r Γ (mlInner sub₁ L₁ n₀₁ n₁) (mlInner sub₂ L₂ n₀₂ n₂) := by
  intro Γ' hΓ J₁ J₂ hJ
  unfold mlInner
  refine .bind (.prim _ (.cons hJ .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by ml_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by ml_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by ml_mem) .nil)) fun _ _ => ?_
  have hL' := hΓ hL
  have hn₀' := hΓ hn₀
  have hn' := hΓ hn
  refine wf_dynSeqProg (fun Γ'' hΓ'' x₁ x₂ c₁ c₂ o₁ o₂ hx hc ho => ?_) (by ml_mem) (by ml_mem)
    (List.Mem.head _)
  refine wf_mlHandle (fun Γ₃ h₃ => hsub Γ₃ fun y hy => h₃ (hΓ'' ?_)) (hΓ'' (by ml_mem))
    (hΓ'' (by ml_mem)) (hΓ'' (by ml_mem)) hx hc ho
  have := hΓ hy
  ml_mem

theorem wf_mlBranch {sub₁ : var₁ (hinstTy D) → Prog (groupSig D) rec var₁ (Ty.answer D)}
    {sub₂ : var₂ (hinstTy D) → Prog (groupSig D) rec var₂ (Ty.answer D)}
    (hsub : WfFun r Γ sub₁ sub₂) {R'₁ : var₁ (Ty.group D)} {R'₂ : var₂ (Ty.group D)}
    {L₁ : var₁ (.array (.list .nat))} {L₂ : var₂ (.array (.list .nat))} {n₀₁ n₁ : var₁ .nat}
    {n₀₂ n₂ : var₂ .nat} (hR' : ⟨Ty.group D, R'₁, R'₂⟩ ∈ Γ)
    (hL : ⟨.array (.list .nat), L₁, L₂⟩ ∈ Γ) (hn₀ : ⟨.nat, n₀₁, n₀₂⟩ ∈ Γ)
    (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) :
    WfFun r Γ (mlBranch sub₁ R'₁ L₁ n₀₁ n₁) (mlBranch sub₂ R'₂ L₂ n₀₂ n₂) := by
  intro Γ' hΓ I₁ I₂ hI
  have hR'' := hΓ hR'
  have hL' := hΓ hL
  have hn₀' := hΓ hn₀
  have hn' := hΓ hn
  unfold mlBranch
  refine .bind (.prim _ (.cons hI .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by ml_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by ml_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by ml_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by ml_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by ml_mem) .nil)) fun _ _ => ?_
  refine .bind (wf_mkWindow (by ml_mem) (List.Mem.head _)) fun _ _ => ?_
  refine .bind (.prim _ .nil) fun _ _ => ?_
  refine wf_viaChildProg (wf_mlInner (fun Γ₃ h₃ => hsub Γ₃ fun y hy => h₃ ?_) (by ml_mem)
    (by ml_mem) (by ml_mem)) (by ml_mem) (by ml_mem) (by ml_mem) (by ml_mem) (by ml_mem)
    (by ml_mem) (by ml_mem) (List.Mem.head _)
  have := hΓ hy
  ml_mem

theorem wf_m2bLoopProg {sub₁ : var₁ (hinstTy D) → Prog (groupSig D) rec var₁ (Ty.answer D)}
    {sub₂ : var₂ (hinstTy D) → Prog (groupSig D) rec var₂ (Ty.answer D)}
    (hsub : WfFun r Γ sub₁ sub₂) {xy₁ : var₁ Ty.strs} {xy₂ : var₂ Ty.strs}
    {σ₁ : var₁ Ty.perm} {σ₂ : var₂ Ty.perm} {R₁ R'₁ : var₁ (Ty.group D)}
    {R₂ R'₂ : var₂ (Ty.group D)} {reps₁ : var₁ Ty.gens} {reps₂ : var₂ Ty.gens}
    {O₁ : var₁ (.list .nat)} {O₂ : var₂ (.list .nat)} {L₁ : var₁ (.array (.list .nat))}
    {L₂ : var₂ (.array (.list .nat))} {n₀₁ n₁ : var₁ .nat} {n₀₂ n₂ : var₂ .nat}
    (hxy : ⟨Ty.strs, xy₁, xy₂⟩ ∈ Γ) (hσ : ⟨Ty.perm, σ₁, σ₂⟩ ∈ Γ)
    (hR : ⟨Ty.group D, R₁, R₂⟩ ∈ Γ) (hR' : ⟨Ty.group D, R'₁, R'₂⟩ ∈ Γ)
    (hreps : ⟨Ty.gens, reps₁, reps₂⟩ ∈ Γ) (hO : ⟨.list .nat, O₁, O₂⟩ ∈ Γ)
    (hL : ⟨.array (.list .nat), L₁, L₂⟩ ∈ Γ) (hn₀ : ⟨.nat, n₀₁, n₀₂⟩ ∈ Γ)
    (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) :
    Prog.Wf r Γ (m2bLoopProg sub₁ xy₁ σ₁ R₁ R'₁ reps₁ O₁ L₁ n₀₁ n₁)
      (m2bLoopProg sub₂ xy₂ σ₂ R₂ R'₂ reps₂ O₂ L₂ n₀₂ n₂) := by
  unfold m2bLoopProg
  refine .bind (.prim _ (.cons hR .nil)) fun _ _ => ?_
  refine .bind (wf_mkWindow (List.Mem.head _) (by ml_mem)) fun _ _ => ?_
  refine wf_branchProg (wf_mlBranch (fun Γ₃ h₃ => hsub Γ₃ fun y hy => h₃ (by ml_mem))
    (by ml_mem) (by ml_mem) (by ml_mem) (by ml_mem)) (by ml_mem) (List.Mem.head _) (by ml_mem)
    (by ml_mem) (by ml_mem)

theorem wf_m2bStepProg {sub₁ : var₁ (hinstTy D) → Prog (groupSig D) rec var₁ (Ty.answer D)}
    {sub₂ : var₂ (hinstTy D) → Prog (groupSig D) rec var₂ (Ty.answer D)}
    (hsub : WfFun r Γ sub₁ sub₂) {I₁ : var₁ (hinstTy D)} {I₂ : var₂ (hinstTy D)}
    {bs₁ : var₁ (.list (.list .nat))} {bs₂ : var₂ (.list (.list .nat))}
    (hI : ⟨hinstTy D, I₁, I₂⟩ ∈ Γ) (hbs : ⟨.list (.list .nat), bs₁, bs₂⟩ ∈ Γ) :
    Prog.Wf r Γ (m2bStepProg sub₁ I₁ bs₁) (m2bStepProg sub₂ I₂ bs₂) := by
  unfold m2bStepProg
  refine .bind (.prim _ (.cons hI .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by ml_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by ml_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by ml_mem) .nil)) fun _ _ => ?_
  refine .caseOption (List.Mem.head _) (.prim _ .nil) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by ml_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by ml_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by ml_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by ml_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by ml_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by ml_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ .nil) fun _ _ => ?_
  refine .bind (wf_m2bProg (by ml_mem) (by ml_mem) (by ml_mem) (by ml_mem) (List.Mem.head _)
    (by ml_mem) (by ml_mem)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by ml_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by ml_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by ml_mem) .nil)) fun _ _ => ?_
  exact wf_m2bLoopProg (fun Γ₃ h₃ => hsub Γ₃ fun y hy => h₃ (by ml_mem)) (by ml_mem)
    (by ml_mem) (by ml_mem) (by ml_mem) (by ml_mem) (by ml_mem) (List.Mem.head _) (by ml_mem)
    (by ml_mem)

end Wf

end GraphIso.Main
