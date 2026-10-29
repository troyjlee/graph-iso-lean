module

public import GraphIso.Main.RD
public import GraphIso.Solver.Entry

/-!
# The mini procedure: a recursion closed by induction

Stage 14j-5b, item 3 (`PLAN-14.md` §14.7). The base case, the chain rule, M0 and M3 composed
into one recursive procedure, with `.recur` as the hinted sub-solver of every step. Its
correctness and cost follow by strong induction on an explicit rank of the measure, from the
specs of stage 14j-2 as repaired in stage 14j-5a, with the Schreier–Sims backend. The
sub-solver hypothesis of each step is discharged by the induction hypothesis; there is no other
assumption. It shows that the repaired contracts close: one generator bound `sG = NB²` is kept
by every child (`SizeChild.closed`).

* `miniBody`: the base-case test; with a hint, M3; without one, the chain rule on at least two
  orbits, else M0.
* `miniEntry`: one charged `generate` on the input generators, then the recursion on the
  instance without a hint, with `n₀ = n = N`.
* `MiniDom`: the domain of the induction (`n₀`, at most `nB` string positions, degree at most
  `NB`, at most `NB²` generators).
* `miniRk`, `miniC`: the rank `p (NB + 2) + b` of a measure `(p, b)`, and the cost bound
  `miniC A W r`, with `A = NB! · nB` (every step has at most `NB! · |W|` children) and `W`
  bounding every step's work on the domain.
* `mini_spec`: correctness and cost on the domain; `miniSolve_ss`: the entry on every valid
  instance.

The cost is exponential in the rank (M3 branches over up to `NB!` cosets): this is a correct
solver, not the quasipolynomial bound of stage 14j-6.
-/

@[expose] public section

namespace GraphIso.Main

open Equiv Cost GraphIso GraphIso.Programs GraphIso.Toolkit GraphIso.Recursion

/-! ### Programs -/

section Programs

variable {D : Ty} {var : Ty → Type}

/-- **The mini procedure.** The base case when the group fixes the window; with a hint, M3;
without one, the chain rule when the window has at least two orbits, else M0. Every step's
sub-solver is the recursive call. -/
def miniBody (D : Ty) : Proc (groupSig D) (hinstTy D) (Ty.answer D) := fun _ I =>
  .bind (fixedTestProg I) fun f =>
  .ite f (fixedStepProg I)
    (.bind (.op1 .snd I) fun r₁ => .bind (.op1 .snd r₁) fun r₂ =>
     .bind (.op1 .snd r₂) fun lab =>
     .caseOption lab
      (.bind (winOrbitsProg I) fun os => .bind (.op1 .length os) fun k =>
       .bind (.op0 (.natLit 1)) fun one => .bind (.op2 .natLt one k) fun many =>
       .ite many (chainProg (fun J => .recur J) I os) (m0StepProg (fun J => .recur J) I))
      (fun _ => m3Prog (fun J => .recur J) I))

/-- **The entry**: generate the group (normalizing the generators), then solve the instance
without a hint, with `n₀ = n = N`. -/
def miniEntry (D : Ty) : (var : Ty → Type) → var Solver.Ty.input →
    Prog (groupSig D) (hinstTy D, Ty.answer D) var (Ty.answer D) := fun _ inp =>
  .bind (.op1 .fst inp) fun xy => .bind (.op1 .snd inp) fun r₁ =>
  .bind (.op1 .fst r₁) fun w => .bind (.op1 .snd r₁) fun r₂ =>
  .bind (.op1 .fst r₂) fun σ => .bind (.op1 .snd r₂) fun ng =>
  .bind (.op1 .fst ng) fun N =>
  .bind (Prog.call (S := groupSig D) GroupOp.generate ng) fun G =>
  .bind (.op2 .pair σ G) fun c => .bind (.op2 .pair w c) fun wc =>
  .bind (.op2 .pair xy wc) fun J => .bind (.op0 .none) fun nl =>
  .bind (.op2 .pair N nl) fun p₁ => .bind (.op2 .pair N p₁) fun p₂ =>
  .bind (.op2 .pair J p₂) fun I => .recur I

end Programs

/-! ### Well-formedness -/

section Wf

variable {D : Ty}

theorem wf_recurFun {var₁ var₂ : Ty → Type} {Γ : WfCtx var₁ var₂} :
    WfFun (S := groupSig D) (rec := (hinstTy D, Ty.answer D)) true Γ
      (fun J => Prog.recur J) (fun J => Prog.recur J) :=
  fun _ _ _ _ hx => .recur rfl hx

/-- The mini procedure is well formed. -/
theorem miniBody_wf : (miniBody D).Wf := by
  intro var₁ var₂ x₁ x₂
  unfold miniBody
  refine .bind (wf_fixedTestProg (List.Mem.head _)) fun _ _ => ?_
  refine .ite (List.Mem.head _) (wf_fixedStepProg (by simp)) ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .caseOption (List.Mem.head _) ?_ fun _ _ => wf_m3Prog wf_recurFun (by simp)
  refine .bind (wf_winOrbitsProg (by simp)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ .nil) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) (.cons (by simp) .nil))) fun _ _ => ?_
  exact .ite (List.Mem.head _) (wf_chainProg wf_recurFun (by simp) (by simp))
    (wf_m0StepProg wf_recurFun (by simp))

theorem miniEntry_wf {var₁ var₂ : Ty → Type} (x₁ : var₁ Solver.Ty.input)
    (x₂ : var₂ Solver.Ty.input) :
    Prog.Wf true [⟨Solver.Ty.input, x₁, x₂⟩] (miniEntry D var₁ x₁) (miniEntry D var₂ x₂) := by
  unfold miniEntry
  prog_wf

end Wf

/-! ### Facts on the data -/

section Facts

variable {D : Ty} {DV : ℕ → GensData → D.denote → Prop}

/-- **A hinted instance has a nonempty base**: its labels are not constant, and they are
subsets of the base. -/
theorem HInstValid.base_pos {I : HInstData D} {L : LabelData} (h : HInstValid DV I)
    (hL : I.lab = some L) : 1 ≤ I.inst.degree - I.n := by
  obtain ⟨hv, -⟩ := h.hint L hL
  obtain ⟨i, hi, j, hj, hne⟩ := hv.nonconst
  by_contra h0
  have e : ∀ k ∈ I.inst.2.1.1, L.getD k [] = [] := fun k hk =>
    List.eq_nil_iff_forall_not_mem.2 fun x hx => by have := hv.lab_lt k hk x hx; omega
  exact hne (by rw [e i hi, e j hj])

/-- The window of a hinted instance has at most `n` points (they are distinct string
positions). -/
theorem HInstValid.winSize_le {I : HInstData D} (h : HInstValid DV I) : I.winSize ≤ I.n :=
  mf_length_le_of_nodup h.valid.win.nodup h.win_lt

/-- **The case of M0**: an instance not fixed pointwise, with at most one orbit on its window,
is transitive on a window of at least two points. -/
theorem mini_m0_case {N : ℕ} {gs : GensData} {w : WinData} {os : List (List ℕ)}
    (hinv : IsInvariant (GensData.denote N gs) (w.denote N))
    (hfix : ¬ FixesPointwise (GensData.denote N gs) (w.denote N))
    (hos : IsOrbitPartition (GensData.denote N gs) w os) (h1 : os.length ≤ 1) :
    IsTransOn (GensData.denote N gs) (w.denote N) ∧ 2 ≤ w.1.length := by
  have hne : w.1 ≠ [] := by
    intro h
    exact hfix fun g _ u hu => absurd (show u.val ∈ w.1 from hu) (by rw [h]; simp)
  obtain ⟨o, rfl⟩ : ∃ o, os = [o] := by
    rcases os with _ | ⟨o, _ | ⟨o', rest⟩⟩
    · exact absurd rfl (hos.ne_nil hne)
    · exact ⟨o, rfl⟩
    · simp at h1
  refine ⟨fun u hu v hv => ?_, ?_⟩
  · obtain ⟨hi, hj, g, hg, hgu⟩ := ((hos.transitive_of_singleton hu) v.val).1 hv
    exact ⟨g, hg, by simpa using hgu⟩
  · by_contra hlt
    refine hfix fun g hg u hu => Fin.ext ?_
    have hgu : (g u).val ∈ w.1 := hinv g hg u hu
    have hu' : u.val ∈ w.1 := hu
    rcases hl : w.1 with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · exact absurd hl hne
    · rw [hl, List.mem_singleton] at hgu hu'
      rw [hgu, hu']
    · rw [hl] at hlt
      simp at hlt

end Facts

/-! ### Schreier–Sims generator counts -/

section SimsCounts

open Sims

/-- **A re-based group has at most `(n + k)²` generators** with Schreier–Sims: the re-based
generators are valid (`allValid_rebaseGens`), and `generate` returns at most `M²` generators
at degree `M` on valid inputs. -/
theorem ss_rebase_gens_le {n N : ℕ} {w : WinData} {bs : List (List ℕ)} {gs : GensData}
    (hn : n ≤ N) (hbase : IsInvariant (GensData.denote N gs) (baseSet n N)) (hw : w.Valid N)
    (hbs : IsBlockList w bs) (hGb : PermutesBlocks (GensData.denote N gs) bs)
    (hgs : GensData.AllValid N gs) :
    (rebaseModel ssOracle n N bs gs).2.1.length ≤ (n + bs.length) * (n + bs.length) := by
  change (generateModel (n + bs.length) (rebaseGens n N bs gs)).length ≤ _
  exact (generateModel_spec (allValid_rebaseGens hn hbase hw hbs hGb hgs)).2.2

/-- **M0's child group** has at most `(2n)²` generators with Schreier–Sims: it is re-based onto
`k ≤ |W| ≤ n` maximal blocks, at degree `n + k ≤ 2n`. -/
theorem ss_m0_gens_le {xy : StrData × StrData} {w : WinData} {σd : PermData} {N : ℕ}
    {gs : GensData} {n₀ n : ℕ}
    (hI : HInstValid ssDV (((xy, w, σd, N, gs, ()), n₀, n, none) : HInstData Ty.unit))
    (htr : IsTransOn (GensData.denote N gs) (w.denote N)) (h2 : 2 ≤ w.1.length) :
    n + (Luks.maxBlocks N gs w.1).length ≤ 2 * n ∧
      (rebaseModel ssOracle n N (Luks.maxBlocks N gs w.1) gs).2.1.length ≤ (2 * n) * (2 * n) := by
  have hw : w.Valid N := hI.valid.win
  have hgs : GensData.AllValid N gs := hI.valid.group.1
  have hinv : IsInvariant (GensData.denote N gs) (w.denote N) := hI.valid.invariant
  obtain ⟨u, rest, hpts⟩ : ∃ u rest, w.1 = u :: rest := by
    rcases h : w.1 with _ | ⟨u, rest⟩
    · rw [h] at h2; simp at h2
    · exact ⟨u, rest, rfl⟩
  have hrest : rest ≠ [] := by
    intro h
    rw [hpts, h] at h2
    simp at h2
  have hu : u ∈ w.1 := hpts ▸ List.mem_cons_self
  have htr' : ∀ j, j ∈ w.1 ↔ SameOrbit (GensData.denote N gs) u j := by
    intro j
    constructor
    · intro hj
      obtain ⟨g, hg, hgu⟩ := htr ⟨u, hw.lt u hu⟩ hu ⟨j, hw.lt j hj⟩ hj
      exact ⟨hw.lt u hu, hw.lt j hj, g, hg, hgu⟩
    · rintro ⟨hu', hj', g, hg, hgu⟩
      have := hinv g hg ⟨u, hu'⟩ hu
      rw [hgu] at this
      exact this
  obtain ⟨hbs, hGb, -, -, -⟩ := Luks.maxBlocks_spec hw hgs hinv hpts hrest htr'
  have hk : (Luks.maxBlocks N gs w.1).length ≤ w.1.length := mf_length_le_of_isBlockList hbs
  have hwn := sh_length_le hI
  have h' : n + (Luks.maxBlocks N gs w.1).length ≤ 2 * n := by omega
  exact ⟨h', (ss_rebase_gens_le hI.le hI.base_inv hw hbs hGb hgs).trans (Nat.mul_le_mul h' h')⟩

/-- **The kernel of the base action** has at most `N²` generators with Schreier–Sims. -/
theorem ss_ker_gens_le {n N : ℕ} {gs : GensData} (hgs : GensData.AllValid N gs) :
    (kerModel ssOracle n ((N, gs, ()) : GroupData Ty.unit.denote)).2.1.length ≤ N * N := by
  change (kernelModel N gs (baseWin n N)).length ≤ N * N
  exact (kernelModel_spec hgs (baseWin_valid n N)).2.2

end SimsCounts

/-! ### The domain, the rank and the cost bound -/

section Rank

open Sims

/-- **The domain of the induction**: the original size `n₀`, at most `nB` string positions,
degree at most `NB`, and at most `NB²` generators. -/
structure MiniDom (n₀ nB NB : ℕ) (I : HInstData Ty.unit) : Prop where
  n₀ : I.n₀ = n₀
  n_le : I.n ≤ nB
  degree_le : I.inst.degree ≤ NB
  gens_le : I.inst.2.2.2.gens.length ≤ NB * NB

/-- **The rank** of a measure `(p, b)` (window size, and the base or `2p + 1` without a hint):
`p (NB + 2) + b`. On the domain every base is at most `NB + 1`, so a smaller measure has a
smaller rank (`miniRk_lt`). -/
def miniRk (NB p : ℕ) (bo : Option ℕ) : ℕ := p * (NB + 2) + bo.getD (2 * p + 1)

theorem miniRk_lt {NB p q b : ℕ} {bo : Option ℕ} (h : MeasLt (p, bo.getD (2 * p + 1)) (q, b))
    (hb : bo.getD (2 * p + 1) ≤ NB + 1) : miniRk NB p bo < q * (NB + 2) + b := by
  unfold miniRk
  rcases h with h | ⟨h1, h2⟩
  · have : (p + 1) * (NB + 2) ≤ q * (NB + 2) := Nat.mul_le_mul_right _ h
    rw [Nat.succ_mul] at this
    omega
  · change p = q at h1
    subst h1
    change bo.getD (2 * p + 1) < b at h2
    omega

/-- **The cost bound** at rank `r`: `miniC A W 0 = W` and
`miniC A W (r + 1) = A (1 + miniC A W r) + W`. -/
def miniC (A W : ℕ) : ℕ → ℕ
  | 0 => W
  | r + 1 => A * (1 + miniC A W r) + W

theorem le_miniC (A W r : ℕ) : W ≤ miniC A W r := by
  cases r <;> simp [miniC]

theorem miniC_mono (A W : ℕ) : Monotone (miniC A W) := by
  refine monotone_nat_of_le_succ fun r => ?_
  induction r with
  | zero => simp only [miniC]; omega
  | succ r ih =>
    change A * (1 + miniC A W r) + W ≤ A * (1 + miniC A W (r + 1)) + W
    gcongr

/-- The children's costs: at most `1 + miniC A W r` each, below rank `r + 1`. -/
theorem mini_sum_le {A W NB r : ℕ} {ch : List (ℕ × Option ℕ)}
    (h : ∀ x ∈ ch, miniRk NB x.1 x.2 < r + 1) :
    (ch.map fun x => 1 + miniC A W (miniRk NB x.1 x.2)).sum ≤ ch.length * (1 + miniC A W r) := by
  have := List.sum_le_length_nsmul (ch.map fun x => 1 + miniC A W (miniRk NB x.1 x.2))
    (1 + miniC A W r) (by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
      exact Nat.add_le_add_left (miniC_mono A W (Nat.lt_succ_iff.1 (h x hx))) 1)
  simpa using this

/-- The base bound of a child predicate, from the parent's window size `n` and base `m`. -/
theorem StepChild.getD_le {n m : ℕ} {x : ℕ × Option ℕ} (h : StepChild n m x) :
    x.2.getD (2 * x.1 + 1) ≤ max m (n + 1) := by
  obtain ⟨-, ⟨m', he, hm'⟩ | ⟨he, h2⟩⟩ := h
  · rw [he]; simp only [Option.getD_some]; omega
  · rw [he]; simp only [Option.getD_none]; omega

theorem FreeChild.getD_le {n m : ℕ} {x : ℕ × Option ℕ} (h : FreeChild n m x) :
    x.2.getD (2 * x.1 + 1) ≤ max m (n + 1) := by
  obtain ⟨-, ⟨m', he, hm', -⟩ | ⟨he, h2⟩⟩ := h
  · rw [he]; simp only [Option.getD_some]; omega
  · rw [he]; simp only [Option.getD_none]; omega

theorem ChainChild.getD_le {n : ℕ} {x : ℕ × Option ℕ} (h : ChainChild n x) :
    x.2.getD (2 * x.1 + 1) ≤ 2 * n + 1 := by
  obtain ⟨he, h1⟩ := h
  rw [he]; simp only [Option.getD_none]; omega

/-- **The rank of a valid instance is positive**: its base is positive with a hint, and is
`2p + 1` without one. -/
theorem mini_rk_pos {NB : ℕ} {I : HInstData Ty.unit} (h : HInstValid ssDV I) :
    1 ≤ miniRk NB I.winSize I.baseOpt := by
  unfold miniRk HInstData.baseOpt
  rcases hL : I.lab with _ | L
  · simp only [Option.map_none, Option.getD_none]
    omega
  · have := h.base_pos hL
    simp only [Option.map_some, Option.getD_some]
    omega

/-- **A child stays in the domain**, and its base is at most `NB + 1`. -/
theorem mini_child {n₀ nB NB sC : ℕ} (h2 : 2 * nB ≤ NB) {I J : HInstData Ty.unit}
    (hI : MiniDom n₀ nB NB I) (hJ : HInstValid ssDV J) (hS : SizeChild sC I J)
    (hs : sC ≤ NB * NB) :
    MiniDom n₀ nB NB J ∧ J.baseOpt.getD (2 * J.winSize + 1) ≤ NB + 1 := by
  obtain ⟨hn, hN, hg⟩ := hS.closed hI.n_le hI.degree_le h2 hs
  refine ⟨⟨hS.n₀.trans hI.n₀, hn, hN, hg⟩, ?_⟩
  have hw := hJ.winSize_le
  unfold HInstData.baseOpt
  rcases J.lab with _ | L
  · simp only [Option.map_none, Option.getD_none]
    omega
  · simp only [Option.map_some, Option.getD_some]
    omega

end Rank

/-! ### Correctness and cost -/

section Spec

open Sims

/-- The work of M0 on the domain. -/
def miniWM0 (nB NB : ℕ) : ℕ :=
  m0StepCost nB NB nB (NB * NB) (NB * NB) (genCost NB (NB * NB) + 2)
    (Sims.liftCost NB (NB * NB) nB + 7) (genCost NB (NB * NB) + 2)

/-- The work of M3 on the domain: at most `NB!` coset representatives. -/
def miniWM3 (nB NB : ℕ) : ℕ :=
  kerRedCost NB 0 nB NB.factorial (NB * NB) (NB * NB) (kerCost NB (NB * NB) NB + 5)
    (orbitsCost NB (NB * NB) nB + 5) (Sims.repsCost NB (NB * NB) (NB * NB) NB.factorial + 7)
    (genCost NB (NB.factorial * (NB * NB + 1)) + 2) + 5

/-- **The work bound**: the dispatch and the work of every step on the domain. -/
def miniW (nB NB : ℕ) : ℕ :=
  fixedTestCost nB (NB * NB) + fixedStepCost nB + orbitsCost NB (NB * NB) nB + nB +
    chainCost NB nB nB + miniWM0 nB NB + miniWM3 nB NB + 30

/-- **The cost bound of the mini procedure** at rank `r`: every step has at most `NB! · nB`
children. -/
abbrev miniCost (nB NB : ℕ) : ℕ → ℕ := miniC (NB.factorial * nB) (miniW nB NB)

/-- **The induction hypothesis** below rank `r`. -/
def MiniIH (n₀ nB NB r : ℕ) : Prop :=
  ∀ J : HInstData Ty.unit, HInstValid ssDV J → MiniDom n₀ nB NB J →
    miniRk NB J.winSize J.baseOpt < r →
    ∃ ans : AnswerData Ty.unit,
      RunsWithin ssCtx (miniBody Ty.unit Ty.denote) (miniBody Ty.unit Ty.denote J) ans
        (miniCost nB NB (miniRk NB J.winSize J.baseOpt)) ∧
      J.inst.OK ssDV ans ∧ ∀ c : CosetData Ty.unit, ans = some c → c.2.gens.length ≤ NB * NB

variable {n₀ nB NB : ℕ}

/-- **The recursive call solves every child of smaller rank** in the domain, by the induction
hypothesis. -/
theorem mini_hsub {r : ℕ} (ih : MiniIH n₀ nB NB r) {P : HInstData Ty.unit → Prop}
    (hP : ∀ J, HInstValid ssDV J → P J →
      MiniDom n₀ nB NB J ∧ miniRk NB J.winSize J.baseOpt < r) :
    HSubSolves ssCtx (miniBody Ty.unit Ty.denote) ssDV (fun J => Prog.recur J) P
      (fun p bo => 1 + miniCost nB NB (miniRk NB p bo)) (NB * NB) := by
  intro J hJ hPJ
  obtain ⟨hd, hr⟩ := hP J hJ hPJ
  obtain ⟨ans, hrun, hok, hg⟩ := ih J hJ hd hr
  exact ⟨ans, RunsWithin.recur hrun, hok, hg⟩

/-- **The chain rule in the mini procedure.** -/
theorem mini_chain (h2 : 2 * nB ≤ NB) {xy : StrData × StrData} {w : WinData} {σd : PermData}
    {N : ℕ} {gs : GensData} {n₀' n : ℕ}
    (hI : HInstValid ssDV (((xy, w, σd, N, gs, ()), n₀', n, none) : HInstData Ty.unit))
    (hd : MiniDom n₀ nB NB (((xy, w, σd, N, gs, ()), n₀', n, none) : HInstData Ty.unit))
    (ih : MiniIH n₀ nB NB (miniRk NB w.1.length none)) {os : List (List ℕ)}
    (hos : IsOrbitPartition (GensData.denote N gs) w os) (h2os : 2 ≤ os.length) :
    ∃ (ans : AnswerData Ty.unit) (ch : List (ℕ × Option ℕ)),
      RunsWithin ssCtx (miniBody Ty.unit Ty.denote)
        (Main.chainProg (fun J => Prog.recur J)
          (((xy, w, σd, N, gs, ()), n₀', n, none) : HInstData Ty.unit) os) ans
        ((ch.map fun x => 1 + miniCost nB NB (miniRk NB x.1 x.2)).sum +
          chainCost N w.1.length os.length) ∧
      InstData.OK (D := Ty.unit) (xy, w, σd, N, gs, ()) ssDV ans ∧
      (∀ c : CosetData Ty.unit, ans = some c → c.2.gens.length ≤ NB * NB) ∧
      (∀ x ∈ ch, miniRk NB x.1 x.2 < miniRk NB w.1.length none) ∧ ch.length ≤ w.1.length := by
  have hwn := sh_length_le hI
  have hsub := mini_hsub (P := fun J => SizeChild (max (NB * NB) gs.length)
      (((xy, w, σd, N, gs, ()), n₀', n, none) : HInstData Ty.unit) J ∧
      ChainChild w.1.length (J.winSize, J.baseOpt)) ih (fun J hJ ⟨hS, hc⟩ => by
    obtain ⟨hdJ, hb⟩ := mini_child h2 hd hJ hS (max_le le_rfl hd.gens_le)
    exact ⟨hdJ, miniRk_lt (ChainChild.measLt (m := 2 * w.1.length + 1) hc) hb⟩)
  obtain ⟨ans, ch, hrun, hok, hg, hch⟩ := RunsWithin.chainProg hI hos h2os hsub
  refine ⟨ans, ch, hrun, hok, fun c hc => (hg c hc).trans (max_le le_rfl hd.gens_le),
    fun x hx => ?_, by simpa using hch.length_le⟩
  have hc := hch.pred x hx
  have hn : n ≤ nB := hd.n_le
  exact miniRk_lt (ChainChild.measLt (m := 2 * w.1.length + 1) hc) (hc.getD_le.trans (by omega))

theorem mini_repsCost_mono {n n' L L' L₁ L₁' I I' : ℕ} (hn : n ≤ n') (hL : L ≤ L')
    (hL₁ : L₁ ≤ L₁') (hI : I ≤ I') : Sims.repsCost n L L₁ I ≤ Sims.repsCost n' L' L₁' I' := by
  unfold Sims.repsCost repsVisitCost siftCost
  gcongr
  exact buildCost_mono₂ hn hL₁

/-- **M0 in the mini procedure**, with its work bounded on the domain. -/
theorem mini_m0 (h2 : 2 * nB ≤ NB) {xy : StrData × StrData} {w : WinData} {σd : PermData}
    {N : ℕ} {gs : GensData} {n₀' n : ℕ}
    (hI : HInstValid ssDV (((xy, w, σd, N, gs, ()), n₀', n, none) : HInstData Ty.unit))
    (hd : MiniDom n₀ nB NB (((xy, w, σd, N, gs, ()), n₀', n, none) : HInstData Ty.unit))
    (ih : MiniIH n₀ nB NB (miniRk NB w.1.length none))
    (htr : IsTransOn (GensData.denote N gs) (w.denote N)) (h2w : 2 ≤ w.1.length) :
    ∃ (ans : AnswerData Ty.unit) (ch : List (ℕ × Option ℕ)),
      RunsWithin ssCtx (miniBody Ty.unit Ty.denote)
        (Main.m0StepProg (fun J => Prog.recur J)
          (((xy, w, σd, N, gs, ()), n₀', n, none) : HInstData Ty.unit)) ans
        ((ch.map fun x => 1 + miniCost nB NB (miniRk NB x.1 x.2)).sum + miniWM0 nB NB) ∧
      InstData.OK (D := Ty.unit) (xy, w, σd, N, gs, ()) ssDV ans ∧
      (∀ c : CosetData Ty.unit, ans = some c → c.2.gens.length ≤ NB * NB) ∧
      (∀ x ∈ ch, miniRk NB x.1 x.2 < miniRk NB w.1.length none) ∧ ch.length ≤ w.1.length := by
  have hwn := sh_length_le hI
  have hn : n ≤ nB := hd.n_le
  have hN : N ≤ NB := hd.degree_le
  have hgl : gs.length ≤ NB * NB := hd.gens_le
  obtain ⟨hk, hsC⟩ := ss_m0_gens_le hI htr h2w
  have hsC' : (rebaseModel ssCtx.O n N (Luks.maxBlocks N gs w.1) gs).2.1.length ≤ NB * NB :=
    hsC.trans (Nat.mul_le_mul (by omega) (by omega))
  have hsub := mini_hsub (P := fun J => SizeChild
      (rebaseModel ssCtx.O n N (Luks.maxBlocks N gs w.1) gs).2.1.length
      (((xy, w, σd, N, gs, ()), n₀', n, none) : HInstData Ty.unit) J ∧
      FreeChild w.1.length (2 * w.1.length + 1) (J.winSize, J.baseOpt)) ih
    (fun J hJ ⟨hS, hc⟩ => by
      obtain ⟨hdJ, hb⟩ := mini_child h2 hd hJ hS hsC'
      exact ⟨hdJ, miniRk_lt (FreeChild.measLt hc (by omega)) hb⟩)
  have hB : ssCtx.B.call GroupOp.generate (n + (Luks.maxBlocks N gs w.1).length,
      rebaseGens n N (Luks.maxBlocks N gs w.1) gs)
      (rebaseModel ssCtx.O n N (Luks.maxBlocks N gs w.1) gs) ≤ genCost NB (NB * NB) + 2 := by
    change genCost _ (rebaseGens n N (Luks.maxBlocks N gs w.1) gs).length + 2 ≤ _
    rw [rebaseGens, List.length_map]
    exact Nat.add_le_add_right (genCost_mono₂ (by omega) hgl) 2
  have hBlift : ∀ π' : PermData, π'.Valid n →
      ssCtx.B.call GroupOp.lift ((N, gs, ()), (strWin N n, π'))
        (ssCtx.O.run GroupOp.lift ((N, gs, ()), (strWin N n, π'))) ≤
        Sims.liftCost NB (NB * NB) nB + 7 := by
    intro π' _
    change Sims.liftCost N gs.length (List.range n).length + 7 ≤ _
    rw [List.length_range]
    exact Nat.add_le_add_right (rd_liftCost_mono₂ hN hgl hn) 7
  have hBgen : ∀ hs : GensData, GensData.AllValid N hs → hs.length ≤ NB * NB →
      GensData.denote N hs ≤ GensData.denote N gs →
      ssCtx.B.call GroupOp.generate (N, hs) (ssCtx.O.run GroupOp.generate (N, hs)) ≤
        genCost NB (NB * NB) + 2 := by
    intro hs _ hl _
    change genCost N hs.length + 2 ≤ _
    exact Nat.add_le_add_right (genCost_mono₂ hN hl) 2
  obtain ⟨ans, ch, hrun, hok, hg, hch⟩ := RunsWithin.m0StepProg (X := ssCtx)
    (fun op x _ hx => ssOracle_meets op x hx) (fun _ _ _ h => h) hI htr h2w hsub hB hBlift hBgen
  have hw : m0StepCost n N w.1.length gs.length (NB * NB) (genCost NB (NB * NB) + 2)
      (Sims.liftCost NB (NB * NB) nB + 7) (genCost NB (NB * NB) + 2) ≤ miniWM0 nB NB := by
    unfold miniWM0 m0StepCost m0Cost Luks.maxBlocksCost Luks.mbCost Luks.closureCost rebaseCost
      viaChildCost transferCost
    gcongr <;> omega
  refine ⟨ans, ch, hrun.mono (Nat.add_le_add_left hw _), hok,
    hg (NB * NB) (fun hs hv _ => (ssOracle_gens_le hv).1.trans (Nat.mul_le_mul hN hN)),
    fun x hx => ?_, by simpa using hch.length_le⟩
  have hc := hch.pred x hx
  exact miniRk_lt (FreeChild.measLt hc (by omega))
    (hc.getD_le.trans (max_le (by omega) (by omega)))

/-- **M3 in the mini procedure**, with its work bounded on the domain: at most
`(N − n)! ≤ NB!` cosets of the kernel. -/
theorem mini_m3 (h2 : 2 * nB ≤ NB) {xy : StrData × StrData} {w : WinData} {σd : PermData}
    {N : ℕ} {gs : GensData} {n₀' n : ℕ} {L : LabelData}
    (hI : HInstValid ssDV (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit))
    (hd : MiniDom n₀ nB NB (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit))
    (ih : MiniIH n₀ nB NB (miniRk NB w.1.length (some (N - n)))) :
    ∃ (ans : AnswerData Ty.unit) (ch : List (ℕ × Option ℕ)),
      RunsWithin ssCtx (miniBody Ty.unit Ty.denote)
        (Main.m3Prog (fun J => Prog.recur J)
          (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit)) ans
        ((ch.map fun x => 1 + miniCost nB NB (miniRk NB x.1 x.2)).sum + miniWM3 nB NB) ∧
      InstData.OK (D := Ty.unit) (xy, w, σd, N, gs, ()) ssDV ans ∧
      (∀ c : CosetData Ty.unit, ans = some c → c.2.gens.length ≤ NB * NB) ∧
      (∀ x ∈ ch, miniRk NB x.1 x.2 < miniRk NB w.1.length (some (N - n))) ∧
      ch.length ≤ NB.factorial * w.1.length := by
  have hwn := sh_length_le hI
  have hn : n ≤ nB := hd.n_le
  have hN : N ≤ NB := hd.degree_le
  have hgl : gs.length ≤ NB * NB := hd.gens_le
  have hgs : GensData.AllValid N gs := hI.valid.group.1
  have hKb : (kerModel ssCtx.O n (N, gs, ())).2.1.length ≤ NB * NB :=
    (ss_ker_gens_le hgs).trans (Nat.mul_le_mul hN hN)
  have hsC : max (NB * NB) (kerModel ssCtx.O n (N, gs, ())).2.1.length ≤ NB * NB :=
    max_le le_rfl hKb
  have hW : 1 ≤ w.1.length := hI.win_pos rfl
  have hm : 1 ≤ N - n := hI.base_pos rfl
  have hsub := mini_hsub (P := fun J => SizeChild
      (max (NB * NB) (kerModel ssCtx.O n (N, gs, ())).2.1.length)
      (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit) J ∧
      StepChild w.1.length (N - n) (J.winSize, J.baseOpt)) ih
    (fun J hJ ⟨hS, hc⟩ => by
      obtain ⟨hdJ, hb⟩ := mini_child h2 hd hJ hS hsC
      exact ⟨hdJ, miniRk_lt (StepChild.measLt hc hW hm) hb⟩)
  have hBk : ssCtx.B.call GroupOp.kernel ((N, gs, ()), baseWin n N)
      (kerModel ssCtx.O n (N, gs, ())) ≤ kerCost NB (NB * NB) NB + 5 := by
    change kerCost N gs.length (baseWin n N).1.length + 5 ≤ _
    exact Nat.add_le_add_right
      (kerCost_mono₂ hN hgl ((WinData.length_le (baseWin_valid n N)).trans hN)) 5
  have hBo : ssCtx.B.call GroupOp.orbits (kerModel ssCtx.O n (N, gs, ()), w)
      (krOrbits ssCtx.O n (N, gs, ()) w) ≤ orbitsCost NB (NB * NB) nB + 5 := by
    change orbitsCost N (kernelModel N gs (baseWin n N)).length w.1.length + 5 ≤ _
    exact Nat.add_le_add_right (rd_orbitsCost_mono₂ hN hKb (hwn.trans hn)) 5
  have hB : ∀ hs : GensData, GensData.AllValid N hs →
      hs.length ≤ (kerReps ssCtx.O n (N, gs, ())).length *
        (max (NB * NB) (kerModel ssCtx.O n (N, gs, ())).2.1.length + 1) →
      GensData.denote N hs ≤ GensData.denote N gs →
      ssCtx.B.call GroupOp.generate (N, hs) (ssCtx.O.run GroupOp.generate (N, hs)) ≤
        genCost NB ((kerReps ssCtx.O n (N, gs, ())).length * (NB * NB + 1)) + 2 := by
    intro hs _ hl _
    change genCost N hs.length + 2 ≤ _
    exact Nat.add_le_add_right (genCost_mono₂ hN
      (hl.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right hsC 1)))) 2
  obtain ⟨ans, ch, hrun, hok, hg, hch, hfact⟩ := RunsWithin.m3Prog (X := ssCtx)
    (fun op x _ hx => ssOracle_meets op x hx) (fun _ _ _ h => h) hI hsub hBk hBo le_rfl hB
  have hreps : (kerReps ssCtx.O n (N, gs, ())).length ≤ NB.factorial :=
    hfact.trans (Nat.factorial_le (by omega))
  have hBcr : ssCtx.B.call GroupOp.cosetReps ((N, gs, ()), kerModel ssCtx.O n (N, gs, ()))
      (kerReps ssCtx.O n (N, gs, ())) ≤ Sims.repsCost NB (NB * NB) (NB * NB) NB.factorial + 7 := by
    change Sims.repsCost N gs.length (kernelModel N gs (baseWin n N)).length
      (kerReps ssCtx.O n (N, gs, ())).length + 7 ≤ _
    exact Nat.add_le_add_right (mini_repsCost_mono hN hgl hKb hreps) 7
  have hw : kerRedCost N n w.1.length (kerReps ssCtx.O n (N, gs, ())).length
      (kerModel ssCtx.O n (N, gs, ())).2.1.length (NB * NB) (kerCost NB (NB * NB) NB + 5)
      (orbitsCost NB (NB * NB) nB + 5)
      (ssCtx.B.call GroupOp.cosetReps ((N, gs, ()), kerModel ssCtx.O n (N, gs, ()))
        (kerReps ssCtx.O n (N, gs, ())))
      (genCost NB ((kerReps ssCtx.O n (N, gs, ())).length * (NB * NB + 1)) + 2) + 5 ≤
      miniWM3 nB NB := by
    unfold miniWM3 kerRedCost baseWinCost
    have hg' := genCost_mono₂ (le_refl NB) (Nat.mul_le_mul_right (NB * NB + 1) hreps)
    gcongr <;> omega
  refine ⟨ans, ch, hrun.mono (Nat.add_le_add_left hw _), hok,
    hg (NB * NB) (fun hs hv _ => (ssOracle_gens_le hv).1.trans (Nat.mul_le_mul hN hN)),
    fun x hx => ?_, hch.length_le.trans (Nat.mul_le_mul_right _ hreps)⟩
  have hc := hch.pred x hx
  exact miniRk_lt (StepChild.measLt hc hW hm) (hc.getD_le.trans (max_le (by omega) (by omega)))

/-- An orbit partition has at most as many orbits as the window has points. -/
theorem IsOrbitPartition.length_le_win {N : ℕ} {G : Subgroup (Perm (Fin N))} {w : WinData}
    {os : List (List ℕ)} (h : IsOrbitPartition G w os) : os.length ≤ w.1.length := by
  have key : ∀ l : List (List ℕ), (∀ o ∈ l, 0 < o.length) →
      l.length ≤ (l.map List.length).sum := by
    intro l hl
    induction l with
    | nil => simp
    | cons o l ih =>
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      have h1 := hl o List.mem_cons_self
      have h2 := ih fun y hy => hl y (List.mem_cons_of_mem _ hy)
      omega
  exact (key os fun o ho => h.length_pos ho).trans h.length_sum.le

/-- **The cost of a step** within the bound at its rank: children of smaller rank, at most
`NB! · nB` of them, and work at most `miniW`. -/
theorem mini_cost_le {R : ℕ} (hR : 1 ≤ R) {ch : List (ℕ × Option ℕ)}
    (hch : ∀ x ∈ ch, miniRk NB x.1 x.2 < R) (hlen : ch.length ≤ NB.factorial * nB) {e : ℕ}
    (he : e ≤ miniW nB NB) :
    (ch.map fun x => 1 + miniCost nB NB (miniRk NB x.1 x.2)).sum + e ≤ miniCost nB NB R := by
  obtain ⟨r, rfl⟩ : ∃ r, R = r + 1 := ⟨R - 1, by omega⟩
  have hs : (ch.map fun x => 1 + miniCost nB NB (miniRk NB x.1 x.2)).sum ≤
      ch.length * (1 + miniC (NB.factorial * nB) (miniW nB NB) r) := mini_sum_le hch
  have hm := Nat.mul_le_mul_right (1 + miniC (NB.factorial * nB) (miniW nB NB) r) hlen
  change _ ≤ NB.factorial * nB * (1 + miniC _ _ r) + miniW nB NB
  omega

theorem mini_fixedTestCost_le {p p' s s' : ℕ} (hp : p ≤ p') (hs : s ≤ s') :
    fixedTestCost p s ≤ fixedTestCost p' s' := by
  unfold fixedTestCost
  gcongr

/-- **One step of the mini procedure**, from the induction hypothesis below its rank. -/
theorem mini_step (h2 : 2 * nB ≤ NB) {I : HInstData Ty.unit} (hI : HInstValid ssDV I)
    (hd : MiniDom n₀ nB NB I) (ih : MiniIH n₀ nB NB (miniRk NB I.winSize I.baseOpt)) :
    ∃ ans : AnswerData Ty.unit,
      RunsWithin ssCtx (miniBody Ty.unit Ty.denote) (miniBody Ty.unit Ty.denote I) ans
        (miniCost nB NB (miniRk NB I.winSize I.baseOpt)) ∧
      I.inst.OK ssDV ans ∧ ∀ c : CosetData Ty.unit, ans = some c → c.2.gens.length ≤ NB * NB := by
  have hr1 := mini_rk_pos (NB := NB) hI
  obtain ⟨⟨xy, w, σd, N, gs, d⟩, n₀', n, lab⟩ := I
  cases d
  have hv : InstData.Valid (D := Ty.unit) (xy, w, σd, N, gs, ()) ssDV := hI.valid
  have hwn := sh_length_le hI
  have hn : n ≤ nB := hd.n_le
  have hN : N ≤ NB := hd.degree_le
  have hgl : gs.length ≤ NB * NB := hd.gens_le
  have hT : fixedTestCost w.1.length gs.length ≤ fixedTestCost nB (NB * NB) :=
    mini_fixedTestCost_le (hwn.trans hn) hgl
  have ht : RunsWithin ssCtx (miniBody Ty.unit Ty.denote)
      (Main.fixedTestProg (S := groupSig Ty.unit)
        (((xy, w, σd, N, gs, ()), n₀', n, lab) : HInstData Ty.unit))
      (GensData.fixesB gs w) (fixedTestCost w.1.length gs.length) :=
    RunsWithin.fixedTestProg _
  cases hfx : GensData.fixesB gs w with
  | true =>
    rw [hfx] at ht
    obtain ⟨ans, hrun, hok, hg⟩ := RunsWithin.fixedStepProg (X := ssCtx)
      (body := miniBody Ty.unit Ty.denote) (n₀ := n₀') (n := n) (lab := lab) hv
      ((GensData.fixesB_iff hv.group.1 hv.win).1 hfx)
    refine ⟨ans, ?_, hok, fun c hc => (hg c hc).trans hgl⟩
    apply RunsWithin.mono
    case h =>
      run_step ht
      exact RunsWithin.ite_true hrun
    case hc =>
      refine le_trans ?_ (le_miniC _ _ _)
      unfold miniW fixedStepCost
      omega
  | false =>
    rw [hfx] at ht
    have hnfix : ¬ FixesPointwise (GensData.denote N gs) (w.denote N) := fun h => by
      have : GensData.fixesB gs w = true := (GensData.fixesB_iff hv.group.1 hv.win).2 h
      rw [hfx] at this
      exact Bool.false_ne_true this
    rcases lab with _ | L
    · obtain ⟨hrunO, hos⟩ := RunsWithin.winOrbitsProg (X := ssCtx)
        (body := miniBody Ty.unit Ty.denote) (n₀ := n₀') (n := n) (lab := none)
        (fun op x _ hx => ssOracle_meets op x hx) (fun _ h => h) hv
      have hosl := IsOrbitPartition.length_le_win hos
      have hBo : ssCtx.B.call GroupOp.orbits ((N, gs, ()), w)
          (ssCtx.O.run GroupOp.orbits ((N, gs, ()), w)) ≤ orbitsCost NB (NB * NB) nB + 5 := by
        change orbitsCost N gs.length w.1.length + 5 ≤ _
        exact Nat.add_le_add_right (rd_orbitsCost_mono₂ hN hgl (hwn.trans hn)) 5
      by_cases hmany : 2 ≤ (ssCtx.O.run GroupOp.orbits ((N, gs, ()), w)).length
      · obtain ⟨ans, ch, hrun, hok, hg, hrk, hlen⟩ := mini_chain h2 hI hd ih hos hmany
        refine ⟨ans, ?_, hok, hg⟩
        apply RunsWithin.mono
        case h =>
          run_step ht
          apply RunsWithin.ite_false
          run_step (RunsWithin.prim _ _)
          run_step (RunsWithin.prim _ _)
          run_step (RunsWithin.prim _ _)
          apply RunsWithin.caseOption_none
          run_step hrunO
          run_step (RunsWithin.prim_le
            (c := (ssCtx.O.run GroupOp.orbits ((N, gs, ()), w)).length + 1) rfl le_rfl)
          run_step (RunsWithin.prim _ _)
          run_step (RunsWithin.prim_le (v := true)
            (show decide (1 < (ssCtx.O.run GroupOp.orbits ((N, gs, ()), w)).length) = true from
              decide_eq_true (by omega)) le_rfl)
          exact RunsWithin.ite_true hrun
        case hc =>
          have hc : chainCost N w.1.length (ssCtx.O.run GroupOp.orbits ((N, gs, ()), w)).length ≤
              chainCost NB nB nB := by
            unfold chainCost
            gcongr <;> omega
          have := mini_cost_le (nB := nB) hr1 hrk (hlen.trans (by
            have := Nat.le_mul_of_pos_left nB (Nat.factorial_pos NB); omega))
            (e := chainCost N w.1.length (ssCtx.O.run GroupOp.orbits ((N, gs, ()), w)).length +
              (fixedTestCost w.1.length gs.length + (6 + ssCtx.B.call GroupOp.orbits
                ((N, gs, ()), w) (ssCtx.O.run GroupOp.orbits ((N, gs, ()), w))) +
                (ssCtx.O.run GroupOp.orbits ((N, gs, ()), w)).length + 10))
            (by unfold miniW; omega)
          simp only [Prim.cost]
          omega
      · have hone : (ssCtx.O.run GroupOp.orbits ((N, gs, ()), w)).length ≤ 1 := by omega
        obtain ⟨htr, h2w⟩ := mini_m0_case hv.invariant hnfix hos hone
        obtain ⟨ans, ch, hrun, hok, hg, hrk, hlen⟩ := mini_m0 h2 hI hd ih htr h2w
        refine ⟨ans, ?_, hok, hg⟩
        apply RunsWithin.mono
        case h =>
          run_step ht
          apply RunsWithin.ite_false
          run_step (RunsWithin.prim _ _)
          run_step (RunsWithin.prim _ _)
          run_step (RunsWithin.prim _ _)
          apply RunsWithin.caseOption_none
          run_step hrunO
          run_step (RunsWithin.prim_le
            (c := (ssCtx.O.run GroupOp.orbits ((N, gs, ()), w)).length + 1) rfl le_rfl)
          run_step (RunsWithin.prim _ _)
          run_step (RunsWithin.prim_le (v := false)
            (show decide (1 < (ssCtx.O.run GroupOp.orbits ((N, gs, ()), w)).length) = false from
              decide_eq_false (by omega)) le_rfl)
          exact RunsWithin.ite_false hrun
        case hc =>
          have := mini_cost_le (nB := nB) hr1 hrk (hlen.trans (by
            have := Nat.le_mul_of_pos_left nB (Nat.factorial_pos NB); omega))
            (e := miniWM0 nB NB +
              (fixedTestCost w.1.length gs.length + (6 + ssCtx.B.call GroupOp.orbits
                ((N, gs, ()), w) (ssCtx.O.run GroupOp.orbits ((N, gs, ()), w))) +
                (ssCtx.O.run GroupOp.orbits ((N, gs, ()), w)).length + 10))
            (by unfold miniW; omega)
          simp only [Prim.cost]
          omega
    · obtain ⟨ans, ch, hrun, hok, hg, hrk, hlen⟩ := mini_m3 h2 hI hd ih
      refine ⟨ans, ?_, hok, hg⟩
      apply RunsWithin.mono
      case h =>
        run_step ht
        apply RunsWithin.ite_false
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        exact RunsWithin.caseOption_some hrun
      case hc =>
        have := mini_cost_le (nB := nB) hr1 hrk
          (hlen.trans (Nat.mul_le_mul_left _ (hwn.trans hn)))
          (e := miniWM3 nB NB + (fixedTestCost w.1.length gs.length + 5))
          (by unfold miniW; omega)
        simp only [Prim.cost]
        omega

/-- **Correctness and cost of the mini procedure** (`PLAN-14.md` §14.7, item 3). On the domain
(`2 nB ≤ NB`): the procedure returns a correct answer with at most `NB²` generators, within
`miniCost nB NB` of the rank of the instance's measure. The proof is strong induction on the
rank; each step's sub-solver hypothesis is the induction hypothesis (`mini_hsub`). -/
theorem mini_spec {n₀ nB NB : ℕ} (h2 : 2 * nB ≤ NB) (I : HInstData Ty.unit)
    (hI : HInstValid ssDV I) (hd : MiniDom n₀ nB NB I) :
    ∃ ans : AnswerData Ty.unit,
      RunsWithin ssCtx (miniBody Ty.unit Ty.denote) (miniBody Ty.unit Ty.denote I) ans
        (miniCost nB NB (miniRk NB I.winSize I.baseOpt)) ∧
      I.inst.OK ssDV ans ∧ ∀ c : CosetData Ty.unit, ans = some c → c.2.gens.length ≤ NB * NB := by
  suffices h : ∀ r, MiniIH n₀ nB NB r from h _ I hI hd (Nat.lt_succ_self _)
  intro r
  induction r with
  | zero => exact fun J _ _ h => absurd h (Nat.not_lt_zero _)
  | succ r ih =>
    intro J hJ hdJ hr
    rcases Nat.lt_succ_iff_lt_or_eq.1 hr with hlt | heq
    · exact ih J hJ hdJ hlt
    · rw [← heq] at ih
      exact mini_step h2 hJ hdJ ih

/-- **The mini procedure on every valid instance** (`PLAN-14.md` §14.7, item 3), with no
hypothesis: the entry generates the group (one charged `generate`, which leaves at most `N²`
generators), and the recursion runs on the instance without a hint, with `n₀ = n = N`, in the
domain `nB = N`, `NB = 2N` (`mini_spec`). An empty window is the base case. -/
theorem miniSolve_ss {xy : StrData × StrData} {w : WinData} {σd : PermData} {N : ℕ}
    {gs : GensData} (hw : w.Valid N) (hσ : σd.Valid N) (hgs : GensData.AllValid N gs)
    (hinv : IsInvariant (GensData.denote N gs) (w.denote N)) :
    ∃ ans : AnswerData Ty.unit,
      RunsWithin ssCtx (miniBody Ty.unit Ty.denote)
        (miniEntry Ty.unit Ty.denote (xy, w, σd, N, gs)) ans
        (genCost N gs.length + 2 + 15 + miniCost N (2 * N) (miniRk (2 * N) w.1.length none)) ∧
      AnsOK ssDV N (w.denote N) (σd.denote N) (gs.denote N) (xy.1.denote N) (xy.2.denote N)
        ans := by
  obtain ⟨hgv, hden, hlen⟩ := generateModel_spec hgs
  have hI : HInstValid ssDV
      (((xy, w, σd, N, generateModel N gs, ()), N, N, none) : HInstData Ty.unit) := by
    refine ⟨⟨hw, hσ, ⟨hgv, trivial⟩, ?_⟩, le_rfl, ?_, fun i hi => hw.lt i hi, ?_, ?_⟩
    · change IsInvariant (GensData.denote N (generateModel N gs)) (w.denote N)
      rw [hden]
      exact hinv
    · intro g _ u hu
      have hu' : u.val < N := u.2
      exact absurd (show N ≤ u.val from hu) (by omega)
    · intro g _ hg
      exact Equiv.ext fun j => hg j j.2
    · intro L hL
      cases hL
  have hd : MiniDom N N (2 * N)
      (((xy, w, σd, N, generateModel N gs, ()), N, N, none) : HInstData Ty.unit) :=
    ⟨rfl, le_rfl, by change N ≤ 2 * N; omega,
      hlen.trans (Nat.mul_le_mul (by omega) (by omega))⟩
  obtain ⟨ans, hrun, hok, -⟩ := mini_spec le_rfl _ hI hd
  replace hrun : RunsWithin ssCtx (miniBody Ty.unit Ty.denote)
      (miniBody Ty.unit Ty.denote
        (((xy, w, σd, N, generateModel N gs, ()), N, N, none) : HInstData Ty.unit)) ans
      (miniCost N (2 * N) (miniRk (2 * N) w.1.length none)) := hrun
  have hG : ssCtx.O.run GroupOp.generate (N, gs) = (N, generateModel N gs, ()) := rfl
  refine ⟨ans, ?_, ?_⟩
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.call (X := ssCtx) (op := GroupOp.generate) (x := (N, gs)) hgs)
      rw [hG]
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      exact RunsWithin.recur hrun
    case hc =>
      have hc : ssCtx.B.call GroupOp.generate (N, gs) (ssCtx.O.run GroupOp.generate (N, gs)) =
          genCost N gs.length + 2 := rfl
      simp only [Prim.cost]
      omega
  · change AnsOK ssDV N (w.denote N) (σd.denote N) (GensData.denote N (generateModel N gs)) _ _
      ans at hok
    rw [hden] at hok
    exact hok

end Spec

end GraphIso.Main
