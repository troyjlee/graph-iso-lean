module

public import GraphIso.Main.Frame
public import GraphIso.Toolkit.Reduce
public import GraphIso.Reductions.BlocksProg
public import GraphIso.Programs.Checks
public import GraphIso.SoJProg.Data

/-!
# The steps without re-based children: base case, chain rule, kernel reduction

Stage 14j-2, item 4 (`PLAN-14.md` §14.2): the steps whose sub-calls are instances **without a
hint at the same degree**, so that no answer transfer is needed. Each takes the hinted
sub-solver `sub` as a parameter; a sub-call wraps an instance `J` as the hinted instance
`(J, n₀, n, none)` (`plainProg`, `plainSub`, with `sb_seqSub` turning `HSubSolves` into the
hypothesis of `seqProg`).

* **The base case** (`fixedStepProg`): the group fixes the window pointwise, in particular when
  the window is empty (the test is `fixedTestProg`, deciding `FixesPointwise` by `fixesB`). The
  answer is the input coset or `none`, by `matchesB`; there are no children.
* **The chain rule** (`chainProg`): the orbits `os` of `G` on `W` (`winOrbitsProg`), at least
  two of them; `seqProg` over the orbits, each a sub-call without a hint (`ChainChild`
  children, `c = 1`).
* **The kernel reduction** (`kerRedProg`), for M3 and for the fallback of reduce-and-derive.
  For an instance `(x, y, w, σ • K)` inside a hinted parent `(G, W, L)` (`K ≤ G`, `w ⊆ W`):
  the kernel `Kb` of `K`'s base action (`kernel` with the base window), the `Kb`-orbits of
  `w`, and `blockProg` (a branch over the cosets of `Kb` in `K`, each solved by `seqProg` over
  the orbits). The kernel fixes every base point, hence every label, so its orbits lie in
  label fibres of the parent's window and have at most `|W|/2` points (`sb_half_of_fix`, by
  `card_le_of_const`): the children are `StepChild` children without a hint, `c = |reps|`, and
  `|reps| = |ψ(K)| ≤ m!` for `m = N − n`.
* **M3** (`m3Prog`): the kernel reduction of the instance itself.

Specs: `RunsWithin.fixedStepProg`, `RunsWithin.chainProg`, `RunsWithin.kerRedProg`,
`RunsWithin.m3Prog`. Each gives the run, with the cost as the sum of the children's costs
`C x.1 x.2` plus the work, `AnsOK`, the output generator bound, and `ChildList` (nonempty
windows: the children are orbits). The sub-solver is asked only for children with at most `sC`
generators (`SizeChild sC`, stage 14j-5a): `max s |gs|` for the chain rule, whose children carry
the parent's group or an answer's, and `max s |Kb|` for the kernel reduction, whose children
carry the kernel's group `Kb` or an answer's. Backend charges
are hypotheses on the specific calls; the final `generate` of the branch combination is charged
on bounded lists, as in `blockProg`.
-/

@[expose] public section

namespace GraphIso.Main

open Equiv Cost GraphIso GraphIso.Programs GraphIso.Toolkit GraphIso.Recursion

/-! ### Programs -/

section Programs

variable {D : Ty} {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- The hinted instance `(J, n₀, n, none)`: the instance `J` without a hint. -/
def plainProg (n₀ n : var .nat) (J : var (Ty.inst D)) : Prog S rec var (hinstTy D) :=
  .bind (.op0 .none) fun nl => .bind (.op2 .pair n nl) fun p₁ =>
  .bind (.op2 .pair n₀ p₁) fun p₂ => .op2 .pair J p₂

/-- The sub-solver on instances without a hint. -/
def plainSub (sub : var (hinstTy D) → Prog S rec var (Ty.answer D)) (n₀ n : var .nat)
    (J : var (Ty.inst D)) : Prog S rec var (Ty.answer D) :=
  .bind (plainProg n₀ n J) sub

/-- **The base-case test**: do the generators fix every window point? -/
def fixedTestProg (I : var (hinstTy D)) : Prog S rec var .bool :=
  .bind (.op1 .fst I) fun J => .bind (.op1 .snd J) fun wc =>
  .bind (.op1 .fst wc) fun w => .bind (.op1 .snd wc) fun c =>
  .bind (.op1 .snd c) fun G => .bind (.op1 .snd G) fun gd => .bind (.op1 .fst gd) fun gens =>
  .bind (.op1 .fst w) fun pts => fixesProg gens pts

/-- **The base case**: the group fixes the window pointwise; the answer is the input coset if
`σ` carries `x` to `y` on the window, and `none` otherwise. -/
def fixedStepProg (I : var (hinstTy D)) : Prog S rec var (Ty.answer D) :=
  .bind (.op1 .fst I) fun J => .bind (.op1 .fst J) fun xy => .bind (.op1 .snd J) fun wc =>
  .bind (.op1 .fst wc) fun w => .bind (.op1 .snd wc) fun c =>
  .bind (.op1 .fst c) fun σ => .bind (.op1 .fst w) fun pts =>
  .bind (matchesProg pts σ xy) fun ok => .ite ok (.op1 .some c) (.op0 .none)

/-- The orbits of the group on the window. -/
def winOrbitsProg (I : var (hinstTy D)) : Prog (groupSig D) rec var (.list (.list .nat)) :=
  .bind (.op1 .fst I) fun J => .bind (.op1 .snd J) fun wc =>
  .bind (.op1 .fst wc) fun w => .bind (.op1 .snd wc) fun c =>
  .bind (.op1 .snd c) fun G => .bind (.op2 .pair G w) fun Gw =>
  Prog.call (S := groupSig D) GroupOp.orbits Gw

/-- **The chain rule**: process the orbits `os` of the group on the window sequentially, each
by a sub-call without a hint. -/
def chainProg (sub : var (hinstTy D) → Prog S rec var (Ty.answer D)) (I : var (hinstTy D))
    (os : var (.list (.list .nat))) : Prog S rec var (Ty.answer D) :=
  .bind (.op1 .fst I) fun J => .bind (.op1 .snd I) fun r₁ =>
  .bind (.op1 .fst r₁) fun n₀ => .bind (.op1 .snd r₁) fun r₂ => .bind (.op1 .fst r₂) fun n =>
  .bind (.op1 .fst J) fun xy => .bind (.op1 .snd J) fun wc => .bind (.op1 .snd wc) fun c =>
  seqProg (plainSub sub n₀ n) xy c os

/-- **The kernel reduction** of the instance `J` (string positions `[0, n)`): the kernel of the
base action, its orbits on the window, and the block reduction over them. -/
def kerRedProg (sub : var (hinstTy D) → Prog (groupSig D) rec var (Ty.answer D))
    (n₀ n : var .nat) (J : var (Ty.inst D)) : Prog (groupSig D) rec var (Ty.answer D) :=
  .bind (.op1 .fst J) fun xy => .bind (.op1 .snd J) fun wc =>
  .bind (.op1 .fst wc) fun w => .bind (.op1 .snd wc) fun c =>
  .bind (.op1 .fst c) fun σ => .bind (.op1 .snd c) fun K =>
  .bind (.op1 .fst K) fun N => .bind (baseWinProg n N) fun bw =>
  .bind (.op2 .pair K bw) fun a₁ =>
  .bind (Prog.call (S := groupSig D) GroupOp.kernel a₁) fun Kb =>
  .bind (.op2 .pair Kb w) fun a₂ =>
  .bind (Prog.call (S := groupSig D) GroupOp.orbits a₂) fun os =>
  blockProg (plainSub sub n₀ n) xy w σ K Kb os

/-- **M3**: the kernel reduction of the hinted instance itself. -/
def m3Prog (sub : var (hinstTy D) → Prog (groupSig D) rec var (Ty.answer D))
    (I : var (hinstTy D)) : Prog (groupSig D) rec var (Ty.answer D) :=
  .bind (.op1 .fst I) fun J => .bind (.op1 .snd I) fun r₁ =>
  .bind (.op1 .fst r₁) fun n₀ => .bind (.op1 .snd r₁) fun r₂ => .bind (.op1 .fst r₂) fun n =>
  kerRedProg sub n₀ n J

end Programs

/-! ### Costs -/

/-- The cost of `fixedTestProg`: `s` generators, `p` window points. -/
def fixedTestCost (p s : ℕ) : ℕ := s * (5 * p + 3) + 9

/-- The cost of `fixedStepProg` on `p` window points. -/
def fixedStepCost (p : ℕ) : ℕ := 7 * p + 12

/-- The work of `chainProg` at degree `N` on `p` window points in `k` orbits. -/
def chainCost (N p k : ℕ) : ℕ := 9 + k * (2 * N + 17) + 5 * p

/-- The work of `kerRedProg` at degree `N` with string positions `[0, n)`, on `p` window points,
with `r` coset representatives, `sK` kernel generators, `s` sub-solver output generators, and
the charges `Bk` (kernel), `Bo` (orbits), `Bcr` (coset representatives) and `Bgen` (the final
`generate`). -/
def kerRedCost (N n p r sK s Bk Bo Bcr Bgen : ℕ) : ℕ :=
  baseWinCost n N + Bk + Bo + Bcr + Bgen + r * (24 * N + p * (2 * N + 22) + max s sK + 48) + 30

/-! ### General facts -/

section Facts

variable {D : Ty} {DV : ℕ → GensData → D.denote → Prop}

/-- An instance inside a parent with string positions `[0, n)`, as a hinted instance without
a hint. -/
theorem sb_hinstValid_plain {J : InstData D} (hv : J.Valid DV) {n₀ n : ℕ}
    (hn : n ≤ J.degree) (hb : IsInvariant J.G (baseSet n J.degree))
    (hw : ∀ i ∈ J.2.1.1, i < n)
    (hf : ∀ g ∈ J.G, (∀ j : Fin J.degree, j.val < n → g j = j) → g = 1) :
    HInstValid DV ((J, n₀, n, none) : HInstData D) :=
  ⟨hv, hn, hb, hw, hf, fun _ h => by cases h⟩

/-- **Elements fixing the base keep the labels**: if `G` is transitive on the window `w` with
valid hint data `L`, then a set of window points connected by a subgroup `H ≤ G` fixing every
base point has at most half of the window (`card_le_of_const`). -/
theorem sb_half_of_fix {n N : ℕ} {gs : GensData} {w : WinData} {L : LabelData}
    (hL : HintValid n N gs w L) (hgs : GensData.AllValid N gs) (hw : w.Valid N)
    (hinv : IsInvariant (GensData.denote N gs) (w.denote N))
    (htr : IsTransOn (GensData.denote N gs) (w.denote N))
    {H : Subgroup (Perm (Fin N))} (hHG : H ≤ GensData.denote N gs)
    (hHb : ∀ h ∈ H, ∀ u ∈ baseSet n N, h u = u)
    {o : List ℕ} (hnd : o.Nodup) (hsub : ∀ i ∈ o, i ∈ w.1)
    (hconn : ∀ i ∈ o, ∀ j ∈ o, SameOrbit H i j) :
    2 * o.length ≤ w.1.length := by
  have hh := hL.isHint hgs hw hinv
  have hW : Invariant ↥(GensData.denote N gs) (winFinset N w) := by
    intro g u hu
    rw [mem_winFinset] at hu ⊢
    exact hinv g.1 g.2 u hu
  have hT : Transitive ↥(GensData.denote N gs) (winFinset N w) := by
    intro u hu v hv
    rw [mem_winFinset] at hu hv
    obtain ⟨g, hg, e⟩ := htr u hu v hv
    exact ⟨⟨g, hg⟩, e⟩
  have hsub' : winFinset N (WinData.ofPoints N o) ⊆ winFinset N w := by
    intro u hu
    rw [mem_winFinset] at hu ⊢
    exact hsub _ hu
  have hnc : ¬ NonConst (winFinset N (WinData.ofPoints N o)) (labOf n N L) := by
    rintro ⟨u, hu, v, hv, hne⟩
    rw [mem_winFinset] at hu hv
    obtain ⟨hi, hj, h, hH, e⟩ := hconn u.val hu v.val hv
    have huv : h u = v := by
      have : (⟨u.val, hi⟩ : Fin N) = u := rfl
      rw [this] at e
      rw [e]
    have h1 : baseHom (GensData.denote N gs) n hL.base_inv ⟨h, hHG hH⟩ = 1 := by
      ext j
      have hj := baseHom_apply (hG := hL.base_inv) ⟨h, hHG hH⟩ j
      rw [hHb h hH _ (basePos_mem j)] at hj
      have := congrArg Fin.val hj
      simp only [basePos] at this
      simp only [Perm.coe_one, id_eq]
      omega
    have he := hh.equivar ⟨h, hHG hH⟩ u (by rw [mem_winFinset]; exact hsub _ hu)
    rw [h1] at he
    have he' : labOf n N L (h u) = labOf n N L u := by
      rw [show labOf n N L (h u) = labOf n N L ((⟨h, hHG hH⟩ : ↥(GensData.denote N gs)) • u)
        from rfl, he]
      ext x
      simp [Finset.mem_smul_finset]
    apply hne
    rw [← he', huv]
  have := card_le_of_const hW hT hh hsub' hnc
  rwa [show (winFinset N (WinData.ofPoints N o)).card = o.length from
      SoJProg.card_setOf hnd fun i hi => hw.lt i (hsub i hi),
    show (winFinset N w).card = w.1.length from SoJProg.card_setOf hw.nodup hw.lt] at this

/-- In an orbit partition with at least two orbits, every orbit is a proper part. -/
theorem sb_length_lt {N : ℕ} {G : Subgroup (Perm (Fin N))} {w : WinData}
    {os : List (List ℕ)} (hos : IsOrbitPartition G w os) (h2 : 2 ≤ os.length) :
    ∀ o ∈ os, o.length < w.1.length := by
  intro o ho
  have hsum : (os.map List.length).sum = w.1.length := by
    rw [← List.length_flatten]
    exact hos.1.length_eq
  have hp := List.perm_cons_erase ho
  have hsum' : (os.map List.length).sum = o.length + ((os.erase o).map List.length).sum := by
    rw [(List.Perm.map List.length hp).sum_eq]
    simp
  have hne : os.erase o ≠ [] := by
    intro h
    have := List.length_erase_of_mem ho
    rw [h] at this
    simp at this
    omega
  obtain ⟨o', ho'⟩ := List.exists_mem_of_ne_nil _ hne
  have ho'os : o' ∈ os := List.mem_of_mem_erase ho'
  have hpos : 0 < o'.length := List.length_pos_of_ne_nil (hos.2 o' ho'os).1
  have := List.le_sum_of_mem
    (List.mem_map.2 ⟨o', ho', rfl⟩ : o'.length ∈ (os.erase o).map List.length)
  omega

/-- The window lengths of an orbit partition sum to the window size. -/
theorem sb_sum_length {N : ℕ} {G : Subgroup (Perm (Fin N))} {w : WinData}
    {os : List (List ℕ)} (hos : IsOrbitPartition G w os) :
    (os.map List.length).sum = w.1.length := by
  rw [← List.length_flatten]
  exact hos.1.length_eq

/-- An orbit of an orbit partition lies in the window. -/
theorem sb_mem_win {N : ℕ} {G : Subgroup (Perm (Fin N))} {w : WinData}
    {os : List (List ℕ)} (hos : IsOrbitPartition G w os) {o : List ℕ} (ho : o ∈ os) :
    ∀ i ∈ o, i ∈ w.1 :=
  fun _ hi => hos.1.mem_iff.1 (List.mem_flatten.2 ⟨o, ho, hi⟩)

/-- The number of orbits is at most the window size. -/
theorem sb_length_le {N : ℕ} {G : Subgroup (Perm (Fin N))} {w : WinData}
    {os : List (List ℕ)} (hos : IsOrbitPartition G w os) : os.length ≤ w.1.length := by
  rw [← sb_sum_length hos]
  have : ∀ o ∈ os, 1 ≤ o.length := fun o ho =>
    List.length_pos_of_ne_nil (hos.2 o ho).1
  calc os.length = (os.map fun _ => 1).sum := by simp
    _ ≤ (os.map List.length).sum := List.sum_le_sum fun o ho => this o ho

/-- The sum of a function over `r` copies of a list. -/
theorem sb_sum_replicate {α : Type*} (f : α → ℕ) (l : List α) (r : ℕ) :
    (((List.replicate r l).flatten).map f).sum = r * (l.map f).sum := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [List.replicate_succ, List.flatten_cons, List.map_append, List.sum_append, ih]
    ring

/-- A duplicate-free sub-list has at most the length of the list. -/
theorem sb_length_le_of_sub {l l' : List ℕ} (hnd : l.Nodup) (hnd' : l'.Nodup)
    (hsub : ∀ i ∈ l, i ∈ l') : l.length ≤ l'.length := by
  rw [← List.toFinset_card_of_nodup hnd, ← List.toFinset_card_of_nodup hnd']
  exact Finset.card_le_card fun i hi => List.mem_toFinset.2 (hsub i (List.mem_toFinset.1 hi))

end Facts

/-! ### Specifications -/

section Specs

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}

theorem RunsWithin.plainProg (n₀ n : ℕ) (J : InstData D) :
    RunsWithin X body (Main.plainProg (S := groupSig D) n₀ n J)
      ((J, n₀, n, none) : HInstData D) 4 := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim _ _
  case hc => simp [Prim.cost]

theorem RunsWithin.plainSub {sub : HInstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)}
    (n₀ n : ℕ) (J : InstData D) {ans : AnswerData D} {k : ℕ}
    (h : RunsWithin X body (sub (J, n₀, n, none)) ans k) :
    RunsWithin X body (Main.plainSub sub n₀ n J) ans (k + 4) :=
  (RunsWithin.bind (RunsWithin.plainProg n₀ n J) h).mono (by omega)

/-- **From hinted sub-solvers to the hypothesis of `seqProg`**: if every instance the sequential
reduction can pass is, without a hint, a valid hinted instance satisfying `P`, the wrapped
sub-solver solves them within `C (window size) none + 4`. -/
theorem sb_seqSub {sub : HInstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)}
    {P : HInstData D → Prop} {C : ℕ → Option ℕ → ℕ} {s : ℕ}
    (hsub : HSubSolves X body DV sub P C s) {n₀ n N sIn : ℕ} {xy : StrData × StrData}
    {os : List (List ℕ)} {G : Subgroup (Perm (Fin N))}
    (hP : ∀ J : InstData D, J.1 = xy → J.Valid DV → J.degree = N →
      (∃ o ∈ os, J.2.1 = WinData.ofPoints N o) → J.2.2.2.gens.length ≤ sIn →
      GensData.denote N J.2.2.2.gens ≤ G →
      HInstValid DV ((J, n₀, n, none) : HInstData D) ∧ P (J, n₀, n, none)) :
    SeqSub X body DV (fun J => Main.plainSub sub n₀ n J) xy N os
      (fun o => C o.length none + 4) s sIn G := by
  rintro J ⟨h1, hv, hdeg, ho, hgl, hG⟩
  obtain ⟨hJ, hPJ⟩ := hP J h1 hv hdeg ho hgl hG
  obtain ⟨ans, hr, hok, hg⟩ := hsub _ hJ hPJ
  exact ⟨ans, RunsWithin.plainSub n₀ n J hr, hok, hg⟩

/-! #### The base case -/

theorem RunsWithin.fixedTestProg (I : HInstData D) :
    RunsWithin X body (Main.fixedTestProg (S := groupSig D) I)
      (GensData.fixesB I.inst.2.2.2.gens I.inst.2.1)
      (fixedTestCost I.inst.2.1.1.length I.inst.2.2.2.gens.length) := by
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
    exact RunsWithin.fixesProg I.inst.2.2.2.gens I.inst.2.1
  case hc =>
    simp only [Prim.cost, fixedTestCost]
    omega

/-- **The base-case test** decides whether the group fixes the window pointwise. -/
theorem fixedTest_iff {I : HInstData D} (hv : I.inst.Valid DV) :
    GensData.fixesB I.inst.2.2.2.gens I.inst.2.1 = true ↔ FixesPointwise I.inst.G I.inst.W :=
  GensData.fixesB_iff hv.group.1 hv.win

/-- **The base case**: when the group fixes the window pointwise (in particular when the window
is empty), the answer is the input coset or `none`; there are no sub-calls. -/
theorem RunsWithin.fixedStepProg {xy : StrData × StrData} {w : WinData} {σd : PermData}
    {N : ℕ} {gs : GensData} {d : D.denote} {n₀ n : ℕ} {lab : Option LabelData}
    (hv : InstData.Valid (D := D) (xy, w, σd, N, gs, d) DV)
    (hfix : FixesPointwise (GensData.denote N gs) (w.denote N)) :
    ∃ ans : AnswerData D,
      RunsWithin X body
        (Main.fixedStepProg (S := groupSig D) (((xy, w, σd, N, gs, d), n₀, n, lab) : HInstData D))
        ans (fixedStepCost w.1.length) ∧
      InstData.OK (D := D) (xy, w, σd, N, gs, d) DV ans ∧
      ∀ c : CosetData D, ans = some c → c.2.gens.length ≤ gs.length := by
  have hσ : σd.Valid N := hv.rep
  have hwv : w.Valid N := hv.win
  refine ⟨if matchesB w σd xy.1 xy.2 then some (σd, N, gs, d) else none, ?_, ?_, ?_⟩
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.matchesProg w σd xy)
      cases matchesB w σd xy.1 xy.2
      · exact RunsWithin.ite_false (RunsWithin.prim _ _)
      · exact RunsWithin.ite_true (RunsWithin.prim _ _)
    case hc =>
      simp only [Prim.cost, fixedStepCost]
      omega
  · change AnsOK DV N _ _ _ _ _ _
    cases hmat : matchesB w σd xy.1 xy.2
    · have := (matchesB_iff hwv hσ xy.1 xy.2).not.1 (by simp [hmat])
      exact iso_of_fixesPointwise_of_not_matches hfix this
    · have := (matchesB_iff hwv hσ xy.1 xy.2).1 hmat
      exact ⟨hσ, rfl, hv.group, (iso_of_fixesPointwise_of_matches hfix this).symm⟩
  · intro c hc
    split at hc
    · cases hc
      exact le_rfl
    · cases hc

/-! #### The chain rule -/

/-- **The orbits of the window**, from the backend. -/
theorem RunsWithin.winOrbitsProg (hO : MeetsContractOn DV (· = .orbits) X.O)
    (hPre : ∀ x, GroupPre DV .orbits x → X.Pre .orbits x) {xy : StrData × StrData}
    {w : WinData} {σd : PermData} {N : ℕ} {gs : GensData} {d : D.denote} {n₀ n : ℕ}
    {lab : Option LabelData} (hv : InstData.Valid (D := D) (xy, w, σd, N, gs, d) DV) :
    RunsWithin X body
        (Main.winOrbitsProg (rec := (a, b)) (((xy, w, σd, N, gs, d), n₀, n, lab) : HInstData D))
        (X.O.run GroupOp.orbits ((N, gs, d), w))
        (6 + X.B.call GroupOp.orbits ((N, gs, d), w) (X.O.run GroupOp.orbits ((N, gs, d), w))) ∧
      IsOrbitPartition (GensData.denote N gs) w (X.O.run GroupOp.orbits ((N, gs, d), w)) := by
  have hpre : GroupPre DV .orbits ((N, gs, d), w) := ⟨hv.group, hv.win, hv.invariant⟩
  refine ⟨?_, hO .orbits _ rfl hpre⟩
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.call (x := ((N, gs, d), w)) (hPre _ hpre)
  case hc =>
    simp only [Prim.cost]
    omega

/-- The sum of the sequential costs over an orbit list. -/
theorem sb_sum_seqCost (N : ℕ) (C : ℕ → Option ℕ → ℕ) (os : List (List ℕ)) :
    (os.map (seqCost N fun o => C o.length none + 4)).sum =
      ((os.map fun o => ((o.length, none) : ℕ × Option ℕ)).map fun x => C x.1 x.2).sum +
        os.length * (2 * N + 17) + 5 * (os.map List.length).sum := by
  induction os with
  | nil => simp
  | cons o os ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih, seqCost]
    ring

/-- **The chain rule**: no hint is needed. If the group has at least two orbits `os` on the
window, the sequential reduction over them is correct, at the cost of the children (one per
orbit, without a hint, on fewer points) plus `chainCost`. -/
theorem RunsWithin.chainProg
    {sub : HInstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)}
    {xy : StrData × StrData} {w : WinData} {σd : PermData} {N : ℕ} {gs : GensData}
    {d : D.denote} {n₀ n : ℕ} {lab : Option LabelData}
    (hI : HInstValid DV (((xy, w, σd, N, gs, d), n₀, n, lab) : HInstData D))
    {os : List (List ℕ)} (hos : IsOrbitPartition (GensData.denote N gs) w os)
    (h2 : 2 ≤ os.length) {C : ℕ → Option ℕ → ℕ} {s : ℕ}
    (hsub : HSubSolves X body DV sub
      (fun J => SizeChild (max s gs.length) (((xy, w, σd, N, gs, d), n₀, n, lab) : HInstData D)
        J ∧ ChainChild w.1.length (J.winSize, J.baseOpt)) C s) :
    ∃ (ans : AnswerData D) (ch : List (ℕ × Option ℕ)),
      RunsWithin X body
        (Main.chainProg sub (((xy, w, σd, N, gs, d), n₀, n, lab) : HInstData D) os) ans
        ((ch.map fun x => C x.1 x.2).sum + chainCost N w.1.length os.length) ∧
      InstData.OK (D := D) (xy, w, σd, N, gs, d) DV ans ∧
      (∀ c : CosetData D, ans = some c → c.2.gens.length ≤ max s gs.length) ∧
      ChildList w.1.length 1 (ChainChild w.1.length) ch := by
  have hv : InstData.Valid (D := D) (xy, w, σd, N, gs, d) DV := hI.valid
  obtain ⟨hseq, hunion⟩ := seqInputs_of_isOrbitPartition (n := N) hv.win hos
  have hlt := sb_length_lt hos h2
  have hsq : SeqSub X body DV (fun J => Main.plainSub sub n₀ n J) xy N os
      (fun o => C o.length none + 4) s (max s gs.length) (GensData.denote N gs) := by
    refine sb_seqSub hsub ?_
    rintro ⟨xy', w', σ', N', gs', d'⟩ h1 hJv hdeg ⟨o, ho, hwo⟩ hgl hG
    change N' = N at hdeg
    subst hdeg
    change w' = WinData.ofPoints N' o at hwo
    subst hwo
    refine ⟨sb_hinstValid_plain hJv hI.le (fun g hg => hI.base_inv g (hG hg)) ?_
      (fun g hg => hI.faithful g (hG hg)), ?_, ?_⟩
    · intro i hi
      exact hI.win_lt i (sb_mem_win hos ho i hi)
    · exact ⟨rfl, le_rfl, le_max_left _ _, hgl, SizeChild.lab_none rfl le_rfl rfl⟩
    · exact ⟨rfl, hlt o ho⟩
  obtain ⟨ans, hrun, hok, hg⟩ := RunsWithin.seqProg (n := N) (σd := σd) (Gd := (N, gs, d)) rfl
    hv.rep
    hv.group hseq hsq
  refine ⟨ans, os.map fun o => (o.length, none), ?_, ?_, hg, ?_, ?_, ?_⟩
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
      exact hrun
    case hc =>
      rw [sb_sum_seqCost, sb_sum_length hos]
      simp only [Prim.cost, chainCost]
      omega
  · rw [hunion] at hok
    exact hok
  · rw [List.map_map]
    simp only [Function.comp_def]
    rw [sb_sum_length hos]
    omega
  · intro x hx
    obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hx
    exact ⟨rfl, hlt o ho⟩
  · intro x hx
    obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hx
    exact List.length_pos_of_ne_nil (hos.2 o ho).1

/-! #### The kernel reduction -/

/-- The orbits of the kernel of the base action on the window, from the backend. -/
def krOrbits (O : Oracle (groupSig D)) (n : ℕ) (G : GroupData D.denote) (w : WinData) :
    List (List ℕ) :=
  O.run GroupOp.orbits (kerModel O n G, w)

/-- The operations of the kernel reduction. -/
def kerRedOps (op : GroupOp) : Prop :=
  op = .kernel ∨ op = .orbits ∨ op = .cosetReps ∨ op = .generate

/-- **The kernel reduction** of an instance `(x, y, w, σ • K)` inside a hinted parent
`(G, W, L)` with the same degree `N` and string positions `[0, n)` (`K ≤ G`, `w ⊆ W`). The
children are the orbits of the kernel `Kb` of `K`'s base action on `w`, without a hint, one per
coset of `Kb` in `K`; they lie in label fibres of `W`, so each has at most `|W|/2` points
(`StepChild`). The number of cosets is `|ψ(K)| ≤ m!`. -/
theorem RunsWithin.kerRedProg (hO : MeetsContractOn DV kerRedOps X.O)
    (hPre : ∀ op x, kerRedOps op → GroupPre DV op x → X.Pre op x)
    {sub : HInstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)}
    {xyP : StrData × StrData} {wP : WinData} {σP : PermData} {N : ℕ} {gsG : GensData}
    {dG : D.denote} {n₀ n : ℕ} {L : LabelData}
    (hP : HInstValid DV (((xyP, wP, σP, N, gsG, dG), n₀, n, some L) : HInstData D))
    {xy : StrData × StrData} {w : WinData} {σd : PermData} {gs : GensData} {d : D.denote}
    (hJ : InstData.Valid (D := D) (xy, w, σd, N, gs, d) DV)
    (hKG : GensData.denote N gs ≤ GensData.denote N gsG) (hw : ∀ i ∈ w.1, i ∈ wP.1)
    {C : ℕ → Option ℕ → ℕ} {s Bk Bo Bcr Bgen : ℕ}
    (hsub : HSubSolves X body DV sub
      (fun J => SizeChild (max s (kerModel X.O n (N, gs, d)).2.1.length)
          (((xyP, wP, σP, N, gsG, dG), n₀, n, some L) : HInstData D) J ∧
        StepChild wP.1.length (N - n) (J.winSize, J.baseOpt)) C s)
    (hBk : X.B.call GroupOp.kernel ((N, gs, d), baseWin n N) (kerModel X.O n (N, gs, d)) ≤ Bk)
    (hBo : X.B.call GroupOp.orbits (kerModel X.O n (N, gs, d), w)
      (krOrbits X.O n (N, gs, d) w) ≤ Bo)
    (hBcr : X.B.call GroupOp.cosetReps ((N, gs, d), kerModel X.O n (N, gs, d))
      (kerReps X.O n (N, gs, d)) ≤ Bcr)
    (hB : ∀ hs : GensData, GensData.AllValid N hs →
      hs.length ≤ (kerReps X.O n (N, gs, d)).length *
        (max s (kerModel X.O n (N, gs, d)).2.1.length + 1) →
      GensData.denote N hs ≤ GensData.denote N gs →
      X.B.call GroupOp.generate (N, hs) (X.O.run GroupOp.generate (N, hs)) ≤ Bgen) :
    ∃ (ans : AnswerData D) (ch : List (ℕ × Option ℕ)),
      RunsWithin X body (Main.kerRedProg sub n₀ n (xy, w, σd, N, gs, d)) ans
        ((ch.map fun x => C x.1 x.2).sum +
          kerRedCost N n w.1.length (kerReps X.O n (N, gs, d)).length
            (kerModel X.O n (N, gs, d)).2.1.length s Bk Bo Bcr Bgen) ∧
      InstData.OK (D := D) (xy, w, σd, N, gs, d) DV ans ∧
      (∀ sGen, (∀ hs, GensData.AllValid N hs → GensData.denote N hs ≤ GensData.denote N gs →
          (X.O.run GroupOp.generate (N, hs)).2.1.length ≤ sGen) →
        ∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sGen) ∧
      ChildList wP.1.length (kerReps X.O n (N, gs, d)).length
        (StepChild wP.1.length (N - n)) ch ∧
      (kerReps X.O n (N, gs, d)).length ≤ (N - n).factorial := by
  -- the parent
  have hPv := hP.valid
  obtain ⟨hhint, htr⟩ := hP.hint L rfl
  have hPgs : GensData.AllValid N gsG := hPv.group.1
  have hbG : IsInvariant (GensData.denote N gs) (baseSet n N) :=
    fun g hg => hP.base_inv g (hKG hg)
  -- the kernel, by `kerProg`'s facts
  obtain ⟨-, hKn, hKv, hKden, -, -, -, hrlen⟩ := RunsWithin.kerProg (X := X) (body := body)
    (n := n) (N := N) (gs := gs) (d := d)
    (fun op x hop hx => hO op x (by rcases hop with h | h <;> simp [kerRedOps, h]) hx)
    (fun op x hop hx => hPre op x (by rcases hop with h | h <;> simp [kerRedOps, h]) hx)
    hJ.group hbG hBk hBcr
  have hkpre : GroupPre DV .kernel ((N, gs, d), baseWin n N) :=
    ⟨hJ.group, baseWin_valid n N, by rw [baseWin_denote]; exact hbG⟩
  have hKm : kerModel X.O n (N, gs, d) = X.O.run GroupOp.kernel ((N, gs, d), baseWin n N) := rfl
  have hRm : kerReps X.O n (N, gs, d) =
      X.O.run GroupOp.cosetReps ((N, gs, d), kerModel X.O n (N, gs, d)) := rfl
  have hfact : (kerReps X.O n (N, gs, d)).length ≤ (N - n).factorial := by
    rw [hrlen]
    calc Nat.card (baseHom (GensData.denote N gs) n hbG).range
        ≤ Nat.card (Perm (Fin (N - n))) := Subgroup.card_le_card_group _
      _ = (N - n).factorial := by
          rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  have hOm : krOrbits X.O n (N, gs, d) w =
      X.O.run GroupOp.orbits (kerModel X.O n (N, gs, d), w) := rfl
  rw [hRm] at hfact hB hBcr ⊢
  rw [hOm] at hBo
  have hBk0 : X.B.call GroupOp.kernel ((N, gs, d), baseWin n N)
      (X.O.run GroupOp.kernel ((N, gs, d), baseWin n N)) ≤ Bk := hBk
  rcases hK : kerModel X.O n (N, gs, d) with ⟨N', ks, e⟩
  rw [hK] at hKn hKv hKden hKm hBo hBcr hB hfact hBk hsub
  change N' = N at hKn
  subst N'
  have hKs : GensData.denote N ks ≤ GensData.denote N gs := by
    rw [hKden]
    exact pointwiseStab_le _ _
  -- the orbits of the kernel on the window
  have hopre : GroupPre DV .orbits ((N, ks, e), w) :=
    ⟨hKv, hJ.win, fun g hg => hJ.invariant g (hKs hg)⟩
  have hos := hO .orbits _ (Or.inr (Or.inl rfl)) hopre
  set os : List (List ℕ) := X.O.run GroupOp.orbits ((N, ks, e), w) with hosdef
  obtain ⟨hseq, -⟩ := seqInputs_of_isOrbitPartition (n := N) hJ.win hos
  -- the sub-solver hypothesis of the block reduction
  have hsq : SeqSub X body DV (fun J => Main.plainSub sub n₀ n J) xy N os
      (fun o => C o.length none + 4) s (max s ks.length) (GensData.denote N ks) := by
    refine sb_seqSub hsub ?_
    rintro ⟨xy', w', σ', N'', gs', d'⟩ h1 hJv hdeg ⟨o, ho, hwo⟩ hgl hG
    change N'' = N at hdeg
    subst hdeg
    change w' = WinData.ofPoints N'' o at hwo
    subst hwo
    have hGG : GensData.denote N'' gs' ≤ GensData.denote N'' gsG := hG.trans (hKs.trans hKG)
    have hoW : ∀ i ∈ o, i ∈ wP.1 := fun i hi => hw i (sb_mem_win hos ho i hi)
    have hhalf : 2 * o.length ≤ wP.1.length := by
      refine sb_half_of_fix hhint hPgs hPv.win hPv.invariant htr (hKs.trans hKG) ?_
        (hseq o ho).1 hoW ?_
      · intro h hh u hu
        rw [hKden] at hh
        exact hh.2 u hu
      · intro i hi j hj
        exact ((hos.2 o ho).2 i hi j).1 hj
    refine ⟨sb_hinstValid_plain hJv hP.le (fun g hg => hP.base_inv g (hGG hg)) ?_
      (fun g hg => hP.faithful g (hGG hg)), ?_, ?_⟩
    · intro i hi
      exact hP.win_lt i (hoW i hi)
    · exact ⟨rfl, le_rfl, le_max_left _ _, hgl, SizeChild.lab_none rfl le_rfl rfl⟩
    · refine ⟨by change o.length ≤ wP.1.length; omega, Or.inr ⟨rfl, hhalf⟩⟩
  -- the block reduction over the kernel's orbits
  have hKblk : GensData.denote N ks ≤ blockKernel (GensData.denote N gs) os := by
    intro g hg
    refine ⟨hKs hg, fun o ho u hu => ?_⟩
    exact ((hos.2 o ho).2 u.val hu (g u).val).2 ⟨u.2, (g u).2, g, hg, rfl⟩
  have hbs : IsBlockList w os := ⟨hos.1, fun o ho => (hos.2 o ho).1⟩
  obtain ⟨ans, hrun, hok, -, hgen⟩ := RunsWithin.blockProg (X := X) (body := body)
    (xy := xy) (w := w) (σd := σd) (n := N) (gs := gs) (ks := ks) (d := d) (e := e) (bs := os)
    (fun op x hop hx => hO op x (by rcases hop with h | h <;> simp [kerRedOps, h]) hx)
    (fun op x hop hx => hPre op x (by rcases hop with h | h <;> simp [kerRedOps, h]) hx)
    hJ.win hJ.rep hJ.group hJ.invariant hKv hKblk hbs hsq hBcr hB
  set r := (X.O.run GroupOp.cosetReps ((N, gs, d), (N, ks, e))).length with hrdef
  refine ⟨ans, (List.replicate r (os.map fun o => ((o.length, none) : ℕ × Option ℕ))).flatten,
    ?_, hok, hgen, ?_, hfact⟩
  · have hwlen := sb_sum_length hos
    have hklen := sb_length_le hos
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.baseWinProg n N)
      run_step (RunsWithin.prim _ _)
      run_step (((RunsWithin.call (x := ((N, gs, d), baseWin n N))
        (hPre _ _ (Or.inl rfl) hkpre)).mono hBk0).of_eq hKm.symm)
      run_step (RunsWithin.prim _ _)
      run_step ((RunsWithin.call (x := ((N, ks, e), w))
        (hPre _ _ (Or.inr (Or.inl rfl)) hopre)).mono hBo)
      exact hrun
    case hc =>
      simp only [Prim.cost]
      rw [sb_sum_replicate, blockBranchCost, sb_sum_seqCost, hwlen]
      simp only [kerRedCost]
      have hm : r * (os.length * (2 * N + 17)) ≤ r * (w.1.length * (2 * N + 17)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hklen)
      nlinarith [hm]
  · refine ⟨?_, ?_, ?_⟩
    · rw [sb_sum_replicate, List.map_map]
      simp only [Function.comp_def]
      rw [sb_sum_length hos]
      exact Nat.mul_le_mul_left _ (sb_length_le_of_sub hJ.win.nodup hPv.win.nodup hw)
    · intro x hx
      obtain ⟨l, hl, hxl⟩ := List.mem_flatten.1 hx
      obtain rfl := List.eq_of_mem_replicate hl
      obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hxl
      have hoW : ∀ i ∈ o, i ∈ wP.1 := fun i hi => hw i (sb_mem_win hos ho i hi)
      have hhalf : 2 * o.length ≤ wP.1.length := by
        refine sb_half_of_fix hhint hPgs hPv.win hPv.invariant htr (hKs.trans hKG) ?_
          (hseq o ho).1 hoW ?_
        · intro h hh u hu
          rw [hKden] at hh
          exact hh.2 u hu
        · intro i hi j hj
          exact ((hos.2 o ho).2 i hi j).1 hj
      exact ⟨by change o.length ≤ wP.1.length; omega, Or.inr ⟨rfl, hhalf⟩⟩
    · intro x hx
      obtain ⟨l, hl, hxl⟩ := List.mem_flatten.1 hx
      obtain rfl := List.eq_of_mem_replicate hl
      obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hxl
      exact List.length_pos_of_ne_nil (hos.2 o ho).1

/-- **M3**: the kernel reduction of a hinted instance `(G, W, L)` itself. The children are the
kernel's orbits on `W`, without a hint and with at most `|W|/2` points each (`StepChild`), one
set per coset of the kernel; there are `|ψ(G)| ≤ m!` cosets. -/
theorem RunsWithin.m3Prog (hO : MeetsContractOn DV kerRedOps X.O)
    (hPre : ∀ op x, kerRedOps op → GroupPre DV op x → X.Pre op x)
    {sub : HInstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)}
    {xy : StrData × StrData} {w : WinData} {σd : PermData} {N : ℕ} {gs : GensData}
    {d : D.denote} {n₀ n : ℕ} {L : LabelData}
    (hI : HInstValid DV (((xy, w, σd, N, gs, d), n₀, n, some L) : HInstData D))
    {C : ℕ → Option ℕ → ℕ} {s Bk Bo Bcr Bgen : ℕ}
    (hsub : HSubSolves X body DV sub
      (fun J => SizeChild (max s (kerModel X.O n (N, gs, d)).2.1.length)
          (((xy, w, σd, N, gs, d), n₀, n, some L) : HInstData D) J ∧
        StepChild w.1.length (N - n) (J.winSize, J.baseOpt)) C s)
    (hBk : X.B.call GroupOp.kernel ((N, gs, d), baseWin n N) (kerModel X.O n (N, gs, d)) ≤ Bk)
    (hBo : X.B.call GroupOp.orbits (kerModel X.O n (N, gs, d), w)
      (krOrbits X.O n (N, gs, d) w) ≤ Bo)
    (hBcr : X.B.call GroupOp.cosetReps ((N, gs, d), kerModel X.O n (N, gs, d))
      (kerReps X.O n (N, gs, d)) ≤ Bcr)
    (hB : ∀ hs : GensData, GensData.AllValid N hs →
      hs.length ≤ (kerReps X.O n (N, gs, d)).length *
        (max s (kerModel X.O n (N, gs, d)).2.1.length + 1) →
      GensData.denote N hs ≤ GensData.denote N gs →
      X.B.call GroupOp.generate (N, hs) (X.O.run GroupOp.generate (N, hs)) ≤ Bgen) :
    ∃ (ans : AnswerData D) (ch : List (ℕ × Option ℕ)),
      RunsWithin X body
        (Main.m3Prog sub (((xy, w, σd, N, gs, d), n₀, n, some L) : HInstData D)) ans
        ((ch.map fun x => C x.1 x.2).sum +
          (kerRedCost N n w.1.length (kerReps X.O n (N, gs, d)).length
            (kerModel X.O n (N, gs, d)).2.1.length s Bk Bo Bcr Bgen + 5)) ∧
      InstData.OK (D := D) (xy, w, σd, N, gs, d) DV ans ∧
      (∀ sGen, (∀ hs, GensData.AllValid N hs → GensData.denote N hs ≤ GensData.denote N gs →
          (X.O.run GroupOp.generate (N, hs)).2.1.length ≤ sGen) →
        ∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sGen) ∧
      ChildList w.1.length (kerReps X.O n (N, gs, d)).length
        (StepChild w.1.length (N - n)) ch ∧
      (kerReps X.O n (N, gs, d)).length ≤ (N - n).factorial := by
  obtain ⟨ans, ch, hrun, hok, hgen, hch, hfact⟩ := RunsWithin.kerRedProg hO hPre hI hI.valid
    le_rfl (fun _ h => h) hsub hBk hBo hBcr hB
  refine ⟨ans, ch, ?_, hok, hgen, hch, hfact⟩
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact hrun
  case hc =>
    simp only [Prim.cost]
    omega

end Specs

/-! ### Well-formedness -/

section Wf

variable {D : Ty} {S : Signature} {rec : Ty × Ty} {var₁ var₂ : Ty → Type} {r : Bool}
  {Γ : WfCtx var₁ var₂}

theorem wf_plainProg {n₀₁ n₁ : var₁ .nat} {n₀₂ n₂ : var₂ .nat} {J₁ : var₁ (Ty.inst D)}
    {J₂ : var₂ (Ty.inst D)} (hn₀ : ⟨.nat, n₀₁, n₀₂⟩ ∈ Γ) (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ)
    (hJ : ⟨Ty.inst D, J₁, J₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (plainProg n₀₁ n₁ J₁) (plainProg n₀₂ n₂ J₂) := by
  unfold plainProg
  refine .bind (.prim _ .nil) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp [hn]) (.cons (List.Mem.head _) .nil))) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp [hn₀]) (.cons (List.Mem.head _) .nil))) fun _ _ => ?_
  exact .prim _ (.cons (by simp [hJ]) (.cons (List.Mem.head _) .nil))

theorem wf_plainSub {sub₁ : var₁ (hinstTy D) → Prog S rec var₁ (Ty.answer D)}
    {sub₂ : var₂ (hinstTy D) → Prog S rec var₂ (Ty.answer D)} (hsub : WfFun r Γ sub₁ sub₂)
    {n₀₁ n₁ : var₁ .nat} {n₀₂ n₂ : var₂ .nat} (hn₀ : ⟨.nat, n₀₁, n₀₂⟩ ∈ Γ)
    (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) :
    WfFun r Γ (plainSub sub₁ n₀₁ n₁) (plainSub sub₂ n₀₂ n₂) := by
  intro Γ' hΓ J₁ J₂ hJ
  unfold plainSub
  exact .bind (wf_plainProg (hΓ hn₀) (hΓ hn) hJ) fun _ _ =>
    hsub _ (fun y hy => List.mem_cons_of_mem _ (hΓ hy)) _ _ (List.Mem.head _)

theorem wf_fixedTestProg {I₁ : var₁ (hinstTy D)} {I₂ : var₂ (hinstTy D)}
    (hI : ⟨hinstTy D, I₁, I₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (fixedTestProg I₁) (fixedTestProg I₂) := by
  unfold fixedTestProg
  refine .bind (.prim _ (.cons hI .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  exact wf_fixesProg (by simp) (List.Mem.head _)

theorem wf_fixedStepProg {I₁ : var₁ (hinstTy D)} {I₂ : var₂ (hinstTy D)}
    (hI : ⟨hinstTy D, I₁, I₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (fixedStepProg I₁) (fixedStepProg I₂) := by
  unfold fixedStepProg
  refine .bind (.prim _ (.cons hI .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (wf_matchesProg (List.Mem.head _) (by simp) (by simp)) fun _ _ => ?_
  exact .ite (List.Mem.head _) (.prim _ (.cons (by simp) .nil)) (.prim _ .nil)

theorem wf_winOrbitsProg {I₁ : var₁ (hinstTy D)} {I₂ : var₂ (hinstTy D)}
    (hI : ⟨hinstTy D, I₁, I₂⟩ ∈ Γ) :
    Prog.Wf (rec := rec) r Γ (winOrbitsProg I₁) (winOrbitsProg I₂) := by
  unfold winOrbitsProg
  refine .bind (.prim _ (.cons hI .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) (.cons (by simp) .nil))) fun _ _ => ?_
  exact .call _ (List.Mem.head _)

theorem wf_chainProg {sub₁ : var₁ (hinstTy D) → Prog S rec var₁ (Ty.answer D)}
    {sub₂ : var₂ (hinstTy D) → Prog S rec var₂ (Ty.answer D)} (hsub : WfFun r Γ sub₁ sub₂)
    {I₁ : var₁ (hinstTy D)} {I₂ : var₂ (hinstTy D)} {os₁ : var₁ (.list (.list .nat))}
    {os₂ : var₂ (.list (.list .nat))} (hI : ⟨hinstTy D, I₁, I₂⟩ ∈ Γ)
    (hos : ⟨.list (.list .nat), os₁, os₂⟩ ∈ Γ) :
    Prog.Wf r Γ (chainProg sub₁ I₁ os₁) (chainProg sub₂ I₂ os₂) := by
  unfold chainProg
  refine .bind (.prim _ (.cons hI .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp [hI]) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine wf_seqProg (wf_plainSub (hsub.mono fun y hy => by simp [hy]) (by simp) (by simp))
    (by simp) (List.Mem.head _) (by simp [hos])

theorem wf_kerRedProg {sub₁ : var₁ (hinstTy D) → Prog (groupSig D) rec var₁ (Ty.answer D)}
    {sub₂ : var₂ (hinstTy D) → Prog (groupSig D) rec var₂ (Ty.answer D)}
    (hsub : WfFun r Γ sub₁ sub₂) {n₀₁ n₁ : var₁ .nat} {n₀₂ n₂ : var₂ .nat}
    {J₁ : var₁ (Ty.inst D)} {J₂ : var₂ (Ty.inst D)} (hn₀ : ⟨.nat, n₀₁, n₀₂⟩ ∈ Γ)
    (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (hJ : ⟨Ty.inst D, J₁, J₂⟩ ∈ Γ) :
    Prog.Wf r Γ (kerRedProg sub₁ n₀₁ n₁ J₁) (kerRedProg sub₂ n₀₂ n₂ J₂) := by
  unfold kerRedProg
  refine .bind (.prim _ (.cons hJ .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp [hJ]) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (wf_baseWinProg (by simp [hn]) (List.Mem.head _)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) (.cons (List.Mem.head _) .nil))) fun _ _ => ?_
  refine .bind (.call _ (List.Mem.head _)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) (.cons (by simp) .nil))) fun _ _ => ?_
  refine .bind (.call _ (List.Mem.head _)) fun _ _ => ?_
  exact wf_blockProg (wf_plainSub (hsub.mono fun y hy => by simp [hy]) (by simp [hn₀])
    (by simp [hn])) (by simp) (by simp) (by simp) (by simp)
    (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (List.Mem.head _)

theorem wf_m3Prog {sub₁ : var₁ (hinstTy D) → Prog (groupSig D) rec var₁ (Ty.answer D)}
    {sub₂ : var₂ (hinstTy D) → Prog (groupSig D) rec var₂ (Ty.answer D)}
    (hsub : WfFun r Γ sub₁ sub₂) {I₁ : var₁ (hinstTy D)} {I₂ : var₂ (hinstTy D)}
    (hI : ⟨hinstTy D, I₁, I₂⟩ ∈ Γ) :
    Prog.Wf r Γ (m3Prog sub₁ I₁) (m3Prog sub₂ I₂) := by
  unfold m3Prog
  refine .bind (.prim _ (.cons hI .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp [hI]) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  exact wf_kerRedProg (hsub.mono fun y hy => by simp [hy]) (by simp) (List.Mem.head _) (by simp)

end Wf

end GraphIso.Main
