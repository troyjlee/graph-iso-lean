module

public import GraphIso.Main.Transfer
public import GraphIso.Main.StepsBase

/-!
# The free coarsenings as steps: M0, M1 and M2a

Stage 14j-2, item 5 (`PLAN-14.md` §14.2). Each step re-bases the group of a hinted instance onto
a coarser base (stage 14j-1's `m0Prog`, `m1Prog`, `m2aProg`) and solves the instance through the
re-based child (`viaChildProg`: the child instance, one call of the hinted sub-solver `sub`, and
the answer transfer). There is one child, on the same window; it has a hint and a base that
shrinks (`FreeChild`, the hypothesis of `pot_free`), and it keeps the size facts (`SizeChild`).

* **M0** (`m0StepProg`): no hint, the group transitive on a window of at least two points. The
  maximal blocks of the window become the base; the child has `k ≤ |W|` base points, so its
  base is smaller than the `2|W| + 1` charged without a hint, and its degree `n + k ≤ 2n`.
* **M1** (`m1StepProg`): a hint `L`, and the base action intransitive (the case condition). An
  orbit of the base action on which the labels are not constant becomes the base: `k < m`.
* **M2a** (`m2aStepProg`): a hint `L`, the base action transitive, its maximal blocks `bs`
  proper (`blkOKD`), and some window label not equidistributed over them (`neqD`). The blocks
  become the base, with the block labels: `2k ≤ m`.

The case conditions are hypotheses of the specs; the dispatcher of stage 14j-5 decides them on
data. `RunsWithin.m0StepProg`, `RunsWithin.m1StepProg`, `RunsWithin.m2aStepProg`: the run within
the child's cost `C x.1 x.2` plus the work (the coarsening, building the child, the transfer),
an answer correct for the instance, the generator bound of the transfer, and the children
(`ChildList` with `c = 1`; the window is nonempty, by `2 ≤ |W|` for M0 and by the hint for M1
and M2a). The child's group is the coarsening's re-based group, so the sub-solver is asked only
for children with at most its number of generators (`SizeChild`, stage 14j-5a). The backend
charges are hypotheses on the specific calls (the
coarsenings' `orbits` and `generate`), and on bounded inputs for the transfer's `lift` and
`generate`, as in `RunsWithin.viaChildProg`.
-/

@[expose] public section

namespace GraphIso.Main

open Equiv Cost GraphIso GraphIso.Programs GraphIso.Toolkit GraphIso.Recursion

/-- The backend operations of the free steps. -/
def hintStepOps (op : GroupOp) : Prop := op = .orbits ∨ op = .lift ∨ op = .generate

theorem hintStepOps_of_transfer {op : GroupOp} (h : transferOps op) : hintStepOps op := by
  rcases h with h | h <;> simp [hintStepOps, h]

theorem hintStepOps_of_rebase {op : GroupOp} (h : rebaseOps op) : hintStepOps op := by
  simp [hintStepOps, show op = .generate from h]

theorem hintStepOps_of_m1 {op : GroupOp} (h : m1Ops op) : hintStepOps op := by
  rcases h with h | h <;> simp [hintStepOps, h]

/-! ### Programs -/

section Programs

variable {D : Ty} {rec : Ty × Ty} {var : Ty → Type}

/-- **Solve through a coarsening's output** `(G', (w', L'))`: the child with the labels `L'`. -/
def childOfProg (sub : var (hinstTy D) → Prog (groupSig D) rec var (Ty.answer D))
    (xy : var Ty.strs) (σ : var Ty.perm) (K : var (Ty.group D)) (n₀ n : var .nat)
    (r : var (.prod (Ty.group D) (.prod Ty.win (.array (.list .nat))))) :
    Prog (groupSig D) rec var (Ty.answer D) :=
  .bind (.op1 .fst r) fun G' => .bind (.op1 .snd r) fun wl =>
  .bind (.op1 .fst wl) fun w' => .bind (.op1 .snd wl) fun L' =>
  .bind (.op1 .some L') fun oL => viaChildProg sub xy σ K n₀ n G' w' oL

/-- **M0 as a step**: re-base onto the maximal blocks of the window, and solve through the
child. -/
def m0StepProg (sub : var (hinstTy D) → Prog (groupSig D) rec var (Ty.answer D))
    (I : var (hinstTy D)) : Prog (groupSig D) rec var (Ty.answer D) :=
  .bind (.op1 .fst I) fun J => .bind (.op1 .snd I) fun r₁ =>
  .bind (.op1 .fst r₁) fun n₀ => .bind (.op1 .snd r₁) fun r₂ => .bind (.op1 .fst r₂) fun n =>
  .bind (.op1 .fst J) fun xy => .bind (.op1 .snd J) fun wc =>
  .bind (.op1 .fst wc) fun w => .bind (.op1 .snd wc) fun c =>
  .bind (.op1 .fst c) fun σ => .bind (.op1 .snd c) fun K =>
  .bind (.op1 .fst K) fun N => .bind (.op1 .snd K) fun kd => .bind (.op1 .fst kd) fun gs =>
  .bind (m0Prog n N gs w) fun r => childOfProg sub xy σ K n₀ n r

/-- **M1 as a step**: re-base onto an orbit of the base action with non-constant labels `L`, and
solve through the child. -/
def m1StepProg (sub : var (hinstTy D) → Prog (groupSig D) rec var (Ty.answer D))
    (I : var (hinstTy D)) (L : var (.array (.list .nat))) :
    Prog (groupSig D) rec var (Ty.answer D) :=
  .bind (.op1 .fst I) fun J => .bind (.op1 .snd I) fun r₁ =>
  .bind (.op1 .fst r₁) fun n₀ => .bind (.op1 .snd r₁) fun r₂ => .bind (.op1 .fst r₂) fun n =>
  .bind (.op1 .fst J) fun xy => .bind (.op1 .snd J) fun wc =>
  .bind (.op1 .fst wc) fun w => .bind (.op1 .snd wc) fun c =>
  .bind (.op1 .fst c) fun σ => .bind (.op1 .snd c) fun K =>
  .bind (.op1 .fst K) fun N =>
  .bind (m1Prog n N K w L) fun r => childOfProg sub xy σ K n₀ n r

/-- **M2a as a step**: re-base onto the blocks `bs` of the base, with the block labels of `L`,
and solve through the child. -/
def m2aStepProg (sub : var (hinstTy D) → Prog (groupSig D) rec var (Ty.answer D))
    (I : var (hinstTy D)) (L : var (.array (.list .nat))) (bs : var (.list (.list .nat))) :
    Prog (groupSig D) rec var (Ty.answer D) :=
  .bind (.op1 .fst I) fun J => .bind (.op1 .snd I) fun r₁ =>
  .bind (.op1 .fst r₁) fun n₀ => .bind (.op1 .snd r₁) fun r₂ => .bind (.op1 .fst r₂) fun n =>
  .bind (.op1 .fst J) fun xy => .bind (.op1 .snd J) fun wc =>
  .bind (.op1 .fst wc) fun w => .bind (.op1 .snd wc) fun c =>
  .bind (.op1 .fst c) fun σ => .bind (.op1 .snd c) fun K =>
  .bind (.op1 .fst K) fun N => .bind (.op1 .snd K) fun kd => .bind (.op1 .fst kd) fun gs =>
  .bind (m2aProg n N gs w L bs) fun r => childOfProg sub xy σ K n₀ n r

end Programs

/-! ### Costs -/

/-- The work of `m0StepProg` at degree `N`, string positions `[0, n)`, `p` window points, `s₀`
generators, the re-basing charge `Bgen₀`, and the transfer's `s`, `Blift`, `Bgen`. -/
def m0StepCost (n N p s₀ s Bgen₀ Blift Bgen : ℕ) : ℕ :=
  m0Cost n N p s₀ Bgen₀ + viaChildCost N (n + p) n s Blift Bgen + 20

/-- The work of `m1StepProg`, with M1's charges `Borb`, `Bgen₁`. -/
def m1StepCost (n N p s₀ s Borb Bgen₁ Blift Bgen : ℕ) : ℕ :=
  m1Cost n N p s₀ Borb Bgen₁ + viaChildCost N N n s Blift Bgen + 20

/-- The work of `m2aStepProg`, with a label array of size `Ls` and the re-basing charge
`Bgen₂`. -/
def m2aStepCost (n N p s₀ s Ls Bgen₂ Blift Bgen : ℕ) : ℕ :=
  m2aCost n N p s₀ Ls Bgen₂ + viaChildCost N N n s Blift Bgen + 20

theorem viaChildCost_mono {N N₁ N₂ n s Blift Bgen : ℕ} (h : N₁ ≤ N₂) :
    viaChildCost N N₁ n s Blift Bgen ≤ viaChildCost N N₂ n s Blift Bgen := by
  simp only [viaChildCost, transferCost]
  omega

/-! ### Specs -/

section Specs

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}

/-- The window of a hinted instance has at most `n` points. -/
theorem sh_length_le {xy : StrData × StrData} {w : WinData} {σd : PermData} {N : ℕ}
    {gs : GensData} {d : D.denote} {n₀ n : ℕ} {lab : Option LabelData}
    (hI : HInstValid DV (((xy, w, σd, N, gs, d), n₀, n, lab) : HInstData D)) :
    w.1.length ≤ n :=
  mf_length_le_of_nodup hI.valid.win.nodup hI.win_lt

/-- **The common tail**: solve the instance through a coarsening's output `r = (G', (w', L'))`
on the same window, given the facts the coarsenings' specs state at the degree `n + k`: valid
group data, valid hint data on a valid invariant window where the child is transitive,
faithfulness on the string positions, and an isomorphism with `K = ⟨gs⟩` keeping the action on
them. -/
theorem sh_childOf (hO : MeetsContractOn DV transferOps X.O)
    (hPre : ∀ op x, transferOps op → GroupPre DV op x → X.Pre op x)
    {sub : HInstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)}
    {P : HInstData D → Prop} {C : ℕ → Option ℕ → ℕ} {s : ℕ}
    (hsub : HSubSolves X body DV sub P C s)
    {xy : StrData × StrData} {w : WinData} {σd : PermData} {N : ℕ} {gs : GensData}
    {d : D.denote} {n₀ n : ℕ} {lab : Option LabelData}
    (hI : HInstValid DV (((xy, w, σd, N, gs, d), n₀, n, lab) : HInstData D)) (hn : n ≤ N)
    {r : GroupData D.denote × (WinData × LabelData)} {k : ℕ}
    (hdeg : r.1.1 = n + k) (hval : GroupValid DV (n + k) r.1.2.1 r.1.2.2)
    (hhint : HintValid n (n + k) r.1.2.1 r.2.1 r.2.2)
    (hfa : ∀ g ∈ GensData.denote (n + k) r.1.2.1,
      (∀ j : Fin (n + k), j.val < n → g j = j) → g = 1)
    (hwv : r.2.1.Valid (n + k))
    (hinv : IsInvariant (GensData.denote (n + k) r.1.2.1) (r.2.1.denote (n + k)))
    (htr : IsTransOn (GensData.denote (n + k) r.1.2.1) (r.2.1.denote (n + k)))
    (hθ : ∃ θ : ↥(GensData.denote N gs) ≃* ↥(GensData.denote (n + k) r.1.2.1),
      ∀ (g : ↥(GensData.denote N gs)) (j : ℕ) (hj : j < n),
        ((θ g : Perm (Fin (n + k))) ⟨j, by omega⟩).val = (g.1 ⟨j, by omega⟩).val)
    (hw : r.2.1.1 = w.1)
    (hP : P (childHInst xy.1 xy.2 σd n₀ n r.1 r.2.1 (some r.2.2)))
    {Blift Bgen : ℕ}
    (hBlift : ∀ π' : PermData, π'.Valid n →
      X.B.call GroupOp.lift ((N, gs, d), (strWin N n, π'))
        (X.O.run GroupOp.lift ((N, gs, d), (strWin N n, π'))) ≤ Blift)
    (hBgen : ∀ hs : GensData, GensData.AllValid N hs → hs.length ≤ s →
      GensData.denote N hs ≤ GensData.denote N gs →
      X.B.call GroupOp.generate (N, hs) (X.O.run GroupOp.generate (N, hs)) ≤ Bgen) :
    ∃ ans : AnswerData D,
      RunsWithin X body (Main.childOfProg sub xy σd (N, gs, d) n₀ n r) ans
        (C w.1.length (some k) + viaChildCost N (n + k) n s Blift Bgen + 5) ∧
      InstData.OK (D := D) (xy, w, σd, N, gs, d) DV ans ∧
      ∀ sGen, (∀ hs, GensData.AllValid N hs → GensData.denote N hs ≤ GensData.denote N gs →
          (X.O.run GroupOp.generate (N, hs)).2.1.length ≤ sGen) →
        ∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sGen := by
  obtain ⟨θ, hθ⟩ := hθ
  have hc : ChildRel DV n N gs r.1.1 r.1.2.1 r.1.2.2 r.2.1 := by
    rw [hdeg]
    exact ⟨hval, by omega, hhint.base_inv, hwv, hhint.win_lt, hinv, hfa,
      ⟨θ, fun g j _ _ hjn => hθ g j hjn⟩⟩
  have hL' : ∀ L, some r.2.2 = some L →
      HintValid n r.1.1 r.1.2.1 r.2.1 L ∧
        IsTransOn (GensData.denote r.1.1 r.1.2.1) (r.2.1.denote r.1.1) := by
    rintro L ⟨⟩
    rw [hdeg]
    exact ⟨hhint, htr⟩
  have hK : GroupValid DV N gs d := hI.valid.group
  have hKb : IsInvariant (GensData.denote N gs) (baseSet n N) := hI.base_inv
  have hσ : σd.Valid N := hI.valid.rep
  obtain ⟨ans, hrun, hok, hg⟩ := RunsWithin.viaChildProg (X := X) (body := body) hO hPre hsub
    hK hn hKb hσ xy hc hL' hP hBlift hBgen
  refine ⟨ans, ?_, ?_, hg⟩
  · apply RunsWithin.mono
    case h =>
      unfold Main.childOfProg
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      exact hrun
    case hc =>
      simp only [Prim.cost, Option.map_some, hw, hdeg, Nat.add_sub_cancel_left]
      omega
  · have e : ptsSet N r.2.1.1 = w.denote N := by rw [hw]; rfl
    rw [e] at hok
    exact hok

/-- **M0 as a step.** For a valid instance without a hint whose group is transitive on a window
of at least two points: the answer through the child re-based onto the maximal blocks of the
window, one `FreeChild` child with base `k ≤ |W| < 2|W| + 1`. -/
theorem RunsWithin.m0StepProg (hO : MeetsContractOn DV hintStepOps X.O)
    (hPre : ∀ op x, hintStepOps op → GroupPre DV op x → X.Pre op x)
    {sub : HInstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)}
    {xy : StrData × StrData} {w : WinData} {σd : PermData} {N : ℕ} {gs : GensData}
    {d : D.denote} {n₀ n : ℕ}
    (hI : HInstValid DV (((xy, w, σd, N, gs, d), n₀, n, none) : HInstData D))
    (htr : IsTransOn (GensData.denote N gs) (w.denote N)) (h2 : 2 ≤ w.1.length)
    {C : ℕ → Option ℕ → ℕ} {s : ℕ}
    (hsub : HSubSolves X body DV sub
      (fun J => SizeChild (rebaseModel X.O n N (Luks.maxBlocks N gs w.1) gs).2.1.length
          (((xy, w, σd, N, gs, d), n₀, n, none) : HInstData D) J ∧
        FreeChild w.1.length (2 * w.1.length + 1) (J.winSize, J.baseOpt)) C s)
    {Bgen₀ Blift Bgen : ℕ}
    (hB : X.B.call GroupOp.generate (n + (Luks.maxBlocks N gs w.1).length,
        rebaseGens n N (Luks.maxBlocks N gs w.1) gs)
      (rebaseModel X.O n N (Luks.maxBlocks N gs w.1) gs) ≤ Bgen₀)
    (hBlift : ∀ π' : PermData, π'.Valid n →
      X.B.call GroupOp.lift ((N, gs, d), (strWin N n, π'))
        (X.O.run GroupOp.lift ((N, gs, d), (strWin N n, π'))) ≤ Blift)
    (hBgen : ∀ hs : GensData, GensData.AllValid N hs → hs.length ≤ s →
      GensData.denote N hs ≤ GensData.denote N gs →
      X.B.call GroupOp.generate (N, hs) (X.O.run GroupOp.generate (N, hs)) ≤ Bgen) :
    ∃ (ans : AnswerData D) (ch : List (ℕ × Option ℕ)),
      RunsWithin X body
        (Main.m0StepProg sub (((xy, w, σd, N, gs, d), n₀, n, none) : HInstData D)) ans
        ((ch.map fun x => C x.1 x.2).sum +
          m0StepCost n N w.1.length gs.length s Bgen₀ Blift Bgen) ∧
      InstData.OK (D := D) (xy, w, σd, N, gs, d) DV ans ∧
      (∀ sGen, (∀ hs, GensData.AllValid N hs → GensData.denote N hs ≤ GensData.denote N gs →
          (X.O.run GroupOp.generate (N, hs)).2.1.length ≤ sGen) →
        ∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sGen) ∧
      ChildList w.1.length 1 (FreeChild w.1.length (2 * w.1.length + 1)) ch := by
  have hn : n ≤ N := hI.le
  have hbase : IsInvariant (GensData.denote N gs) (baseSet n N) := hI.base_inv
  have hwv0 : w.Valid N := hI.valid.win
  have hwin : ∀ i ∈ w.1, i < n := hI.win_lt
  have hgv : GroupValid DV N gs d := hI.valid.group
  have hinv0 : IsInvariant (GensData.denote N gs) (w.denote N) := hI.valid.invariant
  have hfa0 : ∀ g ∈ GensData.denote N gs, (∀ j : Fin N, j.val < n → g j = j) → g = 1 :=
    hI.faithful
  have hwn := sh_length_le hI
  obtain ⟨hrun0, hdeg, hval, hhint, hfa, hwv, hinv, htr', h2k, hkw, hθ⟩ :=
    RunsWithin.m0Prog (X := X) (body := body) (DV := DV)
      (fun op x hop hx => hO op x (hintStepOps_of_rebase hop) hx)
      (fun op x hop hx => hPre op x (hintStepOps_of_rebase hop) hx) hn hbase hwv0
      hwin hgv.1 hinv0 hfa0 htr h2 hB
  have hw' : (m0Model X.O n N gs w).2.1.1 = w.1 := WinData.ofPoints_fst _ _
  obtain ⟨ans, hrun, hok, hg⟩ := sh_childOf (X := X) (body := body)
    (fun op x hop hx => hO op x (hintStepOps_of_transfer hop) hx)
    (fun op x hop hx => hPre op x (hintStepOps_of_transfer hop) hx) hsub hI hn
    (r := m0Model X.O n N gs w) hdeg hval hhint hfa hwv hinv htr' hθ hw'
    (by
      refine ⟨⟨rfl, le_rfl, ?_, le_rfl, fun hI' => childHInst_labInv hI'.n_le
        (LabInvAt.of_le_one ?_ (labLen_labM0D _ _))⟩, ?_⟩
      · show (m0Model X.O n N gs w).1.1 ≤ max N (2 * n)
        rw [hdeg]
        omega
      · have := hI'.n_le
        change n ≤ n₀ at this
        rw [hdeg]
        omega
      · show FreeChild w.1.length (2 * w.1.length + 1)
          ((m0Model X.O n N gs w).2.1.1.length, some ((m0Model X.O n N gs w).1.1 - n))
        rw [hw', hdeg]
        exact ⟨by omega, Or.inl ⟨_, rfl, by omega, by omega⟩⟩)
    hBlift hBgen
  refine ⟨ans, [(w.1.length, some (Luks.maxBlocks N gs w.1).length)], ?_, hok, hg, ?_⟩
  · apply RunsWithin.mono
    case h =>
      unfold Main.m0StepProg
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
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step hrun0
      exact hrun
    case hc =>
      have hmono := viaChildCost_mono (N := N) (n := n) (s := s) (Blift := Blift) (Bgen := Bgen)
        (show n + (Luks.maxBlocks N gs w.1).length ≤ n + w.1.length by omega)
      clear * - hmono
      simp only [Prim.cost, m0StepCost, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil]
      omega
  · refine ⟨by simp, ?_, ?_⟩
    · intro x hx
      simp only [List.mem_singleton] at hx
      subst hx
      exact ⟨by omega, Or.inl ⟨_, rfl, by omega, by omega⟩⟩
    · intro x hx
      simp only [List.mem_singleton] at hx
      subst hx
      change 1 ≤ w.1.length
      omega

/-- **M1 as a step.** For a valid instance with the hint `L` whose base action is intransitive:
the answer through the child re-based onto an orbit of the base action with non-constant
labels, one `FreeChild` child with base `k < m`. -/
theorem RunsWithin.m1StepProg (hO : MeetsContractOn DV hintStepOps X.O)
    (hPre : ∀ op x, hintStepOps op → GroupPre DV op x → X.Pre op x)
    {sub : HInstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)}
    {xy : StrData × StrData} {w : WinData} {σd : PermData} {N : ℕ} {gs : GensData}
    {d : D.denote} {n₀ n : ℕ} {L : LabelData}
    (hI : HInstValid DV (((xy, w, σd, N, gs, d), n₀, n, some L) : HInstData D))
    (hnt : ¬ IsTransOn (GensData.denote N gs) (baseSet n N))
    {C : ℕ → Option ℕ → ℕ} {s : ℕ}
    (hsub : HSubSolves X body DV sub
      (fun J => SizeChild
          (rebaseModel X.O n N (singD (m1O X.O n N (N, gs, d) w L)) gs).2.1.length
          (((xy, w, σd, N, gs, d), n₀, n, some L) : HInstData D) J ∧
        FreeChild w.1.length (N - n) (J.winSize, J.baseOpt)) C s)
    {Borb Bgen₁ Blift Bgen : ℕ}
    (hBo : X.B.call GroupOp.orbits ((N, gs, d), baseWin n N)
      (X.O.run GroupOp.orbits ((N, gs, d), baseWin n N)) ≤ Borb)
    (hB : X.B.call GroupOp.generate (n + (singD (m1O X.O n N (N, gs, d) w L)).length,
        rebaseGens n N (singD (m1O X.O n N (N, gs, d) w L)) gs)
      (rebaseModel X.O n N (singD (m1O X.O n N (N, gs, d) w L)) gs) ≤ Bgen₁)
    (hBlift : ∀ π' : PermData, π'.Valid n →
      X.B.call GroupOp.lift ((N, gs, d), (strWin N n, π'))
        (X.O.run GroupOp.lift ((N, gs, d), (strWin N n, π'))) ≤ Blift)
    (hBgen : ∀ hs : GensData, GensData.AllValid N hs → hs.length ≤ s →
      GensData.denote N hs ≤ GensData.denote N gs →
      X.B.call GroupOp.generate (N, hs) (X.O.run GroupOp.generate (N, hs)) ≤ Bgen) :
    ∃ (ans : AnswerData D) (ch : List (ℕ × Option ℕ)),
      RunsWithin X body
        (Main.m1StepProg sub (((xy, w, σd, N, gs, d), n₀, n, some L) : HInstData D) L) ans
        ((ch.map fun x => C x.1 x.2).sum +
          m1StepCost n N w.1.length gs.length s Borb Bgen₁ Blift Bgen) ∧
      InstData.OK (D := D) (xy, w, σd, N, gs, d) DV ans ∧
      (∀ sGen, (∀ hs, GensData.AllValid N hs → GensData.denote N hs ≤ GensData.denote N gs →
          (X.O.run GroupOp.generate (N, hs)).2.1.length ≤ sGen) →
        ∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sGen) ∧
      ChildList w.1.length 1 (FreeChild w.1.length (N - n)) ch := by
  have hn : n ≤ N := hI.le
  have hbase : IsInvariant (GensData.denote N gs) (baseSet n N) := hI.base_inv
  have hwv0 : w.Valid N := hI.valid.win
  have hwin : ∀ i ∈ w.1, i < n := hI.win_lt
  have hgv : GroupValid DV N gs d := hI.valid.group
  have hinv0 : IsInvariant (GensData.denote N gs) (w.denote N) := hI.valid.invariant
  have hfa0 : ∀ g ∈ GensData.denote N gs, (∀ j : Fin N, j.val < n → g j = j) → g = 1 :=
    hI.faithful
  have hLv : HintValid n N gs w L := (hI.hint L rfl).1
  have htr : IsTransOn (GensData.denote N gs) (w.denote N) := (hI.hint L rfl).2
  obtain ⟨hrun0, hdeg, hval, hhint, hfa, hwv, hinv, htr', hkm, hlt, hθ⟩ :=
    RunsWithin.m1Prog (X := X) (body := body) (DV := DV)
      (fun op x hop hx => hO op x (hintStepOps_of_m1 hop) hx)
      (fun op x hop hx => hPre op x (hintStepOps_of_m1 hop) hx) hgv hwv0 hinv0
      hfa0 htr hLv hBo hB
  have hk := hlt hnt
  have hw' : (m1Model X.O n N (N, gs, d) w L).2.1.1 = w.1 := WinData.ofPoints_fst _ _
  obtain ⟨ans, hrun, hok, hg⟩ := sh_childOf (X := X) (body := body)
    (fun op x hop hx => hO op x (hintStepOps_of_transfer hop) hx)
    (fun op x hop hx => hPre op x (hintStepOps_of_transfer hop) hx) hsub hI hn
    (r := m1Model X.O n N (N, gs, d) w L) hdeg hval hhint hfa hwv hinv htr' hθ hw'
    (by
      refine ⟨⟨rfl, le_rfl, ?_, le_rfl, fun hI' => childHInst_labInv hI'.n_le
        ((hI'.hint L rfl).mono ?_ ?_)⟩, ?_⟩
      · show (m1Model X.O n N (N, gs, d) w L).1.1 ≤ max N (2 * n)
        rw [hdeg]
        omega
      · show (m1Model X.O n N (N, gs, d) w L).1.1 - n ≤ N - n
        rw [hdeg]
        omega
      · obtain ⟨hOnd, hOn⟩ := m1O_facts (X := X) (fun op x hop hx => hO op x
          (hintStepOps_of_m1 hop) hx) hgv hLv
        exact labLen_labM1D_le hOnd hOn L w.2
      · show FreeChild w.1.length (N - n)
          ((m1Model X.O n N (N, gs, d) w L).2.1.1.length,
            some ((m1Model X.O n N (N, gs, d) w L).1.1 - n))
        rw [hw', hdeg]
        exact ⟨by omega, Or.inl ⟨_, rfl, by omega, by omega⟩⟩)
    hBlift hBgen
  have hwp : 1 ≤ w.1.length := hI.win_pos rfl
  refine ⟨ans, [(w.1.length, some (singD (m1O X.O n N (N, gs, d) w L)).length)], ?_, hok, hg,
    ?_⟩
  · apply RunsWithin.mono
    case h =>
      unfold Main.m1StepProg
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
      run_step (RunsWithin.prim _ _)
      run_step hrun0
      exact hrun
    case hc =>
      have hmono := viaChildCost_mono (N := N) (n := n) (s := s) (Blift := Blift) (Bgen := Bgen)
        (show n + (singD (m1O X.O n N (N, gs, d) w L)).length ≤ N by omega)
      clear * - hmono
      simp only [Prim.cost, m1StepCost, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil]
      omega
  · refine ⟨by simp, ?_, ?_⟩
    · intro x hx
      simp only [List.mem_singleton] at hx
      subst hx
      exact ⟨by omega, Or.inl ⟨_, rfl, by omega, by omega⟩⟩
    · intro x hx
      simp only [List.mem_singleton] at hx
      subst hx
      exact hwp

/-- **M2a as a step.** For a valid instance with the hint `L` whose base action is transitive,
with proper maximal blocks `mbD n N gs` (`blkOKD`) over which some window label is not
equidistributed (`neqD`): the answer through the child re-based onto the blocks with the block
labels, one `FreeChild` child with base `2k ≤ m`. -/
theorem RunsWithin.m2aStepProg (hO : MeetsContractOn DV hintStepOps X.O)
    (hPre : ∀ op x, hintStepOps op → GroupPre DV op x → X.Pre op x)
    {sub : HInstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)}
    {xy : StrData × StrData} {w : WinData} {σd : PermData} {N : ℕ} {gs : GensData}
    {d : D.denote} {n₀ n : ℕ} {L : LabelData}
    (hI : HInstValid DV (((xy, w, σd, N, gs, d), n₀, n, some L) : HInstData D))
    (htrB : IsTransOn (GensData.denote N gs) (baseSet n N))
    (hok : blkOKD (N - n) (mbD n N gs) = true) (hne : neqD n N (mbD n N gs) L w.1 = true)
    {C : ℕ → Option ℕ → ℕ} {s : ℕ}
    (hsub : HSubSolves X body DV sub
      (fun J => SizeChild (rebaseModel X.O n N (mbD n N gs) gs).2.1.length
          (((xy, w, σd, N, gs, d), n₀, n, some L) : HInstData D) J ∧
        FreeChild w.1.length (N - n) (J.winSize, J.baseOpt)) C s)
    {Bgen₂ Blift Bgen : ℕ}
    (hB : X.B.call GroupOp.generate (n + (mbD n N gs).length, rebaseGens n N (mbD n N gs) gs)
      (rebaseModel X.O n N (mbD n N gs) gs) ≤ Bgen₂)
    (hBlift : ∀ π' : PermData, π'.Valid n →
      X.B.call GroupOp.lift ((N, gs, d), (strWin N n, π'))
        (X.O.run GroupOp.lift ((N, gs, d), (strWin N n, π'))) ≤ Blift)
    (hBgen : ∀ hs : GensData, GensData.AllValid N hs → hs.length ≤ s →
      GensData.denote N hs ≤ GensData.denote N gs →
      X.B.call GroupOp.generate (N, hs) (X.O.run GroupOp.generate (N, hs)) ≤ Bgen) :
    ∃ (ans : AnswerData D) (ch : List (ℕ × Option ℕ)),
      RunsWithin X body
        (Main.m2aStepProg sub (((xy, w, σd, N, gs, d), n₀, n, some L) : HInstData D) L
          (mbD n N gs)) ans
        ((ch.map fun x => C x.1 x.2).sum +
          m2aStepCost n N w.1.length gs.length s L.size Bgen₂ Blift Bgen) ∧
      InstData.OK (D := D) (xy, w, σd, N, gs, d) DV ans ∧
      (∀ sGen, (∀ hs, GensData.AllValid N hs → GensData.denote N hs ≤ GensData.denote N gs →
          (X.O.run GroupOp.generate (N, hs)).2.1.length ≤ sGen) →
        ∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sGen) ∧
      ChildList w.1.length 1 (FreeChild w.1.length (N - n)) ch := by
  have hn : n ≤ N := hI.le
  have hbase : IsInvariant (GensData.denote N gs) (baseSet n N) := hI.base_inv
  have hwv0 : w.Valid N := hI.valid.win
  have hwin : ∀ i ∈ w.1, i < n := hI.win_lt
  have hgv : GroupValid DV N gs d := hI.valid.group
  have hinv0 : IsInvariant (GensData.denote N gs) (w.denote N) := hI.valid.invariant
  have hfa0 : ∀ g ∈ GensData.denote N gs, (∀ j : Fin N, j.val < n → g j = j) → g = 1 :=
    hI.faithful
  have hLv : HintValid n N gs w L := (hI.hint L rfl).1
  have htr : IsTransOn (GensData.denote N gs) (w.denote N) := (hI.hint L rfl).2
  obtain ⟨h2m, hh⟩ := blkOKD_iff.1 hok
  obtain ⟨hbs, hGb, hΨ, -, hsz⟩ := dv_blocks_facts hgv.1 hbase htrB h2m hh
  have htrB' := dv_baseHom_trans hbase htrB
  obtain ⟨u, hu, hu'⟩ := List.any_eq_true.1 hne
  have hne' : ∃ u ∈ w.1, equidistB (mbD n N gs).length (m2aIdx n N (mbD n N gs))
      (L.getD u []) = false := ⟨u, hu, by simpa using hu'⟩
  obtain ⟨hrun0, hdeg, hval, hhint, hfa, hwv, hinv, htr', h2k, hθ⟩ :=
    RunsWithin.m2aProg (X := X) (body := body) (DV := DV)
      (fun op x hop hx => hO op x (hintStepOps_of_rebase hop) hx)
      (fun op x hop hx => hPre op x (hintStepOps_of_rebase hop) hx) hgv.1 hwv0
      hinv0 hfa0 htr hLv hbs hGb hΨ htrB' hsz hne' hB
  have hw' : (m2aModel X.O n N gs w L (mbD n N gs)).2.1.1 = w.1 := WinData.ofPoints_fst _ _
  obtain ⟨ans, hrun, hok', hg⟩ := sh_childOf (X := X) (body := body)
    (fun op x hop hx => hO op x (hintStepOps_of_transfer hop) hx)
    (fun op x hop hx => hPre op x (hintStepOps_of_transfer hop) hx) hsub hI hn
    (r := m2aModel X.O n N gs w L (mbD n N gs)) hdeg hval hhint hfa hwv hinv htr' hθ hw'
    (by
      refine ⟨⟨rfl, le_rfl, ?_, le_rfl, fun hI' => childHInst_labInv hI'.n_le
        ((hI'.hint L rfl).mono ?_ (labLen_labM2aD_le hwv0.nodup n N _ L))⟩, ?_⟩
      · show (m2aModel X.O n N gs w L (mbD n N gs)).1.1 ≤ max N (2 * n)
        rw [hdeg]
        omega
      · show (m2aModel X.O n N gs w L (mbD n N gs)).1.1 - n ≤ N - n
        rw [hdeg]
        omega
      · show FreeChild w.1.length (N - n)
          ((m2aModel X.O n N gs w L (mbD n N gs)).2.1.1.length,
            some ((m2aModel X.O n N gs w L (mbD n N gs)).1.1 - n))
        rw [hw', hdeg]
        exact ⟨by omega, Or.inl ⟨_, rfl, by omega, by omega⟩⟩)
    hBlift hBgen
  have hwp : 1 ≤ w.1.length := hI.win_pos rfl
  refine ⟨ans, [(w.1.length, some (mbD n N gs).length)], ?_, hok', hg, ?_⟩
  · apply RunsWithin.mono
    case h =>
      unfold Main.m2aStepProg
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
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step hrun0
      exact hrun
    case hc =>
      have hmono := viaChildCost_mono (N := N) (n := n) (s := s) (Blift := Blift) (Bgen := Bgen)
        (show n + (mbD n N gs).length ≤ N by omega)
      clear * - hmono
      simp only [Prim.cost, m2aStepCost, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil]
      omega
  · refine ⟨by simp, ?_, ?_⟩
    · intro x hx
      simp only [List.mem_singleton] at hx
      subst hx
      exact ⟨by omega, Or.inl ⟨_, rfl, by omega, by omega⟩⟩
    · intro x hx
      simp only [List.mem_singleton] at hx
      subst hx
      exact hwp

end Specs

/-! ### Well-formedness -/

section Wf

variable {D : Ty} {rec : Ty × Ty} {var₁ var₂ : Ty → Type} {r : Bool}
  {Γ : WfCtx var₁ var₂}

theorem wf_childOfProg {sub₁ : var₁ (hinstTy D) → Prog (groupSig D) rec var₁ (Ty.answer D)}
    {sub₂ : var₂ (hinstTy D) → Prog (groupSig D) rec var₂ (Ty.answer D)}
    (hsub : WfFun r Γ sub₁ sub₂) {xy₁ : var₁ Ty.strs} {xy₂ : var₂ Ty.strs}
    {σ₁ : var₁ Ty.perm} {σ₂ : var₂ Ty.perm} {K₁ : var₁ (Ty.group D)} {K₂ : var₂ (Ty.group D)}
    {n₀₁ n₁ : var₁ .nat} {n₀₂ n₂ : var₂ .nat}
    {r₁ : var₁ (.prod (Ty.group D) (.prod Ty.win (.array (.list .nat))))}
    {r₂ : var₂ (.prod (Ty.group D) (.prod Ty.win (.array (.list .nat))))}
    (hxy : ⟨Ty.strs, xy₁, xy₂⟩ ∈ Γ) (hσ : ⟨Ty.perm, σ₁, σ₂⟩ ∈ Γ)
    (hK : ⟨Ty.group D, K₁, K₂⟩ ∈ Γ) (hn₀ : ⟨.nat, n₀₁, n₀₂⟩ ∈ Γ) (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ)
    (hr : ⟨.prod (Ty.group D) (.prod Ty.win (.array (.list .nat))), r₁, r₂⟩ ∈ Γ) :
    Prog.Wf r Γ (childOfProg sub₁ xy₁ σ₁ K₁ n₀₁ n₁ r₁) (childOfProg sub₂ xy₂ σ₂ K₂ n₀₂ n₂ r₂) := by
  unfold childOfProg
  refine .bind (.prim _ (.cons hr .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp [hr]) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  exact wf_viaChildProg (WfFun.mono hsub (by intro y hy; simp [hy]))
    (by simp [hxy]) (by simp [hσ]) (by simp [hK]) (by simp [hn₀]) (by simp [hn])
    (by simp) (by simp) (List.Mem.head _)

theorem wf_m0StepProg {sub₁ : var₁ (hinstTy D) → Prog (groupSig D) rec var₁ (Ty.answer D)}
    {sub₂ : var₂ (hinstTy D) → Prog (groupSig D) rec var₂ (Ty.answer D)}
    (hsub : WfFun r Γ sub₁ sub₂) {I₁ : var₁ (hinstTy D)} {I₂ : var₂ (hinstTy D)}
    (hI : ⟨hinstTy D, I₁, I₂⟩ ∈ Γ) :
    Prog.Wf r Γ (m0StepProg sub₁ I₁) (m0StepProg sub₂ I₂) := by
  unfold m0StepProg
  refine .bind (.prim _ (.cons hI .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp [hI]) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (wf_m0Prog (by simp) (by simp) (List.Mem.head _) (by simp)) fun _ _ => ?_
  exact wf_childOfProg (hsub.mono fun y hy => by simp [hy]) (by simp) (by simp) (by simp)
    (by simp) (by simp) (List.Mem.head _)

theorem wf_m1StepProg {sub₁ : var₁ (hinstTy D) → Prog (groupSig D) rec var₁ (Ty.answer D)}
    {sub₂ : var₂ (hinstTy D) → Prog (groupSig D) rec var₂ (Ty.answer D)}
    (hsub : WfFun r Γ sub₁ sub₂) {I₁ : var₁ (hinstTy D)} {I₂ : var₂ (hinstTy D)}
    {L₁ : var₁ (.array (.list .nat))} {L₂ : var₂ (.array (.list .nat))}
    (hI : ⟨hinstTy D, I₁, I₂⟩ ∈ Γ)
    (hL : ⟨.array (.list .nat), L₁, L₂⟩ ∈ Γ) :
    Prog.Wf r Γ (m1StepProg sub₁ I₁ L₁) (m1StepProg sub₂ I₂ L₂) := by
  unfold m1StepProg
  refine .bind (.prim _ (.cons hI .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp [hI]) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (wf_m1Prog (by simp) (List.Mem.head _) (by simp) (by simp) (by simp [hL]))
    fun _ _ => ?_
  exact wf_childOfProg (hsub.mono fun y hy => by simp [hy]) (by simp) (by simp) (by simp)
    (by simp) (by simp) (List.Mem.head _)

theorem wf_m2aStepProg {sub₁ : var₁ (hinstTy D) → Prog (groupSig D) rec var₁ (Ty.answer D)}
    {sub₂ : var₂ (hinstTy D) → Prog (groupSig D) rec var₂ (Ty.answer D)}
    (hsub : WfFun r Γ sub₁ sub₂) {I₁ : var₁ (hinstTy D)} {I₂ : var₂ (hinstTy D)}
    {L₁ : var₁ (.array (.list .nat))} {L₂ : var₂ (.array (.list .nat))}
    {bs₁ : var₁ (.list (.list .nat))} {bs₂ : var₂ (.list (.list .nat))}
    (hI : ⟨hinstTy D, I₁, I₂⟩ ∈ Γ)
    (hL : ⟨.array (.list .nat), L₁, L₂⟩ ∈ Γ) (hbs : ⟨.list (.list .nat), bs₁, bs₂⟩ ∈ Γ) :
    Prog.Wf r Γ (m2aStepProg sub₁ I₁ L₁ bs₁) (m2aStepProg sub₂ I₂ L₂ bs₂) := by
  unfold m2aStepProg
  refine .bind (.prim _ (.cons hI .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp [hI]) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (wf_m2aProg (by simp) (by simp) (List.Mem.head _) (by simp) (by simp [hL])
    (by simp [hbs])) fun _ _ => ?_
  exact wf_childOfProg (hsub.mono fun y hy => by simp [hy]) (by simp) (by simp) (by simp)
    (by simp) (by simp) (List.Mem.head _)

end Wf

end GraphIso.Main
