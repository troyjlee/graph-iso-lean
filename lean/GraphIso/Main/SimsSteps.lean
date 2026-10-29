module

public import GraphIso.Main.SimsCounts

/-!
# The free coarsenings with the Schreier–Sims backend

Stage 14j-5c, items 1 and 2 (`PLAN-14.md` §14.8), for M1 and M2a: the step specs
`RunsWithin.m1StepProg` and `RunsWithin.m2aStepProg` at `ssCtx`, with every charge proved.

* **Charges.** A Schreier–Sims charge depends only on the degree, the number of input
  generators and the window's length (`ssB`). The charges of a step are bounded by those
  functions at the step's sizes: the degree of a re-based group is at most `N`, and re-basing
  keeps the number of generators (`rebaseGens_length`).
* **The work** (`m1WorkSS`, `m2aWorkSS`) is the spec's cost with these charges, written in the
  string positions `n`, the base size `m` (degree `n + m`), the window `p`, the number of
  generators `g`, the sub-solver's generator bound `s` and the label array's size `Ls`. In these
  sizes every term is monotone (`m1WorkSS_mono`, `m2aWorkSS_mono`).
-/

@[expose] public section

namespace GraphIso.Main

open Equiv Cost GraphIso GraphIso.Programs GraphIso.Toolkit GraphIso.Recursion Sims Solver

attribute [local gcongr] buildCost_mono₂ genCost_mono₂ kerCost_mono₂ rd_liftCost_mono₂
  rd_orbitsCost_mono₂

theorem baseWin_length (n N : ℕ) : (baseWin n N).1.length = N - n := by
  rw [baseWin, WinData.ofPoints_fst, length_basePts]

theorem rebaseGens_length (n N : ℕ) (bs : List (List ℕ)) (gs : GensData) :
    (rebaseGens n N bs gs).length = gs.length :=
  List.length_map _

/-! ### The charges of `ssB` -/

section Charges

theorem ssB_generate (M : ℕ) (hs : GensData) (y : (Ty.group .unit).denote) :
    ssB.call GroupOp.generate (M, hs) y = genCost M hs.length + 2 := rfl

theorem ssB_orbits (Hd : GroupData Unit) (w : WinData) (y : List (List ℕ)) :
    ssB.call GroupOp.orbits (Hd, w) y = orbitsCost Hd.1 Hd.2.1.length w.1.length + 5 := rfl

theorem ssB_lift (Hd : GroupData Unit) (w : WinData) (π : PermData) (y : PermData) :
    ssB.call GroupOp.lift (Hd, (w, π)) y = Sims.liftCost Hd.1 Hd.2.1.length w.1.length + 7 :=
  rfl

/-- The `generate` charge on at most `L` generators at degree at most `M`. -/
theorem ssB_generate_le {M M' : ℕ} {hs : GensData} {L : ℕ} (hM : M ≤ M') (hL : hs.length ≤ L)
    (y : (Ty.group .unit).denote) :
    ssB.call GroupOp.generate (M, hs) y ≤ genCost M' L + 2 := by
  rw [ssB_generate]
  exact Nat.add_le_add_right (genCost_mono₂ hM hL) 2

/-- **M1's base orbits** (`hBo` of `RunsWithin.m1StepProg`). -/
theorem ss_hint_hBo (N n : ℕ) (gs : GensData) (d : Unit) :
    ssCtx.B.call GroupOp.orbits ((N, gs, d), baseWin n N)
      (ssCtx.O.run GroupOp.orbits ((N, gs, d), baseWin n N)) ≤
      orbitsCost N gs.length (N - n) + 5 := by
  change orbitsCost N gs.length (baseWin n N).1.length + 5 ≤ _
  rw [baseWin_length]

/-- **The re-basing** onto `bs` within degree `N` (`hB` of M1 on its orbit, of M2a on its
blocks). -/
theorem ss_hint_hB {n N : ℕ} {bs : List (List ℕ)} (gs : GensData) (h : n + bs.length ≤ N) :
    ssCtx.B.call GroupOp.generate (n + bs.length, rebaseGens n N bs gs)
      (rebaseModel ssCtx.O n N bs gs) ≤ genCost N gs.length + 2 :=
  ssB_generate_le h (by rw [rebaseGens_length]) _

/-- **The transfer's lifts** (`hBlift` of M1 and M2a). -/
theorem ss_hint_hBlift (N n : ℕ) (gs : GensData) (d : Unit) :
    ∀ π' : PermData, π'.Valid n → ssCtx.B.call GroupOp.lift ((N, gs, d), (strWin N n, π'))
      (ssCtx.O.run GroupOp.lift ((N, gs, d), (strWin N n, π'))) ≤
      Sims.liftCost N gs.length n + 7 := by
  intro π' _
  change Sims.liftCost N gs.length (strWin N n).1.length + 7 ≤ _
  simp only [strWin, WinData.ofPoints_fst, List.length_range, le_refl]

/-- **The transfer's `generate`** on at most `s` generators (`hBgen` of M1 and M2a). -/
theorem ss_hint_hBgen (N s : ℕ) (gs : GensData) :
    ∀ hs : GensData, GensData.AllValid N hs → hs.length ≤ s →
      GensData.denote N hs ≤ GensData.denote N gs →
      ssCtx.B.call GroupOp.generate (N, hs) (ssCtx.O.run GroupOp.generate (N, hs)) ≤
        genCost N s + 2 :=
  fun _ _ hl _ => ssB_generate_le le_rfl hl _

end Charges

/-! ### M1 -/

section M1

/-- **The work of M1 with Schreier–Sims**: `m1StepCost` with the charges of `ssB`, for `n` string
positions, base size `m`, a window of `p` points, `g` generators and sub-solver answers of at
most `s` generators. -/
def m1WorkSS (n m p g s : ℕ) : ℕ :=
  m1StepCost n (n + m) p g s (orbitsCost (n + m) g m + 5) (genCost (n + m) g + 2)
    (Sims.liftCost (n + m) g n + 7) (genCost (n + m) s + 2)

theorem m1WorkSS_mono {n n' m m' p p' g g' s s' : ℕ} (hn : n ≤ n') (hm : m ≤ m') (hp : p ≤ p')
    (hg : g ≤ g') (hs : s ≤ s') : m1WorkSS n m p g s ≤ m1WorkSS n' m' p' g' s' := by
  unfold m1WorkSS m1StepCost m1Cost viaChildCost transferCost baseWinCost pickCost ncCost
    ncPairCost interOCost SoJTree.setEqCost rebaseCost labM1Cost
  simp only [Nat.add_sub_cancel_left]
  gcongr

variable {a b : Ty} {body : a.denote → Prog (groupSig Ty.unit) (a, b) Ty.denote b}
  {sub : HInstData Ty.unit → Prog (groupSig Ty.unit) (a, b) Ty.denote (Ty.answer Ty.unit)}

/-- **M1 with Schreier–Sims** (`RunsWithin.m1StepProg` at `ssCtx`). For a valid instance with
the hint `L` whose base action is intransitive, and a sub-solver for the re-based child: the
spec's conclusion, with the work `m1WorkSS n (N − n) |W| |gs| s`. No charge hypothesis. -/
theorem RunsWithin.m1StepProg_ss {xy : StrData × StrData} {w : WinData} {σd : PermData}
    {N : ℕ} {gs : GensData} {d : Unit} {n₀ n : ℕ} {L : LabelData}
    (hI : HInstValid ssDV (((xy, w, σd, N, gs, d), n₀, n, some L) : HInstData Ty.unit))
    (hnt : ¬ IsTransOn (GensData.denote N gs) (baseSet n N))
    {C : ℕ → Option ℕ → ℕ} {s : ℕ}
    (hsub : HSubSolves ssCtx body ssDV sub
      (fun J => SizeChild
          (rebaseModel ssCtx.O n N (singD (m1O ssCtx.O n N (N, gs, d) w L)) gs).2.1.length
          (((xy, w, σd, N, gs, d), n₀, n, some L) : HInstData Ty.unit) J ∧
        FreeChild w.1.length (N - n) (J.winSize, J.baseOpt)) C s) :
    ∃ (ans : AnswerData Ty.unit) (ch : List (ℕ × Option ℕ)),
      RunsWithin ssCtx body
        (Main.m1StepProg sub (((xy, w, σd, N, gs, d), n₀, n, some L) : HInstData Ty.unit) L)
        ans ((ch.map fun x => C x.1 x.2).sum + m1WorkSS n (N - n) w.1.length gs.length s) ∧
      InstData.OK (D := Ty.unit) (xy, w, σd, N, gs, d) ssDV ans ∧
      (∀ sGen, (∀ hs, GensData.AllValid N hs → GensData.denote N hs ≤ GensData.denote N gs →
          (ssCtx.O.run GroupOp.generate (N, hs)).2.1.length ≤ sGen) →
        ∀ c : CosetData Ty.unit, ans = some c → c.2.gens.length ≤ sGen) ∧
      ChildList w.1.length 1 (FreeChild w.1.length (N - n)) ch := by
  have hn : n ≤ N := hI.le
  have hO : MeetsContractOn ssDV hintStepOps ssCtx.O := fun op x _ hx => ssOracle_meets op x hx
  have hPre : ∀ op x, hintStepOps op → GroupPre ssDV op x → ssCtx.Pre op x := fun _ _ _ h => h
  -- the orbit's size, from M1's program spec at the exact charges
  obtain ⟨-, -, -, -, -, -, -, -, hk0, -⟩ := RunsWithin.m1Prog (X := ssCtx) (body := body)
    (DV := ssDV) (fun op x hop hx => hO op x (hintStepOps_of_m1 hop) hx)
    (fun op x hop hx => hPre op x (hintStepOps_of_m1 hop) hx) hI.valid.group hI.valid.win
    hI.valid.invariant hI.faithful (hI.hint L rfl).2 (hI.hint L rfl).1 le_rfl le_rfl
  have hk : (singD (m1O ssCtx.O n N (N, gs, d) w L)).length ≤ N - n := hk0
  obtain ⟨ans, ch, hrun, hok, hg, hch⟩ := RunsWithin.m1StepProg (X := ssCtx) hO hPre hI hnt hsub
    (Borb := orbitsCost N gs.length (N - n) + 5) (Bgen₁ := genCost N gs.length + 2)
    (Blift := Sims.liftCost N gs.length n + 7) (Bgen := genCost N s + 2)
    (ss_hint_hBo N n gs d) (ss_hint_hB gs (by omega)) (ss_hint_hBlift N n gs d)
    (ss_hint_hBgen N s gs)
  refine ⟨ans, ch, hrun.mono ?_, hok, hg, hch⟩
  have e : n + (N - n) = N := by omega
  unfold m1WorkSS
  rw [e]

end M1


/-! ### M2a -/

section M2a

/-- **The work of M2a with Schreier–Sims**: `m2aStepCost` with the charges of `ssB`, for `n`
string positions, base size `m`, a window of `p` points, `g` generators, sub-solver answers of at
most `s` generators and a label array of size `Ls`. -/
def m2aWorkSS (n m p g s Ls : ℕ) : ℕ :=
  m2aStepCost n (n + m) p g s Ls (genCost (n + m) g + 2) (Sims.liftCost (n + m) g n + 7)
    (genCost (n + m) s + 2)

theorem m2aWorkSS_mono {n n' m m' p p' g g' s s' Ls Ls' : ℕ} (hn : n ≤ n') (hm : m ≤ m')
    (hp : p ≤ p') (hg : g ≤ g') (hs : s ≤ s') (hL : Ls ≤ Ls') :
    m2aWorkSS n m p g s Ls ≤ m2aWorkSS n' m' p' g' s' Ls' := by
  unfold m2aWorkSS m2aStepCost m2aCost viaChildCost transferCost rebaseCost blockLabCost
  simp only [Nat.add_sub_cancel_left]
  gcongr

variable {a b : Ty} {body : a.denote → Prog (groupSig Ty.unit) (a, b) Ty.denote b}
  {sub : HInstData Ty.unit → Prog (groupSig Ty.unit) (a, b) Ty.denote (Ty.answer Ty.unit)}

/-- **M2a with Schreier–Sims** (`RunsWithin.m2aStepProg` at `ssCtx`). For a valid instance with
the hint `L` whose base action is transitive, with proper maximal blocks over which some window
label is not equidistributed, and a sub-solver for the re-based child: the spec's conclusion,
with the work `m2aWorkSS n (N − n) |W| |gs| s |L|`. No charge hypothesis. -/
theorem RunsWithin.m2aStepProg_ss {xy : StrData × StrData} {w : WinData} {σd : PermData}
    {N : ℕ} {gs : GensData} {d : Unit} {n₀ n : ℕ} {L : LabelData}
    (hI : HInstValid ssDV (((xy, w, σd, N, gs, d), n₀, n, some L) : HInstData Ty.unit))
    (htrB : IsTransOn (GensData.denote N gs) (baseSet n N))
    (hok : blkOKD (N - n) (mbD n N gs) = true) (hne : neqD n N (mbD n N gs) L w.1 = true)
    {C : ℕ → Option ℕ → ℕ} {s : ℕ}
    (hsub : HSubSolves ssCtx body ssDV sub
      (fun J => SizeChild (rebaseModel ssCtx.O n N (mbD n N gs) gs).2.1.length
          (((xy, w, σd, N, gs, d), n₀, n, some L) : HInstData Ty.unit) J ∧
        FreeChild w.1.length (N - n) (J.winSize, J.baseOpt)) C s) :
    ∃ (ans : AnswerData Ty.unit) (ch : List (ℕ × Option ℕ)),
      RunsWithin ssCtx body
        (Main.m2aStepProg sub (((xy, w, σd, N, gs, d), n₀, n, some L) : HInstData Ty.unit) L
          (mbD n N gs)) ans
        ((ch.map fun x => C x.1 x.2).sum + m2aWorkSS n (N - n) w.1.length gs.length s L.size) ∧
      InstData.OK (D := Ty.unit) (xy, w, σd, N, gs, d) ssDV ans ∧
      (∀ sGen, (∀ hs, GensData.AllValid N hs → GensData.denote N hs ≤ GensData.denote N gs →
          (ssCtx.O.run GroupOp.generate (N, hs)).2.1.length ≤ sGen) →
        ∀ c : CosetData Ty.unit, ans = some c → c.2.gens.length ≤ sGen) ∧
      ChildList w.1.length 1 (FreeChild w.1.length (N - n)) ch := by
  have hn : n ≤ N := hI.le
  have hO : MeetsContractOn ssDV hintStepOps ssCtx.O := fun op x _ hx => ssOracle_meets op x hx
  have hPre : ∀ op x, hintStepOps op → GroupPre ssDV op x → ssCtx.Pre op x := fun _ _ _ h => h
  obtain ⟨h2m, hh⟩ := blkOKD_iff.1 hok
  obtain ⟨hbs, -⟩ := dv_blocks_facts hI.valid.group.1 hI.base_inv htrB h2m hh
  have hk : (mbD n N gs).length ≤ N - n := by
    have := IsBlockList.length_le hbs
    rwa [WinData.ofPoints_fst, length_basePts] at this
  obtain ⟨ans, ch, hrun, hok, hg, hch⟩ := RunsWithin.m2aStepProg (X := ssCtx) hO hPre hI htrB
    hok hne hsub (Bgen₂ := genCost N gs.length + 2) (Blift := Sims.liftCost N gs.length n + 7)
    (Bgen := genCost N s + 2)
    (ss_hint_hB gs (by omega)) (ss_hint_hBlift N n gs d) (ss_hint_hBgen N s gs)
  refine ⟨ans, ch, hrun.mono ?_, hok, hg, hch⟩
  have e : n + (N - n) = N := by omega
  unfold m2aWorkSS
  rw [e]

end M2a


/-! ### M2b -/

section M2b

theorem extendGens_length (N : ℕ) (bs : List (List ℕ)) (gs : GensData) :
    (extendGens N bs gs).length = gs.length :=
  List.length_map _

/-- **The sizes of the block stabilizer with Schreier–Sims.** The extended group at degree
`N + |bs|`, the stabilizer of block `t`'s point and its transversal, and the setwise stabilizer
of block `t` with its coset representatives. The last two come from `RunsWithin.blockStabProg`
for the invariant `ssBnd 0` (the truncated stabilizer generators are valid there). -/
theorem ss_blockStab_sizes {n N : ℕ} {w : WinData} {bs : List (List ℕ)} {gs : GensData}
    {t : ℕ} (hG : IsInvariant (GensData.denote N gs) (baseSet n N)) (hw : w.Valid N)
    (hwb : ∀ i ∈ w.1, n ≤ i) (hbs : IsBlockList w bs)
    (hGb : PermutesBlocks (GensData.denote N gs) bs) (hgs : GensData.AllValid N gs)
    (ht : t < bs.length) :
    (extGroup ssCtx.O N bs gs).2.1.length ≤ (N + bs.length) * (N + bs.length) ∧
      (bsStab ssCtx.O N bs gs t).2.1.length ≤ (N + bs.length) * (N + bs.length) ∧
      (bsTrans ssCtx.O N bs gs t).length ≤ N + bs.length ∧
      (blockStabModel ssCtx.O N bs gs t).1.2.1.length ≤ N * N ∧
      (blockStabModel ssCtx.O N bs gs t).2.length ≤ bs.length := by
  have hev : GensData.AllValid (N + bs.length) (extendGens N bs gs) :=
    GensData.allValid_extendTo hw hbs hGb hgs
  have hv1 : GensData.AllValid (N + bs.length) (extGroup ssCtx.O N bs gs).2.1 :=
    (generateModel_spec hev).1
  have hlt : N + t < N + bs.length := by omega
  obtain ⟨-, -, hv, -, -, -, hlen⟩ := RunsWithin.blockStabProg (X := ssCtxB 0) (DV := ssBnd 0)
    (a := Ty.unit) (b := Ty.unit)
    (body := fun x => (Prog.ret x : Prog (groupSig Ty.unit) (Ty.unit, Ty.unit) Ty.denote Ty.unit))
    (fun op x _ hx => ssOracle_meets_bnd 0 op x hx) (fun _ _ _ h => h) hG hw hwb hbs hGb hgs ht
    le_rfl le_rfl le_rfl le_rfl
  refine ⟨(generateModel_spec hev).2.2, (stabModel_spec hv1 hlt).2.2,
    orbitBFS_length_le hlt hv1, ?_, hlen⟩
  have h := hv.2
  change _ ≤ max 0 (N * N) at h
  exact h.trans (max_le (Nat.zero_le _) le_rfl)

/-- **The work of M2b with Schreier–Sims**: `m2bStepCost` with the charges of `ssB` and the
sizes of the block stabilizer, for `n` string positions, base size `m`, a window of `p` points,
`g` generators, a label array of size `Ls` and the sub-solver's generator bound `sIn`. The block
has at most `m` points and there are at most `m` blocks, so the extended degree is at most
`n + 2m`. -/
def m2bWorkSS (n m p g Ls sIn : ℕ) : ℕ :=
  m2bStepCost n (n + m) m p Ls g ((n + 2 * m) * (n + 2 * m)) (n + 2 * m) ((n + m) * (n + m)) sIn
    ((n + m) * (n + m)) (genCost (n + 2 * m) g + 2)
    (stabCost (n + 2 * m) ((n + 2 * m) * (n + 2 * m)) + 5)
    (transCost (n + 2 * m) ((n + 2 * m) * (n + 2 * m)) + 5)
    (genCost (n + m) ((n + 2 * m) * (n + 2 * m)) + 2) (genCost (n + m) ((n + m) * (n + m)) + 2)
    (Sims.liftCost (n + m) ((n + m) * (n + m)) n + 7) (genCost (n + m) sIn + 2)
    (orbitsCost (n + m) sIn (n + m) + 5) (genCost (n + m) (m * ((n + m) * (n + m) + 1)) + 2)

theorem m2bStepCost_mono_k {n N k k' p Ls s sS Lt sH sIn sR Bge Bst Btr Bgt Bgen₃ Blift Bgen Bo
    Bgen₂ : ℕ} (hk : k ≤ k') :
    m2bStepCost n N k p Ls s sS Lt sH sIn sR Bge Bst Btr Bgt Bgen₃ Blift Bgen Bo Bgen₂ ≤
      m2bStepCost n N k' p Ls s sS Lt sH sIn sR Bge Bst Btr Bgt Bgen₃ Blift Bgen Bo Bgen₂ := by
  unfold m2bStepCost m2bCost m2bLoopCost mlBranchCost mlHandleCost ncBCost ncCost ncPairCost
    interOCost SoJTree.setEqCost rebaseCost markCost viaChildCost transferCost baseWinCost
    dynSeqCost dynStepCost
  simp only [Nat.add_sub_cancel_left]
  gcongr

theorem m2bWorkSS_mono {n n' m m' p p' g g' Ls Ls' sIn sIn' : ℕ} (hn : n ≤ n')
    (hm : m ≤ m') (hp : p ≤ p') (hg : g ≤ g') (hL : Ls ≤ Ls') (hsIn : sIn ≤ sIn') :
    m2bWorkSS n m p g Ls sIn ≤ m2bWorkSS n' m' p' g' Ls' sIn' := by
  unfold m2bWorkSS m2bStepCost m2bCost m2bLoopCost mlBranchCost mlHandleCost ncBCost ncCost
    ncPairCost interOCost SoJTree.setEqCost rebaseCost markCost viaChildCost transferCost
    blockStabCost baseWinCost interCost dynSeqCost dynStepCost stabCost transCost
  simp only [Nat.add_sub_cancel_left]
  gcongr

/-- The sizes behind M2b's charges: the block list `bs` of the base `[n, N)` has at most
`N − n` blocks, so the extended degree `N + |bs|` is at most `E = n + 2(N − n)`; the block
stabilizer's data at that degree; and the re-basing onto block `0` stays within degree `N`. -/
theorem ss_m2b_sizes {n N : ℕ} {gs : GensData} {bs : List (List ℕ)} (hn : n ≤ N)
    (hG : IsInvariant (GensData.denote N gs) (baseSet n N))
    (hbs : IsBlockList (WinData.ofPoints N (basePts n N)) bs)
    (hGb : PermutesBlocks (GensData.denote N gs) bs) (hgs : GensData.AllValid N gs)
    (hbs0 : 0 < bs.length) :
    N + bs.length ≤ n + 2 * (N - n) ∧ bs.length ≤ N - n ∧
      (extGroup ssCtx.O N bs gs).2.1.length ≤ (N + bs.length) * (N + bs.length) ∧
      (bsStab ssCtx.O N bs gs 0).2.1.length ≤ (N + bs.length) * (N + bs.length) ∧
      (bsTrans ssCtx.O N bs gs 0).length ≤ N + bs.length ∧
      (blockStabModel ssCtx.O N bs gs 0).1.2.1.length ≤ N * N ∧
      (blockStabModel ssCtx.O N bs gs 0).2.length ≤ bs.length ∧
      n + ((bs.toArray.getD 0 []).map fun p => [p]).length ≤ N := by
  have hwbv : (WinData.ofPoints N (basePts n N)).Valid N :=
    WinData.valid_ofPoints (basePts_nodup _ _) fun i hi => (mem_basePts.1 hi).2
  have hwbn : ∀ i ∈ (WinData.ofPoints N (basePts n N)).1, n ≤ i :=
    fun i hi => (mem_basePts.1 hi).1
  have hbl : bs.length ≤ N - n := by
    have := IsBlockList.length_le hbs
    rwa [WinData.ofPoints_fst, length_basePts] at this
  obtain ⟨hse, hss, hst, hsH, hreps⟩ := ss_blockStab_sizes (t := 0) hG hwbv hwbn hbs hGb
    hgs hbs0
  have hflat : bs.flatten.length = N - n := by
    rw [hbs.1.length_eq, WinData.ofPoints_fst, length_basePts]
  have hkle : (bs.toArray.getD 0 []).length ≤ N - n := by
    rw [← hflat, mr_getD_toArray', List.getD_eq_getElem _ _ hbs0, List.length_flatten]
    exact List.le_sum_of_mem (List.mem_map.2 ⟨_, List.getElem_mem hbs0, rfl⟩)
  refine ⟨by omega, hbl, hse, hss, hst, hsH, hreps, ?_⟩
  rw [List.length_map]
  omega

/-- **M2b's block-stabilizer charges** with Schreier–Sims (`M2bCharges`), at the extended
degree `E = n + 2(N − n)`: the extended group, the stabilizer and transversal of block `0`, the
stabilizer at degree `N` and its re-basing onto the block. -/
theorem ss_m2bCharges {n N : ℕ} {gs : GensData} {bs : List (List ℕ)} (hn : n ≤ N)
    (hG : IsInvariant (GensData.denote N gs) (baseSet n N))
    (hbs : IsBlockList (WinData.ofPoints N (basePts n N)) bs)
    (hGb : PermutesBlocks (GensData.denote N gs) bs) (hgs : GensData.AllValid N gs)
    (hbs0 : 0 < bs.length) :
    M2bCharges ssCtx n N gs bs (genCost (n + 2 * (N - n)) gs.length + 2)
      (stabCost (n + 2 * (N - n)) ((n + 2 * (N - n)) * (n + 2 * (N - n))) + 5)
      (transCost (n + 2 * (N - n)) ((n + 2 * (N - n)) * (n + 2 * (N - n))) + 5)
      (genCost N ((n + 2 * (N - n)) * (n + 2 * (N - n))) + 2) (genCost N (N * N) + 2)
      ((n + 2 * (N - n)) * (n + 2 * (N - n))) (n + 2 * (N - n)) (N * N) := by
  obtain ⟨e2, -, hse, hss, hst, hsH, -, hRb1⟩ := ss_m2b_sizes hn hG hbs hGb hgs hbs0
  exact
    { ge := ssB_generate_le e2 (by rw [extendGens_length]) _
      st := by
        change stabCost (extGroup ssCtx.O N bs gs).1 (extGroup ssCtx.O N bs gs).2.1.length + 5 ≤ _
        change stabCost (N + bs.length) _ + 5 ≤ _
        unfold stabCost
        gcongr
        exact hse.trans (Nat.mul_le_mul e2 e2)
      tr := by
        change transCost (N + bs.length) (extGroup ssCtx.O N bs gs).2.1.length + 5 ≤ _
        unfold transCost
        gcongr
        exact hse.trans (Nat.mul_le_mul e2 e2)
      gt := ssB_generate_le le_rfl
        ((List.length_map _).trans_le (hss.trans (Nat.mul_le_mul e2 e2))) _
      gen3 := ssB_generate_le hRb1 (by rw [rebaseGens_length]; exact hsH) _
      sS := hss.trans (Nat.mul_le_mul e2 e2)
      Lt := hst.trans e2
      sH := hsH }

/-- M2b's lifts from the block stabilizer (`hBlift`). -/
theorem ss_m2b_hBlift {n N : ℕ} {gs : GensData} {bs : List (List ℕ)} (hn : n ≤ N)
    (hG : IsInvariant (GensData.denote N gs) (baseSet n N))
    (hbs : IsBlockList (WinData.ofPoints N (basePts n N)) bs)
    (hGb : PermutesBlocks (GensData.denote N gs) bs) (hgs : GensData.AllValid N gs)
    (hbs0 : 0 < bs.length) :
    ∀ π' : PermData, π'.Valid n →
      ssCtx.B.call GroupOp.lift (m2bRg ssCtx.O N gs bs, (strWin N n, π'))
        (ssCtx.O.run GroupOp.lift (m2bRg ssCtx.O N gs bs, (strWin N n, π'))) ≤
        Sims.liftCost N (N * N) n + 7 := by
  obtain ⟨-, -, -, -, -, hsH, -, -⟩ := ss_m2b_sizes hn hG hbs hGb hgs hbs0
  intro π' _
  change Sims.liftCost N (blockStabModel ssCtx.O N bs gs 0).1.2.1.length
    (strWin N n).1.length + 7 ≤ _
  simp only [strWin, WinData.ofPoints_fst, List.length_range]
  exact Nat.add_le_add_right (rd_liftCost_mono₂ le_rfl hsH le_rfl) 7

/-- M2b's `generate` on the branches' answers (`hBgen`). -/
theorem ss_m2b_hBgen {N sIn : ℕ} {gs : GensData} {bs : List (List ℕ)} :
    ∀ hs : GensData, GensData.AllValid N hs → hs.length ≤ sIn →
      GensData.denote N hs ≤ GensData.denote N (m2bRg ssCtx.O N gs bs).2.1 →
      ssCtx.B.call GroupOp.generate (N, hs) (ssCtx.O.run GroupOp.generate (N, hs)) ≤
        genCost N sIn + 2 :=
  fun _ _ hl _ => ssB_generate_le le_rfl hl _

/-- M2b's orbits of the re-based block stabilizer's subgroups (`hBo`). -/
theorem ss_m2b_hBo {n N sIn : ℕ} {gs : GensData} {bs : List (List ℕ)} (hn : n ≤ N)
    (hG : IsInvariant (GensData.denote N gs) (baseSet n N))
    (hbs : IsBlockList (WinData.ofPoints N (basePts n N)) bs)
    (hGb : PermutesBlocks (GensData.denote N gs) bs) (hgs : GensData.AllValid N gs)
    (hbs0 : 0 < bs.length) :
    ∀ (Hd : GroupData Ty.unit.denote) (w' : WinData), Hd.1 = (m2bRb ssCtx.O n N gs bs).1 →
      Hd.2.1.length ≤ sIn →
      GensData.denote (m2bRb ssCtx.O n N gs bs).1 Hd.2.1 ≤
        GensData.denote (m2bRb ssCtx.O n N gs bs).1 (m2bRb ssCtx.O n N gs bs).2.1 →
      GroupPre ssDV .orbits (Hd, w') →
      ssCtx.B.call GroupOp.orbits (Hd, w') (ssCtx.O.run GroupOp.orbits (Hd, w')) ≤
        orbitsCost N sIn N + 5 := by
  obtain ⟨-, -, -, -, -, -, -, hRb1⟩ := ss_m2b_sizes hn hG hbs hGb hgs hbs0
  intro Hd w' h1 hl _ hpre
  obtain ⟨M, gs', d'⟩ := Hd
  obtain ⟨-, hw', -⟩ := hpre
  change orbitsCost M gs'.length w'.1.length + 5 ≤ _
  have hRb1' : (m2bRb ssCtx.O n N gs bs).1 ≤ N := hRb1
  have hM : M ≤ N := by change M = _ at h1; rw [h1]; exact hRb1'
  exact Nat.add_le_add_right (rd_orbitsCost_mono₂ hM hl ((WinData.length_le hw').trans hM)) 5

/-- M2b's `generate` on the combined branches (`hBgen₂`, with `sR = N²`). -/
theorem ss_m2b_hBgen₂ {n N : ℕ} {gs : GensData} {bs : List (List ℕ)} (hn : n ≤ N)
    (hG : IsInvariant (GensData.denote N gs) (baseSet n N))
    (hbs : IsBlockList (WinData.ofPoints N (basePts n N)) bs)
    (hGb : PermutesBlocks (GensData.denote N gs) bs) (hgs : GensData.AllValid N gs)
    (hbs0 : 0 < bs.length) :
    ∀ gs' : GensData, GensData.AllValid N gs' →
      gs'.length ≤ (blockStabModel ssCtx.O N bs gs 0).2.length * (N * N + 1) →
      GensData.denote N gs' ≤ GensData.denote N gs →
      ssCtx.B.call GroupOp.generate (N, gs') (ssCtx.O.run GroupOp.generate (N, gs')) ≤
        genCost N ((N - n) * (N * N + 1)) + 2 := by
  obtain ⟨-, hbl, -, -, -, -, hreps, -⟩ := ss_m2b_sizes hn hG hbs hGb hgs hbs0
  exact fun gs' _ hl _ => ssB_generate_le le_rfl (hl.trans (Nat.mul_le_mul_right _
    (hreps.trans hbl))) _

variable {a b : Ty} {body : a.denote → Prog (groupSig Ty.unit) (a, b) Ty.denote b}
  {sub : HInstData Ty.unit → Prog (groupSig Ty.unit) (a, b) Ty.denote (Ty.answer Ty.unit)}

/-- **M2b with Schreier–Sims** (`RunsWithin.m2bStepProg` at `ssCtx`). For a valid hinted
instance whose base action is transitive with a block system `bs` of at least two blocks on
which some window label is equidistributed, a sub-solver with the spec's predicate, and
`N² ≤ sIn`, `s ≤ sIn`: the spec's conclusion, with the work
`m2bWorkSS n (N − n) |W| |gs| |L| sIn`. No charge or generator-count hypothesis. -/
theorem RunsWithin.m2bStepProg_ss {C : ℕ → Option ℕ → ℕ} {s : ℕ} {xy : StrData × StrData}
    {w : WinData} {σd : PermData} {N : ℕ} {gs : GensData} {d : Unit} {n₀ n : ℕ}
    {L : LabelData}
    (hI : HInstValid ssDV ((((xy, (w, (σd, (N, gs, d)))), (n₀, (n, some L)))) :
      HInstData Ty.unit))
    {bs : List (List ℕ)} (hbs : IsBlockList (WinData.ofPoints N (basePts n N)) bs)
    (hGb : PermutesBlocks (GensData.denote N gs) bs)
    (hΨ : IsBlockSys (baseHom (GensData.denote N gs) n hI.base_inv) (blockFam n N bs))
    (hcard : 2 ≤ (blockFam n N bs).card)
    (htrB : ∀ γ δ : Fin (N - n), ∃ g, baseHom (GensData.denote N gs) n hI.base_inv g γ = δ)
    {u₀ : Fin N} (hu₀ : u₀.val ∈ w.1) (heq : Equidist (blockFam n N bs) (labOf n N L u₀))
    {sIn : ℕ}
    (hsub : HSubSolves ssCtx body ssDV sub
      (fun J => SizeChild sIn ((((xy, (w, (σd, (N, gs, d)))), (n₀, (n, some L)))) :
        HInstData Ty.unit) J ∧ StepChild w.1.length (N - n) (J.winSize, J.baseOpt)) C s)
    (hs : s ≤ sIn) (hN : N * N ≤ sIn) :
    ∃ (ans : AnswerData Ty.unit) (ch : List (ℕ × Option ℕ)),
      RunsWithin ssCtx body
        (Main.m2bStepProg sub ((((xy, (w, (σd, (N, gs, d)))), (n₀, (n, some L)))) :
          HInstData Ty.unit) bs) ans
        ((ch.map fun x => C x.1 x.2).sum +
          m2bWorkSS n (N - n) w.1.length gs.length L.size sIn) ∧
      InstData.OK (D := Ty.unit) (xy, (w, (σd, (N, gs, d)))) ssDV ans ∧
      (∀ sGen, (∀ hs, GensData.AllValid N hs → GensData.denote N hs ≤ GensData.denote N gs →
          (ssCtx.O.run GroupOp.generate (N, hs)).2.1.length ≤ sGen) →
        ∀ c : CosetData Ty.unit, ans = some c → c.2.gens.length ≤ sGen) ∧
      ChildList w.1.length (blockStabModel ssCtx.O N bs gs 0).2.length
        (StepChild w.1.length (N - n)) ch ∧
      (blockStabModel ssCtx.O N bs gs 0).2.length ≤ bs.length := by
  have hn : n ≤ N := hI.le
  have hgs : GensData.AllValid N gs := hI.valid.group.1
  have hO : MeetsContractOn ssDV m2bStepOps ssCtx.O := fun op x _ hx => ssOracle_meets op x hx
  have hPre : ∀ op x, m2bStepOps op → GroupPre ssDV op x → ssCtx.Pre op x := fun _ _ _ h => h
  have hbs0 : 0 < bs.length := by
    have h2 : 2 ≤ (blockFam n N bs).card := hcard
    rcases Nat.eq_zero_or_pos bs.length with h | h
    · rw [List.length_eq_zero_iff.1 h] at h2
      simp [blockFam] at h2
    · exact h
  have hkle : (bs.toArray.getD 0 []).length ≤ N - n := by
    have := (ss_m2b_sizes hn hI.base_inv hbs hGb hgs hbs0).2.2.2.2.2.2.2
    rw [List.length_map] at this
    omega
  have hRb : (m2bRb ssCtx.O n N gs bs).2.1.length ≤ sIn :=
    (ss_m2bRb_gens_le hn hI.base_inv hgs hbs hGb hbs0).trans hN
  have e1 : n + (N - n) = N := by omega
  obtain ⟨ans, ch, hrun, hok, hg, hch, hR⟩ := RunsWithin.m2bStepProg (X := ssCtx) hO hPre hI hbs
    hGb hΨ hcard htrB hu₀ heq hsub (sR := N * N)
    (ss_m2bCharges hn hI.base_inv hbs hGb hgs hbs0) hs hRb
    (ss_m2b_hBlift hn hI.base_inv hbs hGb hgs hbs0) ss_m2b_hBgen
    (ss_m2b_hBo hn hI.base_inv hbs hGb hgs hbs0) (ss_hsR N _)
    (ss_m2b_hBgen₂ hn hI.base_inv hbs hGb hgs hbs0)
  refine ⟨ans, ch, hrun.mono (Nat.add_le_add_left ((m2bStepCost_mono_k hkle).trans ?_) _), hok,
    hg, hch, hR⟩
  unfold m2bWorkSS
  rw [e1]

/-! ### Parameter choices

The step corollaries take numeric conditions on their parameters (`sIn`, `Lg`, `uB`, M5's `k`).
Each holds at an explicit choice: `ssSIn` here, `ssLgM4` and `ssLgM4Ns` (M4) and `ssLgM5` (M5),
with `uB = m` and, for M5, any `k` with `5 ≤ k` and `2k ≤ m`, for instance `k = 5` when
`12 ≤ m`. -/

/-- The generator bound `max (N²) (max s g)`: at least the degree squared, the sub-solver's
answers and the instance's generators. -/
def ssSIn (N s g : ℕ) : ℕ := max (N * N) (max s g)

theorem ssSIn_spec (N s g : ℕ) : N * N ≤ ssSIn N s g ∧ s ≤ ssSIn N s g ∧ g ≤ ssSIn N s g := by
  unfold ssSIn
  omega

/-- **M2b's parameters**: `sIn = ssSIn N s 0` meets `hs` and `hN` of
`RunsWithin.m2bStepProg_ss`. -/
theorem m2b_params (N s : ℕ) : s ≤ ssSIn N s 0 ∧ N * N ≤ ssSIn N s 0 :=
  ⟨(ssSIn_spec N s 0).2.1, (ssSIn_spec N s 0).1⟩

end M2b


/-! ### Monotone envelopes

For the larger steps (M4, M5) the work is the step's cost at the Schreier–Sims charges, which is
not monotone in every size: the base size of the remaining structure is `m − j`, for instance.
Its **monotone envelope** `envSup as f` is the largest value of `f` over the box of size lists
below `as`. It is explicit, at least `f as` (`le_envSup`), and monotone in every size
(`envSup_mono`). -/

section Envelope

theorem foldr_max_le {l : List ℕ} {B : ℕ} (h : ∀ x ∈ l, x ≤ B) : l.foldr max 0 ≤ B := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons a l ih =>
    exact max_le (h a List.mem_cons_self) (ih fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem supTo_le {f : ℕ → ℕ} {k B : ℕ} (h : ∀ x ≤ k, f x ≤ B) : supTo f k ≤ B :=
  foldr_max_le fun y hy => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    exact h x (by have := List.mem_range.1 hx; omega)

theorem supTo_mono {f g : ℕ → ℕ} {k k' : ℕ} (hfg : ∀ x, f x ≤ g x) (hk : k ≤ k') :
    supTo f k ≤ supTo g k' :=
  supTo_le fun x hx => (hfg x).trans (le_supTo (by omega))

/-- **The monotone envelope**: the largest value of `f` over the size lists below `as`, entry by
entry. -/
def envSup : List ℕ → (List ℕ → ℕ) → ℕ
  | [], f => f []
  | a :: as, f => supTo (fun x => envSup as fun ys => f (x :: ys)) a

theorem envSup_mono_fun : ∀ (as : List ℕ) {f g : List ℕ → ℕ}, (∀ xs, f xs ≤ g xs) →
    envSup as f ≤ envSup as g
  | [], _, _, h => h []
  | _ :: as, _, _, h => supTo_mono (fun _ => envSup_mono_fun as fun _ => h _) le_rfl

theorem le_envSup : ∀ {as xs : List ℕ}, List.Forall₂ (· ≤ ·) xs as → ∀ f : List ℕ → ℕ,
    f xs ≤ envSup as f
  | [], [], .nil, _ => le_rfl
  | _ :: _, _ :: _, .cons hx h, f =>
    (le_envSup h fun ys => f (_ :: ys)).trans (le_supTo (f := fun x => envSup _ fun ys =>
      f (x :: ys)) hx)

theorem envSup_mono : ∀ {as bs : List ℕ}, List.Forall₂ (· ≤ ·) as bs → ∀ f : List ℕ → ℕ,
    envSup as f ≤ envSup bs f
  | [], [], .nil, _ => le_rfl
  | _ :: _, _ :: _, .cons ha h, _ => supTo_mono (fun _ => envSup_mono h _) ha

theorem forall₂_le_refl (as : List ℕ) : List.Forall₂ (· ≤ ·) as as := by
  induction as with
  | nil => exact .nil
  | cons a as ih => exact .cons le_rfl ih

end Envelope

end GraphIso.Main
