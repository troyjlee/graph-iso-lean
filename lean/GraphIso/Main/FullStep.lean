module

public import GraphIso.Main.FullCase

/-!
# The full procedure: the steps at the instance's sizes

Stage 14j-5d, items 3 and 4 (`PLAN-14.md` §14.9). Each macro-step of the full procedure, with
`.recur` as its sub-solver, from one hypothesis: the recursive call solves every valid instance
of the domain (`MiniDom`) of smaller measure (`MainSub`). The step corollaries of stage 14j-5c
are applied with explicit parameters: `sIn = s = NB²` (the domain's generator bound), and for
M4 and M5 either
* at the instance's sizes, `Lg = ssLgM4 m j sIn`, `ssLgM5 m k sIn` and `uB = m`, as in
  `m4_params` and `m5_params` (`main_m4`, `main_m5`, used by `main_step`); or
* at the domain's bounds (§14.9 item 4), `Lg = domLgM4 NB sIn`, `domLgM5 NB sIn` and `uB = NB`,
  whose conditions hold for every `m ≤ NB`, `j ≤ NB`, `k ≤ NB` (`m4_dom_params`,
  `m5_dom_params`; `main_m4_dom`, `main_m5_dom`). The instance-level `Lg` is at most the
  domain-level one (`ssLgM4_le_dom`, `ssLgM5_le_dom`).

Both are instances of `main_m4_at` and `main_m5_at`, which take any `Lg` (and `uB`) meeting the
corollaries' conditions. The children of every step stay in the domain (`SizeChild.closed`).

The work of each step is an explicit function of the instance's sizes (`m0WorkSS`, `m3WorkSS`,
`rbOverSS` and the work functions of stage 14j-5c).

**The label invariant** (stage 14j-6a, `PLAN-14.md` §14.10). Every step lemma takes a flag `b`
and the hypothesis `LabInvIf b I` (`LabInv I` when `b` holds), and its sub-solver hypothesis
`MainSubB` covers the domain's instances with `LabInvIf b`: a step's children have `LabInv`
when the parent has it (`main_predB`, from `SizeChild.lab`). `b = false` is the hypothesis
`MainSub` of stage 14j-5d (`MainSub.toB`); `b = true` is `MainSubL` (`MainSubL.toB`). The
dispatcher's normalization of the labels keeps the invariant (`labLen_normLabD_le`,
`LabInvIf.normLab`).
-/

@[expose] public section

namespace GraphIso.Main

open Equiv Cost GraphIso GraphIso.Programs GraphIso.Toolkit GraphIso.Recursion Sims

/-! ### The work functions -/

section Work

/-- **M0's work with Schreier–Sims** for `n` string positions, degree `N`, a window of `p`
points, `g` generators and sub-solver answers of at most `s` generators. The re-based group has
degree at most `2n`. -/
def m0WorkSS (n N p g s : ℕ) : ℕ :=
  m0StepCost n N p g s (genCost (2 * n) g + 2) (Sims.liftCost N g n + 7) (genCost N s + 2)

/-- **M3's work with Schreier–Sims**: at most `(N − n)!` coset representatives of the kernel,
which has at most `N²` generators, and sub-solver answers of at most `s ≥ N²` generators. -/
def m3WorkSS (n N p g s : ℕ) : ℕ :=
  kerRedCost N n p (N - n).factorial (N * N) s (kerCost N g (N - n) + 5)
    (orbitsCost N (N * N) p + 5) (Sims.repsCost N g (N * N) (N - n).factorial + 7)
    (genCost N ((N - n).factorial * (s + 1)) + 2) + 5

/-- **The restriction's work in M5** (`rbCost` without its continuation), at degree `N`, a
window of `p` points, base `m`, `g` generators and `s` generators of the sub-solver's
answers. -/
def rbOverSS (N p m g s : ℕ) : ℕ :=
  rbCost N p m g 0 s (N * N) (genCost N s + 2) (Sims.liftCost N s N + 7) (kerCost N s N + 5)
    (genCost N (N * N + s) + 2)

theorem rbCost_eq (N k m s C' s' sK Bgm Blift Bker Bgn : ℕ) :
    rbCost N k m s C' s' sK Bgm Blift Bker Bgn =
      rbCost N k m s 0 s' sK Bgm Blift Bker Bgn + C' := by
  unfold rbCost
  omega

theorem rbCost_mono_Bgm {N k m s C' s' sK Bgm Bgm' Blift Bker Bgn : ℕ} (h : Bgm ≤ Bgm') :
    rbCost N k m s C' s' sK Bgm Blift Bker Bgn ≤ rbCost N k m s C' s' sK Bgm' Blift Bker Bgn := by
  unfold rbCost
  omega

/-- The bound on M5's children's factor: Cases 1, 2b and 3 at `uB = m`. -/
def m5FB (m k : ℕ) : ℕ :=
  m + Case3.c3R k m (Case2b.sojZ m) * m.factorial +
    (Case3.c3R k m (Case2b.sojZ m) * m.factorial + m.factorial) + c2bRU m * m.factorial

/-- The bound on M5's children's factor at a union-cell bound `u ≥ m`: Cases 1, 2b and 3. -/
def m5FBu (m k u : ℕ) : ℕ :=
  m + Case3.c3R k m (Case2b.sojZ m) * max m u.factorial +
    (Case3.c3R k m (Case2b.sojZ m) * m.factorial + m.factorial) + c2bRU m * max m u.factorial

theorem m5FBu_self (m k : ℕ) : m5FBu m k m = m5FB m k := by
  unfold m5FBu m5FB
  rw [max_eq_right (Nat.self_le_factorial m)]

end Work

/-! ### The parameters at the domain's bounds -/

section DomParams

/-- **M4's `Lg` at the domain's bounds**: a base and an individualization depth of at most `NB`
points, `s` generators. -/
def domLgM4 (NB s : ℕ) : ℕ := (NB.factorial + NB ^ NB * msCount NB) * (s + 1)

/-- **M5's `Lg` at the domain's bounds**: a base and a certificate size of at most `NB`, `s`
generators, with `uB = NB`. -/
def domLgM5 (NB s : ℕ) : ℕ :=
  (NB.factorial + c2bRU NB + Case3.c3R NB NB (Case2b.sojZ NB)) * (s + 1)

theorem msCount_mono {a b : ℕ} (h : a ≤ b) : msCount a ≤ msCount b := by
  unfold msCount
  have := Nat.clog_mono_right 2 h
  exact Nat.pow_le_pow_right two_pos (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))

theorem pow_le_dom {m j NB : ℕ} (hm : m ≤ NB) (hj : j ≤ NB) : m ^ j ≤ NB ^ NB := by
  rcases Nat.eq_zero_or_pos NB with h0 | hpos
  · subst h0
    have hm0 : m = 0 := by omega
    have hj0 : j = 0 := by omega
    subst hm0
    subst hj0
    exact le_rfl
  · exact (Nat.pow_le_pow_left hm j).trans (Nat.pow_le_pow_right hpos hj)

theorem m4R_le_dom {m j NB : ℕ} (hm : m ≤ NB) (hj : j ≤ NB) : m4R m j ≤ NB ^ NB * msCount NB :=
  Nat.mul_le_mul (pow_le_dom hm hj) (msCount_mono (by omega))

theorem c2bRU_mono {a b : ℕ} (h : a ≤ b) : c2bRU a ≤ c2bRU b := by
  unfold c2bRU
  have hp : (a + 1) ^ a ≤ (b + 1) ^ b :=
    (Nat.pow_le_pow_left (by omega) a).trans (Nat.pow_le_pow_right (by omega) h)
  have hz := Case2b.sojZ_mono h
  exact Nat.mul_le_mul hp (Nat.mul_le_mul (Nat.mul_le_mul h h) (by omega))

theorem c3R_le_dom {k m NB Z Z' : ℕ} (hk : k ≤ NB) (hm : m ≤ NB) (hZ : Z ≤ Z') :
    Case3.c3R k m Z ≤ Case3.c3R NB NB Z' := by
  unfold Case3.c3R
  have := pow_le_dom hm hk
  exact Nat.mul_le_mul (Nat.mul_le_mul hk (by omega)) (by omega)

/-- **M4's conditions at the domain's bounds**: `hLg` and `hLR` of `RunsWithin.m4StepProg_ss` at
`Lg = domLgM4 NB s`, for every base of `m ≤ NB` points and depth `j ≤ NB`. -/
theorem m4_dom_params {m j NB : ℕ} (s : ℕ) (hm : m ≤ NB) (hj : j ≤ NB) :
    m.factorial * (s + 1) ≤ domLgM4 NB s ∧ m4R m j * (s + 1) ≤ domLgM4 NB s := by
  have hf := Nat.factorial_le hm
  have hR := m4R_le_dom hm hj
  unfold domLgM4
  exact ⟨Nat.mul_le_mul_right _ (by omega), Nat.mul_le_mul_right _ (by omega)⟩

/-- **M5's conditions at the domain's bounds**: `hLg`, `huB`, `hLgJ` and `hLY` of
`RunsWithin.m5StepCJProg_ss` at `Lg = domLgM5 NB s` and `uB = NB`, for every base of `m ≤ NB`
points and certificate size `k ≤ NB`. -/
theorem m5_dom_params {m k NB : ℕ} (s : ℕ) (hm : m ≤ NB) (hk : k ≤ NB) :
    m.factorial * (s + 1) ≤ domLgM5 NB s ∧ m ≤ NB ∧
      max m NB.factorial * (s + 1) ≤ domLgM5 NB s ∧
      (c2bRU m + Case3.c3R k m (Case2b.sojZ m)) * (s + 1) ≤ domLgM5 NB s := by
  have hf := Nat.factorial_le hm
  have hfN := Nat.self_le_factorial NB
  have h2 := c2bRU_mono hm
  have h3 := c3R_le_dom (Z := Case2b.sojZ m) (Z' := Case2b.sojZ NB) hk hm (Case2b.sojZ_mono hm)
  have hmax : max m NB.factorial = NB.factorial := max_eq_right (by omega)
  unfold domLgM5
  rw [hmax]
  exact ⟨Nat.mul_le_mul_right _ (by omega), hm, Nat.mul_le_mul_right _ (by omega),
    Nat.mul_le_mul_right _ (by omega)⟩

/-- The instance-level `Lg` of M4 is at most the domain-level one. -/
theorem ssLgM4_le_dom {m j NB : ℕ} (s : ℕ) (hm : m ≤ NB) (hj : j ≤ NB) :
    ssLgM4 m j s ≤ domLgM4 NB s := by
  have hf := Nat.factorial_le hm
  have hR := m4R_le_dom hm hj
  unfold ssLgM4 domLgM4
  exact Nat.mul_le_mul_right _ (by omega)

/-- The instance-level `Lg` of M5 is at most the domain-level one. -/
theorem ssLgM5_le_dom {m k NB : ℕ} (s : ℕ) (hm : m ≤ NB) (hk : k ≤ NB) :
    ssLgM5 m k s ≤ domLgM5 NB s := by
  have hf := Nat.factorial_le hm
  have h2 := c2bRU_mono hm
  have h3 := c3R_le_dom (Z := Case2b.sojZ m) (Z' := Case2b.sojZ NB) hk hm (Case2b.sojZ_mono hm)
  unfold ssLgM5 domLgM5
  exact Nat.mul_le_mul_right _ (by omega)

end DomParams

/-! ### The domain's sub-solver -/

section Sub

variable {n₀ nB NB : ℕ}

/-- **The sub-solver hypothesis of the full procedure** at the instance `I`: the recursive call
solves every valid instance of the domain of smaller measure, within `C` of its measure. -/
def MainSub (thr : ThrProg Ty.unit) (n₀ nB NB : ℕ) (I : HInstData Ty.unit)
    (C : ℕ → Option ℕ → ℕ) : Prop :=
  HSubSolves ssCtx (mainBody thr Ty.denote) ssDV (fun J => Prog.recur J)
    (fun J => MiniDom n₀ nB NB J ∧ MeasLt (hmeasure J) (hmeasure I)) C (NB * NB)

/-- **A child of a step** is in the domain and of smaller measure, from its size facts with a
generator bound at most `NB²` and a smaller measure. -/
theorem main_pred (h2 : 2 * nB ≤ NB) {I J : HInstData Ty.unit} (hd : MiniDom n₀ nB NB I)
    (hJ : HInstValid ssDV J) {sC : ℕ} (hS : SizeChild sC I J) (hs : sC ≤ NB * NB)
    (hlt : MeasLt (J.winSize, J.baseOpt.getD (2 * J.winSize + 1))
      (I.winSize, I.baseOpt.getD (2 * I.winSize + 1))) :
    MiniDom n₀ nB NB J ∧ MeasLt (hmeasure J) (hmeasure I) := by
  rw [hmeasure_eq, hmeasure_eq]
  exact ⟨(mini_child h2 hd hJ hS hs).1, hlt⟩

/-- **A step's sub-solver hypothesis** from the domain's. -/
theorem MainSub.step {thr : ThrProg Ty.unit} {I : HInstData Ty.unit} {C : ℕ → Option ℕ → ℕ}
    (h : MainSub thr n₀ nB NB I C) {P : HInstData Ty.unit → Prop}
    (hP : ∀ J, HInstValid ssDV J → P J → MiniDom n₀ nB NB J ∧ MeasLt (hmeasure J) (hmeasure I)) :
    HSubSolves ssCtx (mainBody thr Ty.denote) ssDV (fun J => Prog.recur J) P C (NB * NB) :=
  fun J hJ hPJ => h J hJ (hP J hJ hPJ)

/-- **The label invariant when `b` holds** (stage 14j-6a): `main_step` and `main_step_lab` are
the cases `b = false` and `b = true` of one proof. -/
def LabInvIf (b : Bool) (J : HInstData Ty.unit) : Prop := b = true → LabInv J

/-- The sub-solver hypothesis with the label invariant when `b` holds. -/
def MainSubB (thr : ThrProg Ty.unit) (b : Bool) (n₀ nB NB : ℕ) (I : HInstData Ty.unit)
    (C : ℕ → Option ℕ → ℕ) : Prop :=
  HSubSolves ssCtx (mainBody thr Ty.denote) ssDV (fun J => Prog.recur J)
    (fun J => MiniDom n₀ nB NB J ∧ LabInvIf b J ∧ MeasLt (hmeasure J) (hmeasure I)) C (NB * NB)

/-- **The sub-solver hypothesis with the label invariant** (stage 14j-6a): the recursive call
solves every valid instance of the domain with `LabInv` of smaller measure, within `C`. -/
def MainSubL (thr : ThrProg Ty.unit) (n₀ nB NB : ℕ) (I : HInstData Ty.unit)
    (C : ℕ → Option ℕ → ℕ) : Prop :=
  HSubSolves ssCtx (mainBody thr Ty.denote) ssDV (fun J => Prog.recur J)
    (fun J => MiniDom n₀ nB NB J ∧ LabInv J ∧ MeasLt (hmeasure J) (hmeasure I)) C (NB * NB)

theorem MainSub.toB {thr : ThrProg Ty.unit} {I : HInstData Ty.unit} {C : ℕ → Option ℕ → ℕ}
    (h : MainSub thr n₀ nB NB I C) : MainSubB thr false n₀ nB NB I C :=
  h.mono fun _ hJ => ⟨hJ.1, hJ.2.2⟩

theorem MainSubL.toB {thr : ThrProg Ty.unit} {I : HInstData Ty.unit} {C : ℕ → Option ℕ → ℕ}
    (h : MainSubL thr n₀ nB NB I C) : MainSubB thr true n₀ nB NB I C :=
  h.mono fun _ hJ => ⟨hJ.1, hJ.2.1 rfl, hJ.2.2⟩

/-- **A step's sub-solver hypothesis** from `MainSubB`. -/
theorem MainSubB.step {thr : ThrProg Ty.unit} {b : Bool} {I : HInstData Ty.unit}
    {C : ℕ → Option ℕ → ℕ} (h : MainSubB thr b n₀ nB NB I C) {P : HInstData Ty.unit → Prop}
    (hP : ∀ J, HInstValid ssDV J → P J →
      MiniDom n₀ nB NB J ∧ LabInvIf b J ∧ MeasLt (hmeasure J) (hmeasure I)) :
    HSubSolves ssCtx (mainBody thr Ty.denote) ssDV (fun J => Prog.recur J) P C (NB * NB) :=
  fun J hJ hPJ => h J hJ (hP J hJ hPJ)

/-- **A child of a step** is in the domain, of smaller measure, and has the label invariant
when its parent has it (`SizeChild.lab`). -/
theorem main_predB (h2 : 2 * nB ≤ NB) {b : Bool} {I J : HInstData Ty.unit}
    (hd : MiniDom n₀ nB NB I) (hb : LabInvIf b I)
    (hJ : HInstValid ssDV J) {sC : ℕ} (hS : SizeChild sC I J) (hs : sC ≤ NB * NB)
    (hlt : MeasLt (J.winSize, J.baseOpt.getD (2 * J.winSize + 1))
      (I.winSize, I.baseOpt.getD (2 * I.winSize + 1))) :
    MiniDom n₀ nB NB J ∧ LabInvIf b J ∧ MeasLt (hmeasure J) (hmeasure I) :=
  have h := main_pred h2 hd hJ hS hs hlt
  ⟨h.1, fun hb' => hS.lab (hb hb'), h.2⟩

/-- **The normalized labels are no longer**: `normLabD n L` keeps the labels at `0, …, n − 1`. -/
theorem labLen_normLabD_le (n : ℕ) (L : LabelData) : labLen (normLabD n L) ≤ labLen L := by
  refine labLen_le_iff.2 fun l hl => ?_
  simp only [normLabD, List.toList_toArray] at hl
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hl
  exact length_getD_le_labLen L i

/-- The label invariant survives the dispatcher's normalization of the labels. -/
theorem LabInvIf.normLab {b : Bool} {xy : StrData × StrData} {w : WinData} {σd : PermData}
    {N : ℕ} {gs : GensData} {n₀' n : ℕ} {L : LabelData}
    (h : LabInvIf b (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit)) :
    LabInvIf b (((xy, w, σd, N, gs, ()), n₀', n, some (normLabD n L)) : HInstData Ty.unit) :=
  fun hb => ⟨(h hb).n_le, fun L' hL' => by
    obtain rfl := Option.some.inj hL'
    exact ((h hb).hint L rfl).mono le_rfl (labLen_normLabD_le n L)⟩

end Sub

/-! ### The steps -/

section Steps

variable {thr : ThrProg Ty.unit} {n₀ nB NB : ℕ} {xy : StrData × StrData} {w : WinData}
  {σd : PermData} {N : ℕ} {gs : GensData} {n₀' n : ℕ} {C : ℕ → Option ℕ → ℕ} {b : Bool}

/-- **The chain rule** in the full procedure. -/
theorem main_chain (h2 : 2 * nB ≤ NB)
    (hI : HInstValid ssDV (((xy, w, σd, N, gs, ()), n₀', n, none) : HInstData Ty.unit))
    (hd : MiniDom n₀ nB NB (((xy, w, σd, N, gs, ()), n₀', n, none) : HInstData Ty.unit))
    (hsub : MainSubB thr b n₀ nB NB
      (((xy, w, σd, N, gs, ()), n₀', n, none) : HInstData Ty.unit) C)
    (hbL : LabInvIf b (((xy, w, σd, N, gs, ()), n₀', n, none) : HInstData Ty.unit))
    {os : List (List ℕ)} (hos : IsOrbitPartition (GensData.denote N gs) w os)
    (h2os : 2 ≤ os.length) :
    ∃ (ans : AnswerData Ty.unit) (ch : List (ℕ × Option ℕ)),
      RunsWithin ssCtx (mainBody thr Ty.denote)
        (Main.chainProg (fun J => Prog.recur J)
          (((xy, w, σd, N, gs, ()), n₀', n, none) : HInstData Ty.unit) os) ans
        ((ch.map fun x => C x.1 x.2).sum + chainCost N w.1.length w.1.length) ∧
      InstData.OK (D := Ty.unit) (xy, w, σd, N, gs, ()) ssDV ans ∧
      (∀ c : CosetData Ty.unit, ans = some c → c.2.gens.length ≤ NB * NB) ∧
      ChildList w.1.length 1 (ChainChild w.1.length) ch := by
  obtain ⟨ans, ch, hrun, hok, hg, hch⟩ := RunsWithin.chainProg hI hos h2os
    (hsub.step fun J hJ ⟨hS, hc⟩ => main_predB h2 hd hbL hJ hS (max_le le_rfl hd.gens_le)
      (ChainChild.measLt hc))
  have hosl := IsOrbitPartition.length_le_win hos
  have hc : chainCost N w.1.length os.length ≤ chainCost N w.1.length w.1.length := by
    unfold chainCost
    gcongr
  exact ⟨ans, ch, hrun.mono (Nat.add_le_add_left hc _), hok,
    fun c hc => (hg c hc).trans (max_le le_rfl hd.gens_le), hch⟩

/-- **M0** in the full procedure. -/
theorem main_m0 (h2 : 2 * nB ≤ NB)
    (hI : HInstValid ssDV (((xy, w, σd, N, gs, ()), n₀', n, none) : HInstData Ty.unit))
    (hd : MiniDom n₀ nB NB (((xy, w, σd, N, gs, ()), n₀', n, none) : HInstData Ty.unit))
    (hsub : MainSubB thr b n₀ nB NB
      (((xy, w, σd, N, gs, ()), n₀', n, none) : HInstData Ty.unit) C)
    (hbL : LabInvIf b (((xy, w, σd, N, gs, ()), n₀', n, none) : HInstData Ty.unit))
    (htr : IsTransOn (GensData.denote N gs) (w.denote N)) (h2w : 2 ≤ w.1.length) :
    ∃ (ans : AnswerData Ty.unit) (ch : List (ℕ × Option ℕ)),
      RunsWithin ssCtx (mainBody thr Ty.denote)
        (Main.m0StepProg (fun J => Prog.recur J)
          (((xy, w, σd, N, gs, ()), n₀', n, none) : HInstData Ty.unit)) ans
        ((ch.map fun x => C x.1 x.2).sum + m0WorkSS n N w.1.length gs.length (NB * NB)) ∧
      InstData.OK (D := Ty.unit) (xy, w, σd, N, gs, ()) ssDV ans ∧
      (∀ c : CosetData Ty.unit, ans = some c → c.2.gens.length ≤ NB * NB) ∧
      ChildList w.1.length 1 (FreeChild w.1.length (2 * w.1.length + 1)) ch := by
  have hwn := sh_length_le hI
  have hn : n ≤ nB := hd.n_le
  have hN : N ≤ NB := hd.degree_le
  obtain ⟨hk, hsC⟩ := ss_m0_gens_le hI htr h2w
  have hsC' : (rebaseModel ssCtx.O n N (Luks.maxBlocks N gs w.1) gs).2.1.length ≤ NB * NB :=
    hsC.trans (Nat.mul_le_mul (by omega) (by omega))
  have hB : ssCtx.B.call GroupOp.generate (n + (Luks.maxBlocks N gs w.1).length,
      rebaseGens n N (Luks.maxBlocks N gs w.1) gs)
      (rebaseModel ssCtx.O n N (Luks.maxBlocks N gs w.1) gs) ≤ genCost (2 * n) gs.length + 2 := by
    change genCost _ (rebaseGens n N (Luks.maxBlocks N gs w.1) gs).length + 2 ≤ _
    rw [rebaseGens, List.length_map]
    exact Nat.add_le_add_right (genCost_mono₂ hk le_rfl) 2
  obtain ⟨ans, ch, hrun, hok, hg, hch⟩ := RunsWithin.m0StepProg (X := ssCtx)
    (fun op x _ hx => ssOracle_meets op x hx) (fun _ _ _ h => h) hI htr h2w
    (hsub.step fun J hJ ⟨hS, hc⟩ => main_predB h2 hd hbL hJ hS hsC'
      (FreeChild.measLt hc (by omega)))
    hB (ss_hint_hBlift N n gs ()) (ss_hint_hBgen N (NB * NB) gs)
  exact ⟨ans, ch, hrun, hok,
    hg (NB * NB) (fun hs hv _ => (ssOracle_gens_le hv).1.trans (Nat.mul_le_mul hN hN)), hch⟩

/-- **M1** in the full procedure: the base is not transitive. -/
theorem main_m1 (h2 : 2 * nB ≤ NB) {L : LabelData}
    (hI : HInstValid ssDV (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit))
    (hd : MiniDom n₀ nB NB (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit))
    (hsub : MainSubB thr b n₀ nB NB
      (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit) C)
    (hbL : LabInvIf b (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit))
    (hnt : ¬ IsTransOn (GensData.denote N gs) (baseSet n N)) :
    ∃ (ans : AnswerData Ty.unit) (ch : List (ℕ × Option ℕ)),
      RunsWithin ssCtx (mainBody thr Ty.denote)
        (Main.m1StepProg (fun J => Prog.recur J)
          (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit) L) ans
        ((ch.map fun x => C x.1 x.2).sum + m1WorkSS n (N - n) w.1.length gs.length (NB * NB)) ∧
      InstData.OK (D := Ty.unit) (xy, w, σd, N, gs, ()) ssDV ans ∧
      (∀ c : CosetData Ty.unit, ans = some c → c.2.gens.length ≤ NB * NB) ∧
      ChildList w.1.length 1 (FreeChild w.1.length (N - n)) ch := by
  have hN : N ≤ NB := hd.degree_le
  have hm : 1 ≤ N - n := hI.base_pos rfl
  have hW : 1 ≤ w.1.length := hI.win_pos rfl
  have hgs : GensData.AllValid N gs := hI.valid.group.1
  have hb : IsInvariant (GensData.denote N gs) (baseSet n N) := hI.base_inv
  obtain ⟨hdeg, -, hlenO, -, hlen, -⟩ := ss_m1_child (d := ()) (w := w) (L := L)
    hgs hb (show n < N by omega)
  have hsC : (rebaseModel ssCtx.O n N (singD (m1O ssCtx.O n N (N, gs, ()) w L)) gs).2.1.length ≤
      NB * NB := by
    have hle : (m1Model ssCtx.O n N (N, gs, ()) w L).1.1 ≤ NB := by omega
    exact hlen.trans (Nat.mul_le_mul hle hle)
  obtain ⟨ans, ch, hrun, hok, hg, hch⟩ := RunsWithin.m1StepProg_ss hI hnt
    (hsub.step fun J hJ ⟨hS, hc⟩ => main_predB h2 hd hbL hJ hS hsC (FreeChild.measLt hc hW))
  exact ⟨ans, ch, hrun, hok,
    hg (NB * NB) (fun hs hv _ => (ssOracle_gens_le hv).1.trans (Nat.mul_le_mul hN hN)), hch⟩

/-- The re-based group onto the maximal blocks of a transitive base has at most `N²`
generators, and the block facts. -/
theorem ss_mb_facts {L : LabelData}
    (hI : HInstValid ssDV (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit))
    (htrB : IsTransOn (GensData.denote N gs) (baseSet n N))
    (hok : blkOKD (N - n) (mbD n N gs) = true) :
    (rebaseModel ssCtx.O n N (mbD n N gs) gs).2.1.length ≤ N * N ∧
      IsBlockList (WinData.ofPoints N (basePts n N)) (mbD n N gs) ∧
      PermutesBlocks (GensData.denote N gs) (mbD n N gs) ∧
      IsBlockSys (baseHom (GensData.denote N gs) n hI.base_inv) (blockFam n N (mbD n N gs)) ∧
      2 ≤ (blockFam n N (mbD n N gs)).card ∧
      (mbD n N gs).flatten.length = N - n ∧ 2 * (mbD n N gs).length ≤ N - n := by
  have hgs : GensData.AllValid N gs := hI.valid.group.1
  have hb : IsInvariant (GensData.denote N gs) (baseSet n N) := hI.base_inv
  have hn : n ≤ N := hI.le
  obtain ⟨h2k, hh⟩ := blkOKD_iff.1 hok
  obtain ⟨hbs, hGb, hΨ, hcard, hsz⟩ := dv_blocks_facts hgs hb htrB h2k hh
  have hflat : (mbD n N gs).flatten.length = N - n := by
    rw [hbs.1.length_eq]
    exact length_basePts n N
  have h2bs : 2 * (mbD n N gs).length ≤ N - n := hflat ▸ mf_two_mul_length_le hsz
  have hwbv : (WinData.ofPoints N (basePts n N)).Valid N :=
    WinData.valid_ofPoints (basePts_nodup _ _) fun i hi => (mem_basePts.1 hi).2
  have hle : n + (mbD n N gs).length ≤ N := by omega
  exact ⟨(ss_rebase_gens_le hn hb hwbv hbs hGb hgs).trans (Nat.mul_le_mul hle hle), hbs, hGb, hΨ,
    hcard, hflat, h2bs⟩

/-- **M2a** in the full procedure: proper maximal blocks, some window label not
equidistributed over them. -/
theorem main_m2a (h2 : 2 * nB ≤ NB) {L : LabelData}
    (hI : HInstValid ssDV (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit))
    (hd : MiniDom n₀ nB NB (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit))
    (hsub : MainSubB thr b n₀ nB NB
      (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit) C)
    (hbL : LabInvIf b (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit))
    (htrB : IsTransOn (GensData.denote N gs) (baseSet n N))
    (hok : blkOKD (N - n) (mbD n N gs) = true) (hne : neqD n N (mbD n N gs) L w.1 = true) :
    ∃ (ans : AnswerData Ty.unit) (ch : List (ℕ × Option ℕ)),
      RunsWithin ssCtx (mainBody thr Ty.denote)
        (Main.m2aStepProg (fun J => Prog.recur J)
          (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit) L (mbD n N gs)) ans
        ((ch.map fun x => C x.1 x.2).sum +
          m2aWorkSS n (N - n) w.1.length gs.length (NB * NB) L.size) ∧
      InstData.OK (D := Ty.unit) (xy, w, σd, N, gs, ()) ssDV ans ∧
      (∀ c : CosetData Ty.unit, ans = some c → c.2.gens.length ≤ NB * NB) ∧
      ChildList w.1.length 1 (FreeChild w.1.length (N - n)) ch := by
  have hN : N ≤ NB := hd.degree_le
  have hW : 1 ≤ w.1.length := hI.win_pos rfl
  obtain ⟨hsC, -⟩ := ss_mb_facts hI htrB hok
  obtain ⟨ans, ch, hrun, hok', hg, hch⟩ := RunsWithin.m2aStepProg_ss hI htrB hok hne
    (hsub.step fun J hJ ⟨hS, hc⟩ => main_predB h2 hd hbL hJ hS
      (hsC.trans (Nat.mul_le_mul hN hN)) (FreeChild.measLt hc hW))
  exact ⟨ans, ch, hrun, hok',
    hg (NB * NB) (fun hs hv _ => (ssOracle_gens_le hv).1.trans (Nat.mul_le_mul hN hN)), hch⟩

/-- **M2b** in the full procedure: proper maximal blocks, every window label equidistributed
over them. At most `N − n` children per window point. -/
theorem main_m2b (h2 : 2 * nB ≤ NB) {L : LabelData}
    (hI : HInstValid ssDV (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit))
    (hd : MiniDom n₀ nB NB (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit))
    (hsub : MainSubB thr b n₀ nB NB
      (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit) C)
    (hbL : LabInvIf b (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit))
    (htrB : IsTransOn (GensData.denote N gs) (baseSet n N))
    (hok : blkOKD (N - n) (mbD n N gs) = true) (hne : neqD n N (mbD n N gs) L w.1 = false) :
    ∃ (ans : AnswerData Ty.unit) (ch : List (ℕ × Option ℕ)),
      RunsWithin ssCtx (mainBody thr Ty.denote)
        (Main.m2bStepProg (fun J => Prog.recur J)
          (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit) (mbD n N gs)) ans
        ((ch.map fun x => C x.1 x.2).sum +
          m2bWorkSS n (N - n) w.1.length gs.length L.size (NB * NB)) ∧
      InstData.OK (D := Ty.unit) (xy, w, σd, N, gs, ()) ssDV ans ∧
      (∀ c : CosetData Ty.unit, ans = some c → c.2.gens.length ≤ NB * NB) ∧
      ChildList w.1.length (N - n) (StepChild w.1.length (N - n)) ch := by
  have hN : N ≤ NB := hd.degree_le
  have hW : 1 ≤ w.1.length := hI.win_pos rfl
  have hm : 1 ≤ N - n := hI.base_pos rfl
  have hh : HintValid n N gs w L := (hI.hint L rfl).1
  obtain ⟨-, hbs, hGb, hΨ, hcard, -, h2bs⟩ := ss_mb_facts hI htrB hok
  have hall : ∀ u ∈ w.1, equidistB (mbD n N gs).length (m2aIdx n N (mbD n N gs))
      (L.getD u []) = true := by
    intro u hu
    by_contra hcon
    have : neqD n N (mbD n N gs) L w.1 = true := List.any_eq_true.2 ⟨u, hu, by simpa using hcon⟩
    rw [hne] at this
    exact Bool.false_ne_true this
  obtain ⟨u₀, hu₀⟩ := List.exists_mem_of_ne_nil _
    (List.ne_nil_of_length_pos (show 0 < w.1.length by change 1 ≤ w.1.length at hW; omega))
  have hu₀N : u₀ < N := hI.valid.win.lt u₀ hu₀
  have heq : Equidist (blockFam n N (mbD n N gs)) (labOf n N L ⟨u₀, hu₀N⟩) := by
    rw [← mf_blockFamily_eq hbs]
    exact (equidistB_iff (hh.lab_nodup u₀ hu₀) (fun x => mem_labOf)
      (hh.lab_lt u₀ hu₀)).1 (hall u₀ hu₀)
  obtain ⟨ans, ch, hrun, hok', hg, hch, hR⟩ := RunsWithin.m2bStepProg_ss hI hbs hGb hΨ hcard
    (dv_baseHom_trans hI.base_inv htrB) (u₀ := ⟨u₀, hu₀N⟩) hu₀ heq
    (hsub.step fun J hJ ⟨hS, hc⟩ => main_predB h2 hd hbL hJ hS le_rfl (StepChild.measLt hc hW hm))
    le_rfl (Nat.mul_le_mul hN hN)
  exact ⟨ans, ch, hrun, hok',
    hg (NB * NB) (fun hs hv _ => (ssOracle_gens_le hv).1.trans (Nat.mul_le_mul hN hN)),
    hch.mono_factor (hR.trans (by omega))⟩

/-- **M3** in the full procedure: at most `(N − n)!` cosets of the kernel. -/
theorem main_m3 (h2 : 2 * nB ≤ NB) {L : LabelData}
    (hI : HInstValid ssDV (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit))
    (hd : MiniDom n₀ nB NB (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit))
    (hsub : MainSubB thr b n₀ nB NB
      (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit) C)
    (hbL : LabInvIf b (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit)) :
    ∃ (ans : AnswerData Ty.unit) (ch : List (ℕ × Option ℕ)),
      RunsWithin ssCtx (mainBody thr Ty.denote)
        (Main.m3Prog (fun J => Prog.recur J)
          (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit)) ans
        ((ch.map fun x => C x.1 x.2).sum + m3WorkSS n N w.1.length gs.length (NB * NB)) ∧
      InstData.OK (D := Ty.unit) (xy, w, σd, N, gs, ()) ssDV ans ∧
      (∀ c : CosetData Ty.unit, ans = some c → c.2.gens.length ≤ NB * NB) ∧
      ChildList w.1.length (N - n).factorial (StepChild w.1.length (N - n)) ch := by
  have hN : N ≤ NB := hd.degree_le
  have hgs : GensData.AllValid N gs := hI.valid.group.1
  have hKN : (kerModel ssCtx.O n (N, gs, ())).2.1.length ≤ N * N := ss_ker_gens_le hgs
  have hNN : N * N ≤ NB * NB := Nat.mul_le_mul hN hN
  have hsC : max (NB * NB) (kerModel ssCtx.O n (N, gs, ())).2.1.length ≤ NB * NB :=
    max_le le_rfl (hKN.trans hNN)
  have hW : 1 ≤ w.1.length := hI.win_pos rfl
  have hm : 1 ≤ N - n := hI.base_pos rfl
  have hBk : ssCtx.B.call GroupOp.kernel ((N, gs, ()), baseWin n N)
      (kerModel ssCtx.O n (N, gs, ())) ≤ kerCost N gs.length (N - n) + 5 := by
    change kerCost N gs.length (baseWin n N).1.length + 5 ≤ _
    rw [baseWin_length]
  have hBo : ssCtx.B.call GroupOp.orbits (kerModel ssCtx.O n (N, gs, ()), w)
      (krOrbits ssCtx.O n (N, gs, ()) w) ≤ orbitsCost N (N * N) w.1.length + 5 := by
    change orbitsCost N (kernelModel N gs (baseWin n N)).length w.1.length + 5 ≤ _
    exact Nat.add_le_add_right (rd_orbitsCost_mono₂ le_rfl hKN le_rfl) 5
  have hB : ∀ hs : GensData, GensData.AllValid N hs →
      hs.length ≤ (kerReps ssCtx.O n (N, gs, ())).length *
        (max (NB * NB) (kerModel ssCtx.O n (N, gs, ())).2.1.length + 1) →
      GensData.denote N hs ≤ GensData.denote N gs →
      ssCtx.B.call GroupOp.generate (N, hs) (ssCtx.O.run GroupOp.generate (N, hs)) ≤
        genCost N ((kerReps ssCtx.O n (N, gs, ())).length * (NB * NB + 1)) + 2 := by
    intro hs _ hl _
    change genCost N hs.length + 2 ≤ _
    exact Nat.add_le_add_right (genCost_mono₂ le_rfl
      (hl.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right hsC 1)))) 2
  obtain ⟨ans, ch, hrun, hok, hg, hch, hfact⟩ := RunsWithin.m3Prog (X := ssCtx)
    (fun op x _ hx => ssOracle_meets op x hx) (fun _ _ _ h => h) hI
    (hsub.step fun J hJ ⟨hS, hc⟩ => main_predB h2 hd hbL hJ hS hsC (StepChild.measLt hc hW hm))
    hBk hBo le_rfl hB
  have hBcr : ssCtx.B.call GroupOp.cosetReps ((N, gs, ()), kerModel ssCtx.O n (N, gs, ()))
      (kerReps ssCtx.O n (N, gs, ())) ≤
        Sims.repsCost N gs.length (N * N) (N - n).factorial + 7 := by
    change Sims.repsCost N gs.length (kernelModel N gs (baseWin n N)).length
      (kerReps ssCtx.O n (N, gs, ())).length + 7 ≤ _
    exact Nat.add_le_add_right (mini_repsCost_mono le_rfl le_rfl hKN hfact) 7
  have hw : kerRedCost N n w.1.length (kerReps ssCtx.O n (N, gs, ())).length
      (kerModel ssCtx.O n (N, gs, ())).2.1.length (NB * NB) (kerCost N gs.length (N - n) + 5)
      (orbitsCost N (N * N) w.1.length + 5)
      (ssCtx.B.call GroupOp.cosetReps ((N, gs, ()), kerModel ssCtx.O n (N, gs, ()))
        (kerReps ssCtx.O n (N, gs, ())))
      (genCost N ((kerReps ssCtx.O n (N, gs, ())).length * (NB * NB + 1)) + 2) + 5 ≤
      m3WorkSS n N w.1.length gs.length (NB * NB) := by
    unfold m3WorkSS kerRedCost
    have hg' := genCost_mono₂ (le_refl N) (Nat.mul_le_mul_right (NB * NB + 1) hfact)
    gcongr
  exact ⟨ans, ch, hrun.mono (Nat.add_le_add_left hw _), hok,
    hg (NB * NB) (fun hs hv _ => (ssOracle_gens_le hv).1.trans hNN),
    hch.mono_factor hfact⟩

/-- **M4** in the full procedure: a transitive base that is not a giant, with `4 + j ≤ m` and
`2j ≤ m`, at any `Lg` meeting the corollary's conditions `hLg` and `hLR` with `sIn = NB²`. -/
theorem main_m4_at (h2 : 2 * nB ≤ NB) {L : LabelData}
    (hI : HInstValid ssDV (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit))
    (hd : MiniDom n₀ nB NB (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit))
    (hsub : MainSubB thr b n₀ nB NB
      (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit) C)
    (hbL : LabInvIf b (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit))
    (htr : IsTransOn (GensData.denote N gs) (baseSet n N))
    (hng : m4Deg ssCtx.O n (N, gs, ()) < N - n - 2) (hk4 : 4 + m4J ssCtx.O n (N, gs, ()) ≤ N - n)
    (hS : 2 * m4J ssCtx.O n (N, gs, ()) ≤ N - n) {Lg : ℕ}
    (hLg : (N - n).factorial * (NB * NB + 1) ≤ Lg)
    (hLR : m4R (N - n) (m4J ssCtx.O n (N, gs, ())) * (NB * NB + 1) ≤ Lg) :
    ∃ (ans : AnswerData Ty.unit) (ch : List (ℕ × Option ℕ)),
      RunsWithin ssCtx (mainBody thr Ty.denote)
        (Main.m4StepProg (fun J => Prog.recur J)
          (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit)) ans
        ((ch.map fun x => C x.1 x.2).sum +
          m4WorkSS n (N - n) (m4J ssCtx.O n (N, gs, ())) w.1.length (NB * NB) L.size (NB * NB)
            Lg) ∧
      InstData.OK (D := Ty.unit) (xy, w, σd, N, gs, ()) ssDV ans ∧
      (∀ c : CosetData Ty.unit, ans = some c → c.2.gens.length ≤ NB * NB) ∧
      ChildList w.1.length (m4R (N - n) (m4J ssCtx.O n (N, gs, ())) * (N - n).factorial)
        (StepChild w.1.length (N - n)) ch := by
  have hN : N ≤ NB := hd.degree_le
  have hgl : gs.length ≤ NB * NB := hd.gens_le
  have hW : 1 ≤ w.1.length := hI.win_pos rfl
  have hm : 1 ≤ N - n := hI.base_pos rfl
  obtain ⟨ans, ch, hrun, hok, hg, hch, hR⟩ := RunsWithin.m4StepProg_ss hI
    (dv_baseHom_trans hI.base_inv htr) hng hk4 hS
    (hsub.step fun J hJ ⟨hS', hc⟩ => main_predB h2 hd hbL hJ hS' le_rfl (StepChild.measLt hc hW hm))
    hgl (Nat.mul_le_mul hN hN) le_rfl (Lg := Lg) hLg hLR
  exact ⟨ans, ch, hrun, hok, hg, hch.mono_factor (Nat.mul_le_mul_right _ hR)⟩

/-- **M4** at the instance's sizes: `Lg = ssLgM4 m j NB²`. -/
theorem main_m4 (h2 : 2 * nB ≤ NB) {L : LabelData}
    (hI : HInstValid ssDV (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit))
    (hd : MiniDom n₀ nB NB (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit))
    (hsub : MainSubB thr b n₀ nB NB
      (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit) C)
    (hbL : LabInvIf b (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit))
    (htr : IsTransOn (GensData.denote N gs) (baseSet n N))
    (hng : m4Deg ssCtx.O n (N, gs, ()) < N - n - 2) (hk4 : 4 + m4J ssCtx.O n (N, gs, ()) ≤ N - n)
    (hS : 2 * m4J ssCtx.O n (N, gs, ()) ≤ N - n) :
    ∃ (ans : AnswerData Ty.unit) (ch : List (ℕ × Option ℕ)),
      RunsWithin ssCtx (mainBody thr Ty.denote)
        (Main.m4StepProg (fun J => Prog.recur J)
          (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit)) ans
        ((ch.map fun x => C x.1 x.2).sum +
          m4WorkSS n (N - n) (m4J ssCtx.O n (N, gs, ())) w.1.length (NB * NB) L.size (NB * NB)
            (ssLgM4 (N - n) (m4J ssCtx.O n (N, gs, ())) (NB * NB))) ∧
      InstData.OK (D := Ty.unit) (xy, w, σd, N, gs, ()) ssDV ans ∧
      (∀ c : CosetData Ty.unit, ans = some c → c.2.gens.length ≤ NB * NB) ∧
      ChildList w.1.length (m4R (N - n) (m4J ssCtx.O n (N, gs, ())) * (N - n).factorial)
        (StepChild w.1.length (N - n)) ch :=
  main_m4_at h2 hI hd hsub hbL htr hng hk4 hS
    (by unfold ssLgM4; exact Nat.mul_le_mul_right _ (Nat.le_add_right _ _))
    (by unfold ssLgM4; exact Nat.mul_le_mul_right _ (Nat.le_add_left _ _))

/-- **M4** at the domain's bounds: `Lg = domLgM4 NB NB²` (§14.9 item 4). -/
theorem main_m4_dom (h2 : 2 * nB ≤ NB) {L : LabelData}
    (hI : HInstValid ssDV (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit))
    (hd : MiniDom n₀ nB NB (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit))
    (hsub : MainSubB thr b n₀ nB NB
      (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit) C)
    (hbL : LabInvIf b (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit))
    (htr : IsTransOn (GensData.denote N gs) (baseSet n N))
    (hng : m4Deg ssCtx.O n (N, gs, ()) < N - n - 2) (hk4 : 4 + m4J ssCtx.O n (N, gs, ()) ≤ N - n)
    (hS : 2 * m4J ssCtx.O n (N, gs, ()) ≤ N - n) :
    ∃ (ans : AnswerData Ty.unit) (ch : List (ℕ × Option ℕ)),
      RunsWithin ssCtx (mainBody thr Ty.denote)
        (Main.m4StepProg (fun J => Prog.recur J)
          (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit)) ans
        ((ch.map fun x => C x.1 x.2).sum +
          m4WorkSS n (N - n) (m4J ssCtx.O n (N, gs, ())) w.1.length (NB * NB) L.size (NB * NB)
            (domLgM4 NB (NB * NB))) ∧
      InstData.OK (D := Ty.unit) (xy, w, σd, N, gs, ()) ssDV ans ∧
      (∀ c : CosetData Ty.unit, ans = some c → c.2.gens.length ≤ NB * NB) ∧
      ChildList w.1.length (m4R (N - n) (m4J ssCtx.O n (N, gs, ())) * (N - n).factorial)
        (StepChild w.1.length (N - n)) ch := by
  have hN : N ≤ NB := hd.degree_le
  obtain ⟨hLg, hLR⟩ := m4_dom_params (NB * NB) (show N - n ≤ NB by omega)
    (show m4J ssCtx.O n (N, gs, ()) ≤ NB by omega)
  exact main_m4_at h2 hI hd hsub hbL htr hng hk4 hS hLg hLR


theorem c3R_mono_m {k m m' Z : ℕ} (h : m ≤ m') : Case3.c3R k m Z ≤ Case3.c3R k m' Z := by
  unfold Case3.c3R
  gcongr

theorem c3Count_mono_mx {mx mx' k n : ℕ} (h : mx ≤ mx') : c3Count mx k n ≤ c3Count mx' k n := by
  unfold c3Count
  gcongr

theorem length_rbPts (n N : ℕ) (w : WinData) : (rbPts n N w).length = w.1.length + (N - n) := by
  simp [rbPts, length_basePts]

/-- **M5's children's factor** with Schreier–Sims and `uB = m`, for certificates that are
valid and keep the base invariant. -/
theorem ss_m5CFCJ_le {wl Nr k : ℕ} {fxs fys : GensData} (hfx : GensData.AllValid Nr fxs)
    (hbx : IsInvariant (GensData.denote Nr fxs) (baseSet wl Nr)) (hfy : GensData.AllValid Nr fys)
    (hby : IsInvariant (GensData.denote Nr fys) (baseSet wl Nr)) :
    m5CFCJ ssCtx.O wl Nr k (Nr, fxs, ()) (Nr, fys, ()) (Nr - wl) ≤ m5FB (Nr - wl) k := by
  have hfix := ss_fixPts_le (e := ()) hfy hby
  have hΦx := ss_m5Cs_le (e := ()) hfx hbx
  have hΦy := ss_m5Cs_le (e := ()) hfy hby
  have hf := Nat.self_le_factorial (Nr - wl)
  have hmax : max (Nr - wl) (Nr - wl).factorial = (Nr - wl).factorial := max_eq_right hf
  have h3 := c3R_mono_m (k := k) (Z := Case2b.sojZ (Nr - wl)) hfix
  have h2b := c2bR_le (N := Nr) (n := wl) hΦy
    ((Nat.sub_le _ 1).trans
      (degD_le ssCtx.O Nr wl (Nr, fxs, ()) (m5Cs ssCtx.O wl Nr (Nr, fxs, ())).2))
  unfold m5CFCJ m5FB
  split
  · omega
  · rw [hmax]
    have := Nat.mul_le_mul_right (Nr - wl).factorial h3
    omega
  · split
    · rw [hmax]
      have := Nat.mul_le_mul_right (Nr - wl).factorial h2b
      omega
    · have := Nat.mul_le_mul_right (Nr - wl).factorial h2b
      omega
  · omega

/-- **M5's children's factor** with Schreier–Sims at a union-cell bound `uB ≥ m`. -/
theorem ss_m5CFCJ_le_u {wl Nr k uB : ℕ} {fxs fys : GensData} (hfy : GensData.AllValid Nr fys)
    (hby : IsInvariant (GensData.denote Nr fys) (baseSet wl Nr)) (hu : Nr - wl ≤ uB) :
    m5CFCJ ssCtx.O wl Nr k (Nr, fxs, ()) (Nr, fys, ()) uB ≤ m5FBu (Nr - wl) k uB := by
  have hfix := ss_fixPts_le (e := ()) hfy hby
  have hΦy := ss_m5Cs_le (e := ()) hfy hby
  have hfm : (Nr - wl).factorial ≤ max (Nr - wl) uB.factorial :=
    (Nat.factorial_le hu).trans (le_max_right _ _)
  have h3 := c3R_mono_m (k := k) (Z := Case2b.sojZ (Nr - wl)) hfix
  have h2b := c2bR_le (N := Nr) (n := wl) hΦy
    ((Nat.sub_le _ 1).trans
      (degD_le ssCtx.O Nr wl (Nr, fxs, ()) (m5Cs ssCtx.O wl Nr (Nr, fxs, ())).2))
  unfold m5CFCJ m5FBu
  split
  · omega
  · have := Nat.mul_le_mul_right (max (Nr - wl) uB.factorial) h3
    have := Nat.mul_le_mul_right (Nr - wl).factorial h3
    omega
  · split
    · have := Nat.mul_le_mul_right (max (Nr - wl) uB.factorial) h2b
      omega
    · have := Nat.mul_le_mul h2b hfm
      omega
  · omega

/-- **M5's counted calls** with Schreier–Sims: at most `2 c3Count m k p` in Case 3. -/
theorem ss_m5CKCJ_le {wl Nr k : ℕ} {fxs fys : GensData} (hfx : GensData.AllValid Nr fxs)
    (hbx : IsInvariant (GensData.denote Nr fxs) (baseSet wl Nr)) :
    m5CKCJ ssCtx.O wl Nr k (Nr, fxs, ()) (Nr, fys, ()) ≤ 2 * c3Count (Nr - wl) k wl := by
  have hfix := ss_fixPts_le (e := ()) hfx hbx
  unfold m5CKCJ
  split_ifs
  · exact Nat.mul_le_mul_left 2 (c3Count_mono_mx hfix)
  · exact Nat.zero_le _

theorem m5CH_le (O : Oracle (groupSig Ty.unit)) (n N sIn wl : ℕ) (Fx Fy : GroupData Unit) :
    m5CH O n N sIn wl Fx Fy ≤ (sIn + 1) * wl := by
  unfold m5CH
  split_ifs
  · exact le_rfl
  · exact Nat.zero_le _

/-- **M5** in the full procedure: a giant base, `5 ≤ k`, `2k ≤ m`, `12 ≤ m`, the state without
structure, and any `Lg`, `uB` meeting the corollary's conditions `huB`, `hLg`, `hLgJ` and `hLY`
with `sIn = NB²`. The sub-calls are the children `ch` (factor `F`), `a` calls on `p / k` points
and `b` on `p / 2` points without a hint. -/
theorem main_m5_at (h2 : 2 * nB ≤ NB) {L : LabelData}
    (hI : HInstValid ssDV (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit))
    (hd : MiniDom n₀ nB NB (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit))
    (hsub : MainSubB thr b n₀ nB NB
      (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit) C)
    (hbL : LabInvIf b (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit))
    (hC : ∀ a b, a ≤ b → C a none ≤ C b none)
    (halt : alternatingGroup (Fin (N - n)) ≤ (baseHom (GensData.denote N gs) n hI.base_inv).range)
    {k : ℕ} (h5 : 5 ≤ k) (h2k : 2 * k ≤ N - n) (h12 : 12 ≤ N - n) {Lg uB : ℕ}
    (huB : N - n ≤ uB) (hLg : (N - n).factorial * (NB * NB + 1) ≤ Lg)
    (hLgJ : max (N - n) uB.factorial * (NB * NB + 1) ≤ Lg)
    (hLY : (c2bRU (N - n) + Case3.c3R k (N - n) (Case2b.sojZ (N - n))) * (NB * NB + 1) ≤ Lg) :
    ∃ (ans : AnswerData Ty.unit) (ch : List (ℕ × Option ℕ)) (F a b : ℕ),
      RunsWithin ssCtx (mainBody thr Ty.denote)
        (Main.m5StepCJProg (fun J => Prog.recur J)
          (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit) L k noStD) ans
        ((ch.map fun x => C x.1 x.2).sum + a * C (w.1.length / k) none +
          b * C (w.1.length / 2) none +
          (rbOverSS N w.1.length (N - n) gs.length (NB * NB) +
            m5WorkSS w.1.length (N - n) k w.1.length (NB * NB) (NB * NB) Lg uB)) ∧
      InstData.OK (D := Ty.unit) (xy, w, σd, N, gs, ()) ssDV ans ∧
      (∀ c : CosetData Ty.unit, ans = some c → c.2.gens.length ≤ NB * NB) ∧
      ChildList w.1.length F (StepChild w.1.length (N - n)) ch ∧ F ≤ m5FBu (N - n) k uB ∧
      a ≤ 2 * certCount (w.1.length + (N - n)) w.1.length k +
        2 * c3Count (N - n) k w.1.length ∧
      b ≤ (NB * NB + 1) * w.1.length := by
  have hN : N ≤ NB := hd.degree_le
  have hn : n ≤ nB := hd.n_le
  have hgl : gs.length ≤ NB * NB := hd.gens_le
  have hNN : N * N ≤ NB * NB := Nat.mul_le_mul hN hN
  have hwn := sh_length_le hI
  have hW : 1 ≤ w.1.length := hI.win_pos rfl
  have hm : 1 ≤ N - n := hI.base_pos rfl
  have hsC : max (NB * NB) (supTo (fun M => M * M) (w.1.length / 2)) ≤ NB * NB :=
    max_le le_rfl (supTo_le fun M hM => by
      have : M ≤ NB := by omega
      exact Nat.mul_le_mul this this)
  obtain ⟨fxs, fys, ex, ey, ans, ch, ⟨hCS, φ, -, hFx, hFy⟩, hrun, hok, hg, hch⟩ :=
    RunsWithin.m5StepCJProg_ss hI halt
      (hsub.step fun J hJ ⟨hS, hc⟩ => main_predB h2 hd hbL hJ hS hsC (StepChild.measLt hc hW hm))
      h5 (by omega) h2k h12 hNN hgl hC le_rfl
      (Lg := Lg) hLg (uB := uB) huB hLgJ hLY noStD_fst
  cases ex
  cases ey
  have hR := length_rbPts n N w
  have hRN : (rbPts n N w).length ≤ N := by
    have := hI.win_lt
    have hwl := sh_length_le hI
    have hle : n ≤ N := hI.le
    rw [hR]
    omega
  have hRm : (rbPts n N w).length - w.1.length = N - n := by omega
  have hfx := hFx.1.1
  have hfy := hFy.1.1
  have hbx := hFx.base_inv
  have hby := hFy.base_inv
  have hF := ss_m5CFCJ_le_u (k := k) (uB := uB) (fxs := fxs) hfy hby (by rw [hRm]; exact huB)
  have hK := ss_m5CKCJ_le (k := k) (fys := fys) hfx hbx
  rw [hRm] at hF hK
  have hH := m5CH_le ssCtx.O w.1.length (rbPts n N w).length (NB * NB) w.1.length
    ((rbPts n N w).length, fxs, ()) ((rbPts n N w).length, fys, ())
  refine ⟨ans, ch, _, 2 * certCount (rbPts n N w).length w.1.length k +
      m5CKCJ ssCtx.O w.1.length (rbPts n N w).length k ((rbPts n N w).length, fxs, ())
        ((rbPts n N w).length, fys, ()),
    m5CH ssCtx.O w.1.length (rbPts n N w).length (NB * NB) w.1.length
      ((rbPts n N w).length, fxs, ()) ((rbPts n N w).length, fys, ()), ?_, hok,
    hg (NB * NB) (fun hs hv _ => (ssOracle_gens_le hv).1.trans hNN), hch, hF,
    Nat.add_le_add (le_of_eq (by rw [hR])) hK, hH⟩
  refine hrun.mono ?_
  rw [rbCost_eq]
  have hBgm := rbCost_mono_Bgm (N := N) (k := w.1.length) (m := N - n) (s := gs.length) (C' := 0)
    (s' := NB * NB) (sK := N * N) (Blift := Sims.liftCost N (NB * NB) N + 7)
    (Bker := kerCost N (NB * NB) N + 5) (Bgn := genCost N (N * N + NB * NB) + 2)
    (Nat.add_le_add_right (genCost_mono₂ hRN (le_refl (NB * NB))) 2)
  unfold rbOverSS
  generalize C (w.1.length / k) none = X at *
  generalize C (w.1.length / 2) none = Y at *
  generalize (ch.map fun x => C x.1 x.2).sum = sc
  generalize certCount (rbPts n N w).length w.1.length k = cc
  generalize m5CKCJ ssCtx.O w.1.length (rbPts n N w).length k ((rbPts n N w).length, fxs, ())
    ((rbPts n N w).length, fys, ()) = ck
  generalize m5CH ssCtx.O w.1.length (rbPts n N w).length (NB * NB) w.1.length
    ((rbPts n N w).length, fxs, ()) ((rbPts n N w).length, fys, ()) = chh
  have e : (2 * cc + ck) * X = 2 * cc * X + ck * X := Nat.add_mul _ _ _
  omega

/-- **M5** at the instance's sizes: `Lg = ssLgM5 m k NB²` and `uB = m`. -/
theorem main_m5 (h2 : 2 * nB ≤ NB) {L : LabelData}
    (hI : HInstValid ssDV (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit))
    (hd : MiniDom n₀ nB NB (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit))
    (hsub : MainSubB thr b n₀ nB NB
      (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit) C)
    (hbL : LabInvIf b (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit))
    (hC : ∀ a b, a ≤ b → C a none ≤ C b none)
    (halt : alternatingGroup (Fin (N - n)) ≤ (baseHom (GensData.denote N gs) n hI.base_inv).range)
    {k : ℕ} (h5 : 5 ≤ k) (h2k : 2 * k ≤ N - n) (h12 : 12 ≤ N - n) :
    ∃ (ans : AnswerData Ty.unit) (ch : List (ℕ × Option ℕ)) (F a b : ℕ),
      RunsWithin ssCtx (mainBody thr Ty.denote)
        (Main.m5StepCJProg (fun J => Prog.recur J)
          (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit) L k noStD) ans
        ((ch.map fun x => C x.1 x.2).sum + a * C (w.1.length / k) none +
          b * C (w.1.length / 2) none +
          (rbOverSS N w.1.length (N - n) gs.length (NB * NB) +
            m5WorkSS w.1.length (N - n) k w.1.length (NB * NB) (NB * NB)
              (ssLgM5 (N - n) k (NB * NB)) (N - n))) ∧
      InstData.OK (D := Ty.unit) (xy, w, σd, N, gs, ()) ssDV ans ∧
      (∀ c : CosetData Ty.unit, ans = some c → c.2.gens.length ≤ NB * NB) ∧
      ChildList w.1.length F (StepChild w.1.length (N - n)) ch ∧ F ≤ m5FB (N - n) k ∧
      a ≤ 2 * certCount (w.1.length + (N - n)) w.1.length k +
        2 * c3Count (N - n) k w.1.length ∧
      b ≤ (NB * NB + 1) * w.1.length := by
  have hf := Nat.self_le_factorial (N - n)
  obtain ⟨ans, ch, F, a, b, hrun, hok, hg, hch, hF, ha, hb⟩ :=
    main_m5_at h2 hI hd hsub hbL hC halt h5 h2k h12 (Lg := ssLgM5 (N - n) k (NB * NB)) le_rfl
      (by unfold ssLgM5; exact Nat.mul_le_mul_right _ (by omega))
      (by unfold ssLgM5; exact Nat.mul_le_mul_right _ (by omega))
      (by unfold ssLgM5; exact Nat.mul_le_mul_right _ (by omega))
  rw [m5FBu_self] at hF
  exact ⟨ans, ch, F, a, b, hrun, hok, hg, hch, hF, ha, hb⟩

/-- **M5** at the domain's bounds: `Lg = domLgM5 NB NB²` and `uB = NB` (§14.9 item 4). -/
theorem main_m5_dom (h2 : 2 * nB ≤ NB) {L : LabelData}
    (hI : HInstValid ssDV (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit))
    (hd : MiniDom n₀ nB NB (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit))
    (hsub : MainSubB thr b n₀ nB NB
      (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit) C)
    (hbL : LabInvIf b (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit))
    (hC : ∀ a b, a ≤ b → C a none ≤ C b none)
    (halt : alternatingGroup (Fin (N - n)) ≤ (baseHom (GensData.denote N gs) n hI.base_inv).range)
    {k : ℕ} (h5 : 5 ≤ k) (h2k : 2 * k ≤ N - n) (h12 : 12 ≤ N - n) :
    ∃ (ans : AnswerData Ty.unit) (ch : List (ℕ × Option ℕ)) (F a b : ℕ),
      RunsWithin ssCtx (mainBody thr Ty.denote)
        (Main.m5StepCJProg (fun J => Prog.recur J)
          (((xy, w, σd, N, gs, ()), n₀', n, some L) : HInstData Ty.unit) L k noStD) ans
        ((ch.map fun x => C x.1 x.2).sum + a * C (w.1.length / k) none +
          b * C (w.1.length / 2) none +
          (rbOverSS N w.1.length (N - n) gs.length (NB * NB) +
            m5WorkSS w.1.length (N - n) k w.1.length (NB * NB) (NB * NB)
              (domLgM5 NB (NB * NB)) NB)) ∧
      InstData.OK (D := Ty.unit) (xy, w, σd, N, gs, ()) ssDV ans ∧
      (∀ c : CosetData Ty.unit, ans = some c → c.2.gens.length ≤ NB * NB) ∧
      ChildList w.1.length F (StepChild w.1.length (N - n)) ch ∧ F ≤ m5FBu (N - n) k NB ∧
      a ≤ 2 * certCount (w.1.length + (N - n)) w.1.length k +
        2 * c3Count (N - n) k w.1.length ∧
      b ≤ (NB * NB + 1) * w.1.length := by
  have hN : N ≤ NB := hd.degree_le
  obtain ⟨hLg, huB, hLgJ, hLY⟩ := m5_dom_params (k := k) (NB * NB) (show N - n ≤ NB by omega)
    (show k ≤ NB by omega)
  exact main_m5_at h2 hI hd hsub hbL hC halt h5 h2k h12 huB hLg hLgJ hLY

end Steps

end GraphIso.Main
