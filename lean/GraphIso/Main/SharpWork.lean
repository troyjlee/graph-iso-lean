module

public import GraphIso.Main.FullSharp

/-!
# Corner bounds of the sharp work

Stage 14j-6b-2 (`PLAN-14.md` §14.12 item 7). The work of M4 and M5 without stuck orbits,
`m4WorkNsLSS` and `m5WorkNsSS`, is a monotone envelope (`envSup`): the maximum of a work
function over a box of sizes. At a large base size the box is too large to evaluate. This file
bounds both envelopes by values at the box's corner, which kernel `decide` evaluates
(`GraphIsoChecks.Sharp`).

* **Monotonicity of the costs** (`CostMono.*`): every cost function that the two works call is
  monotone in its natural-number arguments, under side conditions for differences, powers,
  binomials and function arguments (see that section).
* **M4** (`m4WorkNsLSS_le`, for `m ≥ 1`). M4's work at given sizes, `m4PtNsL`, is monotone in
  every size except the individualization depth `j`, which enters through `m - j`
  (`m4PtNsL_mono`). So the envelope is at most the maximum over `j' ≤ j` of `m4PtNsL` at the
  corner of the other sizes.
* **M5** (`m5WorkNsSS_le`, for `1 ≤ k`, `2k ≤ m` and `jB < m`). `m5WorkRawNs` is the
  certificates' work, twice the case decision's work at the worst orbit size `a ≤ m`, and an
  inner envelope of the dispatch's work over its data (`m5WorkRawNs_eq`):
  - the certificates' work `m5CertPt` is monotone when `2k ≤ m`: its binomial `C(m, k)` grows
    in `k` below `m/2` (`m5CertPt_mono`);
  - the case decision's work `m5CasePt` is monotone in the sizes and in `a` (`m5CasePt_mono`);
  - the dispatch's work `m5DispPt` is monotone in every size and datum except Case 2b's depth
    `j`, which enters through `nx - j` and `ny - j` (`m5DispPt_mono`, for positive `k`, `m`,
    `mx`, `my` and `j < nx, ny`).

  So the envelope is at most `m5WorkUB`: the certificates' and the case decision's work at the
  corner, and the maximum over `j ≤ jB` of the dispatch's work at the corner of the other data.
* **The sharp case work** (`caseWorkS_m4_le`, `caseWorkS_m5_le`): `caseWorkS` at M4 and M5 is
  at most these bounds, under the same conditions on `m = N - n`.
* **A lower bound on `m!`** (`pow_half_le_factorial`): `(m/2)^(m - m/2) ≤ m!`, to compare with
  `m!` at a large `m` without evaluating it.
-/

@[expose] public section

namespace GraphIso.Main

open Equiv Cost GraphIso GraphIso.Programs GraphIso.Toolkit GraphIso.Recursion GraphIso.Certificates
  Sims

/-! ### Tools -/

/-- `psCostFrom` is monotone in its sizes and its length. -/
theorem psCostFrom_mono {N N' m m' Bt Bt' Bs Bs' len len' : ℕ} (k : ℕ) (hN : N ≤ N')
    (hm : m ≤ m') (ht : Bt ≤ Bt') (hs : Bs ≤ Bs') (hl : len ≤ len') :
    psCostFrom N m Bt Bs k len ≤ psCostFrom N' m' Bt' Bs' k len' := by
  induction len generalizing k len' with
  | zero => simp [psCostFrom]
  | succ len ih =>
    obtain ⟨len', rfl⟩ : ∃ l, len' = l + 1 := ⟨len' - 1, by omega⟩
    rw [psCostFrom_succ, psCostFrom_succ]
    gcongr
    · unfold psStepCost
      gcongr
    · exact ih _ (by omega)

attribute [gcongr only] psCostFrom_mono

/-- An upper bound on an envelope from a bound at every point of its box. -/
theorem envSup_le {B : ℕ} : ∀ {as : List ℕ} {f : List ℕ → ℕ},
    (∀ xs, List.Forall₂ (· ≤ ·) xs as → f xs ≤ B) → envSup as f ≤ B
  | [], _, h => h [] .nil
  | _ :: _, _, h => supTo_le fun _ hx => envSup_le fun ys hys => h (_ :: ys) (.cons hx hys)

/-- **A lower bound on `m!`**: `(m/2)^(m - m/2) ≤ m!`. -/
theorem pow_half_le_factorial (m : ℕ) : (m / 2) ^ (m - m / 2) ≤ m.factorial :=
  (Nat.le_mul_of_pos_left _ (Nat.factorial_pos _)).trans
    (Nat.factorial_mul_pow_sub_le_factorial (Nat.div_le_self m 2))

/-! ### Monotonicity of the costs

One lemma per cost function that M4's and M5's sharp work calls, callees first, named
`CostMono.<namespace>_<name>`. Each states the cost's monotonicity and is proved by `unfold` and
`gcongr` with the lemmas before it; each is tagged `@[gcongr only]`. The hypotheses are `x ≤ x'`
for the arguments the cost grows in, and these side conditions where `gcongr` needs them:
* `a - b ≤ a' - b'` for a difference of two arguments, in which the cost may decrease in `b`
  (at the callers, `a = n + m` and `b = n`, or `b` is a depth that does not vary);
* `1 ≤ x'` for a power `x ^ y` whose exponent varies;
* `C(a, b) ≤ C(a', b')` for a binomial whose lower argument varies;
* for an argument `f : ℕ → ℕ`, which does not vary, `f x ≤ f x'` at the points where it is
  called;
* for the bounds structure `β` of `m5DispNumNs`, `β.F ≤ β'.F` for each field `F` it uses.
-/

@[gcongr only] theorem CostMono.Align_isoInPCost {m m' k k' : ℕ} (h0 : m ≤ m') (h1 : k ≤ k') :
    GraphIso.Align.isoInPCost m k ≤
      GraphIso.Align.isoInPCost m' k' := by
  unfold GraphIso.Align.isoInPCost
  gcongr

@[gcongr only] theorem CostMono.Toolkit_baseWinCost {n n' N N' : ℕ} (h1 : N ≤ N')
    (s0 : N - n ≤ N' - n') :
    GraphIso.Toolkit.baseWinCost n N ≤
      GraphIso.Toolkit.baseWinCost n' N' := by
  unfold GraphIso.Toolkit.baseWinCost
  gcongr

@[gcongr only] theorem CostMono.Align_alignCallCost
    {n n' N N' k k' cI cI' Bmem Bmem' Bl Bl' Cb Cb' : ℕ} (h1 : N ≤ N') (h2 : k ≤ k') (h3 : cI ≤ cI')
    (h4 : Bmem ≤ Bmem') (h5 : Bl ≤ Bl') (h6 : Cb ≤ Cb') (s0 : N - n ≤ N' - n') :
    GraphIso.Align.alignCallCost n N k cI Bmem Bl Cb ≤
      GraphIso.Align.alignCallCost n' N' k' cI' Bmem' Bl' Cb' := by
  unfold GraphIso.Align.alignCallCost
  gcongr

@[gcongr only] theorem CostMono.Align_baseDCost {m m' : ℕ} (h0 : m ≤ m') :
    GraphIso.Align.baseDCost m ≤
      GraphIso.Align.baseDCost m' := by
  unfold GraphIso.Align.baseDCost
  gcongr

@[gcongr only] theorem CostMono.Align_preCost {n n' N N' k k' Bk Bk' Bl Bl' Bg Bg' : ℕ}
    (h1 : N ≤ N') (h2 : k ≤ k') (h3 : Bk ≤ Bk') (h4 : Bl ≤ Bl') (h5 : Bg ≤ Bg')
    (x0 : N - n ≤ N' - n') :
    GraphIso.Align.preCost n N k Bk Bl Bg ≤
      GraphIso.Align.preCost n' N' k' Bk' Bl' Bg' := by
  unfold GraphIso.Align.preCost
  gcongr

@[gcongr only] theorem CostMono.Align_stabInPCost {m m' k k' : ℕ} (h0 : m ≤ m') (h1 : k ≤ k') :
    GraphIso.Align.stabInPCost m k ≤
      GraphIso.Align.stabInPCost m' k' := by
  unfold GraphIso.Align.stabInPCost
  gcongr

@[gcongr only] theorem CostMono.Align_alignCost
    {n n' N N' g g' k k' r r' cG cG' cI cI' BgP BgP' Bmem Bmem' Bk Bk' Bl Bl' Bg1 Bg1' Bgen : ℕ}
    {Bgen' Cb Cb' s s' : ℕ} (h1 : N ≤ N') (h2 : g ≤ g') (h3 : k ≤ k') (h4 : r ≤ r') (h5 : cG ≤ cG')
    (h6 : cI ≤ cI') (h7 : BgP ≤ BgP') (h8 : Bmem ≤ Bmem') (h9 : Bk ≤ Bk') (h10 : Bl ≤ Bl')
    (h11 : Bg1 ≤ Bg1') (h12 : Bgen ≤ Bgen') (h13 : Cb ≤ Cb') (h14 : s ≤ s') (s0 : N - n ≤ N' - n') :
    GraphIso.Align.alignCost n N g k r cG cI BgP Bmem Bk Bl Bg1 Bgen Cb s ≤
      GraphIso.Align.alignCost n' N' g' k' r' cG' cI' BgP' Bmem' Bk' Bl' Bg1' Bgen' Cb' s' := by
  unfold GraphIso.Align.alignCost
  gcongr

@[gcongr only] theorem CostMono.Align_blkLCost {m m' L L' : ℕ} (h0 : m ≤ m') (h1 : L ≤ L') :
    GraphIso.Align.blkLCost m L ≤
      GraphIso.Align.blkLCost m' L' := by
  unfold GraphIso.Align.blkLCost
  gcongr

@[gcongr only] theorem CostMono.Align_preVCost {B B' cπ cπ' : ℕ} (h0 : B ≤ B') (h1 : cπ ≤ cπ') :
    GraphIso.Align.preVCost B cπ ≤
      GraphIso.Align.preVCost B' cπ' := by
  unfold GraphIso.Align.preVCost
  gcongr

@[gcongr only] theorem CostMono.Align_jmapCost {B B' cπ cπ' cρ cρ' : ℕ} (h0 : B ≤ B')
    (h1 : cπ ≤ cπ') (h2 : cρ ≤ cρ') :
    GraphIso.Align.jmapCost B cπ cρ ≤
      GraphIso.Align.jmapCost B' cπ' cρ' := by
  unfold GraphIso.Align.jmapCost
  gcongr

@[gcongr only] theorem CostMono.Align_ordCost {k k' B B' : ℕ} (h0 : k ≤ k') (h1 : B ≤ B') :
    GraphIso.Align.ordCost k B ≤
      GraphIso.Align.ordCost k' B' := by
  unfold GraphIso.Align.ordCost
  gcongr

@[gcongr only] theorem CostMono.Align_branchCost {B B' : ℕ} (h0 : B ≤ B') :
    GraphIso.Align.branchCost B ≤
      GraphIso.Align.branchCost B' := by
  unfold GraphIso.Align.branchCost
  gcongr

@[gcongr only] theorem CostMono.Align_cellSwapCost {B B' : ℕ} (h0 : B ≤ B') :
    GraphIso.Align.cellSwapCost B ≤
      GraphIso.Align.cellSwapCost B' := by
  unfold GraphIso.Align.cellSwapCost
  gcongr

@[gcongr only] theorem CostMono.Align_exchDCost {m m' K K' : ℕ} (h0 : m ≤ m') (h1 : K ≤ K') :
    GraphIso.Align.exchDCost m K ≤
      GraphIso.Align.exchDCost m' K' := by
  unfold GraphIso.Align.exchDCost
  gcongr

@[gcongr only] theorem CostMono.Align_exchRowCost {m m' L L' R R' : ℕ} (h0 : m ≤ m') (h1 : L ≤ L')
    (h2 : R ≤ R') :
    GraphIso.Align.exchRowCost m L R ≤
      GraphIso.Align.exchRowCost m' L' R' := by
  unfold GraphIso.Align.exchRowCost
  gcongr

@[gcongr only] theorem CostMono.Align_exchGensCost {m m' L L' R R' : ℕ} (h0 : m ≤ m') (h1 : L ≤ L')
    (h2 : R ≤ R') :
    GraphIso.Align.exchGensCost m L R ≤
      GraphIso.Align.exchGensCost m' L' R' := by
  unfold GraphIso.Align.exchGensCost
  gcongr

@[gcongr only] theorem CostMono.Align_rowACost {B B' : ℕ} (h0 : B ≤ B') :
    GraphIso.Align.rowACost B ≤
      GraphIso.Align.rowACost B' := by
  unfold GraphIso.Align.rowACost
  gcongr

@[gcongr only] theorem CostMono.Align_rowCCost {B B' : ℕ} (h0 : B ≤ B') :
    GraphIso.Align.rowCCost B ≤
      GraphIso.Align.rowCCost B' := by
  unfold GraphIso.Align.rowCCost
  gcongr

@[gcongr only] theorem CostMono.Align_johnGensCost {B B' : ℕ} (h0 : B ≤ B') :
    GraphIso.Align.johnGensCost B ≤
      GraphIso.Align.johnGensCost B' := by
  unfold GraphIso.Align.johnGensCost
  gcongr

@[gcongr only] theorem CostMono.Align_sizesCost {k k' B B' : ℕ} (h0 : k ≤ k') (h1 : B ≤ B') :
    GraphIso.Align.sizesCost k B ≤
      GraphIso.Align.sizesCost k' B' := by
  unfold GraphIso.Align.sizesCost
  gcongr

@[gcongr only] theorem CostMono.Align_profCost {B B' : ℕ} (h0 : B ≤ B') :
    GraphIso.Align.profCost B ≤
      GraphIso.Align.profCost B' := by
  unfold GraphIso.Align.profCost
  gcongr

@[gcongr only] theorem CostMono.Align_johnIsoCost {B B' : ℕ} (h0 : B ≤ B') :
    GraphIso.Align.johnIsoCost B ≤
      GraphIso.Align.johnIsoCost B' := by
  unfold GraphIso.Align.johnIsoCost
  gcongr

@[gcongr only] theorem CostMono.Align_keyCost {m m' L L' : ℕ} (h0 : m ≤ m') (h1 : L ≤ L') :
    GraphIso.Align.keyCost m L ≤
      GraphIso.Align.keyCost m' L' := by
  unfold GraphIso.Align.keyCost
  gcongr

@[gcongr only] theorem CostMono.Align_matchStepCost {m m' Lx Lx' Ly Ly' R R' : ℕ} (h0 : m ≤ m')
    (h1 : Lx ≤ Lx') (h2 : Ly ≤ Ly') (h3 : R ≤ R') :
    GraphIso.Align.matchStepCost m Lx Ly R ≤
      GraphIso.Align.matchStepCost m' Lx' Ly' R' := by
  unfold GraphIso.Align.matchStepCost
  gcongr

@[gcongr only] theorem CostMono.Align_repsCost {m m' L L' : ℕ} (h0 : m ≤ m') (h1 : L ≤ L') :
    GraphIso.Align.repsCost m L ≤
      GraphIso.Align.repsCost m' L' := by
  unfold GraphIso.Align.repsCost
  gcongr

@[gcongr only] theorem CostMono.Align_matchCost {m m' Lx Lx' Ly Ly' : ℕ} (h0 : m ≤ m')
    (h1 : Lx ≤ Lx') (h2 : Ly ≤ Ly') :
    GraphIso.Align.matchCost m Lx Ly ≤
      GraphIso.Align.matchCost m' Lx' Ly' := by
  unfold GraphIso.Align.matchCost
  gcongr

@[gcongr only] theorem CostMono.Align_rowCost {m m' L L' : ℕ} (h0 : m ≤ m') (h1 : L ≤ L') :
    GraphIso.Align.rowCost m L ≤
      GraphIso.Align.rowCost m' L' := by
  unfold GraphIso.Align.rowCost
  gcongr

@[gcongr only] theorem CostMono.Align_withinCost {m m' L L' : ℕ} (h0 : m ≤ m') (h1 : L ≤ L') :
    GraphIso.Align.withinCost m L ≤
      GraphIso.Align.withinCost m' L' := by
  unfold GraphIso.Align.withinCost
  gcongr

@[gcongr only] theorem CostMono.Align_partGensCost {m m' L L' : ℕ} (h0 : m ≤ m') (h1 : L ≤ L') :
    GraphIso.Align.partGensCost m L ≤
      GraphIso.Align.partGensCost m' L' := by
  unfold GraphIso.Align.partGensCost
  gcongr

@[gcongr only] theorem CostMono.Align_permCost {m m' Lx Lx' Ly Ly' P P' : ℕ} (h0 : m ≤ m')
    (h1 : Lx ≤ Lx') (h2 : Ly ≤ Ly') (h3 : P ≤ P') :
    GraphIso.Align.permCost m Lx Ly P ≤
      GraphIso.Align.permCost m' Lx' Ly' P' := by
  unfold GraphIso.Align.permCost
  gcongr

@[gcongr only] theorem CostMono.Align_partIsoCost {m m' Lx Lx' Ly Ly' : ℕ} (h0 : m ≤ m')
    (h1 : Lx ≤ Lx') (h2 : Ly ≤ Ly') :
    GraphIso.Align.partIsoCost m Lx Ly ≤
      GraphIso.Align.partIsoCost m' Lx' Ly' := by
  unfold GraphIso.Align.partIsoCost
  gcongr

@[gcongr only] theorem CostMono.Align_setPartCost {m m' k k' : ℕ} (h0 : m ≤ m') (h1 : k ≤ k') :
    GraphIso.Align.setPartCost m k ≤
      GraphIso.Align.setPartCost m' k' := by
  unfold GraphIso.Align.setPartCost
  gcongr

@[gcongr only] theorem CostMono.Align_setGensCost {m m' k k' : ℕ} (h0 : m ≤ m') (h1 : k ≤ k') :
    GraphIso.Align.setGensCost m k ≤
      GraphIso.Align.setGensCost m' k' := by
  unfold GraphIso.Align.setGensCost
  gcongr

@[gcongr only] theorem CostMono.Align_setIsoCost {m m' k k'' k' k''' : ℕ} (h0 : m ≤ m')
    (h1 : k ≤ k'') (h2 : k' ≤ k''') :
    GraphIso.Align.setIsoCost m k k' ≤
      GraphIso.Align.setIsoCost m' k'' k''' := by
  unfold GraphIso.Align.setIsoCost
  gcongr

@[gcongr only] theorem CostMono.Case2b_pairsCost {m m' : ℕ} (h0 : m ≤ m') :
    GraphIso.Case2b.pairsCost m ≤
      GraphIso.Case2b.pairsCost m' := by
  unfold GraphIso.Case2b.pairsCost
  gcongr

@[gcongr only] theorem CostMono.Case2b_tupleCost {m m' nΦ nΦ' j j' Cc Cc' Lc Lc' : ℕ} (h0 : m ≤ m')
    (h1 : nΦ ≤ nΦ') (h2 : j ≤ j') (h3 : Cc ≤ Cc') (h4 : Lc ≤ Lc') :
    GraphIso.Case2b.tupleCost m nΦ j Cc Lc ≤
      GraphIso.Case2b.tupleCost m' nΦ' j' Cc' Lc' := by
  unfold GraphIso.Case2b.tupleCost
  gcongr

@[gcongr only] theorem CostMono.Case2b_tupStepCost {L L' A A' j j' : ℕ} (h0 : L ≤ L') (h1 : A ≤ A')
    (h2 : j ≤ j') :
    GraphIso.Case2b.tupStepCost L A j ≤
      GraphIso.Case2b.tupStepCost L' A' j' := by
  unfold GraphIso.Case2b.tupStepCost
  gcongr

@[gcongr only] theorem CostMono.Case2b_tuplesCost {L L' j j' : ℕ} (h0 : L ≤ L') (h1 : j ≤ j') :
    GraphIso.Case2b.tuplesCost L j ≤
      GraphIso.Case2b.tuplesCost L' j' := by
  unfold GraphIso.Case2b.tuplesCost
  gcongr
  all_goals omega

@[gcongr only] theorem CostMono.Case2b_allCost {m m' nΦ nΦ' j j' Cc Cc' Lc Lc' : ℕ} (h0 : m ≤ m')
    (h1 : nΦ ≤ nΦ') (h2 : j ≤ j') (h3 : Cc ≤ Cc') (h4 : Lc ≤ Lc') (x0 : 1 ≤ nΦ') :
    GraphIso.Case2b.allCost m nΦ j Cc Lc ≤
      GraphIso.Case2b.allCost m' nΦ' j' Cc' Lc' := by
  unfold GraphIso.Case2b.allCost
  gcongr

@[gcongr only] theorem CostMono.Case2b_c2bR {N N' n n' nΦ nΦ' j j' Z Z' : ℕ} (h2 : nΦ ≤ nΦ')
    (h3 : j ≤ j') (h4 : Z ≤ Z') (s0 : N - n ≤ N' - n') (x0 : 1 ≤ nΦ') :
    GraphIso.Case2b.c2bR N n nΦ j Z ≤
      GraphIso.Case2b.c2bR N' n' nΦ' j' Z' := by
  unfold GraphIso.Case2b.c2bR
  gcongr

@[gcongr only] theorem CostMono.Coherent_infoAtCost {k k' m m' K K' : ℕ} (h0 : k ≤ k') (h1 : m ≤ m')
    (h2 : K ≤ K') :
    GraphIso.Coherent.infoAtCost k m K ≤
      GraphIso.Coherent.infoAtCost k' m' K' := by
  unfold GraphIso.Coherent.infoAtCost
  gcongr

@[gcongr only] theorem CostMono.Coherent_pwTabCost {k k' m m' : ℕ} (h0 : k ≤ k') (h1 : m ≤ m') :
    GraphIso.Coherent.pwTabCost k m ≤
      GraphIso.Coherent.pwTabCost k' m' := by
  unfold GraphIso.Coherent.pwTabCost
  gcongr

@[gcongr only] theorem CostMono.Coherent_extCost {m m' L L' : ℕ} (h0 : m ≤ m') (h1 : L ≤ L') :
    GraphIso.Coherent.extCost m L ≤
      GraphIso.Coherent.extCost m' L' := by
  unfold GraphIso.Coherent.extCost
  gcongr

@[gcongr only] theorem CostMono.Coherent_tupsCost {k k' m m' : ℕ} (h0 : k ≤ k') (h1 : m ≤ m')
    (x0 : 1 ≤ m') :
    GraphIso.Coherent.tupsCost k m ≤
      GraphIso.Coherent.tupsCost k' m' := by
  unfold GraphIso.Coherent.tupsCost
  gcongr

@[gcongr only] theorem CostMono.Coherent_infoCost {k k' m m' : ℕ} (h0 : k ≤ k') (h1 : m ≤ m')
    (x0 : 1 ≤ m') (x1 : 1 ≤ k') :
    GraphIso.Coherent.infoCost k m ≤
      GraphIso.Coherent.infoCost k' m' := by
  unfold GraphIso.Coherent.infoCost
  gcongr

@[gcongr only] theorem CostMono.Coherent_ceSig0 {k k' : ℕ} (h0 : k ≤ k') :
    GraphIso.Coherent.ceSig0 k ≤
      GraphIso.Coherent.ceSig0 k' := by
  unfold GraphIso.Coherent.ceSig0
  gcongr

@[gcongr only] theorem CostMono.Coherent_rankCost {N N' ce ce' : ℕ} (h0 : N ≤ N') (h1 : ce ≤ ce') :
    GraphIso.Coherent.rankCost N ce ≤
      GraphIso.Coherent.rankCost N' ce' := by
  unfold GraphIso.Coherent.rankCost
  gcongr

@[gcongr only] theorem CostMono.Coherent_initCost {N N' k k' : ℕ} (h0 : N ≤ N') (h1 : k ≤ k') :
    GraphIso.Coherent.initCost N k ≤
      GraphIso.Coherent.initCost N' k' := by
  unfold GraphIso.Coherent.initCost
  gcongr

@[gcongr only] theorem CostMono.Coherent_ceSig {k k' m m' K K' : ℕ} (h0 : k ≤ k') (h1 : m ≤ m')
    (h2 : K ≤ K') :
    GraphIso.Coherent.ceSig k m K ≤
      GraphIso.Coherent.ceSig k' m' K' := by
  unfold GraphIso.Coherent.ceSig
  gcongr

@[gcongr only] theorem CostMono.Coherent_sigCost {k k' m m' K K' : ℕ} (h0 : k ≤ k') (h1 : m ≤ m')
    (h2 : K ≤ K') :
    GraphIso.Coherent.sigCost k m K ≤
      GraphIso.Coherent.sigCost k' m' K' := by
  unfold GraphIso.Coherent.sigCost
  gcongr

@[gcongr only] theorem CostMono.Coherent_roundCost {N N' k k' m m' K K' : ℕ} (h0 : N ≤ N')
    (h1 : k ≤ k') (h2 : m ≤ m') (h3 : K ≤ K') :
    GraphIso.Coherent.roundCost N k m K ≤
      GraphIso.Coherent.roundCost N' k' m' K' := by
  unfold GraphIso.Coherent.roundCost
  gcongr

@[gcongr only] theorem CostMono.Coherent_wlRunCost {k k' m m' : ℕ} (h0 : k ≤ k') (h1 : m ≤ m')
    (x0 : 1 ≤ m') (x1 : 1 ≤ k') :
    GraphIso.Coherent.wlRunCost k m ≤
      GraphIso.Coherent.wlRunCost k' m' := by
  unfold GraphIso.Coherent.wlRunCost
  gcongr

@[gcongr only] theorem CostMono.Coherent_wlCost {k k' m m' : ℕ} (h0 : k ≤ k') (h1 : m ≤ m')
    (x0 : 1 ≤ m') (x1 : 1 ≤ k') :
    GraphIso.Coherent.wlCost k m ≤
      GraphIso.Coherent.wlCost k' m' := by
  unfold GraphIso.Coherent.wlCost
  gcongr

@[gcongr only] theorem CostMono.Toolkit_matrixCost {m m' c c' : ℕ} (h0 : m ≤ m') (h1 : c ≤ c') :
    GraphIso.Toolkit.matrixCost m c ≤
      GraphIso.Toolkit.matrixCost m' c' := by
  unfold GraphIso.Toolkit.matrixCost
  gcongr

@[gcongr only] theorem CostMono.Toolkit_orbitalCost {N N' m m' Btr Btr' Bstab Bstab' Borb Borb' : ℕ}
    (h0 : N ≤ N') (h1 : m ≤ m') (h2 : Btr ≤ Btr') (h3 : Bstab ≤ Bstab') (h4 : Borb ≤ Borb') :
    GraphIso.Toolkit.orbitalCost N m Btr Bstab Borb ≤
      GraphIso.Toolkit.orbitalCost N' m' Btr' Bstab' Borb' := by
  unfold GraphIso.Toolkit.orbitalCost
  gcongr

@[gcongr only] theorem CostMono.Case2b_colCost {m' m'' a a' Btr Btr' Bstab Bstab' Borb Borb' : ℕ}
    (h0 : m' ≤ m'') (h1 : a ≤ a') (h2 : Btr ≤ Btr') (h3 : Bstab ≤ Bstab') (h4 : Borb ≤ Borb')
    (x0 : 1 ≤ m'') :
    GraphIso.Case2b.colCost m' a Btr Bstab Borb ≤
      GraphIso.Case2b.colCost m'' a' Btr' Bstab' Borb' := by
  unfold GraphIso.Case2b.colCost
  gcongr
  all_goals omega

@[gcongr only] theorem CostMono.Case2b_extCost {m m' P P' L L' : ℕ} (h0 : m ≤ m') (h1 : P ≤ P')
    (h2 : L ≤ L') :
    GraphIso.Case2b.extCost m P L ≤
      GraphIso.Case2b.extCost m' P' L' := by
  unfold GraphIso.Case2b.extCost
  gcongr

@[gcongr only] theorem CostMono.Case2b_trimCost {m m' V V' : ℕ} (h0 : m ≤ m') (h1 : V ≤ V') :
    GraphIso.Case2b.trimCost m V ≤
      GraphIso.Case2b.trimCost m' V' := by
  unfold GraphIso.Case2b.trimCost
  gcongr

@[gcongr only] theorem CostMono.SoJTree_outB {m m' q q' : ℕ} (h0 : m ≤ m') (h1 : q ≤ q') :
    GraphIso.SoJTree.outB m q ≤
      GraphIso.SoJTree.outB m' q' := by
  unfold GraphIso.SoJTree.outB
  gcongr

@[gcongr only] theorem CostMono.SoJTree_addPieceCost {m m' d d' : ℕ} (h0 : m ≤ m') (h1 : d ≤ d') :
    GraphIso.SoJTree.addPieceCost m d ≤
      GraphIso.SoJTree.addPieceCost m' d' := by
  unfold GraphIso.SoJTree.addPieceCost
  gcongr

@[gcongr only] theorem CostMono.SoJTree_exBlkCost {v v' M M' : ℕ} (h0 : v ≤ v') (h1 : M ≤ M') :
    GraphIso.SoJTree.exBlkCost v M ≤
      GraphIso.SoJTree.exBlkCost v' M' := by
  unfold GraphIso.SoJTree.exBlkCost
  gcongr

@[gcongr only] theorem CostMono.SoJTree_extendOutCost {m m' v v' : ℕ} (h0 : m ≤ m') (h1 : v ≤ v') :
    GraphIso.SoJTree.extendOutCost m v ≤
      GraphIso.SoJTree.extendOutCost m' v' := by
  unfold GraphIso.SoJTree.extendOutCost
  gcongr

@[gcongr only] theorem CostMono.SoJTree_opCost {m m' L L' : ℕ} (h0 : m ≤ m') (h1 : L ≤ L') :
    GraphIso.SoJTree.opCost m L ≤
      GraphIso.SoJTree.opCost m' L' := by
  unfold GraphIso.SoJTree.opCost
  gcongr

@[gcongr only] theorem CostMono.SoJTree_stepK {m m' q q' t t' : ℕ} (h0 : m ≤ m') (h1 : q ≤ q')
    (h2 : t ≤ t') :
    GraphIso.SoJTree.stepK m q t ≤
      GraphIso.SoJTree.stepK m' q' t' := by
  unfold GraphIso.SoJTree.stepK
  gcongr

@[gcongr only] theorem CostMono.Case2b_sojBranchCost {m m' sz sz' : ℕ} (h0 : m ≤ m') (h1 : sz ≤ sz')
    :
    GraphIso.Case2b.sojBranchCost m sz ≤
      GraphIso.Case2b.sojBranchCost m' sz' := by
  unfold GraphIso.Case2b.sojBranchCost
  gcongr

@[gcongr only] theorem CostMono.SoJProg_stepCost {N N' L L' : ℕ} (h0 : N ≤ N') (h1 : L ≤ L') :
    GraphIso.SoJProg.stepCost N L ≤
      GraphIso.SoJProg.stepCost N' L' := by
  unfold GraphIso.SoJProg.stepCost
  gcongr

@[gcongr only] theorem CostMono.SoJProg_compCost {N N' : ℕ} (h0 : N ≤ N') :
    GraphIso.SoJProg.compCost N ≤
      GraphIso.SoJProg.compCost N' := by
  unfold GraphIso.SoJProg.compCost
  gcongr

@[gcongr only] theorem CostMono.SoJProg_compPartCost {N N' : ℕ} (h0 : N ≤ N') :
    GraphIso.SoJProg.compPartCost N ≤
      GraphIso.SoJProg.compPartCost N' := by
  unfold GraphIso.SoJProg.compPartCost
  gcongr

@[gcongr only] theorem CostMono.SoJProg_offColsCost {N N' : ℕ} (h0 : N ≤ N') :
    GraphIso.SoJProg.offColsCost N ≤
      GraphIso.SoJProg.offColsCost N' := by
  unfold GraphIso.SoJProg.offColsCost
  gcongr

@[gcongr only] theorem CostMono.SoJProg_disconnCost {N N' : ℕ} (h0 : N ≤ N') :
    GraphIso.SoJProg.disconnCost N ≤
      GraphIso.SoJProg.disconnCost N' := by
  unfold GraphIso.SoJProg.disconnCost
  gcongr

@[gcongr only] theorem CostMono.Case2b_leavesOfCost {m m' sz sz' : ℕ} (h0 : m ≤ m') (h1 : sz ≤ sz')
    :
    GraphIso.Case2b.leavesOfCost m sz ≤
      GraphIso.Case2b.leavesOfCost m' sz' := by
  unfold GraphIso.Case2b.leavesOfCost
  gcongr

@[gcongr only] theorem CostMono.Case2b_resCost {N N' nS nS' m' m'' s s' Bstab Bstab' Bg Bg' : ℕ}
    (h0 : N ≤ N') (h1 : nS ≤ nS') (h2 : m' ≤ m'') (h3 : s ≤ s') (h4 : Bstab ≤ Bstab')
    (h5 : Bg ≤ Bg') :
    GraphIso.Case2b.resCost N nS m' s Bstab Bg ≤
      GraphIso.Case2b.resCost N' nS' m'' s' Bstab' Bg' := by
  unfold GraphIso.Case2b.resCost
  gcongr

@[gcongr only] theorem CostMono.Case2b_choiceCost
    {N N' n n' s s' nΦ nΦ' nS nS' m' m'' a a' Bstab Bstab'' Bg Bg' Btr' Btr'' Bstab' : ℕ}
    {Bstab''' Borb' Borb'' sz sz' : ℕ} (h0 : N ≤ N') (h2 : s ≤ s') (h3 : nΦ ≤ nΦ') (h4 : nS ≤ nS')
    (h5 : m' ≤ m'') (h6 : a ≤ a') (h7 : Bstab ≤ Bstab'') (h8 : Bg ≤ Bg') (h9 : Btr' ≤ Btr'')
    (h10 : Bstab' ≤ Bstab''') (h11 : Borb' ≤ Borb'') (h12 : sz ≤ sz') (s0 : N - n ≤ N' - n')
    (x0 : 1 ≤ m'') :
    GraphIso.Case2b.choiceCost N n s nΦ nS m' a Bstab Bg Btr' Bstab' Borb' sz ≤
      GraphIso.Case2b.choiceCost N' n' s' nΦ' nS' m'' a' Bstab'' Bg' Btr'' Bstab''' Borb'' sz' := by
  unfold GraphIso.Case2b.choiceCost
  gcongr

@[gcongr only] theorem CostMono.Case2b_chCost
    {N N' n n' s s' nΦ nΦ' j j' Bstab Bstab' Bg Bg' Btr Btr' Bst Bst' Borb Borb' Z Z' : ℕ}
    (h0 : N ≤ N') (h2 : s ≤ s') (h3 : nΦ ≤ nΦ') (h4 : j ≤ j') (h5 : Bstab ≤ Bstab') (h6 : Bg ≤ Bg')
    (h7 : Btr ≤ Btr') (h8 : Bst ≤ Bst') (h9 : Borb ≤ Borb') (h10 : Z ≤ Z') (s0 : nΦ - j ≤ nΦ' - j')
    (x0 : N - n ≤ N' - n') (x1 : 1 ≤ nΦ' - j') :
    GraphIso.Case2b.chCost N n s nΦ j Bstab Bg Btr Bst Borb Z ≤
      GraphIso.Case2b.chCost N' n' s' nΦ' j' Bstab' Bg' Btr' Bst' Borb' Z' := by
  unfold GraphIso.Case2b.chCost
  gcongr

@[gcongr only] theorem CostMono.Toolkit_degRound {N N' Borb Borb' Bstab Bstab' : ℕ} (h0 : N ≤ N')
    (h1 : Borb ≤ Borb') (h2 : Bstab ≤ Bstab') :
    GraphIso.Toolkit.degRound N Borb Bstab ≤
      GraphIso.Toolkit.degRound N' Borb' Bstab' := by
  unfold GraphIso.Toolkit.degRound
  gcongr

@[gcongr only] theorem CostMono.Toolkit_degreeCost {N N' cap cap' Borb Borb' Bstab Bstab' : ℕ}
    (h0 : N ≤ N') (h1 : cap ≤ cap') (h2 : Borb ≤ Borb') (h3 : Bstab ≤ Bstab') :
    GraphIso.Toolkit.degreeCost N cap Borb Bstab ≤
      GraphIso.Toolkit.degreeCost N' cap' Borb' Bstab' := by
  unfold GraphIso.Toolkit.degreeCost
  gcongr

@[gcongr only] theorem CostMono.Case2b_degCost
    {N N' n n' nΦ nΦ' m' m'' s s' Bstab Bstab'' Bg Bg' Borb' Borb'' Bstab' Bstab''' : ℕ}
    (h0 : N ≤ N') (h2 : nΦ ≤ nΦ') (h3 : m' ≤ m'') (h4 : s ≤ s') (h5 : Bstab ≤ Bstab'')
    (h6 : Bg ≤ Bg') (h7 : Borb' ≤ Borb'') (h8 : Bstab' ≤ Bstab''') (s0 : N - n ≤ N' - n') :
    GraphIso.Case2b.degCost N n nΦ m' s Bstab Bg Borb' Bstab' ≤
      GraphIso.Case2b.degCost N' n' nΦ' m'' s' Bstab'' Bg' Borb'' Bstab''' := by
  unfold GraphIso.Case2b.degCost
  gcongr

@[gcongr only] theorem CostMono.Case2b_leafB {m m' : ℕ} (h0 : m ≤ m') :
    GraphIso.Case2b.leafB m ≤
      GraphIso.Case2b.leafB m' := by
  unfold GraphIso.Case2b.leafB
  gcongr

@[gcongr only] theorem CostMono.Case2b_outGensCost {m m' L L' B B' : ℕ} (h0 : m ≤ m') (h1 : L ≤ L')
    (h2 : B ≤ B') :
    GraphIso.Case2b.outGensCost m L B ≤
      GraphIso.Case2b.outGensCost m' L' B' := by
  unfold GraphIso.Case2b.outGensCost
  gcongr

@[gcongr only] theorem CostMono.Case2b_outIsoCost {m m' Lx Lx' Ly Ly' B B' : ℕ} (h0 : m ≤ m')
    (h1 : Lx ≤ Lx') (h2 : Ly ≤ Ly') (h3 : B ≤ B') :
    GraphIso.Case2b.outIsoCost m Lx Ly B ≤
      GraphIso.Case2b.outIsoCost m' Lx' Ly' B' := by
  unfold GraphIso.Case2b.outIsoCost
  gcongr

@[gcongr only] theorem CostMono.Case2b_c2bCost
    {n n' N N' s s' g g' nx nx' ny ny' j j' k k' Bstab Bstab' Bg Bg' Z Z' BgP BgP' Bmem : ℕ}
    {Bmem' Bk Bk' Bl Bl' Bg1 Bg1' Bgen Bgen' Cb Cb' : ℕ} {Bo : ℕ → ℕ} {Bs : ℕ → ℕ} {Bt : ℕ → ℕ}
    (h1 : N ≤ N') (h2 : s ≤ s') (h3 : g ≤ g') (h4 : nx ≤ nx') (h5 : ny ≤ ny') (h6 : j ≤ j')
    (h7 : k ≤ k') (h8 : Bstab ≤ Bstab') (h9 : Bg ≤ Bg') (h10 : Z ≤ Z') (h11 : BgP ≤ BgP')
    (h12 : Bmem ≤ Bmem') (h13 : Bk ≤ Bk') (h14 : Bl ≤ Bl') (h15 : Bg1 ≤ Bg1') (h16 : Bgen ≤ Bgen')
    (h17 : Cb ≤ Cb') (s0 : nx - j ≤ nx' - j') (s1 : N - n ≤ N' - n') (s2 : ny - j ≤ ny' - j')
    (x0 : Bo nx ≤ Bo nx') (x1 : Bs nx ≤ Bs nx') (x2 : Bo ny ≤ Bo ny') (x3 : Bs ny ≤ Bs ny')
    (x4 : 1 ≤ nx' - j') (x5 : Bt (nx - j) ≤ Bt (nx' - j')) (x6 : Bs (nx - j) ≤ Bs (nx' - j'))
    (x7 : Bo (nx - j) ≤ Bo (nx' - j')) (x8 : 1 ≤ ny') (x9 : 1 ≤ ny' - j')
    (x10 : Bt (ny - j) ≤ Bt (ny' - j')) (x11 : Bs (ny - j) ≤ Bs (ny' - j'))
    (x12 : Bo (ny - j) ≤ Bo (ny' - j')) :
    GraphIso.Case2b.c2bCost n N s g nx ny j k Bstab Bg Z BgP Bmem Bk Bl Bg1 Bgen Cb Bo Bs Bt ≤
      GraphIso.Case2b.c2bCost n' N' s' g' nx' ny' j' k' Bstab' Bg' Z' BgP' Bmem' Bk' Bl' Bg1' Bgen'
        Cb' Bo Bs Bt := by
  unfold GraphIso.Case2b.c2bCost
  gcongr

@[gcongr only] theorem CostMono.Case2b_outGensB {m m' : ℕ} (h0 : m ≤ m') :
    GraphIso.Case2b.outGensB m ≤
      GraphIso.Case2b.outGensB m' := by
  unfold GraphIso.Case2b.outGensB
  gcongr

@[gcongr only] theorem CostMono.Case2b_sojZ {M M' : ℕ} (h0 : M ≤ M') :
    GraphIso.Case2b.sojZ M ≤
      GraphIso.Case2b.sojZ M' := by
  unfold GraphIso.Case2b.sojZ
  gcongr

@[gcongr only] theorem CostMono.Case3_c3R {k k' m m' Z Z' : ℕ} (h0 : k ≤ k') (h1 : m ≤ m')
    (h2 : Z ≤ Z') (x0 : 1 ≤ m') :
    GraphIso.Case3.c3R k m Z ≤
      GraphIso.Case3.c3R k' m' Z' := by
  unfold GraphIso.Case3.c3R
  gcongr

@[gcongr only] theorem CostMono.Coherent_goodCost {k k' m m' : ℕ} (h0 : k ≤ k') (h1 : m ≤ m') :
    GraphIso.Coherent.goodCost k m ≤
      GraphIso.Coherent.goodCost k' m' := by
  unfold GraphIso.Coherent.goodCost
  gcongr

@[gcongr only] theorem CostMono.Coherent_tupsBound {k k' m m' : ℕ} (h0 : k ≤ k') (h1 : m ≤ m')
    (x0 : 1 ≤ m') :
    GraphIso.Coherent.tupsBound k m ≤
      GraphIso.Coherent.tupsBound k' m' := by
  unfold GraphIso.Coherent.tupsBound
  gcongr

@[gcongr only] theorem CostMono.SoJProg_goodListCost {k k' m m' : ℕ} (h0 : k ≤ k') (h1 : m ≤ m')
    (x0 : 1 ≤ m') :
    GraphIso.SoJProg.goodListCost k m ≤
      GraphIso.SoJProg.goodListCost k' m' := by
  unfold GraphIso.SoJProg.goodListCost
  gcongr

@[gcongr only] theorem CostMono.Case3_pipePrefixCost {k k' m m' : ℕ} (h0 : k ≤ k') (h1 : m ≤ m')
    (x0 : 1 ≤ m') (x1 : 1 ≤ k') :
    GraphIso.Case3.pipePrefixCost k m ≤
      GraphIso.Case3.pipePrefixCost k' m' := by
  unfold GraphIso.Case3.pipePrefixCost
  gcongr

@[gcongr only] theorem CostMono.Case3_structsCost {k k' m m' Cz Cz' Z Z' : ℕ} (h0 : k ≤ k')
    (h1 : m ≤ m') (h2 : Cz ≤ Cz') (h3 : Z ≤ Z') (x0 : 1 ≤ m') (x1 : 1 ≤ k') :
    GraphIso.Case3.structsCost k m Cz Z ≤
      GraphIso.Case3.structsCost k' m' Cz' Z' := by
  unfold GraphIso.Case3.structsCost
  gcongr

@[gcongr only] theorem CostMono.Case3_twinsFlagCost {k k' m m' : ℕ} (h0 : k ≤ k') (h1 : m ≤ m')
    (x0 : 1 ≤ m') (x1 : 1 ≤ k') :
    GraphIso.Case3.twinsFlagCost k m ≤
      GraphIso.Case3.twinsFlagCost k' m' := by
  unfold GraphIso.Case3.twinsFlagCost
  gcongr

@[gcongr only] theorem CostMono.Case3_c3Cost
    {n n' N N' s s' g g' k k' mx mx' my my' kX kX' Ccol Ccol' Cx Cx' Cy Cy' Z Z' BgP BgP' : ℕ}
    {Bmem Bmem' Bk Bk' Bl Bl' Bg1 Bg1' Bgen Bgen' Cb Cb' : ℕ} (h1 : N ≤ N') (h2 : s ≤ s')
    (h3 : g ≤ g') (h4 : k ≤ k') (h5 : mx ≤ mx') (h6 : my ≤ my') (h7 : kX ≤ kX') (h8 : Ccol ≤ Ccol')
    (h9 : Cx ≤ Cx') (h10 : Cy ≤ Cy') (h11 : Z ≤ Z') (h12 : BgP ≤ BgP') (h13 : Bmem ≤ Bmem')
    (h14 : Bk ≤ Bk') (h15 : Bl ≤ Bl') (h16 : Bg1 ≤ Bg1') (h17 : Bgen ≤ Bgen') (h18 : Cb ≤ Cb')
    (s0 : N - n ≤ N' - n') (x0 : 1 ≤ my') (x1 : 1 ≤ mx') (x2 : 1 ≤ k') :
    GraphIso.Case3.c3Cost n N s g k mx my kX Ccol Cx Cy Z BgP Bmem Bk Bl Bg1 Bgen Cb ≤
      GraphIso.Case3.c3Cost n' N' s' g' k' mx' my' kX' Ccol' Cx' Cy' Z' BgP' Bmem' Bk' Bl' Bg1'
        Bgen' Cb' := by
  unfold GraphIso.Case3.c3Cost
  gcongr

@[gcongr only] theorem CostMono.Case3_skelCost {k k' c c' s s' : ℕ} (h0 : k ≤ k') (h1 : c ≤ c')
    (h2 : s ≤ s') :
    GraphIso.Case3.skelCost k c s ≤
      GraphIso.Case3.skelCost k' c' s' := by
  unfold GraphIso.Case3.skelCost
  gcongr

@[gcongr only] theorem CostMono.Case3_domCost {M M' k k' m m' s s' sz sz' : ℕ} (h0 : M ≤ M')
    (h1 : k ≤ k') (h2 : m ≤ m') (h3 : s ≤ s') (h4 : sz ≤ sz') :
    GraphIso.Case3.domCost M k m s sz ≤
      GraphIso.Case3.domCost M' k' m' s' sz' := by
  unfold GraphIso.Case3.domCost
  gcongr

@[gcongr only] theorem CostMono.Case3_outPrefixCost {k k' m m' L L' : ℕ} (h0 : k ≤ k') (h1 : m ≤ m')
    (h2 : L ≤ L') :
    GraphIso.Case3.outPrefixCost k m L ≤
      GraphIso.Case3.outPrefixCost k' m' L' := by
  unfold GraphIso.Case3.outPrefixCost
  gcongr

@[gcongr only] theorem CostMono.Case3_smallLeafCost {m m' : ℕ} (h0 : m ≤ m') :
    GraphIso.Case3.smallLeafCost m ≤
      GraphIso.Case3.smallLeafCost m' := by
  unfold GraphIso.Case3.smallLeafCost
  gcongr

@[gcongr only] theorem CostMono.Case3_c3OutCost {M M' k k' m m' Z Z' : ℕ} (h0 : M ≤ M')
    (h1 : k ≤ k') (h2 : m ≤ m') (h3 : Z ≤ Z') :
    GraphIso.Case3.c3OutCost M k m Z ≤
      GraphIso.Case3.c3OutCost M' k' m' Z' := by
  unfold GraphIso.Case3.c3OutCost
  gcongr

@[gcongr only] theorem CostMono.Case3_cmpCost {N N' k k' CI CI' : ℕ} (h0 : N ≤ N') (h1 : k ≤ k')
    (h2 : CI ≤ CI') :
    GraphIso.Case3.cmpCost N k CI ≤
      GraphIso.Case3.cmpCost N' k' CI' := by
  unfold GraphIso.Case3.cmpCost
  gcongr

@[gcongr only] theorem CostMono.Case3_firstIdxCost {L L' c c' : ℕ} (h0 : L ≤ L') (h1 : c ≤ c') :
    GraphIso.Case3.firstIdxCost L c ≤
      GraphIso.Case3.firstIdxCost L' c' := by
  unfold GraphIso.Case3.firstIdxCost
  gcongr

@[gcongr only] theorem CostMono.Case3_nodupCost {L L' : ℕ} (h0 : L ≤ L') :
    GraphIso.Case3.nodupCost L ≤
      GraphIso.Case3.nodupCost L' := by
  unfold GraphIso.Case3.nodupCost
  gcongr

@[gcongr only] theorem CostMono.Case3_entryXCost {L L' k k' cC cC' : ℕ} (h0 : L ≤ L') (h1 : k ≤ k')
    (h2 : cC ≤ cC') :
    GraphIso.Case3.entryXCost L k cC ≤
      GraphIso.Case3.entryXCost L' k' cC' := by
  unfold GraphIso.Case3.entryXCost
  gcongr

@[gcongr only] theorem CostMono.Case3_entryYCost {L L' k k' cC cC' : ℕ} (h0 : L ≤ L') (h1 : k ≤ k')
    (h2 : cC ≤ cC') :
    GraphIso.Case3.entryYCost L k cC ≤
      GraphIso.Case3.entryYCost L' k' cC' := by
  unfold GraphIso.Case3.entryYCost
  gcongr

@[gcongr only] theorem CostMono.Case3_tupleColCost {N N' k k' m m' CI CI' : ℕ} (h0 : N ≤ N')
    (h1 : k ≤ k') (h2 : m ≤ m') (h3 : CI ≤ CI') (x0 : 1 ≤ m') :
    GraphIso.Case3.tupleColCost N k m CI ≤
      GraphIso.Case3.tupleColCost N' k' m' CI' := by
  unfold GraphIso.Case3.tupleColCost
  gcongr

@[gcongr only] theorem CostMono.Case3_c3CostC
    {n n' N N' s s' g g' k k' mx mx' my my' CI CI' Z Z' BgP BgP' Bmem Bmem' Bk Bk' Bl Bl' : ℕ}
    {Bg1 Bg1' Bgen Bgen' Cb Cb' : ℕ} (h1 : N ≤ N') (h2 : s ≤ s') (h3 : g ≤ g') (h4 : k ≤ k')
    (h5 : mx ≤ mx') (h6 : my ≤ my') (h7 : CI ≤ CI') (h8 : Z ≤ Z') (h9 : BgP ≤ BgP')
    (h10 : Bmem ≤ Bmem') (h11 : Bk ≤ Bk') (h12 : Bl ≤ Bl') (h13 : Bg1 ≤ Bg1') (h14 : Bgen ≤ Bgen')
    (h15 : Cb ≤ Cb') (s0 : N - n ≤ N' - n') (x0 : 1 ≤ mx') (x1 : 1 ≤ my') (x2 : 1 ≤ k') :
    GraphIso.Case3.c3CostC n N s g k mx my CI Z BgP Bmem Bk Bl Bg1 Bgen Cb ≤
      GraphIso.Case3.c3CostC n' N' s' g' k' mx' my' CI' Z' BgP' Bmem' Bk' Bl' Bg1' Bgen' Cb' := by
  unfold GraphIso.Case3.c3CostC
  gcongr

@[gcongr only] theorem CostMono.CertProg_giantACost
    {k k' s s' Bgen Bgen' Borb Borb' Bstab Bstab' : ℕ} (h0 : k ≤ k') (h1 : s ≤ s')
    (h2 : Bgen ≤ Bgen') (h3 : Borb ≤ Borb') (h4 : Bstab ≤ Bstab') :
    GraphIso.CertProg.giantACost k s Bgen Borb Bstab ≤
      GraphIso.CertProg.giantACost k' s' Bgen' Borb' Bstab' := by
  unfold GraphIso.CertProg.giantACost
  gcongr

@[gcongr only] theorem CostMono.CertProg_affCost
    {n n' k k' s s' Bstab Bstab'' Bgen' Bgen'' Borb' Borb'' Bstab' Bstab''' : ℕ} (h0 : n ≤ n')
    (h1 : k ≤ k') (h2 : s ≤ s') (h3 : Bstab ≤ Bstab'') (h4 : Bgen' ≤ Bgen'') (h5 : Borb' ≤ Borb'')
    (h6 : Bstab' ≤ Bstab''') :
    GraphIso.CertProg.affCost n k s Bstab Bgen' Borb' Bstab' ≤
      GraphIso.CertProg.affCost n' k' s' Bstab'' Bgen'' Borb'' Bstab''' := by
  unfold GraphIso.CertProg.affCost
  gcongr

@[gcongr only] theorem CostMono.CertProg_stepPoly₀
    {N N' n n' k k' s s' Bstab Bstab'' Btr Btr' Borb Borb'' Bgen' Bgen'' Borb' Borb''' : ℕ}
    {Bstab' Bstab''' Bgen Bgen''' : ℕ} (h0 : N ≤ N') (h1 : n ≤ n') (h2 : k ≤ k') (h3 : s ≤ s')
    (h4 : Bstab ≤ Bstab'') (h5 : Btr ≤ Btr') (h6 : Borb ≤ Borb'') (h7 : Bgen' ≤ Bgen'')
    (h8 : Borb' ≤ Borb''') (h9 : Bstab' ≤ Bstab''') (h10 : Bgen ≤ Bgen''') :
    GraphIso.CertProg.stepPoly₀ N n k s Bstab Btr Borb Bgen' Borb' Bstab' Bgen ≤
      GraphIso.CertProg.stepPoly₀ N' n' k' s' Bstab'' Btr' Borb'' Bgen'' Borb''' Bstab'''
        Bgen''' := by
  unfold GraphIso.CertProg.stepPoly₀
  gcongr

@[gcongr only] theorem CostMono.CertProg_stepPoly₁ {N N' n n' k k' s s' : ℕ} (h0 : N ≤ N')
    (h1 : n ≤ n') (h2 : k ≤ k') (h3 : s ≤ s') :
    GraphIso.CertProg.stepPoly₁ N n k s ≤
      GraphIso.CertProg.stepPoly₁ N' n' k' s' := by
  unfold GraphIso.CertProg.stepPoly₁
  gcongr

@[gcongr only] theorem CostMono.CertProg_stepPoly
    {N N' n n' k k' s s' Bstab Bstab'' Btr Btr' Borb Borb'' Bgen' Bgen'' Borb' Borb''' : ℕ}
    {Bstab' Bstab''' Bgen Bgen''' : ℕ} (h0 : N ≤ N') (h1 : n ≤ n') (h2 : k ≤ k') (h3 : s ≤ s')
    (h4 : Bstab ≤ Bstab'') (h5 : Btr ≤ Btr') (h6 : Borb ≤ Borb'') (h7 : Bgen' ≤ Bgen'')
    (h8 : Borb' ≤ Borb''') (h9 : Bstab' ≤ Bstab''') (h10 : Bgen ≤ Bgen''') :
    GraphIso.CertProg.stepPoly N n k s Bstab Btr Borb Bgen' Borb' Bstab' Bgen ≤
      GraphIso.CertProg.stepPoly N' n' k' s' Bstab'' Btr' Borb'' Bgen'' Borb''' Bstab'''
        Bgen''' := by
  unfold GraphIso.CertProg.stepPoly
  gcongr

@[gcongr only] theorem CostMono.CertProg_unionCost {k k' l l' : ℕ} (h0 : k ≤ k') (h1 : l ≤ l') :
    GraphIso.CertProg.unionCost k l ≤
      GraphIso.CertProg.unionCost k' l' := by
  unfold GraphIso.CertProg.unionCost
  gcongr

@[gcongr only] theorem CostMono.CertProg_loopPoly
    {N N' n n' k k' s s' Bstab Bstab'' Btr Btr' Borb Borb'' Bgen' Bgen'' Borb' Borb''' : ℕ}
    {Bstab' Bstab''' Bgen Bgen''' : ℕ} (h0 : N ≤ N') (h1 : n ≤ n') (h2 : k ≤ k') (h3 : s ≤ s')
    (h4 : Bstab ≤ Bstab'') (h5 : Btr ≤ Btr') (h6 : Borb ≤ Borb'') (h7 : Bgen' ≤ Bgen'')
    (h8 : Borb' ≤ Borb''') (h9 : Bstab' ≤ Bstab''') (h10 : Bgen ≤ Bgen''') :
    GraphIso.CertProg.loopPoly N n k s Bstab Btr Borb Bgen' Borb' Bstab' Bgen ≤
      GraphIso.CertProg.loopPoly N' n' k' s' Bstab'' Btr' Borb'' Bgen'' Borb''' Bstab'''
        Bgen''' := by
  unfold GraphIso.CertProg.loopPoly
  gcongr

@[gcongr only] theorem CostMono.CertProg_outsideCost {m m' k k' : ℕ} (h0 : m ≤ m') (h1 : k ≤ k') :
    GraphIso.CertProg.outsideCost m k ≤
      GraphIso.CertProg.outsideCost m' k' := by
  unfold GraphIso.CertProg.outsideCost
  gcongr

@[gcongr only] theorem CostMono.Toolkit_swapPairCost {m m' : ℕ} (h0 : m ≤ m') :
    GraphIso.Toolkit.swapPairCost m ≤
      GraphIso.Toolkit.swapPairCost m' := by
  unfold GraphIso.Toolkit.swapPairCost
  gcongr

@[gcongr only] theorem CostMono.CertProg_moveFixCost {m m' k k' : ℕ} (h0 : m ≤ m') (h1 : k ≤ k') :
    GraphIso.CertProg.moveFixCost m k ≤
      GraphIso.CertProg.moveFixCost m' k' := by
  unfold GraphIso.CertProg.moveFixCost
  gcongr

@[gcongr only] theorem CostMono.CertProg_moveStepCost {m m' : ℕ} (h0 : m ≤ m') :
    GraphIso.CertProg.moveStepCost m ≤
      GraphIso.CertProg.moveStepCost m' := by
  unfold GraphIso.CertProg.moveStepCost
  gcongr

@[gcongr only] theorem CostMono.CertProg_moveDataCost {m m' k k'' k' k''' : ℕ} (h0 : m ≤ m')
    (h1 : k ≤ k'') (h2 : k' ≤ k''') :
    GraphIso.CertProg.moveDataCost m k k' ≤
      GraphIso.CertProg.moveDataCost m' k'' k''' := by
  unfold GraphIso.CertProg.moveDataCost
  gcongr

@[gcongr only] theorem CostMono.CertProg_ttStepCost {N N' Bt Bt' Bs Bs' : ℕ} (h0 : N ≤ N')
    (h1 : Bt ≤ Bt') (h2 : Bs ≤ Bs') :
    GraphIso.CertProg.ttStepCost N Bt Bs ≤
      GraphIso.CertProg.ttStepCost N' Bt' Bs' := by
  unfold GraphIso.CertProg.ttStepCost
  gcongr

@[gcongr only] theorem CostMono.CertProg_tupleTransCost {N N' k k' Bt Bt' Bs Bs' : ℕ} (h0 : N ≤ N')
    (h1 : k ≤ k') (h2 : Bt ≤ Bt') (h3 : Bs ≤ Bs') :
    GraphIso.CertProg.tupleTransCost N k Bt Bs ≤
      GraphIso.CertProg.tupleTransCost N' k' Bt' Bs' := by
  unfold GraphIso.CertProg.tupleTransCost
  gcongr

@[gcongr only] theorem CostMono.Toolkit_giantSetStabCost {n n' N N' k k' Bs Bs' Bl Bl' Bg Bg' : ℕ}
    (h1 : N ≤ N') (h2 : k ≤ k') (h3 : Bs ≤ Bs') (h4 : Bl ≤ Bl') (h5 : Bg ≤ Bg')
    (s0 : N - n ≤ N' - n') :
    GraphIso.Toolkit.giantSetStabCost n N k Bs Bl Bg ≤
      GraphIso.Toolkit.giantSetStabCost n' N' k' Bs' Bl' Bg' := by
  unfold GraphIso.Toolkit.giantSetStabCost
  gcongr

@[gcongr only] theorem CostMono.CertProg_certIsoPoly
    {N N' n n' k k' s s' Bstab Bstab'' Btr Btr' Borb Borb'' Bgen' Bgen'' Borb' Borb''' : ℕ}
    {Bstab' Bstab''' Bgen Bgen''' Bl Bl' Bgs Bgs' : ℕ} (h0 : N ≤ N') (h1 : n ≤ n') (h2 : k ≤ k')
    (h3 : s ≤ s') (h4 : Bstab ≤ Bstab'') (h5 : Btr ≤ Btr') (h6 : Borb ≤ Borb'')
    (h7 : Bgen' ≤ Bgen'') (h8 : Borb' ≤ Borb''') (h9 : Bstab' ≤ Bstab''') (h10 : Bgen ≤ Bgen''')
    (h11 : Bl ≤ Bl') (h12 : Bgs ≤ Bgs') (s0 : N - n ≤ N' - n') :
    GraphIso.CertProg.certIsoPoly N n k s Bstab Btr Borb Bgen' Borb' Bstab' Bgen Bl Bgs ≤
      GraphIso.CertProg.certIsoPoly N' n' k' s' Bstab'' Btr' Borb'' Bgen'' Borb''' Bstab''' Bgen'''
        Bl' Bgs' := by
  unfold GraphIso.CertProg.certIsoPoly
  gcongr

@[gcongr only] theorem CostMono.CertProg_certPoly
    {N N' n n' k k' s s' Bstab Bstab'' Btr Btr' Borb Borb'' Bgen' Bgen'' Borb' Borb''' : ℕ}
    {Bstab' Bstab''' Bgen Bgen''' Bl Bl' Bgs Bgs' : ℕ} (h0 : N ≤ N') (h1 : n ≤ n') (h2 : k ≤ k')
    (h3 : s ≤ s') (h4 : Bstab ≤ Bstab'') (h5 : Btr ≤ Btr') (h6 : Borb ≤ Borb'')
    (h7 : Bgen' ≤ Bgen'') (h8 : Borb' ≤ Borb''') (h9 : Bstab' ≤ Bstab''') (h10 : Bgen ≤ Bgen''')
    (h11 : Bl ≤ Bl') (h12 : Bgs ≤ Bgs') (s0 : N - n ≤ N' - n') :
    GraphIso.CertProg.certPoly N n k s Bstab Btr Borb Bgen' Borb' Bstab' Bgen Bl Bgs ≤
      GraphIso.CertProg.certPoly N' n' k' s' Bstab'' Btr' Borb'' Bgen'' Borb''' Bstab''' Bgen''' Bl'
        Bgs' := by
  unfold GraphIso.CertProg.certPoly
  gcongr

@[gcongr only] theorem CostMono.CertProg_kerACost {N N' k k' Bt Bt' Bs Bs' : ℕ} (h0 : N ≤ N')
    (h1 : k ≤ k') (h2 : Bt ≤ Bt') (h3 : Bs ≤ Bs') :
    GraphIso.CertProg.kerACost N k Bt Bs ≤
      GraphIso.CertProg.kerACost N' k' Bt' Bs' := by
  unfold GraphIso.CertProg.kerACost
  gcongr

@[gcongr only] theorem CostMono.Giant_agExtCost {L L' : ℕ} (h0 : L ≤ L') :
    GraphIso.Giant.agExtCost L ≤
      GraphIso.Giant.agExtCost L' := by
  unfold GraphIso.Giant.agExtCost
  gcongr

@[gcongr only] theorem CostMono.Giant_c1OrbitCost {K K' L L' : ℕ} (h0 : K ≤ K') (h1 : L ≤ L') :
    GraphIso.Giant.c1OrbitCost K L ≤
      GraphIso.Giant.c1OrbitCost K' L' := by
  unfold GraphIso.Giant.c1OrbitCost
  gcongr

@[gcongr only] theorem CostMono.Giant_c2aCost
    {n n' N N' g g' k k' Φl Φl' BgP BgP' Bmem Bmem' Bk Bk' Bl Bl' Bg1 Bg1' Bgen Bgen' cP : ℕ}
    {cP' s s' : ℕ} (h1 : N ≤ N') (h2 : g ≤ g') (h3 : k ≤ k') (h4 : Φl ≤ Φl') (h5 : BgP ≤ BgP')
    (h6 : Bmem ≤ Bmem') (h7 : Bk ≤ Bk') (h8 : Bl ≤ Bl') (h9 : Bg1 ≤ Bg1') (h10 : Bgen ≤ Bgen')
    (h11 : cP ≤ cP') (h12 : s ≤ s') (s0 : N - n ≤ N' - n') :
    GraphIso.Giant.c2aCost n N g k Φl BgP Bmem Bk Bl Bg1 Bgen cP s ≤
      GraphIso.Giant.c2aCost n' N' g' k' Φl' BgP' Bmem' Bk' Bl' Bg1' Bgen' cP' s' := by
  unfold GraphIso.Giant.c2aCost
  gcongr

@[gcongr only] theorem CostMono.Giant_orbitPartCost {m m' K K' L L' : ℕ} (h0 : m ≤ m') (h1 : K ≤ K')
    (h2 : L ≤ L') :
    GraphIso.Giant.orbitPartCost m K L ≤
      GraphIso.Giant.orbitPartCost m' K' L' := by
  unfold GraphIso.Giant.orbitPartCost
  gcongr

@[gcongr only] theorem CostMono.Giant_case1Cost
    {n n' N N' g g' k k' Box Box' Boy Boy' BgP BgP' Bmem Bmem' Bk Bk' Bl Bl' Bg1 Bg1' Bgen : ℕ}
    {Bgen' Cb Cb' s s' : ℕ} (h1 : N ≤ N') (h2 : g ≤ g') (h3 : k ≤ k') (h4 : Box ≤ Box')
    (h5 : Boy ≤ Boy') (h6 : BgP ≤ BgP') (h7 : Bmem ≤ Bmem') (h8 : Bk ≤ Bk') (h9 : Bl ≤ Bl')
    (h10 : Bg1 ≤ Bg1') (h11 : Bgen ≤ Bgen') (h12 : Cb ≤ Cb') (h13 : s ≤ s') (s0 : N - n ≤ N' - n') :
    GraphIso.Giant.case1Cost n N g k Box Boy BgP Bmem Bk Bl Bg1 Bgen Cb s ≤
      GraphIso.Giant.case1Cost n' N' g' k' Box' Boy' BgP' Bmem' Bk' Bl' Bg1' Bgen' Cb' s' := by
  unfold GraphIso.Giant.case1Cost
  gcongr

@[gcongr only] theorem CostMono.Giant_caseCost {n n' N N' Borb Borb' : ℕ} (h1 : N ≤ N')
    (h2 : Borb ≤ Borb') (s0 : N - n ≤ N' - n') :
    GraphIso.Giant.caseCost n N Borb ≤
      GraphIso.Giant.caseCost n' N' Borb' := by
  unfold GraphIso.Giant.caseCost
  gcongr

@[gcongr only] theorem CostMono.Giant_ksubsCost {m m' k k' : ℕ} (h0 : m ≤ m') (h1 : k ≤ k')
    (x0 : m.choose k ≤ m'.choose k') :
    GraphIso.Giant.ksubsCost m k ≤
      GraphIso.Giant.ksubsCost m' k' := by
  unfold GraphIso.Giant.ksubsCost
  gcongr

@[gcongr only] theorem CostMono.Giant_pbBranchCost {N N' s s' Cb Cb' Bg Bg' wl wl' : ℕ}
    (h0 : N ≤ N') (h1 : s ≤ s') (h2 : Cb ≤ Cb') (h3 : Bg ≤ Bg') (h4 : wl ≤ wl') :
    GraphIso.Giant.pbBranchCost N s Cb Bg wl ≤
      GraphIso.Giant.pbBranchCost N' s' Cb' Bg' wl' := by
  unfold GraphIso.Giant.pbBranchCost
  gcongr

@[gcongr only] theorem CostMono.Giant_pbCost
    {N N' s s' Cb Cb' Bstab Bstab' Borb Borb' Bgen Bgen' p p' h h' wl wl' : ℕ} (h0 : N ≤ N')
    (h1 : s ≤ s') (h2 : Cb ≤ Cb') (h3 : Bstab ≤ Bstab') (h4 : Borb ≤ Borb') (h5 : Bgen ≤ Bgen')
    (h6 : p ≤ p') (h7 : h ≤ h') (h8 : wl ≤ wl') :
    GraphIso.Giant.pbCost N s Cb Bstab Borb Bgen p h wl ≤
      GraphIso.Giant.pbCost N' s' Cb' Bstab' Borb' Bgen' p' h' wl' := by
  unfold GraphIso.Giant.pbCost
  gcongr

@[gcongr only] theorem CostMono.Luks_closureCost {n n' m m' s s' : ℕ} (h0 : n ≤ n') (h1 : m ≤ m')
    (h2 : s ≤ s') :
    GraphIso.Luks.closureCost n m s ≤
      GraphIso.Luks.closureCost n' m' s' := by
  unfold GraphIso.Luks.closureCost
  gcongr

@[gcongr only] theorem CostMono.Luks_mbCost {n n' m m' s s' : ℕ} (h0 : n ≤ n') (h1 : m ≤ m')
    (h2 : s ≤ s') :
    GraphIso.Luks.mbCost n m s ≤
      GraphIso.Luks.mbCost n' m' s' := by
  unfold GraphIso.Luks.mbCost
  gcongr

@[gcongr only] theorem CostMono.Luks_maxBlocksCost {n n' m m' s s' : ℕ} (h0 : n ≤ n') (h1 : m ≤ m')
    (h2 : s ≤ s') :
    GraphIso.Luks.maxBlocksCost n m s ≤
      GraphIso.Luks.maxBlocksCost n' m' s' := by
  unfold GraphIso.Luks.maxBlocksCost
  gcongr

@[gcongr only] theorem CostMono.Toolkit_blockLabCost {k k' t t' : ℕ} (h0 : k ≤ k') (h1 : t ≤ t') :
    GraphIso.Toolkit.blockLabCost k t ≤
      GraphIso.Toolkit.blockLabCost k' t' := by
  unfold GraphIso.Toolkit.blockLabCost
  gcongr

@[gcongr only] theorem CostMono.Toolkit_rebaseCost {n n' N N' m m' k k' s s' Bgen Bgen' : ℕ}
    (h0 : n ≤ n') (h1 : N ≤ N') (h2 : m ≤ m') (h3 : k ≤ k') (h4 : s ≤ s') (h5 : Bgen ≤ Bgen') :
    GraphIso.Toolkit.rebaseCost n N m k s Bgen ≤
      GraphIso.Toolkit.rebaseCost n' N' m' k' s' Bgen' := by
  unfold GraphIso.Toolkit.rebaseCost
  gcongr

@[gcongr only] theorem CostMono.Main_m2aCost {n n' N N' p p' s s' Ls Ls' Bgen Bgen' : ℕ}
    (h0 : n ≤ n') (h1 : N ≤ N') (h2 : p ≤ p') (h3 : s ≤ s') (h4 : Ls ≤ Ls') (h5 : Bgen ≤ Bgen')
    (s0 : N - n ≤ N' - n') :
    GraphIso.Main.m2aCost n N p s Ls Bgen ≤
      GraphIso.Main.m2aCost n' N' p' s' Ls' Bgen' := by
  unfold GraphIso.Main.m2aCost
  gcongr

@[gcongr only] theorem CostMono.Toolkit_blockStabCost
    {N N' m m' k k' s s' sS sS' L L' Bge Bge' Bst Bst' Btr Btr' Bgt Bgt' : ℕ} (h0 : N ≤ N')
    (h1 : m ≤ m') (h2 : k ≤ k') (h3 : s ≤ s') (h4 : sS ≤ sS') (h5 : L ≤ L') (h6 : Bge ≤ Bge')
    (h7 : Bst ≤ Bst') (h8 : Btr ≤ Btr') (h9 : Bgt ≤ Bgt') :
    GraphIso.Toolkit.blockStabCost N m k s sS L Bge Bst Btr Bgt ≤
      GraphIso.Toolkit.blockStabCost N' m' k' s' sS' L' Bge' Bst' Btr' Bgt' := by
  unfold GraphIso.Toolkit.blockStabCost
  gcongr

@[gcongr only] theorem CostMono.Toolkit_interCost {t t' : ℕ} (h0 : t ≤ t') :
    GraphIso.Toolkit.interCost t ≤
      GraphIso.Toolkit.interCost t' := by
  unfold GraphIso.Toolkit.interCost
  gcongr

@[gcongr only] theorem CostMono.Toolkit_markCost {k k' t t' : ℕ} (h0 : k ≤ k') (h1 : t ≤ t') :
    GraphIso.Toolkit.markCost k t ≤
      GraphIso.Toolkit.markCost k' t' := by
  unfold GraphIso.Toolkit.markCost
  gcongr

@[gcongr only] theorem CostMono.Main_m2bCost
    {N N' n n' mb mb' kb kb' s s' sS sS' Lt Lt' Bge Bge' Bst Bst' Btr Btr' Bgt Bgt' k k' sH : ℕ}
    {sH' Bgen Bgen' wl wl' T T' Ls Ls' : ℕ} (h0 : N ≤ N') (h1 : n ≤ n') (h2 : mb ≤ mb')
    (h3 : kb ≤ kb') (h4 : s ≤ s') (h5 : sS ≤ sS') (h6 : Lt ≤ Lt') (h7 : Bge ≤ Bge')
    (h8 : Bst ≤ Bst') (h9 : Btr ≤ Btr') (h10 : Bgt ≤ Bgt') (h11 : k ≤ k') (h12 : sH ≤ sH')
    (h13 : Bgen ≤ Bgen') (h14 : wl ≤ wl') (h15 : T ≤ T') (h16 : Ls ≤ Ls') (s0 : N - n ≤ N' - n') :
    GraphIso.Main.m2bCost N n mb kb s sS Lt Bge Bst Btr Bgt k sH Bgen wl T Ls ≤
      GraphIso.Main.m2bCost N' n' mb' kb' s' sS' Lt' Bge' Bst' Btr' Bgt' k' sH' Bgen' wl' T'
        Ls' := by
  unfold GraphIso.Main.m2bCost
  gcongr

@[gcongr only] theorem CostMono.Toolkit_equidistCost {k k' t t' : ℕ} (h0 : k ≤ k') (h1 : t ≤ t') :
    GraphIso.Toolkit.equidistCost k t ≤
      GraphIso.Toolkit.equidistCost k' t' := by
  unfold GraphIso.Toolkit.equidistCost
  gcongr

@[gcongr only] theorem CostMono.Main_neqCost {N N' m m' f f' k k' p p' T T' : ℕ} (h0 : N ≤ N')
    (h1 : m ≤ m') (h2 : f ≤ f') (h3 : k ≤ k') (h4 : p ≤ p') (h5 : T ≤ T') :
    GraphIso.Main.neqCost N m f k p T ≤
      GraphIso.Main.neqCost N' m' f' k' p' T' := by
  unfold GraphIso.Main.neqCost
  gcongr

@[gcongr only] theorem CostMono.Toolkit_baseBlocksCost {N N' m m' s s' : ℕ} (h0 : N ≤ N')
    (h1 : m ≤ m') (h2 : s ≤ s') :
    GraphIso.Toolkit.baseBlocksCost N m s ≤
      GraphIso.Toolkit.baseBlocksCost N' m' s' := by
  unfold GraphIso.Toolkit.baseBlocksCost
  gcongr

@[gcongr only] theorem CostMono.Main_blocksCost
    {n n' N N' p p' s₁ s₁' sS sS' Lt Lt' sH sH' Bgen₂ Bgen₂' Bge Bge' Bst Bst' Btr Btr' Bgt : ℕ}
    {Bgt' Bgen₃ Bgen₃' : ℕ} (h0 : n ≤ n') (h1 : N ≤ N') (h2 : p ≤ p') (h3 : s₁ ≤ s₁')
    (h4 : sS ≤ sS') (h5 : Lt ≤ Lt') (h6 : sH ≤ sH') (h7 : Bgen₂ ≤ Bgen₂') (h8 : Bge ≤ Bge')
    (h9 : Bst ≤ Bst') (h10 : Btr ≤ Btr') (h11 : Bgt ≤ Bgt') (h12 : Bgen₃ ≤ Bgen₃')
    (s0 : N - n ≤ N' - n') :
    GraphIso.Main.blocksCost n N p s₁ sS Lt sH Bgen₂ Bge Bst Btr Bgt Bgen₃ ≤
      GraphIso.Main.blocksCost n' N' p' s₁' sS' Lt' sH' Bgen₂' Bge' Bst' Btr' Bgt' Bgen₃' := by
  unfold GraphIso.Main.blocksCost
  gcongr

@[gcongr only] theorem CostMono.Programs_liftCost
    {n n' s' s'' sK sK' Blift Blift' Bker Bker' Bgn Bgn' : ℕ} (h0 : n ≤ n') (h1 : s' ≤ s'')
    (h2 : sK ≤ sK') (h3 : Blift ≤ Blift') (h4 : Bker ≤ Bker') (h5 : Bgn ≤ Bgn') :
    GraphIso.Programs.liftCost n s' sK Blift Bker Bgn ≤
      GraphIso.Programs.liftCost n' s'' sK' Blift' Bker' Bgn' := by
  unfold GraphIso.Programs.liftCost
  gcongr

@[gcongr only] theorem CostMono.Programs_restrictCost
    {n n' m m' s s'' C C' s' s''' sK sK' Bgm Bgm' Blift Blift' Bker Bker' Bgn Bgn' : ℕ}
    (h0 : n ≤ n') (h1 : m ≤ m') (h2 : s ≤ s'') (h3 : C ≤ C') (h4 : s' ≤ s''') (h5 : sK ≤ sK')
    (h6 : Bgm ≤ Bgm') (h7 : Blift ≤ Blift') (h8 : Bker ≤ Bker') (h9 : Bgn ≤ Bgn') :
    GraphIso.Programs.restrictCost n m s C s' sK Bgm Blift Bker Bgn ≤
      GraphIso.Programs.restrictCost n' m' s'' C' s''' sK' Bgm' Blift' Bker' Bgn' := by
  unfold GraphIso.Programs.restrictCost
  gcongr

@[gcongr only] theorem CostMono.Main_c2aWork
    {n n' N N' g g' k k' Φl Φl' BgP BgP' Bmem Bmem' Bk Bk' Bl Bl' Bg1 Bg1' Bgen Bgen' s s' : ℕ}
    {Bstab Bstab' Borb Borb' Bpb Bpb' wl wl' sH sH' sK sK' Bgm Bgm' Blift Blift' Bker Bker' : ℕ}
    {Bgn Bgn' : ℕ} (h1 : N ≤ N') (h2 : g ≤ g') (h3 : k ≤ k') (h4 : Φl ≤ Φl') (h5 : BgP ≤ BgP')
    (h6 : Bmem ≤ Bmem') (h7 : Bk ≤ Bk') (h8 : Bl ≤ Bl') (h9 : Bg1 ≤ Bg1') (h10 : Bgen ≤ Bgen')
    (h11 : s ≤ s') (h12 : Bstab ≤ Bstab') (h13 : Borb ≤ Borb') (h14 : Bpb ≤ Bpb') (h15 : wl ≤ wl')
    (h16 : sH ≤ sH') (h17 : sK ≤ sK') (h18 : Bgm ≤ Bgm') (h19 : Blift ≤ Blift') (h20 : Bker ≤ Bker')
    (h21 : Bgn ≤ Bgn') (x0 : N - n ≤ N' - n') :
    GraphIso.Main.c2aWork n N g k Φl BgP Bmem Bk Bl Bg1 Bgen s Bstab Borb Bpb wl sH sK Bgm Blift
        Bker Bgn ≤
      GraphIso.Main.c2aWork n' N' g' k' Φl' BgP' Bmem' Bk' Bl' Bg1' Bgen' s' Bstab' Borb' Bpb' wl'
        sH' sK' Bgm' Blift' Bker' Bgn' := by
  unfold GraphIso.Main.c2aWork
  gcongr

@[gcongr only] theorem CostMono.Main_cjPairCost {Cc Cc' Lc Lc' : ℕ} (h0 : Cc ≤ Cc') (h1 : Lc ≤ Lc')
    :
    GraphIso.Main.cjPairCost Cc Lc ≤
      GraphIso.Main.cjPairCost Cc' Lc' := by
  unfold GraphIso.Main.cjPairCost
  gcongr

@[gcongr only] theorem CostMono.Main_q2bCost {m m' p p' s s' : ℕ} (h0 : m ≤ m') (h1 : p ≤ p')
    (h2 : s ≤ s') :
    GraphIso.Main.q2bCost m p s ≤
      GraphIso.Main.q2bCost m' p' s' := by
  unfold GraphIso.Main.q2bCost
  gcongr

@[gcongr only] theorem CostMono.Main_cjTupleCost {m m' nΦ nΦ' j j' Cc Cc' Lc Lc' : ℕ} (h0 : m ≤ m')
    (h1 : nΦ ≤ nΦ') (h2 : j ≤ j') (h3 : Cc ≤ Cc') (h4 : Lc ≤ Lc') :
    GraphIso.Main.cjTupleCost m nΦ j Cc Lc ≤
      GraphIso.Main.cjTupleCost m' nΦ' j' Cc' Lc' := by
  unfold GraphIso.Main.cjTupleCost
  gcongr

@[gcongr only] theorem CostMono.Main_cjAllCost {m m' nΦ nΦ' j j' Cc Cc' Lc Lc' : ℕ} (h0 : m ≤ m')
    (h1 : nΦ ≤ nΦ') (h2 : j ≤ j') (h3 : Cc ≤ Cc') (h4 : Lc ≤ Lc') (x0 : 1 ≤ nΦ') :
    GraphIso.Main.cjAllCost m nΦ j Cc Lc ≤
      GraphIso.Main.cjAllCost m' nΦ' j' Cc' Lc' := by
  unfold GraphIso.Main.cjAllCost
  gcongr

@[gcongr only] theorem CostMono.Main_cjohnGensCost {B B' : ℕ} (h0 : B ≤ B') :
    GraphIso.Main.cjohnGensCost B ≤
      GraphIso.Main.cjohnGensCost B' := by
  unfold GraphIso.Main.cjohnGensCost
  gcongr

@[gcongr only] theorem CostMono.Main_ccolsCost {B B' : ℕ} (h0 : B ≤ B') :
    GraphIso.Main.ccolsCost B ≤
      GraphIso.Main.ccolsCost B' := by
  unfold GraphIso.Main.ccolsCost
  gcongr

@[gcongr only] theorem CostMono.Main_crestCost {B B' : ℕ} (h0 : B ≤ B') :
    GraphIso.Main.crestCost B ≤
      GraphIso.Main.crestCost B' := by
  unfold GraphIso.Main.crestCost
  gcongr

@[gcongr only] theorem CostMono.Main_cjohnIsoCost {B B' : ℕ} (h0 : B ≤ B') :
    GraphIso.Main.cjohnIsoCost B ≤
      GraphIso.Main.cjohnIsoCost B' := by
  unfold GraphIso.Main.cjohnIsoCost
  gcongr

@[gcongr only] theorem CostMono.Main_c2bCJCost
    {n n' N N' s s' g g' nx nx' ny ny' j j' k k' Bstab Bstab' Bg Bg' Z Z' BgP BgP' Bmem : ℕ}
    {Bmem' Bk Bk' Bl Bl' Bg1 Bg1' Bgen Bgen' Cb Cb' : ℕ} {Bo : ℕ → ℕ} {Bs : ℕ → ℕ} {Bt : ℕ → ℕ}
    (h1 : N ≤ N') (h2 : s ≤ s') (h3 : g ≤ g') (h4 : nx ≤ nx') (h5 : ny ≤ ny') (h6 : j ≤ j')
    (h7 : k ≤ k') (h8 : Bstab ≤ Bstab') (h9 : Bg ≤ Bg') (h10 : Z ≤ Z') (h11 : BgP ≤ BgP')
    (h12 : Bmem ≤ Bmem') (h13 : Bk ≤ Bk') (h14 : Bl ≤ Bl') (h15 : Bg1 ≤ Bg1') (h16 : Bgen ≤ Bgen')
    (h17 : Cb ≤ Cb') (s0 : nx - j ≤ nx' - j') (s1 : N - n ≤ N' - n') (s2 : ny - j ≤ ny' - j')
    (x0 : Bo nx ≤ Bo nx') (x1 : Bs nx ≤ Bs nx') (x2 : Bo ny ≤ Bo ny') (x3 : Bs ny ≤ Bs ny')
    (x4 : 1 ≤ nx' - j') (x5 : Bt (nx - j) ≤ Bt (nx' - j')) (x6 : Bs (nx - j) ≤ Bs (nx' - j'))
    (x7 : Bo (nx - j) ≤ Bo (nx' - j')) (x8 : 1 ≤ ny') (x9 : 1 ≤ ny' - j')
    (x10 : Bt (ny - j) ≤ Bt (ny' - j')) (x11 : Bs (ny - j) ≤ Bs (ny' - j'))
    (x12 : Bo (ny - j) ≤ Bo (ny' - j')) :
    GraphIso.Main.c2bCJCost n N s g nx ny j k Bstab Bg Z BgP Bmem Bk Bl Bg1 Bgen Cb Bo Bs Bt ≤
      GraphIso.Main.c2bCJCost n' N' s' g' nx' ny' j' k' Bstab' Bg' Z' BgP' Bmem' Bk' Bl' Bg1' Bgen'
        Cb' Bo Bs Bt := by
  unfold GraphIso.Main.c2bCJCost
  gcongr

@[gcongr only] theorem CostMono.Main_c2bJTestCost
    {N N' n n' s s' nx nx' j j' Bstab Bstab' Bg Bg' Z Z' : ℕ} {Bo : ℕ → ℕ} {Bs : ℕ → ℕ} {Bt : ℕ → ℕ}
    (h0 : N ≤ N') (h2 : s ≤ s') (h3 : nx ≤ nx') (h4 : j ≤ j') (h5 : Bstab ≤ Bstab') (h6 : Bg ≤ Bg')
    (h7 : Z ≤ Z') (s0 : nx - j ≤ nx' - j') (x0 : N - n ≤ N' - n') (x1 : Bo nx ≤ Bo nx')
    (x2 : Bs nx ≤ Bs nx') (x3 : 1 ≤ nx' - j') (x4 : Bt (nx - j) ≤ Bt (nx' - j'))
    (x5 : Bs (nx - j) ≤ Bs (nx' - j')) (x6 : Bo (nx - j) ≤ Bo (nx' - j')) :
    GraphIso.Main.c2bJTestCost N n s nx j Bstab Bg Z Bo Bs Bt ≤
      GraphIso.Main.c2bJTestCost N' n' s' nx' j' Bstab' Bg' Z' Bo Bs Bt := by
  unfold GraphIso.Main.c2bJTestCost
  gcongr

@[gcongr only] theorem CostMono.Main_c2bRU {m m' : ℕ} (h0 : m ≤ m') :
    GraphIso.Main.c2bRU m ≤
      GraphIso.Main.c2bRU m' := by
  unfold GraphIso.Main.c2bRU
  gcongr
  all_goals omega

@[gcongr only] theorem CostMono.Main_c2bRj {m m' jB jB' : ℕ} (h0 : m ≤ m') (h1 : jB ≤ jB') :
    GraphIso.Main.c2bRj m jB ≤
      GraphIso.Main.c2bRj m' jB' := by
  unfold GraphIso.Main.c2bRj
  gcongr
  all_goals omega

@[gcongr only] theorem CostMono.Main_c3ClsCost {k k' m m' L L' : ℕ} (h0 : k ≤ k') (h1 : m ≤ m')
    (h2 : L ≤ L') :
    GraphIso.Main.c3ClsCost k m L ≤
      GraphIso.Main.c3ClsCost k' m' L' := by
  unfold GraphIso.Main.c3ClsCost
  gcongr

@[gcongr only] theorem CostMono.Main_c3FirstClsCost {k k' m m' : ℕ} (h0 : k ≤ k') (h1 : m ≤ m')
    (x0 : 1 ≤ m') (x1 : 1 ≤ k') :
    GraphIso.Main.c3FirstClsCost k m ≤
      GraphIso.Main.c3FirstClsCost k' m' := by
  unfold GraphIso.Main.c3FirstClsCost
  gcongr

@[gcongr only] theorem CostMono.Main_q3Cost {M M' p p' s s' : ℕ} (h0 : M ≤ M') (h1 : p ≤ p')
    (h2 : s ≤ s') :
    GraphIso.Main.q3Cost M p s ≤
      GraphIso.Main.q3Cost M' p' s' := by
  unfold GraphIso.Main.q3Cost
  gcongr

@[gcongr only] theorem CostMono.Main_cjOut3Cost {M M' k k' m m' L L' Cz Cz' Z Z' : ℕ} (h0 : M ≤ M')
    (h1 : k ≤ k') (h2 : m ≤ m') (h3 : L ≤ L') (h4 : Cz ≤ Cz') (h5 : Z ≤ Z') :
    GraphIso.Main.cjOut3Cost M k m L Cz Z ≤
      GraphIso.Main.cjOut3Cost M' k' m' L' Cz' Z' := by
  unfold GraphIso.Main.cjOut3Cost
  gcongr

@[gcongr only] theorem CostMono.Main_cjStructs3Cost {M M' k k' m m' Cz Cz' Z Z' : ℕ} (h0 : M ≤ M')
    (h1 : k ≤ k') (h2 : m ≤ m') (h3 : Cz ≤ Cz') (h4 : Z ≤ Z') (x0 : 1 ≤ m') (x1 : 1 ≤ k') :
    GraphIso.Main.cjStructs3Cost M k m Cz Z ≤
      GraphIso.Main.cjStructs3Cost M' k' m' Cz' Z' := by
  unfold GraphIso.Main.cjStructs3Cost
  gcongr

@[gcongr only] theorem CostMono.Main_c3CJCost
    {n n' N N' s s' g g' k k' mx mx' my my' Z Z' BgP BgP' Bmem Bmem' Bk Bk' Bl Bl' Bg1 Bg1' : ℕ}
    {Bgen Bgen' Cb Cb' : ℕ} (h1 : N ≤ N') (h2 : s ≤ s') (h3 : g ≤ g') (h4 : k ≤ k') (h5 : mx ≤ mx')
    (h6 : my ≤ my') (h7 : Z ≤ Z') (h8 : BgP ≤ BgP') (h9 : Bmem ≤ Bmem') (h10 : Bk ≤ Bk')
    (h11 : Bl ≤ Bl') (h12 : Bg1 ≤ Bg1') (h13 : Bgen ≤ Bgen') (h14 : Cb ≤ Cb') (s0 : N - n ≤ N' - n')
    (x0 : 1 ≤ my') (x1 : 1 ≤ mx') (x2 : 1 ≤ k') :
    GraphIso.Main.c3CJCost n N s g k mx my Z BgP Bmem Bk Bl Bg1 Bgen Cb ≤
      GraphIso.Main.c3CJCost n' N' s' g' k' mx' my' Z' BgP' Bmem' Bk' Bl' Bg1' Bgen' Cb' := by
  unfold GraphIso.Main.c3CJCost
  gcongr

@[gcongr only] theorem CostMono.Main_c3ColWork
    {N N' n n' s s' k k' mx mx' Bstab Bstab'' Btr Btr' Borb Borb'' Bgen' Bgen'' Borb' : ℕ}
    {Borb''' Bstab' Bstab''' Bgk Bgk' Bl Bl' Bgs Bgs' wl wl' : ℕ} (h0 : N ≤ N') (h1 : n ≤ n')
    (h2 : s ≤ s') (h3 : k ≤ k') (h4 : mx ≤ mx') (h5 : Bstab ≤ Bstab'') (h6 : Btr ≤ Btr')
    (h7 : Borb ≤ Borb'') (h8 : Bgen' ≤ Bgen'') (h9 : Borb' ≤ Borb''') (h10 : Bstab' ≤ Bstab''')
    (h11 : Bgk ≤ Bgk') (h12 : Bl ≤ Bl') (h13 : Bgs ≤ Bgs') (h14 : wl ≤ wl') (x0 : N - n ≤ N' - n')
    (x1 : 1 ≤ mx') :
    GraphIso.Main.c3ColWork N n s k mx Bstab Btr Borb Bgen' Borb' Bstab' Bgk Bl Bgs wl ≤
      GraphIso.Main.c3ColWork N' n' s' k' mx' Bstab'' Btr' Borb'' Bgen'' Borb''' Bstab''' Bgk' Bl'
        Bgs' wl' := by
  unfold GraphIso.Main.c3ColWork
  gcongr

@[gcongr only] theorem CostMono.Main_c3PreWork
    {N N' n n' s s' k k' mx mx' my my' Bstab Bstab'' Btr Btr' Borb Borb'' Bgen' Bgen'' : ℕ}
    {Borb' Borb''' Bstab' Bstab''' Bgk Bgk' Bl Bl' Bgs Bgs' wl wl' Z Z' : ℕ} (h0 : N ≤ N')
    (h1 : n ≤ n') (h2 : s ≤ s') (h3 : k ≤ k') (h4 : mx ≤ mx') (h5 : my ≤ my') (h6 : Bstab ≤ Bstab'')
    (h7 : Btr ≤ Btr') (h8 : Borb ≤ Borb'') (h9 : Bgen' ≤ Bgen'') (h10 : Borb' ≤ Borb''')
    (h11 : Bstab' ≤ Bstab''') (h12 : Bgk ≤ Bgk') (h13 : Bl ≤ Bl') (h14 : Bgs ≤ Bgs')
    (h15 : wl ≤ wl') (h16 : Z ≤ Z') (s0 : N - n ≤ N' - n') (x0 : 1 ≤ mx') (x1 : 1 ≤ k') :
    GraphIso.Main.c3PreWork N n s k mx my Bstab Btr Borb Bgen' Borb' Bstab' Bgk Bl Bgs wl Z ≤
      GraphIso.Main.c3PreWork N' n' s' k' mx' my' Bstab'' Btr' Borb'' Bgen'' Borb''' Bstab''' Bgk'
        Bl' Bgs' wl' Z' := by
  unfold GraphIso.Main.c3PreWork
  gcongr

@[gcongr only] theorem CostMono.Main_c3Work
    {n n' N N' s s' g g' k k' mx mx' my my' Z Z' BgP BgP' Bmem Bmem' Bker Bker' Bl Bl' Bg1 : ℕ}
    {Bg1' Bgen Bgen'' Bstab Bstab'' Btr Btr' Borb Borb'' Bgen' Bgen''' Borb' Borb''' Bstab' : ℕ}
    {Bstab''' Bgk Bgk' Bgs Bgs' wl wl' Wb Wb' : ℕ} (h0 : n ≤ n') (h1 : N ≤ N') (h2 : s ≤ s')
    (h3 : g ≤ g') (h4 : k ≤ k') (h5 : mx ≤ mx') (h6 : my ≤ my') (h7 : Z ≤ Z') (h8 : BgP ≤ BgP')
    (h9 : Bmem ≤ Bmem') (h10 : Bker ≤ Bker') (h11 : Bl ≤ Bl') (h12 : Bg1 ≤ Bg1')
    (h13 : Bgen ≤ Bgen'') (h14 : Bstab ≤ Bstab'') (h15 : Btr ≤ Btr') (h16 : Borb ≤ Borb'')
    (h17 : Bgen' ≤ Bgen''') (h18 : Borb' ≤ Borb''') (h19 : Bstab' ≤ Bstab''') (h20 : Bgk ≤ Bgk')
    (h21 : Bgs ≤ Bgs') (h22 : wl ≤ wl') (h23 : Wb ≤ Wb') (x0 : N - n ≤ N' - n') (x1 : 1 ≤ mx')
    (x2 : 1 ≤ my') (x3 : 1 ≤ k') :
    GraphIso.Main.c3Work n N s g k mx my Z BgP Bmem Bker Bl Bg1 Bgen Bstab Btr Borb Bgen' Borb'
        Bstab' Bgk Bgs wl Wb ≤
      GraphIso.Main.c3Work n' N' s' g' k' mx' my' Z' BgP' Bmem' Bker' Bl' Bg1' Bgen'' Bstab'' Btr'
        Borb'' Bgen''' Borb''' Bstab''' Bgk' Bgs' wl' Wb' := by
  unfold GraphIso.Main.c3Work
  gcongr

@[gcongr only] theorem CostMono.Main_certCount {N N' n n' k k' : ℕ} (h1 : n ≤ n') (h2 : k ≤ k')
    (x0 : (N - n).choose k ≤ (N' - n').choose k') :
    GraphIso.Main.certCount N n k ≤
      GraphIso.Main.certCount N' n' k' := by
  unfold GraphIso.Main.certCount
  gcongr

@[gcongr only] theorem CostMono.Main_certWork
    {N N' n n' k k' s s' Bstab Bstab'' Btr Btr' Borb Borb'' Bgen' Bgen'' Borb' Borb''' : ℕ}
    {Bstab' Bstab''' Bgen Bgen''' Bl Bl' Bgs Bgs' BF BF' : ℕ} (h0 : N ≤ N') (h1 : n ≤ n')
    (h2 : k ≤ k') (h3 : s ≤ s') (h4 : Bstab ≤ Bstab'') (h5 : Btr ≤ Btr') (h6 : Borb ≤ Borb'')
    (h7 : Bgen' ≤ Bgen'') (h8 : Borb' ≤ Borb''') (h9 : Bstab' ≤ Bstab''') (h10 : Bgen ≤ Bgen''')
    (h11 : Bl ≤ Bl') (h12 : Bgs ≤ Bgs') (h13 : BF ≤ BF') (s0 : N - n ≤ N' - n')
    (x0 : (N - n).choose k ≤ (N' - n').choose k') :
    GraphIso.Main.certWork N n k s Bstab Btr Borb Bgen' Borb' Bstab' Bgen Bl Bgs BF ≤
      GraphIso.Main.certWork N' n' k' s' Bstab'' Btr' Borb'' Bgen'' Borb''' Bstab''' Bgen''' Bl'
        Bgs' BF' := by
  unfold GraphIso.Main.certWork
  gcongr

@[gcongr only] theorem CostMono.Main_cjB {m m' : ℕ} (h0 : m ≤ m') :
    GraphIso.Main.cjB m ≤
      GraphIso.Main.cjB m' := by
  unfold GraphIso.Main.cjB
  gcongr

@[gcongr only] theorem CostMono.Main_jfallbackCost {N N' u u' Bt Bt' Bs Bs' : ℕ} (h0 : N ≤ N')
    (h1 : u ≤ u') (h2 : Bt ≤ Bt') (h3 : Bs ≤ Bs') :
    GraphIso.Main.jfallbackCost N u Bt Bs ≤
      GraphIso.Main.jfallbackCost N' u' Bt' Bs' := by
  unfold GraphIso.Main.jfallbackCost
  gcongr

@[gcongr only] theorem CostMono.Main_interOCost {m m' Lb Lb' : ℕ} (h0 : m ≤ m') (h1 : Lb ≤ Lb') :
    GraphIso.Main.interOCost m Lb ≤
      GraphIso.Main.interOCost m' Lb' := by
  unfold GraphIso.Main.interOCost
  gcongr

@[gcongr only] theorem CostMono.SoJTree_setEqCost {m m' L L' : ℕ} (h0 : m ≤ m') (h1 : L ≤ L') :
    GraphIso.SoJTree.setEqCost m L ≤
      GraphIso.SoJTree.setEqCost m' L' := by
  unfold GraphIso.SoJTree.setEqCost
  gcongr

@[gcongr only] theorem CostMono.Main_ncPairCost {m m' Lb Lb' : ℕ} (h0 : m ≤ m') (h1 : Lb ≤ Lb') :
    GraphIso.Main.ncPairCost m Lb ≤
      GraphIso.Main.ncPairCost m' Lb' := by
  unfold GraphIso.Main.ncPairCost
  gcongr

@[gcongr only] theorem CostMono.Main_ncCost {p p' m m' Lb Lb' : ℕ} (h0 : p ≤ p') (h1 : m ≤ m')
    (h2 : Lb ≤ Lb') :
    GraphIso.Main.ncCost p m Lb ≤
      GraphIso.Main.ncCost p' m' Lb' := by
  unfold GraphIso.Main.ncCost
  gcongr

@[gcongr only] theorem CostMono.Main_ncBCost {n n' N N' p p' Lb Lb' : ℕ} (h1 : N ≤ N') (h2 : p ≤ p')
    (h3 : Lb ≤ Lb') (s0 : N - n ≤ N' - n') :
    GraphIso.Main.ncBCost n N p Lb ≤
      GraphIso.Main.ncBCost n' N' p' Lb' := by
  unfold GraphIso.Main.ncBCost
  gcongr

@[gcongr only] theorem CostMono.Toolkit_jUnionCost {nc nc' t t' s s' : ℕ} (h0 : nc ≤ nc')
    (h1 : t ≤ t') (h2 : s ≤ s') :
    GraphIso.Toolkit.jUnionCost nc t s ≤
      GraphIso.Toolkit.jUnionCost nc' t' s' := by
  unfold GraphIso.Toolkit.jUnionCost
  gcongr

@[gcongr only] theorem CostMono.Main_johnStepCost
    {n n' N N' p p' Ls Ls' s s' uB uB' Bt Bt' Bs Bs' Bgen₄ Bgen₄' : ℕ} (h0 : n ≤ n') (h1 : N ≤ N')
    (h2 : p ≤ p') (h3 : Ls ≤ Ls') (h4 : s ≤ s') (h5 : uB ≤ uB') (h6 : Bt ≤ Bt') (h7 : Bs ≤ Bs')
    (h8 : Bgen₄ ≤ Bgen₄') (s0 : N - n ≤ N' - n') :
    GraphIso.Main.johnStepCost n N p Ls s uB Bt Bs Bgen₄ ≤
      GraphIso.Main.johnStepCost n' N' p' Ls' s' uB' Bt' Bs' Bgen₄' := by
  unfold GraphIso.Main.johnStepCost
  gcongr

@[gcongr only] theorem CostMono.Main_labM1Cost {n n' m m' Lb Lb' : ℕ} (h0 : n ≤ n') (h1 : m ≤ m')
    (h2 : Lb ≤ Lb') :
    GraphIso.Main.labM1Cost n m Lb ≤
      GraphIso.Main.labM1Cost n' m' Lb' := by
  unfold GraphIso.Main.labM1Cost
  gcongr

@[gcongr only] theorem CostMono.Main_pickCost {p p' m m' Lb Lb' : ℕ} (h0 : p ≤ p') (h1 : m ≤ m')
    (h2 : Lb ≤ Lb') :
    GraphIso.Main.pickCost p m Lb ≤
      GraphIso.Main.pickCost p' m' Lb' := by
  unfold GraphIso.Main.pickCost
  gcongr

@[gcongr only] theorem CostMono.Main_m1Cost {n n' N N' p p' s s' Borb Borb' Bgen Bgen' : ℕ}
    (h0 : n ≤ n') (h1 : N ≤ N') (h2 : p ≤ p') (h3 : s ≤ s') (h4 : Borb ≤ Borb') (h5 : Bgen ≤ Bgen')
    (s0 : N - n ≤ N' - n') :
    GraphIso.Main.m1Cost n N p s Borb Bgen ≤
      GraphIso.Main.m1Cost n' N' p' s' Borb' Bgen' := by
  unfold GraphIso.Main.m1Cost
  gcongr

@[gcongr only] theorem CostMono.Main_m1ContCost
    {n n' N N' p p' s s' Borb Borb' Bgen Bgen' s₁ s₁' sS sS' Lt Lt' sH sH' Bgen₂ Bgen₂' Bge : ℕ}
    {Bge' Bst Bst' Btr Btr' Bgt Bgt' Bgen₃ Bgen₃' : ℕ} (h0 : n ≤ n') (h1 : N ≤ N') (h2 : p ≤ p')
    (h3 : s ≤ s') (h4 : Borb ≤ Borb') (h5 : Bgen ≤ Bgen') (h6 : s₁ ≤ s₁') (h7 : sS ≤ sS')
    (h8 : Lt ≤ Lt') (h9 : sH ≤ sH') (h10 : Bgen₂ ≤ Bgen₂') (h11 : Bge ≤ Bge') (h12 : Bst ≤ Bst')
    (h13 : Btr ≤ Btr') (h14 : Bgt ≤ Bgt') (h15 : Bgen₃ ≤ Bgen₃') (x0 : N - n ≤ N' - n') :
    GraphIso.Main.m1ContCost n N p s Borb Bgen s₁ sS Lt sH Bgen₂ Bge Bst Btr Bgt Bgen₃ ≤
      GraphIso.Main.m1ContCost n' N' p' s' Borb' Bgen' s₁' sS' Lt' sH' Bgen₂' Bge' Bst' Btr' Bgt'
        Bgen₃' := by
  unfold GraphIso.Main.m1ContCost
  gcongr

@[gcongr only] theorem CostMono.Main_deriveCJCost
    {n n' N N' p p' Ls Ls' s s' Borb Borb' Bgen Bgen' s₁ s₁' sS sS' Lt Lt' sH sH' Bgen₂ : ℕ}
    {Bgen₂' Bge Bge' Bst Bst' Btr Btr' Bgt Bgt' Bgen₃ Bgen₃' Bgen₄ Bgen₄' uB uB' Bt Bt' Bs : ℕ}
    {Bs' : ℕ} (h0 : n ≤ n') (h1 : N ≤ N') (h2 : p ≤ p') (h3 : Ls ≤ Ls') (h4 : s ≤ s')
    (h5 : Borb ≤ Borb') (h6 : Bgen ≤ Bgen') (h7 : s₁ ≤ s₁') (h8 : sS ≤ sS') (h9 : Lt ≤ Lt')
    (h10 : sH ≤ sH') (h11 : Bgen₂ ≤ Bgen₂') (h12 : Bge ≤ Bge') (h13 : Bst ≤ Bst') (h14 : Btr ≤ Btr')
    (h15 : Bgt ≤ Bgt') (h16 : Bgen₃ ≤ Bgen₃') (h17 : Bgen₄ ≤ Bgen₄') (h18 : uB ≤ uB')
    (h19 : Bt ≤ Bt') (h20 : Bs ≤ Bs') (s0 : N - n ≤ N' - n') :
    GraphIso.Main.deriveCJCost n N p Ls s Borb Bgen s₁ sS Lt sH Bgen₂ Bge Bst Btr Bgt Bgen₃ Bgen₄ uB
        Bt Bs ≤
      GraphIso.Main.deriveCJCost n' N' p' Ls' s' Borb' Bgen' s₁' sS' Lt' sH' Bgen₂' Bge' Bst' Btr'
        Bgt' Bgen₃' Bgen₄' uB' Bt' Bs' := by
  unfold GraphIso.Main.deriveCJCost
  gcongr

@[gcongr only] theorem CostMono.Main_deriveFreeCost
    {n n' N N' p p' s s' Borb Borb' Bgen Bgen' s₁ s₁' sS sS' Lt Lt' sH sH' Bgen₂ Bgen₂' Bge : ℕ}
    {Bge' Bst Bst' Btr Btr' Bgt Bgt' Bgen₃ Bgen₃' : ℕ} (h0 : n ≤ n') (h1 : N ≤ N') (h2 : p ≤ p')
    (h3 : s ≤ s') (h4 : Borb ≤ Borb') (h5 : Bgen ≤ Bgen') (h6 : s₁ ≤ s₁') (h7 : sS ≤ sS')
    (h8 : Lt ≤ Lt') (h9 : sH ≤ sH') (h10 : Bgen₂ ≤ Bgen₂') (h11 : Bge ≤ Bge') (h12 : Bst ≤ Bst')
    (h13 : Btr ≤ Btr') (h14 : Bgt ≤ Bgt') (h15 : Bgen₃ ≤ Bgen₃') (s0 : N - n ≤ N' - n') :
    GraphIso.Main.deriveFreeCost n N p s Borb Bgen s₁ sS Lt sH Bgen₂ Bge Bst Btr Bgt Bgen₃ ≤
      GraphIso.Main.deriveFreeCost n' N' p' s' Borb' Bgen' s₁' sS' Lt' sH' Bgen₂' Bge' Bst' Btr'
        Bgt' Bgen₃' := by
  unfold GraphIso.Main.deriveFreeCost
  gcongr

@[gcongr only] theorem CostMono.Main_dynStepCost {N N' p p' Bo Bo' : ℕ} (h0 : N ≤ N') (h1 : p ≤ p')
    (h2 : Bo ≤ Bo') :
    GraphIso.Main.dynStepCost N p Bo ≤
      GraphIso.Main.dynStepCost N' p' Bo' := by
  unfold GraphIso.Main.dynStepCost
  gcongr

@[gcongr only] theorem CostMono.Main_dynSeqCost {N N' p p' Bo Bo' : ℕ} (h0 : N ≤ N') (h1 : p ≤ p')
    (h2 : Bo ≤ Bo') :
    GraphIso.Main.dynSeqCost N p Bo ≤
      GraphIso.Main.dynSeqCost N' p' Bo' := by
  unfold GraphIso.Main.dynSeqCost
  gcongr

@[gcongr only] theorem CostMono.Main_fixPtsCost {m m' : ℕ} (h0 : m ≤ m') :
    GraphIso.Main.fixPtsCost m ≤
      GraphIso.Main.fixPtsCost m' := by
  unfold GraphIso.Main.fixPtsCost
  gcongr

@[gcongr only] theorem CostMono.Main_mlHandleCost {n n' N' N'' p p' : ℕ} (h1 : N' ≤ N'')
    (h2 : p ≤ p') (s0 : N' - n ≤ N'' - n') :
    GraphIso.Main.mlHandleCost n N' p ≤
      GraphIso.Main.mlHandleCost n' N'' p' := by
  unfold GraphIso.Main.mlHandleCost
  gcongr

@[gcongr only] theorem CostMono.Main_transferCost
    {N N'' N' N''' n n' s s' Blift Blift' Bgen Bgen' : ℕ} (h0 : N ≤ N'') (h1 : N' ≤ N''')
    (h2 : n ≤ n') (h3 : s ≤ s') (h4 : Blift ≤ Blift') (h5 : Bgen ≤ Bgen') :
    GraphIso.Main.transferCost N N' n s Blift Bgen ≤
      GraphIso.Main.transferCost N'' N''' n' s' Blift' Bgen' := by
  unfold GraphIso.Main.transferCost
  gcongr

@[gcongr only] theorem CostMono.Main_viaChildCost
    {N N'' N' N''' n n' s s' Blift Blift' Bgen Bgen' : ℕ} (h0 : N ≤ N'') (h1 : N' ≤ N''')
    (h2 : n ≤ n') (h3 : s ≤ s') (h4 : Blift ≤ Blift') (h5 : Bgen ≤ Bgen') :
    GraphIso.Main.viaChildCost N N' n s Blift Bgen ≤
      GraphIso.Main.viaChildCost N'' N''' n' s' Blift' Bgen' := by
  unfold GraphIso.Main.viaChildCost
  gcongr

@[gcongr only] theorem CostMono.Main_mlBranchCost
    {N₁ N₁' N' N'' n n' p p' sIn sIn' Blift Blift' Bgen Bgen' Bo Bo' : ℕ} (h0 : N₁ ≤ N₁')
    (h1 : N' ≤ N'') (h2 : n ≤ n') (h3 : p ≤ p') (h4 : sIn ≤ sIn') (h5 : Blift ≤ Blift')
    (h6 : Bgen ≤ Bgen') (h7 : Bo ≤ Bo') (x0 : N' - n ≤ N'' - n') :
    GraphIso.Main.mlBranchCost N₁ N' n p sIn Blift Bgen Bo ≤
      GraphIso.Main.mlBranchCost N₁' N'' n' p' sIn' Blift' Bgen' Bo' := by
  unfold GraphIso.Main.mlBranchCost
  gcongr

@[gcongr only] theorem CostMono.Main_m2bLoopCost
    {N₁ N₁' N' N'' n n' p p' r r' sIn sIn' sR sR' Blift Blift' Bgen Bgen' Bo Bo' Bgen₂ : ℕ}
    {Bgen₂' : ℕ} (h0 : N₁ ≤ N₁') (h1 : N' ≤ N'') (h2 : n ≤ n') (h3 : p ≤ p') (h4 : r ≤ r')
    (h5 : sIn ≤ sIn') (h6 : sR ≤ sR') (h7 : Blift ≤ Blift') (h8 : Bgen ≤ Bgen') (h9 : Bo ≤ Bo')
    (h10 : Bgen₂ ≤ Bgen₂') (x0 : N' - n ≤ N'' - n') :
    GraphIso.Main.m2bLoopCost N₁ N' n p r sIn sR Blift Bgen Bo Bgen₂ ≤
      GraphIso.Main.m2bLoopCost N₁' N'' n' p' r' sIn' sR' Blift' Bgen' Bo' Bgen₂' := by
  unfold GraphIso.Main.m2bLoopCost
  gcongr

@[gcongr only] theorem CostMono.Main_msCount {k k' : ℕ} (h0 : k ≤ k') :
    GraphIso.Main.msCount k ≤
      GraphIso.Main.msCount k' := by
  unfold GraphIso.Main.msCount
  gcongr

@[gcongr only] theorem CostMono.Main_m4R {m m' j j' : ℕ} (h0 : m ≤ m') (h1 : j ≤ j')
    (s0 : m - j ≤ m' - j') (x0 : 1 ≤ m') :
    GraphIso.Main.m4R m j ≤
      GraphIso.Main.m4R m' j' := by
  unfold GraphIso.Main.m4R
  gcongr

@[gcongr only] theorem CostMono.Main_m4StructCost
    {N N' k k' s s' Btr Btr'' Bstab Bstab' Borb Borb' sS sS' L L' Bge Bge' Bst Bst' Btr' : ℕ}
    {Btr''' Bgt Bgt' : ℕ} (h0 : N ≤ N') (h1 : k ≤ k') (h2 : s ≤ s') (h3 : Btr ≤ Btr'')
    (h4 : Bstab ≤ Bstab') (h5 : Borb ≤ Borb') (h6 : sS ≤ sS') (h7 : L ≤ L') (h8 : Bge ≤ Bge')
    (h9 : Bst ≤ Bst') (h10 : Btr' ≤ Btr''') (h11 : Bgt ≤ Bgt') :
    GraphIso.Main.m4StructCost N k s Btr Bstab Borb sS L Bge Bst Btr' Bgt ≤
      GraphIso.Main.m4StructCost N' k' s' Btr'' Bstab' Borb' sS' L' Bge' Bst' Btr''' Bgt' := by
  unfold GraphIso.Main.m4StructCost
  have e := Nat.pow_le_pow_left (show N + k + s + GraphIso.Main.msCount k +
      GraphIso.SoJTree.outB k ((k + 3) / 2) + 2 ≤ N' + k' + s' + GraphIso.Main.msCount k' +
      GraphIso.SoJTree.outB k' ((k' + 3) / 2) + 2 by gcongr) 8
  gcongr

@[gcongr only] theorem CostMono.Main_prodRepsLCost {N N' a a' b b' : ℕ} (h0 : N ≤ N') (h1 : a ≤ a')
    (h2 : b ≤ b') :
    GraphIso.Main.prodRepsLCost N a b ≤
      GraphIso.Main.prodRepsLCost N' a' b' := by
  unfold GraphIso.Main.prodRepsLCost
  gcongr

@[gcongr only] theorem CostMono.Main_rdCost {N N' p p' r r' sIn sIn' Wh Wh' Bo Bo' Bgen Bgen' : ℕ}
    (h0 : N ≤ N') (h1 : p ≤ p') (h2 : r ≤ r') (h3 : sIn ≤ sIn') (h4 : Wh ≤ Wh') (h5 : Bo ≤ Bo')
    (h6 : Bgen ≤ Bgen') :
    GraphIso.Main.rdCost N p r sIn Wh Bo Bgen ≤
      GraphIso.Main.rdCost N' p' r' sIn' Wh' Bo' Bgen' := by
  unfold GraphIso.Main.rdCost
  gcongr

@[gcongr only] theorem CostMono.Toolkit_pointStabsCost {N N' m m' Bt Bt' Bs Bs' r r' : ℕ}
    (h0 : N ≤ N') (h1 : m ≤ m') (h2 : Bt ≤ Bt') (h3 : Bs ≤ Bs') (h4 : r ≤ r') :
    GraphIso.Toolkit.pointStabsCost N m Bt Bs r ≤
      GraphIso.Toolkit.pointStabsCost N' m' Bt' Bs' r' := by
  unfold GraphIso.Toolkit.pointStabsCost
  gcongr

@[gcongr only] theorem CostMono.Main_m4StepCost
    {N N' m m' j j' s s' Borb Borb' Bstab Bstab' Btr Btr'' sS sS' L L' Bge Bge' Bst Bst' : ℕ}
    {Btr' Btr''' Bgt Bgt' p p' sIn sIn' Wh Wh' Bo Bo' Bgen Bgen' : ℕ} (h0 : N ≤ N') (h1 : m ≤ m')
    (h2 : j ≤ j') (h3 : s ≤ s') (h4 : Borb ≤ Borb') (h5 : Bstab ≤ Bstab') (h6 : Btr ≤ Btr'')
    (h7 : sS ≤ sS') (h8 : L ≤ L') (h9 : Bge ≤ Bge') (h10 : Bst ≤ Bst') (h11 : Btr' ≤ Btr''')
    (h12 : Bgt ≤ Bgt') (h13 : p ≤ p') (h14 : sIn ≤ sIn') (h15 : Wh ≤ Wh') (h16 : Bo ≤ Bo')
    (h17 : Bgen ≤ Bgen') (s0 : m - j ≤ m' - j') (x0 : 1 ≤ m') :
    GraphIso.Main.m4StepCost N m j s Borb Bstab Btr sS L Bge Bst Btr' Bgt p sIn Wh Bo Bgen ≤
      GraphIso.Main.m4StepCost N' m' j' s' Borb' Bstab' Btr'' sS' L' Bge' Bst' Btr''' Bgt' p' sIn'
        Wh' Bo' Bgen' := by
  unfold GraphIso.Main.m4StepCost
  gcongr

@[gcongr only] theorem CostMono.Sims_initCost {n n' L L' : ℕ} (h0 : n ≤ n') (h1 : L ≤ L') :
    GraphIso.Sims.initCost n L ≤
      GraphIso.Sims.initCost n' L' := by
  unfold GraphIso.Sims.initCost
  gcongr

@[gcongr only] theorem CostMono.Sims_siftCost {n n' : ℕ} (h0 : n ≤ n') :
    GraphIso.Sims.siftCost n ≤
      GraphIso.Sims.siftCost n' := by
  unfold GraphIso.Sims.siftCost
  gcongr

@[gcongr only] theorem CostMono.Sims_itemCost {n n' : ℕ} (h0 : n ≤ n') :
    GraphIso.Sims.itemCost n ≤
      GraphIso.Sims.itemCost n' := by
  unfold GraphIso.Sims.itemCost
  gcongr

@[gcongr only] theorem CostMono.Sims_insCost {n n' : ℕ} (h0 : n ≤ n') :
    GraphIso.Sims.insCost n ≤
      GraphIso.Sims.insCost n' := by
  unfold GraphIso.Sims.insCost
  gcongr

@[gcongr only] theorem CostMono.Sims_slotCost {n n' : ℕ} (h0 : n ≤ n') :
    GraphIso.Sims.slotCost n ≤
      GraphIso.Sims.slotCost n' := by
  unfold GraphIso.Sims.slotCost
  gcongr

@[gcongr only] theorem CostMono.Sims_buildCost {n n' L L' : ℕ} (h0 : n ≤ n') (h1 : L ≤ L') :
    GraphIso.Sims.buildCost n L ≤
      GraphIso.Sims.buildCost n' L' := by
  unfold GraphIso.Sims.buildCost
  gcongr

@[gcongr only] theorem CostMono.Sims_genCost {n n' L L' : ℕ} (h0 : n ≤ n') (h1 : L ≤ L') :
    GraphIso.Sims.genCost n L ≤
      GraphIso.Sims.genCost n' L' := by
  unfold GraphIso.Sims.genCost
  gcongr

@[gcongr only] theorem CostMono.Sims_transCost {n n' L L' : ℕ} (h0 : n ≤ n') (h1 : L ≤ L') :
    GraphIso.Sims.transCost n L ≤
      GraphIso.Sims.transCost n' L' := by
  unfold GraphIso.Sims.transCost
  gcongr

@[gcongr only] theorem CostMono.Sims_orbitsCost {n n' L L' m m' : ℕ} (h0 : n ≤ n') (h1 : L ≤ L')
    (h2 : m ≤ m') :
    GraphIso.Sims.orbitsCost n L m ≤
      GraphIso.Sims.orbitsCost n' L' m' := by
  unfold GraphIso.Sims.orbitsCost
  gcongr

@[gcongr only] theorem CostMono.Sims_stabCost {n n' L L' : ℕ} (h0 : n ≤ n') (h1 : L ≤ L') :
    GraphIso.Sims.stabCost n L ≤
      GraphIso.Sims.stabCost n' L' := by
  unfold GraphIso.Sims.stabCost
  gcongr

@[gcongr only] theorem CostMono.Main_m4CostSS {n n' m m' j j' p p' sIn sIn' Lg Lg' Wh Wh' : ℕ}
    (h0 : n ≤ n') (h1 : m ≤ m') (h2 : j ≤ j') (h3 : p ≤ p') (h4 : sIn ≤ sIn') (h5 : Lg ≤ Lg')
    (h6 : Wh ≤ Wh') (s0 : m - j ≤ m' - j') (x0 : 1 ≤ m') :
    GraphIso.Main.m4CostSS n m j p sIn Lg Wh ≤
      GraphIso.Main.m4CostSS n' m' j' p' sIn' Lg' Wh' := by
  unfold GraphIso.Main.m4CostSS
  gcongr

@[gcongr only] theorem CostMono.Main_rd5Cost {N N' p p' F F' sIn sIn' Bo Bo' Bgen Bgen' : ℕ}
    (h0 : N ≤ N') (h1 : p ≤ p') (h2 : F ≤ F') (h3 : sIn ≤ sIn') (h4 : Bo ≤ Bo') (h5 : Bgen ≤ Bgen')
    :
    GraphIso.Main.rd5Cost N p F sIn Bo Bgen ≤
      GraphIso.Main.rd5Cost N' p' F' sIn' Bo' Bgen' := by
  unfold GraphIso.Main.rd5Cost
  gcongr

@[gcongr only] theorem CostMono.Main_rdOrbitWork
    {N N' n n' p p' s s' sIn sIn' F F' Bd Bd' Blift Blift' Bgen Bgen' Bo Bo' W6 W6' : ℕ}
    (h0 : N ≤ N') (h1 : n ≤ n') (h2 : p ≤ p') (h3 : s ≤ s') (h4 : sIn ≤ sIn') (h5 : F ≤ F')
    (h6 : Bd ≤ Bd') (h7 : Blift ≤ Blift') (h8 : Bgen ≤ Bgen') (h9 : Bo ≤ Bo') (h10 : W6 ≤ W6')
    (s0 : N - n ≤ N' - n') :
    GraphIso.Main.rdOrbitWork N n p s sIn F Bd Blift Bgen Bo W6 ≤
      GraphIso.Main.rdOrbitWork N' n' p' s' sIn' F' Bd' Blift' Bgen' Bo' W6' := by
  unfold GraphIso.Main.rdOrbitWork
  gcongr

@[gcongr only] theorem CostMono.Main_ssBdF {n n' N N' p p' S S' : ℕ} (h0 : n ≤ n') (h1 : N ≤ N')
    (h2 : p ≤ p') (h3 : S ≤ S') (s0 : N - n ≤ N' - n') :
    GraphIso.Main.ssBdF n N p S ≤
      GraphIso.Main.ssBdF n' N' p' S' := by
  unfold GraphIso.Main.ssBdF
  gcongr

@[gcongr only] theorem CostMono.Main_ssBdJU {n n' N N' p p' Ls Ls' S S' u u' : ℕ} (h0 : n ≤ n')
    (h1 : N ≤ N') (h2 : p ≤ p') (h3 : Ls ≤ Ls') (h4 : S ≤ S') (h5 : u ≤ u') (s0 : N - n ≤ N' - n') :
    GraphIso.Main.ssBdJU n N p Ls S u ≤
      GraphIso.Main.ssBdJU n' N' p' Ls' S' u' := by
  unfold GraphIso.Main.ssBdJU
  gcongr

@[gcongr only] theorem CostMono.Sims_liftCost {n n' L L' m m' : ℕ} (h0 : n ≤ n') (h1 : L ≤ L')
    (h2 : m ≤ m') :
    GraphIso.Sims.liftCost n L m ≤
      GraphIso.Sims.liftCost n' L' m' := by
  unfold GraphIso.Sims.liftCost
  gcongr

@[gcongr only] theorem CostMono.Main_m4WhUSS
    {n n' m m' p p' s s' Ls Ls' sIn sIn' Lg Lg' F F' W6 W6' u u' : ℕ} (h0 : n ≤ n') (h1 : m ≤ m')
    (h2 : p ≤ p') (h3 : s ≤ s') (h4 : Ls ≤ Ls') (h5 : sIn ≤ sIn') (h6 : Lg ≤ Lg') (h7 : F ≤ F')
    (h8 : W6 ≤ W6') (h9 : u ≤ u') (x0 : n + m - n ≤ n' + m' - n') :
    GraphIso.Main.m4WhUSS n m p s Ls sIn Lg F W6 u ≤
      GraphIso.Main.m4WhUSS n' m' p' s' Ls' sIn' Lg' F' W6' u' := by
  unfold GraphIso.Main.m4WhUSS
  gcongr

@[gcongr only] theorem CostMono.Main_m5CaseCost {n n' N N' Borb Borb' ldeg ldeg' : ℕ} (h1 : N ≤ N')
    (h2 : Borb ≤ Borb') (h3 : ldeg ≤ ldeg') (s0 : N - n ≤ N' - n') :
    GraphIso.Main.m5CaseCost n N Borb ldeg ≤
      GraphIso.Main.m5CaseCost n' N' Borb' ldeg' := by
  unfold GraphIso.Main.m5CaseCost
  gcongr

@[gcongr only] theorem CostMono.Main_m5Wb
    {N N' n n' wl wl' s s' sIn sIn' F F' Bd Bd' Blift Blift' Bgen Bgen' Bo Bo' W6 W6' : ℕ}
    (h0 : N ≤ N') (h1 : n ≤ n') (h2 : wl ≤ wl') (h3 : s ≤ s') (h4 : sIn ≤ sIn') (h5 : F ≤ F')
    (h6 : Bd ≤ Bd') (h7 : Blift ≤ Blift') (h8 : Bgen ≤ Bgen') (h9 : Bo ≤ Bo') (h10 : W6 ≤ W6')
    (x0 : N - n ≤ N' - n') :
    GraphIso.Main.m5Wb N n wl s sIn F Bd Blift Bgen Bo W6 ≤
      GraphIso.Main.m5Wb N' n' wl' s' sIn' F' Bd' Blift' Bgen' Bo' W6' := by
  unfold GraphIso.Main.m5Wb
  gcongr

@[gcongr only] theorem CostMono.Main_m5DispNumNs
    {n n' N N' k k' s s' sIn sIn' Bgen Bgen' Blift Blift' Bo Bo'' Bd Bd' wl wl' : ℕ}
    {β β' : GraphIso.Main.M5Bounds} {Bst Bst' Btr Btr' Borb Borb' Bkg Bkg' Bko Bko' Bks Bks' : ℕ}
    {Bo' : ℕ → ℕ} {Bs' : ℕ → ℕ} {Bt' : ℕ → ℕ}
    {uB uB' Bg1J₂ Bg1J₂' Bg1J₃ Bg1J₃' g g' P₁ P₁' P₂ P₂' nΦ nΦ' mx mx' my my' nx nx' ny ny' : ℕ}
    {j j' cl cl' ol ol' : ℕ} (h0 : n ≤ n') (h1 : N ≤ N') (h2 : k ≤ k') (h3 : s ≤ s')
    (h4 : sIn ≤ sIn') (h5 : Bgen ≤ Bgen') (h6 : Blift ≤ Blift') (h7 : Bo ≤ Bo'') (h8 : Bd ≤ Bd')
    (h9 : wl ≤ wl') (b_Bg : β.Bg ≤ β'.Bg) (b_Bg1₁ : β.Bg1₁ ≤ β'.Bg1₁) (b_Bg1₂ᵦ : β.Bg1₂ᵦ ≤ β'.Bg1₂ᵦ)
    (b_Bg1₂ₐ : β.Bg1₂ₐ ≤ β'.Bg1₂ₐ) (b_Bg1₃ : β.Bg1₃ ≤ β'.Bg1₃) (b_BgP : β.BgP ≤ β'.BgP)
    (b_Bgen₂ᵦ : β.Bgen₂ᵦ ≤ β'.Bgen₂ᵦ) (b_Bgen₂ₐ : β.Bgen₂ₐ ≤ β'.Bgen₂ₐ)
    (b_Bgen₃ : β.Bgen₃ ≤ β'.Bgen₃) (b_Bgk : β.Bgk ≤ β'.Bgk) (b_Bgm : β.Bgm ≤ β'.Bgm)
    (b_Bgn : β.Bgn ≤ β'.Bgn) (b_Bgs : β.Bgs ≤ β'.Bgs) (b_BkA : β.BkA ≤ β'.BkA)
    (b_Bker : β.Bker ≤ β'.Bker) (b_BlA : β.BlA ≤ β'.BlA) (b_Blift : β.Blift ≤ β'.Blift)
    (b_Bmem : β.Bmem ≤ β'.Bmem) (b_Box : β.Box ≤ β'.Box) (b_Boy : β.Boy ≤ β'.Boy)
    (b_Bpb : β.Bpb ≤ β'.Bpb) (b_sK : β.sK ≤ β'.sK) (h11 : Bst ≤ Bst') (h12 : Btr ≤ Btr')
    (h13 : Borb ≤ Borb') (h14 : Bkg ≤ Bkg') (h15 : Bko ≤ Bko') (h16 : Bks ≤ Bks') (h20 : uB ≤ uB')
    (h21 : Bg1J₂ ≤ Bg1J₂') (h22 : Bg1J₃ ≤ Bg1J₃') (h23 : g ≤ g') (h24 : P₁ ≤ P₁') (h25 : P₂ ≤ P₂')
    (h26 : nΦ ≤ nΦ') (h27 : mx ≤ mx') (h28 : my ≤ my') (h29 : nx ≤ nx') (h30 : ny ≤ ny')
    (h31 : j ≤ j') (h32 : cl ≤ cl') (h33 : ol ≤ ol') (s0 : N - n ≤ N' - n') (x0 : 1 ≤ mx')
    (x1 : 1 ≤ my') (x2 : 1 ≤ k') (x3 : nx - j ≤ nx' - j') (x4 : Bo' nx ≤ Bo' nx')
    (x5 : Bs' nx ≤ Bs' nx') (x6 : 1 ≤ nx' - j') (x7 : Bt' (nx - j) ≤ Bt' (nx' - j'))
    (x8 : Bs' (nx - j) ≤ Bs' (nx' - j')) (x9 : Bo' (nx - j) ≤ Bo' (nx' - j'))
    (x10 : ny - j ≤ ny' - j') (x11 : Bo' ny ≤ Bo' ny') (x12 : Bs' ny ≤ Bs' ny') (x13 : 1 ≤ ny')
    (x14 : 1 ≤ ny' - j') (x15 : Bt' (ny - j) ≤ Bt' (ny' - j')) (x16 : Bs' (ny - j) ≤ Bs' (ny' - j'))
    (x17 : Bo' (ny - j) ≤ Bo' (ny' - j')) :
    GraphIso.Main.m5DispNumNs n N k s sIn Bgen Blift Bo Bd wl β Bst Btr Borb Bkg Bko Bks Bo' Bs' Bt'
        uB Bg1J₂ Bg1J₃ g P₁ P₂ nΦ mx my nx ny j cl ol ≤
      GraphIso.Main.m5DispNumNs n' N' k' s' sIn' Bgen' Blift' Bo'' Bd' wl' β' Bst' Btr' Borb' Bkg'
        Bko' Bks' Bo' Bs' Bt' uB' Bg1J₂' Bg1J₃' g' P₁' P₂' nΦ' mx' my' nx' ny' j' cl' ol' := by
  unfold GraphIso.Main.m5DispNumNs
  gcongr

@[gcongr only] theorem CostMono.Main_olB {m m' : ℕ} (h0 : m ≤ m') :
    GraphIso.Main.olB m ≤
      GraphIso.Main.olB m' := by
  unfold GraphIso.Main.olB
  gcongr

@[gcongr only] theorem CostMono.Main_ssBg1J {N N' m m' : ℕ} (h0 : N ≤ N') (h1 : m ≤ m') :
    GraphIso.Main.ssBg1J N m ≤
      GraphIso.Main.ssBg1J N' m' := by
  unfold GraphIso.Main.ssBg1J
  gcongr

@[gcongr only] theorem CostMono.Sims_kerCost {n n' L L' m m' : ℕ} (h0 : n ≤ n') (h1 : L ≤ L')
    (h2 : m ≤ m') :
    GraphIso.Sims.kerCost n L m ≤
      GraphIso.Sims.kerCost n' L' m' := by
  unfold GraphIso.Sims.kerCost
  gcongr

@[gcongr only] theorem CostMono.Sims_memCost {n n' L L' : ℕ} (h0 : n ≤ n') (h1 : L ≤ L') :
    GraphIso.Sims.memCost n L ≤
      GraphIso.Sims.memCost n' L' := by
  unfold GraphIso.Sims.memCost
  gcongr

@[gcongr only] theorem CostMono.Sims_repsVisitCost {n n' I I' : ℕ} (h0 : n ≤ n') (h1 : I ≤ I') :
    GraphIso.Sims.repsVisitCost n I ≤
      GraphIso.Sims.repsVisitCost n' I' := by
  unfold GraphIso.Sims.repsVisitCost
  gcongr

@[gcongr only] theorem CostMono.Sims_repsCost {n n' L L'' L' L''' I I' : ℕ} (h0 : n ≤ n')
    (h1 : L ≤ L'') (h2 : L' ≤ L''') (h3 : I ≤ I') :
    GraphIso.Sims.repsCost n L L' I ≤
      GraphIso.Sims.repsCost n' L'' L''' I' := by
  unfold GraphIso.Sims.repsCost
  gcongr

@[gcongr only] theorem CostMono.Toolkit_psStepCost {N N' m m' Bt Bt' Bs Bs' j j' : ℕ} (h0 : N ≤ N')
    (h1 : m ≤ m') (h2 : Bt ≤ Bt') (h3 : Bs ≤ Bs') (h4 : j ≤ j') (x0 : 1 ≤ m') :
    GraphIso.Toolkit.psStepCost N m Bt Bs j ≤
      GraphIso.Toolkit.psStepCost N' m' Bt' Bs' j' := by
  unfold GraphIso.Toolkit.psStepCost
  gcongr

/-! ### M4 -/

section M4

/-- **M4's work without stuck orbits at given sizes**: the function whose envelope is
`m4WorkNsLSS`. -/
def m4PtNsL (n m j p s Ls sIn Lg uB : ℕ) : ℕ :=
  m4CostSS n m j p sIn Lg (m4WhUSS n m p s Ls sIn Lg (max m uB.factorial) 0 uB)

/-- `m4PtNsL` is monotone in every size except `j`, for a base size `m' ≥ 1`. -/
theorem m4PtNsL_mono {n n' m m' j p p' s s' Ls Ls' sIn sIn' Lg Lg' uB uB' : ℕ} (hn : n ≤ n')
    (hm : m ≤ m') (hp : p ≤ p') (hs : s ≤ s') (hL : Ls ≤ Ls') (hI : sIn ≤ sIn') (hg : Lg ≤ Lg')
    (hu : uB ≤ uB') (hm1 : 1 ≤ m') :
    m4PtNsL n m j p s Ls sIn Lg uB ≤ m4PtNsL n' m' j p' s' Ls' sIn' Lg' uB' := by
  unfold m4PtNsL
  gcongr
  all_goals omega

/-- **M4's work without stuck orbits is at most its corner values**, maximized over the
individualization depth, for `m ≥ 1`. -/
theorem m4WorkNsLSS_le {n m j p s Ls sIn Lg uB : ℕ} (hm : 1 ≤ m) :
    m4WorkNsLSS n m j p s Ls sIn Lg uB ≤ supTo (fun j' => m4PtNsL n m j' p s Ls sIn Lg uB) j := by
  unfold m4WorkNsLSS
  refine envSup_le fun xs hxs => ?_
  obtain ⟨x₀, t₀, h₀, k₀, rfl⟩ := List.forall₂_cons_right_iff.1 hxs
  obtain ⟨x₁, t₁, h₁, k₁, rfl⟩ := List.forall₂_cons_right_iff.1 k₀
  obtain ⟨x₂, t₂, h₂, k₂, rfl⟩ := List.forall₂_cons_right_iff.1 k₁
  obtain ⟨x₃, t₃, h₃, k₃, rfl⟩ := List.forall₂_cons_right_iff.1 k₂
  obtain ⟨x₄, t₄, h₄, k₄, rfl⟩ := List.forall₂_cons_right_iff.1 k₃
  obtain ⟨x₅, t₅, h₅, k₅, rfl⟩ := List.forall₂_cons_right_iff.1 k₄
  obtain ⟨x₆, t₆, h₆, k₆, rfl⟩ := List.forall₂_cons_right_iff.1 k₅
  obtain ⟨x₇, t₇, h₇, k₇, rfl⟩ := List.forall₂_cons_right_iff.1 k₆
  obtain ⟨x₈, t₈, h₈, k₈, rfl⟩ := List.forall₂_cons_right_iff.1 k₇
  obtain rfl := List.forall₂_nil_right_iff.1 k₈
  simp only [List.getD_cons_zero, List.getD_cons_succ]
  exact (m4PtNsL_mono h₀ h₁ h₃ h₄ h₅ h₆ h₇ h₈ hm).trans
    (le_supTo (f := fun j' => m4PtNsL n m j' p s Ls sIn Lg uB) h₂)

end M4

/-! ### M5 -/

section M5

/-- **M5's certificates' work** in `m5WorkRawNs`. -/
def m5CertPt (n m k s sIn jB : ℕ) : ℕ :=
  2 * (certCount (n + m) n k * 4 +
      certWork (n + m) n k sIn (stabCost (n + m) sIn + 5) (transCost (n + m) sIn + 5)
        (orbitsCost (n + m) sIn (n + m) + 5) (genCost k (k * (sIn + 1)) + 2)
        (orbitsCost k sIn k + 5) (stabCost k sIn + 5) (ssM5βns (n + m) m k sIn s jB).Bgk
        (ssM5βns (n + m) m k sIn s jB).BlA (ssM5βns (n + m) m k sIn s jB).Bgs
        (ssM5βns (n + m) m k sIn s jB).BF)

/-- **M5's case decision's work** in `m5WorkRawNs`, at orbit size `a`. -/
def m5CasePt (n m k s sIn jB a : ℕ) : ℕ :=
  m5CaseCost n (n + m) (orbitsCost (n + m) sIn (n + m) + 5)
    (Case2b.degCost (n + m) n a a sIn (stabCost (n + m) sIn + 5)
      (ssM5βns (n + m) m k sIn s jB).Bg (orbitsCost a (a * a) a + 5)
      (stabCost a (a * a) + 5))

/-- **M5's dispatch's work** in `m5WorkRawNs`, at the data `g, P₁, …, ol`. -/
def m5DispPt (n m k p s sIn Lg uB jB g P₁ P₂ nΦ mx my nx ny j cl ol : ℕ) : ℕ :=
  m5DispNumNs n (n + m) k s sIn (genCost (n + m) Lg + 2) (Sims.liftCost (n + m) sIn n + 7)
    (orbitsCost (n + m) sIn (n + m) + 5)
    (ssBdF n (n + m) p sIn + ssBdJU n (n + m) p p sIn uB) p (ssM5βns (n + m) m k sIn s jB)
    (stabCost (n + m) sIn + 5) (transCost (n + m) sIn + 5)
    (orbitsCost (n + m) sIn (n + m) + 5) (genCost k (k * (sIn + 1)) + 2)
    (orbitsCost k sIn k + 5) (stabCost k sIn + 5) (fun M => orbitsCost M (M * M) M + 5)
    (fun M => stabCost M (M * M) + 5) (fun M => transCost M (M * M) + 5) uB
    (ssBg1J (n + m) m) (ssBg1J (n + m) m) g P₁ P₂ nΦ mx my nx ny j cl ol

theorem m5WorkRawNs_eq (n m k p s sIn Lg uB jB : ℕ) :
    m5WorkRawNs n m k p s sIn Lg uB jB =
      m5CertPt n m k s sIn jB + 2 * supTo (m5CasePt n m k s sIn jB) m +
        envSup [sIn, m * m + m, m * m + m, m, m, m, m, m, jB, cjB m, olB m] (fun ds =>
          m5DispPt n m k p s sIn Lg uB jB (ds.getD 0 0) (ds.getD 1 0) (ds.getD 2 0)
            (ds.getD 3 0) (ds.getD 4 0) (ds.getD 5 0) (ds.getD 6 0) (ds.getD 7 0)
            (ds.getD 8 0) (ds.getD 9 0) (ds.getD 10 0)) + 15 :=
  rfl

/-- **The corner bound on M5's work without stuck orbits**: the certificates' and the case
decision's work at the corner, and the maximum over Case 2b's depth `j ≤ jB` of the dispatch's
work at the corner of the other data. -/
def m5WorkUB (n m k p s sIn Lg uB jB : ℕ) : ℕ :=
  m5CertPt n m k s sIn jB + 2 * m5CasePt n m k s sIn jB m +
    supTo (fun j => m5DispPt n m k p s sIn Lg uB jB sIn (m * m + m) (m * m + m) m m m m m j
      (cjB m) (olB m)) jB + 15

/-- `m5CertPt` is monotone in `n`, `m`, `k` and `sIn` when `2k' ≤ m'`: the binomial `C(m, k)`
grows in `k` below `m/2`. It does not depend on `s` and `jB`. -/
theorem m5CertPt_mono {n n' m m' k k' s s' sIn sIn' jB jB' : ℕ} (hn : n ≤ n') (hm : m ≤ m')
    (hk : k ≤ k') (hI : sIn ≤ sIn') (hkm : 2 * k' ≤ m') :
    m5CertPt n m k s sIn jB ≤ m5CertPt n' m' k' s' sIn' jB' := by
  unfold m5CertPt
  gcongr
  all_goals try omega
  all_goals try simp only [ssM5βns, ssM5β]
  all_goals try gcongr
  all_goals
    rw [Nat.add_sub_cancel_left, Nat.add_sub_cancel_left]
    exact (Nat.choose_le_choose k hm).trans (choose_mono_le_half hk hkm)

/-- `m5CasePt` is monotone in the sizes `n`, `m`, `sIn` and in the orbit size `a`; it does not
depend on `k`, `s` and `jB`. -/
theorem m5CasePt_mono {n n' m m' k k' s s' sIn sIn' jB jB' a a' : ℕ} (hn : n ≤ n')
    (hm : m ≤ m') (hI : sIn ≤ sIn') (ha : a ≤ a') :
    m5CasePt n m k s sIn jB a ≤ m5CasePt n' m' k' s' sIn' jB' a' := by
  unfold m5CasePt
  gcongr
  all_goals try omega
  all_goals try simp only [ssM5βns, ssM5β]
  all_goals try gcongr

/-- `m5DispPt` is monotone in every size and datum except Case 2b's depth `j`, when `k'`, `m'`,
`mx'` and `my'` are positive and `j < nx', ny'`. -/
theorem m5DispPt_mono {n n' m m' k k' p p' s s' sIn sIn' Lg Lg' uB uB' jB jB' : ℕ}
    {g g' P₁ P₁' P₂ P₂' nΦ nΦ' mx mx' my my' nx nx' ny ny' j cl cl' ol ol' : ℕ}
    (hn : n ≤ n') (hm : m ≤ m') (hk : k ≤ k') (hp : p ≤ p') (hs : s ≤ s') (hI : sIn ≤ sIn')
    (hLg : Lg ≤ Lg') (hu : uB ≤ uB') (hjB : jB ≤ jB') (h₀ : g ≤ g') (h₁ : P₁ ≤ P₁')
    (h₂ : P₂ ≤ P₂') (h₃ : nΦ ≤ nΦ') (h₄ : mx ≤ mx') (h₅ : my ≤ my') (h₆ : nx ≤ nx')
    (h₇ : ny ≤ ny') (h₉ : cl ≤ cl') (h₁₀ : ol ≤ ol') (hk1 : 1 ≤ k') (hm1 : 1 ≤ m')
    (hx1 : 1 ≤ mx') (hy1 : 1 ≤ my') (hjx : j < nx') (hjy : j < ny') :
    m5DispPt n m k p s sIn Lg uB jB g P₁ P₂ nΦ mx my nx ny j cl ol ≤
      m5DispPt n' m' k' p' s' sIn' Lg' uB' jB' g' P₁' P₂' nΦ' mx' my' nx' ny' j cl' ol' := by
  unfold m5DispPt
  gcongr
  all_goals try omega
  all_goals try simp only [ssM5βns, ssM5β]
  all_goals gcongr

/-- **M5's work without stuck orbits is at most `m5WorkUB`**, for `1 ≤ k`, `2k ≤ m` and
`jB < m`. -/
theorem m5WorkNsSS_le {n m k p s sIn Lg uB jB : ℕ} (hk : 1 ≤ k) (hkm : 2 * k ≤ m)
    (hjm : jB < m) : m5WorkNsSS n m k p s sIn Lg uB jB ≤ m5WorkUB n m k p s sIn Lg uB jB := by
  unfold m5WorkNsSS
  refine envSup_le fun xs hxs => ?_
  obtain ⟨x₀, t₀, h₀, k₀, rfl⟩ := List.forall₂_cons_right_iff.1 hxs
  obtain ⟨x₁, t₁, h₁, k₁, rfl⟩ := List.forall₂_cons_right_iff.1 k₀
  obtain ⟨x₂, t₂, h₂, k₂, rfl⟩ := List.forall₂_cons_right_iff.1 k₁
  obtain ⟨x₃, t₃, h₃, k₃, rfl⟩ := List.forall₂_cons_right_iff.1 k₂
  obtain ⟨x₄, t₄, h₄, k₄, rfl⟩ := List.forall₂_cons_right_iff.1 k₃
  obtain ⟨x₅, t₅, h₅, k₅, rfl⟩ := List.forall₂_cons_right_iff.1 k₄
  obtain ⟨x₆, t₆, h₆, k₆, rfl⟩ := List.forall₂_cons_right_iff.1 k₅
  obtain ⟨x₇, t₇, h₇, k₇, rfl⟩ := List.forall₂_cons_right_iff.1 k₆
  obtain ⟨x₈, t₈, h₈, k₈, rfl⟩ := List.forall₂_cons_right_iff.1 k₇
  obtain rfl := List.forall₂_nil_right_iff.1 k₈
  simp only [List.getD_cons_zero, List.getD_cons_succ]
  rw [m5WorkRawNs_eq]
  unfold m5WorkUB
  gcongr ?_ + 2 * ?_ + ?_ + 15
  · exact m5CertPt_mono h₀ h₁ h₂ h₅ hkm
  · exact supTo_le fun a ha => m5CasePt_mono h₀ h₁ h₅ (ha.trans h₁)
  · refine envSup_le fun ds hds => ?_
    obtain ⟨d₀, u₀, e₀, l₀, rfl⟩ := List.forall₂_cons_right_iff.1 hds
    obtain ⟨d₁, u₁, e₁, l₁, rfl⟩ := List.forall₂_cons_right_iff.1 l₀
    obtain ⟨d₂, u₂, e₂, l₂, rfl⟩ := List.forall₂_cons_right_iff.1 l₁
    obtain ⟨d₃, u₃, e₃, l₃, rfl⟩ := List.forall₂_cons_right_iff.1 l₂
    obtain ⟨d₄, u₄, e₄, l₄, rfl⟩ := List.forall₂_cons_right_iff.1 l₃
    obtain ⟨d₅, u₅, e₅, l₅, rfl⟩ := List.forall₂_cons_right_iff.1 l₄
    obtain ⟨d₆, u₆, e₆, l₆, rfl⟩ := List.forall₂_cons_right_iff.1 l₅
    obtain ⟨d₇, u₇, e₇, l₇, rfl⟩ := List.forall₂_cons_right_iff.1 l₆
    obtain ⟨d₈, u₈, e₈, l₈, rfl⟩ := List.forall₂_cons_right_iff.1 l₇
    obtain ⟨d₉, u₉, e₉, l₉, rfl⟩ := List.forall₂_cons_right_iff.1 l₈
    obtain ⟨d₁₀, u₁₀, e₁₀, l₁₀, rfl⟩ := List.forall₂_cons_right_iff.1 l₉
    obtain rfl := List.forall₂_nil_right_iff.1 l₁₀
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    have hsq : x₁ * x₁ + x₁ ≤ m * m + m := by gcongr
    have hj : d₈ ≤ jB := e₈.trans h₈
    exact (m5DispPt_mono h₀ h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ (e₀.trans h₅) (e₁.trans hsq) (e₂.trans hsq)
      (e₃.trans h₁) (e₄.trans h₁) (e₅.trans h₁) (e₆.trans h₁) (e₇.trans h₁)
      (e₉.trans (by gcongr)) (e₁₀.trans (by gcongr)) hk (by omega) (by omega) (by omega)
      (by omega) (by omega)).trans
      (le_supTo (f := fun j => m5DispPt n m k p s sIn Lg uB jB sIn (m * m + m) (m * m + m) m m m
        m m j (cjB m) (olB m)) hj)

end M5

/-! ### The sharp case work -/

section CaseWork

/-- **The sharp work at M4 is at most its corner values**, for a base `m = N - n ≥ 1`. -/
theorem caseWorkS_m4_le {n N p g s k j t jB : ℕ} (hm : 1 ≤ N - n) :
    caseWorkS .m4 n N p g s k j t jB ≤
      supTo (fun j' => m4PtNsL n (N - n) j' p s n s (ssLgM4Ns (N - n) j (t * lam (N - n)) s)
        (t * lam (N - n))) j :=
  m4WorkNsLSS_le hm

/-- **The sharp work at M5 is at most the restriction's work and `m5WorkUB`**, for `1 ≤ k`,
`2k ≤ m` and `jB < m`, where `m = N - n`. -/
theorem caseWorkS_m5_le {n N p g s k j t jB : ℕ} (hk : 1 ≤ k) (hkm : 2 * k ≤ N - n)
    (hjm : jB < N - n) :
    caseWorkS .m5 n N p g s k j t jB ≤
      rbOverSS N p (N - n) g s +
        m5WorkUB p (N - n) k p s s (ssLgM5Ns (N - n) k (t * lam (N - n)) jB s) (t * lam (N - n))
          jB :=
  Nat.add_le_add_left (m5WorkNsSS_le hk hkm hjm) _

end CaseWork

end GraphIso.Main
