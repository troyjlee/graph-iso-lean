module

public import GraphIso.Main.SharpWork

/-!
# Monotonicity of the remaining costs

Stage 14j-6c-1 (`PLAN-14.md` §14.13 item 3). `Q(n₀)` (`GraphIso.Main.PotQ`) evaluates every
case's work and factor at the corner of its sizes on the domain. That needs every cost function
involved to be monotone. `GraphIso.Main.SharpWork` proved this for the functions M4's and M5's
sharp work calls. This module covers the rest:
- the dispatch's tests (`mainTestCost`);
- the work of the base case, the chain rule, M0, M1, M2a, M2b and M3;
- M5's restriction (`rbOverSS`);
- the step parameters `ssLgM4Ns` and `ssLgM5Ns`;
- the factors and counted calls (`m5FBns`, `c3Count`).

* **Monotonicity of the costs** (`CostMono.*`, generated as in `SharpWork`): each lemma states
  that a cost function grows with its natural-number arguments. It is proved by `unfold` and
  `gcongr`, with the lemmas of `SharpWork` and the earlier ones (all tagged `@[gcongr only]`).
  A difference `a - b` of two arguments gets the hypothesis `a - b ≤ a' - b'`. A power with a
  varying exponent, or a product that `gcongr` needs positive, gets `1 ≤ x'`.
* **M5's work bound** `m5WorkUB` (`caseWorkS_m5_le`) is monotone in all its sizes for `1 ≤ k'`
  and `2k' ≤ m'`, and for Case 2b's depth bound `jB < m` (`m5WorkUB_mono`).
-/

@[expose] public section

namespace GraphIso.Main

open Equiv Cost GraphIso GraphIso.Programs GraphIso.Toolkit GraphIso.Recursion GraphIso.Certificates
  Sims

/-! ### Monotonicity of the costs -/

@[gcongr only] theorem CostMono.Main_bigTestCost {n n' N N' s s' t t' : ℕ} (h1 : N ≤ N')
    (h2 : s ≤ s') (h3 : t ≤ t') (s0 : N - n ≤ N' - n') :
    GraphIso.Main.bigTestCost n N s t ≤
      GraphIso.Main.bigTestCost n' N' s' t' := by
  unfold GraphIso.Main.bigTestCost
  gcongr

@[gcongr only] theorem CostMono.Main_blkTestCost {n n' N N' g g' : ℕ} (h1 : N ≤ N') (h2 : g ≤ g')
    (s0 : N - n ≤ N' - n') :
    GraphIso.Main.blkTestCost n N g ≤
      GraphIso.Main.blkTestCost n' N' g' := by
  unfold GraphIso.Main.blkTestCost
  gcongr

@[gcongr only] theorem CostMono.Main_c3Count {mx mx' k k' n n' : ℕ} (h0 : mx ≤ mx') (h1 : k ≤ k')
    (h2 : n ≤ n') (x0 : 1 ≤ mx') :
    GraphIso.Main.c3Count mx k n ≤
      GraphIso.Main.c3Count mx' k' n' := by
  unfold GraphIso.Main.c3Count
  gcongr

@[gcongr only] theorem CostMono.Main_chainCost {N N' p p' k k' : ℕ} (h0 : N ≤ N') (h1 : p ≤ p')
    (h2 : k ≤ k') :
    GraphIso.Main.chainCost N p k ≤
      GraphIso.Main.chainCost N' p' k' := by
  unfold GraphIso.Main.chainCost
  gcongr

@[gcongr only] theorem CostMono.Main_fixedStepCost {p p' : ℕ} (h0 : p ≤ p') :
    GraphIso.Main.fixedStepCost p ≤
      GraphIso.Main.fixedStepCost p' := by
  unfold GraphIso.Main.fixedStepCost
  gcongr

@[gcongr only] theorem CostMono.Main_fixedTestCost {p p' s s' : ℕ} (h0 : p ≤ p') (h1 : s ≤ s') :
    GraphIso.Main.fixedTestCost p s ≤
      GraphIso.Main.fixedTestCost p' s' := by
  unfold GraphIso.Main.fixedTestCost
  gcongr

@[gcongr only] theorem CostMono.Main_hintPreCost {n n' N N' g g' : ℕ} (h0 : n ≤ n') (h1 : N ≤ N')
    (h2 : g ≤ g') (s0 : N - n ≤ N' - n') :
    GraphIso.Main.hintPreCost n N g ≤
      GraphIso.Main.hintPreCost n' N' g' := by
  unfold GraphIso.Main.hintPreCost
  gcongr

@[gcongr only] theorem CostMono.Main_kerRedCost
    {N N' n n' p p' r r' sK sK' s s' Bk Bk' Bo Bo' Bcr Bcr' Bgen Bgen' : ℕ} (h0 : N ≤ N')
    (h2 : p ≤ p') (h3 : r ≤ r') (h4 : sK ≤ sK') (h5 : s ≤ s') (h6 : Bk ≤ Bk') (h7 : Bo ≤ Bo')
    (h8 : Bcr ≤ Bcr') (h9 : Bgen ≤ Bgen') (x0 : N - n ≤ N' - n') :
    GraphIso.Main.kerRedCost N n p r sK s Bk Bo Bcr Bgen ≤
      GraphIso.Main.kerRedCost N' n' p' r' sK' s' Bk' Bo' Bcr' Bgen' := by
  unfold GraphIso.Main.kerRedCost
  gcongr

@[gcongr only] theorem CostMono.Main_m0Cost {n n' N N' p p' s s' Bgen Bgen' : ℕ} (h0 : n ≤ n')
    (h1 : N ≤ N') (h2 : p ≤ p') (h3 : s ≤ s') (h4 : Bgen ≤ Bgen') :
    GraphIso.Main.m0Cost n N p s Bgen ≤
      GraphIso.Main.m0Cost n' N' p' s' Bgen' := by
  unfold GraphIso.Main.m0Cost
  gcongr

@[gcongr only] theorem CostMono.Main_m0StepCost
    {n n' N N' p p' s₀ s₀' s s' Bgen₀ Bgen₀' Blift Blift' Bgen Bgen' : ℕ} (h0 : n ≤ n')
    (h1 : N ≤ N') (h2 : p ≤ p') (h3 : s₀ ≤ s₀') (h4 : s ≤ s') (h5 : Bgen₀ ≤ Bgen₀')
    (h6 : Blift ≤ Blift') (h7 : Bgen ≤ Bgen') :
    GraphIso.Main.m0StepCost n N p s₀ s Bgen₀ Blift Bgen ≤
      GraphIso.Main.m0StepCost n' N' p' s₀' s' Bgen₀' Blift' Bgen' := by
  unfold GraphIso.Main.m0StepCost
  gcongr

@[gcongr only] theorem CostMono.Main_m0WorkSS {n n' N N' p p' g g' s s' : ℕ} (h0 : n ≤ n')
    (h1 : N ≤ N') (h2 : p ≤ p') (h3 : g ≤ g') (h4 : s ≤ s') :
    GraphIso.Main.m0WorkSS n N p g s ≤
      GraphIso.Main.m0WorkSS n' N' p' g' s' := by
  unfold GraphIso.Main.m0WorkSS
  gcongr

@[gcongr only] theorem CostMono.Main_m1StepCost
    {n n' N N' p p' s₀ s₀' s s' Borb Borb' Bgen₁ Bgen₁' Blift Blift' Bgen Bgen' : ℕ} (h0 : n ≤ n')
    (h1 : N ≤ N') (h2 : p ≤ p') (h3 : s₀ ≤ s₀') (h4 : s ≤ s') (h5 : Borb ≤ Borb')
    (h6 : Bgen₁ ≤ Bgen₁') (h7 : Blift ≤ Blift') (h8 : Bgen ≤ Bgen') (x0 : N - n ≤ N' - n') :
    GraphIso.Main.m1StepCost n N p s₀ s Borb Bgen₁ Blift Bgen ≤
      GraphIso.Main.m1StepCost n' N' p' s₀' s' Borb' Bgen₁' Blift' Bgen' := by
  unfold GraphIso.Main.m1StepCost
  gcongr

@[gcongr only] theorem CostMono.Main_m1WorkSS {n n' m m' p p' g g' s s' : ℕ} (h0 : n ≤ n')
    (h1 : m ≤ m') (h2 : p ≤ p') (h3 : g ≤ g') (h4 : s ≤ s') (x0 : n + m - n ≤ n' + m' - n') :
    GraphIso.Main.m1WorkSS n m p g s ≤
      GraphIso.Main.m1WorkSS n' m' p' g' s' := by
  unfold GraphIso.Main.m1WorkSS
  gcongr

@[gcongr only] theorem CostMono.Main_m2aStepCost
    {n n' N N' p p' s₀ s₀' s s' Ls Ls' Bgen₂ Bgen₂' Blift Blift' Bgen Bgen' : ℕ} (h0 : n ≤ n')
    (h1 : N ≤ N') (h2 : p ≤ p') (h3 : s₀ ≤ s₀') (h4 : s ≤ s') (h5 : Ls ≤ Ls') (h6 : Bgen₂ ≤ Bgen₂')
    (h7 : Blift ≤ Blift') (h8 : Bgen ≤ Bgen') (x0 : N - n ≤ N' - n') :
    GraphIso.Main.m2aStepCost n N p s₀ s Ls Bgen₂ Blift Bgen ≤
      GraphIso.Main.m2aStepCost n' N' p' s₀' s' Ls' Bgen₂' Blift' Bgen' := by
  unfold GraphIso.Main.m2aStepCost
  gcongr

@[gcongr only] theorem CostMono.Main_m2aWorkSS {n n' m m' p p' g g' s s' Ls Ls' : ℕ} (h0 : n ≤ n')
    (h1 : m ≤ m') (h2 : p ≤ p') (h3 : g ≤ g') (h4 : s ≤ s') (h5 : Ls ≤ Ls')
    (x0 : n + m - n ≤ n' + m' - n') :
    GraphIso.Main.m2aWorkSS n m p g s Ls ≤
      GraphIso.Main.m2aWorkSS n' m' p' g' s' Ls' := by
  unfold GraphIso.Main.m2aWorkSS
  gcongr

@[gcongr only] theorem CostMono.Main_m2bStepCost
    {n n' N N' k k' p p' Ls Ls' s s' sS sS' Lt Lt' sH sH' sIn sIn' sR sR' Bge Bge' Bst Bst' : ℕ}
    {Btr Btr' Bgt Bgt' Bgen₃ Bgen₃' Blift Blift' Bgen Bgen' Bo Bo' Bgen₂ Bgen₂' : ℕ} (h0 : n ≤ n')
    (h1 : N ≤ N') (h2 : k ≤ k') (h3 : p ≤ p') (h4 : Ls ≤ Ls') (h5 : s ≤ s') (h6 : sS ≤ sS')
    (h7 : Lt ≤ Lt') (h8 : sH ≤ sH') (h9 : sIn ≤ sIn') (h10 : sR ≤ sR') (h11 : Bge ≤ Bge')
    (h12 : Bst ≤ Bst') (h13 : Btr ≤ Btr') (h14 : Bgt ≤ Bgt') (h15 : Bgen₃ ≤ Bgen₃')
    (h16 : Blift ≤ Blift') (h17 : Bgen ≤ Bgen') (h18 : Bo ≤ Bo') (h19 : Bgen₂ ≤ Bgen₂')
    (s0 : N - n ≤ N' - n') (x0 : n + k - n ≤ n' + k' - n') :
    GraphIso.Main.m2bStepCost n N k p Ls s sS Lt sH sIn sR Bge Bst Btr Bgt Bgen₃ Blift Bgen Bo
        Bgen₂ ≤
      GraphIso.Main.m2bStepCost n' N' k' p' Ls' s' sS' Lt' sH' sIn' sR' Bge' Bst' Btr' Bgt' Bgen₃'
        Blift' Bgen' Bo' Bgen₂' := by
  unfold GraphIso.Main.m2bStepCost
  gcongr

@[gcongr only] theorem CostMono.Main_m2bWorkSS {n n' m m' p p' g g' Ls Ls' sIn sIn' : ℕ}
    (h0 : n ≤ n') (h1 : m ≤ m') (h2 : p ≤ p') (h3 : g ≤ g') (h4 : Ls ≤ Ls') (h5 : sIn ≤ sIn')
    (x0 : n + m - n ≤ n' + m' - n') :
    GraphIso.Main.m2bWorkSS n m p g Ls sIn ≤
      GraphIso.Main.m2bWorkSS n' m' p' g' Ls' sIn' := by
  unfold GraphIso.Main.m2bWorkSS
  gcongr

@[gcongr only] theorem CostMono.Main_m3WorkSS {n n' N N' p p' g g' s s' : ℕ} (h1 : N ≤ N')
    (h2 : p ≤ p') (h3 : g ≤ g') (h4 : s ≤ s') (s0 : N - n ≤ N' - n') :
    GraphIso.Main.m3WorkSS n N p g s ≤
      GraphIso.Main.m3WorkSS n' N' p' g' s' := by
  unfold GraphIso.Main.m3WorkSS
  gcongr

@[gcongr only] theorem CostMono.Main_m5FBns {m m' k k' uB uB' jB jB' : ℕ} (h0 : m ≤ m')
    (h1 : k ≤ k') (h2 : uB ≤ uB') (h3 : jB ≤ jB') (x0 : 1 ≤ m') :
    GraphIso.Main.m5FBns m k uB jB ≤
      GraphIso.Main.m5FBns m' k' uB' jB' := by
  unfold GraphIso.Main.m5FBns
  gcongr

@[gcongr only] theorem CostMono.Main_neqTestCost {n n' N N' p p' : ℕ} (h1 : N ≤ N') (h2 : p ≤ p')
    (s0 : N - n ≤ N' - n') :
    GraphIso.Main.neqTestCost n N p ≤
      GraphIso.Main.neqTestCost n' N' p' := by
  unfold GraphIso.Main.neqTestCost
  gcongr

@[gcongr only] theorem CostMono.Main_mainTestCost {n n' N N' p p' g g' s s' t t' : ℕ} (h0 : n ≤ n')
    (h1 : N ≤ N') (h2 : p ≤ p') (h3 : g ≤ g') (h4 : s ≤ s') (h5 : t ≤ t') (x0 : N - n ≤ N' - n') :
    GraphIso.Main.mainTestCost n N p g s t ≤
      GraphIso.Main.mainTestCost n' N' p' g' s' t' := by
  unfold GraphIso.Main.mainTestCost
  gcongr

@[gcongr only] theorem CostMono.Main_rbCost
    {N N' k k' m m' s s'' C' C'' s' s''' sK sK' Bgm Bgm' Blift Blift' Bker Bker' Bgn Bgn' : ℕ}
    (h0 : N ≤ N') (h1 : k ≤ k') (h2 : m ≤ m') (h3 : s ≤ s'') (h4 : C' ≤ C'') (h5 : s' ≤ s''')
    (h6 : sK ≤ sK') (h7 : Bgm ≤ Bgm') (h8 : Blift ≤ Blift') (h9 : Bker ≤ Bker') (h10 : Bgn ≤ Bgn') :
    GraphIso.Main.rbCost N k m s C' s' sK Bgm Blift Bker Bgn ≤
      GraphIso.Main.rbCost N' k' m' s'' C'' s''' sK' Bgm' Blift' Bker' Bgn' := by
  unfold GraphIso.Main.rbCost
  gcongr

@[gcongr only] theorem CostMono.Main_rbOverSS {N N' p p' m m' g g' s s' : ℕ} (h0 : N ≤ N')
    (h1 : p ≤ p') (h2 : m ≤ m') (h3 : g ≤ g') (h4 : s ≤ s') :
    GraphIso.Main.rbOverSS N p m g s ≤
      GraphIso.Main.rbOverSS N' p' m' g' s' := by
  unfold GraphIso.Main.rbOverSS
  gcongr

@[gcongr only] theorem CostMono.Main_ssLgM4Ns {m m' j j' uB uB' sIn sIn' : ℕ} (h0 : m ≤ m')
    (h1 : j ≤ j') (h2 : uB ≤ uB') (h3 : sIn ≤ sIn') (x0 : m - j ≤ m' - j') (x1 : 1 ≤ m') :
    GraphIso.Main.ssLgM4Ns m j uB sIn ≤
      GraphIso.Main.ssLgM4Ns m' j' uB' sIn' := by
  unfold GraphIso.Main.ssLgM4Ns
  gcongr

@[gcongr only] theorem CostMono.Main_ssLgM5Ns {m m' k k' uB uB' jB jB' sIn sIn' : ℕ} (h0 : m ≤ m')
    (h1 : k ≤ k') (h2 : uB ≤ uB') (h3 : jB ≤ jB') (h4 : sIn ≤ sIn') (x0 : 1 ≤ m') :
    GraphIso.Main.ssLgM5Ns m k uB jB sIn ≤
      GraphIso.Main.ssLgM5Ns m' k' uB' jB' sIn' := by
  unfold GraphIso.Main.ssLgM5Ns
  gcongr

/-! ### M5's work bound -/

/-- **`m5WorkUB` is monotone** in all its sizes, for `1 ≤ k'`, `2k' ≤ m'` (the certificates'
binomial) and `jB < m` (Case 2b's depth below the base, for `m5DispPt_mono`). -/
theorem m5WorkUB_mono {n n' m m' k k' p p' s s' sIn sIn' Lg Lg' uB uB' jB jB' : ℕ}
    (hn : n ≤ n') (hm : m ≤ m') (hk : k ≤ k') (hp : p ≤ p') (hs : s ≤ s') (hI : sIn ≤ sIn')
    (hLg : Lg ≤ Lg') (hu : uB ≤ uB') (hjB : jB ≤ jB') (hk1 : 1 ≤ k') (hkm : 2 * k' ≤ m')
    (hjm : jB < m) :
    m5WorkUB n m k p s sIn Lg uB jB ≤ m5WorkUB n' m' k' p' s' sIn' Lg' uB' jB' := by
  unfold m5WorkUB
  gcongr ?_ + 2 * ?_ + ?_ + 15
  · exact m5CertPt_mono hn hm hk hI hkm
  · exact m5CasePt_mono hn hm hI hm
  · refine supTo_le fun j hj => le_trans ?_ (le_supTo (hj.trans hjB))
    exact m5DispPt_mono hn hm hk hp hs hI hLg hu hjB hI (by gcongr) (by gcongr) hm hm hm hm hm
      (CostMono.Main_cjB hm) (CostMono.Main_olB hm) hk1 (by omega) (by omega) (by omega)
      (by omega) (by omega)

end GraphIso.Main
