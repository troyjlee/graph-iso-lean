module

public import GraphIso.Solver.Sims
public import GraphIso.Solver.ReferenceCompose

/-!
# The reductions with the solver and the Schreier–Sims backend

The compositions of `GraphIso/Solver/Compose.lean`, instantiated with the Schreier–Sims
backend: closed programs over the empty signature, run inside `simsSolver`, with correctness
and cost bounds and no assumed group oracle. The instance carries no backend data (`()`).

* `restrict_sims`: the restriction reduction, whose sub-call is the solver at the window's
  degree `m`, costs at most `restrictSimsCost n m L N`. Every backend charge is polynomial in
  `n`, `m` and `L`; the group order `N` enters only through the sub-call's `solveBound`.
* `blockReduce_sims`: the block-system reduction with `k` blocks costs at most
  `blockSimsCost n m k L N R` for `R = N / |K|` branches; the backend charges are polynomial in
  `n`, `k`, `L` and `R`.
-/

@[expose] public section

namespace GraphIso.Sims

open Equiv Cost Programs Solver

/-! ### Restriction -/

/-- The cost bound of the restriction reduction with the Schreier–Sims backend, for degree `n`,
window size `m`, `L` generators and group order `N`. -/
def restrictSimsCost (n m L N : ℕ) : ℕ :=
  restrictCost n m L (1 + solveBound (simsQ m) m N) (m * m) (n * n) (genCost m L + 2)
    (liftCost n L m + 7) (kerCost n L m + 5) (genCost n (n * n + m * m) + 2)

/-- **The restriction reduction with the solver and the Schreier–Sims backend.** -/
theorem restrict_sims {n : ℕ} {xy : StrData × StrData} {w : WinData} {σd : PermData}
    {gs : GensData} (hw : w.Valid n) (hσ : σd.Valid n) (hgs : GensData.AllValid n gs)
    (hinv : IsInvariant (GensData.denote n gs) (w.denote n)) :
    ∃ (ans : AnswerData Ty.unit) (tr : Trace Signature.empty),
      Runs Ctx.empty.O (simsSolver.proc Ty.denote)
        ((Programs.restrictProg (fun J => .recur J) (xy, w, σd, n, gs, ())).subst ssImpl)
        ans tr ∧
      Trace.localCost tr ≤
        restrictSimsCost n w.1.length gs.length (Nat.card (GensData.denote n gs)) ∧
      AnsOK ssDV n (w.denote n) (σd.denote n) (gs.denote n) (xy.1.denote n) (xy.2.denote n)
        ans := by
  have hv : InstData.Valid (D := Ty.unit) (xy, w, σd, n, gs, ()) ssDV :=
    ⟨hw, hσ, ⟨hgs, trivial⟩, hinv⟩
  obtain ⟨ans, ⟨tr, hr, hc, hpre⟩, hok, -⟩ := restrict_solve_spec (X := ssCtx) (DV := ssDV)
    (fun op x _ hx => ssOracle_meets op x hx) (fun _ _ _ hx => hx) hv
    (ssBounds w.1.length _) (sK := n * n)
    (Bgm := genCost w.1.length gs.length + 2) (Blift := liftCost n gs.length w.1.length + 7)
    (Bker := kerCost n gs.length w.1.length + 5)
    (Bgn := genCost n (n * n + w.1.length * w.1.length) + 2)
    (by
      show genCost _ (GensData.restrictTo (WinData.pos n w) w.1 gs).length + 2 ≤ _
      simp [GensData.restrictTo])
    (fun _ => le_rfl) le_rfl (kernelModel_spec hgs hw).2.2
    (fun _ _ hl _ => Nat.add_le_add_right (genCost_mono hl) 2)
  obtain ⟨tr', hr', hc'⟩ := Runs.subst ssImpl_implements hr hpre
  refine ⟨ans, tr', hr', ?_, hok⟩
  rw [Trace.cost_empty] at hc'
  exact hc'.trans hc

/-! ### Block systems -/

theorem repsCost_mono {n L L₁ L₂ I : ℕ} (h : L₁ ≤ L₂) : repsCost n L L₁ I ≤ repsCost n L L₂ I := by
  unfold repsCost
  gcongr
  exact buildCost_mono h

/-- The cost bound of the block-system reduction with the Schreier–Sims backend, for degree
`n`, `m` window points in `k` blocks, `L` generators, group order `N` and `R` branches. -/
def blockSimsCost (n m k L N R : ℕ) : ℕ :=
  3 + blockKernelCost n m k L ((n + k) * (n + k)) (genCost (n + k) L + 2)
      (kerCost (n + k) ((n + k) * (n + k)) k + 5) (genCost n ((n + k) * (n + k)) + 2) +
    (2 + (repsCost n L (n * n) R + 7) +
      R * (24 * n + (3 + k * (2 * n + 14) + 5 * m + 2 * m * N * simsQ n) + n * n + 45) +
      (genCost n (R * (n * n + 1)) + 2) + 19)

/-- **The block-system reduction with the solver and the Schreier–Sims backend.** The bound
has `R = N / |K|` branches. -/
theorem blockReduce_sims {n : ℕ} {xy : StrData × StrData} {w : WinData} {σd : PermData}
    {gs : GensData} {bs : List (List ℕ)} (hw : w.Valid n) (hσ : σd.Valid n)
    (hgs : GensData.AllValid n gs) (hinv : IsInvariant (GensData.denote n gs) (w.denote n))
    (hbs : IsBlockList w bs) (hG : PermutesBlocks (GensData.denote n gs) bs) :
    ∃ (ans : AnswerData Ty.unit) (tr : Trace Signature.empty),
      Runs Ctx.empty.O (simsSolver.proc Ty.denote)
        ((Programs.blockReduceProg (fun J => .recur J) xy w σd (n, gs, ()) bs).subst ssImpl)
        ans tr ∧
      Trace.localCost tr ≤ blockSimsCost n w.1.length bs.length gs.length
        (Nat.card (GensData.denote n gs))
        (Nat.card (GensData.denote n gs) / Nat.card (blockKernel (GensData.denote n gs) bs)) ∧
      AnsOK ssDV n (w.denote n) (σd.denote n) (gs.denote n) (xy.1.denote n) (xy.2.denote n)
        ans := by
  have hNpos : 0 < Nat.card (GensData.denote n gs) := Nat.card_pos
  set k := bs.length
  -- the extended group and its kernel on the block points
  have hegv : GensData.AllValid (n + k) (extendGens n bs gs) :=
    GensData.allValid_extendTo hw hbs hG hgs
  obtain ⟨hev, heden, hel⟩ := generateModel_spec hegv
  have hext : extGroup ssOracle n bs gs = (n + k, generateModel (n + k) (extendGens n bs gs), ()) :=
    rfl
  obtain ⟨hkv, hkden, hkl⟩ := kernelModel_spec hev (valid_blockWin n k)
  have hextK : extKernel ssOracle n bs gs = (n + k, kernelModel (n + k)
      (generateModel (n + k) (extendGens n bs gs)) (blockWin n k), ()) := rfl
  rw [heden, extendGens, GensData.denote_extendTo hw hbs hG hgs] at hkden
  have htv := allValid_truncTo hw hbs hG hkv hkden
  have hKs : (blockKernelModel ssOracle n bs gs).2.1.length ≤ n * n := by
    show (generateModel n ((kernelModel (n + k) (generateModel (n + k) (extendGens n bs gs))
      (blockWin n k)).map (PermData.truncTo n))).length ≤ _
    exact (generateModel_spec htv).2.2
  have hwin : (blockWin n k).1.length = k := by
    simp [blockWin, WinData.ofPoints_fst, blockPts]
  obtain ⟨ans, ⟨tr, hr, hc, hpre⟩, hok, hidx, -⟩ := blockReduce_solve_spec (X := ssCtx)
    (DV := ssDV) (fun op x _ hx => ssOracle_meets op x hx) (fun _ _ _ hx => hx) hw hσ
    ⟨hgs, trivial⟩ hinv hbs hG (ssBounds n _) hKs
    (Bge := genCost (n + k) gs.length + 2)
    (Bke := kerCost (n + k) ((n + k) * (n + k)) k + 5)
    (Bgt := genCost n ((n + k) * (n + k)) + 2)
    (Bcr := repsCost n gs.length (n * n)
      (ssOracle.run GroupOp.cosetReps ((n, gs, ()), blockKernelModel ssOracle n bs gs)).length + 7)
    (by
      show genCost (n + k) (extendGens n bs gs).length + 2 ≤ _
      simp [extendGens])
    (by
      show kerCost (n + k) (generateModel (n + k) (extendGens n bs gs)).length
        (blockWin n k).1.length + 5 ≤ _
      rw [hwin]
      exact Nat.add_le_add_right (kerCost_mono hel le_rfl) 5)
    (by
      show genCost n ((kernelModel (n + k) (generateModel (n + k) (extendGens n bs gs))
        (blockWin n k)).map (PermData.truncTo n)).length + 2 ≤ _
      rw [List.length_map]
      exact Nat.add_le_add_right (genCost_mono hkl) 2)
    (Nat.add_le_add_right (repsCost_mono hKs) 7)
    (fun _ _ hl _ => Nat.add_le_add_right (genCost_mono hl) 2)
  obtain ⟨tr', hr', hc'⟩ := Runs.subst ssImpl_implements hr hpre
  refine ⟨ans, tr', hr', ?_, hok⟩
  rw [Trace.cost_empty] at hc'
  refine hc'.trans (hc.trans ?_)
  have hbr := Reference.blockBranchCost_le (Q := simsQ n) (n := n) hNpos hbs
  have hsK : (extKernel ssOracle n bs gs).2.1.length ≤ (n + k) * (n + k) := hkl
  rw [Nat.div_eq_of_eq_mul_left (Nat.card_pos) hidx.symm]
  unfold blockSimsCost blockKernelCost
  rw [hbs.1.length_eq]
  gcongr
  all_goals first | exact le_rfl | exact hsK | exact hbr

end GraphIso.Sims
