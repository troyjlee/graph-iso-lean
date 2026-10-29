module

public import GraphIso.Solver.Compose
public import GraphIso.Solver.Reference

/-!
# The phase-5 reductions with the solver and the reference backend

The compositions of `GraphIso/Solver/Compose.lean`, instantiated with the reference backend:
closed programs over the empty signature, run inside `referenceSolver`, with correctness and
a finite cost bound and no assumed group oracle. The instance carries the group by all its
elements, `enumerate n gs`, as the reduction programs expect valid backend data. The bounds
start from that data: computing it is not included, and the reference `generate` charges at
most `closureCost n N |gs| + 6` for it (`refB_generate_le`).

* `restrict_reference`: the restriction reduction, whose sub-call is the reference solver at
  the window's degree `m`, costs at most `restrictReferenceCost n m N |gs|` for `N = |G|`.
* `blockReduce_reference`: the block-system reduction with `k` blocks costs at most
  `blockReferenceCost n m k N |gs| R` for `R = N / |K|` branches, `K` the block kernel.
-/

@[expose] public section

namespace GraphIso.Reference

open Equiv Pointwise Cost Programs Enum Solver

/-- The per-invocation unit `solveQ` of the reference bounds, for degree `n` and an ambient
group of order `N`. -/
def refQ (n N : ℕ) : ℕ :=
  solveQ n N (n * (N * (3 * n + 6) + 4 * n + 10) + 9) (7 * N + 10) (N * (4 * n + 7) + 5)
    (closureCost n N (n * (N + 1)) + 6)

/-! ### Restriction -/

/-- The reference backend implements the operations of the restriction with the solver. -/
theorem restrictSolveOps_refOps {op : GroupOp} (h : restrictSolveOps op) : refOps op := by
  rcases h with h | h | h | h
  · exact Or.inl h
  · subst h; exact Or.inl (Or.inr (Or.inr (Or.inr rfl)))
  · subst h; exact Or.inr (Or.inr (Or.inl rfl))
  · subst h; exact Or.inr (Or.inl rfl)

/-- The cost bound of the restriction reduction with the reference backend, for degree `n`,
window size `m`, group order `N` and `L` generators. -/
def restrictReferenceCost (n m N L : ℕ) : ℕ :=
  restrictCost n m L (1 + solveBound (refQ m N) m N) N N (closureCost m N L + 6)
    (N * (8 * m + 8) + 2 * m + 2 * n + 16) (N * (5 * m + 5) + 11) (closureCost n N (2 * N) + 6)

/-- The reference `generate` on valid generators of a group of order at most `N` is charged at
most `closureCost n N L + 6`, for `L` at least the number of generators. -/
theorem refB_generate_le {n N L : ℕ} {hs : GensData} (hv : GensData.AllValid n hs)
    (hN : Nat.card (GensData.denote n hs) ≤ N) (hL : hs.length ≤ L) :
    refB.call GroupOp.generate (n, hs) (refOracle.run GroupOp.generate (n, hs)) ≤
      closureCost n N L + 6 := by
  show closureCost n (enumerate n hs).length hs.length + 6 ≤ _
  rw [(enumerate_spec hv).2]
  exact Nat.add_le_add_right (closureCost_mono hN hL) 6

/-- **The restriction reduction with the solver and the reference backend: correctness and a
finite cost bound, without an assumed group oracle.** -/
theorem restrict_reference {n : ℕ} {xy : StrData × StrData} {w : WinData} {σd : PermData}
    {gs : GensData} (hw : w.Valid n) (hσ : σd.Valid n) (hgs : GensData.AllValid n gs)
    (hinv : IsInvariant (GensData.denote n gs) (w.denote n)) :
    ∃ (ans : AnswerData Ty.gens) (tr : Trace Signature.empty),
      Runs Ctx.empty.O (referenceSolver.proc Ty.denote)
        ((Programs.restrictProg (fun J => .recur J) (xy, w, σd, n, gs, enumerate n gs)).subst
          refImpl) ans tr ∧
      Trace.localCost tr ≤
        restrictReferenceCost n w.1.length (Nat.card (GensData.denote n gs)) gs.length ∧
      AnsOK refDV n (w.denote n) (σd.denote n) (gs.denote n) (xy.1.denote n) (xy.2.denote n)
        ans := by
  have hen := enumerate_spec hgs
  have hv : InstData.Valid (D := Ty.gens) (xy, w, σd, n, gs, enumerate n gs) refDV :=
    ⟨hw, hσ, ⟨hgs, hen.1⟩, hinv⟩
  have hcard := card_restrictTo_le hinv hw hgs
  have hrv := GensData.allValid_restrictTo hinv hw hgs
  obtain ⟨ans, ⟨tr, hr, hc, hpre⟩, hok, -⟩ := restrict_solve_spec (X := refCtx) (DV := refDV)
    (fun op x hop hx => refOracle_meets_refOps op x (restrictSolveOps_refOps hop) hx)
    (fun op x hop hx => ⟨restrictSolveOps_refOps hop, hx⟩) hv
    (refBounds w.1.length _ _ hcard) (sK := Nat.card (GensData.denote n gs))
    (Bgm := closureCost w.1.length (Nat.card (GensData.denote n gs)) gs.length + 6)
    (Blift := Nat.card (GensData.denote n gs) * (8 * w.1.length + 8) + 2 * w.1.length + 2 * n +
      16)
    (Bker := Nat.card (GensData.denote n gs) * (5 * w.1.length + 5) + 11)
    (Bgn := closureCost n (Nat.card (GensData.denote n gs))
      (2 * Nat.card (GensData.denote n gs)) + 6)
    (refB_generate_le hrv hcard (by simp [GensData.restrictTo]))
    (fun π' => by
      show (enumerate n gs).length * (8 * w.1.length + 8) + 2 * w.1.length + 2 * n + 16 ≤ _
      rw [hen.2])
    (by
      show (enumerate n gs).length * (5 * w.1.length + 5) + 11 ≤ _
      rw [hen.2])
    (by
      show (kerElems (enumerate n gs) w.1).length ≤ _
      exact (List.length_filter_le _ _).trans hen.2.le)
    (fun hs hv' hl hle => refB_generate_le hv' (Subgroup.card_le_of_le hle) (by omega))
  obtain ⟨tr', hr', hc'⟩ := Runs.subst refImpl_implements hr hpre
  refine ⟨ans, tr', hr', ?_, hok⟩
  rw [Trace.cost_empty] at hc'
  refine hc'.trans (hc.trans (le_of_eq ?_))
  rfl

/-! ### Block systems -/

/-- The reference backend implements the operations of the block reduction with the
solver. -/
theorem blockSolveOps_refOps {op : GroupOp} (h : blockSolveOps op) : refOps op := by
  rcases h with h | h | h | h
  · exact Or.inl h
  · subst h; exact Or.inl (Or.inr (Or.inr (Or.inr rfl)))
  · subst h; exact Or.inr (Or.inl rfl)
  · subst h; exact Or.inr (Or.inr (Or.inr rfl))

/-- The work in one coset of the block reduction with the solver: one call per block, whose
window sizes add up to `m`. -/
theorem blockBranchCost_le {Q N n : ℕ} (hN : 0 < N) {w : WinData} {bs : List (List ℕ)}
    (hbs : IsBlockList w bs) :
    blockBranchCost n (fun o => 1 + solveBound Q o.length N) bs ≤
      3 + bs.length * (2 * n + 14) + 5 * w.1.length + 2 * w.1.length * N * Q := by
  have hsum := sum_solveBound (Q := Q) hN bs fun o ho => List.length_pos_iff.2 (hbs.2 o ho)
  have hm : (bs.map List.length).sum = w.1.length := by
    rw [← List.length_flatten]
    exact hbs.1.length_eq
  have key : ∀ l : List (List ℕ),
      (l.map (seqCost n fun o => 1 + solveBound Q o.length N)).sum =
        (l.map fun o => solveBound Q o.length N).sum + l.length * (2 * n + 14) +
          5 * (l.map List.length).sum := by
    intro l
    induction l with
    | nil => simp
    | cons o l ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, ih, seqCost]
      ring
  unfold blockBranchCost
  rw [key, hm]
  rw [hm] at hsum
  nlinarith

/-- The cost bound of the block-system reduction with the reference backend, for degree `n`,
`m` window points in `k` blocks, group order `N`, `L` generators and `R` branches. -/
def blockReferenceCost (n m k N L R : ℕ) : ℕ :=
  3 + blockKernelCost n m k L N (closureCost (n + k) N L + 6) (N * (5 * k + 5) + 11)
      (closureCost n N N + 6) +
    (2 + (N * (N * (N * (6 * n + 12) + 12 * n + 19) + 4) + 7) +
      R * (24 * n + (3 + k * (2 * n + 14) + 5 * m + 2 * m * N * refQ n N) + N + 45) +
      (closureCost n N (R * (N + 1)) + 6) + 19)

/-- **The block-system reduction with the solver and the reference backend: correctness and
a finite cost bound, without an assumed group oracle.** The bound has `R = N / |K|`
branches. -/
theorem blockReduce_reference {n : ℕ} {xy : StrData × StrData} {w : WinData} {σd : PermData}
    {gs : GensData} {bs : List (List ℕ)} (hw : w.Valid n) (hσ : σd.Valid n)
    (hgs : GensData.AllValid n gs) (hinv : IsInvariant (GensData.denote n gs) (w.denote n))
    (hbs : IsBlockList w bs) (hG : PermutesBlocks (GensData.denote n gs) bs) :
    ∃ (ans : AnswerData Ty.gens) (tr : Trace Signature.empty),
      Runs Ctx.empty.O (referenceSolver.proc Ty.denote)
        ((Programs.blockReduceProg (fun J => .recur J) xy w σd (n, gs, enumerate n gs) bs).subst
          refImpl) ans tr ∧
      Trace.localCost tr ≤ blockReferenceCost n w.1.length bs.length
        (Nat.card (GensData.denote n gs)) gs.length
        (Nat.card (GensData.denote n gs) / Nat.card (blockKernel (GensData.denote n gs) bs)) ∧
      AnsOK refDV n (w.denote n) (σd.denote n) (gs.denote n) (xy.1.denote n) (xy.2.denote n)
        ans := by
  have hen := enumerate_spec hgs
  have hNpos : 0 < Nat.card (GensData.denote n gs) := Nat.card_pos
  have hO : MeetsContractOn refDV blockSolveOps refOracle :=
    fun op x hop hx => refOracle_meets_refOps op x (blockSolveOps_refOps hop) hx
  have hPre : ∀ op x, blockSolveOps op → GroupPre refDV op x → refCtx.Pre op x :=
    fun op x hop hx => ⟨blockSolveOps_refOps hop, hx⟩
  -- the extended group and its kernel on the block points
  have hegv : GensData.AllValid (n + bs.length) (extendGens n bs gs) :=
    GensData.allValid_extendTo hw hbs hG hgs
  have hegcard : Nat.card (GensData.denote (n + bs.length) (extendGens n bs gs)) ≤
      Nat.card (GensData.denote n gs) := by
    rw [extendGens, GensData.denote_extendTo hw hbs hG hgs]
    exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_range_dvd _)
  have hel : (extGroup refOracle n bs gs).2.2.length ≤ Nat.card (GensData.denote n gs) := by
    show (enumerate (n + bs.length) (extendGens n bs gs)).length ≤ _
    rw [(enumerate_spec hegv).2]
    exact hegcard
  have hsK : (extKernel refOracle n bs gs).2.1.length ≤ Nat.card (GensData.denote n gs) := by
    show (kerElems (extGroup refOracle n bs gs).2.2 (blockWin n bs.length).1).length ≤ _
    exact (List.length_filter_le _ _).trans hel
  -- the block kernel
  have hKops : ∀ op, blockKernelOps op → blockSolveOps op := by
    intro op hop
    rcases hop with h | h <;> simp [blockSolveOps, blockReduceOps, h]
  obtain ⟨-, -, hKv, hKden⟩ := RunsWithin.blockKernelProg (X := refCtx)
    (body := solveBody Ty.gens Ty.denote) (fun op x hop => hO op x (hKops op hop))
    (fun op x hop => hPre op x (hKops op hop)) hw hbs hG hgs le_rfl le_rfl le_rfl
  have hKcard : (blockKernelModel refOracle n bs gs).2.2.length ≤
      Nat.card (blockKernel (GensData.denote n gs) bs) := by
    rw [← hKden]
    exact length_data_le hKv.2 le_rfl
  have hKN : (blockKernelModel refOracle n bs gs).2.2.length ≤
      Nat.card (GensData.denote n gs) :=
    hKcard.trans (Subgroup.card_le_of_le (blockKernel_le _ _))
  obtain ⟨ans, ⟨tr, hr, hc, hpre⟩, hok, hidx, -⟩ := blockReduce_solve_spec (X := refCtx)
    (DV := refDV) hO hPre hw hσ ⟨hgs, hen.1⟩ hinv hbs hG (refBounds n _ _ le_rfl) hKN
    (Bge := closureCost (n + bs.length) (Nat.card (GensData.denote n gs)) gs.length + 6)
    (Bke := Nat.card (GensData.denote n gs) * (5 * bs.length + 5) + 11)
    (Bgt := closureCost n (Nat.card (GensData.denote n gs)) (Nat.card (GensData.denote n gs)) +
      6)
    (Bcr := Nat.card (GensData.denote n gs) * (Nat.card (GensData.denote n gs) *
      (Nat.card (GensData.denote n gs) * (6 * n + 12) + 12 * n + 19) + 4) + 7)
    (refB_generate_le hegv hegcard (by simp [extendGens]))
    (by
      show (extGroup refOracle n bs gs).2.2.length * (5 * (blockWin n bs.length).1.length + 5) +
        11 ≤ _
      simp only [blockWin, WinData.ofPoints_fst, blockPts, List.length_map, List.length_range]
      gcongr)
    (by
      show closureCost n (blockKernelModel refOracle n bs gs).2.2.length
        ((extKernel refOracle n bs gs).2.1.map (PermData.truncTo n)).length + 6 ≤ _
      rw [List.length_map]
      exact Nat.add_le_add_right (closureCost_mono hKN hsK) 6)
    (by
      show (enumerate n gs).length * ((enumerate n gs).length *
        ((blockKernelModel refOracle n bs gs).2.2.length * (6 * n + 12) + 12 * n + 19) + 4) +
          7 ≤ _
      rw [hen.2]
      gcongr)
    (fun hs hv' hl hle => refB_generate_le hv' (Subgroup.card_le_of_le hle) hl)
  obtain ⟨tr', hr', hc'⟩ := Runs.subst refImpl_implements hr hpre
  refine ⟨ans, tr', hr', ?_, hok⟩
  rw [Trace.cost_empty] at hc'
  refine hc'.trans (hc.trans ?_)
  have hbr := blockBranchCost_le (Q := refQ n (Nat.card (GensData.denote n gs))) (n := n) hNpos
    hbs
  rw [Nat.div_eq_of_eq_mul_left (Nat.card_pos) hidx.symm]
  unfold blockReferenceCost blockKernelCost
  rw [hbs.1.length_eq]
  gcongr
  exacts [hsK, hbr]

end GraphIso.Reference
