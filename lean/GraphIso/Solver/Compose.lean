module

public import GraphIso.Solver.Entry
public import GraphIso.Reductions.RestrictionProg
public import GraphIso.Reductions.BlockKernelProg
public import Mathlib.GroupTheory.Index

/-!
# The phase-5 reductions composed with the solver

The restriction and block-system reductions take their sub-solver as a hypothesis
(`SubSolves`, `SeqSub`). Here the sub-solver is a recursive call of the solver itself
(`fun J => .recur J`, inside `solveBody`), and `solve_spec` discharges the hypothesis.

* `SubSolves.solve`: a recursive call solves every valid instance of degree `n` whose group
  lies in `G₀` and has at most `s` generators, within `1 + solveBound Q m N` for its window
  size `m` and group order `N`.
* `restrict_solve_spec`: the restriction reduction whose sub-call is the solver at the
  window's degree `m`, with backend bounds at degree `m` for the restricted group. The
  restricted group is a quotient of `G`, so the sub-call costs at most `1 + solveBound Q m N`
  for `N = |G|`.
* `blockReduce_solve_spec`: the block-system reduction whose per-block calls are the solver
  at degree `n`, inside each coset of the block kernel.

Both hold against any backend meeting the contracts of the operations involved, with the
charges of the reductions' own backend calls as hypotheses.
-/

@[expose] public section

namespace GraphIso.Solver

open Equiv Pointwise Cost Programs

variable {D : Ty} {X : Ctx (groupSig D)} {DV : ℕ → GensData → D.denote → Prop}

/-- **The solver as a sub-solver**, on instances of degree `n` described by `P`. -/
theorem SubSolves.solve (hO : MeetsContractOn DV solverOps X.O)
    (hPre : ∀ op x, solverOps op → GroupPre DV op x → X.Pre op x)
    {n s : ℕ} {G₀ : Subgroup (Perm (Fin n))} (B : BackendBounds X DV n s G₀)
    {P : InstData D → Prop} {C : InstData D → ℕ}
    (hP : ∀ I, P I → ∃ (xy : StrData × StrData) (w : WinData) (σd : PermData) (gs : GensData)
      (d : D.denote), I = (xy, w, σd, n, gs, d) ∧ InstData.Valid (D := D) I DV ∧
      gs.length ≤ s ∧ GensData.denote n gs ≤ G₀ ∧
      1 + solveBound (solveQ n s B.Borb B.Bstab B.Btr B.Bgen) w.1.length
        (Nat.card (GensData.denote n gs)) ≤ C I) :
    SubSolves X (solveBody D Ty.denote) DV (fun J => .recur J) P C s := by
  intro I hI
  obtain ⟨xy, w, σd, gs, d, rfl, hv, hs, hle, hC⟩ := hP I hI
  obtain ⟨ans, hr, hok, hg⟩ := solve_spec hO hPre B _ _ xy w σd gs d hv hs hle rfl rfl
  exact ⟨ans, (RunsWithin.recur hr).mono hC, hok, hg⟩

/-! ### Restriction -/

/-- The operations of the restriction reduction with the solver as sub-solver. -/
def restrictSolveOps (op : GroupOp) : Prop := solverOps op ∨ restrictOps op

/-- The restricted group has at most `|G|` elements: it is the image of `G`. -/
theorem card_restrictTo_le {n : ℕ} {w : WinData} {gs : GensData}
    (hW : IsInvariant (GensData.denote n gs) (w.denote n)) (hw : w.Valid n)
    (hgs : GensData.AllValid n gs) :
    Nat.card (GensData.denote w.1.length (GensData.restrictTo (WinData.pos n w) w.1 gs)) ≤
      Nat.card (GensData.denote n gs) := by
  rw [GensData.denote_restrictTo hW hw hgs]
  exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_range_dvd _)

/-- **The restriction reduction with the solver as sub-solver.** The sub-call runs at the
window's degree `m`, against backend bounds at degree `m` for the restricted group. -/
theorem restrict_solve_spec (hO : MeetsContractOn DV restrictSolveOps X.O)
    (hPre : ∀ op x, restrictSolveOps op → GroupPre DV op x → X.Pre op x)
    {xy : StrData × StrData} {w : WinData} {σd : PermData} {n : ℕ} {gs : GensData}
    {d : D.denote} (hv : InstData.Valid (D := D) (xy, w, σd, n, gs, d) DV) {s : ℕ}
    (B : BackendBounds X DV w.1.length s
      (GensData.denote w.1.length (GensData.restrictTo (WinData.pos n w) w.1 gs)))
    {sK Bgm Blift Bker Bgn : ℕ}
    (hBgm : X.B.call GroupOp.generate
      (w.1.length, GensData.restrictTo (WinData.pos n w) w.1 gs)
      (X.O.run GroupOp.generate (w.1.length, GensData.restrictTo (WinData.pos n w) w.1 gs)) ≤ Bgm)
    (hBlift : ∀ π' : PermData, X.B.call GroupOp.lift ((n, gs, d), (w, π'))
      (X.O.run GroupOp.lift ((n, gs, d), (w, π'))) ≤ Blift)
    (hBker : X.B.call GroupOp.kernel ((n, gs, d), w) (X.O.run GroupOp.kernel ((n, gs, d), w)) ≤
      Bker)
    (hsK : (X.O.run GroupOp.kernel ((n, gs, d), w)).2.1.length ≤ sK)
    (hBgn : ∀ hs : GensData, GensData.AllValid n hs → hs.length ≤ sK + s →
      GensData.denote n hs ≤ GensData.denote n gs →
      X.B.call GroupOp.generate (n, hs) (X.O.run GroupOp.generate (n, hs)) ≤ Bgn) :
    ∃ ans : AnswerData D,
      RunsWithin X (solveBody D Ty.denote)
        (Programs.restrictProg (fun J => .recur J) (xy, w, σd, n, gs, d)) ans
        (restrictCost n w.1.length gs.length
          (1 + solveBound (solveQ w.1.length s B.Borb B.Bstab B.Btr B.Bgen) w.1.length
            (Nat.card (GensData.denote n gs))) s sK Bgm Blift Bker Bgn) ∧
      AnsOK DV n (w.denote n) (PermData.denote n σd) (GensData.denote n gs) (xy.1.denote n)
        (xy.2.denote n) ans ∧
      ∀ sGen, (∀ hs, GensData.AllValid n hs → GensData.denote n hs ≤ GensData.denote n gs →
          (X.O.run GroupOp.generate (n, hs)).2.1.length ≤ sGen) →
        ∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sGen := by
  have hv' := hv
  obtain ⟨hw, -, hgv, hW⟩ := hv'
  change WinData.Valid n w at hw
  change GroupValid DV n gs d at hgv
  change IsInvariant (GensData.denote n gs) (WinData.denote n w) at hW
  have hrv := GensData.allValid_restrictTo hW hw hgv.1
  have hcard := card_restrictTo_le hW hw hgv.1
  have hsub : SubSolves X (solveBody D Ty.denote) DV (fun J => .recur J)
      (fun J => J = restrictInst X.O (xy, w, σd, n, gs, d) ∧ J.Valid DV)
      (fun _ => 1 + solveBound (solveQ w.1.length s B.Borb B.Bstab B.Btr B.Bgen) w.1.length
        (Nat.card (GensData.denote n gs))) s := by
    refine SubSolves.solve (fun op x hop => hO op x (Or.inl hop))
      (fun op x hop => hPre op x (Or.inl hop)) B ?_
    rintro J ⟨rfl, hJv⟩
    have hpost := hO .generate (w.1.length, GensData.restrictTo (WinData.pos n w) w.1 gs)
      (Or.inl (Or.inr (Or.inr (Or.inr rfl)))) hrv
    have hgenOut := B.genOut _ hrv le_rfl
    have hJ : restrictInst X.O (xy, w, σd, n, gs, d) =
        ((StrData.restrictTo w.1 xy.1, StrData.restrictComp w.1 xy.2 σd),
          WinData.ofPoints w.1.length (List.range w.1.length), PermData.one w.1.length,
          X.O.run GroupOp.generate (w.1.length, GensData.restrictTo (WinData.pos n w) w.1 gs)) :=
      rfl
    rw [hJ] at hJv ⊢
    revert hpost hgenOut hJv
    generalize X.O.run GroupOp.generate (w.1.length, GensData.restrictTo (WinData.pos n w) w.1 gs)
      = G'
    rcases G' with ⟨m', gs', d'⟩
    intro hJv hpost hgenOut
    obtain ⟨hm', -, hden⟩ := hpost
    change m' = w.1.length at hm'
    subst hm'
    change GensData.denote _ gs' = GensData.denote _ _ at hden
    refine ⟨_, _, _, gs', d', rfl, hJv, hgenOut, hden.le, ?_⟩
    simp only [WinData.ofPoints_fst, List.length_range]
    have := solveBound_mono (Q := solveQ w.1.length s B.Borb B.Bstab B.Btr B.Bgen)
      (m := w.1.length) (hden ▸ hcard)
    omega
  exact RunsWithin.restrictProg (fun op x hop => hO op x (Or.inr hop))
    (fun op x hop => hPre op x (Or.inr hop)) hv hsub hBgm hBlift hBker hsK hBgn

/-! ### Block systems -/

/-- The operations of the block-system reduction with the solver as sub-solver. -/
def blockSolveOps (op : GroupOp) : Prop := solverOps op ∨ blockReduceOps op

/-- **The block-system reduction with the solver as sub-solver**: one recursive call per block
inside each coset of the block kernel `K`, which must have at most `s` generators. The number
of cosets `R` satisfies `R |K| = |G|`. -/
theorem blockReduce_solve_spec (hO : MeetsContractOn DV blockSolveOps X.O)
    (hPre : ∀ op x, blockSolveOps op → GroupPre DV op x → X.Pre op x)
    {xy : StrData × StrData} {w : WinData} {σd : PermData} {n : ℕ} {gs : GensData}
    {d : D.denote} {bs : List (List ℕ)} (hw : w.Valid n) (hσ : σd.Valid n)
    (hGv : GroupValid DV n gs d) (hWG : IsInvariant (GensData.denote n gs) (w.denote n))
    (hbs : IsBlockList w bs) (hG : PermutesBlocks (GensData.denote n gs) bs) {s : ℕ}
    (B : BackendBounds X DV n s (GensData.denote n gs))
    (hKs : (blockKernelModel X.O n bs gs).2.1.length ≤ s) {Bge Bke Bgt Bcr Bgen : ℕ}
    (hBge : X.B.call GroupOp.generate (n + bs.length, extendGens n bs gs)
      (extGroup X.O n bs gs) ≤ Bge)
    (hBke : X.B.call GroupOp.kernel (extGroup X.O n bs gs, blockWin n bs.length)
      (extKernel X.O n bs gs) ≤ Bke)
    (hBgt : X.B.call GroupOp.generate (n, (extKernel X.O n bs gs).2.1.map (PermData.truncTo n))
      (blockKernelModel X.O n bs gs) ≤ Bgt)
    (hBcr : X.B.call GroupOp.cosetReps ((n, gs, d), blockKernelModel X.O n bs gs)
      (X.O.run GroupOp.cosetReps ((n, gs, d), blockKernelModel X.O n bs gs)) ≤ Bcr)
    (hB : ∀ hs : GensData, GensData.AllValid n hs →
      hs.length ≤ (X.O.run GroupOp.cosetReps ((n, gs, d), blockKernelModel X.O n bs gs)).length *
        (s + 1) →
      GensData.denote n hs ≤ GensData.denote n gs →
      X.B.call GroupOp.generate (n, hs) (X.O.run GroupOp.generate (n, hs)) ≤ Bgen) :
    ∃ ans : AnswerData D,
      RunsWithin X (solveBody D Ty.denote)
        (Programs.blockReduceProg (fun J => .recur J) xy w σd (n, gs, d) bs) ans
        (3 + blockKernelCost n bs.flatten.length bs.length gs.length
            (extKernel X.O n bs gs).2.1.length Bge Bke Bgt +
          (2 + Bcr + (X.O.run GroupOp.cosetReps ((n, gs, d), blockKernelModel X.O n bs gs)).length *
            (24 * n + blockBranchCost n (fun o => 1 + solveBound
              (solveQ n s B.Borb B.Bstab B.Btr B.Bgen) o.length (Nat.card (GensData.denote n gs)))
              bs + s + 45) + Bgen + 19)) ∧
      AnsOK DV n (w.denote n) (PermData.denote n σd) (GensData.denote n gs) (xy.1.denote n)
        (xy.2.denote n) ans ∧
      (X.O.run GroupOp.cosetReps ((n, gs, d), blockKernelModel X.O n bs gs)).length *
          Nat.card (blockKernel (GensData.denote n gs) bs) = Nat.card (GensData.denote n gs) ∧
      ∀ sGen, (∀ hs, GensData.AllValid n hs → GensData.denote n hs ≤ GensData.denote n gs →
          (X.O.run GroupOp.generate (n, hs)).2.1.length ≤ sGen) →
        ∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sGen := by
  have hKops : ∀ op, blockKernelOps op → blockSolveOps op := by
    intro op hop
    rcases hop with h | h <;> simp [blockSolveOps, blockReduceOps, h]
  obtain ⟨-, -, -, hKden⟩ := RunsWithin.blockKernelProg (X := X)
    (body := solveBody D Ty.denote) (fun op x hop => hO op x (hKops op hop))
    (fun op x hop => hPre op x (hKops op hop)) hw hbs hG hGv.1 hBge hBke hBgt
  have hmax : max s (blockKernelModel X.O n bs gs).2.1.length = s := max_eq_left hKs
  have hKG : GensData.denote n (blockKernelModel X.O n bs gs).2.1 ≤ GensData.denote n gs :=
    hKden ▸ blockKernel_le _ _
  have hsub : SeqSub X (solveBody D Ty.denote) DV (fun J => .recur J) xy n bs
      (fun o => 1 + solveBound (solveQ n s B.Borb B.Bstab B.Btr B.Bgen) o.length
        (Nat.card (GensData.denote n gs))) s
      (max s (blockKernelModel X.O n bs gs).2.1.length)
      (GensData.denote n (blockKernelModel X.O n bs gs).2.1) := by
    refine SubSolves.solve (fun op x hop => hO op x (Or.inl hop))
      (fun op x hop => hPre op x (Or.inl hop)) B ?_
    rintro ⟨xy', w', τ, n', ks', e'⟩ ⟨-, hval, hdeg, -, hlen, hle⟩
    change n' = n at hdeg
    subst hdeg
    refine ⟨xy', w', τ, ks', e', rfl, hval, hmax ▸ hlen, hle.trans hKG, ?_⟩
    show 1 + solveBound _ w'.1.length (Nat.card (GensData.denote n' ks')) ≤
      1 + solveBound _ w'.1.length _
    exact Nat.add_le_add_left (solveBound_mono (Subgroup.card_le_of_le (hle.trans hKG))) 1
  obtain ⟨ans, hr, hok, hidx, hg⟩ := RunsWithin.blockReduceProg
    (fun op x hop => hO op x (Or.inr hop)) (fun op x hop => hPre op x (Or.inr hop))
    hw hσ hGv hWG hbs hG hBge hBke hBgt hsub hBcr (by rw [hmax]; exact hB)
  rw [hmax] at hr
  exact ⟨ans, hr, hok, hidx, hg⟩

end GraphIso.Solver
