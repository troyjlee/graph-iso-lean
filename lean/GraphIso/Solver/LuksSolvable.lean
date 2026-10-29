module

public import GraphIso.Solver.Luks
public import GraphIso.Luks.Solvable

/-!
# String isomorphism for solvable groups

* `solve_luks_solvable`: **for a solvable group whose order has at most `s + 1` prime
  divisors, cost at most `6640 (n + 1)^{36 s + 8} + 60 L (n + 1)²`**, with no assumed group
  oracle (`primBounded_of_isSolvable`, and `luksSimsCost_le_pow` for `c = 12 s + 1`). For
  `s = 0` this is the bound of `solve_luks_nilpotent`.
-/

@[expose] public section

namespace GraphIso.Sims

open Equiv Cost Programs Solver Luks

/-- **String isomorphism for solvable groups in polynomial time**: with Luks's strategy and
the Schreier–Sims backend, for a solvable group whose order has at most `s + 1` prime divisors,
the cost is at most `6640 (n + 1)^{36 s + 8} + 60 L (n + 1)²` for `L` input generators. -/
theorem solve_luks_solvable {n s : ℕ} {xy : StrData × StrData} {w : WinData} {σd : PermData}
    {gs : GensData} (hsol : Group.IsSolvable (GensData.denote n gs))
    (hs : (Nat.card (GensData.denote n gs)).primeFactors.card ≤ s + 1) (hw : w.Valid n)
    (hσ : σd.Valid n) (hgs : GensData.AllValid n gs)
    (hinv : IsInvariant (GensData.denote n gs) (w.denote n)) :
    ∃ (ans : AnswerData Ty.unit) (tr : Trace Signature.empty),
      Runs Ctx.empty.O (luksSolver.proc Ty.denote)
        ((solveEntry Ty.unit Ty.denote (xy, w, σd, n, gs)).subst ssImpl) ans tr ∧
      Trace.localCost tr ≤ 6640 * (n + 1) ^ (36 * s + 8) + 60 * gs.length * (n + 1) ^ 2 ∧
      AnsOK ssDV n (w.denote n) (σd.denote n) (gs.denote n) (xy.1.denote n) (xy.2.denote n)
        ans := by
  obtain ⟨ans, tr, hr, hc, hok⟩ :=
    solve_luks (primBounded_of_isSolvable hsol hs) hw hσ hgs hinv
  refine ⟨ans, tr, hr, hc.trans ?_, hok⟩
  have := luksSimsCost_le_pow (L := gs.length) (c := 12 * s + 1) (by omega)
    (WinData.length_le hw)
  rwa [show 3 * (12 * s + 1) + 5 = 36 * s + 8 by ring] at this

end GraphIso.Sims
