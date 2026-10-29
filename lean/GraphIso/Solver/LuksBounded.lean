module

public import GraphIso.Solver.Luks
public import GraphIso.Luks.Bounded

/-!
# String isomorphism for groups with bounded simple sections

* `solve_luks_bounded`: **for a group all of whose simple sections have order at most `k`, cost
  at most `6640 (n + 1)^{9 k³ + 9 k² + 36 k + 8} + 60 L (n + 1)²`**, with no assumed group oracle
  (`primBounded_of_boundedSections`, and `luksSimsCost_le_pow` for
  `c = 3 k³ + 3 k² + 12 k + 1`, so `3 c + 5 = 9 k³ + 9 k² + 36 k + 8`).
-/

@[expose] public section

namespace GraphIso.Sims

open Equiv Cost Programs Solver Luks

/-- **String isomorphism for groups with bounded composition factors in polynomial time**: with
Luks's strategy and the Schreier–Sims backend, for a group all of whose simple sections have
order at most `k`, the cost is at most `6640 (n + 1)^{9 k³ + 9 k² + 36 k + 8} + 60 L (n + 1)²`
for `L` input generators. -/
theorem solve_luks_bounded {n k : ℕ} {xy : StrData × StrData} {w : WinData} {σd : PermData}
    {gs : GensData} (hk : Groups.BoundedSections k (GensData.denote n gs)) (hw : w.Valid n)
    (hσ : σd.Valid n) (hgs : GensData.AllValid n gs)
    (hinv : IsInvariant (GensData.denote n gs) (w.denote n)) :
    ∃ (ans : AnswerData Ty.unit) (tr : Trace Signature.empty),
      Runs Ctx.empty.O (luksSolver.proc Ty.denote)
        ((solveEntry Ty.unit Ty.denote (xy, w, σd, n, gs)).subst ssImpl) ans tr ∧
      Trace.localCost tr ≤
        6640 * (n + 1) ^ (9 * k ^ 3 + 9 * k ^ 2 + 36 * k + 8) + 60 * gs.length * (n + 1) ^ 2 ∧
      AnsOK ssDV n (w.denote n) (σd.denote n) (gs.denote n) (xy.1.denote n) (xy.2.denote n)
        ans := by
  obtain ⟨ans, tr, hr, hc, hok⟩ := solve_luks (primBounded_of_boundedSections hk) hw hσ hgs hinv
  refine ⟨ans, tr, hr, hc.trans ?_, hok⟩
  have := luksSimsCost_le_pow (L := gs.length) (c := 3 * k ^ 3 + 3 * k ^ 2 + 12 * k + 1)
    (by omega) (WinData.length_le hw)
  rwa [show 3 * (3 * k ^ 3 + 3 * k ^ 2 + 12 * k + 1) + 5 = 9 * k ^ 3 + 9 * k ^ 2 + 36 * k + 8
    by ring] at this

end GraphIso.Sims
