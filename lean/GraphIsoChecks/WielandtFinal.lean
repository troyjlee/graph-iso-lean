module

public import GraphIso.Wielandt.Final
import all Init.Data.Array.Basic
import all Init.Data.List.Sort.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Mathlib.Data.List.Sort

/-!
# Checks of stage 16b: the unconditional theorems

`PLAN-16.md` §5. As before, the checks are instantiations of the library, with kernel `decide`
for numbers.

* **The thresholds:** `ℓT 181 = 2119936 > 2²¹`; `sq_le_two_pow` at `L = 21`; `jq 1 = 1024`.
* **A negative control:** for every `C'`, `Tq m ≤ C' (λ(m) + 1)` fails at `m = 2^{C'}`, so
  milestone 14's `QPHyp` cannot hold at `Tq`: the generalization `QPHypJ` is needed.
* **The final hypothesis and headlines**, restated: `qpHypJ_final`, and `gi_simpleGraph_final`
  specialized to the empty graphs on `Fin 3`, which are isomorphic.
-/

@[expose] public section

namespace GraphIsoChecks.WielandtFinal

open Equiv GraphIso GraphIso.Cost GraphIso.Graph GraphIso.Main GraphIso.Recursion GraphIso.Wielandt
  GraphIso.Pyber

/-! ### The thresholds -/

example : ℓT 181 = 2119936 ∧ 2 ^ 21 < ℓT 181 := by
  decide +kernel

example : 1024 * (21 + 1) ^ 2 + 6 ≤ 2 ^ 21 := sq_le_two_pow le_rfl

example : jq 1 = 1024 := by
  decide +kernel

/-! ### A negative control -/

/-- **`QPHyp`'s linear bound fails for `Tq`:** for every `C'`, at `m = 2^{C'}`,
`Tq m = 256 (C' + 1)² > C' (C' + 1)`. -/
theorem not_tle_Tq (C' : ℕ) : ¬∀ m, Tq m ≤ C' * (lam m + 1) := by
  intro h
  have h1 := h (2 ^ C')
  have hl : lam (2 ^ C') = C' := Nat.log_pow (by norm_num) C'
  unfold Tq at h1
  rw [show Nat.log 2 (2 ^ C') = C' from hl, hl] at h1
  nlinarith

theorem not_qpHyp_Tq (K : ℕ → ℕ) (C C' : ℕ) : ¬QPHyp K Tq C C' := fun h =>
  not_tle_Tq C' h.tle

/-! ### The final hypothesis and headlines -/

example : QPHypJ Kpy Tq 192 181 jq := qpHypJ_final

/-- The final theorem on the empty graphs on `Fin 3`: some run returns a nonempty answer. -/
example : ∃ c, ∃ (r : Option (PermData × GensData)) (tr : Cost.Trace Cost.Signature.empty),
    Cost.Runs Cost.Ctx.empty.O ((qpSolver 192 181).proc Ty.denote)
      ((giEntry Ty.unit Ty.denote (3, GraphData.ofSimpleGraph (⊥ : SimpleGraph (Fin 3)),
        GraphData.ofSimpleGraph (⊥ : SimpleGraph (Fin 3)))).subst Sims.ssImpl) r tr ∧
      Cost.Trace.localCost tr ≤ 2 ^ (c * (lam 3 + 1) ^ 8) ∧ r ≠ none := by
  obtain ⟨c, hc⟩ := gi_simpleGraph_final
  obtain ⟨r, tr, hr, hcost, hnone, -⟩ := hc (⊥ : SimpleGraph (Fin 3)) ⊥
  refine ⟨c, r, tr, hr, hcost, fun h => ?_⟩
  exact (hnone.mp h).false (SimpleGraph.Iso.refl)

end GraphIsoChecks.WielandtFinal
