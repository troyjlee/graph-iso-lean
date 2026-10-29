module

public import GraphIso.Pyber.Lemma12
public import GraphIso.Main.GraphQP

/-!
# The discharge of `AltQuotientIso`

Stage 15d. Pyber's Lemma 12 gives `AltQuotientIso Kpy` with `Kpy n = 192 (λ(n) + 1)⁵`, monotone.
So the interface hypotheses of milestone 14 reduce to Wielandt's bound:

* **`qpHyp_pyber`**: `TransitivityBound T` and `T m ≤ C' (λ(m) + 1)` give `QPHyp Kpy T 192 C'`.
* **The headlines under Wielandt's bound alone** (`mainSolve_qp_exp_pyber`,
  `giSolve_qp_exp_pyber`, `gi_qp_simpleGraph_pyber`): the milestone 14 theorems
  `mainSolve_qp_exp`, `giSolve_qp_exp` and `gi_qp_simpleGraph` at `C = 192`, with `QPHyp`
  replaced by its `TransitivityBound` part.

`TransitivityBound T` with `T m ≤ C' (λ(m) + 1)` is Wielandt's bound. **Historical:** milestone
16 was planned to prove it, and did not. The completed route proves the weaker
`TransitivityBound Tq` with `Tq m = 256 (λ(m) + 1)²` (`transitivityBound_quad`), for which
`QPHyp` fails (`not_qpHyp_Tq`, `GraphIsoChecks/WielandtFinal.lean`), and generalizes milestone
14's analysis to `QPHypJ`: `qpHypJ_final` and the unconditional `mainSolve_final`,
`giSolve_final` and `gi_simpleGraph_final` (`GraphIso/Wielandt/Final.lean`). The theorems here
still take a linear `TransitivityBound` as their hypothesis, which is not discharged.
-/

@[expose] public section

namespace GraphIso.Pyber

open Equiv Pointwise Cost GraphIso GraphIso.Graph GraphIso.Recursion GraphIso.Main Sims

/-- `Kpy n ≤ 192 (λ(n) + 1)⁵`, with milestone 14's `lam = Nat.log 2`. -/
theorem Kpy_le_lam (n : ℕ) : Kpy n ≤ 192 * (lam n + 1) ^ 5 :=
  le_rfl

/-- **The reduction of `QPHyp` to Wielandt's bound:** under `TransitivityBound T` with
`T m ≤ C' (λ(m) + 1)`, `QPHyp Kpy T 192 C'` holds. -/
theorem qpHyp_pyber {T : ℕ → ℕ} {C' : ℕ} (hT : AltQuot.TransitivityBound T)
    (htle : ∀ m, T m ≤ C' * (lam m + 1)) : QPHyp Kpy T 192 C' :=
  ⟨altQuotientIso_pyber, Kpy_mono, Kpy_le_lam, hT, htle⟩

/-- **`mainSolve_qp_exp` under Wielandt's bound alone:** for every `C'` there is `c` such that
for every `T` with `TransitivityBound T` and `T m ≤ C' (λ(m) + 1)`, on every valid plain
instance, `mainEntry (thrQP 192 C')` returns a correct answer within
`genCost N |gs| + 2^{c (λ(N) + 1)⁸}`. -/
theorem mainSolve_qp_exp_pyber (C' : ℕ) :
    ∃ c, ∀ {T : ℕ → ℕ}, AltQuot.TransitivityBound T → (∀ m, T m ≤ C' * (lam m + 1)) →
      ∀ {xy : StrData × StrData} {w : WinData} {σd : PermData} {N : ℕ} {gs : GensData},
        w.Valid N → σd.Valid N → GensData.AllValid N gs →
        IsInvariant (GensData.denote N gs) (w.denote N) →
        ∃ ans : AnswerData Ty.unit,
          RunsWithin ssCtx (mainBody (thrQP 192 C') Ty.denote)
            (mainEntry Ty.unit Ty.denote (xy, w, σd, N, gs)) ans
            (genCost N gs.length + 2 ^ (c * (lam N + 1) ^ 8)) ∧
          AnsOK ssDV N (w.denote N) (σd.denote N) (gs.denote N) (xy.1.denote N)
            (xy.2.denote N) ans := by
  obtain ⟨c, hc⟩ := mainSolve_qp_exp 192 C'
  exact ⟨c, fun hT htle => hc (qpHyp_pyber hT htle)⟩

/-- **`giSolve_qp_exp` under Wielandt's bound alone:** for every `C'` there is `c` such that for
every `T` with `TransitivityBound T` and `T m ≤ C' (λ(m) + 1)`: on valid graph data `X`, `Y` on
`n` points, the closed entry at `thrQP 192 C'` returns a `GICosetOK` result with local cost at
most `2^{c (λ(n) + 1)⁸}`. -/
theorem giSolve_qp_exp_pyber (C' : ℕ) :
    ∃ c, ∀ {T : ℕ → ℕ}, AltQuot.TransitivityBound T → (∀ m, T m ≤ C' * (lam m + 1)) →
      ∀ {Δ n : ℕ} {X Y : GraphData}, X.ValidD Δ n → Y.ValidD Δ n →
      ∃ (r : Option (PermData × GensData)) (tr : Trace Signature.empty),
        Runs Ctx.empty.O ((qpSolver 192 C').proc Ty.denote)
          ((giEntry Ty.unit Ty.denote (n, X, Y)).subst ssImpl) r tr ∧
        Trace.localCost tr ≤ 2 ^ (c * (lam n + 1) ^ 8) ∧ GICosetOK n X Y r := by
  obtain ⟨c, hc⟩ := giSolve_qp_exp 192 C'
  exact ⟨c, fun hT htle => hc (qpHyp_pyber hT htle)⟩

/-- **Graph isomorphism of simple graphs in time `2^{O((log n)⁸)}`, under Wielandt's bound
alone.** For every `C'` there is `c` such that for every `T` with `TransitivityBound T` and
`T m ≤ C' (λ(m) + 1)`: for simple graphs `G`, `H` on `Fin n`, the closed entry at
`thrQP 192 C'` returns `r` with local cost at most `2^{c (λ(n) + 1)⁸}`; `r = none` exactly when
`G` and `H` are not isomorphic, and `r = some (τ, hs)` gives valid data of a permutation and of
generators such that the coset `τ • ⟨hs⟩` is exactly the set of the permutations underlying the
isomorphisms `G ≃g H`. -/
theorem gi_qp_simpleGraph_pyber (C' : ℕ) :
    ∃ c, ∀ {T : ℕ → ℕ}, AltQuot.TransitivityBound T → (∀ m, T m ≤ C' * (lam m + 1)) →
      ∀ {n : ℕ} (G H : SimpleGraph (Fin n)) [DecidableRel G.Adj] [DecidableRel H.Adj],
      ∃ (r : Option (PermData × GensData)) (tr : Trace Signature.empty),
        Runs Ctx.empty.O ((qpSolver 192 C').proc Ty.denote)
          ((giEntry Ty.unit Ty.denote
            (n, GraphData.ofSimpleGraph G, GraphData.ofSimpleGraph H)).subst ssImpl) r tr ∧
        Trace.localCost tr ≤ 2 ^ (c * (lam n + 1) ^ 8) ∧
        (r = none ↔ IsEmpty (G ≃g H)) ∧
        ∀ τ hs, r = some (τ, hs) → τ.Valid n ∧ GensData.AllValid n hs ∧
          {φ : Perm (Fin n) | ∃ e : G ≃g H, e.toEquiv = φ} =
            PermData.denote n τ • (GensData.denote n hs : Set (Perm (Fin n))) := by
  obtain ⟨c, hc⟩ := gi_qp_simpleGraph 192 C'
  exact ⟨c, fun hT htle => hc (qpHyp_pyber hT htle)⟩

end GraphIso.Pyber
