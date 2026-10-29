module

public import GraphIso.Main.QPJ
public import GraphIso.Pyber.Discharge
public import GraphIso.Wielandt.Bound

/-!
# Graph isomorphism in quasipolynomial time, with no hypothesis

Stage 16b (`PLAN-16.md` §5). The interfaces of milestone 12 are discharged: `AltQuotientIso Kpy`
(Pyber's Lemma 12, milestone 15, `Kpy n = 192 (λ(n) + 1)⁵`) and `TransitivityBound Tq`
(stage 16a, `Tq m = 256 (λ(m) + 1)²`). With the depth bound `jq n₀ = Tq (2 n₀)`, milestone 14's
generalized hypothesis holds: **`qpHypJ_final : QPHypJ Kpy Tq 192 181 jq`**.

* `Tq` is monotone, so `supTo Tq m ≤ Tq k` for `m ≤ k` (`supTo_Tq_le`).
* **`TBelow Tq (ℓT 181)`** (`tBelow_Tq`): above `ℓT 181 = 64 · 182² > 2²¹`, `λ(m) ≥ 21` and
  `4 Tq m + 6 = 1024 (λ(m) + 1)² + 6 ≤ 2^{λ(m)} ≤ m` (`sq_le_two_pow`).
* `jq ∈ PLB λ 5` (`jq_plb`): `Tq (2n) ≤ 1024 (λ(n) + 1)²`.

**The unconditional headlines** (`mainSolve_final`, `giSolve_final`,
`gi_simpleGraph_final`) are `mainSolve_qp_exp`, `giSolve_qp_exp` and `gi_qp_simpleGraph` of
milestone 14 at the programs `thrQP 192 181` and `qpSolver 192 181`, with no hypothesis: some
`c` bounds the cost by `genCost N |gs| + 2^{c (λ(N) + 1)⁸}` (respectively the local cost by
`2^{c (λ(n) + 1)⁸}` on graphs on `n` points), with correct answers.
-/

@[expose] public section

namespace GraphIso.Wielandt

open Equiv Pointwise Cost GraphIso GraphIso.Graph GraphIso.Recursion GraphIso.Main Sims
  GraphIso.Pyber

/-! ### `Tq` -/

theorem Tq_mono : Monotone Tq := fun _ _ h =>
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right (Nat.log_mono_right h) 1) 2)

/-- `supTo Tq m ≤ Tq k` for `m ≤ k`. -/
theorem supTo_Tq_le {m k : ℕ} (h : m ≤ k) : supTo Tq m ≤ Tq k :=
  supTo_le fun _ hi => Tq_mono (hi.trans h)

/-- `1024 (L + 1)² + 6 ≤ 2^L` for `L ≥ 21`. -/
theorem sq_le_two_pow {L : ℕ} (hL : 21 ≤ L) : 1024 * (L + 1) ^ 2 + 6 ≤ 2 ^ L := by
  induction L, hL using Nat.le_induction with
  | base => norm_num
  | succ L hL ih =>
    have h : 1024 * (L + 1 + 1) ^ 2 + 6 ≤ 2 * (1024 * (L + 1) ^ 2 + 6) := by nlinarith
    rw [pow_succ 2 L]
    omega

/-- **`TBelow` for `Tq`** above `ℓT 181 = 64 · 182²`. -/
theorem tBelow_Tq : TBelow Tq (ℓT 181) := by
  intro m hm
  have hm' : 2 ^ 21 ≤ m := by
    unfold ℓT at hm
    omega
  have hL : 21 ≤ Nat.log 2 m := Nat.le_log_of_pow_le (by norm_num) hm'
  have hp : 2 ^ Nat.log 2 m ≤ m := Nat.pow_log_le_self 2 (by omega)
  have h1 : supTo Tq m ≤ 256 * (Nat.log 2 m + 1) ^ 2 := supTo_Tq_le (le_refl m)
  have h2 := sq_le_two_pow hL
  omega

/-- **The depth bound** `jq n₀ = Tq (2 n₀)`. -/
def jq (n₀ : ℕ) : ℕ := Tq (2 * n₀)

/-- `jq ∈ PLB λ 5`: `Tq (2n) ≤ 1024 (λ(n) + 1)² ≤ 1024 (λ(n) + 1)⁵`. -/
theorem jq_plb : Growth.PLB lam 5 jq := by
  refine ⟨1024, fun n => ?_⟩
  have h : lam (2 * n) ≤ lam n + 1 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [lam]
    · have := Growth.lt_two_pow_lam n
      have h2 : 2 * n < 2 ^ (lam n + 2) := by rw [pow_succ]; omega
      exact Nat.lt_succ_iff.1 (Nat.log_lt_of_lt_pow (by omega) h2)
  show 256 * (lam (2 * n) + 1) ^ 2 ≤ 1024 * (lam n + 1) ^ 5
  calc 256 * (lam (2 * n) + 1) ^ 2 ≤ 256 * (2 * (lam n + 1)) ^ 2 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
    _ = 1024 * (lam n + 1) ^ 2 := by ring
    _ ≤ 1024 * (lam n + 1) ^ 5 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by norm_num))

/-! ### The hypothesis holds -/

/-- **Every interface hypothesis holds:** `QPHypJ Kpy Tq 192 181 jq`. -/
theorem qpHypJ_final : QPHypJ Kpy Tq 192 181 jq :=
  ⟨altQuotientIso_pyber, Kpy_mono, Kpy_le_lam, transitivityBound_quad, tBelow_Tq,
    fun _ _ hm => supTo_Tq_le hm⟩

/-! ### The unconditional headlines -/

/-- **The main procedure in time `2^{O((log N)⁸)}`, with no hypothesis.** There is `c` such that
on every valid plain instance (window `w`, permutation `σd`, generators `gs` on `N` points, `w`
invariant under the group they generate), `mainEntry (thrQP 192 181)` returns a correct answer
(`AnsOK`) within `genCost N |gs| + 2^{c (λ(N) + 1)⁸}`. -/
theorem mainSolve_final :
    ∃ c, ∀ {xy : StrData × StrData} {w : WinData} {σd : PermData} {N : ℕ} {gs : GensData},
      w.Valid N → σd.Valid N → GensData.AllValid N gs →
      IsInvariant (GensData.denote N gs) (w.denote N) →
      ∃ ans : AnswerData Ty.unit,
        RunsWithin ssCtx (mainBody (thrQP 192 181) Ty.denote)
          (mainEntry Ty.unit Ty.denote (xy, w, σd, N, gs)) ans
          (genCost N gs.length + 2 ^ (c * (lam N + 1) ^ 8)) ∧
        AnsOK ssDV N (w.denote N) (σd.denote N) (gs.denote N) (xy.1.denote N)
          (xy.2.denote N) ans := by
  obtain ⟨c, hc⟩ := mainSolve_qp_expJ 192 181 jq_plb
  exact ⟨c, hc qpHypJ_final⟩

/-- **Graph isomorphism in time `2^{O((log n)⁸)}`, with no hypothesis.** There is `c` such that
on valid graph data `X`, `Y` on `n` points (of any degree), the closed entry at `qpSolver 192 181`
(Schreier–Sims substituted, no oracle) returns a `GICosetOK` result with local cost at most
`2^{c (λ(n) + 1)⁸}`. -/
theorem giSolve_final :
    ∃ c, ∀ {Δ n : ℕ} {X Y : GraphData}, X.ValidD Δ n → Y.ValidD Δ n →
      ∃ (r : Option (PermData × GensData)) (tr : Trace Signature.empty),
        Runs Ctx.empty.O ((qpSolver 192 181).proc Ty.denote)
          ((giEntry Ty.unit Ty.denote (n, X, Y)).subst ssImpl) r tr ∧
        Trace.localCost tr ≤ 2 ^ (c * (lam n + 1) ^ 8) ∧ GICosetOK n X Y r := by
  obtain ⟨c, hc⟩ := giSolve_qp_expJ 192 181 jq_plb
  exact ⟨c, hc qpHypJ_final⟩

/-- **Graph isomorphism of simple graphs in time `2^{O((log n)⁸)}`, with no hypothesis.** There
is `c` such that for simple graphs `G`, `H` on `Fin n`, the closed entry at `qpSolver 192 181`
returns `r` with local cost at most `2^{c (λ(n) + 1)⁸}`; `r = none` exactly when `G` and `H` are
not isomorphic, and `r = some (τ, hs)` gives valid data of a permutation and of generators such
that the coset `τ • ⟨hs⟩` is exactly the set of the permutations underlying the isomorphisms
`G ≃g H`. -/
theorem gi_simpleGraph_final :
    ∃ c, ∀ {n : ℕ} (G H : SimpleGraph (Fin n)) [DecidableRel G.Adj] [DecidableRel H.Adj],
      ∃ (r : Option (PermData × GensData)) (tr : Trace Signature.empty),
        Runs Ctx.empty.O ((qpSolver 192 181).proc Ty.denote)
          ((giEntry Ty.unit Ty.denote
            (n, GraphData.ofSimpleGraph G, GraphData.ofSimpleGraph H)).subst ssImpl) r tr ∧
        Trace.localCost tr ≤ 2 ^ (c * (lam n + 1) ^ 8) ∧
        (r = none ↔ IsEmpty (G ≃g H)) ∧
        ∀ τ hs, r = some (τ, hs) → τ.Valid n ∧ GensData.AllValid n hs ∧
          {φ : Perm (Fin n) | ∃ e : G ≃g H, e.toEquiv = φ} =
            PermData.denote n τ • (GensData.denote n hs : Set (Perm (Fin n))) := by
  obtain ⟨c, hc⟩ := gi_qp_simpleGraphJ 192 181 jq_plb
  exact ⟨c, hc qpHypJ_final⟩

end GraphIso.Wielandt
