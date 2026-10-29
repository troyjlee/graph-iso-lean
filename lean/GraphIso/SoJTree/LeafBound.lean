module

public import GraphIso.SoJTree.Trees
public import GraphIso.SoJTree.LeafStab

/-!
# The cost of a leaf stabilizer for the leaves of Split-or-Johnson

Stage 14d (`PLAN-14.md` §8): the cost `leafStabCost` of `leafStabProg`
(`GraphIso/SoJTree/LeafStab.lean`) depends on the size `outSize o₀` of the leaf data. The leaves
the tree programs produce are small (`sojProg_outSize`: at most `outB m t`), so for them the
cost is polynomial.

* `leafStabCost_le_of_outSize`: for leaves of size at most `S`, `leafStabCost` is at most
  `1000 (N + k + |gs| + r + S + 2)^8`, plus the stabilizer and transversal terms
  `sS (11N + 13) + L (11N + 14)` and the four backend charges.
* `RunsWithin.leafStabProg_of_outSize`: `leafStabProg` within that bound, for `outSize o₀ ≤ S`.
* `RunsWithin.leafStabProg_sojLeaf` (**M4's bound**): for a leaf `o₀` of `sojProg` on the `k`
  listed points with a colouring `c` preserved by `ψ(G)` (and `k ≤ 2t`), `leafStabProg` runs
  within the bound with `S = outB k t`, and the orbit size `r` is at most the count of
  `soj (colOf k c) t`.
-/

@[expose] public section

namespace GraphIso.SoJTree

open Equiv Cost GraphIso GraphIso.Programs GraphIso.SplitJohnson GraphIso.SoJProg Pointwise

/-- **`leafStabCost` is polynomial in the size of the leaf.** -/
theorem leafStabCost_le_of_outSize {N k s g r sS L Bge Bst Btr Bgt S : ℕ} (hs : s ≤ S) :
    leafStabCost N k s g r sS L Bge Bst Btr Bgt ≤
      1000 * (N + k + g + r + S + 2) ^ 8 + sS * (11 * N + 13) + L * (11 * N + 14) +
        Bge + Bst + Btr + Bgt := by
  set P := N + k + g + r + S + 2 with hP
  have hA : actOutCost k s ≤ 150 * P ^ 3 := by
    refine (actOutCost_le k s).trans ?_
    have h₁ : (k + 1) * (s + 1) ^ 2 ≤ P * P ^ 2 :=
      Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (by omega) 2)
    have e : P * P ^ 2 = P ^ 3 := by ring
    have e' : 150 * (k + 1) * (s + 1) ^ 2 = 150 * ((k + 1) * (s + 1) ^ 2) := by ring
    omega
  have hE : outEqCost k s ≤ 200 * P ^ 5 := by
    refine (outEqCost_le k s).trans ?_
    have h₁ : (k + 1) ^ 2 * (s + 1) ^ 3 ≤ P ^ 2 * P ^ 3 :=
      Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) 2) (Nat.pow_le_pow_left (by omega) 3)
    have e : P ^ 2 * P ^ 3 = P ^ 5 := by ring
    have e' : 200 * (k + 1) ^ 2 * (s + 1) ^ 3 = 200 * ((k + 1) ^ 2 * (s + 1) ^ 3) := by ring
    omega
  have hP1 : 1 ≤ P := by omega
  have h : leafStabCost N k s g r sS L Bge Bst Btr Bgt ≤
      P * (12 * P + 12) + ((P + 1) * (P * (150 * P ^ 3 + P * (200 * P ^ 5 + 13) + 20) + 19) +
        P * (4 * P + 7) + P + 14) + (P * (6 * P + 21 * P + P + 25) + P + 3 * P + 6 +
          sS * (11 * N + 13) + L * (11 * N + 14) + Bge + Bst + Btr + Bgt + 20) + P + 5 := by
    unfold leafStabCost orbitCost orbitStabCost extIdxGensCost
    gcongr <;> omega
  have p8 : ∀ i ≤ 8, P ^ i ≤ P ^ 8 := fun i hi => Nat.pow_le_pow_right hP1 hi
  have q₀ := p8 0 (by norm_num)
  have q₁ := p8 1 (by norm_num)
  have q₂ := p8 2 (by norm_num)
  have q₃ := p8 3 (by norm_num)
  have q₄ := p8 4 (by norm_num)
  have q₅ := p8 5 (by norm_num)
  have q₆ := p8 6 (by norm_num)
  have q₇ := p8 7 (by norm_num)
  clear_value P
  ring_nf at h q₀ q₁ ⊢
  omega

section Spec

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}
  {N : ℕ} {w : WinData} {gs : GensData}

/-- **`leafStabProg` within a polynomial bound**, for leaf data of size at most `S`. -/
theorem RunsWithin.leafStabProg_of_outSize (hO : MeetsContractOn DV orbitStabOps X.O)
    (hPre : ∀ op x, orbitStabOps op → GroupPre DV op x → X.Pre op x)
    (hgs : GensData.AllValid N gs) (hw : w.Valid N)
    (hW : IsInvariant (GensData.denote N gs) (w.denote N)) {o₀ : OutD} {S : ℕ}
    (hS : outSize o₀ ≤ S) {r : ℕ} {imgs : List (List ℕ)}
    (hr : leafR w.1.length (WinData.pos N w) w.1 gs o₀ = r)
    (himgs : leafImgs w.1.length (WinData.pos N w) w.1 gs o₀ = imgs) {Bge Bst Btr Bgt : ℕ}
    (hBge : X.B.call GroupOp.generate (N + r, os_extGens N r gs imgs)
      (osGroup X.O N r gs imgs) ≤ Bge)
    (hBst : X.B.call GroupOp.stabilizer (osGroup X.O N r gs imgs, N)
      (osStab X.O N r gs imgs) ≤ Bst)
    (hBtr : X.B.call GroupOp.orbitTransversal (osGroup X.O N r gs imgs, N)
      (osTrans X.O N r gs imgs) ≤ Btr)
    (hBgt : X.B.call GroupOp.generate (N, (osStab X.O N r gs imgs).2.1.map (PermData.truncTo N))
      (orbitStabModel X.O N r gs imgs).1 ≤ Bgt) :
    RunsWithin X body (SoJTree.leafStabProg N w.1.length (WinData.pos N w) w.1 gs o₀)
      (leafStabModel X.O N w.1.length (WinData.pos N w) w.1 gs o₀)
      (1000 * (N + w.1.length + gs.length + r + S + 2) ^ 8 +
        (osStab X.O N r gs imgs).2.1.length * (11 * N + 13) +
        (osTrans X.O N r gs imgs).length * (11 * N + 14) + Bge + Bst + Btr + Bgt) :=
  (RunsWithin.leafStabProg (body := body) hO hPre hgs hw hW o₀ hr himgs hBge hBst hBtr
    hBgt).1.mono (leafStabCost_le_of_outSize hS)

/-- **M4's bound for the leaves of Split-or-Johnson.** For a leaf `o₀` of `sojProg` on the
`k = |w.1|` listed points (`k ≤ 2t`) with a colouring `colOf k c` preserved by `ψ(G)`,
`leafStabProg` runs within `1000 (N + k + |gs| + r + outB k t + 2)^8`, plus the stabilizer and
transversal terms and the four backend charges, and the orbit size `r` is at most the count of
`soj (colOf k c) t`. -/
theorem RunsWithin.leafStabProg_sojLeaf (hO : MeetsContractOn DV orbitStabOps X.O)
    (hPre : ∀ op x, orbitStabOps op → GroupPre DV op x → X.Pre op x)
    (hgs : GensData.AllValid N gs) (hw : w.Valid N)
    (hW : IsInvariant (GensData.denote N gs) (w.denote N)) {c : Array ℕ} {t : ℕ}
    (hmt : w.1.length ≤ 2 * t)
    (hc : ∀ g, relab2 (restrictHom hW (WinData.reindex hw) g) (colOf w.1.length c) =
      colOf w.1.length c) {o₀ : OutD}
    (ho : o₀ ∈ worklistD (stepD w.1.length t) tr_rank (tr_size w.1.length t)
      (splitI (tr_sojItems w.1.length t c)).2 (splitI (tr_sojItems w.1.length t c)).1)
    {r : ℕ} {imgs : List (List ℕ)} (hr : leafR w.1.length (WinData.pos N w) w.1 gs o₀ = r)
    (himgs : leafImgs w.1.length (WinData.pos N w) w.1 gs o₀ = imgs) {Bge Bst Btr Bgt : ℕ}
    (hBge : X.B.call GroupOp.generate (N + r, os_extGens N r gs imgs)
      (osGroup X.O N r gs imgs) ≤ Bge)
    (hBst : X.B.call GroupOp.stabilizer (osGroup X.O N r gs imgs, N)
      (osStab X.O N r gs imgs) ≤ Bst)
    (hBtr : X.B.call GroupOp.orbitTransversal (osGroup X.O N r gs imgs, N)
      (osTrans X.O N r gs imgs) ≤ Btr)
    (hBgt : X.B.call GroupOp.generate (N, (osStab X.O N r gs imgs).2.1.map (PermData.truncTo N))
      (orbitStabModel X.O N r gs imgs).1 ≤ Bgt) :
    RunsWithin X body (SoJTree.leafStabProg N w.1.length (WinData.pos N w) w.1 gs o₀)
      (leafStabModel X.O N w.1.length (WinData.pos N w) w.1 gs o₀)
      (1000 * (N + w.1.length + gs.length + r + outB w.1.length t + 2) ^ 8 +
        (osStab X.O N r gs imgs).2.1.length * (11 * N + 13) +
        (osTrans X.O N r gs imgs).length * (11 * N + 14) + Bge + Bst + Btr + Bgt) ∧
      r ≤ (soj (colOf w.1.length c) t).count := by
  refine ⟨RunsWithin.leafStabProg_of_outSize hO hPre hgs hw hW (sojProg_outSize c hmt o₀ ho)
    hr himgs hBge hBst hBtr hBgt, ?_⟩
  have hreach := (sojProg_reach w.1.length t c (decodeOut w.1.length o₀)).1 ⟨o₀, ho, rfl⟩
  exact hr ▸ leafStab_index_le_count hgs hw hW o₀ hc hreach

end Spec

end GraphIso.SoJTree
