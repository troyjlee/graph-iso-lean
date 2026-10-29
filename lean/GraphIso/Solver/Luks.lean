module

public import GraphIso.Solver.SimsCompose
public import GraphIso.Luks.Entry
public import GraphIso.Luks.Nilpotent

/-!
# Luks's strategy with the Schreier–Sims backend

`ssLuksBounds n R G₀` discharges `LuksBounds` for the Schreier–Sims backend at degree `n`,
with `s = n²` generators and at most `R` coset representatives, for every ambient group `G₀`.
The block kernel is computed at degree `n + k ≤ 2n`, so its charges are those of degree `2n`.

* `solve_luks`: for a group with `PrimBounded ⟨gs⟩ c`, the public solver with Luks's strategy
  and this backend is a closed program over the empty signature; on every valid input it
  returns a correct answer at cost at most `luksSimsCost n L m c`, with per-invocation unit
  `luksSimsQ n (n ^ c)`.
* `solve_luks_checked`: the validating entry, on every input.
* `solve_luks_any`: every group, with the exponential bound for `c = n`
  (`primBounded_degree`).
* `luksSimsCost_le_pow`: for primitive sections bounded by `k ^ c` with `c ≥ 1` and windows of
  size at most `n`, the bound `luksSimsCost` is at most `6640 (n + 1)^{3c + 5} + 60 L (n + 1)²`.
* `solve_luks_nilpotent`: **for nilpotent groups (in particular `p`-groups), cost at most
  `6640 (n + 1)⁸ + 60 L (n + 1)²`**, polynomial in the degree and the number of input
  generators (`luksSimsCost_one_le`, the case `c = 1`).
-/

@[expose] public section

namespace GraphIso.Sims

open Equiv Cost Programs Solver Luks

/-! ### Monotonicity in the degree -/

theorem buildCost_mono₂ {n n' L L' : ℕ} (hn : n ≤ n') (hL : L ≤ L') :
    buildCost n L ≤ buildCost n' L' := by
  unfold buildCost initCost slotCost insCost itemCost siftCost
  gcongr

theorem genCost_mono₂ {n n' L L' : ℕ} (hn : n ≤ n') (hL : L ≤ L') :
    genCost n L ≤ genCost n' L' := by
  unfold genCost
  gcongr
  exact buildCost_mono₂ hn hL

theorem kerCost_mono₂ {n n' L L' m m' : ℕ} (hn : n ≤ n') (hL : L ≤ L') (hm : m ≤ m') :
    kerCost n L m ≤ kerCost n' L' m' := by
  unfold kerCost
  gcongr
  exact buildCost_mono₂ hn hL

theorem repsCost_mono₃ {n L L' L₁ L₁' I I' : ℕ} (hL : L ≤ L') (hL₁ : L₁ ≤ L₁') (hI : I ≤ I') :
    repsCost n L L₁ I ≤ repsCost n L' L₁' I' := by
  unfold repsCost repsVisitCost
  gcongr
  exact buildCost_mono hL₁

theorem IsBlockList.length_le {w : WinData} {bs : List (List ℕ)} (h : IsBlockList w bs) :
    bs.length ≤ w.1.length := by
  rw [← h.1.length_eq, List.length_flatten]
  have h₁ : (bs.map fun _ => 1).sum ≤ (bs.map List.length).sum :=
    sum_map_le_sum_map bs _ _ fun b hb => List.length_pos_of_ne_nil (h.2 b hb)
  rw [sum_map_const, Nat.mul_one] at h₁
  exact h₁

/-! ### The bounds -/

/-- **The Schreier–Sims backend's bounds for Luks's strategy**, for subgroups of any ambient
group `G₀`, with at most `n²` generators and at most `R` coset representatives. -/
def ssLuksBounds (n R : ℕ) (G₀ : Subgroup (Perm (Fin n))) :
    LuksBounds ssCtx ssDV n (n * n) R G₀ where
  Borb := orbitsCost n (n * n) n + 5
  Bge := genCost (2 * n) (n * n) + 2
  Bke := kerCost (2 * n) (2 * n * (2 * n)) n + 5
  Bgt := genCost n (2 * n * (2 * n)) + 2
  sKe := 2 * n * (2 * n)
  Bcr := repsCost n (n * n) (n * n) R + 7
  Bgen := genCost n (R * (n * n + 1)) + 2
  orbits gs _ w hs _ hpre := by
    obtain ⟨-, hw, -⟩ := hpre
    exact Nat.add_le_add_right (orbitsCost_mono hs (WinData.length_le hw)) 5
  blocks gs d w bs hs _ hGv hw hbs hG := by
    have hkn : bs.length ≤ n := (IsBlockList.length_le hbs).trans (WinData.length_le hw)
    have hnk : n + bs.length ≤ 2 * n := by omega
    have hegv : GensData.AllValid (n + bs.length) (extendGens n bs gs) :=
      GensData.allValid_extendTo hw hbs hG hGv.1
    obtain ⟨hev, heden, hel⟩ := generateModel_spec hegv
    obtain ⟨hkv, hkden, hkl⟩ := kernelModel_spec hev (valid_blockWin n bs.length)
    rw [heden, extendGens, GensData.denote_extendTo hw hbs hG hGv.1] at hkden
    have htv := allValid_truncTo hw hbs hG hkv hkden
    have hsq : (n + bs.length) * (n + bs.length) ≤ 2 * n * (2 * n) := Nat.mul_le_mul hnk hnk
    have hwin : (blockWin n bs.length).1.length = bs.length := by
      simp [blockWin, WinData.ofPoints_fst, blockPts]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show genCost (n + bs.length) (extendGens n bs gs).length + 2 ≤ _
      rw [extendGens, List.length_map]
      exact Nat.add_le_add_right (genCost_mono₂ hnk hs) 2
    · show kerCost (n + bs.length) (generateModel (n + bs.length) (extendGens n bs gs)).length
        (blockWin n bs.length).1.length + 5 ≤ _
      rw [hwin]
      exact Nat.add_le_add_right (kerCost_mono₂ hnk (hel.trans hsq) hkn) 5
    · show genCost n ((kernelModel (n + bs.length) (generateModel (n + bs.length)
        (extendGens n bs gs)) (blockWin n bs.length)).map (PermData.truncTo n)).length + 2 ≤ _
      rw [List.length_map]
      exact Nat.add_le_add_right (genCost_mono (hkl.trans hsq)) 2
    · exact hkl.trans hsq
    · exact (generateModel_spec htv).2.2
  cosetReps gs d w bs hs _ hGv hw hbs hG hR := by
    have hegv : GensData.AllValid (n + bs.length) (extendGens n bs gs) :=
      GensData.allValid_extendTo hw hbs hG hGv.1
    obtain ⟨hev, heden, -⟩ := generateModel_spec hegv
    obtain ⟨hkv, hkden, -⟩ := kernelModel_spec hev (valid_blockWin n bs.length)
    rw [heden, extendGens, GensData.denote_extendTo hw hbs hG hGv.1] at hkden
    have htv := allValid_truncTo hw hbs hG hkv hkden
    show repsCost n gs.length (blockKernelModel ssOracle n bs gs).2.1.length _ + 7 ≤ _
    exact Nat.add_le_add_right (repsCost_mono₃ hs (generateModel_spec htv).2.2 hR) 7
  generate _ _ hl _ := Nat.add_le_add_right (genCost_mono hl) 2
  genOut _ hgs _ := (generateModel_spec hgs).2.2

/-- The per-invocation unit of Luks's strategy with the Schreier–Sims backend, for at most `R`
coset representatives. -/
def luksSimsQ (n R : ℕ) : ℕ :=
  luksQ n (n * n) (orbitsCost n (n * n) n + 5) (genCost (2 * n) (n * n) + 2)
    (kerCost (2 * n) (2 * n * (2 * n)) n + 5) (genCost n (2 * n * (2 * n)) + 2) (2 * n * (2 * n))
    (repsCost n (n * n) (n * n) R + 7) (genCost n (R * (n * n + 1)) + 2)

/-- The cost bound of the public solver with Luks's strategy and the Schreier–Sims backend, for
degree `n`, `L` input generators, window size `m` and primitive sections bounded by `k ^ c`. -/
def luksSimsCost (n L m c : ℕ) : ℕ := 11 + (genCost n L + 2) + luksBound (luksSimsQ n (n ^ c)) c m

/-! ### Closed polynomial bounds -/

/-- **The per-invocation unit is `O(n⁶ + R² n⁴)`.** -/
theorem luksSimsQ_le (n R : ℕ) :
    luksSimsQ n R ≤ 3200 * (n + 1) ^ 6 + 50 * R * (n + 1) ^ 4 + 13 * R ^ 2 * (n + 1) ^ 4 := by
  simp only [luksSimsQ, luksQ, luksNode, luksEdge, luksBranch, maxBlocksCost, mbCost,
    closureCost, blockKernelCost, orbitsCost, transCost, genCost, kerCost, repsCost,
    repsVisitCost, buildCost, initCost, itemCost, slotCost, insCost, siftCost]
  ring_nf
  omega

theorem luksBound_le {Q c m : ℕ} : luksBound Q c m ≤ 2 * Q * (m + 1) ^ (c + 1) := by
  unfold luksBound
  split
  · have : 1 ≤ (m + 1) ^ (c + 1) := Nat.one_le_pow _ _ (by omega)
    nlinarith
  · have : m ^ (c + 1) ≤ (m + 1) ^ (c + 1) := Nat.pow_le_pow_left (by omega) _
    have : 2 * Q * m ^ (c + 1) ≤ 2 * Q * (m + 1) ^ (c + 1) := Nat.mul_le_mul_left _ this
    omega

/-- **The solver's cost bound in closed form**, for primitive sections bounded by `k ^ c`. -/
theorem luksSimsCost_le (n L m c : ℕ) :
    luksSimsCost n L m c ≤ 13 + 100 * (n + 1) ^ 6 + 60 * L * (n + 1) ^ 2 +
      2 * (m + 1) ^ (c + 1) *
        (3200 * (n + 1) ^ 6 + 50 * n ^ c * (n + 1) ^ 4 + 13 * (n ^ c) ^ 2 * (n + 1) ^ 4) := by
  have h₁ := genCost_le n L
  have h₂ := luksSimsQ_le n (n ^ c)
  have h₃ : luksBound (luksSimsQ n (n ^ c)) c m ≤ 2 * luksSimsQ n (n ^ c) * (m + 1) ^ (c + 1) :=
    luksBound_le
  have h₄ : 2 * luksSimsQ n (n ^ c) * (m + 1) ^ (c + 1) ≤ 2 * (m + 1) ^ (c + 1) *
      (3200 * (n + 1) ^ 6 + 50 * n ^ c * (n + 1) ^ 4 + 13 * (n ^ c) ^ 2 * (n + 1) ^ 4) := by
    rw [Nat.mul_right_comm]
    exact Nat.mul_le_mul_left _ h₂
  unfold luksSimsCost
  omega

/-! ### The concrete theorems -/

/-- The public solver with Luks's strategy and the Schreier–Sims backend substituted: a
closed program over the empty signature, inside the substituted procedure. -/
def luksSolver : WfProc Signature.empty (Ty.inst Ty.unit) (Ty.answer Ty.unit) :=
  WfProc.subst ⟨luksBody Ty.unit, luksBody_wf⟩ ⟨ssImpl, ssImpl_wf⟩

/-- **Luks's strategy with the Schreier–Sims backend**: correctness, and a cost bound
polynomial in the degree for groups with bounded primitive sections, without an assumed group
oracle. -/
theorem solve_luks {n c : ℕ} {xy : StrData × StrData} {w : WinData} {σd : PermData}
    {gs : GensData} (hprim : PrimBounded (GensData.denote n gs) c) (hw : w.Valid n)
    (hσ : σd.Valid n) (hgs : GensData.AllValid n gs)
    (hinv : IsInvariant (GensData.denote n gs) (w.denote n)) :
    ∃ (ans : AnswerData Ty.unit) (tr : Trace Signature.empty),
      Runs Ctx.empty.O (luksSolver.proc Ty.denote)
        ((solveEntry Ty.unit Ty.denote (xy, w, σd, n, gs)).subst ssImpl) ans tr ∧
      Trace.localCost tr ≤ luksSimsCost n gs.length w.1.length c ∧
      AnsOK ssDV n (w.denote n) (σd.denote n) (gs.denote n) (xy.1.denote n) (xy.2.denote n)
        ans := by
  obtain ⟨ans, tr, hr, hc, hok⟩ := luks_backend_refinement (X := ssCtx) (DV := ssDV)
    (I := ⟨ssImpl, ssImpl_wf⟩) (fun op x _ hx => ssOracle_meets op x hx) (fun _ _ _ hx => hx)
    ssImpl_implements (ssLuksBounds n (n ^ c) _) hprim le_rfl hw hσ hgs hinv
  refine ⟨ans, tr, hr, ?_, hok⟩
  rw [Trace.cost_empty] at hc
  exact hc

/-- **The checked solver with Luks's strategy and the Schreier–Sims backend, on every
input.** -/
theorem solve_luks_checked (q n c : ℕ) (xy : StrData × StrData) (w : WinData) (σd : PermData)
    (gs : GensData) (hprim : PrimBounded (GensData.denote n gs) c) :
    ∃ (r : Option (AnswerData Ty.unit)) (tr : Trace Signature.empty),
      Runs Ctx.empty.O (luksSolver.proc Ty.denote)
        ((solveChecked Ty.unit Ty.denote (q, xy, w, σd, n, gs)).subst ssImpl) r tr ∧
      Trace.localCost tr ≤ validCost n w.1.length gs.length + 4 +
        luksSimsCost n gs.length w.1.length c ∧
      (r = none ↔ ¬ InputValid q (xy, w, σd, n, gs)) ∧
      ∀ ans, r = some ans →
        AnsOK ssDV n (w.denote n) (σd.denote n) (gs.denote n) (xy.1.denote n) (xy.2.denote n)
          ans := by
  obtain ⟨r, ⟨tr, hr, hc, hpre⟩, hnone, hsome⟩ := luksChecked_spec (X := ssCtx) (DV := ssDV)
    (q := q) (fun op x _ hx => ssOracle_meets op x hx) (fun _ _ _ hx => hx)
    (ssLuksBounds n (n ^ c) (GensData.denote n gs)) hprim le_rfl
  obtain ⟨tr', hr', hc'⟩ := Runs.subst ssImpl_implements hr hpre
  refine ⟨r, tr', hr', ?_, hnone, fun ans h => (hsome ans h).1⟩
  rw [Trace.cost_empty] at hc'
  refine hc'.trans (hc.trans ?_)
  split
  · exact le_rfl
  · exact Nat.add_le_add_left (Nat.zero_le _) _

/-- **Luks's strategy is correct for every group**, with the bound for `c = n`. -/
theorem solve_luks_any {n : ℕ} {xy : StrData × StrData} {w : WinData} {σd : PermData}
    {gs : GensData} (hw : w.Valid n) (hσ : σd.Valid n) (hgs : GensData.AllValid n gs)
    (hinv : IsInvariant (GensData.denote n gs) (w.denote n)) :
    ∃ (ans : AnswerData Ty.unit) (tr : Trace Signature.empty),
      Runs Ctx.empty.O (luksSolver.proc Ty.denote)
        ((solveEntry Ty.unit Ty.denote (xy, w, σd, n, gs)).subst ssImpl) ans tr ∧
      Trace.localCost tr ≤ luksSimsCost n gs.length w.1.length n ∧
      AnsOK ssDV n (w.denote n) (σd.denote n) (gs.denote n) (xy.1.denote n) (xy.2.denote n)
        ans :=
  solve_luks (primBounded_degree _) hw hσ hgs hinv

/-- The solver's bound for primitive sections of order at most `k ^ c`, `c ≥ 1`: at most
`6640 (n + 1)^{3c + 5} + 60 L (n + 1)²` for windows of size at most `n`. -/
theorem luksSimsCost_le_pow {n L m c : ℕ} (hc : 1 ≤ c) (hmn : m ≤ n) :
    luksSimsCost n L m c ≤ 6640 * (n + 1) ^ (3 * c + 5) + 60 * L * (n + 1) ^ 2 := by
  have h := luksSimsCost_le n L m c
  have hn1 : 1 ≤ n + 1 := by omega
  have hm : (m + 1) ^ (c + 1) ≤ (n + 1) ^ (c + 1) := Nat.pow_le_pow_left (by omega) _
  have hnc : n ^ c ≤ (n + 1) ^ c := Nat.pow_le_pow_left (by omega) _
  have e₁ : (n + 1) ^ 6 ≤ (n + 1) ^ (2 * c + 4) := Nat.pow_le_pow_right hn1 (by omega)
  have e₂ : n ^ c * (n + 1) ^ 4 ≤ (n + 1) ^ (2 * c + 4) := by
    calc n ^ c * (n + 1) ^ 4 ≤ (n + 1) ^ c * (n + 1) ^ 4 := Nat.mul_le_mul_right _ hnc
      _ = (n + 1) ^ (c + 4) := by rw [← pow_add]
      _ ≤ (n + 1) ^ (2 * c + 4) := Nat.pow_le_pow_right hn1 (by omega)
  have e₃ : (n ^ c) ^ 2 * (n + 1) ^ 4 ≤ (n + 1) ^ (2 * c + 4) := by
    calc (n ^ c) ^ 2 * (n + 1) ^ 4 ≤ ((n + 1) ^ c) ^ 2 * (n + 1) ^ 4 :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hnc 2)
      _ = (n + 1) ^ (2 * c + 4) := by rw [← pow_mul, ← pow_add, mul_comm c 2]
  have e₄ : 3200 * (n + 1) ^ 6 + 50 * n ^ c * (n + 1) ^ 4 + 13 * (n ^ c) ^ 2 * (n + 1) ^ 4 ≤
      3263 * (n + 1) ^ (2 * c + 4) := by
    have := Nat.mul_le_mul_left 50 e₂
    have := Nat.mul_le_mul_left 13 e₃
    rw [← mul_assoc] at *
    omega
  have e₅ : 2 * (m + 1) ^ (c + 1) *
      (3200 * (n + 1) ^ 6 + 50 * n ^ c * (n + 1) ^ 4 + 13 * (n ^ c) ^ 2 * (n + 1) ^ 4) ≤
      6526 * (n + 1) ^ (3 * c + 5) := by
    calc 2 * (m + 1) ^ (c + 1) *
          (3200 * (n + 1) ^ 6 + 50 * n ^ c * (n + 1) ^ 4 + 13 * (n ^ c) ^ 2 * (n + 1) ^ 4)
        ≤ 2 * (n + 1) ^ (c + 1) * (3263 * (n + 1) ^ (2 * c + 4)) := by gcongr
      _ = 6526 * (n + 1) ^ (3 * c + 5) := by
        rw [show 3 * c + 5 = (c + 1) + (2 * c + 4) by omega, pow_add]
        ring
  have e₆ : 13 + 100 * (n + 1) ^ 6 ≤ 114 * (n + 1) ^ (3 * c + 5) := by
    have h1 : 1 ≤ (n + 1) ^ (3 * c + 5) := Nat.one_le_pow _ _ (by omega)
    have h6 : (n + 1) ^ 6 ≤ (n + 1) ^ (3 * c + 5) := Nat.pow_le_pow_right hn1 (by omega)
    omega
  omega

/-- The bound for primitive sections of degree `k` of order at most `k` (exponent `c = 1`): at
most `6640 (n + 1)⁸ + 60 L (n + 1)²` for windows of size at most `n`. -/
theorem luksSimsCost_one_le {n L m : ℕ} (hmn : m ≤ n) :
    luksSimsCost n L m 1 ≤ 6640 * (n + 1) ^ 8 + 60 * L * (n + 1) ^ 2 :=
  luksSimsCost_le_pow le_rfl hmn

/-- **String isomorphism for nilpotent groups in polynomial time**: with Luks's strategy and
the Schreier–Sims backend, the cost is at most `6640 (n + 1)⁸ + 60 L (n + 1)²` for `L` input
generators. This covers `p`-groups. -/
theorem solve_luks_nilpotent {n : ℕ} {xy : StrData × StrData} {w : WinData} {σd : PermData}
    {gs : GensData} (hnil : Group.IsNilpotent (GensData.denote n gs)) (hw : w.Valid n)
    (hσ : σd.Valid n) (hgs : GensData.AllValid n gs)
    (hinv : IsInvariant (GensData.denote n gs) (w.denote n)) :
    ∃ (ans : AnswerData Ty.unit) (tr : Trace Signature.empty),
      Runs Ctx.empty.O (luksSolver.proc Ty.denote)
        ((solveEntry Ty.unit Ty.denote (xy, w, σd, n, gs)).subst ssImpl) ans tr ∧
      Trace.localCost tr ≤ 6640 * (n + 1) ^ 8 + 60 * gs.length * (n + 1) ^ 2 ∧
      AnsOK ssDV n (w.denote n) (σd.denote n) (gs.denote n) (xy.1.denote n) (xy.2.denote n)
        ans := by
  obtain ⟨ans, tr, hr, hc, hok⟩ := solve_luks (primBounded_of_isNilpotent hnil) hw hσ hgs hinv
  exact ⟨ans, tr, hr, hc.trans (luksSimsCost_one_le (WinData.length_le hw)), hok⟩

end GraphIso.Sims
