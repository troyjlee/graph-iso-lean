module

public import GraphIso.Main.SimsM5
public import GraphIso.Main.M5StepNs

/-!
# M5 without stuck orbits, with the Schreier–Sims backend

Stage 14j-6b-1, items 1–6 (`PLAN-14.md` §14.11): `RunsWithin.m5StepCJProg_ns_ss`, the step
`RunsWithin.m5StepCJProg_ns` at `ssCtx` with every hypothesis discharged except numeric ones and
the two interfaces, and with no factorial of the base size in its factor, `Lg` or work.

* **Case 2b's counts at a depth bound** (`c2bRj m jB = (m + 1)^jB · m² (Z + 1)`, against
  `c2bRU m = c2bRj m m`). Under `TransitivityBound T`, Case 2b's computed degree on its large
  orbit `Φ` is at most `T |Φ|` (`ss_m5_degD_le_T`, from `degD_le_T`), so with `T m' ≤ jB + 1` for
  every `m' ≤ m` its depth `degD − 1` is at most `jB`. The bounds `ssM5βns` are `ssM5β` with
  Case 2b's `generate` at `c2bRj m jB` candidates.
* **The discharged hypotheses of `RunsWithin.m5StepCJProg_ns`**:
  - Case 2b's counts for `y` (`ss_m5_hBgen₂ᵦ_ns`, `ss_m5_hLY₂_ns`), which the step needs only
    when `y` is in Case 2b;
  - Case 2b's partition leaves (`ss_m5_hpart₂ᵦ`): `t ≤ max ((|Φ| − j + 3)/2) (m − |Φ| + j)`
    (`firstLeafD_partLe`), so `4t ≤ 3m` from `2|Φ| > m`, `4 jB ≤ m` and `m ≥ 6`;
  - no twins in Case 3 (`ss_m5_hnt₃`), from `m5_no_twins` under `Thresholds K |W| k`, with
    `k ≤ tOf |Vx|` from Case 3's `2|S| < m` and `4k ≤ m`;
  - Case 3's partition structures (`ss_m5_hpart₃`): `t ≤ max ((|Vx| + 3)/2) (m − tOf |Vx| − 1)`
    (`firstStructD_partLe`), so `4t ≤ 3m` from `2|Vx| > m` and `m ≥ 6` alone;
  - the union cells (`ss_m5_hu₂_lab`, `ss_m5_hu₃_lab`): at most `labLen L · λ(m)`
    (`ss_union_le_lab`).
-/

@[expose] public section

namespace GraphIso.Main

open Equiv MulAction Pointwise Cost GraphIso GraphIso.Programs GraphIso.Toolkit
  GraphIso.Recursion GraphIso.SplitJohnson GraphIso.Solver GraphIso.Align GraphIso.Certificates
  GraphIso.CertProg Sims

/-! ### Case 2b's counts at a depth bound -/

section Counts

/-- **The bound on Case 2b's candidates at depth at most `jB`**, for base size `m`: `c2bR` with
at most `m + 1` points in `Φ`. `c2bRU m = c2bRj m m`. -/
def c2bRj (m jB : ℕ) : ℕ := (m + 1) ^ jB * (m * m * (Case2b.sojZ m + 1))

theorem c2bRU_eq_c2bRj (m : ℕ) : c2bRU m = c2bRj m m := rfl

theorem c2bR_le_j {N n nΦ j jB : ℕ} (hΦ : nΦ ≤ N - n) (hj : j ≤ jB) :
    Case2b.c2bR N n nΦ j (Case2b.sojZ (N - n)) ≤ c2bRj (N - n) jB := by
  unfold Case2b.c2bR c2bRj
  refine Nat.mul_le_mul_right _ ((Nat.pow_le_pow_left (show nΦ ≤ N - n + 1 by omega) j).trans ?_)
  exact Nat.pow_le_pow_right (by omega) hj

theorem c2bRj_mono {m m' jB jB' : ℕ} (hm : m ≤ m') (hj : jB ≤ jB') : c2bRj m jB ≤ c2bRj m' jB' := by
  unfold c2bRj Case2b.sojZ
  have h1 : (m + 1) ^ jB ≤ (m' + 1) ^ jB' :=
    (Nat.pow_le_pow_left (by omega) jB).trans (Nat.pow_le_pow_right (by omega) hj)
  have h2 := Nat.clog_mono_right 2 hm
  have h3 : 2 ^ (129 * (Nat.clog 2 m + 2) ^ 2) ≤ 2 ^ (129 * (Nat.clog 2 m' + 2) ^ 2) :=
    Nat.pow_le_pow_right two_pos (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
  gcongr

/-- **M5's bounds with Schreier–Sims without stuck orbits**: `ssM5β` with Case 2b's `generate` on
at most `c2bRj m jB · (sIn + 1)` generators. -/
def ssM5βns (N m k sIn s jB : ℕ) : M5Bounds :=
  { ssM5β N m k sIn s with Bgen₂ᵦ := genCost N (c2bRj m jB * (sIn + 1)) + 2 }

end Counts

/-! ### The case of the dispatch -/

section Sel

variable {D : Ty} {O : Oracle (groupSig D)} {n N : ℕ} {Fx Fy : GroupData D.denote}

theorem m5Sel_four (h : m5Sel O n N Fx Fy = 4) :
    (m5Cs O n N Fx).1 = 2 ∧ m5IsA O n N Fx = false := by
  unfold m5Sel at h
  split_ifs at h with h1 h2 h3 h4 <;> simp_all

theorem m5Sel_three (h : m5Sel O n N Fx Fy = 3) :
    (m5Cs O n N Fx).1 ≠ 1 ∧ (m5Cs O n N Fx).1 ≠ 2 := by
  unfold m5Sel at h
  split_ifs at h with h1 h2 h3 h4 <;> simp_all

end Sel

/-! ### The hypotheses without stuck orbits, discharged -/

section Discharge

variable {N n k sIn s : ℕ} {gs : GensData} {xy : StrData × StrData} {w : WinData}
  {L : LabelData} {st : ℕ × CJData} {a b : Ty}
  {body : a.denote → Prog (groupSig Ty.unit) (a, b) Ty.denote b}

/-- **Case 2b's degree under `TransitivityBound T`**, with Schreier–Sims: for a full group in
Case 2b (tag `2`, not Case 2a), the computed degree on its large orbit `Φ` is at most `T |Φ|`
(`degD_le_T`, with `hng` of `m5Case_spec`). -/
theorem ss_m5_degD_le_T {T : ℕ → ℕ} (hT : AltQuot.TransitivityBound T) (hNs : N * N ≤ sIn)
    {hC : CertSetting (GensData.denote N gs) n} {φ : strGroup hC →* Perm (Fin (N - n))}
    {x : StrData} {fs : GensData} {e : Ty.unit.denote}
    (hF : M5Full (D := Ty.unit) ssDV hC φ k sIn x fs e)
    (h2 : (m5Cs ssCtx.O n N (N, fs, e)).1 = 2) (hA : m5IsA ssCtx.O n N (N, fs, e) = false) :
    Case2b.degD ssCtx.O N n (N, fs, e) (m5Cs ssCtx.O n N (N, fs, e)).2 ≤
      T (m5Cs ssCtx.O n N (N, fs, e)).2.length := by
  have hO : MeetsContractOn ssDV m5CaseOps ssCtx.O := fun op x _ hx => ssOracle_meets op x hx
  have hPre : ∀ op x, m5CaseOps op → GroupPre ssDV op x → ssCtx.Pre op x := fun _ _ _ h => h
  have hOd : MeetsContractOn ssDV Case2b.degOps ssCtx.O := fun op x _ hx => ssOracle_meets op x hx
  have hPd : ∀ op x, Case2b.degOps op → GroupPre ssDV op x → ssCtx.Pre op x := fun _ _ _ h => h
  have hFi := hF.base_inv
  obtain ⟨hos, -, hng⟩ := m5Case_spec hO hPre (ssBoundsS N sIn ⊤ hNs) ssBm hF.1 hF.2.1 le_top hFi
  have hc := Giant.caseD_spec hFi hos
  rw [m5Cs_eq] at hc
  obtain ⟨hΦn, hΦl, -, γ, -, hγ⟩ := hc.2.1 h2
  exact Case2b.degD_le_T hT hOd hPd (ssBoundsS N sIn ⊤ hNs) hF.1 hF.2.1 le_top hFi hΦn hΦl
    (Case2b.cp2_inv_of_orbit hFi hΦl ⟨γ, hγ⟩) (ssBm _) (hng h2 hA)

/-- Case 2b's depth in Case 2b is at most `jB`, when `T m' ≤ jB + 1` for every `m' ≤ m`. -/
theorem ss_m5_depth_le {T : ℕ → ℕ} (hT : AltQuot.TransitivityBound T) (hNs : N * N ≤ sIn)
    {jB : ℕ} (hjB : ∀ m' ≤ N - n, T m' ≤ jB + 1)
    {hC : CertSetting (GensData.denote N gs) n} {φ : strGroup hC →* Perm (Fin (N - n))}
    {x : StrData} {fs : GensData} {e : Ty.unit.denote}
    (hF : M5Full (D := Ty.unit) ssDV hC φ k sIn x fs e)
    (h2 : (m5Cs ssCtx.O n N (N, fs, e)).1 = 2) (hA : m5IsA ssCtx.O n N (N, fs, e) = false) :
    Case2b.degD ssCtx.O N n (N, fs, e) (m5Cs ssCtx.O n N (N, fs, e)).2 - 1 ≤ jB := by
  have hd := ss_m5_degD_le_T hT hNs hF h2 hA
  have := hjB _ (ss_m5Cs_le (e := e) hF.1.1 hF.base_inv)
  omega

/-- Case 2b's candidates' `generate` for `y` in Case 2b (`hBgen₂ᵦ` of
`RunsWithin.m5StepCJProg_ns`), at the depth bound. -/
theorem ss_m5_hBgen₂ᵦ_ns {T : ℕ → ℕ} (hT : AltQuot.TransitivityBound T) (hNs : N * N ≤ sIn)
    {jB : ℕ} (hjB : ∀ m' ≤ N - n, T m' ≤ jB + 1) :
    ∀ (hC : CertSetting (GensData.denote N gs) n) (φ : strGroup hC →* Perm (Fin (N - n))),
      IsPhi hC φ → ∀ fs e, M5Full (D := Ty.unit) ssDV hC φ k sIn xy.2 fs e →
      (m5Cs ssCtx.O n N (N, fs, e)).1 = 2 → m5IsA ssCtx.O n N (N, fs, e) = false →
      ∀ gs' : GensData, GensData.AllValid N gs' →
      gs'.length ≤ Case2b.c2bR N n (m5Cs ssCtx.O n N (N, fs, e)).2.length
        (Case2b.degD ssCtx.O N n (N, fs, e) (m5Cs ssCtx.O n N (N, fs, e)).2 - 1)
        (Case2b.sojZ (N - n)) * (sIn + 1) →
      GensData.denote N gs' ≤ GensData.denote N gs →
      ssCtx.B.call GroupOp.generate (N, gs') (ssCtx.O.run GroupOp.generate (N, gs')) ≤
        (ssM5βns N (N - n) k sIn s jB).Bgen₂ᵦ := by
  intro hC φ hφ fs e hF h2 hA gs' _ hl _
  have hc := c2bR_le_j (ss_m5Cs_le (e := e) hF.1.1 hF.base_inv)
    (ss_m5_depth_le hT hNs hjB hF h2 hA)
  exact ssB_generate_le le_rfl (hl.trans (Nat.mul_le_mul_right _ hc)) _

/-- Case 2b's count for `y` in Case 2b (`hLY₂` of `RunsWithin.m5StepCJProg_ns`), at the depth
bound. -/
theorem ss_m5_hLY₂_ns {T : ℕ → ℕ} (hT : AltQuot.TransitivityBound T) (hNs : N * N ≤ sIn)
    {jB : ℕ} (hjB : ∀ m' ≤ N - n, T m' ≤ jB + 1) {Lg : ℕ}
    (hLY : c2bRj (N - n) jB * (sIn + 1) ≤ Lg) :
    ∀ (hC : CertSetting (GensData.denote N gs) n) (φ : strGroup hC →* Perm (Fin (N - n))),
      IsPhi hC φ → ∀ fs e, M5Full (D := Ty.unit) ssDV hC φ k sIn xy.2 fs e →
      (m5Cs ssCtx.O n N (N, fs, e)).1 = 2 → m5IsA ssCtx.O n N (N, fs, e) = false →
      Case2b.c2bR N n (m5Cs ssCtx.O n N (N, fs, e)).2.length
        (Case2b.degD ssCtx.O N n (N, fs, e) (m5Cs ssCtx.O n N (N, fs, e)).2 - 1)
        (Case2b.sojZ (N - n)) * (sIn + 1) ≤ Lg := by
  intro hC φ hφ fs e hF h2 hA
  have hc := c2bR_le_j (ss_m5Cs_le (e := e) hF.1.1 hF.base_inv)
    (ss_m5_depth_le hT hNs hjB hF h2 hA)
  exact (Nat.mul_le_mul_right _ hc).trans hLY

/-- **Case 2b's partition leaves are small** (`hpart₂ᵦ` of `RunsWithin.m5StepCJProg_ns`): a first
leaf that is not a Johnson leaf is a colored `t`-partition with `4t ≤ 3m`, from
`t ≤ max ((|Φ| − j + 3)/2) (m − |Φ| + j)` (`firstLeafD_partLe`), `2|Φ| > m`, `j ≤ jB`,
`4 jB ≤ m` and `m ≥ 6`. -/
theorem ss_m5_hpart₂ᵦ {T : ℕ → ℕ} (hT : AltQuot.TransitivityBound T) (hNs : N * N ≤ sIn)
    {jB : ℕ} (hjB : ∀ m' ≤ N - n, T m' ≤ jB + 1) (h4j : 4 * jB ≤ N - n) (hm : 6 ≤ N - n) :
    ∀ (hC : CertSetting (GensData.denote N gs) n) (φ : strGroup hC →* Perm (Fin (N - n))),
      IsPhi hC φ → ∀ fxs ex fys ey, M5Full (D := Ty.unit) ssDV hC φ k sIn xy.1 fxs ex →
      M5Full (D := Ty.unit) ssDV hC φ k sIn xy.2 fys ey →
      m5Sel ssCtx.O n N (N, fxs, ex) (N, fys, ey) = 4 → ∀ X₀,
      m5Leaf2b ssCtx.O N n (N, fxs, ex) (m5Cs ssCtx.O n N (N, fxs, ex)).2 = some X₀ → X₀.1 ≠ 2 →
      ∃ (p : CPart (Fin (N - n))) (t : ℕ), (Case2b.outOps (N - n)).dec X₀ = some (Sum.inl p) ∧
        IsColPart Finset.univ t p ∧ 4 * t ≤ 3 * (N - n) := by
  classical
  intro hC φ hφ fxs ex fys ey hF _ hsel X₀ hX₀ hX₂
  obtain ⟨h2, hA⟩ := m5Sel_four hsel
  have hO : MeetsContractOn ssDV m5CaseOps ssCtx.O := fun op x _ hx => ssOracle_meets op x hx
  have hPre : ∀ op x, m5CaseOps op → GroupPre ssDV op x → ssCtx.Pre op x := fun _ _ _ h => h
  have hOd : MeetsContractOn ssDV Case2b.degOps ssCtx.O := fun op x _ hx => ssOracle_meets op x hx
  have hPd : ∀ op x, Case2b.degOps op → GroupPre ssDV op x → ssCtx.Pre op x := fun _ _ _ h => h
  have hFi := hF.base_inv
  obtain ⟨hos, -, hng⟩ := m5Case_spec hO hPre (ssBoundsS N sIn ⊤ hNs) ssBm hF.1 hF.2.1 le_top hFi
  have hc := Giant.caseD_spec hFi hos
  rw [m5Cs_eq] at hc
  obtain ⟨hΦn, hΦl, hΦ2, γ, -, hγ⟩ := hc.2.1 h2
  have hΦi := Case2b.cp2_inv_of_orbit hFi hΦl ⟨γ, hγ⟩
  obtain ⟨h1, H⟩ := Case2b.case2bHyp_degD hOd hPd (ssBoundsS N sIn ⊤ hNs) hF.1 hF.2.1 le_top hFi
    hΦn hΦl hΦi (ssBm _) ⟨γ, hγ⟩ (hng h2 hA)
  have H' : Case2b.Case2bHyp (baseHom _ n hFi).range
      (SoJProg.setOf (N - n) (m5Cs ssCtx.O n N (N, fxs, ex)).2)
      (Case2b.degD ssCtx.O N n (N, fxs, ex) (m5Cs ssCtx.O n N (N, fxs, ex)).2 - 1 + 1) := by
    rw [Nat.sub_add_cancel h1]
    exact H
  have hsize := H'.size
  rw [SoJProg.card_setOf hΦn hΦl] at hsize
  obtain ⟨p, t, hdec, hp, ht⟩ := Case2b.firstLeafD_partLe (F := (N, fxs, ex))
    (Case2b.cp2_choiceOps_of_deg hOd) rfl hF.1 hFi hΦn hΦl H' hX₀ hX₂
  have hj := ss_m5_depth_le hT hNs hjB hF h2 hA
  have hΦm := ss_m5Cs_le (e := ex) hF.1.1 hFi
  refine ⟨p, t, hdec, hp, ?_⟩
  rcases le_total ((((m5Cs ssCtx.O n N (N, fxs, ex)).2.length -
      (Case2b.degD ssCtx.O N n (N, fxs, ex) (m5Cs ssCtx.O n N (N, fxs, ex)).2 - 1)) + 3) / 2)
      (N - n - ((m5Cs ssCtx.O n N (N, fxs, ex)).2.length -
        (Case2b.degD ssCtx.O N n (N, fxs, ex) (m5Cs ssCtx.O n N (N, fxs, ex)).2 - 1))) with hc | hc
  · rw [max_eq_right hc] at ht
    omega
  · rw [max_eq_left hc] at ht
    omega

/-- The Johnson routes' union labels in Case 2b (`hu₂`), at `uB = labLen L · λ(m)`
(`ss_union_le_lab`). -/
theorem ss_m5_hu₂_lab :
    ∀ (hC : CertSetting (GensData.denote N gs) n) (φ : strGroup hC →* Perm (Fin (N - n))), IsPhi hC
      φ → ∀ fs e, M5Full (D := Ty.unit) ssDV hC φ k sIn xy.1 fs e → (m5Cs ssCtx.O n N (N, fs, e)).1
      = 2 → m5IsA ssCtx.O n N (N, fs, e) = false → ∀ X₀, m5Leaf2b ssCtx.O N n (N, fs, e) (m5Cs
      ssCtx.O n N (N, fs, e)).2 = some X₀ → X₀.1 = 2 → CJFacts (N - n) (cjFirst2bD N n (m5Cs ssCtx.O
      n N (N, fs, e)).2 (Case2b.degD ssCtx.O N n (N, fs, e) (m5Cs ssCtx.O n N (N, fs, e)).2 - 1) X₀)
      → ∀ gs' d' O', RDSet (D := Ty.unit) ssDV n N gs w L (Giant.g1Model ssCtx.O n (N, gs, ())
      (cjohnOps (N - n)) (cjFirst2bD N n (m5Cs ssCtx.O n N (N, fs, e)).2 (Case2b.degD ssCtx.O N n
      (N, fs, e) (m5Cs ssCtx.O n N (N, fs, e)).2 - 1) X₀)).2.1 sIn gs' d' O' → ((labJUD
      X₀.2.2.2.1.length (markArr (N - n) X₀.2.2.1) X₀.2.2.2.2.2 L O').getD (O'.headD 0) []).length ≤
      labLen L * lam (N - n) := by
  intro hC φ hφ fs e hF _ _ X₀ _ _ hcj gs' d' O' hset
  obtain ⟨t, hJ⟩ := hcj.2
  exact ss_union_le_lab (jd := X₀.2.2) hcj.1 hJ hset.1.nodup _

/-- The Johnson routes' union labels in Case 3 (`hu₃`), at `uB = labLen L · λ(m)`. -/
theorem ss_m5_hu₃_lab :
    ∀ (hC : CertSetting (GensData.denote N gs) n) (φ : strGroup hC →* Perm (Fin (N - n))), IsPhi hC
      φ → ∀ fs e, M5Full (D := Ty.unit) ssDV hC φ k sIn xy.1 fs e → (m5Cs ssCtx.O n N (N, fs, e)).1
      ≠ 1 → (m5Cs ssCtx.O n N (N, fs, e)).1 ≠ 2 → ∀ cXX X₀, Case3.ColChar φ (strOn hC.le
      (xy.1.denote N)) (strOn hC.le (xy.1.denote N)) k (fixPtsD (m5Os ssCtx.O n N (N, fs,
      e))).length (fixPtsD (m5Os ssCtx.O n N (N, fs, e))) (fixPtsD (m5Os ssCtx.O n N (N, fs, e)))
      cXX → Case3.firstStructD (N - n) k (fixPtsD (m5Os ssCtx.O n N (N, fs, e))) (Case3.colXD cXX k
      (fixPtsD (m5Os ssCtx.O n N (N, fs, e))).length) = some X₀ → X₀.1 = 2 → CJFacts (N - n)
      (cjFirst3D (N - n) k (fixPtsD (m5Os ssCtx.O n N (N, fs, e))) (Case3.colXD cXX k (fixPtsD (m5Os
      ssCtx.O n N (N, fs, e))).length) X₀) → ∀ gs' d' O', RDSet (D := Ty.unit) ssDV n N gs w L
      (Giant.g1Model ssCtx.O n (N, gs, ()) (cjohnOps (N - n)) (cjFirst3D (N - n) k (fixPtsD (m5Os
      ssCtx.O n N (N, fs, e))) (Case3.colXD cXX k (fixPtsD (m5Os ssCtx.O n N (N, fs, e))).length)
      X₀)).2.1 sIn gs' d' O' → ((labJUD X₀.2.2.2.1.length (markArr (N - n) X₀.2.2.1) X₀.2.2.2.2.2 L
      O').getD (O'.headD 0) []).length ≤ labLen L * lam (N - n) := by
  intro hC φ hφ fs e hF _ _ cXX X₀ _ _ _ hcj gs' d' O' hset
  obtain ⟨t, hJ⟩ := hcj.2
  exact ss_union_le_lab (jd := X₀.2.2) hcj.1 hJ hset.1.nodup _

/-- **Case 3's fixed points**, for a full group in Case 3 (tag neither `1` nor `2`): duplicate-free
base indices, exactly the fixed points of `ψ(F(x))`, more than half of the base (`2|S| < m`). -/
theorem ss_m5_c3_facts {hC : CertSetting (GensData.denote N gs) n}
    {φ : strGroup hC →* Perm (Fin (N - n))} {x : StrData} {fs : GensData} {e : Ty.unit.denote}
    (hF : M5Full (D := Ty.unit) ssDV hC φ k sIn x fs e)
    (h1 : (m5Cs ssCtx.O n N (N, fs, e)).1 ≠ 1) (h2 : (m5Cs ssCtx.O n N (N, fs, e)).1 ≠ 2) :
    (fixPtsD (m5Os ssCtx.O n N (N, fs, e))).Nodup ∧
      (∀ v ∈ fixPtsD (m5Os ssCtx.O n N (N, fs, e)), v < N - n) ∧
      (∀ v : Fin (N - n), v.val ∈ fixPtsD (m5Os ssCtx.O n N (N, fs, e)) ↔
        ∀ f ∈ (baseHom (m5Fmap hC φ k (x.denote N)) n (m5Fmap_base hC φ k _)).range, f v = v) ∧
      N - n < 2 * (fixPtsD (m5Os ssCtx.O n N (N, fs, e))).length := by
  have hos := ss_baseOrbits (e := e) hF.1.1 hF.base_inv
  rw [hF.2.2] at hos
  have hFi := m5Fmap_base hC φ k (x.denote N)
  obtain ⟨hVn, hVl, hVF⟩ := fixPtsD_spec hFi hos
  have hc := Giant.caseD_spec hFi hos
  rw [m5Cs_eq] at hc
  have h3 : (m5Cs ssCtx.O n N (N, fs, e)).1 = 3 := by
    rcases m5_caseD_tag (N - n) (m5Os ssCtx.O n N (N, fs, e)) with h | h | h
    · exact absurd h h1
    · exact absurd h h2
    · exact h
  obtain ⟨-, hc3b⟩ := hc.2.2.2.1 h3
  rw [m5Os_eq] at hVn hVl hVF
  have hlen := m5_fix_len hVn hVl hVF
  exact ⟨hVn, hVl, hVF, by omega⟩

/-- **No twins in Case 3 under the thresholds** (`hnt₃` of `RunsWithin.m5StepCJProg_ns`):
`m5_no_twins` under `Thresholds K n k`, with `k ≤ tOf |Vx|` from `2|Vx| > m` and `4k ≤ m`. -/
theorem ss_m5_hnt₃ {K : ℕ → ℕ} (hTh : Thresholds K n k) (h4k : 4 * k ≤ N - n) :
    ∀ (hC : CertSetting (GensData.denote N gs) n) (φ : strGroup hC →* Perm (Fin (N - n))),
      IsPhi hC φ → ∀ fxs ex fys ey, M5Full (D := Ty.unit) ssDV hC φ k sIn xy.1 fxs ex →
      M5Full (D := Ty.unit) ssDV hC φ k sIn xy.2 fys ey →
      m5Sel ssCtx.O n N (N, fxs, ex) (N, fys, ey) = 3 →
      ¬ Case3.C3Twins φ (strOn hC.le (xy.1.denote N)) k
        (fixPtsD (m5Os ssCtx.O n N (N, fxs, ex))) := by
  intro hC φ hφ fxs ex fys ey hF _ hsel
  obtain ⟨h1, h2⟩ := m5Sel_three hsel
  obtain ⟨hVn, hVl, hVF, hV2⟩ := ss_m5_c3_facts hF h1 h2
  exact m5_no_twins hφ hTh _ (m5Fmap_base hC φ k _) hVl hVn hVF (by unfold Case3.tOf; omega)

/-- **Case 3's partition structures are small** (`hpart₃` of `RunsWithin.m5StepCJProg_ns`): a
first structure that is not a Johnson one is a colored `t`-partition with `4t ≤ 3m`, from
`t ≤ max ((|Vx| + 3)/2) (m − tOf |Vx| − 1)` (`firstStructD_partLe`, with no twins) and
`2|Vx| > m`. -/
theorem ss_m5_hpart₃ {K : ℕ → ℕ} (hTh : Thresholds K n k) (h4k : 4 * k ≤ N - n)
    (hk2 : 2 ≤ k) (hm : 12 ≤ N - n) :
    ∀ (hC : CertSetting (GensData.denote N gs) n) (φ : strGroup hC →* Perm (Fin (N - n))),
      IsPhi hC φ → ∀ fxs ex fys ey, M5Full (D := Ty.unit) ssDV hC φ k sIn xy.1 fxs ex →
      M5Full (D := Ty.unit) ssDV hC φ k sIn xy.2 fys ey →
      m5Sel ssCtx.O n N (N, fxs, ex) (N, fys, ey) = 3 → ∀ X₀,
      Case3.C3First φ (strOn hC.le (xy.1.denote N)) (N - n) k
        (fixPtsD (m5Os ssCtx.O n N (N, fxs, ex))) X₀ → X₀.1 ≠ 2 →
      ∃ (p : CPart (Fin (N - n))) (t : ℕ), (Case2b.outOps (N - n)).dec X₀ = some (Sum.inl p) ∧
        IsColPart Finset.univ t p ∧ 4 * t ≤ 3 * (N - n) := by
  intro hC φ hφ fxs ex fys ey hF hFy hsel X₀ hX₀ hX₂
  have hnt := ss_m5_hnt₃ (xy := xy) (gs := gs) hTh h4k hC φ hφ fxs ex fys ey hF hFy hsel
  obtain ⟨h1, h2⟩ := m5Sel_three hsel
  obtain ⟨hVn, hVl, -, hV2⟩ := ss_m5_c3_facts hF h1 h2
  have hVm := ss_fixPts_le (e := ex) hF.1.1 hF.base_inv
  obtain ⟨cXX, hch, hfirst⟩ := hX₀
  obtain ⟨p, t, hdec, hp, ht⟩ := Case3.firstStructD_partLe hVl hVn _ hk2 (by omega)
    (fun T hT => not_lt.1 fun hlt => hnt ⟨cXX, hch, T, hlt, hT⟩) hfirst hX₂
  refine ⟨p, t, hdec, hp, ?_⟩
  unfold Case3.thr at ht
  rcases le_total (((fixPtsD (m5Os ssCtx.O n N (N, fxs, ex))).length + 3) / 2)
      (N - n - ((fixPtsD (m5Os ssCtx.O n N (N, fxs, ex))).length + 1) / 2 - 1) with hc | hc
  · rw [max_eq_right hc] at ht
    omega
  · rw [max_eq_left hc] at ht
    omega

/-- Case 2b, Johnson leaves: every orbit of reduce-and-derive, with the derived hints' Johnson
fallback at the labels' bound `labLen L · λ(m)` (`rd_orbit_cj_ssL`). -/
theorem ss_m5_hDJ₂_lab (hNs : N * N ≤ sIn) (hgsv : GensData.AllValid N gs)
    (hgsl : gs.length ≤ sIn) (hG : IsInvariant (GensData.denote N gs) (baseSet n N))
    (halt : alternatingGroup (Fin (N - n)) ≤ (baseHom (GensData.denote N gs) n hG).range) {Bd : ℕ}
    (hBd : ssBdJU n N w.1.length L.size sIn (labLen L * lam (N - n)) ≤ Bd) :
    ∀ (hC : CertSetting (GensData.denote N gs) n) (φ : strGroup hC →* Perm (Fin (N - n))), IsPhi hC
      φ → ∀ fs e, M5Full (D := Ty.unit) ssDV hC φ k sIn xy.1 fs e → (m5Cs ssCtx.O n N (N, fs, e)).1
      = 2 → m5IsA ssCtx.O n N (N, fs, e) = false → ∀ X₀, m5Leaf2b ssCtx.O N n (N, fs, e) (m5Cs
      ssCtx.O n N (N, fs, e)).2 = some X₀ → X₀.1 = 2 → CJFacts (N - n) (cjFirst2bD N n (m5Cs ssCtx.O
      n N (N, fs, e)).2 (Case2b.degD ssCtx.O N n (N, fs, e) (m5Cs ssCtx.O n N (N, fs, e)).2 - 1) X₀)
      → ∀ gs' d' O', RDSet (D := Ty.unit) ssDV n N gs w L (Giant.g1Model ssCtx.O n (N, gs, ())
      (cjohnOps (N - n)) (cjFirst2bD N n (m5Cs ssCtx.O n N (N, fs, e)).2 (Case2b.degD ssCtx.O N n
      (N, fs, e) (m5Cs ssCtx.O n N (N, fs, e)).2 - 1) X₀)).2.1 sIn gs' d' O' → RDOrbit ssCtx body
      ssDV n N w L (2, cjFirst2bD N n (m5Cs ssCtx.O n N (N, fs, e)).2 (Case2b.degD ssCtx.O N n (N,
      fs, e) (m5Cs ssCtx.O n N (N, fs, e)).2 - 1) X₀) sIn Bd gs' d' O' := by
  intro hC φ hφ fs e hF _ _ X₀ _ _ hcj gs' d' O' hset
  obtain ⟨t, hJ⟩ := hcj.2
  have hOa : MeetsContractOn ssDV alignOps ssCtx.O := fun op x _ hx => ssOracle_meets op x hx
  obtain ⟨-, hKb, hfix⟩ := ar_g1_facts hOa (fun _ _ _ h => h) (ssBoundsS _ sIn ⊤ hNs)
    ⟨hgsv, trivial⟩ le_top hG halt (cjohnOps_spec _) hcj.1
    (BlA := Sims.liftCost N sIn (N - n) + 7) (fun π => by
      change Sims.liftCost N gs.length (baseWin n N).1.length + 7 ≤ _
      rw [baseWin_length]
      exact Nat.add_le_add_right (rd_liftCost_mono₂ le_rfl hgsl le_rfl) 7)
  exact (rd_orbit_cj_ssL (st := (2, _)) rfl hKb hcj.1 hJ hfix hNs gs' d' O' hset).mono hBd

/-- Case 3, Johnson leaves: every orbit of reduce-and-derive, with the derived hints' Johnson
fallback at the labels' bound `labLen L · λ(m)` (`rd_orbit_cj_ssL`). -/
theorem ss_m5_hDJ₃_lab (hNs : N * N ≤ sIn) (hgsv : GensData.AllValid N gs)
    (hgsl : gs.length ≤ sIn) (hG : IsInvariant (GensData.denote N gs) (baseSet n N))
    (halt : alternatingGroup (Fin (N - n)) ≤ (baseHom (GensData.denote N gs) n hG).range) {Bd : ℕ}
    (hBd : ssBdJU n N w.1.length L.size sIn (labLen L * lam (N - n)) ≤ Bd) :
    ∀ (hC : CertSetting (GensData.denote N gs) n) (φ : strGroup hC →* Perm (Fin (N - n))), IsPhi hC
      φ → ∀ fs e, M5Full (D := Ty.unit) ssDV hC φ k sIn xy.1 fs e → (m5Cs ssCtx.O n N (N, fs, e)).1
      ≠ 1 → (m5Cs ssCtx.O n N (N, fs, e)).1 ≠ 2 → ∀ cXX X₀, Case3.ColChar φ (strOn hC.le
      (xy.1.denote N)) (strOn hC.le (xy.1.denote N)) k (fixPtsD (m5Os ssCtx.O n N (N, fs,
      e))).length (fixPtsD (m5Os ssCtx.O n N (N, fs, e))) (fixPtsD (m5Os ssCtx.O n N (N, fs, e)))
      cXX → Case3.firstStructD (N - n) k (fixPtsD (m5Os ssCtx.O n N (N, fs, e))) (Case3.colXD cXX k
      (fixPtsD (m5Os ssCtx.O n N (N, fs, e))).length) = some X₀ → X₀.1 = 2 → CJFacts (N - n)
      (cjFirst3D (N - n) k (fixPtsD (m5Os ssCtx.O n N (N, fs, e))) (Case3.colXD cXX k (fixPtsD (m5Os
      ssCtx.O n N (N, fs, e))).length) X₀) → ∀ gs' d' O', RDSet (D := Ty.unit) ssDV n N gs w L
      (Giant.g1Model ssCtx.O n (N, gs, ()) (cjohnOps (N - n)) (cjFirst3D (N - n) k (fixPtsD (m5Os
      ssCtx.O n N (N, fs, e))) (Case3.colXD cXX k (fixPtsD (m5Os ssCtx.O n N (N, fs, e))).length)
      X₀)).2.1 sIn gs' d' O' → RDOrbit ssCtx body ssDV n N w L (2, cjFirst3D (N - n) k (fixPtsD
      (m5Os ssCtx.O n N (N, fs, e))) (Case3.colXD cXX k (fixPtsD (m5Os ssCtx.O n N (N, fs,
      e))).length) X₀) sIn Bd gs' d' O' := by
  intro hC φ hφ fs e hF _ _ cXX X₀ _ _ _ hcj gs' d' O' hset
  obtain ⟨t, hJ⟩ := hcj.2
  have hOa : MeetsContractOn ssDV alignOps ssCtx.O := fun op x _ hx => ssOracle_meets op x hx
  obtain ⟨-, hKb, hfix⟩ := ar_g1_facts hOa (fun _ _ _ h => h) (ssBoundsS _ sIn ⊤ hNs)
    ⟨hgsv, trivial⟩ le_top hG halt (cjohnOps_spec _) hcj.1
    (BlA := Sims.liftCost N sIn (N - n) + 7) (fun π => by
      change Sims.liftCost N gs.length (baseWin n N).1.length + 7 ≤ _
      rw [baseWin_length]
      exact Nat.add_le_add_right (rd_liftCost_mono₂ le_rfl hgsl le_rfl) 7)
  exact (rd_orbit_cj_ssL (st := (2, _)) rfl hKb hcj.1 hJ hfix hNs gs' d' O' hset).mono hBd

end Discharge

/-! ### The work -/

section Work

/-- **M5's dispatch work without stuck orbits as a function of its data**: the sum of every
case's work in `m5WnsCJ` (no kernel reduction, factor `m` on the partition routes), at the data
`g`, `P₁`, `P₂`, `nΦ`, `mx`, `my`, `nx`, `ny`, `j`, `cl`, `ol` of `m5DispNum`. -/
def m5DispNumNs (n N k s sIn Bgen Blift Bo Bd wl : ℕ) (β : M5Bounds)
    (Bst Btr Borb Bkg Bko Bks : ℕ) (Bo' Bs' Bt' : ℕ → ℕ) (uB Bg1J₂ Bg1J₃ : ℕ)
    (g P₁ P₂ nΦ mx my nx ny j cl ol : ℕ) : ℕ :=
  (Giant.case1Cost n N g P₁ β.Box β.Boy β.BgP β.Bmem β.BkA β.BlA β.Bg1₁ Bgen
    (m5Wb N n wl s sIn (N - n) Bd Blift Bgen Bo 0) sIn + 16) +
  (c2aWork n N g P₂ nΦ β.BgP β.Bmem β.BkA β.BlA β.Bg1₂ₐ β.Bgen₂ₐ sIn Bst Borb β.Bpb wl s
    β.sK β.Bgm β.Blift β.Bker β.Bgn + 30) +
  (c3Work n N sIn g k mx my (Case2b.sojZ (N - n)) β.BgP β.Bmem β.BkA β.BlA β.Bg1₃
      β.Bgen₃ Bst Btr Borb Bkg Bko Bks β.Bgk β.Bgs wl
      (m5Wb N n wl s sIn (N - n) Bd Blift Bgen Bo 0) + wl + 3 +
    c3PreWork N n sIn k mx my Bst Btr Borb Bkg Bko Bks β.Bgk β.BlA β.Bgs wl
      (Case2b.sojZ (N - n)) +
    c3CJCost n N sIn g k mx my (Case2b.sojZ (N - n)) β.BgP β.Bmem β.BkA β.BlA Bg1J₃ Bgen
      (m5Wb N n wl s sIn (max (N - n) uB.factorial) Bd Blift Bgen Bo 0) +
    2 * fixPtsCost (N - n) + 20) +
  (c2bJTestCost N n sIn nx j Bst β.Bg (Case2b.sojZ (N - n)) Bo' Bs' Bt' + 1 +
    (c2bCJCost n N sIn g nx ny j cl Bst β.Bg (Case2b.sojZ (N - n)) β.BgP β.Bmem β.BkA β.BlA
        Bg1J₂ Bgen (m5Wb N n wl s sIn (max (N - n) uB.factorial) Bd Blift Bgen Bo 0) Bo' Bs'
        Bt' +
      Case2b.c2bCost n N sIn g nx ny j ol Bst β.Bg (Case2b.sojZ (N - n)) β.BgP β.Bmem β.BkA
        β.BlA β.Bg1₂ᵦ β.Bgen₂ᵦ (m5Wb N n wl s sIn (N - n) Bd Blift Bgen Bo 0) Bo' Bs' Bt') +
    28) + 28

/-- **The dispatch's work without stuck orbits is at most `m5DispNumNs` at its data**, with
Case 2b's depth taken only in Case 2b (`0` otherwise): only there does the work depend on it. -/
theorem m5WnsCJ_le {D : Ty} (O : Oracle (groupSig D)) (n N k s sIn Bgen Blift Bo Bd : ℕ)
    (G Fx Fy : GroupData D.denote) (wl : ℕ) (β : M5Bounds) (Bst Btr Borb Bkg Bko Bks : ℕ)
    (Bo' Bs' Bt' : ℕ → ℕ) (uB Bg1J₂ Bg1J₃ : ℕ) :
    m5WnsCJ O n N k s sIn Bgen Blift Bo Bd G Fx Fy wl β Bst Btr Borb Bkg Bko Bks Bo' Bs' Bt' uB
        Bg1J₂ Bg1J₃ ≤
      m5DispNumNs n N k s sIn Bgen Blift Bo Bd wl β Bst Btr Borb Bkg Bko Bks Bo' Bs' Bt' uB
        Bg1J₂ Bg1J₃ G.2.1.length (partGensD (N - n) (Giant.orbitPartModel O n N Fx)).length
        ((setOps (N - n)).gens (m5Cs O n N Fx).2).length (m5Cs O n N Fx).2.length
        (fixPtsD (m5Os O n N Fx)).length (fixPtsD (m5Os O n N Fy)).length
        (m5Cs O n N Fx).2.length (m5Cs O n N Fy).2.length
        (if m5Sel O n N Fx Fy = 4 then Case2b.degD O N n Fx (m5Cs O n N Fx).2 - 1 else 0)
        (((m5Leaf2b O N n Fx (m5Cs O n N Fx).2).map fun X₀ =>
          (cjohnGensD (N - n) (cjFirst2bD N n (m5Cs O n N Fx).2
            (Case2b.degD O N n Fx (m5Cs O n N Fx).2 - 1) X₀)).length).getD 0)
        (((m5Leaf2b O N n Fx (m5Cs O n N Fx).2).map fun X₀ =>
          (Case2b.outGensD (N - n) X₀).length).getD 0) := by
  unfold m5WnsCJ m5DispNumNs
  split
  · omega
  · omega
  · omega
  · next h =>
    rw [if_pos' h]
    rcases hX : m5Leaf2b O N n Fx (m5Cs O n N Fx).2 with _ | X₀
    · simp only [Option.map_none, Option.getD_none]
      omega
    · simp only [Option.map_some, Option.getD_some]
      split_ifs <;> omega
  · omega

/-- **M5's work without stuck orbits with Schreier–Sims at given sizes**: as `m5WorkRaw`, with
the dispatch's work `m5DispNumNs` (no kernel, so no `m!` representatives), Case 2b's depth at
most `jB`, the bounds `ssM5βns`, and the derived hints' Johnson fallback at `uB` (`ssBdJU`). -/
def m5WorkRawNs (n m k p s sIn Lg uB jB : ℕ) : ℕ :=
  2 * (certCount (n + m) n k * 4 +
      certWork (n + m) n k sIn (stabCost (n + m) sIn + 5) (transCost (n + m) sIn + 5)
        (orbitsCost (n + m) sIn (n + m) + 5) (genCost k (k * (sIn + 1)) + 2)
        (orbitsCost k sIn k + 5) (stabCost k sIn + 5) (ssM5βns (n + m) m k sIn s jB).Bgk
        (ssM5βns (n + m) m k sIn s jB).BlA (ssM5βns (n + m) m k sIn s jB).Bgs
        (ssM5βns (n + m) m k sIn s jB).BF) +
    2 * supTo (fun a => m5CaseCost n (n + m) (orbitsCost (n + m) sIn (n + m) + 5)
      (Case2b.degCost (n + m) n a a sIn (stabCost (n + m) sIn + 5)
        (ssM5βns (n + m) m k sIn s jB).Bg (orbitsCost a (a * a) a + 5)
        (stabCost a (a * a) + 5))) m +
    envSup [sIn, m * m + m, m * m + m, m, m, m, m, m, jB, cjB m, olB m] (fun ds =>
      m5DispNumNs n (n + m) k s sIn (genCost (n + m) Lg + 2) (Sims.liftCost (n + m) sIn n + 7)
        (orbitsCost (n + m) sIn (n + m) + 5)
        (ssBdF n (n + m) p sIn + ssBdJU n (n + m) p p sIn uB) p (ssM5βns (n + m) m k sIn s jB)
        (stabCost (n + m) sIn + 5) (transCost (n + m) sIn + 5)
        (orbitsCost (n + m) sIn (n + m) + 5) (genCost k (k * (sIn + 1)) + 2)
        (orbitsCost k sIn k + 5) (stabCost k sIn + 5) (fun M => orbitsCost M (M * M) M + 5)
        (fun M => stabCost M (M * M) + 5) (fun M => transCost M (M * M) + 5) uB
        (ssBg1J (n + m) m) (ssBg1J (n + m) m) (ds.getD 0 0) (ds.getD 1 0) (ds.getD 2 0)
        (ds.getD 3 0) (ds.getD 4 0) (ds.getD 5 0) (ds.getD 6 0) (ds.getD 7 0) (ds.getD 8 0)
        (ds.getD 9 0) (ds.getD 10 0)) + 15

/-- **The work of M5 without stuck orbits with Schreier–Sims**: the monotone envelope of
`m5WorkRawNs`. -/
def m5WorkNsSS (n m k p s sIn Lg uB jB : ℕ) : ℕ :=
  envSup [n, m, k, p, s, sIn, Lg, uB, jB] fun xs =>
    m5WorkRawNs (xs.getD 0 0) (xs.getD 1 0) (xs.getD 2 0) (xs.getD 3 0) (xs.getD 4 0)
      (xs.getD 5 0) (xs.getD 6 0) (xs.getD 7 0) (xs.getD 8 0)

theorem m5WorkNsSS_mono {n n' m m' k k' p p' s s' sIn sIn' Lg Lg' uB uB' jB jB' : ℕ}
    (hn : n ≤ n') (hm : m ≤ m') (hk : k ≤ k') (hp : p ≤ p') (hs : s ≤ s') (hI : sIn ≤ sIn')
    (hg : Lg ≤ Lg') (hu : uB ≤ uB') (hj : jB ≤ jB') :
    m5WorkNsSS n m k p s sIn Lg uB jB ≤ m5WorkNsSS n' m' k' p' s' sIn' Lg' uB' jB' :=
  envSup_mono (.cons hn (.cons hm (.cons hk (.cons hp (.cons hs (.cons hI (.cons hg
    (.cons hu (.cons hj .nil))))))))) _

theorem le_m5WorkNsSS (n m k p s sIn Lg uB jB : ℕ) :
    m5WorkRawNs n m k p s sIn Lg uB jB ≤ m5WorkNsSS n m k p s sIn Lg uB jB := by
  unfold m5WorkNsSS
  refine le_of_eq_of_le ?_ (le_envSup (forall₂_le_refl _) _)
  simp only [List.getD_cons_zero, List.getD_cons_succ]

/-- **M5's core work without stuck orbits with Schreier–Sims is at most `m5WorkRawNs`**, given
the bounds on its data and Case 2b's depth at most `jB` in Case 2b. -/
theorem m5CoreWorkNsCJ_le {n m k s sIn Lg uB jB : ℕ} {G Fx Fy : GroupData Unit} {p : ℕ}
    (hg : G.2.1.length ≤ sIn) (hΦx : (m5Cs ssCtx.O n (n + m) Fx).2.length ≤ m)
    (hΦy : (m5Cs ssCtx.O n (n + m) Fy).2.length ≤ m)
    (hmx : (fixPtsD (m5Os ssCtx.O n (n + m) Fx)).length ≤ m)
    (hmy : (fixPtsD (m5Os ssCtx.O n (n + m) Fy)).length ≤ m)
    (hj : m5Sel ssCtx.O n (n + m) Fx Fy = 4 →
      Case2b.degD ssCtx.O (n + m) n Fx (m5Cs ssCtx.O n (n + m) Fx).2 - 1 ≤ jB) :
    m5CoreWorkNsCJ ssCtx.O n (n + m) k s sIn (genCost (n + m) Lg + 2)
        (Sims.liftCost (n + m) sIn n + 7) (orbitsCost (n + m) sIn (n + m) + 5)
        (ssBdF n (n + m) p sIn + ssBdJU n (n + m) p p sIn uB) G Fx Fy p
        (ssM5βns (n + m) m k sIn s jB)
        (stabCost (n + m) sIn + 5) (transCost (n + m) sIn + 5)
        (orbitsCost (n + m) sIn (n + m) + 5) (genCost k (k * (sIn + 1)) + 2)
        (orbitsCost k sIn k + 5) (stabCost k sIn + 5) (fun M => orbitsCost M (M * M) M + 5)
        (fun M => stabCost M (M * M) + 5) (fun M => transCost M (M * M) + 5) uB
        (ssBg1J (n + m) m) (ssBg1J (n + m) m) ≤ m5WorkRawNs n m k p s sIn Lg uB jB := by
  have hm : n + m - n = m := by omega
  have hdisp := m5WnsCJ_le ssCtx.O n (n + m) k s sIn (genCost (n + m) Lg + 2)
    (Sims.liftCost (n + m) sIn n + 7) (orbitsCost (n + m) sIn (n + m) + 5)
    (ssBdF n (n + m) p sIn + ssBdJU n (n + m) p p sIn uB) G Fx Fy p
    (ssM5βns (n + m) m k sIn s jB)
    (stabCost (n + m) sIn + 5) (transCost (n + m) sIn + 5) (orbitsCost (n + m) sIn (n + m) + 5)
    (genCost k (k * (sIn + 1)) + 2) (orbitsCost k sIn k + 5) (stabCost k sIn + 5)
    (fun M => orbitsCost M (M * M) M + 5) (fun M => stabCost M (M * M) + 5)
    (fun M => transCost M (M * M) + 5) uB (ssBg1J (n + m) m) (ssBg1J (n + m) m)
  have hj' : (if m5Sel ssCtx.O n (n + m) Fx Fy = 4 then
      Case2b.degD ssCtx.O (n + m) n Fx (m5Cs ssCtx.O n (n + m) Fx).2 - 1 else 0) ≤ jB := by
    split_ifs with h
    · exact hj h
    · exact Nat.zero_le _
  have hcl : ((m5Leaf2b ssCtx.O (n + m) n Fx (m5Cs ssCtx.O n (n + m) Fx).2).map fun X₀ =>
      (cjohnGensD (n + m - n) (cjFirst2bD (n + m) n (m5Cs ssCtx.O n (n + m) Fx).2
        (Case2b.degD ssCtx.O (n + m) n Fx (m5Cs ssCtx.O n (n + m) Fx).2 - 1) X₀)).length).getD
        0 ≤ cjB m := by
    rcases hX : m5Leaf2b ssCtx.O (n + m) n Fx (m5Cs ssCtx.O n (n + m) Fx).2 with _ | X₀
    · simp only [Option.map_none, Option.getD_none]
      exact Nat.zero_le _
    · simp only [Option.map_some, Option.getD_some]
      have hs := Case2b.outSize_firstLeafD hX
      refine (cjohnGensD_length_le_bound (Case2b.cp2_jbound_le hs)).trans (le_of_eq ?_)
      rw [hm]
      rfl
  have hol : ((m5Leaf2b ssCtx.O (n + m) n Fx (m5Cs ssCtx.O n (n + m) Fx).2).map fun X₀ =>
      (Case2b.outGensD (n + m - n) X₀).length).getD 0 ≤ olB m := by
    rcases hX : m5Leaf2b ssCtx.O (n + m) n Fx (m5Cs ssCtx.O n (n + m) Fx).2 with _ | X₀
    · simp only [Option.map_none, Option.getD_none]
      exact Nat.zero_le _
    · simp only [Option.map_some, Option.getD_some]
      have hs := Case2b.outSize_firstLeafD hX
      refine (outGensD_length_le_bound hs).trans (le_of_eq ?_)
      rw [hm]
      rfl
  have hP₁ : (partGensD (n + m - n) (Giant.orbitPartModel ssCtx.O n (n + m) Fx)).length ≤
      m * m + m := (partGensD_length_le _ _).trans (le_of_eq (by rw [hm]))
  have hP₂ : ((setOps (n + m - n)).gens (m5Cs ssCtx.O n (n + m) Fx).2).length ≤ m * m + m :=
    (partGensD_length_le _ _).trans (le_of_eq (by rw [hm]))
  have henv := le_envSup (as := [sIn, m * m + m, m * m + m, m, m, m, m, m, jB, cjB m, olB m])
    (.cons hg (.cons hP₁ (.cons hP₂ (.cons hΦx (.cons hmx (.cons hmy (.cons hΦx (.cons hΦy
      (.cons hj' (.cons hcl (.cons hol .nil)))))))))))
    (fun ds =>
      m5DispNumNs n (n + m) k s sIn (genCost (n + m) Lg + 2) (Sims.liftCost (n + m) sIn n + 7)
        (orbitsCost (n + m) sIn (n + m) + 5)
        (ssBdF n (n + m) p sIn + ssBdJU n (n + m) p p sIn uB) p (ssM5βns (n + m) m k sIn s jB)
        (stabCost (n + m) sIn + 5) (transCost (n + m) sIn + 5)
        (orbitsCost (n + m) sIn (n + m) + 5) (genCost k (k * (sIn + 1)) + 2)
        (orbitsCost k sIn k + 5) (stabCost k sIn + 5) (fun M => orbitsCost M (M * M) M + 5)
        (fun M => stabCost M (M * M) + 5) (fun M => transCost M (M * M) + 5) uB
        (ssBg1J (n + m) m) (ssBg1J (n + m) m) (ds.getD 0 0) (ds.getD 1 0) (ds.getD 2 0)
        (ds.getD 3 0) (ds.getD 4 0) (ds.getD 5 0) (ds.getD 6 0) (ds.getD 7 0) (ds.getD 8 0)
        (ds.getD 9 0) (ds.getD 10 0))
  simp only [List.getD_cons_zero, List.getD_cons_succ] at henv
  have hdx : m5DecCost ssCtx.O n (n + m) sIn (stabCost (n + m) sIn + 5)
      (orbitsCost (n + m) sIn (n + m) + 5) (ssM5βns (n + m) m k sIn s jB).Bg
      (fun M => orbitsCost M (M * M) M + 5) (fun M => stabCost M (M * M) + 5) Fx ≤
      supTo (fun a => m5CaseCost n (n + m) (orbitsCost (n + m) sIn (n + m) + 5)
        (Case2b.degCost (n + m) n a a sIn (stabCost (n + m) sIn + 5)
          (ssM5βns (n + m) m k sIn s jB).Bg (orbitsCost a (a * a) a + 5)
          (stabCost a (a * a) + 5))) m :=
    le_supTo (f := fun a => m5CaseCost n (n + m) (orbitsCost (n + m) sIn (n + m) + 5)
      (Case2b.degCost (n + m) n a a sIn (stabCost (n + m) sIn + 5)
        (ssM5βns (n + m) m k sIn s jB).Bg (orbitsCost a (a * a) a + 5)
        (stabCost a (a * a) + 5))) hΦx
  have hdy : m5DecCost ssCtx.O n (n + m) sIn (stabCost (n + m) sIn + 5)
      (orbitsCost (n + m) sIn (n + m) + 5) (ssM5βns (n + m) m k sIn s jB).Bg
      (fun M => orbitsCost M (M * M) M + 5) (fun M => stabCost M (M * M) + 5) Fy ≤
      supTo (fun a => m5CaseCost n (n + m) (orbitsCost (n + m) sIn (n + m) + 5)
        (Case2b.degCost (n + m) n a a sIn (stabCost (n + m) sIn + 5)
          (ssM5βns (n + m) m k sIn s jB).Bg (orbitsCost a (a * a) a + 5)
          (stabCost a (a * a) + 5))) m :=
    le_supTo (f := fun a => m5CaseCost n (n + m) (orbitsCost (n + m) sIn (n + m) + 5)
      (Case2b.degCost (n + m) n a a sIn (stabCost (n + m) sIn + 5)
        (ssM5βns (n + m) m k sIn s jB).Bg (orbitsCost a (a * a) a + 5)
        (stabCost a (a * a) + 5))) hΦy
  unfold m5CoreWorkNsCJ m5WorkRawNs
  omega

end Work

/-! ### The step -/

section Step

theorem ssBdJU_mono_u {n N p Ls S u u' : ℕ} (h : u ≤ u') :
    ssBdJU n N p Ls S u ≤ ssBdJU n N p Ls S u' := by
  unfold ssBdJU deriveCJCost johnStepCost jfallbackCost CertProg.kerACost
  have := Nat.factorial_le h
  gcongr

variable {a b : Ty} {body : a.denote → Prog (groupSig Ty.unit) (a, b) Ty.denote b}
  {sub : HInstData Ty.unit → Prog (groupSig Ty.unit) (a, b) Ty.denote (Ty.answer Ty.unit)}

/-- **M5 without stuck orbits with Schreier–Sims, before the explicit work**
(`RunsWithin.m5StepCJProg_ns` at `ssCtx` with `ssM5βns`; stage 14j-6b-1): every backend
hypothesis is proved by `RunsWithin.m5StepCJProg_ss₀`'s charge lemmas, and the hypotheses
without stuck orbits by this file's lemmas (items 1–4 of `PLAN-14.md` §14.11), at the union-cell
bound `labLen L · λ(m)` of the parent's labels. -/
theorem RunsWithin.m5StepCJProg_ns_ss₀ {C : ℕ → Option ℕ → ℕ} {s : ℕ}
    {xyP : StrData × StrData} {wP : WinData} {σP : PermData} {NP : ℕ} {gsP : GensData}
    {n₀ nP : ℕ} {LP : LabelData}
    (hIP : HInstValid ssDV
      (((xyP, (wP, (σP, (NP, gsP, ())))), (n₀, (nP, some LP))) : HInstData Ty.unit))
    {hBP : IsInvariant (GensData.denote NP gsP) (baseSet nP NP)}
    (haltP : alternatingGroup (Fin (NP - nP)) ≤ (baseHom (GensData.denote NP gsP) nP hBP).range)
    {sIn : ℕ}
    (hsubP : HSubSolves ssCtx body ssDV sub
      (fun J => SizeChild (max sIn (supTo (fun M => M * M) (wP.1.length / 2)))
        (((xyP, (wP, (σP, (NP, gsP, ())))), (n₀, (nP, some LP))) : HInstData Ty.unit) J ∧
        StepChild wP.1.length (NP - nP) (J.winSize, J.baseOpt)) C s)
    {k : ℕ} (h5 : 5 ≤ k) (hk : k + 2 ≤ NP - nP) (h2k : 2 * k ≤ NP - nP) (hm12 : 12 ≤ NP - nP)
    (hN : NP * NP ≤ sIn) (hgsP : gsP.length ≤ sIn)
    (hCmono : ∀ a b, a ≤ b → C a none ≤ C b none) (hs : s ≤ sIn)
    {Lg : ℕ} (hLgJ : max (NP - nP) (labLen LP * lam (NP - nP)).factorial * (sIn + 1) ≤ Lg)
    {jB : ℕ}
    (hLY : (c2bRj (NP - nP) jB + Case3.c3R k (NP - nP) (Case2b.sojZ (NP - nP))) * (sIn + 1) ≤ Lg)
    {st : ℕ × CJData} (hst : st.1 ≠ 2)
    -- the interfaces
    {T : ℕ → ℕ} (hT : AltQuot.TransitivityBound T) (hjB : ∀ m' ≤ NP - nP, T m' ≤ jB + 1)
    (h4j : 4 * jB ≤ NP - nP) {K : ℕ → ℕ} (hTh : Thresholds K wP.1.length k)
    (h4k : 4 * k ≤ NP - nP) :
    ∃ (fxs fys : GensData) (ex ey : Ty.unit.denote) (ans : AnswerData Ty.unit)
      (ch : List (ℕ × Option ℕ)),
      (∃ (hC : CertSetting (GensData.denote (rbPts nP NP wP).length
          (generateModel (rbPts nP NP wP).length (rbGens nP NP wP gsP))) wP.1.length)
          (φ : strGroup hC →* Perm (Fin ((rbPts nP NP wP).length - wP.1.length))),
        IsPhi hC φ ∧
        M5Full (D := Ty.unit) ssDV hC φ k sIn (StrData.restrictTo (rbPts nP NP wP) xyP.1) fxs ex ∧
        M5Full (D := Ty.unit) ssDV hC φ k sIn (StrData.restrictComp (rbPts nP NP wP) xyP.2 σP)
          fys ey) ∧
      RunsWithin ssCtx body (Main.m5StepCJProg sub
          (((xyP, (wP, (σP, (NP, gsP, ())))), (n₀, (nP, some LP))) : HInstData Ty.unit) LP k st)
        ans
        (rbCost NP wP.1.length (NP - nP) gsP.length
          ((ch.map fun x => C x.1 x.2).sum +
            2 * certCount (rbPts nP NP wP).length wP.1.length k * C (wP.1.length / k) none +
            m5CKCJ ssCtx.O wP.1.length (rbPts nP NP wP).length k
              ((rbPts nP NP wP).length, fxs, ex) ((rbPts nP NP wP).length, fys, ey) *
              C (wP.1.length / k) none +
            m5CH ssCtx.O wP.1.length (rbPts nP NP wP).length sIn
              (WinData.ofPoints (rbPts nP NP wP).length (List.range wP.1.length)).1.length
              ((rbPts nP NP wP).length, fxs, ex) ((rbPts nP NP wP).length, fys, ey) *
              C ((WinData.ofPoints (rbPts nP NP wP).length (List.range wP.1.length)).1.length / 2)
                none +
            m5CoreWorkNsCJ ssCtx.O wP.1.length (rbPts nP NP wP).length k s sIn
              (genCost (rbPts nP NP wP).length Lg + 2)
              (Sims.liftCost (rbPts nP NP wP).length sIn wP.1.length + 7)
              (orbitsCost (rbPts nP NP wP).length sIn (rbPts nP NP wP).length + 5)
              (ssBdF wP.1.length (rbPts nP NP wP).length wP.1.length sIn +
                ssBdJU wP.1.length (rbPts nP NP wP).length wP.1.length wP.1.length sIn
                  (labLen LP * lam (NP - nP)))
              ((rbPts nP NP wP).length,
                generateModel (rbPts nP NP wP).length (rbGens nP NP wP gsP), ())
              ((rbPts nP NP wP).length, fxs, ex) ((rbPts nP NP wP).length, fys, ey)
              (WinData.ofPoints (rbPts nP NP wP).length (List.range wP.1.length)).1.length
              (ssM5βns (rbPts nP NP wP).length ((rbPts nP NP wP).length - wP.1.length) k sIn s
                jB)
              (stabCost (rbPts nP NP wP).length sIn + 5) (transCost (rbPts nP NP wP).length sIn + 5)
              (orbitsCost (rbPts nP NP wP).length sIn (rbPts nP NP wP).length + 5)
              (genCost k (k * (sIn + 1)) + 2) (orbitsCost k sIn k + 5) (stabCost k sIn + 5)
              (fun M => orbitsCost M (M * M) M + 5) (fun M => stabCost M (M * M) + 5)
              (fun M => transCost M (M * M) + 5) (labLen LP * lam (NP - nP))
              (ssBg1J (rbPts nP NP wP).length ((rbPts nP NP wP).length - wP.1.length))
              (ssBg1J (rbPts nP NP wP).length ((rbPts nP NP wP).length - wP.1.length)))
          sIn (NP * NP) (genCost (rbPts nP NP wP).length sIn + 2) (Sims.liftCost NP sIn NP + 7)
          (kerCost NP sIn NP + 5) (genCost NP (NP * NP + sIn) + 2)) ∧
      AnsOK ssDV NP (wP.denote NP) (PermData.denote NP σP) (GensData.denote NP gsP)
        (xyP.1.denote NP) (xyP.2.denote NP) ans ∧
      (∀ sGen, (∀ hs, GensData.AllValid NP hs →
          GensData.denote NP hs ≤ GensData.denote NP gsP →
          (ssCtx.O.run GroupOp.generate (NP, hs)).2.1.length ≤ sGen) →
        ∀ c : CosetData Ty.unit, ans = some c → c.2.gens.length ≤ sGen) ∧
      ChildList wP.1.length (m5CFnsCJ ssCtx.O wP.1.length (rbPts nP NP wP).length k
          ((rbPts nP NP wP).length, fxs, ex) ((rbPts nP NP wP).length, fys, ey)
          (labLen LP * lam (NP - nP)))
        (StepChild wP.1.length (NP - nP)) ch := by
  obtain ⟨hNle, hm, hrbv, hI', halt'⟩ := ss_m5_rb hIP haltP (by omega)
  have hNs : (rbPts nP NP wP).length * (rbPts nP NP wP).length ≤ sIn :=
    (Nat.mul_le_mul hNle hNle).trans hN
  have hgsv := (generateModel_spec hrbv).1
  have hgsl : (generateModel (rbPts nP NP wP).length (rbGens nP NP wP gsP)).length ≤ sIn :=
    (generateModel_spec hrbv).2.2.trans hNs
  have hG : IsInvariant (GensData.denote (rbPts nP NP wP).length
      (generateModel (rbPts nP NP wP).length (rbGens nP NP wP gsP)))
      (baseSet wP.1.length (rbPts nP NP wP).length) := hI'.base_inv
  have hkN : k ≤ (rbPts nP NP wP).length := by omega
  have hks : k * k ≤ sIn := (Nat.mul_le_mul hkN hkN).trans hNs
  have hsk : sIn ≤ k * (sIn + 1) := by nlinarith
  have hB := rd_ss_boundsS wP.1.length (rbPts nP NP wP).length sIn Lg hNs
  have hLg : (NP - nP) * (sIn + 1) ≤ Lg :=
    (Nat.mul_le_mul_right _ (le_max_left _ _)).trans hLgJ
  have hLY₂' : c2bRj ((rbPts nP NP wP).length - wP.1.length) jB * (sIn + 1) ≤ Lg := by
    rw [hm]
    exact (Nat.mul_le_mul_right _ (Nat.le_add_right _ _)).trans hLY
  have hLY₃' : Case3.c3R k ((rbPts nP NP wP).length - wP.1.length)
      (Case2b.sojZ ((rbPts nP NP wP).length - wP.1.length)) * (sIn + 1) ≤ Lg := by
    rw [hm]
    exact (Nat.mul_le_mul_right _ (Nat.le_add_left _ _)).trans hLY
  have hjB' : ∀ m' ≤ (rbPts nP NP wP).length - wP.1.length, T m' ≤ jB + 1 := by
    rw [hm]
    exact hjB
  have h4j' : 4 * jB ≤ (rbPts nP NP wP).length - wP.1.length := by rw [hm]; exact h4j
  have h4k' : 4 * k ≤ (rbPts nP NP wP).length - wP.1.length := by rw [hm]; exact h4k
  have hm12' : 12 ≤ (rbPts nP NP wP).length - wP.1.length := by omega
  have hUL : labLen (rbLabels wP LP) * lam ((rbPts nP NP wP).length - wP.1.length) ≤
      labLen LP * lam (NP - nP) := by
    rw [hm]
    exact Nat.mul_le_mul_right _ (labLen_rbLabels_le wP LP)
  have hBd : ∀ x : ℕ, ssBdF wP.1.length (rbPts nP NP wP).length
      (WinData.ofPoints (rbPts nP NP wP).length (List.range wP.1.length)).1.length sIn ≤
      ssBdF wP.1.length (rbPts nP NP wP).length wP.1.length sIn + x := by
    intro x
    rw [WinData.ofPoints_fst, List.length_range]
    exact Nat.le_add_right _ _
  have hBdJ : ssBdJU wP.1.length (rbPts nP NP wP).length
      (WinData.ofPoints (rbPts nP NP wP).length (List.range wP.1.length)).1.length
      (rbLabels wP LP).size sIn
      (labLen (rbLabels wP LP) * lam ((rbPts nP NP wP).length - wP.1.length)) ≤
      ssBdF wP.1.length (rbPts nP NP wP).length wP.1.length sIn +
        ssBdJU wP.1.length (rbPts nP NP wP).length wP.1.length wP.1.length sIn
          (labLen LP * lam (NP - nP)) := by
    rw [WinData.ofPoints_fst, List.length_range]
    have : (rbLabels wP LP).size = wP.1.length := by simp [rbLabels]
    rw [this]
    exact (ssBdJU_mono_u hUL).trans (Nat.le_add_left _ _)
  exact RunsWithin.m5StepCJProg_ns (X := ssCtx) (body := body) (sub := sub) (C := C) (s := s)
    (Bd := ssBdF wP.1.length (rbPts nP NP wP).length wP.1.length sIn +
      ssBdJU wP.1.length (rbPts nP NP wP).length wP.1.length wP.1.length sIn
        (labLen LP * lam (NP - nP)))
    (uB := labLen LP * lam (NP - nP))
    (Bg1J₂ := ssBg1J (rbPts nP NP wP).length ((rbPts nP NP wP).length - wP.1.length))
    (Bg1J₃ := ssBg1J (rbPts nP NP wP).length ((rbPts nP NP wP).length - wP.1.length))
    (sKR := NP * NP) (BgmR := genCost (rbPts nP NP wP).length sIn + 2)
    (BliftR := Sims.liftCost NP sIn NP + 7) (BkerR := kerCost NP sIn NP + 5)
    (BgnR := genCost NP (NP * NP + sIn) + 2)
    (fun op x _ hx => ssOracle_meets op x hx) (fun _ _ _ h => h) hIP haltP (sm := fun M => M * M)
    hsubP rfl rfl rfl rfl rfl h5 hk h2k hm12 (ssBoundsS _ sIn ⊤ hNs) hgsl le_top
    (ssBoundsS k sIn ⊤ hks) hsk ssBm hCmono hs hB hLg hst
    (ssM5βns (rbPts nP NP wP).length ((rbPts nP NP wP).length - wP.1.length) k sIn s jB)
    (ss_m5_hBgP (n := wP.1.length) (k := k) (sIn := sIn) (s := s) hgsl)
    (ss_m5_hBmem (n := wP.1.length) (k := k) (sIn := sIn) (s := s) hgsv hG)
    (hB.kernel _ () ⟨hgsv, trivial⟩ hgsl)
    (ss_m5_hBlA (n := wP.1.length) (k := k) (sIn := sIn) (s := s) hgsl)
    (ss_m5_hBg (n := wP.1.length) (k := k) (sIn := sIn) (s := s))
    (ss_m5_hBgk (n := wP.1.length) (k := k) (sIn := sIn) (s := s))
    (ss_m5_hBgs (n := wP.1.length) (k := k) (sIn := sIn) (s := s) hNs hgsv hgsl)
    (ss_m5_hBF (n := wP.1.length) (k := k) (sIn := sIn) (s := s))
    (ss_m5_hBox (n := wP.1.length) (k := k) (sIn := sIn) (s := s))
    (ss_m5_hBoy (n := wP.1.length) (k := k) (sIn := sIn) (s := s))
    (ss_m5_hBg1₁ (n := wP.1.length) (k := k) (sIn := sIn) (s := s) hgsv) (ss_m5_hD₁ hst hNs (hBd _))
    (ss_m5_hBg1₂ₐ (n := wP.1.length) (k := k) (sIn := sIn) (s := s) hgsv)
    (ss_m5_hBgen₂ₐ (n := wP.1.length) (k := k) (sIn := sIn) (s := s))
    (ss_m5_hBpb (n := wP.1.length) (k := k) (sIn := sIn) (s := s))
    (ss_m5_hBgm (n := wP.1.length) (k := k) (sIn := sIn) (s := s))
    (ss_m5_hBlift (n := wP.1.length) (k := k) (sIn := sIn) (s := s))
    (ss_m5_hBker (n := wP.1.length) (k := k) (sIn := sIn) (s := s)) ss_hsK
    (ss_m5_hBgn (n := wP.1.length) (k := k) (sIn := sIn) (s := s))
    (ss_m5_hBg1₂ᵦ (n := wP.1.length) (k := k) (sIn := sIn) (s := s) hgsv)
    (ss_m5_hBgen₂ᵦ_ns hT hNs hjB') (ss_m5_hD₂ᵦ hst hNs (hBd _))
    (ss_m5_hpart₂ᵦ hT hNs hjB' h4j' (by omega))
    (ss_m5_hBg1₃ (n := wP.1.length) (k := k) (sIn := sIn) (s := s) hgsv)
    (ss_m5_hBgen₃ (n := wP.1.length) (k := k) (sIn := sIn) (s := s)) (ss_m5_hD₃ hst hNs (hBd _))
    (ss_m5_hnt₃ hTh h4k') (ss_m5_hpart₃ hTh h4k' (by omega) hm12')
    hLgJ (ss_m5_hBg1J₂ hgsv) (ss_m5_hLY₂_ns hT hNs hjB' hLY₂')
    (ss_m5_hDJ₂_lab hNs hgsv hgsl hG halt' hBdJ)
    (fun hC φ hφ fs e hF h2 hA X₀ hX hX2 hcj gs' d' O' hset =>
      (ss_m5_hu₂_lab hC φ hφ fs e hF h2 hA X₀ hX hX2 hcj gs' d' O' hset).trans hUL)
    (ss_m5_hBg1J₃ hgsv) (ss_m5_hLY₃ hLY₃') (ss_m5_hDJ₃_lab hNs hgsv hgsl hG halt' hBdJ)
    (fun hC φ hφ fs e hF h1 h2 cXX X₀ hch hX hX2 hcj gs' d' O' hset =>
      (ss_m5_hu₃_lab hC φ hφ fs e hF h1 h2 cXX X₀ hch hX hX2 hcj gs' d' O' hset).trans hUL)
    (ss_m5_hBgmR hgsP) (ss_m5_hBliftR hgsP hNle) (ss_m5_hBkerR hgsP hNle) (ss_m5_hsKR hIP)
    ss_m5_hBgnR

/-- **M5 without stuck orbits with Schreier–Sims** (stage 14j-6b-1, `PLAN-14.md` §14.11 item
5). For a valid hinted instance whose base action is a giant, with M5's numeric conditions on
`k`, at most `sIn ≥ NP²` generators, a sub-solver with the spec's predicate (`sm M = M²`) whose
cost is monotone in the window, `s ≤ sIn`, a state `st` without a Johnson structure, and:
* `Lg` large enough for `generate`'s inputs: `max(m, uB!)`, Case 2b's count `c2bRj m jB` and Case
  3's `c3R`, with `uB = labLen L · λ(m)`;
* `TransitivityBound T` with a depth bound `jB` (`T m' ≤ jB + 1` for `m' ≤ m`) and `4 jB ≤ m`;
* `Thresholds K |W| k` and `4k ≤ m`:

the answer is correct; the children are `StepChild |W| m` with factor `m5CFnsCJ … uB` (no `m!`);
the work is `m5WorkNsSS |W| m k |W| s sIn Lg uB jB` (no kernel reduction, no stuck work, the
derived hints' Johnson fallback at `uB`); the counted calls are `certCount`, `m5CKCJ` and `m5CH`.
No charge, generator-count, `BackendBounds`, `RDBounds`, `RDOrbit`, partition, twin or union-cell
hypothesis. -/
theorem RunsWithin.m5StepCJProg_ns_ss {C : ℕ → Option ℕ → ℕ} {s : ℕ}
    {xyP : StrData × StrData} {wP : WinData} {σP : PermData} {NP : ℕ} {gsP : GensData}
    {n₀ nP : ℕ} {LP : LabelData}
    (hIP : HInstValid ssDV
      (((xyP, (wP, (σP, (NP, gsP, ())))), (n₀, (nP, some LP))) : HInstData Ty.unit))
    {hBP : IsInvariant (GensData.denote NP gsP) (baseSet nP NP)}
    (haltP : alternatingGroup (Fin (NP - nP)) ≤ (baseHom (GensData.denote NP gsP) nP hBP).range)
    {sIn : ℕ}
    (hsubP : HSubSolves ssCtx body ssDV sub
      (fun J => SizeChild (max sIn (supTo (fun M => M * M) (wP.1.length / 2)))
        (((xyP, (wP, (σP, (NP, gsP, ())))), (n₀, (nP, some LP))) : HInstData Ty.unit) J ∧
        StepChild wP.1.length (NP - nP) (J.winSize, J.baseOpt)) C s)
    {k : ℕ} (h5 : 5 ≤ k) (hk : k + 2 ≤ NP - nP) (h2k : 2 * k ≤ NP - nP) (hm12 : 12 ≤ NP - nP)
    (hN : NP * NP ≤ sIn) (hgsP : gsP.length ≤ sIn)
    (hCmono : ∀ a b, a ≤ b → C a none ≤ C b none) (hs : s ≤ sIn)
    {Lg : ℕ} (hLgJ : max (NP - nP) (labLen LP * lam (NP - nP)).factorial * (sIn + 1) ≤ Lg)
    {jB : ℕ}
    (hLY : (c2bRj (NP - nP) jB + Case3.c3R k (NP - nP) (Case2b.sojZ (NP - nP))) * (sIn + 1) ≤ Lg)
    {st : ℕ × CJData} (hst : st.1 ≠ 2)
    -- the interfaces
    {T : ℕ → ℕ} (hT : AltQuot.TransitivityBound T) (hjB : ∀ m' ≤ NP - nP, T m' ≤ jB + 1)
    (h4j : 4 * jB ≤ NP - nP) {K : ℕ → ℕ} (hTh : Thresholds K wP.1.length k)
    (h4k : 4 * k ≤ NP - nP) :
    ∃ (fxs fys : GensData) (ex ey : Ty.unit.denote) (ans : AnswerData Ty.unit)
      (ch : List (ℕ × Option ℕ)),
      (∃ (hC : CertSetting (GensData.denote (rbPts nP NP wP).length
          (generateModel (rbPts nP NP wP).length (rbGens nP NP wP gsP))) wP.1.length)
          (φ : strGroup hC →* Perm (Fin ((rbPts nP NP wP).length - wP.1.length))),
        IsPhi hC φ ∧
        M5Full (D := Ty.unit) ssDV hC φ k sIn (StrData.restrictTo (rbPts nP NP wP) xyP.1) fxs ex ∧
        M5Full (D := Ty.unit) ssDV hC φ k sIn (StrData.restrictComp (rbPts nP NP wP) xyP.2 σP)
          fys ey) ∧
      RunsWithin ssCtx body (Main.m5StepCJProg sub
          (((xyP, (wP, (σP, (NP, gsP, ())))), (n₀, (nP, some LP))) : HInstData Ty.unit) LP k st)
        ans
        (rbCost NP wP.1.length (NP - nP) gsP.length
          ((ch.map fun x => C x.1 x.2).sum +
            2 * certCount (rbPts nP NP wP).length wP.1.length k * C (wP.1.length / k) none +
            m5CKCJ ssCtx.O wP.1.length (rbPts nP NP wP).length k
              ((rbPts nP NP wP).length, fxs, ex) ((rbPts nP NP wP).length, fys, ey) *
              C (wP.1.length / k) none +
            m5CH ssCtx.O wP.1.length (rbPts nP NP wP).length sIn wP.1.length
              ((rbPts nP NP wP).length, fxs, ex) ((rbPts nP NP wP).length, fys, ey) *
              C (wP.1.length / 2) none +
            m5WorkNsSS wP.1.length (NP - nP) k wP.1.length s sIn Lg (labLen LP * lam (NP - nP)) jB)
          sIn (NP * NP) (genCost (rbPts nP NP wP).length sIn + 2) (Sims.liftCost NP sIn NP + 7)
          (kerCost NP sIn NP + 5) (genCost NP (NP * NP + sIn) + 2)) ∧
      AnsOK ssDV NP (wP.denote NP) (PermData.denote NP σP) (GensData.denote NP gsP)
        (xyP.1.denote NP) (xyP.2.denote NP) ans ∧
      (∀ sGen, (∀ hs, GensData.AllValid NP hs →
          GensData.denote NP hs ≤ GensData.denote NP gsP →
          (ssCtx.O.run GroupOp.generate (NP, hs)).2.1.length ≤ sGen) →
        ∀ c : CosetData Ty.unit, ans = some c → c.2.gens.length ≤ sGen) ∧
      ChildList wP.1.length (m5CFnsCJ ssCtx.O wP.1.length (rbPts nP NP wP).length k
          ((rbPts nP NP wP).length, fxs, ex) ((rbPts nP NP wP).length, fys, ey)
          (labLen LP * lam (NP - nP)))
        (StepChild wP.1.length (NP - nP)) ch := by
  obtain ⟨fxs, fys, ex, ey, ans, ch, ⟨hC, φ, hφ, hFx, hFy⟩, hrun, hok, hg, hch⟩ :=
    RunsWithin.m5StepCJProg_ns_ss₀ (body := body) (sub := sub) hIP haltP hsubP h5 hk h2k hm12 hN
      hgsP hCmono hs hLgJ hLY hst hT hjB h4j hTh h4k
  refine ⟨fxs, fys, ex, ey, ans, ch, ⟨hC, φ, hφ, hFx, hFy⟩, hrun.mono ?_, hok, hg, hch⟩
  obtain ⟨hNle, hm, hrbv, hI', -⟩ := ss_m5_rb hIP haltP (by omega)
  have hlen : (rbPts nP NP wP).length = wP.1.length + (NP - nP) := rb_length
  have hNs : (rbPts nP NP wP).length * (rbPts nP NP wP).length ≤ sIn :=
    (Nat.mul_le_mul hNle hNle).trans hN
  have hgsv := (generateModel_spec hrbv).1
  have hgsl : (generateModel (rbPts nP NP wP).length (rbGens nP NP wP gsP)).length ≤ sIn :=
    (generateModel_spec hrbv).2.2.trans hNs
  have hwl : (WinData.ofPoints (rbPts nP NP wP).length (List.range wP.1.length)).1.length =
      wP.1.length := by rw [WinData.ofPoints_fst, List.length_range]
  rw [hwl]
  have hFxb := hFx.base_inv
  have hFyb := hFy.base_inv
  have hjB' : ∀ m' ≤ (rbPts nP NP wP).length - wP.1.length, T m' ≤ jB + 1 := by
    rw [hm]
    exact hjB
  have hj : m5Sel ssCtx.O wP.1.length (rbPts nP NP wP).length ((rbPts nP NP wP).length, fxs, ex)
      ((rbPts nP NP wP).length, fys, ey) = 4 →
      Case2b.degD ssCtx.O (rbPts nP NP wP).length wP.1.length ((rbPts nP NP wP).length, fxs, ex)
        (m5Cs ssCtx.O wP.1.length (rbPts nP NP wP).length
          ((rbPts nP NP wP).length, fxs, ex)).2 - 1 ≤ jB := fun h4 => by
    obtain ⟨h2, hA⟩ := m5Sel_four h4
    exact ss_m5_depth_le hT hNs hjB' hFx h2 hA
  have hΦx := ss_m5Cs_le (e := ex) hFx.1.1 hFxb
  have hΦy := ss_m5Cs_le (e := ey) hFy.1.1 hFyb
  have hmx := ss_fixPts_le (e := ex) hFx.1.1 hFxb
  have hmy := ss_fixPts_le (e := ey) hFy.1.1 hFyb
  revert hgsl hj hΦx hΦy hmx hmy
  generalize (rbPts nP NP wP).length = N at hlen hm ⊢
  subst hlen
  intro hgsl hj hΦx hΦy hmx hmy
  rw [Nat.add_sub_cancel_left] at hΦx hΦy hmx hmy ⊢
  have h0 := m5CoreWorkNsCJ_le (n := wP.1.length) (m := NP - nP) (k := k) (s := s) (sIn := sIn)
    (Lg := Lg) (uB := labLen LP * lam (NP - nP)) (jB := jB) (p := wP.1.length)
    (G := (wP.1.length + (NP - nP), generateModel (wP.1.length + (NP - nP)) (rbGens nP NP wP gsP),
      ())) hgsl hΦx hΦy hmx hmy hj
  have h1 := le_m5WorkNsSS wP.1.length (NP - nP) k wP.1.length s sIn Lg
    (labLen LP * lam (NP - nP)) jB
  unfold rbCost
  omega

end Step

/-! ### The factor and the parameters -/

section Params

/-- **The bound on M5's children's factor without stuck orbits** (stage 14j-6b-1, item 6), for
base size `m`, certificate size `k`, union-cell bound `uB` and Case 2b's depth bound `jB`: Case 1's
`m`, Case 3's two routes `c3R · max(m, uB!)` and `c3R · m`, and Case 2b's
`c2bRj m jB · max(m, uB!)`. No factorial of `m`. -/
def m5FBns (m k uB jB : ℕ) : ℕ :=
  m + Case3.c3R k m (Case2b.sojZ m) * max m uB.factorial +
    Case3.c3R k m (Case2b.sojZ m) * m + c2bRj m jB * max m uB.factorial

/-- **M5's children's factor without stuck orbits** with Schreier–Sims is at most `m5FBns`, when
Case 2b's depth is at most `jB` in Case 2b (`ss_m5_depth_le` under `TransitivityBound`). -/
theorem ss_m5CFnsCJ_le {wl Nr k uB jB : ℕ} {fxs fys : GensData}
    (hfy : GensData.AllValid Nr fys) (hby : IsInvariant (GensData.denote Nr fys) (baseSet wl Nr))
    (hj : m5Sel ssCtx.O wl Nr (Nr, fxs, ()) (Nr, fys, ()) = 4 →
      Case2b.degD ssCtx.O Nr wl (Nr, fxs, ()) (m5Cs ssCtx.O wl Nr (Nr, fxs, ())).2 - 1 ≤ jB) :
    m5CFnsCJ ssCtx.O wl Nr k (Nr, fxs, ()) (Nr, fys, ()) uB ≤ m5FBns (Nr - wl) k uB jB := by
  have hfix := ss_fixPts_le (e := ()) hfy hby
  have hΦy := ss_m5Cs_le (e := ()) hfy hby
  have h3 := c3R_mono (k := k) (Z := Case2b.sojZ (Nr - wl)) hfix
  have hmu : Nr - wl ≤ max (Nr - wl) uB.factorial := le_max_left _ _
  unfold m5CFnsCJ m5FBns
  split
  · omega
  · have := Nat.mul_le_mul_right (max (Nr - wl) uB.factorial) h3
    have := Nat.mul_le_mul_right (Nr - wl) h3
    omega
  · next h =>
    have h2b := c2bR_le_j (N := Nr) (n := wl) hΦy (hj h)
    split
    · have := Nat.mul_le_mul_right (max (Nr - wl) uB.factorial) h2b
      omega
    · have := Nat.mul_le_mul h2b hmu
      omega
  · omega

/-- The bound on `generate`'s inputs for M5 without stuck orbits, on base size `m` with
certificates of size `k`, union-cell bound `uB` and Case 2b's depth bound `jB`. -/
def ssLgM5Ns (m k uB jB sIn : ℕ) : ℕ :=
  (max m uB.factorial + c2bRj m jB + Case3.c3R k m (Case2b.sojZ m)) * (sIn + 1)

/-- **M5's parameters without stuck orbits**: `sIn = ssSIn NP s |gsP|` and
`Lg = ssLgM5Ns m k uB jB sIn` meet `hN`, `hgsP`, `hs`, `hLgJ` and `hLY` of
`RunsWithin.m5StepCJProg_ns_ss`. -/
theorem m5ns_params (NP nP k s g uB jB : ℕ) :
    NP * NP ≤ ssSIn NP s g ∧ g ≤ ssSIn NP s g ∧ s ≤ ssSIn NP s g ∧
      max (NP - nP) uB.factorial * (ssSIn NP s g + 1) ≤
        ssLgM5Ns (NP - nP) k uB jB (ssSIn NP s g) ∧
      (c2bRj (NP - nP) jB + Case3.c3R k (NP - nP) (Case2b.sojZ (NP - nP))) *
        (ssSIn NP s g + 1) ≤ ssLgM5Ns (NP - nP) k uB jB (ssSIn NP s g) := by
  obtain ⟨h1, h2, h3⟩ := ssSIn_spec NP s g
  exact ⟨h1, h3, h2, Nat.mul_le_mul_right _ (by omega), Nat.mul_le_mul_right _ (by omega)⟩

end Params

end GraphIso.Main
