module

public import GraphIso.Main.M5Cases

/-!
# M5: the dispatcher on the restricted instance

Stage 14j-4, item 5 (`PLAN-14.md` §14.4). On a hinted instance `I = (x, y, W, 1 • G)` after the
restriction of item 1 (the string positions `[0, n)` all in the window, the representative `1`),
with `G` faithful on the strings (`CertSetting`), a giant base action on `m = N − n` points,
`G` transitive on `W` and valid labels:

* **The fixed points** of `ψ(F)` on data (`fixPtsD`, `fixPtsProg`, `RunsWithin.fixPtsProg`):
  the points of the singleton orbits; `fixPtsD_spec` (the `Vx`, `Vy` of Case 3), and
  `m5_fix_len` (they and the moved points partition the base).
* **Conjugation** (`m5_Fmap_iso`, `m5_range_conj`, `m5_card_orbit_conj`): an isomorphism `g`
  conjugates `F(x)` to `F(y)`, so their base actions are conjugate by `ψ(g)` and their orbits
  correspond. Hence Case 2 for `x` is Case 2 for `y` (`m5_large_iso`), and the separation of
  Case 2a from Case 2b agrees (`m5_isA_iff`, `m5_tupTrans_iso`): when they differ, there is no
  isomorphism.
* **Case 2a's labels** (`m5_labels`): from the hint, equivariant labels of constant size `t`,
  `1 ≤ t`, `2 t ≤ m`.
* **The dispatch** (`m5Dispatch`, `RunsWithin.m5Dispatch`): from `Fx = F(x)`, `Fy = F(y)` and
  their case decisions, Case 1 (`m5Case1Prog`, no-stuck form), Case 2a (`m5Case2aProg`),
  Case 2b (`m5Case2bProg`, factor `m!`), the answer `none` when `y`'s Case 2 decision differs,
  or Case 3 (`m5Case3Prog`, with the fixed points; factor `m!`). The case run is `m5Sel`; its
  sub-calls are counted by `m5CK` (windows of at most `n / k` points) and `m5CH` (at most
  `|W| / 2`), its children's factor is `m5CF`, its work `m5W`.
* **M5** (`m5CoreProg`, `RunsWithin.m5CoreProg`): the certificates of `x` and `y`
  (`m5CertProg`, which compute `F(x)`, `F(y)`: `M5Full`), their case decisions
  (`m5CaseProg`), and the dispatch. The answer is correct for `I` (`InstData.OK`); the cost is
  the children's (`ChildList`, `StepChild |W| m`), `2 · certCount + m5CK` sub-calls without a
  hint on windows of at most `n / k` points (by `fullCost_le_count`), `m5CH` on windows of at
  most `|W| / 2` points, and the work `m5CoreWork`.
* **Well-formedness** (`wf_fixPtsProg`, `wf_m5Dispatch`, `wf_m5CoreProg`).

The sub-solver is asked for children with at most `max sIn (supTo sm (|W| / 2))` generators
(`SizeChild`, stage 14j-5a): `sIn` for the certificates' sub-calls and Cases 1, 2b and 3, and the
backend's output bound `sm M` at degrees `M ≤ |W| / 2` (`Bm`'s `genOut`) for Case 2a's restricted
sub-calls, which discharges `RunsWithin.m5Case2aProg`'s hypothesis `hgR`.

The backends' charges (`M5Bounds`; those depending on `F(x)`, `F(y)` for every group `M5Full`
allows), reduce-and-derive's `RDBounds` and per-orbit `RDOrbit` (`hD`), and `m ≥ 12`,
`k ≥ 5`, `2 k ≤ m` are hypotheses. The work bounds are functions of the oracle's values
(`m5W`); bounding them is left to stage 14j-6.
-/

@[expose] public section

namespace GraphIso.Main

open Equiv MulAction Pointwise Cost GraphIso GraphIso.Programs GraphIso.Toolkit
  GraphIso.Recursion GraphIso.SplitJohnson GraphIso.Solver GraphIso.Align GraphIso.Certificates
  GraphIso.CertProg

/-! ### Fixed points on data -/

section FixPts

/-- **The fixed points of `ψ(F)`** from its orbits as base indices: the points of the singleton
orbits. -/
def fixPtsD (bos : List (List ℕ)) : List ℕ := (bos.filter fun o => o.length == 1).flatten

theorem m5_foldl_prepend : ∀ (l : List (List ℕ)) (acc : List ℕ),
    l.foldl (fun acc o => o ++ acc) acc = l.reverse.flatten ++ acc
  | [], acc => by simp
  | o :: t, acc => by
    rw [List.foldl_cons, m5_foldl_prepend t (o ++ acc)]
    simp

theorem mem_fixPtsD {bos : List (List ℕ)} {v : ℕ} :
    v ∈ fixPtsD bos ↔ ∃ o ∈ bos, o.length = 1 ∧ v ∈ o := by
  simp only [fixPtsD, List.mem_flatten, List.mem_filter, beq_iff_eq]
  constructor
  · rintro ⟨o, ⟨ho, hl⟩, hv⟩
    exact ⟨o, ho, hl, hv⟩
  · rintro ⟨o, ho, hl, hv⟩
    exact ⟨o, ⟨ho, hl⟩, hv⟩

/-- A point fixed by every element has an orbit of one point, and conversely. -/
theorem m5_card_orbit_eq_one {Γ : Type*} {P : Subgroup (Perm Γ)} {v : Γ} :
    Nat.card (orbit P v) = 1 ↔ ∀ f ∈ P, f v = v := by
  constructor
  · intro h f hf
    obtain ⟨hsub, -⟩ := Nat.card_eq_one_iff_unique.1 h
    have h1 : (⟨f v, ⟨⟨f, hf⟩, rfl⟩⟩ : orbit P v) = ⟨v, mem_orbit_self v⟩ := Subsingleton.elim _ _
    exact congrArg Subtype.val h1
  · intro h
    refine Nat.card_eq_one_iff_unique.2 ⟨⟨fun a b => ?_⟩, ⟨⟨v, mem_orbit_self v⟩⟩⟩
    obtain ⟨a, ⟨fa, rfl⟩⟩ := a
    obtain ⟨b, ⟨fb, rfl⟩⟩ := b
    apply Subtype.ext
    change fa.1 v = fb.1 v
    rw [h fa.1 fa.2, h fb.1 fb.2]

/-- **The fixed points on data** are the fixed points of `ψ(F)`. -/
theorem fixPtsD_spec {N n : ℕ} {F : Subgroup (Perm (Fin N))} (hF : IsInvariant F (baseSet n N))
    {os : List (List ℕ)} (hos : IsOrbitPartition F (baseWin n N) os) :
    (fixPtsD (Giant.agShiftD n os)).Nodup ∧ (∀ v ∈ fixPtsD (Giant.agShiftD n os), v < N - n) ∧
      ∀ v : Fin (N - n), v.val ∈ fixPtsD (Giant.agShiftD n os) ↔
        ∀ f ∈ (baseHom F n hF).range, f v = v := by
  have hflat := (Giant.ag_bos_flatten hos).nodup_iff.2 List.nodup_range
  refine ⟨(List.filter_sublist.flatten).nodup hflat, fun v hv => ?_, fun v => ?_⟩
  · obtain ⟨o, ho, -, hvo⟩ := mem_fixPtsD.1 hv
    exact (Giant.ag_bos_nodup hos ho).2 v hvo
  · rw [mem_fixPtsD, ← m5_card_orbit_eq_one]
    constructor
    · rintro ⟨o, ho, hl, hvo⟩
      rw [Giant.ag_card_orbit hF hos ho hvo, hl]
    · intro h
      obtain ⟨o, ho, hvo⟩ := Giant.ag_bos_cover hos v
      exact ⟨o, ho, by rw [← Giant.ag_card_orbit hF hos ho hvo, h], hvo⟩

end FixPts

/-! ### Conjugation by an isomorphism -/

section Conj

variable {N n : ℕ}

theorem m5_basePos_injective : Function.Injective (basePos (n := n) (N := N)) := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [basePos] at this
  omega

/-- The base action depends only on the permutation, not on the subgroup it is taken in. -/
theorem m5_baseHom_eq {G H : Subgroup (Perm (Fin N))} {hG : IsInvariant G (baseSet n N)}
    {hH : IsInvariant H (baseSet n N)} (g : G) (h : H) (he : g.1 = h.1) :
    baseHom G n hG g = baseHom H n hH h := by
  ext j
  have := m5_basePos_injective (n := n) (N := N)
    ((baseHom_apply (hG := hG) g j).trans (he ▸ (baseHom_apply (hG := hH) h j).symm))
  rw [this]

/-- **An isomorphism conjugates the full groups**: `F(y) = g F(x) g⁻¹` (the window contains the
string positions, `F` is local and canonical). -/
theorem m5_Fmap_iso {G : Subgroup (Perm (Fin N))} (hC : CertSetting G n)
    (φ : strGroup hC →* Perm (Fin (N - n))) (k : ℕ) {W : Set (Fin N)}
    (hwS : ∀ u : Fin N, u.val < n → u ∈ W) (hWG : IsInvariant G W) {x y : Fin N → ℕ}
    {g : Perm (Fin N)} (hg : g ∈ iso W 1 G x y) :
    m5Fmap hC φ k y = (m5Fmap hC φ k x).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨hgG, hm⟩ := mem_iso_one.1 hg
  rw [← m5Fmap_relabel hC φ k g hgG x]
  refine m5Fmap_loc hC φ k hwS y (relabel g x) fun u hu => ?_
  have hu' : g⁻¹ u ∈ W := hWG _ (inv_mem hgG) u hu
  rw [relabel_apply, hm _ hu', perm_apply_inv_self]

/-- **Conjugate base actions**: for `F' = g F g⁻¹` inside `G`, `p` acts in `ψ(F')` exactly
when `σ⁻¹ p σ` acts in `ψ(F)`, with `σ = ψ(g)`. -/
theorem m5_range_conj {G F F' : Subgroup (Perm (Fin N))} (hG : IsInvariant G (baseSet n N))
    (hF : IsInvariant F (baseSet n N)) (hF' : IsInvariant F' (baseSet n N)) (hFG : F ≤ G)
    {g : Perm (Fin N)} (hgG : g ∈ G) (hF'e : F' = F.map (MulAut.conj g).toMonoidHom)
    (p : Perm (Fin (N - n))) :
    p ∈ (baseHom F' n hF').range ↔
      (baseHom G n hG ⟨g, hgG⟩)⁻¹ * p * baseHom G n hG ⟨g, hgG⟩ ∈ (baseHom F n hF).range := by
  have hF'G : F' ≤ G := by
    rw [hF'e]
    rintro _ ⟨f, hf, rfl⟩
    exact mul_mem (mul_mem hgG (hFG hf)) (inv_mem hgG)
  constructor
  · rintro ⟨⟨f', hf'⟩, rfl⟩
    have hf'' := hf'
    rw [hF'e] at hf''
    obtain ⟨f, hf, rfl⟩ := hf''
    refine ⟨⟨f, hf⟩, ?_⟩
    rw [m5_baseHom_eq (hH := hG) ⟨f, hf⟩ ⟨f, hFG hf⟩ rfl,
      m5_baseHom_eq (hH := hG) ⟨_, hf'⟩ ⟨_, hF'G hf'⟩ rfl, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simp [mul_assoc]
  · rintro ⟨⟨f, hf⟩, he⟩
    have hf' : g * f * g⁻¹ ∈ F' := by
      rw [hF'e]
      exact ⟨f, hf, rfl⟩
    refine ⟨⟨_, hf'⟩, ?_⟩
    rw [m5_baseHom_eq (hH := hG) ⟨_, hf'⟩ ⟨_, hF'G hf'⟩ rfl]
    rw [m5_baseHom_eq (hH := hG) ⟨f, hf⟩ ⟨f, hFG hf⟩ rfl] at he
    have h2 : baseHom G n hG ⟨g * f * g⁻¹, hF'G hf'⟩ = baseHom G n hG ⟨g, hgG⟩ *
        baseHom G n hG ⟨f, hFG hf⟩ * (baseHom G n hG ⟨g, hgG⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [h2, he]
    group

/-- **Orbits correspond under conjugation**: the orbit of `σ γ` under `ψ(F')` is the image of
the orbit of `γ` under `ψ(F)`. -/
theorem m5_card_orbit_conj {Γ : Type*} {P P' : Subgroup (Perm Γ)} (σ : Perm Γ)
    (hP : ∀ p, p ∈ P' ↔ σ⁻¹ * p * σ ∈ P) (γ : Γ) :
    Nat.card (orbit P' (σ γ)) = Nat.card (orbit P γ) := by
  have hset : (orbit P' (σ γ) : Set Γ) = σ '' orbit P γ := by
    ext δ
    simp only [Set.mem_image, mem_orbit_iff]
    constructor
    · rintro ⟨⟨p, hp⟩, rfl⟩
      refine ⟨(σ⁻¹ * p * σ) γ, ⟨⟨σ⁻¹ * p * σ, (hP p).1 hp⟩, rfl⟩, ?_⟩
      simp [Perm.mul_apply]
    · rintro ⟨δ', ⟨⟨q, hq⟩, rfl⟩, rfl⟩
      refine ⟨⟨σ * q * σ⁻¹, (hP _).2 (by simpa [mul_assoc] using hq)⟩, ?_⟩
      simp [Perm.mul_apply]
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, hset, Set.ncard_image_of_injective _ σ.injective]

end Conj

/-! ### The case decision under an isomorphism -/

section CaseIso

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}

/-- **Case 2a** is `ψ(F)` being `(|Φ| − 2)`-transitive on the large orbit `Φ` (the degree
program's characterization, `degD_spec`, `m5_tupTrans_iff`). -/
theorem m5_isA_iff (hO : MeetsContractOn DV m5CaseOps X.O)
    (hPre : ∀ op x, m5CaseOps op → GroupPre DV op x → X.Pre op x) {N n s : ℕ}
    {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N s G₀) {sm : ℕ → ℕ}
    (Bm : ∀ M, BackendBounds X DV M (sm M) ⊤) {fs : GensData} {fd : D.denote}
    (hFv : GroupValid DV N fs fd) (hs : fs.length ≤ s) (hG₀ : GensData.denote N fs ≤ G₀)
    (hF : IsInvariant (GensData.denote N fs) (baseSet n N))
    (h2 : (m5Cs X.O n N (N, fs, fd)).1 = 2) :
    Case2b.TupTrans (baseHom (GensData.denote N fs) n hF).range
        (SoJProg.setOf (N - n) (m5Cs X.O n N (N, fs, fd)).2)
        ((m5Cs X.O n N (N, fs, fd)).2.length - 2) ↔ m5IsA X.O n N (N, fs, fd) = true := by
  obtain ⟨hos, -, -⟩ := m5Case_spec hO hPre B Bm hFv hs hG₀ hF
  set Φ := (m5Cs X.O n N (N, fs, fd)).2 with hΦdef
  have hc := (Giant.caseD_spec hF hos).2.1 h2
  have hnd : Φ.Nodup := hc.1
  have hlt : ∀ i ∈ Φ, i < N - n := hc.2.1
  obtain ⟨γ, -, hγ₀⟩ := hc.2.2.2
  have hγ : ∀ δ : Fin (N - n),
      δ.val ∈ Φ ↔ δ ∈ MulAction.orbit (baseHom (GensData.denote N fs) n hF).range γ := hγ₀
  have hΦi := Case2b.cp2_inv_of_orbit (Φ := Φ) hF hlt ⟨γ, hγ⟩
  obtain ⟨hle, htr, hnot⟩ := Case2b.degD_spec (X := X)
    (fun op x h hp => hO op x (Or.inr h) hp) (fun op x h hp => hPre op x (Or.inr h) hp)
    B hFv hs hG₀ hF hnd hlt hΦi (Bm _)
  have hpres : ∀ g ∈ (baseHom (GensData.denote N fs) n hF).range,
      ∀ x ∈ SoJProg.setOf (N - n) Φ, g x ∈ SoJProg.setOf (N - n) Φ := by
    intro g hg x hx
    rw [SoJProg.mem_setOf, hγ] at hx ⊢
    exact Case2b.cp2_orbit_pres hg hx
  have hcard : (SoJProg.setOf (N - n) Φ).card = Φ.length := SoJProg.card_setOf hnd hlt
  have hiff := m5_tupTrans_iff hpres (d := Case2b.degD X.O N n (N, fs, fd) Φ)
    (by rw [hcard]; exact hle) htr (fun h => hnot (by rw [← hcard]; exact h))
  rw [hcard] at hiff
  rw [hiff]
  have hb : ((m5Cs X.O n N (N, fs, fd)).1 == 2) = true := by simp [h2]
  simp only [m5IsA, hb, Bool.cond_true, ← hΦdef, Bool.not_eq_true', decide_eq_false_iff_not,
    not_lt]

/-- **Case 2 is invariant**: if `x ≅ y` and `ψ(F(x))` has an orbit of more than `m/2` points,
so has `ψ(F(y))`. -/
theorem m5_large_iso {N n : ℕ} {G : Subgroup (Perm (Fin N))} (hC : CertSetting G n)
    (φ : strGroup hC →* Perm (Fin (N - n))) (k : ℕ) {W : Set (Fin N)}
    (hwS : ∀ u : Fin N, u.val < n → u ∈ W) (hWG : IsInvariant G W) {x y : Fin N → ℕ}
    {g : Perm (Fin N)} (hg : g ∈ iso W 1 G x y) {Fx Fy : Subgroup (Perm (Fin N))}
    (hFxe : Fx = m5Fmap hC φ k x) (hFye : Fy = m5Fmap hC φ k y)
    (hFx : IsInvariant Fx (baseSet n N)) (hFy : IsInvariant Fy (baseSet n N))
    (h : ∃ γ : Fin (N - n), N - n < 2 * Nat.card (orbit (baseHom _ n hFx).range γ)) :
    ∃ γ : Fin (N - n), N - n < 2 * Nat.card (orbit (baseHom _ n hFy).range γ) := by
  subst hFxe hFye
  obtain ⟨γ, hγ⟩ := h
  have hgG : g ∈ G := (mem_iso_one.1 hg).1
  have hP := m5_range_conj hC.base hFx hFy (m5Fmap_le hC φ k x) hgG
    (m5_Fmap_iso hC φ k hwS hWG hg)
  refine ⟨baseHom G n hC.base ⟨g, hgG⟩ γ, ?_⟩
  rwa [m5_card_orbit_conj _ hP]

/-- **The separation of Case 2a from Case 2b is invariant**: if `x ≅ y`, with the large orbits
`Φx`, `Φy` of `ψ(F(x))`, `ψ(F(y))`, the conditions of `(|Φ| − 2)`-transitivity agree. -/
theorem m5_tupTrans_iso {N n : ℕ} {G : Subgroup (Perm (Fin N))} (hC : CertSetting G n)
    (φ : strGroup hC →* Perm (Fin (N - n))) (k : ℕ) {W : Set (Fin N)}
    (hwS : ∀ u : Fin N, u.val < n → u ∈ W) (hWG : IsInvariant G W) {x y : Fin N → ℕ}
    {g : Perm (Fin N)} (hg : g ∈ iso W 1 G x y) {Fx Fy : Subgroup (Perm (Fin N))}
    (hFxe : Fx = m5Fmap hC φ k x) (hFye : Fy = m5Fmap hC φ k y)
    (hFx : IsInvariant Fx (baseSet n N)) (hFy : IsInvariant Fy (baseSet n N))
    {Φx Φy : List ℕ} (hΦxn : Φx.Nodup) (hΦxl : ∀ i ∈ Φx, i < N - n)
    (hΦx2 : N - n < 2 * Φx.length)
    (hΦxo : ∃ γ : Fin (N - n), γ.val ∈ Φx ∧
      ∀ δ : Fin (N - n), δ.val ∈ Φx ↔ δ ∈ MulAction.orbit (baseHom _ n hFx).range γ)
    (hΦyn : Φy.Nodup) (hΦyl : ∀ i ∈ Φy, i < N - n) (hΦy2 : N - n < 2 * Φy.length)
    (hΦyo : ∃ γ : Fin (N - n), γ.val ∈ Φy ∧
      ∀ δ : Fin (N - n), δ.val ∈ Φy ↔ δ ∈ MulAction.orbit (baseHom _ n hFy).range γ) :
    (Case2b.TupTrans (baseHom _ n hFy).range (SoJProg.setOf (N - n) Φy) (Φy.length - 2) ↔
      Case2b.TupTrans (baseHom _ n hFx).range (SoJProg.setOf (N - n) Φx) (Φx.length - 2)) := by
  subst hFxe hFye
  have hgG : g ∈ G := (mem_iso_one.1 hg).1
  have hP := m5_range_conj hC.base hFx hFy (m5Fmap_le hC φ k x) hgG
    (m5_Fmap_iso hC φ k hwS hWG hg)
  have hσ := Giant.largeOrbit_canonical hC.base hWG (m5Fmap_loc hC φ k hwS)
    (m5Fmap_relabel hC φ k) rfl rfl hFx hFy hg hΦxn hΦxl hΦx2 hΦxo hΦyn hΦyl hΦy2 hΦyo
  set σ := baseHom G n hC.base ⟨g, hgG⟩ with hσdef
  have hΦ : ∀ v, v ∈ SoJProg.setOf (N - n) Φy ↔ σ⁻¹ v ∈ SoJProg.setOf (N - n) Φx := by
    intro v
    rw [← hσ, Finset.mem_smul_finset]
    constructor
    · rintro ⟨u, hu, rfl⟩
      simpa using hu
    · intro h
      exact ⟨σ⁻¹ v, h, by simp⟩
  have hlen : Φy.length = Φx.length := by
    rw [← SoJProg.card_setOf hΦyn hΦyl, ← SoJProg.card_setOf hΦxn hΦxl, ← hσ,
      Finset.card_smul_finset]
  rw [hlen]
  exact Case2b.cp2_tupTrans_conj σ hP hΦ _

end CaseIso

/-! ### Case 3's fixed points, and Case 2a's labels -/

section Facts

/-- **The fixed points and the moved points** partition the base. -/
theorem m5_fix_len {m : ℕ} {P : Subgroup (Perm (Fin m))} {V : List ℕ} (hVn : V.Nodup)
    (hVl : ∀ v ∈ V, v < m) (hVF : ∀ v : Fin m, v.val ∈ V ↔ ∀ f ∈ P, f v = v) :
    V.length + Nat.card {γ : Fin m // 1 < Nat.card (orbit P γ)} = m := by
  classical
  have hA : SoJProg.setOf m V =
      Finset.univ.filter (fun γ : Fin m => Nat.card (orbit P γ) = 1) := by
    ext γ
    rw [SoJProg.mem_setOf, hVF, Finset.mem_filter, m5_card_orbit_eq_one]
    simp
  rw [← SoJProg.card_setOf hVn hVl, hA, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun γ : Fin m => Nat.card (orbit P γ) = 1)
  rw [Finset.card_univ, Fintype.card_fin] at h
  have hf : (Finset.univ.filter fun γ : Fin m => 1 < Nat.card (orbit P γ)) =
      Finset.univ.filter fun γ : Fin m => ¬ Nat.card (orbit P γ) = 1 := by
    ext γ
    have := Giant.c1_card_orbit_pos P γ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  rw [hf]
  exact h

/-- **Case 2a's labels**: from valid hint data on a window on which `G` is transitive, labels
equivariant for the base action, all of the same size `t` with `1 ≤ t` and `2t ≤ m` (the hint's
labels, or their complements). -/
theorem m5_labels {N n : ℕ} {gs : GensData} {w : WinData} {L : LabelData}
    (hL : HintValid n N gs w L) (hgs : GensData.AllValid N gs) (hw : w.Valid N)
    (hinv : IsInvariant (GensData.denote N gs) (w.denote N))
    (htr : IsTransOn (GensData.denote N gs) (w.denote N))
    (hG : IsInvariant (GensData.denote N gs) (baseSet n N)) :
    ∃ (lab : Fin N → Finset (Fin (N - n))) (t : ℕ),
      Recursion.Equivar (baseHom _ n hG) (winFinset N w) lab ∧
      (∀ u ∈ winFinset N w, (lab u).card = t) ∧ 1 ≤ t ∧ 2 * t ≤ N - n := by
  classical
  have hh := hL.isHint hgs hw hinv
  have he : Recursion.Equivar (baseHom _ n hG) (winFinset N w) (labOf n N L) := hh.equivar
  obtain ⟨u₀, hu₀, v₀, hv₀, hne⟩ := hh.nonconst
  set t₀ := (labOf n N L u₀).card with ht₀
  have hcard : ∀ u ∈ winFinset N w, (labOf n N L u).card = t₀ := by
    intro u hu
    obtain ⟨g, hg, hgu⟩ := htr u₀ (mem_winFinset.1 hu₀) u (mem_winFinset.1 hu)
    have := he ⟨g, hg⟩ u₀ hu₀
    change labOf n N L (g u₀) = _ at this
    rw [hgu] at this
    rw [this, Finset.card_smul_finset]
  have hle : t₀ ≤ N - n := by
    have := Finset.card_le_univ (labOf n N L u₀)
    rwa [Fintype.card_fin] at this
  have h1 : 1 ≤ t₀ := by
    by_contra h0
    have hz : ∀ u ∈ winFinset N w, labOf n N L u = ∅ := fun u hu =>
      Finset.card_eq_zero.1 ((hcard u hu).trans (by omega))
    exact hne ((hz u₀ hu₀).trans (hz v₀ hv₀).symm)
  have hlt : t₀ < N - n := by
    by_contra hm
    have hu : ∀ u ∈ winFinset N w, labOf n N L u = Finset.univ := fun u hu =>
      Finset.eq_univ_of_card _ (by rw [hcard u hu, Fintype.card_fin]; omega)
    exact hne ((hu u₀ hu₀).trans (hu v₀ hv₀).symm)
  by_cases h2 : 2 * t₀ ≤ N - n
  · exact ⟨labOf n N L, t₀, he, hcard, h1, h2⟩
  · refine ⟨fun u => Finset.univ \ labOf n N L u, N - n - t₀, fun g u hu => ?_, fun u hu => ?_,
      by omega, by omega⟩
    · change Finset.univ \ labOf n N L (g • u) = _
      rw [he g u hu, Finset.smul_finset_sdiff, Finset.smul_finset_univ]
    · rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
        Fintype.card_fin, hcard u hu]

end Facts

/-! ### Programs -/

section Programs

variable {D : Ty} {rec : Ty × Ty} {var : Ty → Type}

/-- The type of `m5CaseProg`'s value: the case and the large orbit, the orbits, Case 2a. -/
abbrev m5CaseTy : Ty := .prod (.prod (.prod .nat (.list .nat)) (.list (.list .nat))) .bool

/-- **The fixed points** of `ψ(F)` from its orbits as base indices (`fixPtsD`). -/
def fixPtsProg {S : Signature} (bos : var (.list (.list .nat))) : Prog S rec var (.list .nat) :=
  .bind (Toolkit.filterList bos fun o => .bind (.op1 .length o) fun l =>
      .bind (.op0 (.natLit 1)) fun one => .op2 .natEq l one) fun fl =>
  .bind (.op1 .reverse fl) fun rl => .bind (.op0 .nil) fun e =>
  .foldList rl e fun acc o => .op2 .append o acc

/-- **The dispatch of M5** on the restricted instance, from the full groups `Fx`, `Fy` and their
case decisions `cx`, `cy`: Case 1, Case 2a or 2b (when `y`'s case and separation agree with
`x`'s; otherwise there is no isomorphism), or Case 3 with the fixed points of `ψ(Fx)`,
`ψ(Fy)`. -/
def m5Dispatch (sub : var (hinstTy D) → Prog (groupSig D) rec var (Ty.answer D))
    (I : var (hinstTy D)) (n₀ n : var .nat) (L : var (.array (.list .nat))) (st : var stTy)
    (k : var .nat) (xy : var Ty.strs) (w : var Ty.win) (G Fx Fy : var (Ty.group D))
    (cx cy : var m5CaseTy) : Prog (groupSig D) rec var (Ty.answer D) :=
  .bind (.op1 .fst cx) fun rx => .bind (.op1 .snd cx) fun ax =>
  .bind (.op1 .fst rx) fun csx => .bind (.op1 .snd rx) fun bosx =>
  .bind (.op1 .fst csx) fun tag => .bind (.op1 .snd csx) fun Φx =>
  .bind (.op1 .fst cy) fun ry => .bind (.op1 .snd cy) fun ay =>
  .bind (.op1 .fst ry) fun csy => .bind (.op1 .snd ry) fun bosy =>
  .bind (.op1 .fst csy) fun tagy => .bind (.op1 .snd csy) fun Φy =>
  .bind (.op0 (.natLit 1)) fun one => .bind (.op2 .natEq tag one) fun is1 =>
  .ite is1 (m5Case1Prog sub n₀ n L st xy w G Fx Fy)
    (.bind (.op0 (.natLit 2)) fun two => .bind (.op2 .natEq tag two) fun is2 =>
      .ite is2
        (.bind (.op2 .natEq tagy two) fun y2 =>
          .bind (.op2 .and ax ay) fun both => .bind (.op1 .not ax) fun nx =>
          .bind (.op1 .not ay) fun ny => .bind (.op2 .and nx ny) fun neither =>
          .bind (.op2 .or both neither) fun same => .bind (.op2 .and y2 same) fun ok =>
          .ite ok
            (.ite ax
              (.bind (.op1 .snd Fx) fun fd => .bind (.op1 .fst fd) fun fgs =>
                m5Case2aProg sub n₀ n xy w G Φx Φy fgs)
              (m5Case2bProg sub n₀ n L st xy w G Fx Fy Φx Φy))
            (.op0 .none))
        (.bind (fixPtsProg bosx) fun Vx => .bind (fixPtsProg bosy) fun Vy =>
          m5Case3Prog sub I n₀ n L st k xy w G Vx Vy))

/-- **M5 on the restricted instance**: the certificates of `x` and `y` (the full groups), their
case decisions, and the dispatch. Without labels (never the case for M5) the answer is
`none`. -/
def m5CoreProg (sub : var (hinstTy D) → Prog (groupSig D) rec var (Ty.answer D))
    (I : var (hinstTy D)) (k : var .nat) (st : var stTy) :
    Prog (groupSig D) rec var (Ty.answer D) :=
  .bind (.op1 .fst I) fun J => .bind (.op1 .snd I) fun r₁ => .bind (.op1 .fst r₁) fun n₀ =>
  .bind (.op1 .snd r₁) fun r₂ => .bind (.op1 .fst r₂) fun n => .bind (.op1 .snd r₂) fun lab =>
  .caseOption lab (.op0 .none) fun L =>
  .bind (.op1 .fst J) fun xy => .bind (.op1 .snd J) fun wc => .bind (.op1 .fst wc) fun w =>
  .bind (.op1 .snd wc) fun c => .bind (.op1 .snd c) fun G => .bind (.op1 .fst G) fun N =>
  .bind (.op1 .fst xy) fun x => .bind (.op1 .snd xy) fun y =>
  .bind (m5CertProg sub n₀ n N k x G) fun Fx => .bind (m5CertProg sub n₀ n N k y G) fun Fy =>
  .bind (m5CaseProg n N Fx) fun cx => .bind (m5CaseProg n N Fy) fun cy =>
  m5Dispatch sub I n₀ n L st k xy w G Fx Fy cx cy

end Programs

/-- The cost of `fixPtsProg` on at most `m` orbits of at most `m` points. -/
def fixPtsCost (m : ℕ) : ℕ := m * (m + 4 + 4) + 3 + (m + 1) + 1 + m * 3

section FixPtsRun

variable {S : Signature} {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

theorem RunsWithin.fixPtsProg {m : ℕ} {bos : List (List ℕ)} (hbl : bos.length ≤ m)
    (hol : ∀ o ∈ bos, o.length ≤ m) :
    RunsWithin X body (Main.fixPtsProg bos) (fixPtsD bos) (fixPtsCost m) := by
  have hfl : RunsWithin X body (Toolkit.filterList (a' := .list .nat) (var := Ty.denote) bos
      fun o => .bind (.op1 .length o) fun l =>
        .bind (.op0 (.natLit 1)) fun one => .op2 .natEq l one)
      (bos.filter fun o => o.length == 1) (bos.length * ((m + 4) + 4) + 3) := by
    apply RunsWithin.filterList (a' := .list .nat)
    intro o ho
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      exact RunsWithin.prim _ _
    case hc =>
      simp only [Prim.cost, Args.head]
      have := hol o ho
      omega
  set fl := bos.filter fun o => o.length == 1 with hfldef
  have hfl1 : ∀ o ∈ fl.reverse, o.length = 1 := fun o ho => by
    have := (List.mem_filter.1 (List.mem_reverse.1 ho)).2
    simpa using this
  have hlen : fl.length ≤ m := (List.length_filter_le _ _).trans hbl
  have hfold := (RunsWithin.foldList_inv (X := X) (body := body) (a' := .list .nat)
    (b' := .list .nat) (f := fun acc o => .op2 .append o acc) (F := fun acc o => o ++ acc)
    (I := fun _ => True) (c := 2) fl.reverse [] (fun acc _ o ho => ⟨by
      apply (RunsWithin.prim _ _).mono
      simp only [Prim.cost, Args.head]
      rw [hfl1 o ho], trivial⟩) trivial).1
  have hval : fl.reverse.foldl (fun acc o => o ++ acc) [] = fixPtsD bos := by
    rw [m5_foldl_prepend, List.reverse_reverse, List.append_nil]
    rfl
  apply RunsWithin.mono
  case h =>
    unfold Main.fixPtsProg
    run_step hfl
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact hfold.of_eq (by simpa using hval)
  case hc =>
    simp only [Prim.cost, Args.head, List.length_reverse, fixPtsCost]
    have h1 := Nat.mul_le_mul_right ((m + 4) + 4) hbl
    have h2 := Nat.mul_le_mul_right (2 + 1) hlen
    omega

end FixPtsRun

/-! ### The dispatch's runs -/

section DispatchRun

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b}
  {sub : HInstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)}
  {I : HInstData D} {n₀ n k : ℕ} {L : LabelData} {st : ℕ × CJData} {xy : StrData × StrData}
  {w : WinData} {G Fx Fy : GroupData D.denote}
  {cx cy : ((ℕ × List ℕ) × List (List ℕ)) × Bool} {ans : AnswerData D} {c : ℕ}

/-- The dispatch in Case 1. -/
theorem m5Dispatch_run1 (h1 : cx.1.1.1 = 1)
    (h : RunsWithin X body (Main.m5Case1Prog sub n₀ n L st xy w G Fx Fy) ans c) :
    RunsWithin X body (Main.m5Dispatch sub I n₀ n L st k xy w G Fx Fy cx cy) ans (c + 16) := by
  have he : (cx.1.1.1 == 1) = true := by simp [h1]
  apply RunsWithin.mono
  case h =>
    unfold Main.m5Dispatch
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    simp only [Prim.eval, he]
    exact RunsWithin.ite_true h
  case hc =>
    simp only [Prim.cost]
    omega

/-- The dispatch in Case 3. -/
theorem m5Dispatch_run3 (h1 : cx.1.1.1 ≠ 1) (h2 : cx.1.1.1 ≠ 2) {m : ℕ}
    (hbx : cx.1.2.length ≤ m) (hox : ∀ o ∈ cx.1.2, o.length ≤ m) (hby : cy.1.2.length ≤ m)
    (hoy : ∀ o ∈ cy.1.2, o.length ≤ m)
    (h : RunsWithin X body (Main.m5Case3Prog sub I n₀ n L st k xy w G (fixPtsD cx.1.2)
      (fixPtsD cy.1.2)) ans c) :
    RunsWithin X body (Main.m5Dispatch sub I n₀ n L st k xy w G Fx Fy cx cy) ans
      (c + 2 * fixPtsCost m + 20) := by
  have he1 : (cx.1.1.1 == 1) = false := by simpa using h1
  have he2 : (cx.1.1.1 == 2) = false := by simpa using h2
  apply RunsWithin.mono
  case h =>
    unfold Main.m5Dispatch
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    simp only [Prim.eval, he1]
    apply RunsWithin.ite_false
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    simp only [Prim.eval, he2]
    apply RunsWithin.ite_false
    run_step (RunsWithin.fixPtsProg hbx hox)
    run_step (RunsWithin.fixPtsProg hby hoy)
    exact h
  case hc =>
    simp only [Prim.cost]
    linarith

/-- The dispatch in Case 2 with `y`'s agreement: the run of the chosen branch. -/
theorem m5Dispatch_run2 (h2 : cx.1.1.1 = 2)
    (hrun : RunsWithin X body (.ite (cy.1.1.1 == 2 && (cx.2 && cy.2 || !cx.2 && !cy.2))
      (.ite cx.2
        (.bind (.op1 (Prim.snd (a := .nat) (b := .prod Ty.gens D)) Fx) fun fd =>
          .bind (.op1 .fst fd) fun fgs =>
          Main.m5Case2aProg sub n₀ n xy w G cx.1.1.2 cy.1.1.2 fgs)
        (Main.m5Case2bProg sub n₀ n L st xy w G Fx Fy cx.1.1.2 cy.1.1.2))
      (.op0 .none)) ans c) :
    RunsWithin X body (Main.m5Dispatch sub I n₀ n L st k xy w G Fx Fy cx cy) ans (c + 26) := by
  have he1 : (cx.1.1.1 == 1) = false := by simp [h2]
  have he2 : (cx.1.1.1 == 2) = true := by simp [h2]
  apply RunsWithin.mono
  case h =>
    unfold Main.m5Dispatch
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    simp only [Prim.eval, he1]
    apply RunsWithin.ite_false
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    simp only [Prim.eval, he2]
    apply RunsWithin.ite_true
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    simp only [Prim.eval]
    exact hrun
  case hc =>
    simp only [Prim.cost]
    linarith

/-- Case 2 when `y` disagrees: no isomorphism. -/
theorem m5_run2_none (hok : (cy.1.1.1 == 2 && (cx.2 && cy.2 || !cx.2 && !cy.2)) = false) :
    RunsWithin X body (.ite (cy.1.1.1 == 2 && (cx.2 && cy.2 || !cx.2 && !cy.2))
      (.ite cx.2
        (.bind (.op1 (Prim.snd (a := .nat) (b := .prod Ty.gens D)) Fx) fun fd =>
          .bind (.op1 .fst fd) fun fgs =>
          Main.m5Case2aProg sub n₀ n xy w G cx.1.1.2 cy.1.1.2 fgs)
        (Main.m5Case2bProg sub n₀ n L st xy w G Fx Fy cx.1.1.2 cy.1.1.2))
      (.op0 .none)) (none : AnswerData D) 2 := by
  rw [hok]
  exact RunsWithin.ite_false (RunsWithin.prim _ _)

/-- Case 2a, when `y` agrees. -/
theorem m5_run2a (hok : (cy.1.1.1 == 2 && (cx.2 && cy.2 || !cx.2 && !cy.2)) = true)
    (hA : cx.2 = true)
    (h : RunsWithin X body (Main.m5Case2aProg sub n₀ n xy w G cx.1.1.2 cy.1.1.2 Fx.2.1) ans c) :
    RunsWithin X body (.ite (cy.1.1.1 == 2 && (cx.2 && cy.2 || !cx.2 && !cy.2))
      (.ite cx.2
        (.bind (.op1 (Prim.snd (a := .nat) (b := .prod Ty.gens D)) Fx) fun fd =>
          .bind (.op1 .fst fd) fun fgs =>
          Main.m5Case2aProg sub n₀ n xy w G cx.1.1.2 cy.1.1.2 fgs)
        (Main.m5Case2bProg sub n₀ n L st xy w G Fx Fy cx.1.1.2 cy.1.1.2))
      (.op0 .none)) ans (c + 4) := by
  rw [hok]
  apply RunsWithin.mono
  case h =>
    apply RunsWithin.ite_true
    rw [hA]
    apply RunsWithin.ite_true
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact h
  case hc =>
    simp only [Prim.cost]
    omega

/-- Case 2b, when `y` agrees. -/
theorem m5_run2b (hok : (cy.1.1.1 == 2 && (cx.2 && cy.2 || !cx.2 && !cy.2)) = true)
    (hA : cx.2 = false)
    (h : RunsWithin X body (Main.m5Case2bProg sub n₀ n L st xy w G Fx Fy cx.1.1.2 cy.1.1.2)
      ans c) :
    RunsWithin X body (.ite (cy.1.1.1 == 2 && (cx.2 && cy.2 || !cx.2 && !cy.2))
      (.ite cx.2
        (.bind (.op1 (Prim.snd (a := .nat) (b := .prod Ty.gens D)) Fx) fun fd =>
          .bind (.op1 .fst fd) fun fgs =>
          Main.m5Case2aProg sub n₀ n xy w G cx.1.1.2 cy.1.1.2 fgs)
        (Main.m5Case2bProg sub n₀ n L st xy w G Fx Fy cx.1.1.2 cy.1.1.2))
      (.op0 .none)) ans (c + 2) := by
  rw [hok]
  apply RunsWithin.mono
  case h =>
    apply RunsWithin.ite_true
    rw [hA]
    exact RunsWithin.ite_false h
  case hc =>
    omega

end DispatchRun

/-! ### The dispatch: bounds, the selected case, its work and children -/

section DispatchDefs

variable {D : Ty}

/-- **The charges of M5's cases** besides reduce-and-derive's (`RDBounds`) and the backends'
(`BackendBounds`), as numbers; the hypotheses of `RunsWithin.m5Dispatch` bound the backend's
charges by them. -/
structure M5Bounds where
  /-- Case 1: the orbits of `F(x)`, `F(y)` on the base. -/
  Box : ℕ
  Boy : ℕ
  /-- Align (all cases): `ψ(G)`, membership, the kernel and lifts of the base action. -/
  BgP : ℕ
  Bmem : ℕ
  BkA : ℕ
  BlA : ℕ
  /-- The aligned group's `generate`, per case. -/
  Bg1₁ : ℕ
  Bg1₂ₐ : ℕ
  Bg1₂ᵦ : ℕ
  Bg1₃ : ℕ
  /-- Align's combining `generate`, Cases 2a, 2b, 3 (Case 1: `RDBounds`). -/
  Bgen₂ₐ : ℕ
  Bgen₂ᵦ : ℕ
  Bgen₃ : ℕ
  /-- Case 2a: the pullback's `generate`, and each sub-call's restriction. -/
  Bpb : ℕ
  sK : ℕ
  Bgm : ℕ
  Blift : ℕ
  Bker : ℕ
  Bgn : ℕ
  /-- The degree programs' `generate` at degree at most `m`. -/
  Bg : ℕ
  /-- Case 3's comparisons: the certificates' `generate` and set stabilizers. -/
  Bgk : ℕ
  Bgs : ℕ
  /-- Case 3's fallback: the kernel reduction. -/
  Bk3 : ℕ
  Bo3 : ℕ
  Bcr3 : ℕ
  Bgen3 : ℕ
  /-- The certificates' final `generate` (on at most `2 s` generators). -/
  BF : ℕ

/-- The operations of M5. -/
def m5Ops (op : GroupOp) : Prop :=
  Giant.case1Ops op ∨ Giant.c2aOps op ∨ restrictOps op ∨ Case2b.c2bOps op ∨ Case3.c3Ops op ∨
    rdOps op ∨ kerRedOps op ∨ m5CaseOps op ∨ certOps op

/-- **The case M5 runs**, from the case decisions of `x` and `y`: `1` (Case 1), `2` (Case 2a),
`4` (Case 2b), `0` (Case 2 for `x` but not in the same way for `y`: no isomorphism), `3`
(Case 3). -/
def m5Sel (O : Oracle (groupSig D)) (n N : ℕ) (Fx Fy : GroupData D.denote) : ℕ :=
  if (m5Cs O n N Fx).1 = 1 then 1
  else if (m5Cs O n N Fx).1 = 2 then
    if ((m5Cs O n N Fy).1 == 2 && (m5IsA O n N Fx && m5IsA O n N Fy ||
        !m5IsA O n N Fx && !m5IsA O n N Fy)) = true then
      (if m5IsA O n N Fx = true then 2 else 4)
    else 0
  else 3

/-- The work of each branch of reduce-and-derive in M5's cases, with factor `F` and stuck work
`W6`. -/
def m5Wb (N n wl s sIn F Bd Blift Bgen Bo W6 : ℕ) : ℕ :=
  wl * rdOrbitWork N n wl s sIn F Bd Blift Bgen Bo W6 + dynSeqCost N wl Bo + 5

/-- **The work of M5's dispatch** besides its sub-calls, for the case it runs. -/
def m5W (O : Oracle (groupSig D)) (n N k s sIn Bgen Blift Bo Bk Bcr Bd : ℕ)
    (G Fx Fy : GroupData D.denote) (wl : ℕ) (β : M5Bounds) (Bst Btr Borb Bkg Bko Bks : ℕ)
    (Bo' Bs' Bt' : ℕ → ℕ) : ℕ :=
  match m5Sel O n N Fx Fy with
  | 1 => Giant.case1Cost n N G.2.1.length
      (partGensD (N - n) (Giant.orbitPartModel O n N Fx)).length β.Box β.Boy β.BgP β.Bmem β.BkA
      β.BlA β.Bg1₁ Bgen (m5Wb N n wl s sIn (N - n) Bd Blift Bgen Bo 0) sIn + 16
  | 2 => c2aWork n N G.2.1.length ((setOps (N - n)).gens (m5Cs O n N Fx).2).length
      (m5Cs O n N Fx).2.length β.BgP β.Bmem β.BkA β.BlA β.Bg1₂ₐ β.Bgen₂ₐ sIn Bst Borb β.Bpb wl s
      β.sK β.Bgm β.Blift β.Bker β.Bgn + 30
  | 3 => c3Work n N sIn G.2.1.length k (fixPtsD (m5Os O n N Fx)).length
      (fixPtsD (m5Os O n N Fy)).length (Case2b.sojZ (N - n)) β.BgP β.Bmem β.BkA β.BlA β.Bg1₃
      β.Bgen₃ Bst Btr Borb Bkg Bko Bks β.Bgk β.Bgs wl
      (m5Wb N n wl s sIn (N - n).factorial Bd Blift Bgen Bo
        (rd6Cost N n wl s sIn Bk Bo Bcr Bgen)) +
      (kerRedCost N n wl (kerReps O n G).length (kerModel O n G).2.1.length s β.Bk3 β.Bo3
        β.Bcr3 β.Bgen3 + 5) + wl + 3 + 2 * fixPtsCost (N - n) + 20
  | 4 => (match m5Leaf2b O N n Fx (m5Cs O n N Fx).2 with
      | some X₀ => Case2b.c2bCost n N sIn G.2.1.length (m5Cs O n N Fx).2.length
          (m5Cs O n N Fy).2.length (Case2b.degD O N n Fx (m5Cs O n N Fx).2 - 1)
          (Case2b.outGensD (N - n) X₀).length Bst β.Bg (Case2b.sojZ (N - n)) β.BgP β.Bmem β.BkA
          β.BlA β.Bg1₂ᵦ β.Bgen₂ᵦ
          (m5Wb N n wl s sIn (N - n).factorial Bd Blift Bgen Bo
            (rd6Cost N n wl s sIn Bk Bo Bcr Bgen)) Bo' Bs' Bt'
      | none => 0) + 28
  | _ => 28

/-- The number of the dispatch's sub-calls on windows of at most `n / k` points (Case 3's
comparisons). -/
def m5CK (O : Oracle (groupSig D)) (n N k : ℕ) (Fx Fy : GroupData D.denote) : ℕ :=
  if m5Sel O n N Fx Fy = 3 then c3Count (fixPtsD (m5Os O n N Fx)).length k n else 0

/-- The number of the dispatch's sub-calls on windows of at most `|W| / 2` points (Case 2a's
pullback). -/
def m5CH (O : Oracle (groupSig D)) (n N sIn wl : ℕ) (Fx Fy : GroupData D.denote) : ℕ :=
  if m5Sel O n N Fx Fy = 2 then (sIn + 1) * wl else 0

/-- The factor of the dispatch's children list. -/
def m5CF (O : Oracle (groupSig D)) (n N k : ℕ) (Fx Fy : GroupData D.denote) : ℕ :=
  match m5Sel O n N Fx Fy with
  | 1 => 1 * (N - n)
  | 3 => Case3.c3R k (fixPtsD (m5Os O n N Fy)).length (Case2b.sojZ (N - n)) *
      (N - n).factorial + (N - n).factorial
  | 4 => Case2b.c2bR N n (m5Cs O n N Fy).2.length (Case2b.degD O N n Fx (m5Cs O n N Fx).2 - 1)
      (Case2b.sojZ (N - n)) * (N - n).factorial
  | _ => 0

theorem m5Cs_eq (O : Oracle (groupSig D)) (n N : ℕ) (F : GroupData D.denote) :
    Giant.caseD (N - n) (Giant.agShiftD n (O.run GroupOp.orbits (F, baseWin n N))) =
      m5Cs O n N F := rfl

theorem m5Os_eq (O : Oracle (groupSig D)) (n N : ℕ) (F : GroupData D.denote) :
    Giant.agShiftD n (O.run GroupOp.orbits (F, baseWin n N)) = m5Os O n N F := rfl

theorem m5CK_of_ne {O : Oracle (groupSig D)} {n N k : ℕ} {Fx Fy : GroupData D.denote}
    (h : m5Sel O n N Fx Fy ≠ 3) : m5CK O n N k Fx Fy = 0 := by
  unfold m5CK
  rw [if_neg' h]

theorem m5CH_of_ne {O : Oracle (groupSig D)} {n N sIn wl : ℕ} {Fx Fy : GroupData D.denote}
    (h : m5Sel O n N Fx Fy ≠ 2) : m5CH O n N sIn wl Fx Fy = 0 := by
  unfold m5CH
  rw [if_neg' h]

end DispatchDefs

/-! ### The dispatch's specification -/

/-- The tag of the case decision is `1`, `2` or `3`. -/
theorem m5_caseD_tag (m : ℕ) (bos : List (List ℕ)) :
    (Giant.caseD m bos).1 = 1 ∨ (Giant.caseD m bos).1 = 2 ∨ (Giant.caseD m bos).1 = 3 := by
  unfold Giant.caseD
  split
  · exact Or.inr (Or.inl rfl)
  · split_ifs
    · exact Or.inr (Or.inr rfl)
    · exact Or.inl rfl

/-- The orbits of `F` on the base, as base indices: at most `m` lists of at most `m` points. -/
theorem m5_os_bounds {N n : ℕ} {F : Subgroup (Perm (Fin N))} {os : List (List ℕ)}
    (hos : IsOrbitPartition F (baseWin n N) os) :
    (Giant.agShiftD n os).length ≤ N - n ∧ ∀ o ∈ Giant.agShiftD n os, o.length ≤ N - n := by
  refine ⟨by simpa [Giant.agShiftD] using Giant.c1_length_os hos, fun o ho => ?_⟩
  obtain ⟨o', ho', rfl⟩ := List.mem_map.1 ho
  simpa using Giant.c1_length_orbit hos ho'

section DispatchSpec

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}
  {sub : HInstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)}
  {C : ℕ → Option ℕ → ℕ} {s : ℕ} {xy : StrData × StrData} {w : WinData}
  {N : ℕ} {gs : GensData} {d : D.denote} {n₀ n : ℕ} {L : LabelData} {st : ℕ × CJData}
  {sIn Lg Blift Bgen Bo Bk Bcr Bd : ℕ}

/-- **M5's dispatch.** On the restricted hinted instance `I` (the string positions all in the
window, representative `1`, `G` faithful on the strings with a giant base action), from the full
groups `Fx = F(x)`, `Fy = F(y)` and their case decisions: the answer is correct for `G` on `W`.
The cost is the children's (`StepChild |W| m`, factor `m5CF`), `m5CK` sub-calls without a hint
on windows of at most `n / k` points (Case 3's comparisons), `m5CH` sub-calls without a hint on
windows of at most `|W| / 2` points (Case 2a's pullback), and the work `m5W` of the case run
(`m5Sel`). In Case 2, when `y`'s case decision differs from `x`'s, there is no isomorphism
(`m5_large_iso`, `m5_tupTrans_iso`). -/
theorem RunsWithin.m5Dispatch (hO : MeetsContractOn DV m5Ops X.O)
    (hPre : ∀ op x, m5Ops op → GroupPre DV op x → X.Pre op x)
    (hI : HInstValid DV (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D))
    {hC : CertSetting (GensData.denote N gs) n} {φ : strGroup hC →* Perm (Fin (N - n))}
    (hφ : IsPhi hC φ)
    (halt : alternatingGroup (Fin (N - n)) ≤ (baseHom _ n hC.base).range)
    (hwS : ∀ u : Fin N, u.val < n → u ∈ w.denote N)
    {k : ℕ} (h5 : 5 ≤ k) (hk : k + 2 ≤ N - n) (hm12 : 12 ≤ N - n)
    {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N sIn G₀) (hgs : gs.length ≤ sIn)
    (hGG₀ : GensData.denote N gs ≤ G₀) {sk : ℕ} (Bk' : BackendBounds X DV k sk ⊤)
    (hsk : sIn ≤ k * (sk + 1)) {sm : ℕ → ℕ} (Bm : ∀ M, BackendBounds X DV M (sm M) ⊤)
    (hsub : HSubSolves X body DV sub
      (fun J => SizeChild (max sIn (supTo sm (w.1.length / 2)))
          (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D) J ∧
        StepChild w.1.length (N - n) (J.winSize, J.baseOpt)) C s)
    (hCmono : ∀ a b, a ≤ b → C a none ≤ C b none) (hs : s ≤ sIn)
    (hB : RDBounds X DV n N sIn Lg Blift Bgen Bo Bk Bcr)
    (hLg : (N - n).factorial * (sIn + 1) ≤ Lg) (hst : st.1 ≠ 2) (β : M5Bounds)
    -- the full groups
    {fxs fys : GensData} {ex ey : D.denote} (hFxv : GroupValid DV N fxs ex)
    (hFyv : GroupValid DV N fys ey) (hFxs : fxs.length ≤ sIn) (hFys : fys.length ≤ sIn)
    (hFxe : GensData.denote N fxs = m5Fmap hC φ k (xy.1.denote N))
    (hFye : GensData.denote N fys = m5Fmap hC φ k (xy.2.denote N))
    -- charges on `G`
    (hBgP : X.B.call GroupOp.generate (N - n, gs.map (baseD n N))
      (X.O.run GroupOp.generate (N - n, gs.map (baseD n N))) ≤ β.BgP)
    (hBmem : ∀ g : PermData, g.Valid (N - n) → X.B.call GroupOp.mem (pModel X.O n (N, gs, d), g)
      (X.O.run GroupOp.mem (pModel X.O n (N, gs, d), g)) ≤ β.Bmem)
    (hBkA : X.B.call GroupOp.kernel ((N, gs, d), baseWin n N) (kerModel X.O n (N, gs, d)) ≤
      β.BkA)
    (hBlA : ∀ π : PermData, X.B.call GroupOp.lift ((N, gs, d), (baseWin n N, π))
      (liftModel X.O n (N, gs, d) π) ≤ β.BlA)
    (hBg : ∀ M ≤ N - n, ∀ gs' : GensData, GensData.AllValid M gs' → gs'.length ≤ sIn →
      X.B.call GroupOp.generate (M, gs') (X.O.run GroupOp.generate (M, gs')) ≤ β.Bg)
    (hBgk : ∀ gs' : GensData, GensData.AllValid N gs' →
      gs'.length ≤ k.factorial * (sIn + 1) → GensData.denote N gs' ≤ GensData.denote N gs →
        X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.Bgk)
    (hBgs : ∀ al : List ℕ, al.Nodup → al.length = k → (∀ a ∈ al, a < N - n) → ∀ b₁ b₂,
      X.B.call GroupOp.generate (N, giantGens X.O n (N, gs, d) al b₁ b₂)
        (giantSetStabModel X.O n (N, gs, d) al b₁ b₂) ≤ β.Bgs)
    (hBk3 : X.B.call GroupOp.kernel ((N, gs, d), baseWin n N) (kerModel X.O n (N, gs, d)) ≤
      β.Bk3)
    (hBo3 : X.B.call GroupOp.orbits (kerModel X.O n (N, gs, d), w)
      (krOrbits X.O n (N, gs, d) w) ≤ β.Bo3)
    (hBcr3 : X.B.call GroupOp.cosetReps ((N, gs, d), kerModel X.O n (N, gs, d))
      (kerReps X.O n (N, gs, d)) ≤ β.Bcr3)
    (hB3 : ∀ hs : GensData, GensData.AllValid N hs →
      hs.length ≤ (kerReps X.O n (N, gs, d)).length *
        (max s (kerModel X.O n (N, gs, d)).2.1.length + 1) →
      GensData.denote N hs ≤ GensData.denote N gs →
      X.B.call GroupOp.generate (N, hs) (X.O.run GroupOp.generate (N, hs)) ≤ β.Bgen3)
    -- Case 1
    (hBox : X.B.call GroupOp.orbits ((N, fxs, ex), baseWin n N)
      (Giant.baseOrbits X.O n N (N, fxs, ex)) ≤ β.Box)
    (hBoy : X.B.call GroupOp.orbits ((N, fys, ey), baseWin n N)
      (Giant.baseOrbits X.O n N (N, fys, ey)) ≤ β.Boy)
    (hBg1₁ : X.B.call GroupOp.generate
      (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
        (partGensD (N - n) (Giant.orbitPartModel X.O n N (N, fxs, ex))))).map
        (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
      (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
        (partGensD (N - n) (Giant.orbitPartModel X.O n N (N, fxs, ex)))))) ≤ β.Bg1₁)
    (hD₁ : ∀ gs' d' O', RDSet DV n N gs w L (Giant.g1Model X.O n (N, gs, d) (partOps (N - n))
        (Giant.orbitPartModel X.O n N (N, fxs, ex))).2.1 sIn gs' d' O' →
      RDOrbit X body DV n N w L st sIn Bd gs' d' O')
    -- Case 2a
    (hBg1₂ₐ : X.B.call GroupOp.generate
      (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
        ((setOps (N - n)).gens (m5Cs X.O n N (N, fxs, ex)).2))).map
        (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
      (Giant.g1Model X.O n (N, gs, d) (setOps (N - n)) (m5Cs X.O n N (N, fxs, ex)).2) ≤
        β.Bg1₂ₐ)
    (hBgen₂ₐ : ∀ gs' : GensData, GensData.AllValid N gs' → gs'.length ≤ sIn + 1 →
      GensData.denote N gs' ≤ GensData.denote N gs →
      X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.Bgen₂ₐ)
    (hBpb : ∀ gs', GensData.AllValid N gs' →
      gs'.length ≤ (sIn + 1) * (sIn + 1) + sIn + fxs.length → GensData.denote N gs' ≤ G₀ →
      X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.Bpb)
    (hBgm : ∀ (w' : WinData) (σ' : PermData) (gs' : GensData) (d' : D.denote),
      Giant.PbSubP DV G₀ xy w.1.length sIn (xy, w', σ', N, gs', d') →
      X.B.call GroupOp.generate (w'.1.length, GensData.restrictTo (WinData.pos N w') w'.1 gs')
        (X.O.run GroupOp.generate
          (w'.1.length, GensData.restrictTo (WinData.pos N w') w'.1 gs')) ≤ β.Bgm)
    (hBlift : ∀ (w' : WinData) (σ' : PermData) (gs' : GensData) (d' : D.denote),
      Giant.PbSubP DV G₀ xy w.1.length sIn (xy, w', σ', N, gs', d') → ∀ π' : PermData,
      X.B.call GroupOp.lift ((N, gs', d'), (w', π'))
        (X.O.run GroupOp.lift ((N, gs', d'), (w', π'))) ≤ β.Blift)
    (hBker : ∀ (w' : WinData) (σ' : PermData) (gs' : GensData) (d' : D.denote),
      Giant.PbSubP DV G₀ xy w.1.length sIn (xy, w', σ', N, gs', d') →
      X.B.call GroupOp.kernel ((N, gs', d'), w') (X.O.run GroupOp.kernel ((N, gs', d'), w')) ≤
        β.Bker)
    (hsK : ∀ (w' : WinData) (σ' : PermData) (gs' : GensData) (d' : D.denote),
      Giant.PbSubP DV G₀ xy w.1.length sIn (xy, w', σ', N, gs', d') →
      (X.O.run GroupOp.kernel ((N, gs', d'), w')).2.1.length ≤ β.sK)
    (hBgn : ∀ hs : GensData, GensData.AllValid N hs → hs.length ≤ β.sK + s →
      GensData.denote N hs ≤ G₀ →
      X.B.call GroupOp.generate (N, hs) (X.O.run GroupOp.generate (N, hs)) ≤ β.Bgn)
    -- Case 2b
    (hBg1₂ᵦ : ∀ X₀ : SoJTree.OutD,
      m5Leaf2b X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 = some X₀ →
      X.B.call GroupOp.generate
        (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (Case2b.outGensD (N - n) X₀))).map
          (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
        (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (Case2b.outGensD (N - n) X₀)))) ≤ β.Bg1₂ᵦ)
    (hBgen₂ᵦ : ∀ gs' : GensData, GensData.AllValid N gs' →
      gs'.length ≤ Case2b.c2bR N n (m5Cs X.O n N (N, fys, ey)).2.length
        (Case2b.degD X.O N n (N, fys, ey) (m5Cs X.O n N (N, fys, ey)).2 - 1)
        (Case2b.sojZ (N - n)) * (sIn + 1) →
      GensData.denote N gs' ≤ GensData.denote N gs →
      X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.Bgen₂ᵦ)
    (hD₂ᵦ : ∀ X₀, m5Leaf2b X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 = some X₀ →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (Case2b.outOps (N - n)) X₀).2.1 sIn gs' d' O' →
      RDOrbit X body DV n N w L st sIn Bd gs' d' O')
    -- Case 3
    (hBg1₃ : ∀ X₀ : SoJTree.OutD, Case3.C3First φ (strOn hC.le (xy.1.denote N)) (N - n) k
        (fixPtsD (m5Os X.O n N (N, fxs, ex))) X₀ →
      X.B.call GroupOp.generate
        (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (Case2b.outGensD (N - n) X₀))).map
          (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
        (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (Case2b.outGensD (N - n) X₀)))) ≤ β.Bg1₃)
    (hBgen₃ : ∀ gs' : GensData, GensData.AllValid N gs' →
      gs'.length ≤ Case3.c3R k (fixPtsD (m5Os X.O n N (N, fys, ey))).length
        (Case2b.sojZ (N - n)) * (sIn + 1) →
      GensData.denote N gs' ≤ GensData.denote N gs →
      X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.Bgen₃)
    (hD₃ : ∀ X₀, Case3.C3First φ (strOn hC.le (xy.1.denote N)) (N - n) k
        (fixPtsD (m5Os X.O n N (N, fxs, ex))) X₀ →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (Case2b.outOps (N - n)) X₀).2.1 sIn gs' d' O' →
      RDOrbit X body DV n N w L st sIn Bd gs' d' O') :
    ∃ (ans : AnswerData D) (ch : List (ℕ × Option ℕ)),
      RunsWithin X body (Main.m5Dispatch sub
          (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D) n₀ n L st k xy w
          (N, gs, d) (N, fxs, ex) (N, fys, ey) (m5CaseD X.O n N (N, fxs, ex))
          (m5CaseD X.O n N (N, fys, ey))) ans
        ((ch.map fun x => C x.1 x.2).sum +
          m5CK X.O n N k (N, fxs, ex) (N, fys, ey) * C (n / k) none +
          m5CH X.O n N sIn w.1.length (N, fxs, ex) (N, fys, ey) * C (w.1.length / 2) none +
          m5W X.O n N k s sIn Bgen Blift Bo Bk Bcr Bd (N, gs, d) (N, fxs, ex) (N, fys, ey)
            w.1.length β B.Bstab B.Btr B.Borb Bk'.Bgen Bk'.Borb Bk'.Bstab
            (fun M => (Bm M).Borb) (fun M => (Bm M).Bstab) (fun M => (Bm M).Btr)) ∧
      AnsOK DV N (w.denote N) 1 (GensData.denote N gs) (xy.1.denote N) (xy.2.denote N) ans ∧
      (∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sIn) ∧
      ChildList w.1.length (m5CF X.O n N k (N, fxs, ex) (N, fys, ey))
        (StepChild w.1.length (N - n)) ch := by
  classical
  -- the sub-solver on the children of every case but 2a, and Case 2a's generator bound
  have hsubI : HSubSolves X body DV sub
      (fun J => SizeChild sIn (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D)
        J ∧ StepChild w.1.length (N - n) (J.winSize, J.baseOpt)) C s :=
    hsub.mono fun J hJ => ⟨hJ.1.mono (le_max_left _ _), hJ.2⟩
  have hgR : ∀ M ≤ w.1.length / 2, ∀ hs : GensData, GensData.AllValid M hs → hs.length ≤ sIn →
      (X.O.run GroupOp.generate (M, hs)).2.1.length ≤ max sIn (supTo sm (w.1.length / 2)) :=
    fun M hM hs hv _ =>
      ((Bm M).genOut hs hv le_top).trans ((le_supTo hM).trans (le_max_right _ _))
  -- the operations
  have hOc1 : MeetsContractOn DV Giant.case1Ops X.O := fun op x h hx => hO op x (Or.inl h) hx
  have hPc1 : ∀ op x, Giant.case1Ops op → GroupPre DV op x → X.Pre op x :=
    fun op x h hx => hPre op x (Or.inl h) hx
  have hO2a : MeetsContractOn DV Giant.c2aOps X.O :=
    fun op x h hx => hO op x (Or.inr (Or.inl h)) hx
  have hP2a : ∀ op x, Giant.c2aOps op → GroupPre DV op x → X.Pre op x :=
    fun op x h hx => hPre op x (Or.inr (Or.inl h)) hx
  have hOr : MeetsContractOn DV restrictOps X.O :=
    fun op x h hx => hO op x (Or.inr (Or.inr (Or.inl h))) hx
  have hPr : ∀ op x, restrictOps op → GroupPre DV op x → X.Pre op x :=
    fun op x h hx => hPre op x (Or.inr (Or.inr (Or.inl h))) hx
  have hO2b : MeetsContractOn DV Case2b.c2bOps X.O :=
    fun op x h hx => hO op x (Or.inr (Or.inr (Or.inr (Or.inl h)))) hx
  have hP2b : ∀ op x, Case2b.c2bOps op → GroupPre DV op x → X.Pre op x :=
    fun op x h hx => hPre op x (Or.inr (Or.inr (Or.inr (Or.inl h)))) hx
  have hO3 : MeetsContractOn DV Case3.c3Ops X.O :=
    fun op x h hx => hO op x (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))) hx
  have hP3 : ∀ op x, Case3.c3Ops op → GroupPre DV op x → X.Pre op x :=
    fun op x h hx => hPre op x (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))) hx
  have hOrd : MeetsContractOn DV rdOps X.O :=
    fun op x h hx => hO op x (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))) hx
  have hPrd : ∀ op x, rdOps op → GroupPre DV op x → X.Pre op x :=
    fun op x h hx => hPre op x (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))) hx
  have hOk : MeetsContractOn DV kerRedOps X.O :=
    fun op x h hx => hO op x (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))) hx
  have hPk : ∀ op x, kerRedOps op → GroupPre DV op x → X.Pre op x := fun op x h hx =>
    hPre op x (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))) hx
  have hOcs : MeetsContractOn DV m5CaseOps X.O := fun op x h hx =>
    hO op x (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))) hx
  have hPcs : ∀ op x, m5CaseOps op → GroupPre DV op x → X.Pre op x := fun op x h hx =>
    hPre op x (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))) hx
  -- the setting
  have hGv : GroupValid DV N gs d := hI.valid.group
  have hG : IsInvariant (GensData.denote N gs) (baseSet n N) := hC.base
  have hWG : IsInvariant (GensData.denote N gs) (w.denote N) := hI.valid.invariant
  have hFxG : GensData.denote N fxs ≤ GensData.denote N gs := hFxe ▸ m5Fmap_le hC φ k _
  have hFyG : GensData.denote N fys ≤ GensData.denote N gs := hFye ▸ m5Fmap_le hC φ k _
  have hFxi : IsInvariant (GensData.denote N fxs) (baseSet n N) := hG.mono hFxG
  have hFyi : IsInvariant (GensData.denote N fys) (baseSet n N) := hG.mono hFyG
  have hFx₀ : GensData.denote N fxs ≤ G₀ := hFxG.trans hGG₀
  have hFy₀ : GensData.denote N fys ≤ G₀ := hFyG.trans hGG₀
  obtain ⟨hosx, hAx, hngx⟩ := m5Case_spec hOcs hPcs B Bm hFxv hFxs hFx₀ hFxi
  obtain ⟨hosy, hAy, hngy⟩ := m5Case_spec hOcs hPcs B Bm hFyv hFys hFy₀ hFyi
  have hcx := Giant.caseD_spec hFxi hosx
  have hcy := Giant.caseD_spec hFyi hosy
  rw [m5Cs_eq] at hcx hcy
  have hLg' : (N - n) * (sIn + 1) ≤ Lg :=
    (Nat.mul_le_mul_right _ (Nat.self_le_factorial _)).trans hLg
  by_cases h1 : (m5Cs X.O n N (N, fxs, ex)).1 = 1
  · -- Case 1
    have hsel : m5Sel X.O n N (N, fxs, ex) (N, fys, ey) = 1 := by simp [m5Sel, h1]
    obtain ⟨hc1a, hc1b⟩ := hcx.2.2.1.1 h1
    obtain ⟨ans, ch, hrun, hok, hg, hch⟩ := RunsWithin.m5Case1Prog_ns hOc1 hPc1 hOrd hPrd hI
      hG halt B hGG₀ le_rfl (m5Fmap_le hC φ k) (m5Fmap_loc hC φ k hwS) (m5Fmap_relabel hC φ k)
      hFxv hFyv hFxe hFye hFxi hc1a hc1b hBox hBoy hBgP hBmem hBkA hBlA hBg1₁ hsubI hB hs hLg'
      (by omega) hst hD₁
    refine ⟨ans, ch, (m5Dispatch_run1 h1 hrun).mono ?_, hok, hg, ?_⟩
    · rw [m5CK_of_ne (by rw [hsel]; decide), m5CH_of_ne (by rw [hsel]; decide)]
      have hW : m5W X.O n N k s sIn Bgen Blift Bo Bk Bcr Bd (N, gs, d) (N, fxs, ex) (N, fys, ey)
          w.1.length β B.Bstab B.Btr B.Borb Bk'.Bgen Bk'.Borb Bk'.Bstab
          (fun M => (Bm M).Borb) (fun M => (Bm M).Bstab) (fun M => (Bm M).Btr) =
          Giant.case1Cost n N gs.length
            (partGensD (N - n) (Giant.orbitPartModel X.O n N (N, fxs, ex))).length β.Box β.Boy
            β.BgP β.Bmem β.BkA β.BlA β.Bg1₁ Bgen
            (m5Wb N n w.1.length s sIn (N - n) Bd Blift Bgen Bo 0) sIn + 16 := by
        unfold m5W
        rw [hsel]
        rfl
      rw [hW]
      simp only [m5Wb]
      omega
    · have hF : m5CF X.O n N k (N, fxs, ex) (N, fys, ey) = 1 * (N - n) := by
        unfold m5CF
        rw [hsel]
        rfl
      rw [hF]
      exact hch
  by_cases h2 : (m5Cs X.O n N (N, fxs, ex)).1 = 2
  · obtain ⟨hΦxn, hΦxl, hΦx2, hΦxo⟩ := hcx.2.1 h2
    by_cases hok : ((m5Cs X.O n N (N, fys, ey)).1 == 2 &&
        (m5IsA X.O n N (N, fxs, ex) && m5IsA X.O n N (N, fys, ey) ||
          !m5IsA X.O n N (N, fxs, ex) && !m5IsA X.O n N (N, fys, ey))) = true
    · have h2y : (m5Cs X.O n N (N, fys, ey)).1 = 2 := by
        simp only [Bool.and_eq_true, beq_iff_eq] at hok
        exact hok.1
      obtain ⟨hΦyn, hΦyl, hΦy2, hΦyo⟩ := hcy.2.1 h2y
      by_cases hA : m5IsA X.O n N (N, fxs, ex) = true
      · -- Case 2a
        have hsel : m5Sel X.O n N (N, fxs, ex) (N, fys, ey) = 2 := by
          unfold m5Sel
          rw [if_neg' h1, if_pos' h2, if_pos' hok, if_pos' hA]
        obtain ⟨lab, t, he, ht, ht1, ht2⟩ := m5_labels (hI.hint L rfl).1 hGv.1 hI.valid.win
          hWG (hI.hint L rfl).2 hG
        obtain ⟨ans, hrun, hok', hg⟩ := RunsWithin.m5Case2aProg hO2a hP2a hOr hPr hI B hGG₀ hG
          halt (by omega) he ht ht1 ht2 (m5Fmap_le hC φ k) (m5Fmap_loc hC φ k hwS)
          (m5Fmap_relabel hC φ k) hFxv.1 hFxe
          (fun f hf => m5Fmap_matchesW hC φ k _ (fun u hu => hI.win_lt u.val hu) f (hFxe ▸ hf))
          hFye hFxi hFyi hΦxn hΦxl hΦx2 hΦxo hΦyn hΦyl hΦy2 hΦyo (hAx h2 hA) hBgP hBmem hBkA
          hBlA hBg1₂ₐ hBgen₂ₐ hBpb hgR hsub hCmono hBgm hBlift hBker hsK hBgn
        refine ⟨ans, [], (m5Dispatch_run2 h2 (m5_run2a hok hA hrun)).mono ?_, hok',
          hg sIn (fun gs' hv hle => B.genOut gs' hv (hle.trans hGG₀)),
          ⟨by simp, by simp, by simp⟩⟩
        rw [m5CK_of_ne (by rw [hsel]; decide)]
        have hH : m5CH X.O n N sIn w.1.length (N, fxs, ex) (N, fys, ey) =
            (sIn + 1) * w.1.length := by
          unfold m5CH
          rw [if_pos' hsel]
        have hW : m5W X.O n N k s sIn Bgen Blift Bo Bk Bcr Bd (N, gs, d) (N, fxs, ex)
            (N, fys, ey) w.1.length β B.Bstab B.Btr B.Borb Bk'.Bgen Bk'.Borb Bk'.Bstab
            (fun M => (Bm M).Borb) (fun M => (Bm M).Bstab) (fun M => (Bm M).Btr) =
            c2aWork n N gs.length ((setOps (N - n)).gens (m5Cs X.O n N (N, fxs, ex)).2).length
              (m5Cs X.O n N (N, fxs, ex)).2.length β.BgP β.Bmem β.BkA β.BlA β.Bg1₂ₐ β.Bgen₂ₐ
              sIn B.Bstab B.Borb β.Bpb w.1.length s β.sK β.Bgm β.Blift β.Bker β.Bgn + 30 := by
          unfold m5W
          rw [hsel]
          rfl
        rw [hH, hW]
        simp only [List.map_nil, List.sum_nil]
        omega
      · -- Case 2b
        have hA' : m5IsA X.O n N (N, fxs, ex) = false := by simpa using hA
        have hAy' : m5IsA X.O n N (N, fys, ey) = false := by
          have h' := hok
          rw [hA'] at h'
          simp only [Bool.and_eq_true, beq_iff_eq, Bool.false_and, Bool.not_false, Bool.true_and,
            Bool.false_or, Bool.not_eq_true'] at h'
          exact h'.2
        have hsel : m5Sel X.O n N (N, fxs, ex) (N, fys, ey) = 4 := by
          unfold m5Sel
          rw [if_neg' h1, if_pos' h2, if_pos' hok, if_neg' hA]
        obtain ⟨X₀, hX₀, ans, ch, hrun, hok', hg, hch⟩ := RunsWithin.m5Case2bProg
          (F := (N - n).factorial) (W6 := rd6Cost N n w.1.length s sIn Bk Bo Bcr Bgen) hO2b
          hP2b hOrd hPrd hI B hGG₀ Bm hG halt (m5Fmap_loc hC φ k hwS) (m5Fmap_relabel hC φ k)
          hFxv hFyv hFxs hFys hFx₀ hFy₀ hFxe hFye hFxi hFyi hΦxn hΦxl hΦx2 hΦxo hΦyn hΦyl
          hΦy2 hΦyo (hngx h2 hA') (hngy h2y hAy') hBg hBgP hBmem hBkA hBlA hBg1₂ᵦ hBgen₂ᵦ
          hsubI hB hs hLg (Nat.factorial_pos _) (Nat.self_le_factorial _) hD₂ᵦ
          (fun _ _ => Or.inl le_rfl) (fun _ _ => Or.inr ⟨le_rfl, le_rfl⟩)
        refine ⟨ans, ch, (m5Dispatch_run2 h2 (m5_run2b hok hA' hrun)).mono ?_, hok', hg, ?_⟩
        · rw [m5CK_of_ne (by rw [hsel]; decide), m5CH_of_ne (by rw [hsel]; decide)]
          have hW : m5W X.O n N k s sIn Bgen Blift Bo Bk Bcr Bd (N, gs, d) (N, fxs, ex)
              (N, fys, ey) w.1.length β B.Bstab B.Btr B.Borb Bk'.Bgen Bk'.Borb Bk'.Bstab
              (fun M => (Bm M).Borb) (fun M => (Bm M).Bstab) (fun M => (Bm M).Btr) =
              Case2b.c2bCost n N sIn gs.length (m5Cs X.O n N (N, fxs, ex)).2.length
                (m5Cs X.O n N (N, fys, ey)).2.length
                (Case2b.degD X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 - 1)
                (Case2b.outGensD (N - n) X₀).length B.Bstab β.Bg (Case2b.sojZ (N - n)) β.BgP
                β.Bmem β.BkA β.BlA β.Bg1₂ᵦ β.Bgen₂ᵦ
                (m5Wb N n w.1.length s sIn (N - n).factorial Bd Blift Bgen Bo
                  (rd6Cost N n w.1.length s sIn Bk Bo Bcr Bgen))
                (fun M => (Bm M).Borb) (fun M => (Bm M).Bstab) (fun M => (Bm M).Btr) + 28 := by
            unfold m5W
            rw [hsel]
            simp only
            rw [hX₀]
          rw [hW]
          simp only [m5Wb]
          omega
        · have hF : m5CF X.O n N k (N, fxs, ex) (N, fys, ey) =
              Case2b.c2bR N n (m5Cs X.O n N (N, fys, ey)).2.length
                (Case2b.degD X.O N n (N, fxs, ex) (m5Cs X.O n N (N, fxs, ex)).2 - 1)
                (Case2b.sojZ (N - n)) * (N - n).factorial := by
            unfold m5CF
            rw [hsel]
            rfl
          rw [hF]
          exact hch
    · -- Case 2 for `x`, not in the same way for `y`: no isomorphism
      have hsel : m5Sel X.O n N (N, fxs, ex) (N, fys, ey) = 0 := by
        unfold m5Sel
        rw [if_neg' h1, if_pos' h2, if_neg' hok]
      refine ⟨none, [], (m5Dispatch_run2 h2 (m5_run2_none (Bool.eq_false_iff.2 hok))).mono ?_, ?_,
        by simp, ⟨by simp, by simp, by simp⟩⟩
      · rw [m5CK_of_ne (by rw [hsel]; decide), m5CH_of_ne (by rw [hsel]; decide)]
        have hW : m5W X.O n N k s sIn Bgen Blift Bo Bk Bcr Bd (N, gs, d) (N, fxs, ex)
            (N, fys, ey) w.1.length β B.Bstab B.Btr B.Borb Bk'.Bgen Bk'.Borb Bk'.Bstab
            (fun M => (Bm M).Borb) (fun M => (Bm M).Bstab) (fun M => (Bm M).Btr) = 28 := by
          unfold m5W
          rw [hsel]
          rfl
        rw [hW]
        simp
      · show iso (w.denote N) 1 (GensData.denote N gs) (xy.1.denote N) (xy.2.denote N) = ∅
        refine Set.eq_empty_of_forall_notMem fun g hg => hok ?_
        have hly := m5_large_iso hC φ k hwS hWG hg hFxe hFye hFxi hFyi (hcx.1.1 h2)
        have h2y : (m5Cs X.O n N (N, fys, ey)).1 = 2 := hcy.1.2 hly
        obtain ⟨hΦyn, hΦyl, hΦy2, hΦyo⟩ := hcy.2.1 h2y
        have hiffx := m5_isA_iff hOcs hPcs B Bm hFxv hFxs hFx₀ hFxi h2
        have hiffy := m5_isA_iff hOcs hPcs B Bm hFyv hFys hFy₀ hFyi h2y
        have htt := m5_tupTrans_iso hC φ k hwS hWG hg hFxe hFye hFxi hFyi hΦxn hΦxl hΦx2 hΦxo
          hΦyn hΦyl hΦy2 hΦyo
        have hAeq : m5IsA X.O n N (N, fxs, ex) = m5IsA X.O n N (N, fys, ey) := by
          rw [Bool.eq_iff_iff, ← hiffx, ← hiffy]
          exact htt.symm
        rw [hAeq, h2y]
        cases m5IsA X.O n N (N, fys, ey) <;> simp
  · -- Case 3
    have h3 : (m5Cs X.O n N (N, fxs, ex)).1 = 3 := by
      rcases m5_caseD_tag (N - n) (m5Os X.O n N (N, fxs, ex)) with h | h | h
      · exact absurd h h1
      · exact absurd h h2
      · exact h
    have hsel : m5Sel X.O n N (N, fxs, ex) (N, fys, ey) = 3 := by
      unfold m5Sel
      rw [if_neg' h1, if_neg' h2]
    obtain ⟨-, hc3b⟩ := hcx.2.2.2.1 h3
    obtain ⟨hVxn, hVxl, hVxF⟩ := fixPtsD_spec hFxi hosx
    obtain ⟨hVyn, hVyl, hVyF⟩ := fixPtsD_spec hFyi hosy
    rw [m5Os_eq] at hVxn hVxl hVxF hVyn hVyl hVyF
    have hlen := m5_fix_len hVxn hVxl hVxF
    have hm6 : 6 ≤ (fixPtsD (m5Os X.O n N (N, fxs, ex))).length := by
      omega
    obtain ⟨ans, ch, hrun, hok', hg, hch⟩ := RunsWithin.m5Case3Prog hO3 hP3 hOrd hPrd hOk hPk
      hI hφ halt hwS (m5Fmap_loc hC φ k hwS) (m5Fmap_relabel hC φ k) hFxe hFye hFxi hFyi hVxl
      hVxn hVyl hVyn hVxF hVyF hm6 h5 hk B hgs hGG₀ Bk' hsk hBgk hBlA hBgs hBgP hBmem hBkA
      hBg1₃ hBgen₃ hsubI hCmono hB hs hLg hD₃ hBk3 hBo3 hBcr3 hB3
    obtain ⟨hbx, hox⟩ := m5_os_bounds hosx
    obtain ⟨hby, hoy⟩ := m5_os_bounds hosy
    refine ⟨ans, ch, (m5Dispatch_run3 h1 h2 hbx hox hby hoy hrun).mono ?_, hok', hg, ?_⟩
    · rw [m5CH_of_ne (by rw [hsel]; decide)]
      have hK : m5CK X.O n N k (N, fxs, ex) (N, fys, ey) =
          c3Count (fixPtsD (m5Os X.O n N (N, fxs, ex))).length k n := by
        unfold m5CK
        rw [if_pos' hsel]
      have hW : m5W X.O n N k s sIn Bgen Blift Bo Bk Bcr Bd (N, gs, d) (N, fxs, ex)
          (N, fys, ey) w.1.length β B.Bstab B.Btr B.Borb Bk'.Bgen Bk'.Borb Bk'.Bstab
          (fun M => (Bm M).Borb) (fun M => (Bm M).Bstab) (fun M => (Bm M).Btr) =
          c3Work n N sIn gs.length k (fixPtsD (m5Os X.O n N (N, fxs, ex))).length
            (fixPtsD (m5Os X.O n N (N, fys, ey))).length (Case2b.sojZ (N - n)) β.BgP β.Bmem
            β.BkA β.BlA β.Bg1₃ β.Bgen₃ B.Bstab B.Btr B.Borb Bk'.Bgen Bk'.Borb Bk'.Bstab β.Bgk
            β.Bgs w.1.length
            (m5Wb N n w.1.length s sIn (N - n).factorial Bd Blift Bgen Bo
              (rd6Cost N n w.1.length s sIn Bk Bo Bcr Bgen)) +
          (kerRedCost N n w.1.length (kerReps X.O n (N, gs, d)).length
            (kerModel X.O n (N, gs, d)).2.1.length s β.Bk3 β.Bo3 β.Bcr3 β.Bgen3 + 5) +
          w.1.length + 3 + 2 * fixPtsCost (N - n) + 20 := by
        unfold m5W
        rw [hsel]
        rfl
      rw [hK, hW]
      simp only [m5Wb]
      omega
    · have hF : m5CF X.O n N k (N, fxs, ex) (N, fys, ey) =
          Case3.c3R k (fixPtsD (m5Os X.O n N (N, fys, ey))).length (Case2b.sojZ (N - n)) *
            (N - n).factorial + (N - n).factorial := by
        unfold m5CF
        rw [hsel]
        rfl
      rw [hF]
      exact hch

end DispatchSpec

/-! ### M5 on the restricted instance -/

section CoreDefs

variable {D : Ty}

/-- **The full group** the certificates compute for the string `x`: a valid group of at most
`sIn` generators denoting `F(x)`. -/
def M5Full (DV : ℕ → GensData → D.denote → Prop) {N n : ℕ} {gs : GensData}
    (hC : CertSetting (GensData.denote N gs) n) (φ : strGroup hC →* Perm (Fin (N - n)))
    (k sIn : ℕ) (x : StrData) (fs : GensData) (e : D.denote) : Prop :=
  GroupValid DV N fs e ∧ fs.length ≤ sIn ∧ GensData.denote N fs = m5Fmap hC φ k (x.denote N)

/-- The cost of the case decision on the full group `F` (`m5CaseCost`, with the degree program
on the large orbit). -/
def m5DecCost (O : Oracle (groupSig D)) (n N s Bst Borb Bg : ℕ) (Bo' Bs' : ℕ → ℕ)
    (F : GroupData D.denote) : ℕ :=
  m5CaseCost n N Borb (Case2b.degCost N n (m5Cs O n N F).2.length (m5Cs O n N F).2.length s Bst
    Bg (Bo' (m5Cs O n N F).2.length) (Bs' (m5Cs O n N F).2.length))

/-- **The work of M5** besides its sub-calls and children: the two certificates (`certWork`,
and `4` per sub-call for the wrapping without a hint), the two case decisions, the dispatch
(`m5W`) and the projections. -/
def m5CoreWork (O : Oracle (groupSig D)) (n N k s sIn Bgen Blift Bo Bk Bcr Bd : ℕ)
    (G Fx Fy : GroupData D.denote) (wl : ℕ) (β : M5Bounds) (Bst Btr Borb Bkg Bko Bks : ℕ)
    (Bo' Bs' Bt' : ℕ → ℕ) : ℕ :=
  2 * (certCount N n k * 4 +
      certWork N n k sIn Bst Btr Borb Bkg Bko Bks β.Bgk β.BlA β.Bgs β.BF) +
    m5DecCost O n N sIn Bst Borb β.Bg Bo' Bs' Fx + m5DecCost O n N sIn Bst Borb β.Bg Bo' Bs' Fy +
    m5W O n N k s sIn Bgen Blift Bo Bk Bcr Bd G Fx Fy wl β Bst Btr Borb Bkg Bko Bks Bo' Bs' Bt' +
    15

end CoreDefs

section CoreRun

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}
  {sub : HInstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)}

/-- M5's run from the runs of its parts: the two certificates, the two case decisions and the
dispatch, plus `15` for the projections and the case on the labels. -/
theorem m5CoreProg_run {xy : StrData × StrData} {w : WinData} {σd : PermData} {N : ℕ}
    {gs : GensData} {d : D.denote} {n₀ n k : ℕ} {L : LabelData} {st : ℕ × CJData}
    {Fx Fy : GroupData D.denote} {cx cy : ((ℕ × List ℕ) × List (List ℕ)) × Bool}
    {ans : AnswerData D} {c₁ c₂ c₃ c₄ c₅ : ℕ}
    (h₁ : RunsWithin X body (Main.m5CertProg sub n₀ n N k xy.1 (N, gs, d)) Fx c₁)
    (h₂ : RunsWithin X body (Main.m5CertProg sub n₀ n N k xy.2 (N, gs, d)) Fy c₂)
    (h₃ : RunsWithin X body (Main.m5CaseProg n N Fx) cx c₃)
    (h₄ : RunsWithin X body (Main.m5CaseProg n N Fy) cy c₄)
    (h₅ : RunsWithin X body (Main.m5Dispatch sub
      (((xy, w, σd, N, gs, d), n₀, n, some L) : HInstData D) n₀ n L st k xy w (N, gs, d) Fx Fy
      cx cy) ans c₅) :
    RunsWithin X body (Main.m5CoreProg sub
        (((xy, w, σd, N, gs, d), n₀, n, some L) : HInstData D) k st) ans
      (c₁ + c₂ + c₃ + c₄ + c₅ + 15) := by
  apply RunsWithin.mono
  case h =>
    unfold Main.m5CoreProg
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_with RunsWithin.caseOption_some _
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step h₁
    run_step h₂
    run_step h₃
    run_step h₄
    exact h₅
  case hc =>
    simp only [Prim.cost]
    omega

/-- A sub-solver with outputs of at most `s` generators has outputs of at most `s' ≥ s`. -/
theorem m5_hsub_mono_s {P : HInstData D → Prop} {C : ℕ → Option ℕ → ℕ} {s s' : ℕ}
    (hsub : HSubSolves X body DV sub P C s) (hs : s ≤ s') : HSubSolves X body DV sub P C s' :=
  fun J hJ hP => by
    obtain ⟨ans, hrun, hok, hg⟩ := hsub J hJ hP
    exact ⟨ans, hrun, hok, fun c hc => (hg c hc).trans hs⟩

/-- **The certificates' sub-calls are children**: a sub-instance of the step (`StepSubP`),
wrapped without a hint, is a child of the restricted instance with a window of at most
`|W| / 2` points. -/
theorem m5_stepSub_child {xy xy' : StrData × StrData} {w : WinData} {N : ℕ} {gs : GensData}
    {d : D.denote} {n₀ n k sIn : ℕ} {L : LabelData} (h5 : 5 ≤ k) (hnw : n ≤ w.1.length)
    {J : InstData D} (hJ : StepSubP (DV := DV) (GensData.denote N gs) xy' n k sIn J) :
    SizeChild sIn (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D)
        ((J, n₀, n, none) : HInstData D) ∧
      StepChild w.1.length (N - n) (HInstData.winSize ((J, n₀, n, none) : HInstData D),
        HInstData.baseOpt ((J, n₀, n, none) : HInstData D)) := by
  obtain ⟨-, -, hdeg, -, hkw, -, hgl⟩ := hJ
  have h5w := Nat.mul_le_mul_right J.2.1.1.length h5
  refine ⟨⟨rfl, le_rfl, ?_, hgl, SizeChild.lab_none rfl le_rfl rfl⟩, ?_, Or.inr ⟨rfl, ?_⟩⟩
  · change J.degree ≤ max N (2 * n)
    rw [hdeg]
    exact le_max_left _ _
  · change J.2.1.1.length ≤ w.1.length
    omega
  · change 2 * J.2.1.1.length ≤ w.1.length
    omega

end CoreRun

section CoreSpec

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}
  {sub : HInstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)}
  {C : ℕ → Option ℕ → ℕ} {s : ℕ} {xy : StrData × StrData} {w : WinData}
  {N : ℕ} {gs : GensData} {d : D.denote} {n₀ n : ℕ} {L : LabelData} {st : ℕ × CJData}
  {sIn Lg Blift Bgen Bo Bk Bcr Bd : ℕ}

/-- **M5 on the restricted instance.** On a hinted instance `I = (x, y, W, 1 • G)` with labels
`L`, the string positions `[0, n)` all in the window `W`, `G` faithful on the strings
(`CertSetting`) with a giant base action on `m = N − n ≥ 12` points: the certificates compute the
full groups `F(x)`, `F(y)` (`M5Full`), and the answer is correct for `I`. The cost is the
children's (`StepChild |W| m`, factor `m5CF`), `2 · certCount` certificate sub-calls and `m5CK`
comparison sub-calls (Case 3) without a hint on windows of at most `n / k` points, `m5CH`
sub-calls without a hint on windows of at most `|W| / 2` points (Case 2a's pullback), and the
work `m5CoreWork`. The charges that depend on the full groups are assumed for every group
`M5Full` allows. -/
theorem RunsWithin.m5CoreProg (hO : MeetsContractOn DV m5Ops X.O)
    (hPre : ∀ op x, m5Ops op → GroupPre DV op x → X.Pre op x)
    (hI : HInstValid DV (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D))
    {hC : CertSetting (GensData.denote N gs) n} {φ : strGroup hC →* Perm (Fin (N - n))}
    (hφ : IsPhi hC φ)
    (halt : alternatingGroup (Fin (N - n)) ≤ (baseHom _ n hC.base).range)
    (hwS : ∀ u : Fin N, u.val < n → u ∈ w.denote N)
    {k : ℕ} (h5 : 5 ≤ k) (hk : k + 2 ≤ N - n) (h2k : 2 * k ≤ N - n) (hm12 : 12 ≤ N - n)
    {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N sIn G₀) (hgs : gs.length ≤ sIn)
    (hGG₀ : GensData.denote N gs ≤ G₀) {sk : ℕ} (Bk' : BackendBounds X DV k sk ⊤)
    (hsk : sIn ≤ k * (sk + 1)) {sm : ℕ → ℕ} (Bm : ∀ M, BackendBounds X DV M (sm M) ⊤)
    (hsub : HSubSolves X body DV sub
      (fun J => SizeChild (max sIn (supTo sm (w.1.length / 2)))
          (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D) J ∧
        StepChild w.1.length (N - n) (J.winSize, J.baseOpt)) C s)
    (hCmono : ∀ a b, a ≤ b → C a none ≤ C b none) (hs : s ≤ sIn)
    (hB : RDBounds X DV n N sIn Lg Blift Bgen Bo Bk Bcr)
    (hLg : (N - n).factorial * (sIn + 1) ≤ Lg) (hst : st.1 ≠ 2) (β : M5Bounds)
    -- charges on `G`
    (hBgP : X.B.call GroupOp.generate (N - n, gs.map (baseD n N))
      (X.O.run GroupOp.generate (N - n, gs.map (baseD n N))) ≤ β.BgP)
    (hBmem : ∀ g : PermData, g.Valid (N - n) → X.B.call GroupOp.mem (pModel X.O n (N, gs, d), g)
      (X.O.run GroupOp.mem (pModel X.O n (N, gs, d), g)) ≤ β.Bmem)
    (hBkA : X.B.call GroupOp.kernel ((N, gs, d), baseWin n N) (kerModel X.O n (N, gs, d)) ≤
      β.BkA)
    (hBlA : ∀ π : PermData, X.B.call GroupOp.lift ((N, gs, d), (baseWin n N, π))
      (liftModel X.O n (N, gs, d) π) ≤ β.BlA)
    (hBg : ∀ M ≤ N - n, ∀ gs' : GensData, GensData.AllValid M gs' → gs'.length ≤ sIn →
      X.B.call GroupOp.generate (M, gs') (X.O.run GroupOp.generate (M, gs')) ≤ β.Bg)
    (hBgk : ∀ gs' : GensData, GensData.AllValid N gs' →
      gs'.length ≤ k.factorial * (sIn + 1) → GensData.denote N gs' ≤ GensData.denote N gs →
        X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.Bgk)
    (hBgs : ∀ al : List ℕ, al.Nodup → al.length = k → (∀ a ∈ al, a < N - n) → ∀ b₁ b₂,
      X.B.call GroupOp.generate (N, giantGens X.O n (N, gs, d) al b₁ b₂)
        (giantSetStabModel X.O n (N, gs, d) al b₁ b₂) ≤ β.Bgs)
    (hBF : ∀ gs' : GensData, GensData.AllValid N gs' → gs'.length ≤ 2 * sIn →
      GensData.denote N gs' ≤ GensData.denote N gs →
        X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.BF)
    (hBk3 : X.B.call GroupOp.kernel ((N, gs, d), baseWin n N) (kerModel X.O n (N, gs, d)) ≤
      β.Bk3)
    (hBo3 : X.B.call GroupOp.orbits (kerModel X.O n (N, gs, d), w)
      (krOrbits X.O n (N, gs, d) w) ≤ β.Bo3)
    (hBcr3 : X.B.call GroupOp.cosetReps ((N, gs, d), kerModel X.O n (N, gs, d))
      (kerReps X.O n (N, gs, d)) ≤ β.Bcr3)
    (hB3 : ∀ hs : GensData, GensData.AllValid N hs →
      hs.length ≤ (kerReps X.O n (N, gs, d)).length *
        (max s (kerModel X.O n (N, gs, d)).2.1.length + 1) →
      GensData.denote N hs ≤ GensData.denote N gs →
      X.B.call GroupOp.generate (N, hs) (X.O.run GroupOp.generate (N, hs)) ≤ β.Bgen3)
    -- Case 1
    (hBox : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e →
      X.B.call GroupOp.orbits ((N, fs, e), baseWin n N)
        (Giant.baseOrbits X.O n N (N, fs, e)) ≤ β.Box)
    (hBoy : ∀ fs e, M5Full DV hC φ k sIn xy.2 fs e →
      X.B.call GroupOp.orbits ((N, fs, e), baseWin n N)
        (Giant.baseOrbits X.O n N (N, fs, e)) ≤ β.Boy)
    (hBg1₁ : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e → X.B.call GroupOp.generate
      (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
        (partGensD (N - n) (Giant.orbitPartModel X.O n N (N, fs, e))))).map
        (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
      (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
        (partGensD (N - n) (Giant.orbitPartModel X.O n N (N, fs, e)))))) ≤ β.Bg1₁)
    (hD₁ : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e →
      ∀ gs' d' O', RDSet DV n N gs w L (Giant.g1Model X.O n (N, gs, d) (partOps (N - n))
        (Giant.orbitPartModel X.O n N (N, fs, e))).2.1 sIn gs' d' O' →
      RDOrbit X body DV n N w L st sIn Bd gs' d' O')
    -- Case 2a
    (hBg1₂ₐ : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e → X.B.call GroupOp.generate
      (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
        ((setOps (N - n)).gens (m5Cs X.O n N (N, fs, e)).2))).map
        (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
      (Giant.g1Model X.O n (N, gs, d) (setOps (N - n)) (m5Cs X.O n N (N, fs, e)).2) ≤
        β.Bg1₂ₐ)
    (hBgen₂ₐ : ∀ gs' : GensData, GensData.AllValid N gs' → gs'.length ≤ sIn + 1 →
      GensData.denote N gs' ≤ GensData.denote N gs →
      X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.Bgen₂ₐ)
    (hBpb : ∀ gs', GensData.AllValid N gs' →
      gs'.length ≤ (sIn + 1) * (sIn + 1) + sIn + sIn → GensData.denote N gs' ≤ G₀ →
      X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.Bpb)
    (hBgm : ∀ (w' : WinData) (σ' : PermData) (gs' : GensData) (d' : D.denote),
      Giant.PbSubP DV G₀ xy w.1.length sIn (xy, w', σ', N, gs', d') →
      X.B.call GroupOp.generate (w'.1.length, GensData.restrictTo (WinData.pos N w') w'.1 gs')
        (X.O.run GroupOp.generate
          (w'.1.length, GensData.restrictTo (WinData.pos N w') w'.1 gs')) ≤ β.Bgm)
    (hBlift : ∀ (w' : WinData) (σ' : PermData) (gs' : GensData) (d' : D.denote),
      Giant.PbSubP DV G₀ xy w.1.length sIn (xy, w', σ', N, gs', d') → ∀ π' : PermData,
      X.B.call GroupOp.lift ((N, gs', d'), (w', π'))
        (X.O.run GroupOp.lift ((N, gs', d'), (w', π'))) ≤ β.Blift)
    (hBker : ∀ (w' : WinData) (σ' : PermData) (gs' : GensData) (d' : D.denote),
      Giant.PbSubP DV G₀ xy w.1.length sIn (xy, w', σ', N, gs', d') →
      X.B.call GroupOp.kernel ((N, gs', d'), w') (X.O.run GroupOp.kernel ((N, gs', d'), w')) ≤
        β.Bker)
    (hsK : ∀ (w' : WinData) (σ' : PermData) (gs' : GensData) (d' : D.denote),
      Giant.PbSubP DV G₀ xy w.1.length sIn (xy, w', σ', N, gs', d') →
      (X.O.run GroupOp.kernel ((N, gs', d'), w')).2.1.length ≤ β.sK)
    (hBgn : ∀ hs : GensData, GensData.AllValid N hs → hs.length ≤ β.sK + s →
      GensData.denote N hs ≤ G₀ →
      X.B.call GroupOp.generate (N, hs) (X.O.run GroupOp.generate (N, hs)) ≤ β.Bgn)
    -- Case 2b
    (hBg1₂ᵦ : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e → ∀ X₀ : SoJTree.OutD,
      m5Leaf2b X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 = some X₀ →
      X.B.call GroupOp.generate
        (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (Case2b.outGensD (N - n) X₀))).map
          (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
        (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (Case2b.outGensD (N - n) X₀)))) ≤ β.Bg1₂ᵦ)
    (hBgen₂ᵦ : ∀ fs e, M5Full DV hC φ k sIn xy.2 fs e → ∀ gs' : GensData,
      GensData.AllValid N gs' →
      gs'.length ≤ Case2b.c2bR N n (m5Cs X.O n N (N, fs, e)).2.length
        (Case2b.degD X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 - 1)
        (Case2b.sojZ (N - n)) * (sIn + 1) →
      GensData.denote N gs' ≤ GensData.denote N gs →
      X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.Bgen₂ᵦ)
    (hD₂ᵦ : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e → ∀ X₀,
      m5Leaf2b X.O N n (N, fs, e) (m5Cs X.O n N (N, fs, e)).2 = some X₀ →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (Case2b.outOps (N - n)) X₀).2.1 sIn gs' d' O' →
      RDOrbit X body DV n N w L st sIn Bd gs' d' O')
    -- Case 3
    (hBg1₃ : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e → ∀ X₀ : SoJTree.OutD,
      Case3.C3First φ (strOn hC.le (xy.1.denote N)) (N - n) k
        (fixPtsD (m5Os X.O n N (N, fs, e))) X₀ →
      X.B.call GroupOp.generate
        (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (Case2b.outGensD (N - n) X₀))).map
          (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
        (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (Case2b.outGensD (N - n) X₀)))) ≤ β.Bg1₃)
    (hBgen₃ : ∀ fs e, M5Full DV hC φ k sIn xy.2 fs e → ∀ gs' : GensData,
      GensData.AllValid N gs' →
      gs'.length ≤ Case3.c3R k (fixPtsD (m5Os X.O n N (N, fs, e))).length
        (Case2b.sojZ (N - n)) * (sIn + 1) →
      GensData.denote N gs' ≤ GensData.denote N gs →
      X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ β.Bgen₃)
    (hD₃ : ∀ fs e, M5Full DV hC φ k sIn xy.1 fs e → ∀ X₀,
      Case3.C3First φ (strOn hC.le (xy.1.denote N)) (N - n) k
        (fixPtsD (m5Os X.O n N (N, fs, e))) X₀ →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (Case2b.outOps (N - n)) X₀).2.1 sIn gs' d' O' →
      RDOrbit X body DV n N w L st sIn Bd gs' d' O') :
    ∃ (fxs fys : GensData) (ex ey : D.denote) (ans : AnswerData D) (ch : List (ℕ × Option ℕ)),
      M5Full DV hC φ k sIn xy.1 fxs ex ∧ M5Full DV hC φ k sIn xy.2 fys ey ∧
      RunsWithin X body (Main.m5CoreProg sub
          (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D) k st) ans
        ((ch.map fun x => C x.1 x.2).sum + 2 * certCount N n k * C (n / k) none +
          m5CK X.O n N k (N, fxs, ex) (N, fys, ey) * C (n / k) none +
          m5CH X.O n N sIn w.1.length (N, fxs, ex) (N, fys, ey) * C (w.1.length / 2) none +
          m5CoreWork X.O n N k s sIn Bgen Blift Bo Bk Bcr Bd (N, gs, d) (N, fxs, ex)
            (N, fys, ey) w.1.length β B.Bstab B.Btr B.Borb Bk'.Bgen Bk'.Borb Bk'.Bstab
            (fun M => (Bm M).Borb) (fun M => (Bm M).Bstab) (fun M => (Bm M).Btr)) ∧
      InstData.OK (D := D) (xy, w, PermData.one N, N, gs, d) DV ans ∧
      (∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sIn) ∧
      ChildList w.1.length (m5CF X.O n N k (N, fxs, ex) (N, fys, ey))
        (StepChild w.1.length (N - n)) ch := by
  have hOc : MeetsContractOn DV certOps X.O := fun op x h hx =>
    hO op x (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))) hx
  have hPc : ∀ op x, certOps op → GroupPre DV op x → X.Pre op x := fun op x h hx =>
    hPre op x (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))) hx
  have hOcs : MeetsContractOn DV m5CaseOps X.O := fun op x h hx =>
    hO op x (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))) hx
  have hPcs : ∀ op x, m5CaseOps op → GroupPre DV op x → X.Pre op x := fun op x h hx =>
    hPre op x (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))) hx
  have hGv : GroupValid DV N gs d := hI.valid.group
  have hG : IsInvariant (GensData.denote N gs) (baseSet n N) := hC.base
  have hnw : n ≤ w.1.length := m5_n_le_win hI.valid.win hI.le hwS
  have hsub' := m5_hsub_mono_s hsub hs
  have hBgs' : ∀ al ∈ Giant.ksubsD (N - n) k, ∀ b₁ b₂,
      X.B.call GroupOp.generate (N, giantGens X.O n (N, gs, d) al b₁ b₂)
        (giantSetStabModel X.O n (N, gs, d) al b₁ b₂) ≤ β.Bgs := fun al hal => by
    obtain ⟨hp, hl, hlt⟩ := Giant.mem_ksubsD.1 hal
    exact hBgs al (hp.imp Nat.ne_of_lt) hl hlt
  -- the certificates
  obtain ⟨⟨N₁, fxs, ex⟩, hrx, hNx, hvx, hlx, hdx⟩ := RunsWithin.m5CertProg (body := body) hOc
    hPc hφ hGv halt h5 hk h2k xy.1 B hgs hGG₀ Bk' hsk hBgk hBlA hBgs' hBF hsub' hCmono n₀
    (fun J hJ => (m5_stepSub_child h5 hnw hJ).imp_left (·.mono (le_max_left _ _)))
  obtain ⟨⟨N₂, fys, ey⟩, hry, hNy, hvy, hly, hdy⟩ := RunsWithin.m5CertProg (body := body) hOc
    hPc hφ hGv halt h5 hk h2k xy.2 B hgs hGG₀ Bk' hsk hBgk hBlA hBgs' hBF hsub' hCmono n₀
    (fun J hJ => (m5_stepSub_child h5 hnw hJ).imp_left (·.mono (le_max_left _ _)))
  simp only at hNx hNy
  subst N₁ N₂
  have hFx : M5Full DV hC φ k sIn xy.1 fxs ex := ⟨hvx, hlx, hdx⟩
  have hFy : M5Full DV hC φ k sIn xy.2 fys ey := ⟨hvy, hly, hdy⟩
  -- the case decisions
  have hFxG : GensData.denote N fxs ≤ GensData.denote N gs := hFx.2.2 ▸ m5Fmap_le hC φ k _
  have hFyG : GensData.denote N fys ≤ GensData.denote N gs := hFy.2.2 ▸ m5Fmap_le hC φ k _
  have hcx : RunsWithin X body (Main.m5CaseProg n N (N, fxs, ex)) (m5CaseD X.O n N (N, fxs, ex))
      (m5DecCost X.O n N sIn B.Bstab B.Borb β.Bg (fun M => (Bm M).Borb)
        (fun M => (Bm M).Bstab) (N, fxs, ex)) :=
    RunsWithin.m5CaseProg hOcs hPcs B Bm hFx.1 hFx.2.1 (hFxG.trans hGG₀) (hG.mono hFxG) hBg
  have hcy : RunsWithin X body (Main.m5CaseProg n N (N, fys, ey)) (m5CaseD X.O n N (N, fys, ey))
      (m5DecCost X.O n N sIn B.Bstab B.Borb β.Bg (fun M => (Bm M).Borb)
        (fun M => (Bm M).Bstab) (N, fys, ey)) :=
    RunsWithin.m5CaseProg hOcs hPcs B Bm hFy.1 hFy.2.1 (hFyG.trans hGG₀) (hG.mono hFyG) hBg
  -- the dispatch
  obtain ⟨ans, ch, hrun, hok, hg, hch⟩ := RunsWithin.m5Dispatch hO hPre hI hφ halt hwS h5 hk
    hm12 B hgs hGG₀ Bk' hsk Bm hsub hCmono hs hB hLg hst β hFx.1 hFy.1 hFx.2.1 hFy.2.1 hFx.2.2
    hFy.2.2 hBgP hBmem hBkA hBlA hBg hBgk hBgs hBk3 hBo3 hBcr3 hB3 (hBox _ _ hFx)
    (hBoy _ _ hFy) (hBg1₁ _ _ hFx) (hD₁ _ _ hFx) (hBg1₂ₐ _ _ hFx) hBgen₂ₐ
    (fun gs' hv hl h0 => hBpb gs' hv (hl.trans (Nat.add_le_add_left hFx.2.1 _)) h0) hBgm hBlift
    hBker hsK hBgn (hBg1₂ᵦ _ _ hFx) (hBgen₂ᵦ _ _ hFy) (hD₂ᵦ _ _ hFx) (hBg1₃ _ _ hFx)
    (hBgen₃ _ _ hFy) (hD₃ _ _ hFx)
  refine ⟨fxs, fys, ex, ey, ans, ch, hFx, hFy,
    (m5CoreProg_run hrx hry hcx hcy hrun).mono ?_, ?_, hg, hch⟩
  · have e1 := fullCost_le_count N n k sIn B.Bstab B.Btr B.Borb Bk'.Bgen Bk'.Borb Bk'.Bstab
      β.Bgk (C (n / k) none + 4) β.BlA β.Bgs β.BF
    unfold m5CoreWork
    linarith
  · show AnsOK DV N (w.denote N) (PermData.denote N (PermData.one N)) (GensData.denote N gs)
      (xy.1.denote N) (xy.2.denote N) ans
    rw [PermData.denote_one]
    exact hok

end CoreSpec

/-! ### Well-formedness -/

section Wf

variable {D : Ty} {rec : Ty × Ty} {var₁ var₂ : Ty → Type} {r : Bool} {Γ : WfCtx var₁ var₂}

local macro "m5_mem" : tactic =>
  `(tactic| repeat (first | exact List.mem_cons_self | assumption | apply List.mem_cons_of_mem))

theorem wf_fixPtsProg {S : Signature} {bos₁ : var₁ (.list (.list .nat))}
    {bos₂ : var₂ (.list (.list .nat))} (hb : ⟨.list (.list .nat), bos₁, bos₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (fixPtsProg bos₁) (fixPtsProg bos₂) := by
  unfold fixPtsProg
  refine .bind (Toolkit.wf_filterList hb fun Γ' _ o₁ o₂ ho => ?_) fun _ _ => ?_
  · refine .bind (.prim _ (.cons ho .nil)) fun _ _ => ?_
    refine .bind (.prim _ .nil) fun _ _ => ?_
    exact .prim _ (.cons (by m5_mem) (.cons (List.Mem.head _) .nil))
  · refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
    refine .bind (.prim _ .nil) fun _ _ => ?_
    exact .foldList (by m5_mem) (List.Mem.head _) fun _ _ _ _ =>
      .prim _ (.cons (by m5_mem) (.cons (List.Mem.head _) .nil))

theorem wf_m5Dispatch {sub₁ : var₁ (hinstTy D) → Prog (groupSig D) rec var₁ (Ty.answer D)}
    {sub₂ : var₂ (hinstTy D) → Prog (groupSig D) rec var₂ (Ty.answer D)}
    (hsub : WfFun r Γ sub₁ sub₂) {I₁ : var₁ (hinstTy D)} {I₂ : var₂ (hinstTy D)}
    {n₀₁ n₁ k₁ : var₁ .nat} {n₀₂ n₂ k₂ : var₂ .nat}
    {L₁ : var₁ (.array (.list .nat))} {L₂ : var₂ (.array (.list .nat))} {st₁ : var₁ stTy}
    {st₂ : var₂ stTy} {xy₁ : var₁ Ty.strs} {xy₂ : var₂ Ty.strs} {w₁ : var₁ Ty.win}
    {w₂ : var₂ Ty.win} {G₁ Fx₁ Fy₁ : var₁ (Ty.group D)} {G₂ Fx₂ Fy₂ : var₂ (Ty.group D)}
    {cx₁ cy₁ : var₁ m5CaseTy} {cx₂ cy₂ : var₂ m5CaseTy}
    (hI : ⟨hinstTy D, I₁, I₂⟩ ∈ Γ) (hn₀ : ⟨.nat, n₀₁, n₀₂⟩ ∈ Γ) (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ)
    (hL : ⟨.array (.list .nat), L₁, L₂⟩ ∈ Γ) (hst : ⟨stTy, st₁, st₂⟩ ∈ Γ)
    (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ) (hxy : ⟨Ty.strs, xy₁, xy₂⟩ ∈ Γ) (hw : ⟨Ty.win, w₁, w₂⟩ ∈ Γ)
    (hG : ⟨Ty.group D, G₁, G₂⟩ ∈ Γ) (hFx : ⟨Ty.group D, Fx₁, Fx₂⟩ ∈ Γ)
    (hFy : ⟨Ty.group D, Fy₁, Fy₂⟩ ∈ Γ) (hcx : ⟨m5CaseTy, cx₁, cx₂⟩ ∈ Γ)
    (hcy : ⟨m5CaseTy, cy₁, cy₂⟩ ∈ Γ) :
    Prog.Wf r Γ (m5Dispatch sub₁ I₁ n₀₁ n₁ L₁ st₁ k₁ xy₁ w₁ G₁ Fx₁ Fy₁ cx₁ cy₁)
      (m5Dispatch sub₂ I₂ n₀₂ n₂ L₂ st₂ k₂ xy₂ w₂ G₂ Fx₂ Fy₂ cx₂ cy₂) := by
  unfold m5Dispatch
  refine .bind (.prim _ (.cons hcx .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by m5_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by m5_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by m5_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by m5_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by m5_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by m5_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by m5_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by m5_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by m5_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by m5_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by m5_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ .nil) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by m5_mem) (.cons (List.Mem.head _) .nil))) fun _ _ => ?_
  refine .ite (List.Mem.head _) ?_ ?_
  · exact wf_m5Case1Prog (hsub.mono fun y hy => by m5_mem) (by m5_mem) (by m5_mem) (by m5_mem)
      (by m5_mem) (by m5_mem) (by m5_mem) (by m5_mem) (by m5_mem) (by m5_mem)
  refine .bind (.prim _ .nil) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by m5_mem) (.cons (List.Mem.head _) .nil))) fun _ _ => ?_
  refine .ite (List.Mem.head _) ?_ ?_
  · refine .bind (.prim _ (.cons (by m5_mem) (.cons (by m5_mem) .nil))) fun _ _ => ?_
    refine .bind (.prim _ (.cons (by m5_mem) (.cons (by m5_mem) .nil))) fun _ _ => ?_
    refine .bind (.prim _ (.cons (by m5_mem) .nil)) fun _ _ => ?_
    refine .bind (.prim _ (.cons (by m5_mem) .nil)) fun _ _ => ?_
    refine .bind (.prim _ (.cons (by m5_mem) (.cons (List.Mem.head _) .nil))) fun _ _ => ?_
    refine .bind (.prim _ (.cons (by m5_mem) (.cons (List.Mem.head _) .nil))) fun _ _ => ?_
    refine .bind (.prim _ (.cons (by m5_mem) (.cons (List.Mem.head _) .nil))) fun _ _ => ?_
    refine .ite (List.Mem.head _) (.ite (by m5_mem) ?_ ?_) (.prim _ .nil)
    · refine .bind (.prim _ (.cons (by m5_mem) .nil)) fun _ _ => ?_
      refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
      exact wf_m5Case2aProg (hsub.mono fun y hy => by m5_mem) (by m5_mem) (by m5_mem)
        (by m5_mem) (by m5_mem) (by m5_mem) (by m5_mem) (by m5_mem) (List.Mem.head _)
    · exact wf_m5Case2bProg (hsub.mono fun y hy => by m5_mem) (by m5_mem) (by m5_mem)
        (by m5_mem) (by m5_mem) (by m5_mem) (by m5_mem) (by m5_mem) (by m5_mem) (by m5_mem)
        (by m5_mem) (by m5_mem)
  · refine .bind (wf_fixPtsProg (by m5_mem)) fun _ _ => ?_
    refine .bind (wf_fixPtsProg (by m5_mem)) fun _ _ => ?_
    exact wf_m5Case3Prog (hsub.mono fun y hy => by m5_mem) (by m5_mem) (by m5_mem) (by m5_mem)
      (by m5_mem) (by m5_mem) (by m5_mem) (by m5_mem) (by m5_mem) (by m5_mem)
      (List.Mem.tail _ (List.Mem.head _)) (List.Mem.head _)

theorem wf_m5CoreProg {sub₁ : var₁ (hinstTy D) → Prog (groupSig D) rec var₁ (Ty.answer D)}
    {sub₂ : var₂ (hinstTy D) → Prog (groupSig D) rec var₂ (Ty.answer D)}
    (hsub : WfFun r Γ sub₁ sub₂) {I₁ : var₁ (hinstTy D)} {I₂ : var₂ (hinstTy D)}
    {k₁ : var₁ .nat} {k₂ : var₂ .nat} {st₁ : var₁ stTy} {st₂ : var₂ stTy}
    (hI : ⟨hinstTy D, I₁, I₂⟩ ∈ Γ) (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ) (hst : ⟨stTy, st₁, st₂⟩ ∈ Γ) :
    Prog.Wf r Γ (m5CoreProg sub₁ I₁ k₁ st₁) (m5CoreProg sub₂ I₂ k₂ st₂) := by
  unfold m5CoreProg
  refine .bind (.prim _ (.cons hI .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by m5_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by m5_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by m5_mem) .nil)) fun _ _ => ?_
  refine .caseOption (List.Mem.head _) (.prim _ .nil) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by m5_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by m5_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by m5_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by m5_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by m5_mem) .nil)) fun _ _ => ?_
  refine .bind (wf_m5CertProg (hsub.mono fun y hy => by m5_mem) (by m5_mem) (by m5_mem)
    (by m5_mem) (by m5_mem) (by m5_mem) (by m5_mem)) fun _ _ => ?_
  refine .bind (wf_m5CertProg (hsub.mono fun y hy => by m5_mem) (by m5_mem) (by m5_mem)
    (by m5_mem) (by m5_mem) (by m5_mem) (by m5_mem)) fun _ _ => ?_
  refine .bind (wf_m5CaseProg (by m5_mem) (by m5_mem) (by m5_mem)) fun _ _ => ?_
  refine .bind (wf_m5CaseProg (by m5_mem) (by m5_mem) (by m5_mem)) fun _ _ => ?_
  exact wf_m5Dispatch (hsub.mono fun y hy => by m5_mem) (by m5_mem) (by m5_mem) (by m5_mem)
    (by m5_mem) (by m5_mem) (by m5_mem) (by m5_mem) (by m5_mem) (by m5_mem) (by m5_mem)
    (by m5_mem) (List.Mem.tail _ (List.Mem.head _)) (List.Mem.head _)

end Wf

end GraphIso.Main
