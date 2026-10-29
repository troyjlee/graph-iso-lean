module

public import GraphIso.Case2b.ChoiceProg
public import GraphIso.Case2b.OutOps
public import GraphIso.Case2b.Tree
public import GraphIso.Case2b.Link
public import GraphIso.Toolkit.Transitivity
public import GraphIso.Align.AlignProg
public import GraphIso.Giant.Case2a
public import GraphIso.Solver.Sims
public import GraphIso.Solver.Luks

/-!
# Case 2b: the program

Stage 14h, item 3 (`PLAN-14.md` §12). Case 2b of the giant macro-step: the full group `F` has
an orbit `Φ` of more than half of the base on which `ψ(F)` is not a giant.

* **The degree** (`degProg`, model `degD`): `F` restricted to the positions of `Φ`
  (`resProg` with no individualized points), generated at degree `|Φ|`, and the toolkit's
  degree program with cap `|Φ|`. `degD_spec`: with `TupTrans P Φ k` (`P` moves any `k` points
  of `Φ` to any other `k`, the form of `case2bHyp_of_degree`), `d = degD` satisfies
  `TupTrans d` and, if `d < |Φ|`, not `TupTrans (d + 1)`. The bridge is
  `cp2_multTrans_iff` (multiple transitivity through a numbering) with `cp2_restrict_iff` (the
  group of restricted generators, elementwise). `case2bHyp_degD`: for an orbit on which `ψ(F)`
  does not move any `|Φ| - 2` points as it likes, `1 ≤ d` and `Case2bHyp ψ(F) Φ d`.
  `cp2_degD_eq`: the degree is canonical (conjugate actions, translated orbits).
* **Uniform costs** (`RunsWithin.choiceProg_le`, `allLeavesProg_le`, `firstLeafProg_le`): every
  choice costs at most `chCost`, given the `soj` sizes (`sojSz ≤ Z`) and the bounded-list
  generation charge `Bg`; the leaves have size at most `leafB (N - n)` (`outSize_extD_le`) and
  number at most `c2bR = |Φ|^j (N - n)² (Z + 1)` (`length_allLeavesD_le`).
* **The program** (`case2bProg`): the degrees for `x` and `y`; if they differ there is no
  isomorphism; otherwise, with `j = d - 1`, the first leaf for `x` (`firstLeafProg`), all leaves
  for `y` (`allLeavesProg`), and `alignProg` with `outOps` (`outGensProg`, `outIsoProg`).
* `RunsWithin.case2bProg`: the answer is correct (`AnsOK … 1 G x y`) under `SubSolves` for
  the aligned cosets, at the explicit cost `c2bCost`, given the facts the model provides as
  hypotheses (valid leaves, the alignment hypothesis when the degrees agree, no isomorphism when
  they differ). `RunsWithin.case2bProg_canonical` discharges them for canonical `F` and `Φ`
  (`largeOrbit_canonical`, `cp2_range_conj`, `case2bTree_relabel'`, and the tree facts of
  `Link.lean`). `RunsWithin.case2bProg_canonical'` also takes `Z = sojZ (N - n)` (`sojSz_le`)
  and the first leaf from the tree (`firstLeafD_ne_none`).
* `c2b_ss_charges`: the two generation charges hold for the Schreier–Sims backend, with bounded
  generator lists.
* `degD_le_T` (stage 14j-6b-1): under `TransitivityBound T`, the computed degree on an orbit on
  which `ψ(F)` is not a giant is at most `T |Φ|`.
-/

@[expose] public section

namespace GraphIso.Case2b

open Equiv MulAction Pointwise GraphIso GraphIso.Cost GraphIso.Programs GraphIso.SplitJohnson
  GraphIso.SoJProg GraphIso.SoJTree GraphIso.Toolkit GraphIso.Sims GraphIso.Solver GraphIso.Align

/-! ### Multiple transitivity on a subset -/

section Trans

/-- `P` carries any `k` distinct points of `Φ` to any `k` distinct points of `Φ`: the form of
the hypotheses of `case2bHyp_of_degree`. -/
def TupTrans {Γ : Type*} (P : Subgroup (Perm Γ)) (Φ : Finset Γ) (k : ℕ) : Prop :=
  ∀ T T' : Fin k → Γ, Function.Injective T → Function.Injective T' → (∀ i, T i ∈ Φ) →
    (∀ i, T' i ∈ Φ) → ∃ g ∈ P, ∀ i, g (T i) = T' i

variable {Γ : Type*} {M : ℕ} {P : Subgroup (Perm Γ)} {Q : Subgroup (Perm (Fin M))}
  {e : Fin M → Γ} {Φ : Finset Γ}

/-- **Multiple transitivity through a numbering.** If `Q` is the action of `P` on `Φ`, numbered
by `e`, then `Q` is `k`-transitive exactly when `P` moves any `k` points of `Φ` to any other
`k`. -/
theorem cp2_multTrans_iff (he : Function.Injective e) (hΦ : ∀ v, v ∈ Φ ↔ ∃ j, e j = v)
    (h1 : ∀ p ∈ P, ∃ q ∈ Q, ∀ j, p (e j) = e (q j))
    (h2 : ∀ q ∈ Q, ∃ p ∈ P, ∀ j, p (e j) = e (q j)) (k : ℕ) :
    IsMultiplyPretransitive Q (Fin M) k ↔ TupTrans P Φ k := by
  rw [isMultiplyPretransitive_iff]
  constructor
  · intro h T T' hT hT' hTΦ hT'Φ
    choose x hx using fun i => (hΦ (T i)).1 (hTΦ i)
    choose y hy using fun i => (hΦ (T' i)).1 (hT'Φ i)
    have hxi : Function.Injective x := fun i i' hii => hT (by rw [← hx, ← hx i', hii])
    have hyi : Function.Injective y := fun i i' hii => hT' (by rw [← hy, ← hy i', hii])
    obtain ⟨⟨q, hq⟩, hqxy⟩ := h ⟨x, hxi⟩ ⟨y, hyi⟩
    obtain ⟨p, hp, hpe⟩ := h2 q hq
    refine ⟨p, hp, fun i => ?_⟩
    have hqi : q (x i) = y i := congrArg (fun z : Fin k ↪ Fin M => z i) hqxy
    rw [← hx, hpe, hqi, hy]
  · intro h x y
    obtain ⟨p, hp, hpT⟩ := h (fun i => e (x i)) (fun i => e (y i)) (he.comp x.injective)
      (he.comp y.injective) (fun i => (hΦ _).2 ⟨_, rfl⟩) (fun i => (hΦ _).2 ⟨_, rfl⟩)
    obtain ⟨q, hq, hqe⟩ := h1 p hp
    refine ⟨⟨q, hq⟩, Function.Embedding.ext fun i => he ?_⟩
    show e (q (x i)) = e (y i)
    rw [← hqe, hpT]

/-- With the identity numbering. -/
theorem cp2_multTrans_univ {P : Subgroup (Perm (Fin M))} (k : ℕ) :
    IsMultiplyPretransitive P (Fin M) k ↔ TupTrans P (Finset.univ : Finset (Fin M)) k :=
  cp2_multTrans_iff (e := id) Function.injective_id (fun v => by simp)
    (fun p hp => ⟨p, hp, fun _ => rfl⟩) (fun q hq => ⟨q, hq, fun _ => rfl⟩) k

/-- The base action at `n = 0` is the group itself. -/
theorem cp2_multTrans_baseHom_zero {R : Subgroup (Perm (Fin M))}
    (hinv : IsInvariant R (baseSet 0 M)) (k : ℕ) :
    IsMultiplyPretransitive (baseHom R 0 hinv).range (Fin (M - 0)) k ↔
      IsMultiplyPretransitive R (Fin M) k := by
  rw [cp2_multTrans_univ (P := R)]
  refine cp2_multTrans_iff (P := R) (Q := (baseHom R 0 hinv).range)
    (e := fun j : Fin (M - 0) => (⟨j.val, by omega⟩ : Fin M))
    (fun i j h => Fin.ext (by simpa using congrArg Fin.val h)) (fun v => ?_) ?_ ?_ k
  · simp only [Finset.mem_univ, true_iff]
    exact ⟨⟨v.val, by omega⟩, rfl⟩
  · intro p hp
    refine ⟨baseHom R 0 hinv ⟨p, hp⟩, ⟨_, rfl⟩, fun j => Fin.ext ?_⟩
    have := congrArg Fin.val (baseHom_apply (hG := hinv) ⟨p, hp⟩ j)
    simp only [basePos, Nat.zero_add] at this
    rw [this]
  · rintro _ ⟨⟨p, hp⟩, rfl⟩
    refine ⟨p, hp, fun j => Fin.ext ?_⟩
    have := congrArg Fin.val (baseHom_apply (hG := hinv) ⟨p, hp⟩ j)
    simp only [basePos, Nat.zero_add] at this
    rw [this]

end Trans

/-! ### The restricted group, elementwise -/

section Restrict

/-- **The group generated by restricted generators**: its elements are the actions on the window
of the elements of `⟨gs⟩`. -/
theorem cp2_restrict_iff {N M : ℕ} {w : WinData} (hw : w.Valid N) {gs : GensData}
    (hgs : GensData.AllValid N gs) (hW : IsInvariant (GensData.denote N gs) (w.denote N))
    (hM : w.1.length = M) :
    (∀ f ∈ GensData.denote N gs, ∃ r ∈ GensData.denote M
        (GensData.restrictTo (WinData.pos N w) w.1 gs),
      ∀ (j : Fin M) (u : Fin N), u.val = w.1.getD j 0 → (f u).val = w.1.getD (r j) 0) ∧
    (∀ r ∈ GensData.denote M (GensData.restrictTo (WinData.pos N w) w.1 gs),
      ∃ f ∈ GensData.denote N gs,
        ∀ (j : Fin M) (u : Fin N), u.val = w.1.getD j 0 → (f u).val = w.1.getD (r j) 0) := by
  subst hM
  rw [GensData.denote_restrictTo hW hw hgs]
  have key : ∀ (f : Perm (Fin N)) (hf : f ∈ GensData.denote N gs) (j : Fin w.1.length)
      (u : Fin N), u.val = w.1.getD j 0 →
        (f u).val = w.1.getD (GraphIso.restrictHom hW (WinData.reindex hw) ⟨f, hf⟩ j) 0 := by
    intro f hf j u hu
    have h := GraphIso.restrictHom_apply hW (WinData.reindex hw) ⟨f, hf⟩ j
    have hu' : u = (WinData.reindex hw j : Fin N) := Fin.ext (by rw [hu, WinData.reindex_val])
    rw [hu', ← WinData.reindex_val hw, ← h]
  refine ⟨fun f hf => ⟨_, ⟨⟨f, hf⟩, rfl⟩, key f hf⟩, ?_⟩
  rintro _ ⟨⟨f, hf⟩, rfl⟩
  exact ⟨f, hf, key f hf⟩

/-- **The restricted group, through the numbering of the list**: the group generated by the
restrictions of `gs` to the positions of `ΦS` is `k`-transitive exactly when `ψ(⟨gs⟩)` moves
any `k` points of `ΦS` to any other `k`. -/
theorem cp2_resTrans_iff {N n M : ℕ} {gs : GensData} (hgs : GensData.AllValid N gs)
    (hF : IsInvariant (GensData.denote N gs) (baseSet n N)) {ΦS : List ℕ} (hn : ΦS.Nodup)
    (hl : ∀ i ∈ ΦS, i < N - n) (hW : IsInvariant (GensData.denote N gs) {u | u.val ∈ ptsD n ΦS})
    (hM : ΦS.length = M) {R : Subgroup (Perm (Fin M))}
    (hR : R = GensData.denote M (rgensD N n gs ΦS)) (k : ℕ) :
    IsMultiplyPretransitive R (Fin M) k ↔
      TupTrans (baseHom _ n hF).range (setOf (N - n) ΦS) k := by
  subst hM hR
  have hwnd : (ptsD n ΦS).Nodup := hn.map fun x y h => by omega
  have hwlt : ∀ u ∈ ptsD n ΦS, u < N := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hu
    have := hl v hv
    omega
  have hwv := WinData.valid_ofPoints hwnd hwlt
  obtain ⟨hr1, hr2⟩ := cp2_restrict_iff (M := ΦS.length) hwv hgs hW (by simp [ptsD])
  have hget : ∀ j : Fin ΦS.length,
      (WinData.ofPoints N (ptsD n ΦS)).1.getD j 0 = n + ΦS[j] := by
    intro j
    simp [ptsD, List.getD_eq_getElem?_getD]
  set e : Fin ΦS.length → Fin (N - n) := fun j => ⟨ΦS[j], hl _ (List.getElem_mem _)⟩ with he
  have hpos : ∀ j, (basePos (e j) : Fin N).val = n + ΦS[j] := fun j => rfl
  -- an element of `F` acting on the positions as `r`
  have hact : ∀ (f : Perm (Fin N)) (hf : f ∈ GensData.denote N gs) (r : Perm (Fin ΦS.length)),
      (∀ (j : Fin ΦS.length) (u : Fin N), u.val = (WinData.ofPoints N (ptsD n ΦS)).1.getD j 0 →
        (f u).val = (WinData.ofPoints N (ptsD n ΦS)).1.getD (r j) 0) →
      ∀ j, baseHom _ n hF ⟨f, hf⟩ (e j) = e (r j) := by
    intro f hf r hfr j
    have h1 := baseHom_apply (hG := hF) ⟨f, hf⟩ (e j)
    have h2 := hfr j (basePos (e j)) (by rw [hpos, hget])
    rw [hget] at h2
    apply Fin.ext
    have h3 : n + (baseHom _ n hF ⟨f, hf⟩ (e j)).val = (f (basePos (e j))).val :=
      congrArg Fin.val h1
    show (baseHom _ n hF ⟨f, hf⟩ (e j)).val = ΦS[r j]
    omega
  refine cp2_multTrans_iff (e := e) (fun i j h => Fin.ext ((List.Nodup.getElem_inj_iff hn).1
    (congrArg Fin.val h))) (fun v => ?_) ?_ ?_ k
  · rw [mem_setOf, List.mem_iff_getElem]
    constructor
    · rintro ⟨i, hi, hv⟩
      exact ⟨⟨i, hi⟩, Fin.ext hv⟩
    · rintro ⟨j, rfl⟩
      exact ⟨j.val, j.isLt, rfl⟩
  · rintro _ ⟨⟨f, hf⟩, rfl⟩
    obtain ⟨r, hr, hfr⟩ := hr1 f hf
    exact ⟨r, hr, hact f hf r hfr⟩
  · intro r hr
    obtain ⟨f, hf, hfr⟩ := hr2 r hr
    exact ⟨_, ⟨⟨f, hf⟩, rfl⟩, hact f hf r hfr⟩

end Restrict

/-! ### Monotonicity, conjugation and uniqueness of the degree -/

section TransFacts

variable {Γ : Type*}

/-- **Fewer points**: if `P` moves any `k'` points of `Φ` (`k' ≤ |Φ|`), it moves any `k ≤ k'`
points (`isMultiplyPretransitive_of_le` on the action on `Φ`). -/
theorem cp2_tupTrans_mono [DecidableEq Γ] {P : Subgroup (Perm Γ)} {Φ : Finset Γ}
    (hpres : ∀ g ∈ P, ∀ x ∈ Φ, g x ∈ Φ) {k k' : ℕ} (h : TupTrans P Φ k') (hk : k ≤ k')
    (hk' : k' ≤ Φ.card) : TupTrans P Φ k := by
  let e : Fin Φ.card ↪ Γ := ⟨fun j => (Φ.equivFin.symm j : Γ), fun i j hij =>
    Φ.equivFin.symm.injective (Subtype.ext hij)⟩
  have hΦ : ∀ v, v ∈ Φ ↔ ∃ j, e j = v := fun v =>
    ⟨fun hv => ⟨Φ.equivFin ⟨v, hv⟩, show (Φ.equivFin.symm (Φ.equivFin ⟨v, hv⟩) : Γ) = v by
      simp⟩, fun ⟨j, hj⟩ => hj ▸ (Φ.equivFin.symm j).2⟩
  have hmaps : ∀ g ∈ P, ∀ i, ∃ j, g (e i) = e j := fun g hg i =>
    ((hΦ _).1 (hpres g hg _ ((hΦ _).2 ⟨i, rfl⟩))).imp fun _ h => h.symm
  have hiff := fun k => cp2_multTrans_iff (P := P) (Q := fixGroup P ∅ e) (Φ := Φ) e.injective hΦ
    (fun p hp => by
      obtain ⟨q, hq, hqe⟩ := cb_realize (S := ∅) hp (fun s hs => absurd hs (Finset.notMem_empty s))
        (hmaps p hp)
      exact ⟨q, hq, hqe⟩)
    (fun q hq => by
      obtain ⟨p, hp, -, hpe⟩ := hq
      exact ⟨p, hp, hpe⟩) k
  rw [← hiff] at h ⊢
  have := h
  exact isMultiplyPretransitive_of_le hk (by simpa using hk')

/-- **Conjugation**: the condition moves with `σ`. -/
theorem cp2_tupTrans_conj (σ : Perm Γ) {P P' : Subgroup (Perm Γ)}
    (hP : ∀ g, g ∈ P' ↔ σ⁻¹ * g * σ ∈ P) {Φ Φ' : Finset Γ} (hΦ : ∀ v, v ∈ Φ' ↔ σ⁻¹ v ∈ Φ)
    (k : ℕ) : TupTrans P' Φ' k ↔ TupTrans P Φ k := by
  constructor
  · intro h T T' hT hT' hTΦ hT'Φ
    obtain ⟨g, hg, hgT⟩ := h (fun i => σ (T i)) (fun i => σ (T' i)) (σ.injective.comp hT)
      (σ.injective.comp hT') (fun i => (hΦ _).2 (by simpa using hTΦ i))
      (fun i => (hΦ _).2 (by simpa using hT'Φ i))
    refine ⟨σ⁻¹ * g * σ, (hP g).1 hg, fun i => ?_⟩
    simp [Perm.mul_apply, hgT]
  · intro h T T' hT hT' hTΦ hT'Φ
    obtain ⟨g, hg, hgT⟩ := h (fun i => σ⁻¹ (T i)) (fun i => σ⁻¹ (T' i))
      (σ⁻¹.injective.comp hT) (σ⁻¹.injective.comp hT') (fun i => (hΦ _).1 (hTΦ i))
      (fun i => (hΦ _).1 (hT'Φ i))
    refine ⟨σ * g * σ⁻¹, (hP _).2 (by simpa [mul_assoc] using hg), fun i => ?_⟩
    rw [Perm.mul_apply, Perm.mul_apply, hgT i, perm_apply_inv_self]

/-- **The degree is determined by the condition**: two cut-off degrees of transitivity of
equivalent monotone conditions coincide. -/
theorem cp2_deg_unique {T₁ T₂ : ℕ → Prop} {L d₁ d₂ : ℕ} (hT : ∀ k, T₁ k ↔ T₂ k)
    (hmono : ∀ k k', T₂ k' → k ≤ k' → k' ≤ L → T₂ k) (h₁ : d₁ ≤ L) (h₂ : d₂ ≤ L)
    (ht₁ : T₁ d₁) (hn₁ : d₁ < L → ¬ T₁ (d₁ + 1)) (ht₂ : T₂ d₂)
    (hn₂ : d₂ < L → ¬ T₂ (d₂ + 1)) : d₁ = d₂ := by
  rcases lt_trichotomy d₁ d₂ with h | h | h
  · exact absurd ((hT _).2 (hmono _ _ ht₂ h h₂)) (hn₁ (by omega))
  · exact h
  · exact absurd (hmono _ _ ((hT _).1 ht₁) h h₁) (hn₂ (by omega))

end TransFacts

/-! ### The degree of transitivity on `Φ` -/

section DegreeProg

variable {D : Ty} {rec : Ty × Ty} {var : Ty → Type}

/-- **The degree of transitivity of `ψ(F)` on `Φ`**: `F` restricted to the positions of `Φ`
(`resProg` with no individualized points), generated at degree `|Φ|`, and the degree program
with cap `|Φ|`. -/
def degProg (N n : var .nat) (F : var (Ty.group D)) (Φ : var (.list .nat)) :
    Prog (groupSig D) rec var .nat :=
  .bind (.op2 .sub N n) fun m => .bind (.op0 .nil) fun nil =>
  .bind (phiSProg m Φ nil) fun ΦS => .bind (.op1 .length ΦS) fun m' =>
  .bind (resProg N n F ΦS nil m') fun R => .bind (.op0 (.natLit 0)) fun z =>
  Toolkit.degreeProg z m' R

end DegreeProg

/-- The model of `degProg`. -/
def degD {D : Ty} (O : Oracle (groupSig D)) (N n : ℕ) (F : GroupData D.denote) (Φ : List ℕ) :
    ℕ :=
  degreeModel O 0 (phiSD (N - n) Φ []).length (resModel O N n F Φ [])

/-- The cost of `degProg`. -/
def degCost (N n nΦ m' s Bstab Bg Borb' Bstab' : ℕ) : ℕ :=
  1 + 1 + ((N - n) * (3 * nΦ + 9) + (N - n) + 4) + (m' + 1) + resCost N 0 m' s Bstab Bg + 1 +
    degreeCost m' m' Borb' Bstab'

section DegreeSpec

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}

/-- The operations of `degProg`. -/
def degOps (op : GroupOp) : Prop := choiceOps op ∨ degreeOps op

theorem cp2_choiceOps_of_deg (hO : MeetsContractOn DV degOps X.O) :
    MeetsContractOn DV choiceOps X.O := fun op x h hp => hO op x (Or.inl h) hp

theorem length_phiSD_nil {m : ℕ} {Φ : List ℕ} (hn : Φ.Nodup) (hl : ∀ i ∈ Φ, i < m) :
    (phiSD m Φ []).length = Φ.length :=
  ((List.perm_ext_iff_of_nodup (phiSD_nodup _ _ _) hn).2 fun v => by
    rw [mem_phiSD]
    exact ⟨fun h => h.2.1, fun h => ⟨hl v h, h, List.not_mem_nil⟩⟩).length_eq

theorem setOf_phiSD_nil {m : ℕ} {Φ : List ℕ} : setOf m (phiSD m Φ []) = setOf m Φ := by
  ext v
  rw [mem_setOf, mem_setOf, mem_phiSD]
  exact ⟨fun h => h.2.1, fun h => ⟨v.isLt, h, List.not_mem_nil⟩⟩

/-- **The cost of the degree program.** -/
theorem RunsWithin.degProg (hO : MeetsContractOn DV degOps X.O)
    (hPre : ∀ op x, degOps op → GroupPre DV op x → X.Pre op x)
    {N n s : ℕ} {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N s G₀)
    {gs : GensData} {d : D.denote} (hGv : GroupValid DV N gs d) (hs : gs.length ≤ s)
    (hG₀ : GensData.denote N gs ≤ G₀) {Φ : List ℕ}
    (hΦ : IsInvariant (GensData.denote N gs) {u | u.val ∈ ptsD n Φ}) {sm : ℕ}
    (Bm : BackendBounds X DV (phiSD (N - n) Φ []).length sm ⊤) {Bg : ℕ}
    (hBg : X.B.call GroupOp.generate ((phiSD (N - n) Φ []).length,
        rgensD N n gs (phiSD (N - n) Φ [])) (resModel X.O N n (N, gs, d) Φ []) ≤ Bg) :
    RunsWithin X body (Case2b.degProg N n (N, gs, d) Φ) (degD X.O N n (N, gs, d) Φ)
      (degCost N n Φ.length (phiSD (N - n) Φ []).length s B.Bstab Bg Bm.Borb Bm.Bstab) := by
  obtain ⟨hrun, hdeg, hRv, hrv⟩ := RunsWithin.resProg (X := X) (body := body)
    (cp2_choiceOps_of_deg hO) (fun op x h hp => hPre op x (Or.inl h) hp) B hGv hs hG₀ hΦ
    (Sl := []) (fun v hv => absurd hv List.not_mem_nil) hBg
  have hgen : (resModel X.O N n (N, gs, d) Φ []).2.1.length ≤ sm := Bm.genOut _ hrv le_top
  unfold degD
  generalize resModel X.O N n (N, gs, d) Φ [] = R at hrun hdeg hRv hgen ⊢
  obtain ⟨M, gsR, eR⟩ := R
  change M = _ at hdeg
  subst hdeg
  have hinv : IsInvariant (GensData.denote (phiSD (N - n) Φ []).length gsR)
      (baseSet 0 (phiSD (N - n) Φ []).length) := fun _ _ u _ => Nat.zero_le _
  have hd := RunsWithin.degreeProg (X := X) (body := body) (cap := (phiSD (N - n) Φ []).length)
    (fun op x h hp => hO op x (Or.inr h) hp) (fun op x h hp => hPre op x (Or.inr h) hp) Bm hRv
    hgen le_top hinv (Nat.zero_le _)
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.phiSProg (N - n) Φ [])
    run_step (RunsWithin.prim _ _)
    run_step hrun
    run_step (RunsWithin.prim _ _)
    exact hd
  case hc =>
    simp only [Prim.cost, Args.head, degCost, List.length_nil, Nat.mul_zero, Nat.add_zero]
    omega

/-- **The meaning of the degree program**: `d = degD` is at most `|Φ|`, `ψ(F)` moves any `d`
points of `Φ` to any other `d`, and, if `d < |Φ|`, not so for `d + 1` points. -/
theorem degD_spec (hO : MeetsContractOn DV degOps X.O)
    (hPre : ∀ op x, degOps op → GroupPre DV op x → X.Pre op x)
    {N n s : ℕ} {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N s G₀)
    {gs : GensData} {d : D.denote} (hGv : GroupValid DV N gs d) (hs : gs.length ≤ s)
    (hG₀ : GensData.denote N gs ≤ G₀) (hF : IsInvariant (GensData.denote N gs) (baseSet n N))
    {Φ : List ℕ} (hΦn : Φ.Nodup) (hΦl : ∀ i ∈ Φ, i < N - n)
    (hΦ : IsInvariant (GensData.denote N gs) {u | u.val ∈ ptsD n Φ}) {sm : ℕ}
    (Bm : BackendBounds X DV (phiSD (N - n) Φ []).length sm ⊤) :
    degD X.O N n (N, gs, d) Φ ≤ Φ.length ∧
      TupTrans (baseHom _ n hF).range (setOf (N - n) Φ) (degD X.O N n (N, gs, d) Φ) ∧
      (degD X.O N n (N, gs, d) Φ < Φ.length →
        ¬ TupTrans (baseHom _ n hF).range (setOf (N - n) Φ) (degD X.O N n (N, gs, d) Φ + 1)) := by
  have hlen := length_phiSD_nil hΦn hΦl
  obtain ⟨-, hdeg, hRv, hrv⟩ := RunsWithin.resProg (X := X) (a := Ty.unit) (b := Ty.unit)
    (body := fun u => .ret u) (cp2_choiceOps_of_deg hO)
    (fun op x h hp => hPre op x (Or.inl h) hp) B hGv hs hG₀ hΦ (Sl := [])
    (fun v hv => absurd hv List.not_mem_nil) le_rfl
  have hpre : GroupPre DV GroupOp.generate
      ((phiSD (N - n) Φ []).length, rgensD N n gs (phiSD (N - n) Φ [])) := hrv
  have hpost := hO GroupOp.generate _ (Or.inl (Or.inr (Or.inr (Or.inr rfl)))) hpre
  have hgen : (resModel X.O N n (N, gs, d) Φ []).2.1.length ≤ sm := Bm.genOut _ hrv le_top
  have hden : GensData.denote (phiSD (N - n) Φ []).length (resModel X.O N n (N, gs, d) Φ []).2.1
      = GensData.denote (phiSD (N - n) Φ []).length
        (rgensD N n gs (phiSD (N - n) Φ [])) := hpost.2.2
  have hW : IsInvariant (GensData.denote N gs) {u | u.val ∈ ptsD n (phiSD (N - n) Φ [])} := by
    intro g hg u hu
    have hu' : u.val ∈ ptsD n Φ := by
      obtain ⟨v, hv, hvu⟩ := List.mem_map.1 (show u.val ∈ ptsD n (phiSD (N - n) Φ []) from hu)
      exact hvu ▸ List.mem_map_of_mem (mem_phiSD.1 hv).2.1
    obtain ⟨v, hv, hvu⟩ := List.mem_map.1 (show (g u).val ∈ ptsD n Φ from hΦ g hg u hu')
    show (g u).val ∈ ptsD n (phiSD (N - n) Φ [])
    exact hvu ▸ List.mem_map_of_mem (mem_phiSD.2 ⟨hΦl v hv, hv, List.not_mem_nil⟩)
  have hiff := fun k => cp2_resTrans_iff (k := k) hGv.1 hF (phiSD_nodup _ _ _)
    (fun i hi => (mem_phiSD.1 hi).1) hW rfl hden
  unfold degD
  generalize resModel X.O N n (N, gs, d) Φ [] = R at hdeg hRv hgen hiff ⊢
  obtain ⟨M, gsR, eR⟩ := R
  change M = _ at hdeg
  subst hdeg
  have hinv : IsInvariant (GensData.denote (phiSD (N - n) Φ []).length gsR)
      (baseSet 0 (phiSD (N - n) Φ []).length) := fun _ _ u _ => Nat.zero_le _
  obtain ⟨hle, htr, hnot⟩ := degreeModel_spec (cap := (phiSD (N - n) Φ []).length)
    (fun op x h hp => hO op x (Or.inr h) hp) Bm hRv hgen le_top hinv (Nat.zero_le _) le_rfl
  rw [cp2_multTrans_baseHom_zero] at htr hnot
  rw [hiff, setOf_phiSD_nil] at htr
  simp only [hiff, setOf_phiSD_nil] at hnot
  rw [← hlen]
  exact ⟨hle, htr, hnot⟩

/-- **Under `TransitivityBound T`** (stage 14j-6b-1, `PLAN-14.md` §14.11 item 2): on an orbit `Φ`
on which `ψ(F)` does not move any `|Φ| − 2` points to any other, the computed degree is at most
`T |Φ|`. The action on `Φ`, numbered, is `d`-transitive (`degD_spec`), and it does not contain
`Alt(Φ)`, which is `(|Φ| − 2)`-transitive (`alt_le_iff`). -/
theorem degD_le_T {T : ℕ → ℕ} (hT : AltQuot.TransitivityBound T)
    (hO : MeetsContractOn DV degOps X.O)
    (hPre : ∀ op x, degOps op → GroupPre DV op x → X.Pre op x)
    {N n s : ℕ} {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N s G₀)
    {gs : GensData} {d : D.denote} (hGv : GroupValid DV N gs d) (hs : gs.length ≤ s)
    (hG₀ : GensData.denote N gs ≤ G₀) (hF : IsInvariant (GensData.denote N gs) (baseSet n N))
    {Φ : List ℕ} (hΦn : Φ.Nodup) (hΦl : ∀ i ∈ Φ, i < N - n)
    (hΦ : IsInvariant (GensData.denote N gs) {u | u.val ∈ ptsD n Φ}) {sm : ℕ}
    (Bm : BackendBounds X DV (phiSD (N - n) Φ []).length sm ⊤)
    (hng : ¬ TupTrans (baseHom _ n hF).range (setOf (N - n) Φ) (Φ.length - 2)) :
    degD X.O N n (N, gs, d) Φ ≤ T Φ.length := by
  have hlen := length_phiSD_nil hΦn hΦl
  obtain ⟨-, hdeg, hRv, hrv⟩ := RunsWithin.resProg (X := X) (a := Ty.unit) (b := Ty.unit)
    (body := fun u => .ret u) (cp2_choiceOps_of_deg hO)
    (fun op x h hp => hPre op x (Or.inl h) hp) B hGv hs hG₀ hΦ (Sl := [])
    (fun v hv => absurd hv List.not_mem_nil) le_rfl
  have hpre : GroupPre DV GroupOp.generate
      ((phiSD (N - n) Φ []).length, rgensD N n gs (phiSD (N - n) Φ [])) := hrv
  have hpost := hO GroupOp.generate _ (Or.inl (Or.inr (Or.inr (Or.inr rfl)))) hpre
  have hgen : (resModel X.O N n (N, gs, d) Φ []).2.1.length ≤ sm := Bm.genOut _ hrv le_top
  have hden : GensData.denote (phiSD (N - n) Φ []).length (resModel X.O N n (N, gs, d) Φ []).2.1
      = GensData.denote (phiSD (N - n) Φ []).length
        (rgensD N n gs (phiSD (N - n) Φ [])) := hpost.2.2
  have hW : IsInvariant (GensData.denote N gs) {u | u.val ∈ ptsD n (phiSD (N - n) Φ [])} := by
    intro g hg u hu
    have hu' : u.val ∈ ptsD n Φ := by
      obtain ⟨v, hv, hvu⟩ := List.mem_map.1 (show u.val ∈ ptsD n (phiSD (N - n) Φ []) from hu)
      exact hvu ▸ List.mem_map_of_mem (mem_phiSD.1 hv).2.1
    obtain ⟨v, hv, hvu⟩ := List.mem_map.1 (show (g u).val ∈ ptsD n Φ from hΦ g hg u hu')
    show (g u).val ∈ ptsD n (phiSD (N - n) Φ [])
    exact hvu ▸ List.mem_map_of_mem (mem_phiSD.2 ⟨hΦl v hv, hv, List.not_mem_nil⟩)
  have hiff := fun k => cp2_resTrans_iff (k := k) hGv.1 hF (phiSD_nodup _ _ _)
    (fun i hi => (mem_phiSD.1 hi).1) hW rfl hden
  unfold degD
  generalize resModel X.O N n (N, gs, d) Φ [] = R at hdeg hRv hgen hiff ⊢
  obtain ⟨M, gsR, eR⟩ := R
  change M = _ at hdeg
  subst hdeg
  have hinv : IsInvariant (GensData.denote (phiSD (N - n) Φ []).length gsR)
      (baseSet 0 (phiSD (N - n) Φ []).length) := fun _ _ u _ => Nat.zero_le _
  obtain ⟨hle, htr, -⟩ := degreeModel_spec (cap := (phiSD (N - n) Φ []).length)
    (fun op x h hp => hO op x (Or.inr h) hp) Bm hRv hgen le_top hinv (Nat.zero_le _) le_rfl
  rw [cp2_multTrans_baseHom_zero] at htr
  have hnA : ¬ alternatingGroup (Fin (phiSD (N - n) Φ []).length) ≤
      GensData.denote (phiSD (N - n) Φ []).length gsR := by
    rw [GraphIso.Recursion.alt_le_iff, Fintype.card_fin, hiff, setOf_phiSD_nil, hlen]
    exact hng
  have h := hT (Fin (phiSD (N - n) Φ []).length) _ _ (by rw [Fintype.card_fin]; omega) htr hnA
  rw [Fintype.card_fin] at h
  rw [← hlen]
  exact h

/-- An orbit is mapped into itself. -/
theorem cp2_orbit_pres {Γ : Type*} {P : Subgroup (Perm Γ)} {γ : Γ} {g : Perm Γ} (hg : g ∈ P)
    {x : Γ} (hx : x ∈ MulAction.orbit P γ) : g x ∈ MulAction.orbit P γ := by
  obtain ⟨⟨h, hh⟩, rfl⟩ := hx
  exact ⟨⟨g * h, P.mul_mem hg hh⟩, rfl⟩

/-- An orbit: any point is moved to any other. -/
theorem cp2_orbit_one {Γ : Type*} {P : Subgroup (Perm Γ)} {γ : Γ} {Φ : Finset Γ}
    (hΦ : ∀ v, v ∈ Φ ↔ v ∈ MulAction.orbit P γ) : TupTrans P Φ 1 := by
  intro T T' _ _ hTΦ hT'Φ
  obtain ⟨⟨a, ha⟩, hTa⟩ := (hΦ _).1 (hTΦ 0)
  obtain ⟨⟨b, hb⟩, hTb⟩ := (hΦ _).1 (hT'Φ 0)
  refine ⟨b * a⁻¹, P.mul_mem hb (P.inv_mem ha), fun i => ?_⟩
  rw [Subsingleton.elim i 0, ← hTa, ← hTb]
  show b (a⁻¹ (a γ)) = b γ
  rw [perm_inv_apply_self]

/-- **The hypotheses of Case 2b from the degree program.** If `Φ` is an orbit of `ψ(F)` on which
`ψ(F)` is not a giant (it does not move any `|Φ| - 2` points of `Φ` to any other), then
`d = degD ≥ 1` and `Case2bHyp ψ(F) Φ d` holds (`case2bHyp_of_degree`). -/
theorem case2bHyp_degD (hO : MeetsContractOn DV degOps X.O)
    (hPre : ∀ op x, degOps op → GroupPre DV op x → X.Pre op x)
    {N n s : ℕ} {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N s G₀)
    {gs : GensData} {d : D.denote} (hGv : GroupValid DV N gs d) (hs : gs.length ≤ s)
    (hG₀ : GensData.denote N gs ≤ G₀) (hF : IsInvariant (GensData.denote N gs) (baseSet n N))
    {Φ : List ℕ} (hΦn : Φ.Nodup) (hΦl : ∀ i ∈ Φ, i < N - n)
    (hΦ : IsInvariant (GensData.denote N gs) {u | u.val ∈ ptsD n Φ}) {sm : ℕ}
    (Bm : BackendBounds X DV (phiSD (N - n) Φ []).length sm ⊤)
    (hΦo : ∃ γ : Fin (N - n), ∀ δ : Fin (N - n),
      δ.val ∈ Φ ↔ δ ∈ MulAction.orbit (baseHom _ n hF).range γ)
    (hng : ¬ TupTrans (baseHom _ n hF).range (setOf (N - n) Φ) (Φ.length - 2)) :
    1 ≤ degD X.O N n (N, gs, d) Φ ∧
      Case2bHyp (baseHom _ n hF).range (setOf (N - n) Φ) (degD X.O N n (N, gs, d) Φ) := by
  obtain ⟨hle, htr, hnot⟩ := degD_spec hO hPre B hGv hs hG₀ hF hΦn hΦl hΦ Bm
  set dd := degD X.O N n (N, gs, d) Φ
  set P := (baseHom _ n hF).range
  obtain ⟨γ, hγ⟩ := hΦo
  have hcard : (setOf (N - n) Φ).card = Φ.length := card_setOf hΦn hΦl
  have hmem : ∀ v, v ∈ setOf (N - n) Φ ↔ v ∈ MulAction.orbit P γ := fun v => by
    rw [mem_setOf, hγ]
  have hpres : ∀ g ∈ P, ∀ x ∈ setOf (N - n) Φ, g x ∈ setOf (N - n) Φ := fun g hg x hx =>
    (hmem _).2 (cp2_orbit_pres hg ((hmem _).1 hx))
  have hone := cp2_orbit_one hmem
  have hpos : 1 ≤ Φ.length := by
    have : γ.val ∈ Φ := (hγ γ).2 (MulAction.mem_orbit_self γ)
    exact List.length_pos_of_mem this
  have h1 : 1 ≤ dd := by
    by_contra h0
    exact hnot (by omega) (by rw [show dd = 0 by omega]; exact hone)
  have hsize : dd - 1 + 4 ≤ (setOf (N - n) Φ).card := by
    rw [hcard]
    by_contra hbig
    exact hng (cp2_tupTrans_mono hpres htr (by omega) (by omega))
  refine ⟨h1, case2bHyp_of_degree hpres hsize ?_ ?_⟩
  · rw [Nat.sub_add_cancel h1]
    exact htr
  · rw [show dd - 1 + 2 = dd + 1 by omega]
    exact hnot (by omega)

end DegreeSpec

/-! ### The sizes of the leaves -/

section Sizes

theorem cp2_length_mapE_le (ΦS l : List ℕ) : (mapE ΦS l).length ≤ l.length := by
  unfold mapE
  rw [List.length_map]
  exact List.length_filter_le _ _

/-- The extension to the base adds at most the base to the size of a leaf. -/
theorem outSize_extD_le (m : ℕ) (ΦS : List ℕ) (o : OutD) :
    outSize (extD m ΦS o) ≤ m + outSize o := by
  unfold extD
  split_ifs with h1 h2
  · have hb : ldMaxLen ((List.range m).map fun v =>
        if v ∈ ΦS then mapE ΦS (o.2.1.2.getD (ΦS.idxOf v) [])
        else (List.range m).filter fun w => decide (w ∉ ΦS)).toArray.toList ≤ m + outSize o :=
      ld_maxLen_map_range_le m _ fun x _ => by
        split_ifs
        · exact (cp2_length_mapE_le _ _).trans ((outSize_blk o _).trans (Nat.le_add_left _ _))
        · exact (List.length_filter_le _ _).trans (by simp)
    unfold outSize
    simp only [partD]
    simp only [ldMaxLen, List.map_nil, List.foldr_nil, List.length_nil, max_le_iff, Nat.zero_le,
      and_true]
    exact hb
  · have hfA : ldMaxLen ((List.range m).map fun v =>
        if v ∈ ΦS then o.2.2.2.2.2.getD (ΦS.idxOf v) [] else []).toArray.toList ≤
          m + outSize o :=
      ld_maxLen_map_range_le m _ fun x _ => by
        split_ifs
        · exact (outSize_fA o _).trans (Nat.le_add_left _ _)
        · simp
    have h3 : ldMaxLen (o.2.2.2.1.map (mapE ΦS)) ≤ m + outSize o := ld_maxLen_le fun c hc => by
      obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
      exact (cp2_length_mapE_le _ _).trans ((outSize_cell o hc').trans (Nat.le_add_left _ _))
    have h1 := (cp2_length_mapE_le ΦS o.2.2.1).trans (outSize_V0 o)
    have h2 := outSize_cs o
    generalize outSize o = L at h1 h2 h3 hfA ⊢
    unfold outSize
    simp only [johnD, List.length_map]
    simp only [ldMaxLen, List.map_nil, List.foldr_nil, max_le_iff, Nat.zero_le, true_and]
    exact ⟨by omega, by omega, h3, hfA⟩
  · exact Nat.le_add_left _ _

/-- The Johnson data of a leaf is bounded by its size. -/
theorem cp2_jbound_outSize (o : OutD) : JBound (outSize o) o.2.2 where
  v0 := outSize_V0 o
  k := outSize_cs o
  cell _ hc := outSize_cell o hc
  fl u := outSize_fA o u

/-- The size bound of the leaves of Case 2b on a base of `m` points. -/
def leafB (m : ℕ) : ℕ := m + outB m (m + 2)

theorem outSize_choiceLeavesD {D : Ty} {O : Oracle (groupSig D)} {N n : ℕ}
    {F : GroupData D.denote} {Φ Sl : List ℕ} {a b : ℕ} :
    ∀ o ∈ choiceLeavesD O N n F Φ Sl a b, outSize o ≤ leafB (N - n) := by
  intro o ho
  obtain ⟨o', ho', rfl⟩ := List.mem_map.1 ho
  have h1 := outSize_leavesOfD _ _ o' ho'
  have hm := length_phiSD_le (N - n) Φ Sl
  set m' := (phiSD (N - n) Φ Sl).length
  have h2 : outB m' ((m' + 3) / 2) ≤ outB (N - n) (N - n + 2) := by
    unfold outB
    have := Nat.mul_le_mul hm hm
    omega
  exact (outSize_extD_le _ _ _).trans (by unfold leafB; omega)

theorem outSize_allLeavesD {D : Ty} {O : Oracle (groupSig D)} {N n : ℕ}
    {F : GroupData D.denote} {Φ : List ℕ} {j : ℕ} :
    ∀ o ∈ allLeavesD O N n F Φ j, outSize o ≤ leafB (N - n) := by
  intro o ho
  obtain ⟨Sl, -, ho⟩ := List.mem_flatMap.1 ho
  obtain ⟨ab, -, ho⟩ := List.mem_flatMap.1 ho
  exact outSize_choiceLeavesD o ho

theorem outSize_firstLeafD {D : Ty} {O : Oracle (groupSig D)} {N n : ℕ}
    {F : GroupData D.denote} {Φ : List ℕ} {j : ℕ} {o : OutD}
    (h : firstLeafD O N n F Φ j = some o) : outSize o ≤ leafB (N - n) := by
  unfold firstLeafD at h
  split at h
  · exact outSize_choiceLeavesD o (List.mem_of_head? h)
  · exact absurd h (by simp)

theorem length_allLeavesD_le {D : Ty} {O : Oracle (groupSig D)} {N n : ℕ}
    {F : GroupData D.denote} {Φ : List ℕ} {j Lc : ℕ}
    (hL : ∀ Sl ∈ tuplesD Φ j, ∀ ab ∈ pairsD (phiSD (N - n) Φ Sl).length,
      (choiceLeavesD O N n F Φ Sl ab.1 ab.2).length ≤ Lc) :
    (allLeavesD O N n F Φ j).length ≤ Φ.length ^ j * ((N - n) * (N - n) * Lc) := by
  refine (po_length_flatMap_le _ fun Sl hSl => ?_).trans
    (Nat.mul_le_mul_right _ (length_tuplesD_le Φ j))
  have hm := length_phiSD_le (N - n) Φ Sl
  refine (po_length_flatMap_le _ fun ab hab => hL Sl hSl ab hab).trans ?_
  exact Nat.mul_le_mul_right _ ((length_pairsD_le _).trans (Nat.mul_le_mul hm hm))

/-- `Spec` for a stronger invariant. -/
theorem cp2_spec_mono {m : ℕ} {τ O : Type} [MulAction (Perm (Fin m)) O] {S : StructOps m τ O}
    {V V' : τ → Prop} (h : S.Spec V) (hV : ∀ x, V' x → V x) : S.Spec V' where
  gens_valid x hx := h.gens_valid x (hV x hx)
  gens_closure x hx := h.gens_closure x (hV x hx)
  iso_some x y hx hy := h.iso_some x y (hV x hx) (hV y hy)
  iso_none x y hx hy := h.iso_none x y (hV x hx) (hV y hy)

end Sizes

/-! ### Uniform costs of the choices -/

section ChoiceBounds

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}

theorem length_phiSD {m : ℕ} {Φ Sl : List ℕ} (hn : Φ.Nodup) (hl : ∀ i ∈ Φ, i < m)
    (hSn : Sl.Nodup) (hS : ∀ x ∈ Sl, x ∈ Φ) :
    (phiSD m Φ Sl).length = Φ.length - Sl.length := by
  have h1 : (phiSD m Φ Sl).toFinset = Φ.toFinset \ Sl.toFinset := by
    ext v
    simp only [List.mem_toFinset, Finset.mem_sdiff, mem_phiSD]
    exact ⟨fun h => ⟨h.2.1, h.2.2⟩, fun h => ⟨hl v h.1, h.1, h.2⟩⟩
  have h2 := congrArg Finset.card h1
  rwa [List.toFinset_card_of_nodup (phiSD_nodup _ _ _), Finset.card_sdiff_of_subset
    (fun x hx => List.mem_toFinset.2 (hS x (List.mem_toFinset.1 hx))),
    List.toFinset_card_of_nodup hn, List.toFinset_card_of_nodup hSn] at h2

theorem choiceCost_mono {N n s nΦ nS m' a a' Bstab Bg Btr Bst Borb sz sz' : ℕ} (ha : a ≤ a')
    (hz : sz ≤ sz') :
    choiceCost N n s nΦ nS m' a Bstab Bg Btr Bst Borb sz ≤
      choiceCost N n s nΦ nS m' a' Bstab Bg Btr Bst Borb sz' := by
  unfold choiceCost colCost leavesOfCost sojBranchCost
  have h1 := Nat.mul_le_mul_left (stepK m' ((m' + 3) / 2) ((m' + 3) / 2) + 11)
    (Nat.mul_le_mul_left ((m' + 3) / 2 + 2) hz)
  have h2 := Nat.mul_le_mul_right (trimCost m' (outB m' ((m' + 3) / 2)) + 3) hz
  have h3 := Nat.mul_le_mul_right (extCost (N - n) m' (outB m' ((m' + 3) / 2)) + 3)
    (Nat.add_le_add_right hz 1)
  omega

/-- The cost of one choice with `|Φ| = nΦ` and `j` individualized points: `m' = nΦ - j`, an
index `a ≤ m'`, and a `soj` tree of size at most `Z`. -/
def chCost (N n s nΦ j Bstab Bg Btr Bst Borb Z : ℕ) : ℕ :=
  choiceCost N n s nΦ j (nΦ - j) (nΦ - j) Bstab Bg Btr Bst Borb Z

/-- **One choice, at the uniform cost.** The generation at degree `m' ≤ N - n` of at most `s`
generators is charged at most `Bg`; the backend at degree `m'` is `Bm m'`. -/
theorem RunsWithin.choiceProg_le (hO : MeetsContractOn DV choiceOps X.O)
    (hPre : ∀ op x, choiceOps op → GroupPre DV op x → X.Pre op x)
    {N n s : ℕ} {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N s G₀)
    {sm : ℕ → ℕ} (Bm : ∀ M, BackendBounds X DV M (sm M) ⊤)
    {gs : GensData} {d : D.denote} (hGv : GroupValid DV N gs d) (hs : gs.length ≤ s)
    (hG₀ : GensData.denote N gs ≤ G₀) {Φ : List ℕ} (hΦn : Φ.Nodup) (hΦl : ∀ i ∈ Φ, i < N - n)
    (hΦ : IsInvariant (GensData.denote N gs) {u | u.val ∈ ptsD n Φ}) {j : ℕ}
    (hj : j < Φ.length) {Bg : ℕ}
    (hBg : ∀ M ≤ N - n, ∀ gs' : GensData, GensData.AllValid M gs' → gs'.length ≤ s →
      X.B.call GroupOp.generate (M, gs') (X.O.run GroupOp.generate (M, gs')) ≤ Bg)
    {Sl : List ℕ} (hSl : Sl ∈ tuplesD Φ j) {a' b' : ℕ} (ha : a' ≤ Φ.length - j) {Z : ℕ}
    (hZ : sojSz (phiSD (N - n) Φ Sl).length (wlColOf X.O N n (N, gs, d) Φ Sl a' b') ≤ Z) :
    RunsWithin X body (Case2b.choiceProg N n (N, gs, d) Φ Sl a' b')
      (choiceLeavesD X.O N n (N, gs, d) Φ Sl a' b')
      (chCost N n s Φ.length j B.Bstab Bg (Bm (Φ.length - j)).Btr (Bm (Φ.length - j)).Bstab
        (Bm (Φ.length - j)).Borb Z) := by
  obtain ⟨hSlen, hSn, hSΦ⟩ := (mem_tuplesD Φ j).1 hSl
  have hlen : (phiSD (N - n) Φ Sl).length = Φ.length - j := by
    rw [length_phiSD hΦn hΦl hSn hSΦ, hSlen]
  have hS : ∀ v ∈ Sl, v < N - n := fun v hv => hΦl v (hSΦ v hv)
  have hstab : MeetsContractOn DV stabOps X.O := fun op x h hp =>
    hO op x (h.elim (fun h => Or.inl h) fun h => Or.inr (Or.inl h)) hp
  obtain ⟨-, -, -, hrv⟩ := RunsWithin.resProg (X := X) (body := body) hO hPre B hGv hs hG₀ hΦ
    hS le_rfl
  have hpS : ∀ u ∈ ptsD n Sl, u < N := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hu
    have := hS v hv
    omega
  have hFS := cp2_iterStab_gens_le hstab B (ptsD n Sl) (N, gs, d) hpS rfl hGv hs hG₀
  have hBg' := hBg _ (length_phiSD_le _ _ _) _ hrv
    (by simpa [rgensD, GensData.restrictTo, fsModel] using hFS)
  have h := RunsWithin.choiceProg (X := X) (body := body) hO hPre B hGv hs hG₀ hΦ hS
    (by omega) (Bm _) hBg' a' b'
  rw [hlen] at h hZ
  refine h.mono ?_
  rw [hSlen]
  exact choiceCost_mono ha hZ

/-- **All leaves, at the uniform cost**: at most `|Φ|^j` tuples, `(N - n)²` pairs, and `Z + 1`
leaves per choice. -/
theorem RunsWithin.allLeavesProg_le (hO : MeetsContractOn DV choiceOps X.O)
    (hPre : ∀ op x, choiceOps op → GroupPre DV op x → X.Pre op x)
    {N n s : ℕ} {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N s G₀)
    {sm : ℕ → ℕ} (Bm : ∀ M, BackendBounds X DV M (sm M) ⊤)
    {gs : GensData} {d : D.denote} (hGv : GroupValid DV N gs d) (hs : gs.length ≤ s)
    (hG₀ : GensData.denote N gs ≤ G₀) {Φ : List ℕ} (hΦn : Φ.Nodup) (hΦl : ∀ i ∈ Φ, i < N - n)
    (hΦ : IsInvariant (GensData.denote N gs) {u | u.val ∈ ptsD n Φ}) {j : ℕ}
    (hj : j < Φ.length) {Bg : ℕ}
    (hBg : ∀ M ≤ N - n, ∀ gs' : GensData, GensData.AllValid M gs' → gs'.length ≤ s →
      X.B.call GroupOp.generate (M, gs') (X.O.run GroupOp.generate (M, gs')) ≤ Bg) {Z : ℕ}
    (hZ : ∀ Sl ∈ tuplesD Φ j, ∀ ab ∈ pairsD (phiSD (N - n) Φ Sl).length,
      sojSz (phiSD (N - n) Φ Sl).length (wlColOf X.O N n (N, gs, d) Φ Sl ab.1 ab.2) ≤ Z) :
    RunsWithin X body (Case2b.allLeavesProg N n (N, gs, d) Φ j) (allLeavesD X.O N n (N, gs, d) Φ j)
      (allCost (N - n) Φ.length j (chCost N n s Φ.length j B.Bstab Bg (Bm (Φ.length - j)).Btr
        (Bm (Φ.length - j)).Bstab (Bm (Φ.length - j)).Borb Z) (Z + 1)) := by
  refine RunsWithin.allLeavesProg (fun Sl hSl ab hab => ?_) fun Sl hSl ab hab => ?_
  · obtain ⟨hSlen, hSn, hSΦ⟩ := (mem_tuplesD Φ j).1 hSl
    have ha := (mem_pairsD.1 (show (ab.1, ab.2) ∈ _ from hab)).1
    rw [length_phiSD hΦn hΦl hSn hSΦ, hSlen] at ha
    exact RunsWithin.choiceProg_le hO hPre B Bm hGv hs hG₀ hΦn hΦl hΦ hj hBg hSl ha.le
      (hZ Sl hSl ab hab)
  · unfold choiceLeavesD
    rw [List.length_map]
    exact (length_leavesOfD_le _ _).trans (Nat.add_le_add_right (hZ Sl hSl ab hab) 1)

/-- **The first leaf, at the uniform cost**, when `Φ ∖ S` has at least two points. -/
theorem RunsWithin.firstLeafProg_le (hO : MeetsContractOn DV choiceOps X.O)
    (hPre : ∀ op x, choiceOps op → GroupPre DV op x → X.Pre op x)
    {N n s : ℕ} {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N s G₀)
    {sm : ℕ → ℕ} (Bm : ∀ M, BackendBounds X DV M (sm M) ⊤)
    {gs : GensData} {d : D.denote} (hGv : GroupValid DV N gs d) (hs : gs.length ≤ s)
    (hG₀ : GensData.denote N gs ≤ G₀) {Φ : List ℕ} (hΦn : Φ.Nodup) (hΦl : ∀ i ∈ Φ, i < N - n)
    (hΦ : IsInvariant (GensData.denote N gs) {u | u.val ∈ ptsD n Φ}) {j : ℕ}
    (hj : j + 2 ≤ Φ.length) {Bg : ℕ}
    (hBg : ∀ M ≤ N - n, ∀ gs' : GensData, GensData.AllValid M gs' → gs'.length ≤ s →
      X.B.call GroupOp.generate (M, gs') (X.O.run GroupOp.generate (M, gs')) ≤ Bg) {Z : ℕ}
    (hZ : ∀ Sl ∈ tuplesD Φ j, ∀ ab ∈ pairsD (phiSD (N - n) Φ Sl).length,
      sojSz (phiSD (N - n) Φ Sl).length (wlColOf X.O N n (N, gs, d) Φ Sl ab.1 ab.2) ≤ Z) :
    RunsWithin X body (Case2b.firstLeafProg N n (N, gs, d) Φ j) (firstLeafD X.O N n (N, gs, d) Φ j)
      (tuplesCost Φ.length j + chCost N n s Φ.length j B.Bstab Bg (Bm (Φ.length - j)).Btr
        (Bm (Φ.length - j)).Bstab (Bm (Φ.length - j)).Borb Z + 8) := by
  refine RunsWithin.firstLeafProg fun Sl hSl => ?_
  obtain ⟨hSlen, hSn, hSΦ⟩ := (mem_tuplesD Φ j).1 hSl
  have hm : (phiSD (N - n) Φ Sl).length = Φ.length - j := by
    rw [length_phiSD hΦn hΦl hSn hSΦ, hSlen]
  have h01 : ((0, 1) : ℕ × ℕ) ∈ pairsD (phiSD (N - n) Φ Sl).length :=
    mem_pairsD.2 ⟨by omega, by omega, Nat.zero_ne_one⟩
  have hZ01 := hZ Sl hSl _ h01
  dsimp only at hZ01
  have hj' : j < Φ.length := by omega
  exact RunsWithin.choiceProg_le (a' := 0) (b' := 1) hO hPre B Bm hGv hs hG₀ hΦn hΦl hΦ hj' hBg
    hSl (Nat.zero_le _) hZ01

end ChoiceBounds

/-! ### The program -/

section Program

variable {D : Ty} {rec : Ty × Ty} {var : Ty → Type}

/-- **Case 2b.** The degrees `dx`, `dy` of transitivity of `ψ(F(x))` on `Φ(x)` and of `ψ(F(y))`
on `Φ(y)`. If they differ, there is no isomorphism. Otherwise, with `j = dx - 1`: the first leaf
`X₀` of `x`'s tree, every leaf of `y`'s tree, and Align (`alignProg` with `outOps`), the
sub-solver on each aligned coset. -/
def case2bProg (sub : var (Ty.inst D) → Prog (groupSig D) rec var (Ty.answer D))
    (n : var .nat) (xy : var Ty.strs) (w : var Ty.win) (G Fx Fy : var (Ty.group D))
    (Φx Φy : var (.list .nat)) : Prog (groupSig D) rec var (Ty.answer D) :=
  .bind (.op1 .fst G) fun N => .bind (.op2 .sub N n) fun m =>
  .bind (degProg N n Fx Φx) fun dx => .bind (degProg N n Fy Φy) fun dy =>
  .bind (.op2 .natEq dx dy) fun same =>
  .ite same
    (.bind (.op0 (.natLit 1)) fun one => .bind (.op2 .sub dx one) fun j =>
      .bind (firstLeafProg N n Fx Φx j) fun ox =>
      .caseOption ox (.op0 .none) fun X₀ =>
      .bind (allLeavesProg N n Fy Φy j) fun Ys =>
      alignProg sub (fun o => outGensProg m o) (fun o o' => outIsoProg m o o') n xy w G X₀ Ys)
    (.op0 .none)

end Program

/-! ### The specification -/

section Spec

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}

/-- The operations of Case 2b. -/
def c2bOps (op : GroupOp) : Prop := degOps op ∨ alignOps op

/-- The bound on the number of leaves for `y`: `|Φ|^j` tuples, `(N - n)²` pairs, `Z + 1` leaves
per choice. -/
def c2bR (N n nΦ j Z : ℕ) : ℕ := nΦ ^ j * ((N - n) * (N - n) * (Z + 1))

/-- **The cost of Case 2b**: `g` generators of `G`, `|Φ(x)| = nx`, `|Φ(y)| = ny`, `j = d - 1`,
`k` stabilizer generators of `x`'s leaf, `soj` trees of size at most `Z`, the backend at degree
`M` with charges `Bo M`, `Bs M`, `Bt M` (orbits, stabilizer, transversal), and Align's
charges. -/
def c2bCost (n N s g nx ny j k Bstab Bg Z BgP Bmem Bk Bl Bg1 Bgen Cb : ℕ)
    (Bo Bs Bt : ℕ → ℕ) : ℕ :=
  1 + 1 + degCost N n nx nx s Bstab Bg (Bo nx) (Bs nx) +
    degCost N n ny ny s Bstab Bg (Bo ny) (Bs ny) + 1 +
    (1 + (1 + 1 + (tuplesCost nx j +
      chCost N n s nx j Bstab Bg (Bt (nx - j)) (Bs (nx - j)) (Bo (nx - j)) Z + 8) +
    (1 + (allCost (N - n) ny j
      (chCost N n s ny j Bstab Bg (Bt (ny - j)) (Bs (ny - j)) (Bo (ny - j)) Z) (Z + 1) +
    alignCost n N g k (c2bR N n ny j Z) (outGensCost (N - n) (leafB (N - n)) (leafB (N - n)))
      (outIsoCost (N - n) (leafB (N - n)) (leafB (N - n)) (leafB (N - n))) BgP Bmem Bk Bl Bg1
      Bgen Cb s))))

theorem cp2_alignCost_mono {n N g k r r' cG cI BgP Bmem Bk Bl Bg1 Bgen Cb s : ℕ} (h : r ≤ r') :
    alignCost n N g k r cG cI BgP Bmem Bk Bl Bg1 Bgen Cb s ≤
      alignCost n N g k r' cG cI BgP Bmem Bk Bl Bg1 Bgen Cb s := by
  unfold alignCost
  have h1 := Nat.mul_le_mul_right (alignCallCost n N k cI Bmem Bl Cb + 3) h
  have h2 := Nat.mul_le_mul_right (12 * N + s + 26) h
  omega

/-- The Johnson data of a leaf of size at most `B` is bounded by `B`. -/
theorem cp2_jbound_le {o : OutD} {B : ℕ} (h : outSize o ≤ B) : JBound B o.2.2 where
  v0 := (outSize_V0 o).trans h
  k := (outSize_cs o).trans h
  cell _ hc := (outSize_cell o hc).trans h
  fl u := (outSize_fA o u).trans h

/-- **The degree program at the uniform charge.** -/
theorem RunsWithin.degProg_le (hO : MeetsContractOn DV degOps X.O)
    (hPre : ∀ op x, degOps op → GroupPre DV op x → X.Pre op x)
    {N n s : ℕ} {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N s G₀)
    {sm : ℕ → ℕ} (Bm : ∀ M, BackendBounds X DV M (sm M) ⊤)
    {gs : GensData} {d : D.denote} (hGv : GroupValid DV N gs d) (hs : gs.length ≤ s)
    (hG₀ : GensData.denote N gs ≤ G₀) {Φ : List ℕ} (hΦn : Φ.Nodup) (hΦl : ∀ i ∈ Φ, i < N - n)
    (hΦ : IsInvariant (GensData.denote N gs) {u | u.val ∈ ptsD n Φ}) {Bg : ℕ}
    (hBg : ∀ M ≤ N - n, ∀ gs' : GensData, GensData.AllValid M gs' → gs'.length ≤ s →
      X.B.call GroupOp.generate (M, gs') (X.O.run GroupOp.generate (M, gs')) ≤ Bg) :
    RunsWithin X body (Case2b.degProg N n (N, gs, d) Φ) (degD X.O N n (N, gs, d) Φ)
      (degCost N n Φ.length Φ.length s B.Bstab Bg (Bm Φ.length).Borb (Bm Φ.length).Bstab) := by
  obtain ⟨-, -, -, hrv⟩ := RunsWithin.resProg (X := X) (body := body)
    (cp2_choiceOps_of_deg hO) (fun op x h hp => hPre op x (Or.inl h) hp) B hGv hs hG₀ hΦ
    (Sl := []) (fun v hv => absurd hv List.not_mem_nil) le_rfl
  have h := RunsWithin.degProg (body := body) hO hPre B hGv hs hG₀ hΦ (Bm _)
    (hBg _ (length_phiSD_le _ _ _) _ hrv (by simpa [rgensD, GensData.restrictTo] using hs))
  rw [length_phiSD_nil hΦn hΦl] at h
  exact h

/-- **Case 2b**, with the hypotheses that the model of the tree provides: the leaves are valid,
the degrees differ only when there is no isomorphism, and, when they agree, every isomorphism
carries the first leaf for `x` to a leaf for `y` (the alignment hypothesis of `alignProg`). The
answer is correct for `G`, under `SubSolves` for the aligned cosets. -/
theorem RunsWithin.case2bProg (hO : MeetsContractOn DV c2bOps X.O)
    (hPre : ∀ op x, c2bOps op → GroupPre DV op x → X.Pre op x)
    {n N s : ℕ} {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N s G₀)
    {sm : ℕ → ℕ} (Bm : ∀ M, BackendBounds X DV M (sm M) ⊤)
    {gs : GensData} {d : D.denote} (hGv : GroupValid DV N gs d)
    (hG : IsInvariant (GensData.denote N gs) (baseSet n N))
    (halt : alternatingGroup (Fin (N - n)) ≤ (baseHom _ n hG).range)
    {xy : StrData × StrData} {w : WinData} (hw : w.Valid N)
    (hWG : IsInvariant (GensData.denote N gs) (w.denote N))
    {fxs fys : GensData} {ex ey : D.denote} (hFxv : GroupValid DV N fxs ex)
    (hFyv : GroupValid DV N fys ey) (hFxs : fxs.length ≤ s) (hFys : fys.length ≤ s)
    (hFx₀ : GensData.denote N fxs ≤ G₀) (hFy₀ : GensData.denote N fys ≤ G₀)
    {Φx Φy : List ℕ} (hΦxn : Φx.Nodup) (hΦxl : ∀ i ∈ Φx, i < N - n) (hΦyn : Φy.Nodup)
    (hΦyl : ∀ i ∈ Φy, i < N - n)
    (hΦx : IsInvariant (GensData.denote N fxs) {u | u.val ∈ ptsD n Φx})
    (hΦy : IsInvariant (GensData.denote N fys) {u | u.val ∈ ptsD n Φy})
    (hjx : degD X.O N n (N, fxs, ex) Φx - 1 + 2 ≤ Φx.length)
    (hjy : degD X.O N n (N, fys, ey) Φy - 1 + 2 ≤ Φy.length) {Z : ℕ}
    (hZx : ∀ Sl ∈ tuplesD Φx (degD X.O N n (N, fxs, ex) Φx - 1),
      ∀ ab ∈ pairsD (phiSD (N - n) Φx Sl).length,
        sojSz (phiSD (N - n) Φx Sl).length (wlColOf X.O N n (N, fxs, ex) Φx Sl ab.1 ab.2) ≤ Z)
    (hZy : ∀ Sl ∈ tuplesD Φy (degD X.O N n (N, fys, ey) Φy - 1),
      ∀ ab ∈ pairsD (phiSD (N - n) Φy Sl).length,
        sojSz (phiSD (N - n) Φy Sl).length (wlColOf X.O N n (N, fys, ey) Φy Sl ab.1 ab.2) ≤ Z)
    {X₀ : OutD}
    (hfirst : firstLeafD X.O N n (N, fxs, ex) Φx (degD X.O N n (N, fxs, ex) Φx - 1) = some X₀)
    (hXv : OutValid (N - n) X₀)
    (hYv : ∀ Y ∈ allLeavesD X.O N n (N, fys, ey) Φy (degD X.O N n (N, fys, ey) Φy - 1),
      OutValid (N - n) Y)
    (hdiff : degD X.O N n (N, fxs, ex) Φx ≠ degD X.O N n (N, fys, ey) Φy →
      iso (w.denote N) 1 (GensData.denote N gs) (xy.1.denote N) (xy.2.denote N) = ∅)
    (halign : degD X.O N n (N, fxs, ex) Φx = degD X.O N n (N, fys, ey) Φy →
      ∀ g ∈ iso (w.denote N) 1 (GensData.denote N gs) (xy.1.denote N) (xy.2.denote N),
        ∃ Y ∈ allLeavesD X.O N n (N, fys, ey) Φy (degD X.O N n (N, fys, ey) Φy - 1),
          ∃ h : g ∈ GensData.denote N gs,
            baseHom _ n hG ⟨g, h⟩ • decodeOut (N - n) X₀ = decodeOut (N - n) Y)
    {Bg BgP Bmem Bk Bl Bg1 Bgen Cb : ℕ}
    (hBg : ∀ M ≤ N - n, ∀ gs' : GensData, GensData.AllValid M gs' → gs'.length ≤ s →
      X.B.call GroupOp.generate (M, gs') (X.O.run GroupOp.generate (M, gs')) ≤ Bg)
    (hBgP : X.B.call GroupOp.generate (N - n, gs.map (baseD n N))
      (X.O.run GroupOp.generate (N - n, gs.map (baseD n N))) ≤ BgP)
    (hBmem : ∀ g : PermData, g.Valid (N - n) → X.B.call GroupOp.mem (pModel X.O n (N, gs, d), g)
      (X.O.run GroupOp.mem (pModel X.O n (N, gs, d), g)) ≤ Bmem)
    (hBk : X.B.call GroupOp.kernel ((N, gs, d), baseWin n N) (kerModel X.O n (N, gs, d)) ≤ Bk)
    (hBl : ∀ π : PermData, X.B.call GroupOp.lift ((N, gs, d), (baseWin n N, π))
      (liftModel X.O n (N, gs, d) π) ≤ Bl)
    (hBg1 : X.B.call GroupOp.generate
      (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d)) (outGensD (N - n) X₀))).map
        (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
      (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
        (outGensD (N - n) X₀)))) ≤ Bg1)
    (hBgen : ∀ gs' : GensData, GensData.AllValid N gs' →
      gs'.length ≤ c2bR N n Φy.length (degD X.O N n (N, fys, ey) Φy - 1) Z * (s + 1) →
      GensData.denote N gs' ≤ GensData.denote N gs →
      X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ Bgen)
    {sub : InstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)}
    (hsub : SubSolves X body DV sub (fun I => I.1 = xy ∧ I.2.1 = w ∧
      I.2.2.2 = preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
        (outGensD (N - n) X₀))) ∧ I.Valid DV) (fun _ => Cb) s) :
    ∃ ans : AnswerData D,
      RunsWithin X body
        (Case2b.case2bProg sub n xy w (N, gs, d) (N, fxs, ex) (N, fys, ey) Φx Φy) ans
        (c2bCost n N s gs.length Φx.length Φy.length (degD X.O N n (N, fxs, ex) Φx - 1)
          (outGensD (N - n) X₀).length B.Bstab Bg Z BgP Bmem Bk Bl Bg1 Bgen Cb
          (fun M => (Bm M).Borb) (fun M => (Bm M).Bstab) (fun M => (Bm M).Btr)) ∧
      AnsOK DV N (w.denote N) 1 (GensData.denote N gs) (xy.1.denote N) (xy.2.denote N) ans ∧
      ∀ sGen, (∀ gs', GensData.AllValid N gs' → GensData.denote N gs' ≤ GensData.denote N gs →
          (X.O.run GroupOp.generate (N, gs')).2.1.length ≤ sGen) →
        ∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sGen := by
  have hOd : MeetsContractOn DV degOps X.O := fun op x h hp => hO op x (Or.inl h) hp
  have hPd : ∀ op x, degOps op → GroupPre DV op x → X.Pre op x := fun op x h hp =>
    hPre op x (Or.inl h) hp
  have hOc := cp2_choiceOps_of_deg hOd
  have hPc : ∀ op x, choiceOps op → GroupPre DV op x → X.Pre op x := fun op x h hp =>
    hPre op x (Or.inl (Or.inl h)) hp
  have hOa : MeetsContractOn DV alignOps X.O := fun op x h hp => hO op x (Or.inr h) hp
  have hPa : ∀ op x, alignOps op → GroupPre DV op x → X.Pre op x := fun op x h hp =>
    hPre op x (Or.inr h) hp
  have hdx := RunsWithin.degProg_le (body := body) hOd hPd B Bm hFxv hFxs hFx₀ hΦxn hΦxl hΦx hBg
  have hdy := RunsWithin.degProg_le (body := body) hOd hPd B Bm hFyv hFys hFy₀ hΦyn hΦyl hΦy hBg
  set dx := degD X.O N n (N, fxs, ex) Φx with hdxdef
  set dy := degD X.O N n (N, fys, ey) Φy with hdydef
  by_cases hxy : dx = dy
  · -- the aligned branch
    rw [← hxy] at hYv hZy halign hBgen hjy
    set j := dx - 1 with hj
    have hfl := RunsWithin.firstLeafProg_le (body := body) hOc hPc B Bm hFxv hFxs hFx₀ hΦxn hΦxl
      hΦx (j := j) hjx hBg hZx
    rw [hfirst] at hfl
    have hal := RunsWithin.allLeavesProg_le (body := body) hOc hPc B Bm hFyv hFys hFy₀ hΦyn hΦyl
      hΦy (j := j) (by omega) hBg hZy
    set Ys := allLeavesD X.O N n (N, fys, ey) Φy j with hYs
    have hmL : N - n ≤ leafB (N - n) := by
      rw [leafB]
      omega
    have hspec : (outOps (N - n)).Spec fun o => OutValid (N - n) o ∧ outSize o ≤ leafB (N - n) :=
      cp2_spec_mono (outOps_spec (N - n)) fun _ h => h.1
    have hgensP : ∀ o, OutValid (N - n) o ∧ outSize o ≤ leafB (N - n) →
        RunsWithin X body (Case2b.outGensProg (N - n) o) ((outOps (N - n)).gens o)
          (outGensCost (N - n) (leafB (N - n)) (leafB (N - n))) := fun o ho =>
      RunsWithin.outGensProg (N - n) o (fun _ v => (outSize_blk o v).trans ho.2) hmL
        fun _ => cp2_jbound_le ho.2
    have hisoP : ∀ o o', OutValid (N - n) o ∧ outSize o ≤ leafB (N - n) →
        OutValid (N - n) o' ∧ outSize o' ≤ leafB (N - n) →
        RunsWithin X body (Case2b.outIsoProg (N - n) o o') ((outOps (N - n)).iso o o')
          (outIsoCost (N - n) (leafB (N - n)) (leafB (N - n)) (leafB (N - n))) := fun o o' ho ho' =>
      RunsWithin.outIsoProg (N - n) o o' (fun _ v => (outSize_blk o v).trans ho.2)
        (fun _ v => (outSize_blk o' v).trans ho'.2) hmL (fun _ => cp2_jbound_le ho.2)
        fun _ => cp2_jbound_le ho'.2
    have hX : OutValid (N - n) X₀ ∧ outSize X₀ ≤ leafB (N - n) := ⟨hXv, outSize_firstLeafD hfirst⟩
    have hYv' : ∀ Y ∈ Ys, OutValid (N - n) Y ∧ outSize Y ≤ leafB (N - n) := fun Y hY =>
      ⟨hYv Y hY, outSize_allLeavesD Y hY⟩
    have hYlen : Ys.length ≤ c2bR N n Φy.length j Z := by
      refine length_allLeavesD_le fun Sl hSl ab hab => ?_
      unfold choiceLeavesD
      rw [List.length_map]
      exact (length_leavesOfD_le _ _).trans (Nat.add_le_add_right (hZy Sl hSl ab hab) 1)
    have hBgen' : ∀ gs' : GensData, GensData.AllValid N gs' → gs'.length ≤ Ys.length * (s + 1) →
        GensData.denote N gs' ≤ GensData.denote N gs →
        X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ Bgen :=
      fun gs' hv hl hle => hBgen gs' hv (hl.trans (Nat.mul_le_mul_right _ hYlen)) hle
    obtain ⟨ans, hrun, hok, hgen⟩ := RunsWithin.alignProg (body := body) (τ := outTy)
      (O := Option (Out (Fin (N - n)))) hOa hPa hGv hG halt (S := outOps (N - n)) hspec hgensP
      hisoP hX hYv' hw hWG (halign rfl) hBgP hBmem hBk hBl hBg1 hBgen' hsub
    refine ⟨ans, ?_, hok, hgen⟩
    apply RunsWithin.mono
    case h =>
      unfold Case2b.case2bProg
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step hdx
      run_step hdy
      run_step (RunsWithin.prim _ _)
      run_with RunsWithin.ite_pos (show (dx == dy) = true by simp [hxy]) _
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step hfl
      run_with RunsWithin.caseOption_some _
      run_step hal
      exact hrun
    case hc =>
      have := cp2_alignCost_mono (n := n) (N := N) (g := gs.length)
        (k := ((outOps (N - n)).gens X₀).length)
        (cG := outGensCost (N - n) (leafB (N - n)) (leafB (N - n)))
        (cI := outIsoCost (N - n) (leafB (N - n)) (leafB (N - n)) (leafB (N - n))) (BgP := BgP)
        (Bmem := Bmem) (Bk := Bk) (Bl := Bl)
        (Bg1 := Bg1) (Bgen := Bgen) (Cb := Cb) (s := s) hYlen
      have e : alignCost n N gs.length ((outOps (N - n)).gens X₀).length (c2bR N n Φy.length j Z)
          (outGensCost (N - n) (leafB (N - n)) (leafB (N - n)))
          (outIsoCost (N - n) (leafB (N - n)) (leafB (N - n)) (leafB (N - n))) BgP Bmem Bk Bl Bg1
          Bgen Cb s =
          alignCost n N gs.length (outGensD (N - n) X₀).length (c2bR N n Φy.length j Z)
          (outGensCost (N - n) (leafB (N - n)) (leafB (N - n)))
          (outIsoCost (N - n) (leafB (N - n)) (leafB (N - n)) (leafB (N - n))) BgP Bmem Bk Bl Bg1
          Bgen Cb s := rfl
      simp only [Prim.cost, c2bCost]
      omega
  · -- different degrees: no isomorphism
    refine ⟨none, ?_, hdiff hxy, fun _ _ c hc => by cases hc⟩
    apply RunsWithin.mono
    case h =>
      unfold Case2b.case2bProg
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step hdx
      run_step hdy
      run_step (RunsWithin.prim _ _)
      exact RunsWithin.ite_neg (show (dx == dy) = false by simp [hxy]) (RunsWithin.prim _ _)
    case hc =>
      simp only [Prim.cost, c2bCost]
      omega

end Spec

/-! ### Canonicity -/

section Canonical

variable {N n : ℕ}

/-- **The base actions of conjugate groups are conjugate.** -/
theorem cp2_range_conj {G F F' : Subgroup (Perm (Fin N))} (hG : IsInvariant G (baseSet n N))
    (hF : IsInvariant F (baseSet n N)) (hF' : IsInvariant F' (baseSet n N)) {g : Perm (Fin N)}
    (hgG : g ∈ G) (hF'F : F' = F.map (MulAut.conj g).toMonoidHom) (h : Perm (Fin (N - n))) :
    h ∈ (baseHom F' n hF').range ↔
      (baseHom G n hG ⟨g, hgG⟩)⁻¹ * h * baseHom G n hG ⟨g, hgG⟩ ∈ (baseHom F n hF).range := by
  set σ := baseHom G n hG ⟨g, hgG⟩ with hσ
  have hfwd : ∀ j, basePos (σ j) = g (basePos j) := fun j => baseHom_apply (hG := hG) ⟨g, hgG⟩ j
  have hinv : ∀ j, basePos (σ⁻¹ j) = g⁻¹ (basePos j) := fun j => by
    rw [hσ, ← map_inv]
    exact baseHom_apply (hG := hG) ⟨g, hgG⟩⁻¹ j
  constructor
  · rintro ⟨⟨f', hf'⟩, rfl⟩
    have hf'm := hf'
    rw [hF'F] at hf'm
    obtain ⟨f, hf, rfl⟩ := Subgroup.mem_map.1 hf'm
    refine ⟨⟨f, hf⟩, Equiv.ext fun j => basePos_injective ?_⟩
    rw [baseHom_apply, Perm.mul_apply, Perm.mul_apply, hinv, baseHom_apply, hfwd]
    simp [MulAut.conj_apply, Perm.mul_apply]
  · rintro ⟨⟨f, hf⟩, hfe⟩
    have hf' : g * f * g⁻¹ ∈ F' := by
      rw [hF'F]
      exact Subgroup.mem_map.2 ⟨f, hf, rfl⟩
    refine ⟨⟨_, hf'⟩, Equiv.ext fun j => basePos_injective ?_⟩
    have hj := congrArg (fun p : Perm (Fin (N - n)) => basePos (p (σ⁻¹ j))) hfe
    simp only [Perm.mul_apply, perm_apply_inv_self, baseHom_apply, hinv] at hj
    rw [baseHom_apply]
    show g (f (g⁻¹ (basePos j))) = basePos (h j)
    rw [hj, perm_apply_inv_self]

/-- The positions of an orbit of the base action are invariant. -/
theorem cp2_inv_of_orbit {F : Subgroup (Perm (Fin N))} (hF : IsInvariant F (baseSet n N))
    {Φ : List ℕ} (hΦl : ∀ i ∈ Φ, i < N - n)
    (hΦo : ∃ γ : Fin (N - n), ∀ δ : Fin (N - n),
      δ.val ∈ Φ ↔ δ ∈ MulAction.orbit (baseHom F n hF).range γ) :
    IsInvariant F {u | u.val ∈ ptsD n Φ} := by
  obtain ⟨γ, hγ⟩ := hΦo
  intro f hf u hu
  obtain ⟨v, hv, hvu⟩ := List.mem_map.1 (show u.val ∈ ptsD n Φ from hu)
  set δ : Fin (N - n) := ⟨v, hΦl v hv⟩
  have hδ : δ ∈ MulAction.orbit (baseHom F n hF).range γ := (hγ δ).1 hv
  have h := cp2_orbit_pres (g := baseHom F n hF ⟨f, hf⟩) (MonoidHom.mem_range.2 ⟨⟨f, hf⟩, rfl⟩) hδ
  have hpos : basePos δ = u := Fin.ext hvu
  have h2 := baseHom_apply (hG := hF) ⟨f, hf⟩ δ
  rw [hpos] at h2
  show (f u).val ∈ ptsD n Φ
  have h3 : (f u).val = n + (baseHom F n hF ⟨f, hf⟩ δ).val := by
    rw [← h2]
    rfl
  rw [h3]
  exact List.mem_map_of_mem ((hγ _).2 h)

/-- **Transport of reachable leaves** along conjugate groups and translated sets
(`case2bTree_relabel'`, `reach_act`). -/
theorem cp2_reach_transport {m : ℕ} {P P' : Subgroup (Perm (Fin m))} [DecidablePred (· ∈ P)]
    [DecidablePred (· ∈ P')] (σ : Perm (Fin m)) (hP : ∀ h, h ∈ P' ↔ σ⁻¹ * h * σ ∈ P)
    {Φ Φ' : Finset (Fin m)} (hΦ : σ • Φ = Φ') (d : ℕ) {o : Option (Out (Fin m))}
    (ho : (case2bTree P Φ d).Reach o) : (case2bTree P' Φ' d).Reach (σ • o) := by
  subst hΦ
  rw [case2bTree_relabel' σ hP Φ d]
  exact (SplitJohnson.CTree.reach_act σ).2 ho

theorem cp2_mem_smul_iff {m : ℕ} (σ : Perm (Fin m)) {Φ Φ' : Finset (Fin m)} (hΦ : σ • Φ = Φ')
    (v : Fin m) : v ∈ Φ' ↔ σ⁻¹ v ∈ Φ := by
  rw [← hΦ, ← Finset.inv_smul_mem_iff, Perm.smul_def]

end Canonical

section DegreeCanonical

variable {D : Ty} {X : Ctx (groupSig D)} {DV : ℕ → GensData → D.denote → Prop}

/-- **The degree is canonical**: for conjugate base actions and translated orbits, the degree
program returns the same value. -/
theorem cp2_degD_eq (hO : MeetsContractOn DV degOps X.O)
    (hPre : ∀ op x, degOps op → GroupPre DV op x → X.Pre op x)
    {N n s : ℕ} {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N s G₀)
    {sm : ℕ → ℕ} (Bm : ∀ M, BackendBounds X DV M (sm M) ⊤)
    {fxs fys : GensData} {ex ey : D.denote} (hFxv : GroupValid DV N fxs ex)
    (hFyv : GroupValid DV N fys ey) (hFxs : fxs.length ≤ s) (hFys : fys.length ≤ s)
    (hFx₀ : GensData.denote N fxs ≤ G₀) (hFy₀ : GensData.denote N fys ≤ G₀)
    (hFxi : IsInvariant (GensData.denote N fxs) (baseSet n N))
    (hFyi : IsInvariant (GensData.denote N fys) (baseSet n N))
    {Φx Φy : List ℕ} (hΦxn : Φx.Nodup) (hΦxl : ∀ i ∈ Φx, i < N - n) (hΦyn : Φy.Nodup)
    (hΦyl : ∀ i ∈ Φy, i < N - n)
    (hΦxo : ∃ γ : Fin (N - n), ∀ δ : Fin (N - n),
      δ.val ∈ Φx ↔ δ ∈ MulAction.orbit (baseHom _ n hFxi).range γ)
    (hΦyo : ∃ γ : Fin (N - n), ∀ δ : Fin (N - n),
      δ.val ∈ Φy ↔ δ ∈ MulAction.orbit (baseHom _ n hFyi).range γ)
    (σ : Perm (Fin (N - n)))
    (hP : ∀ h, h ∈ (baseHom _ n hFyi).range ↔ σ⁻¹ * h * σ ∈ (baseHom _ n hFxi).range)
    (hΦ : σ • setOf (N - n) Φx = setOf (N - n) Φy) :
    degD X.O N n (N, fxs, ex) Φx = degD X.O N n (N, fys, ey) Φy := by
  obtain ⟨hlx, htx, hnx⟩ := degD_spec hO hPre B hFxv hFxs hFx₀ hFxi hΦxn hΦxl
    (cp2_inv_of_orbit hFxi hΦxl hΦxo) (Bm _)
  obtain ⟨hly, hty, hny⟩ := degD_spec hO hPre B hFyv hFys hFy₀ hFyi hΦyn hΦyl
    (cp2_inv_of_orbit hFyi hΦyl hΦyo) (Bm _)
  have hlen : Φx.length = Φy.length := by
    rw [← card_setOf hΦxn hΦxl, ← card_setOf hΦyn hΦyl, ← hΦ, Finset.card_smul_finset]
  obtain ⟨γ, hγ⟩ := hΦyo
  have hpres : ∀ p ∈ (baseHom _ n hFyi).range, ∀ x ∈ setOf (N - n) Φy, p x ∈ setOf (N - n) Φy :=
    fun p hp x hx => by
      rw [mem_setOf, hγ] at hx ⊢
      exact cp2_orbit_pres hp hx
  have hcard : (setOf (N - n) Φy).card = Φy.length := card_setOf hΦyn hΦyl
  refine cp2_deg_unique (L := Φx.length)
    (fun k => (cp2_tupTrans_conj σ hP (cp2_mem_smul_iff σ hΦ) k).symm)
    (fun k k' h hk hk' => cp2_tupTrans_mono hpres h hk (by omega)) hlx (by omega) htx hnx hty
    (fun h => hny (by omega))

end DegreeCanonical

/-! ### Case 2b with canonical `F` and `Φ` -/

section CanonicalSpec

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}

/-- **Case 2b, canonical form.** `F` is a canonical map of the strings into subgroups of `G`
(local on the window, `F (relabel g x) = g F(x) g⁻¹`), `Fx`, `Fy` represent `F(x)`, `F(y)`, and
`Φx`, `Φy` list the orbits of more than half of the base of `ψ(F(x))`, `ψ(F(y))`, on which these
are not giants. The validity of the leaves and the alignment hypothesis come from the tree
(`Link.lean`: `allLeavesD_leafMs`, `firstLeafD_reach`, `allLeavesD_valid`,
`firstLeafD_valid`; canonicity by
`largeOrbit_canonical`, `cp2_range_conj` and `case2bTree_relabel'`), and the degrees agree
whenever an isomorphism exists (`cp2_degD_eq`). The answer is correct for `G`. -/
theorem RunsWithin.case2bProg_canonical (hO : MeetsContractOn DV c2bOps X.O)
    (hPre : ∀ op x, c2bOps op → GroupPre DV op x → X.Pre op x)
    {n N s : ℕ} {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N s G₀)
    {sm : ℕ → ℕ} (Bm : ∀ M, BackendBounds X DV M (sm M) ⊤)
    {gs : GensData} {d : D.denote} (hGv : GroupValid DV N gs d)
    (hG : IsInvariant (GensData.denote N gs) (baseSet n N))
    (halt : alternatingGroup (Fin (N - n)) ≤ (baseHom _ n hG).range)
    {xy : StrData × StrData} {w : WinData} (hw : w.Valid N)
    (hWG : IsInvariant (GensData.denote N gs) (w.denote N))
    {Fmap : (Fin N → ℕ) → Subgroup (Perm (Fin N))}
    (hloc : ∀ x x', (∀ u ∈ w.denote N, x u = x' u) → Fmap x = Fmap x')
    (heq : ∀ g ∈ GensData.denote N gs, ∀ x,
      Fmap (relabel g x) = (Fmap x).map (MulAut.conj g).toMonoidHom)
    {fxs fys : GensData} {ex ey : D.denote} (hFxv : GroupValid DV N fxs ex)
    (hFyv : GroupValid DV N fys ey) (hFxs : fxs.length ≤ s) (hFys : fys.length ≤ s)
    (hFx₀ : GensData.denote N fxs ≤ G₀) (hFy₀ : GensData.denote N fys ≤ G₀)
    (hFxe : GensData.denote N fxs = Fmap (xy.1.denote N))
    (hFye : GensData.denote N fys = Fmap (xy.2.denote N))
    (hFxi : IsInvariant (GensData.denote N fxs) (baseSet n N))
    (hFyi : IsInvariant (GensData.denote N fys) (baseSet n N))
    {Φx Φy : List ℕ} (hΦxn : Φx.Nodup) (hΦxl : ∀ i ∈ Φx, i < N - n)
    (hΦx2 : N - n < 2 * Φx.length)
    (hΦxo : ∃ γ : Fin (N - n), γ.val ∈ Φx ∧ ∀ δ : Fin (N - n),
      δ.val ∈ Φx ↔ δ ∈ MulAction.orbit (baseHom _ n hFxi).range γ)
    (hΦyn : Φy.Nodup) (hΦyl : ∀ i ∈ Φy, i < N - n) (hΦy2 : N - n < 2 * Φy.length)
    (hΦyo : ∃ γ : Fin (N - n), γ.val ∈ Φy ∧ ∀ δ : Fin (N - n),
      δ.val ∈ Φy ↔ δ ∈ MulAction.orbit (baseHom _ n hFyi).range γ)
    (hngx : ¬ TupTrans (baseHom _ n hFxi).range (setOf (N - n) Φx) (Φx.length - 2))
    (hngy : ¬ TupTrans (baseHom _ n hFyi).range (setOf (N - n) Φy) (Φy.length - 2)) {Z : ℕ}
    (hZx : ∀ Sl ∈ tuplesD Φx (degD X.O N n (N, fxs, ex) Φx - 1),
      ∀ ab ∈ pairsD (phiSD (N - n) Φx Sl).length,
        sojSz (phiSD (N - n) Φx Sl).length (wlColOf X.O N n (N, fxs, ex) Φx Sl ab.1 ab.2) ≤ Z)
    (hZy : ∀ Sl ∈ tuplesD Φy (degD X.O N n (N, fys, ey) Φy - 1),
      ∀ ab ∈ pairsD (phiSD (N - n) Φy Sl).length,
        sojSz (phiSD (N - n) Φy Sl).length (wlColOf X.O N n (N, fys, ey) Φy Sl ab.1 ab.2) ≤ Z)
    {X₀ : OutD}
    (hfirst : firstLeafD X.O N n (N, fxs, ex) Φx (degD X.O N n (N, fxs, ex) Φx - 1) = some X₀)
    {Bg BgP Bmem Bk Bl Bg1 Bgen Cb : ℕ}
    (hBg : ∀ M ≤ N - n, ∀ gs' : GensData, GensData.AllValid M gs' → gs'.length ≤ s →
      X.B.call GroupOp.generate (M, gs') (X.O.run GroupOp.generate (M, gs')) ≤ Bg)
    (hBgP : X.B.call GroupOp.generate (N - n, gs.map (baseD n N))
      (X.O.run GroupOp.generate (N - n, gs.map (baseD n N))) ≤ BgP)
    (hBmem : ∀ g : PermData, g.Valid (N - n) → X.B.call GroupOp.mem (pModel X.O n (N, gs, d), g)
      (X.O.run GroupOp.mem (pModel X.O n (N, gs, d), g)) ≤ Bmem)
    (hBk : X.B.call GroupOp.kernel ((N, gs, d), baseWin n N) (kerModel X.O n (N, gs, d)) ≤ Bk)
    (hBl : ∀ π : PermData, X.B.call GroupOp.lift ((N, gs, d), (baseWin n N, π))
      (liftModel X.O n (N, gs, d) π) ≤ Bl)
    (hBg1 : X.B.call GroupOp.generate
      (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d)) (outGensD (N - n) X₀))).map
        (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
      (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
        (outGensD (N - n) X₀)))) ≤ Bg1)
    (hBgen : ∀ gs' : GensData, GensData.AllValid N gs' →
      gs'.length ≤ c2bR N n Φy.length (degD X.O N n (N, fys, ey) Φy - 1) Z * (s + 1) →
      GensData.denote N gs' ≤ GensData.denote N gs →
      X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ Bgen)
    {sub : InstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)}
    (hsub : SubSolves X body DV sub (fun I => I.1 = xy ∧ I.2.1 = w ∧
      I.2.2.2 = preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
        (outGensD (N - n) X₀))) ∧ I.Valid DV) (fun _ => Cb) s) :
    ∃ ans : AnswerData D,
      RunsWithin X body
        (Case2b.case2bProg sub n xy w (N, gs, d) (N, fxs, ex) (N, fys, ey) Φx Φy) ans
        (c2bCost n N s gs.length Φx.length Φy.length (degD X.O N n (N, fxs, ex) Φx - 1)
          (outGensD (N - n) X₀).length B.Bstab Bg Z BgP Bmem Bk Bl Bg1 Bgen Cb
          (fun M => (Bm M).Borb) (fun M => (Bm M).Bstab) (fun M => (Bm M).Btr)) ∧
      AnsOK DV N (w.denote N) 1 (GensData.denote N gs) (xy.1.denote N) (xy.2.denote N) ans ∧
      ∀ sGen, (∀ gs', GensData.AllValid N gs' → GensData.denote N gs' ≤ GensData.denote N gs →
          (X.O.run GroupOp.generate (N, gs')).2.1.length ≤ sGen) →
        ∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sGen := by
  classical
  have hOd : MeetsContractOn DV degOps X.O := fun op x h hp => hO op x (Or.inl h) hp
  have hPd : ∀ op x, degOps op → GroupPre DV op x → X.Pre op x := fun op x h hp =>
    hPre op x (Or.inl h) hp
  have hOc := cp2_choiceOps_of_deg hOd
  obtain ⟨γx, hγxm, hγx⟩ := hΦxo
  obtain ⟨γy, hγym, hγy⟩ := hΦyo
  have hΦx := cp2_inv_of_orbit hFxi hΦxl ⟨γx, hγx⟩
  have hΦy := cp2_inv_of_orbit hFyi hΦyl ⟨γy, hγy⟩
  obtain ⟨h1x, Hx⟩ := case2bHyp_degD hOd hPd B hFxv hFxs hFx₀ hFxi hΦxn hΦxl hΦx (Bm _)
    ⟨γx, hγx⟩ hngx
  obtain ⟨h1y, Hy⟩ := case2bHyp_degD hOd hPd B hFyv hFys hFy₀ hFyi hΦyn hΦyl hΦy (Bm _)
    ⟨γy, hγy⟩ hngy
  set dx := degD X.O N n (N, fxs, ex) Φx with hdx
  set dy := degD X.O N n (N, fys, ey) Φy with hdy
  have Hx' : Case2bHyp (baseHom _ n hFxi).range (setOf (N - n) Φx) (dx - 1 + 1) := by
    rw [Nat.sub_add_cancel h1x]
    exact Hx
  have Hy' : Case2bHyp (baseHom _ n hFyi).range (setOf (N - n) Φy) (dy - 1 + 1) := by
    rw [Nat.sub_add_cancel h1y]
    exact Hy
  have hjx : dx - 1 + 2 ≤ Φx.length := by
    have := Hx.size
    rw [card_setOf hΦxn hΦxl] at this
    omega
  have hjy : dy - 1 + 2 ≤ Φy.length := by
    have := Hy.size
    rw [card_setOf hΦyn hΦyl] at this
    omega
  have hYv := allLeavesD_valid (F := (N, fys, ey)) hOc rfl hFyv hFyi hΦyn hΦyl Hy'
  have hXv : OutValid (N - n) X₀ :=
    firstLeafD_valid (F := (N, fxs, ex)) hOc rfl hFxv hFxi hΦxn hΦxl Hx' hfirst
  -- an isomorphism conjugates `F` and translates `Φ`
  have hconj : ∀ g ∈ iso (w.denote N) 1 (GensData.denote N gs) (xy.1.denote N) (xy.2.denote N),
      ∃ hgG : g ∈ GensData.denote N gs,
        (∀ h, h ∈ (baseHom _ n hFyi).range ↔ (baseHom _ n hG ⟨g, hgG⟩)⁻¹ * h *
          baseHom _ n hG ⟨g, hgG⟩ ∈ (baseHom _ n hFxi).range) ∧
        baseHom _ n hG ⟨g, hgG⟩ • setOf (N - n) Φx = setOf (N - n) Φy := by
    intro g hg
    have hgG : g ∈ GensData.denote N gs := (mem_iso_one.1 hg).1
    have hy : GensData.denote N fys = (GensData.denote N fxs).map (MulAut.conj g).toMonoidHom := by
      rw [hFye, hFxe, ← heq g hgG _]
      exact (hloc _ _ (Recursion.relabel_eq_on_of_mem_iso hWG hg)).symm
    exact ⟨hgG, cp2_range_conj hG hFxi hFyi hgG hy, Giant.largeOrbit_canonical hG hWG hloc heq
      hFxe hFye hFxi hFyi hg hΦxn hΦxl hΦx2 ⟨γx, hγxm, hγx⟩ hΦyn hΦyl hΦy2 ⟨γy, hγym, hγy⟩⟩
  refine RunsWithin.case2bProg hO hPre B Bm hGv hG halt hw hWG hFxv hFyv hFxs hFys hFx₀ hFy₀
    hΦxn hΦxl hΦyn hΦyl hΦx hΦy hjx hjy hZx hZy hfirst hXv hYv ?_ ?_ hBg hBgP hBmem hBk hBl hBg1
    hBgen hsub
  · -- the degrees agree when there is an isomorphism
    intro hne
    by_contra hiso
    obtain ⟨g, hg⟩ := Set.nonempty_iff_ne_empty.2 hiso
    obtain ⟨hgG, hP, hΦ⟩ := hconj g hg
    exact hne (cp2_degD_eq hOd hPd B Bm hFxv hFyv hFxs hFys hFx₀ hFy₀ hFxi hFyi hΦxn hΦxl hΦyn
      hΦyl ⟨γx, hγx⟩ ⟨γy, hγy⟩ _ hP hΦ)
  · -- the alignment
    intro hxy g hg
    obtain ⟨hgG, hP, hΦ⟩ := hconj g hg
    have hreach := firstLeafD_reach (F := (N, fxs, ex)) hOc rfl hFxv hFxi hΦxn hΦxl Hx' hfirst
    have hreach' := cp2_reach_transport _ hP hΦ _ hreach
    rw [show dx - 1 + 1 = dy - 1 + 1 from congrArg (fun k => k - 1 + 1) hxy, ← CTree.mem_leafMs,
      ← allLeavesD_leafMs (F := (N, fys, ey)) hOc rfl hFyv hFyi hΦyn hΦyl Hy',
      Multiset.mem_coe] at hreach'
    obtain ⟨Y, hY, hYe⟩ := List.mem_map.1 hreach'
    exact ⟨Y, hY, hgG, hYe.symm⟩

/-- **Case 2b, canonical form, with the tree's bounds.** As `RunsWithin.case2bProg_canonical`,
with the `soj` sizes bounded by `sojZ (N - n)` (`sojSz_le`) and the first leaf `X₀` supplied by
the tree (`firstLeafD_ne_none`): the charges of Align and the sub-solver are assumed for the
first leaf, whatever it is. -/
theorem RunsWithin.case2bProg_canonical' (hO : MeetsContractOn DV c2bOps X.O)
    (hPre : ∀ op x, c2bOps op → GroupPre DV op x → X.Pre op x)
    {n N s : ℕ} {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N s G₀)
    {sm : ℕ → ℕ} (Bm : ∀ M, BackendBounds X DV M (sm M) ⊤)
    {gs : GensData} {d : D.denote} (hGv : GroupValid DV N gs d)
    (hG : IsInvariant (GensData.denote N gs) (baseSet n N))
    (halt : alternatingGroup (Fin (N - n)) ≤ (baseHom _ n hG).range)
    {xy : StrData × StrData} {w : WinData} (hw : w.Valid N)
    (hWG : IsInvariant (GensData.denote N gs) (w.denote N))
    {Fmap : (Fin N → ℕ) → Subgroup (Perm (Fin N))}
    (hloc : ∀ x x', (∀ u ∈ w.denote N, x u = x' u) → Fmap x = Fmap x')
    (heq : ∀ g ∈ GensData.denote N gs, ∀ x,
      Fmap (relabel g x) = (Fmap x).map (MulAut.conj g).toMonoidHom)
    {fxs fys : GensData} {ex ey : D.denote} (hFxv : GroupValid DV N fxs ex)
    (hFyv : GroupValid DV N fys ey) (hFxs : fxs.length ≤ s) (hFys : fys.length ≤ s)
    (hFx₀ : GensData.denote N fxs ≤ G₀) (hFy₀ : GensData.denote N fys ≤ G₀)
    (hFxe : GensData.denote N fxs = Fmap (xy.1.denote N))
    (hFye : GensData.denote N fys = Fmap (xy.2.denote N))
    (hFxi : IsInvariant (GensData.denote N fxs) (baseSet n N))
    (hFyi : IsInvariant (GensData.denote N fys) (baseSet n N))
    {Φx Φy : List ℕ} (hΦxn : Φx.Nodup) (hΦxl : ∀ i ∈ Φx, i < N - n)
    (hΦx2 : N - n < 2 * Φx.length)
    (hΦxo : ∃ γ : Fin (N - n), γ.val ∈ Φx ∧ ∀ δ : Fin (N - n),
      δ.val ∈ Φx ↔ δ ∈ MulAction.orbit (baseHom _ n hFxi).range γ)
    (hΦyn : Φy.Nodup) (hΦyl : ∀ i ∈ Φy, i < N - n) (hΦy2 : N - n < 2 * Φy.length)
    (hΦyo : ∃ γ : Fin (N - n), γ.val ∈ Φy ∧ ∀ δ : Fin (N - n),
      δ.val ∈ Φy ↔ δ ∈ MulAction.orbit (baseHom _ n hFyi).range γ)
    (hngx : ¬ TupTrans (baseHom _ n hFxi).range (setOf (N - n) Φx) (Φx.length - 2))
    (hngy : ¬ TupTrans (baseHom _ n hFyi).range (setOf (N - n) Φy) (Φy.length - 2))
    {Bg BgP Bmem Bk Bl Bg1 Bgen Cb : ℕ}
    (hBg : ∀ M ≤ N - n, ∀ gs' : GensData, GensData.AllValid M gs' → gs'.length ≤ s →
      X.B.call GroupOp.generate (M, gs') (X.O.run GroupOp.generate (M, gs')) ≤ Bg)
    (hBgP : X.B.call GroupOp.generate (N - n, gs.map (baseD n N))
      (X.O.run GroupOp.generate (N - n, gs.map (baseD n N))) ≤ BgP)
    (hBmem : ∀ g : PermData, g.Valid (N - n) → X.B.call GroupOp.mem (pModel X.O n (N, gs, d), g)
      (X.O.run GroupOp.mem (pModel X.O n (N, gs, d), g)) ≤ Bmem)
    (hBk : X.B.call GroupOp.kernel ((N, gs, d), baseWin n N) (kerModel X.O n (N, gs, d)) ≤ Bk)
    (hBl : ∀ π : PermData, X.B.call GroupOp.lift ((N, gs, d), (baseWin n N, π))
      (liftModel X.O n (N, gs, d) π) ≤ Bl)
    (hBg1 : ∀ X₀ : OutD,
      firstLeafD X.O N n (N, fxs, ex) Φx (degD X.O N n (N, fxs, ex) Φx - 1) = some X₀ →
      X.B.call GroupOp.generate
        (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d)) (outGensD (N - n) X₀))).map
          (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
        (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (outGensD (N - n) X₀)))) ≤ Bg1)
    (hBgen : ∀ gs' : GensData, GensData.AllValid N gs' →
      gs'.length ≤ c2bR N n Φy.length (degD X.O N n (N, fys, ey) Φy - 1) (sojZ (N - n)) *
        (s + 1) →
      GensData.denote N gs' ≤ GensData.denote N gs →
      X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ Bgen)
    {sub : InstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)}
    (hsub : ∀ X₀ : OutD,
      firstLeafD X.O N n (N, fxs, ex) Φx (degD X.O N n (N, fxs, ex) Φx - 1) = some X₀ →
      SubSolves X body DV sub (fun I => I.1 = xy ∧ I.2.1 = w ∧
        I.2.2.2 = preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (outGensD (N - n) X₀))) ∧ I.Valid DV) (fun _ => Cb) s) :
    ∃ X₀ : OutD,
      firstLeafD X.O N n (N, fxs, ex) Φx (degD X.O N n (N, fxs, ex) Φx - 1) = some X₀ ∧
      ∃ ans : AnswerData D,
        RunsWithin X body
          (Case2b.case2bProg sub n xy w (N, gs, d) (N, fxs, ex) (N, fys, ey) Φx Φy) ans
          (c2bCost n N s gs.length Φx.length Φy.length (degD X.O N n (N, fxs, ex) Φx - 1)
            (outGensD (N - n) X₀).length B.Bstab Bg (sojZ (N - n)) BgP Bmem Bk Bl Bg1 Bgen Cb
            (fun M => (Bm M).Borb) (fun M => (Bm M).Bstab) (fun M => (Bm M).Btr)) ∧
        AnsOK DV N (w.denote N) 1 (GensData.denote N gs) (xy.1.denote N) (xy.2.denote N) ans ∧
        ∀ sGen, (∀ gs', GensData.AllValid N gs' →
            GensData.denote N gs' ≤ GensData.denote N gs →
            (X.O.run GroupOp.generate (N, gs')).2.1.length ≤ sGen) →
          ∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sGen := by
  classical
  have hOd : MeetsContractOn DV degOps X.O := fun op x h hp => hO op x (Or.inl h) hp
  have hPd : ∀ op x, degOps op → GroupPre DV op x → X.Pre op x := fun op x h hp =>
    hPre op x (Or.inl h) hp
  have hOc := cp2_choiceOps_of_deg hOd
  obtain ⟨γx, hγxm, hγx⟩ := hΦxo
  obtain ⟨γy, hγym, hγy⟩ := hΦyo
  obtain ⟨h1x, Hx⟩ := case2bHyp_degD hOd hPd B hFxv hFxs hFx₀ hFxi hΦxn hΦxl
    (cp2_inv_of_orbit hFxi hΦxl ⟨γx, hγx⟩) (Bm _) ⟨γx, hγx⟩ hngx
  obtain ⟨h1y, Hy⟩ := case2bHyp_degD hOd hPd B hFyv hFys hFy₀ hFyi hΦyn hΦyl
    (cp2_inv_of_orbit hFyi hΦyl ⟨γy, hγy⟩) (Bm _) ⟨γy, hγy⟩ hngy
  have Hx' : Case2bHyp (baseHom _ n hFxi).range (setOf (N - n) Φx)
      (degD X.O N n (N, fxs, ex) Φx - 1 + 1) := by
    rw [Nat.sub_add_cancel h1x]
    exact Hx
  have Hy' : Case2bHyp (baseHom _ n hFyi).range (setOf (N - n) Φy)
      (degD X.O N n (N, fys, ey) Φy - 1 + 1) := by
    rw [Nat.sub_add_cancel h1y]
    exact Hy
  obtain ⟨X₀, hfirst⟩ := Option.ne_none_iff_exists'.1
    (firstLeafD_ne_none (F := (N, fxs, ex)) hOc rfl hFxv hFxi hΦxn hΦxl Hx')
  exact ⟨X₀, hfirst, RunsWithin.case2bProg_canonical hO hPre B Bm hGv hG halt hw hWG hloc heq
    hFxv hFyv hFxs hFys hFx₀ hFy₀ hFxe hFye hFxi hFyi hΦxn hΦxl hΦx2 ⟨γx, hγxm, hγx⟩ hΦyn hΦyl
    hΦy2 ⟨γy, hγym, hγy⟩ hngx hngy
    (fun Sl hSl ab hab => sojSz_le (F := (N, fxs, ex)) hOc rfl hFxv hFxi hΦxl Hx' hSl hab)
    (fun Sl hSl ab hab => sojSz_le (F := (N, fys, ey)) hOc rfl hFyv hFyi hΦyl Hy' hSl hab)
    hfirst hBg hBgP hBmem hBk hBl (hBg1 X₀ hfirst) hBgen (hsub X₀ hfirst)⟩

end CanonicalSpec

/-! ### The charges of the Schreier–Sims backend -/

section SimsCharges

/-- **The generation charges of Case 2b hold for the Schreier–Sims backend**, with explicit
values: `genCost (N - n) s + 2` for the generation at any degree `M ≤ N - n` of at most `s`
restricted generators (`hBg` of `RunsWithin.case2bProg`), and `genCost N (R (s + 1)) + 2` for
Align's combination of at most `R (s + 1)` generators (`hBgen`). Both premises bound the
number of generators. -/
theorem c2b_ss_charges {N n s R : ℕ} :
    (∀ M ≤ N - n, ∀ gs' : GensData, GensData.AllValid M gs' → gs'.length ≤ s →
      ssCtx.B.call GroupOp.generate (M, gs') (ssCtx.O.run GroupOp.generate (M, gs')) ≤
        genCost (N - n) s + 2) ∧
    (∀ gs' : GensData, GensData.AllValid N gs' → gs'.length ≤ R * (s + 1) →
      ssCtx.B.call GroupOp.generate (N, gs') (ssCtx.O.run GroupOp.generate (N, gs')) ≤
        genCost N (R * (s + 1)) + 2) := by
  refine ⟨fun M hM gs' _ hl => ?_, fun gs' _ hl => ?_⟩
  · change genCost M gs'.length + 2 ≤ genCost (N - n) s + 2
    exact Nat.add_le_add_right (genCost_mono₂ hM hl) 2
  · change genCost N gs'.length + 2 ≤ genCost N (R * (s + 1)) + 2
    exact Nat.add_le_add_right (genCost_mono hl) 2

end SimsCharges

/-! ### Well-formedness -/

section Wf

variable {D : Ty} {rec : Ty × Ty} {var₁ var₂ : Ty → Type} {r : Bool} {Γ : WfCtx var₁ var₂}

theorem wf_degProg {N₁ n₁ : var₁ .nat} {N₂ n₂ : var₂ .nat} {F₁ : var₁ (Ty.group D)}
    {F₂ : var₂ (Ty.group D)} {Φ₁ : var₁ (.list .nat)} {Φ₂ : var₂ (.list .nat)}
    (hN : ⟨.nat, N₁, N₂⟩ ∈ Γ) (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (hF : ⟨Ty.group D, F₁, F₂⟩ ∈ Γ)
    (hΦ : ⟨.list .nat, Φ₁, Φ₂⟩ ∈ Γ) :
    Prog.Wf (S := groupSig D) (rec := rec) r Γ (degProg N₁ n₁ F₁ Φ₁) (degProg N₂ n₂ F₂ Φ₂) := by
  unfold degProg
  refine .bind (.prim _ (.cons hN (.cons hn .nil))) fun m₁ m₂ => ?_
  refine .bind (.prim _ .nil) fun l₁ l₂ => ?_
  refine .bind (wf_phiSProg (by simp) (by simp [hΦ]) (by simp)) fun S₁ S₂ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun k₁ k₂ => ?_
  refine .bind (wf_resProg (by simp [hN]) (by simp [hn]) (by simp [hF]) (by simp) (by simp)
    (by simp)) fun R₁ R₂ => ?_
  exact .bind (.prim _ .nil) fun _ _ => wf_degreeProg (by simp) (by simp) (by simp)

theorem wf_case2bProg {sub₁ : var₁ (Ty.inst D) → Prog (groupSig D) rec var₁ (Ty.answer D)}
    {sub₂ : var₂ (Ty.inst D) → Prog (groupSig D) rec var₂ (Ty.answer D)}
    (hsub : WfFun r Γ sub₁ sub₂) {n₁ : var₁ .nat} {n₂ : var₂ .nat}
    {xy₁ : var₁ Ty.strs} {xy₂ : var₂ Ty.strs} {w₁ : var₁ Ty.win} {w₂ : var₂ Ty.win}
    {G₁ Fx₁ Fy₁ : var₁ (Ty.group D)} {G₂ Fx₂ Fy₂ : var₂ (Ty.group D)}
    {Φx₁ Φy₁ : var₁ (.list .nat)} {Φx₂ Φy₂ : var₂ (.list .nat)}
    (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (hxy : ⟨Ty.strs, xy₁, xy₂⟩ ∈ Γ) (hw : ⟨Ty.win, w₁, w₂⟩ ∈ Γ)
    (hG : ⟨Ty.group D, G₁, G₂⟩ ∈ Γ) (hFx : ⟨Ty.group D, Fx₁, Fx₂⟩ ∈ Γ)
    (hFy : ⟨Ty.group D, Fy₁, Fy₂⟩ ∈ Γ) (hΦx : ⟨.list .nat, Φx₁, Φx₂⟩ ∈ Γ)
    (hΦy : ⟨.list .nat, Φy₁, Φy₂⟩ ∈ Γ) :
    Prog.Wf r Γ (case2bProg sub₁ n₁ xy₁ w₁ G₁ Fx₁ Fy₁ Φx₁ Φy₁)
      (case2bProg sub₂ n₂ xy₂ w₂ G₂ Fx₂ Fy₂ Φx₂ Φy₂) := by
  unfold case2bProg
  refine .bind (.prim _ (.cons hG .nil)) fun N₁ N₂ => ?_
  refine .bind (.prim _ (.cons (by simp) (.cons (by simp [hn]) .nil))) fun m₁ m₂ => ?_
  refine .bind (wf_degProg (by simp) (by simp [hn]) (by simp [hFx]) (by simp [hΦx]))
    fun dx₁ dx₂ => ?_
  refine .bind (wf_degProg (by simp) (by simp [hn]) (by simp [hFy]) (by simp [hΦy]))
    fun dy₁ dy₂ => ?_
  refine .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun e₁ e₂ => ?_
  refine .ite (by simp) ?_ (.prim _ .nil)
  refine .bind (.prim _ .nil) fun o₁ o₂ => ?_
  refine .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun j₁ j₂ => ?_
  refine .bind (wf_firstLeafProg (by simp) (by simp [hn]) (by simp [hFx]) (by simp [hΦx])
    (by simp)) fun ox₁ ox₂ => ?_
  refine .caseOption (by simp) (.prim _ .nil) fun X₁ X₂ => ?_
  refine .bind (wf_allLeavesProg (by simp) (by simp [hn]) (by simp [hFy]) (by simp [hΦy])
    (by simp)) fun Ys₁ Ys₂ => ?_
  exact Align.wf_alignProg (hsub.mono fun z hz => by simp [hz])
    (fun Γ' hΓ' z₁ z₂ hz => wf_outGensProg (hΓ' (by simp)) hz)
    (fun Γ' hΓ' z₁ z₂ y₁ y₂ hz hy => wf_outIsoProg (hΓ' (by simp)) hz hy)
    (by simp [hn]) (by simp [hxy]) (by simp [hw]) (by simp [hG]) (by simp) (by simp)

end Wf

end GraphIso.Case2b
