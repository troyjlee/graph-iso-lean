module

public import GraphIso.CertProg.Affected

/-!
# The kernel of `ψ_A` and its orbits

Stage 14e, item 4's ingredients (`PLAN-14.md` §9).

* `kerAProg`: for `H ≤ G_A`, the kernel `N = H ∩ ker ψ_A` is the pointwise stabilizer of the
  positions of `A` (the toolkit's `pointStabsProg`), with coset representatives forming an
  `IsLeftCover` of `H` by `N`. Since `H` permutes the `k` positions of `A`, the `i`-th
  transversal has at most `k - i` points, so there are at most `k!` representatives
  (`pointStabs_reps_le_factorial`), not just the toolkit's `(N - n)^k`.
  `RunsWithin.kerAProg`; `toStab_kerA`: in milestone 13's terms the kernel is
  `toStab φ A H ⊓ ker ψ_A`.
* `kerOrbitsProg`: the backend's orbits of a group on a window (`RunsWithin.kerOrbitsProg`).
* **The orbit bound** (Babai, Cor. 8.3.7; milestone 13's `kernel_orbit`, for any subgroup:
  `kernel_orbit_of_giant`): if `ψ_A(H)` is a giant, `|A| ≥ 5` and the window consists of points
  affected by `H`, every orbit of `N` on it has at most `n / |A|` points
  (`kerOrbit_length_le`).
-/

@[expose] public section

namespace GraphIso.CertProg

open Equiv MulAction Pointwise GraphIso GraphIso.Toolkit GraphIso.Certificates Cost
  GraphIso.Programs GraphIso.Solver GraphIso.AltQuot

/-! ### The orbit bound, for any subgroup -/

section OrbitBound

variable {Ω Γ : Type} [Fintype Ω] [DecidableEq Ω] [Fintype Γ] [DecidableEq Γ]
variable {G : Subgroup (Perm Ω)} (φ : G →* Perm Γ)

omit [DecidableEq Ω] [Fintype Γ] in
/-- **The kernel on the affected points** (Babai, Cor. 8.3.7): milestone 13's `kernel_orbit`
for any subgroup `H ≤ G_A` with a giant image. -/
theorem kernel_orbit_of_giant {A : Finset Γ} (H : Subgroup (stabA φ A)) (h5 : 5 ≤ A.card)
    (h : IsGiantOn φ A H) {u : Ω} (hu : u ∈ aff φ A H) :
    A.card * Nat.card (orbit ↥(H ⊓ (psiA φ A).ker) u) ≤ Nat.card (orbit H u) := by
  obtain ⟨P, ρ, hrange, hstab, -, horb, hker⟩ := Local.exists_permGroup H (psiA φ A)
  have hρ : IsGiant ρ := by
    rw [IsGiant, hrange]
    exact h
  have hu' : IsAffected ρ u := by
    rw [IsAffected, hstab]
    exact hu
  have key := affected_orbit ρ hρ (by rwa [Fintype.card_coe]) hu'
  rwa [Fintype.card_coe, hker, horb] at key

omit [DecidableEq Ω] [Fintype Γ] in
theorem card_orbit_le_card {A : Finset Γ} (H : Subgroup (stabA φ A)) (u : Ω) :
    Nat.card (orbit H u) ≤ Fintype.card Ω := by
  rw [← Nat.card_eq_fintype_card]
  exact Finite.card_subtype_le _

end OrbitBound

/-! ### At most `k!` representatives -/

section PSCard

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}

theorem cp_length_filter_not_mem {S pre : List ℕ} (hS : S.Nodup) (hpre : pre.Nodup)
    (hsub : ∀ u ∈ pre, u ∈ S) : (S.filter fun j => j ∉ pre).length + pre.length = S.length := by
  have h1 := List.length_eq_length_filter_add (l := S) (fun j => decide (j ∉ pre))
  have h2 : (S.filter fun j => !decide (j ∉ pre)).length = pre.length := by
    refine ((List.perm_ext_iff_of_nodup (hS.filter _) hpre).2 fun j => ?_).length_eq
    simp only [List.mem_filter, decide_not, Bool.not_not, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨hsub j h, h⟩⟩
  have h3 : (S.filter fun j => j ∉ pre) = S.filter fun j => decide (j ∉ pre) := rfl
  omega

/-- **Representatives of the pointwise stabilizer of a list of points permuted by `H`**: the
`i`-th transversal has at most `|S| - i` points. -/
theorem cp_ps_card (hO : MeetsContractOn DV stabOps X.O) {N : ℕ}
    {H : Subgroup (Perm (Fin N))} {S : List ℕ} (hS : S.Nodup)
    (hHS : ∀ g ∈ H, ∀ u : Fin N, u.val ∈ S → (g u).val ∈ S) :
    ∀ (rest pre : List ℕ) (acc : GroupData D.denote × List PermData),
      (pre ++ rest).Nodup → (∀ u ∈ pre ++ rest, u ∈ S ∧ u < N) → acc.1.1 = N →
      GroupValid DV N acc.1.2.1 acc.1.2.2 → GensData.denote N acc.1.2.1 ≤ H →
      (∀ g ∈ GensData.denote N acc.1.2.1, ∀ u : Fin N, u.val ∈ pre → g u = u) →
      acc.2.length * (S.length - pre.length).factorial ≤ S.length.factorial →
      (rest.foldl (psStep X.O) acc).2.length * (S.length - (pre ++ rest).length).factorial ≤
        S.length.factorial := by
  intro rest
  induction rest with
  | nil =>
    intro pre acc _ _ _ _ _ _ h
    simpa using h
  | cons u rest ih =>
    intro pre acc hnd hmem hdeg hv hle hfix hcard
    obtain ⟨⟨N', ks, e⟩, reps⟩ := acc
    change N' = N at hdeg
    subst hdeg
    have hu := hmem u (by simp)
    have hupre : u ∉ pre := by
      intro h
      have := List.nodup_append.1 hnd
      exact this.2.2 u h u (by simp) rfl
    have hpre : GroupValid DV N' ks e ∧ u < N' := ⟨hv, hu.2⟩
    obtain ⟨hnd₁, hfst, -⟩ := hO .orbitTransversal ((N', ks, e), u) (Or.inr rfl) hpre
    have hSpost := hO .stabilizer ((N', ks, e), u) (Or.inl rfl) hpre
    rcases hSt : X.O.run GroupOp.stabilizer ((N', ks, e), u) with ⟨N'', ks', e'⟩
    rw [hSt] at hSpost
    obtain ⟨hN'', hv', hden⟩ := hSpost
    change N'' = N' at hN''
    subst hN''
    have hden' := hden hu.2
    set tr : List (ℕ × PermData) := X.O.run GroupOp.orbitTransversal ((N'', ks, e), u) with htr
    -- the transversal lies in `S` minus `pre`
    have htrlen : tr.length ≤ S.length - pre.length := by
      have hsub : ∀ j ∈ tr.map Prod.fst, j ∈ S.filter fun j => j ∉ pre := by
        intro j hj
        obtain ⟨hi, hj', g, hg, hgu⟩ := (hfst j).1 hj
        rw [List.mem_filter, decide_eq_true_eq]
        have hjS : j ∈ S := by
          have := hHS g (hle hg) ⟨u, hi⟩ hu.1
          rwa [hgu] at this
        refine ⟨hjS, fun hjp => hupre ?_⟩
        have hgj := hfix g hg ⟨j, hj'⟩ hjp
        have e := g.injective (hgu.trans hgj.symm)
        have hje : u = j := congrArg Fin.val e
        rw [hje]
        exact hjp
      have hle' := (List.subperm_of_subset hnd₁ hsub).length_le
      have hpren : pre.Nodup := (List.nodup_append.1 hnd).1
      have hpreS : ∀ v ∈ pre, v ∈ S := fun v hv => (hmem v (by simp [hv])).1
      have := cp_length_filter_not_mem hS hpren hpreS
      simp only [List.length_map] at hle'
      omega
    have hpos : 1 ≤ S.length - pre.length := by
      have hpren : pre.Nodup := (List.nodup_append.1 hnd).1
      have hpreS : ∀ v ∈ pre, v ∈ S := fun v hv => (hmem v (by simp [hv])).1
      have := cp_length_filter_not_mem hS hpren hpreS
      have : 0 < (S.filter fun j => j ∉ pre).length :=
        List.length_pos_of_mem (List.mem_filter.2 ⟨hu.1, decide_eq_true hupre⟩)
      omega
    have hstep : psStep X.O ((N'', ks, e), reps) u = ((N'', ks', e'), prodReps reps tr) := by
      simp only [psStep]
      rw [hSt]
    rw [List.foldl_cons, hstep]
    have key := ih (pre ++ [u]) ((N'', ks', e'), prodReps reps tr) (by simpa using hnd)
      (by simpa using hmem) rfl hv' (by
        change GensData.denote N'' ks' ≤ H
        rw [hden']
        exact inf_le_left.trans hle) (by
        intro g hg v hv
        change g ∈ GensData.denote N'' ks' at hg
        rw [hden', mem_pointStab] at hg
        rw [List.mem_append, List.mem_singleton] at hv
        rcases hv with hv | hv
        · exact hfix g hg.1 v hv
        · rw [show v = ⟨u, hu.2⟩ from Fin.ext hv]
          exact hg.2) (by
        change (prodReps reps tr).length * _ ≤ _
        rw [length_prodReps, List.length_append, List.length_singleton]
        have hfac : (S.length - pre.length).factorial =
            (S.length - pre.length) * (S.length - (pre.length + 1)).factorial := by
          rw [show S.length - pre.length = (S.length - (pre.length + 1)) + 1 by omega,
            Nat.factorial_succ]
        calc reps.length * tr.length * (S.length - (pre.length + 1)).factorial
            ≤ reps.length * (S.length - pre.length) * (S.length - (pre.length + 1)).factorial :=
              Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ htrlen)
          _ = reps.length * (S.length - pre.length).factorial := by rw [hfac]; ring
          _ ≤ S.length.factorial := hcard)
    simpa using key

/-- **At most `k!` representatives.** If `H = ⟨gs⟩` permutes the duplicate-free list `S` of
points, the pointwise stabilizer of `S` comes with at most `|S|!` representatives. -/
theorem pointStabs_reps_le_factorial (hO : MeetsContractOn DV stabOps X.O) {N : ℕ}
    {gs : GensData} {d : D.denote} (hGv : GroupValid DV N gs d) {S : List ℕ} (hS : S.Nodup)
    (hSN : ∀ u ∈ S, u < N)
    (hHS : ∀ g ∈ GensData.denote N gs, ∀ u : Fin N, u.val ∈ S → (g u).val ∈ S) :
    (pointStabsModel X.O (N, gs, d) S).2.length ≤ S.length.factorial := by
  have key := cp_ps_card (X := X) hO hS hHS S [] ((N, gs, d), [PermData.one N])
    (by simpa using hS) (by simpa using fun u hu => ⟨hu, hSN u hu⟩) rfl hGv le_rfl
    (by simp) (by simp)
  simpa [pointStabsModel] using key

/-- The cost of `kerAProg` on `k` points: at most `k!` representatives at every stage, and
transversals of at most `k` points. -/
def kerACost (N k Bt Bs : ℕ) : ℕ :=
  2 * N + 7 + k * (Bt + Bs + k.factorial * (k * (12 * N + 18) + 4) + 8)

/-- **The run of the pointwise-stabilizer fold with factorial bounds.** -/
theorem cp_ps_run (hO : MeetsContractOn DV stabOps X.O)
    (hPre : ∀ op x, stabOps op → GroupPre DV op x → X.Pre op x) {N s : ℕ}
    {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N s G₀)
    {H : Subgroup (Perm (Fin N))} {S : List ℕ} (hS : S.Nodup)
    (hHS : ∀ g ∈ H, ∀ u : Fin N, u.val ∈ S → (g u).val ∈ S) :
    ∀ (rest pre : List ℕ) (acc : GroupData D.denote × List PermData),
      (pre ++ rest).Nodup → (∀ u ∈ pre ++ rest, u ∈ S ∧ u < N) → acc.1.1 = N →
      GroupValid DV N acc.1.2.1 acc.1.2.2 → acc.1.2.1.length ≤ s →
      GensData.denote N acc.1.2.1 ≤ H → GensData.denote N acc.1.2.1 ≤ G₀ →
      (∀ g ∈ GensData.denote N acc.1.2.1, ∀ u : Fin N, u.val ∈ pre → g u = u) →
      (∀ r ∈ acc.2, PermData.Valid N r) →
      acc.2.length * (S.length - pre.length).factorial ≤ S.length.factorial →
      RunsWithin X body (Prog.foldList (a := .nat) (b := .prod (Ty.group D) (.list Ty.perm))
          rest acc psBody) (rest.foldl (psStep X.O) acc)
        (rest.length * (B.Btr + B.Bstab + S.length.factorial * (S.length * (12 * N + 18) + 4) +
          8)) := by
  intro rest
  induction rest with
  | nil =>
    intro _ _ _ _ _ _ _ _ _ _ _ _
    exact (RunsWithin.foldList_nil (X := X) (body := body)).mono (Nat.zero_le _)
  | cons u rest ih =>
    intro pre acc hnd hmem hdeg hv hlen hle hle₀ hfix hrv hcard
    obtain ⟨⟨N', ks, e⟩, reps⟩ := acc
    change N' = N at hdeg
    subst hdeg
    change ks.length ≤ s at hlen
    have hu := hmem u (by simp)
    have hupre : u ∉ pre := by
      intro h
      exact (List.nodup_append.1 hnd).2.2 u h u (by simp) rfl
    have hpre : GroupPre DV .orbitTransversal ((N', ks, e), u) := ⟨hv, hu.2⟩
    have hpreS : GroupPre DV .stabilizer ((N', ks, e), u) := ⟨hv, hu.2⟩
    obtain ⟨hnd₁, hfst, htr⟩ := hO .orbitTransversal _ (Or.inr rfl) hpre
    have hSpost := hO .stabilizer _ (Or.inl rfl) hpreS
    have hBtu := B.transversal ks e u hlen hle₀ hpre
    have hBsu := B.stabilizer ks e u hlen hle₀ hpreS
    have hout := B.stabOut ks e u hle₀ hpreS
    obtain ⟨tr, htr_def⟩ : ∃ tr : List (ℕ × PermData),
        X.O.run GroupOp.orbitTransversal ((N', ks, e), u) = tr := ⟨_, rfl⟩
    rw [htr_def] at hnd₁ hfst htr hBtu
    rcases hS' : X.O.run GroupOp.stabilizer ((N', ks, e), u) with ⟨N'', ks', e'⟩
    rw [hS'] at hSpost hBsu hout
    obtain ⟨hN'', hv', hden⟩ := hSpost
    change N'' = N' at hN''
    subst hN''
    have hden' := hden hu.2
    have hpren : pre.Nodup := (List.nodup_append.1 hnd).1
    have hpreSub : ∀ v ∈ pre, v ∈ S := fun v hv => (hmem v (by simp [hv])).1
    have hlf := cp_length_filter_not_mem hS hpren hpreSub
    -- the transversal lies in `S` minus `pre`
    have htrlen : tr.length ≤ S.length - pre.length := by
      have hsub : ∀ j ∈ tr.map Prod.fst, j ∈ S.filter fun j => j ∉ pre := by
        intro j hj
        obtain ⟨hi, hj', g, hg, hgu⟩ := (hfst j).1 hj
        rw [List.mem_filter, decide_eq_true_eq]
        have hjS : j ∈ S := by
          have := hHS g (hle hg) ⟨u, hi⟩ hu.1
          rwa [hgu] at this
        refine ⟨hjS, fun hjp => hupre ?_⟩
        have hgj := hfix g hg ⟨j, hj'⟩ hjp
        have e := g.injective (hgu.trans hgj.symm)
        have hje : u = j := congrArg Fin.val e
        rw [hje]
        exact hjp
      have hle' := (List.subperm_of_subset hnd₁ hsub).length_le
      simp only [List.length_map] at hle'
      omega
    have hpos : 1 ≤ S.length - pre.length := by
      have : 0 < (S.filter fun j => j ∉ pre).length :=
        List.length_pos_of_mem (List.mem_filter.2 ⟨hu.1, decide_eq_true hupre⟩)
      omega
    have hrepsle : reps.length ≤ S.length.factorial :=
      (Nat.le_mul_of_pos_right _ (Nat.factorial_pos _)).trans hcard
    have hstep : psStep X.O ((N'', ks, e), reps) u = ((N'', ks', e'), prodReps reps tr) := by
      simp only [psStep]
      rw [hS', htr_def]
    have hrun₁ : RunsWithin X body (psBody ((N'', ks, e), reps) u)
        ((N'', ks', e'), prodReps reps tr)
        (B.Btr + B.Bstab + S.length.factorial * (S.length * (12 * N'' + 18) + 4) + 7) := by
      have hpr := RunsWithin.prodRepsProg (X := X) (body := body) (N := N'') (reps := reps)
        (tr := tr) hrv fun vt hvt => (htr vt hvt).1
      apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.call (hPre _ _ (Or.inr rfl) hpre))
        run_step (RunsWithin.call (hPre _ _ (Or.inl rfl) hpreS))
        simp only [Prim.eval]
        rw [hS', htr_def]
        run_step hpr
        exact RunsWithin.prim_le rfl le_rfl
      case hc =>
        have hp : Prim.eval (Prim.pair (a := Ty.group D) (b := .nat))
            (Args.cons (Prim.eval (Prim.fst (a := Ty.group D) (b := .list Ty.perm))
              (Args.cons ((N'', ks, e), reps) Args.nil)) (Args.cons u Args.nil)) =
            ((N'', ks, e), u) := rfl
        have hmul : reps.length * (tr.length * (12 * N'' + 18) + 4) ≤
            S.length.factorial * (S.length * (12 * N'' + 18) + 4) :=
          Nat.mul_le_mul hrepsle (Nat.add_le_add_right (Nat.mul_le_mul_right _
            (htrlen.trans (Nat.sub_le _ _))) _)
        simp only [Prim.cost]
        rw [hp, hS', htr_def]
        omega
    have hrun₂ := ih (pre ++ [u]) ((N'', ks', e'), prodReps reps tr) (by simpa using hnd)
      (by simpa using hmem) rfl hv' hout (by
        change GensData.denote N'' ks' ≤ H
        rw [hden']
        exact inf_le_left.trans hle) (by
        change GensData.denote N'' ks' ≤ G₀
        rw [hden']
        exact inf_le_left.trans hle₀) (by
        intro g hg v hv
        change g ∈ GensData.denote N'' ks' at hg
        rw [hden', mem_pointStab] at hg
        rw [List.mem_append, List.mem_singleton] at hv
        rcases hv with hv | hv
        · exact hfix g hg.1 v hv
        · rw [show v = ⟨u, hu.2⟩ from Fin.ext hv]
          exact hg.2) (by
        intro x hx
        obtain ⟨r, hr, vt, hvt, rfl⟩ := mem_prodReps.1 hx
        exact (hrv r hr).mul (htr vt hvt).1) (by
        change (prodReps reps tr).length * _ ≤ _
        rw [length_prodReps, List.length_append, List.length_singleton]
        have hfac : (S.length - pre.length).factorial =
            (S.length - pre.length) * (S.length - (pre.length + 1)).factorial := by
          rw [show S.length - pre.length = (S.length - (pre.length + 1)) + 1 by omega,
            Nat.factorial_succ]
        calc reps.length * tr.length * (S.length - (pre.length + 1)).factorial
            ≤ reps.length * (S.length - pre.length) * (S.length - (pre.length + 1)).factorial :=
              Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ htrlen)
          _ = reps.length * (S.length - pre.length).factorial := by rw [hfac]; ring
          _ ≤ S.length.factorial := hcard)
    rw [List.foldl_cons, hstep]
    refine (RunsWithin.foldList_cons hrun₁ hrun₂).mono ?_
    simp only [List.length_cons, Nat.succ_mul]
    omega

end PSCard

/-! ### The kernel as a program -/

section Programs

variable {D : Ty} {rec : Ty × Ty} {var : Ty → Type}

/-- **The kernel `H ∩ ker ψ_A`**: the pointwise stabilizer of the positions of `A`, with coset
representatives. -/
def kerAProg (H : var (Ty.group D)) (pA : var (.list .nat)) :
    Prog (groupSig D) rec var (.prod (Ty.group D) (.list Ty.perm)) :=
  Toolkit.pointStabsProg H pA

/-- The backend's orbits of a group on a window. -/
def kerOrbitsProg (K : var (Ty.group D)) (w : var Ty.win) :
    Prog (groupSig D) rec var (.list (.list .nat)) :=
  .bind (.op2 .pair K w) fun a => Prog.call (S := groupSig D) GroupOp.orbits a

end Programs

section Spec

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}

variable {N n : ℕ} {G : Subgroup (Perm (Fin N))} {hC : CertSetting G n}
  {φ : strGroup hC →* Perm (Fin (N - n))}

theorem basePosSet_finsetOf (al : List ℕ) :
    basePosSet (finsetOf (N - n) al) = {v : Fin N | v.val ∈ posA n al} := by
  ext v
  simp only [basePosSet, Set.mem_ofPred_eq, mem_finsetOf, mem_posA]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a.val, ha, rfl⟩
  · rintro ⟨a, ha, hv⟩
    exact ⟨⟨a, by have := v.2; omega⟩, ha, Fin.ext hv⟩

/-- **The kernel in milestone 13's terms**: the pointwise stabilizer of the positions of `A` in
`H` gives `toStab φ A H ⊓ ker ψ_A`. -/
theorem toStab_kerA (hφ : IsPhi hC φ) (al : List ℕ) (H : Subgroup (Perm (Fin N))) :
    toStab φ (finsetOf (N - n) al) (pointwiseStab H {v : Fin N | v.val ∈ posA n al}) =
      toStab φ (finsetOf (N - n) al) H ⊓ (psiA φ (finsetOf (N - n) al)).ker := by
  rw [← basePosSet_finsetOf, toStab_pointwiseStab hφ]

/-- **The kernel of `ψ_A` with at most `k!` representatives.** -/
theorem RunsWithin.kerAProg (hO : MeetsContractOn DV stabOps X.O)
    (hPre : ∀ op x, stabOps op → GroupPre DV op x → X.Pre op x) {al : List ℕ} (hal : al.Nodup)
    (halm : ∀ x ∈ al, x < N - n) {hs : GensData} {e : D.denote} (hHv : GroupValid DV N hs e)
    (hH : StabsA hC al (GensData.denote N hs)) {s : ℕ} {G₀ : Subgroup (Perm (Fin N))}
    (B : BackendBounds X DV N s G₀) (hlen : hs.length ≤ s)
    (hG₀ : GensData.denote N hs ≤ G₀) :
    RunsWithin X body (CertProg.kerAProg (N, hs, e) (posA n al))
        (pointStabsModel X.O (N, hs, e) (posA n al))
        (kerACost N al.length B.Btr B.Bstab) ∧
      (pointStabsModel X.O (N, hs, e) (posA n al)).1.1 = N ∧
      GroupValid DV N (pointStabsModel X.O (N, hs, e) (posA n al)).1.2.1
        (pointStabsModel X.O (N, hs, e) (posA n al)).1.2.2 ∧
      GensData.denote N (pointStabsModel X.O (N, hs, e) (posA n al)).1.2.1 =
        pointwiseStab (GensData.denote N hs) {v : Fin N | v.val ∈ posA n al} ∧
      (∀ r ∈ (pointStabsModel X.O (N, hs, e) (posA n al)).2, PermData.Valid N r) ∧
      IsLeftCover (GensData.denote N hs)
        (GensData.denote N (pointStabsModel X.O (N, hs, e) (posA n al)).1.2.1)
        (fun i : Fin (pointStabsModel X.O (N, hs, e) (posA n al)).2.length =>
          PermData.denote N ((pointStabsModel X.O (N, hs, e) (posA n al)).2.get i)) ∧
      (pointStabsModel X.O (N, hs, e) (posA n al)).2.length ≤ al.length.factorial := by
  have hnN := hC.le
  have hGb : IsInvariant (GensData.denote N hs) (baseSet n N) := fun g hg =>
    hC.base g (hH.1 hg)
  have hps : ∀ u ∈ posA n al, n ≤ u ∧ u < N := by
    intro u hu
    obtain ⟨x, hx, rfl⟩ := mem_posA.1 hu
    have := halm x hx
    omega
  obtain ⟨hrun, hN, hv, hden, hrv, hcov, -⟩ := RunsWithin.pointStabsProg (X := X) (body := body)
    hO hPre hHv hGb hps B hlen hG₀
  have hW := isInvariant_winA hH
  have hHS : ∀ g ∈ GensData.denote N hs, ∀ u : Fin N, u.val ∈ posA n al →
      (g u).val ∈ posA n al := fun g hg u hu => by
    have := hW g hg u (by rw [winA, WinData.denote_ofPoints]; exact hu)
    rwa [winA, WinData.denote_ofPoints] at this
  refine ⟨?_, hN, hv, hden, hrv, hcov, ?_⟩
  · have hfold := cp_ps_run (X := X) (body := body) hO hPre B (posA_nodup n hal) hHS (posA n al)
      [] ((N, hs, e), [PermData.one N]) (by simpa using posA_nodup n hal)
      (by simpa using fun u hu => ⟨hu, (hps u hu).2⟩) rfl hHv hlen le_rfl hG₀ (by simp)
      (by simp [PermData.valid_one]) (by simp)
    rw [length_posA] at hfold
    apply RunsWithin.mono
    case h =>
      unfold CertProg.kerAProg Toolkit.pointStabsProg
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.permOne N)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      exact hfold
    case hc =>
      simp only [Prim.cost, kerACost]
      omega
  · have hW := isInvariant_winA hH
    have key := pointStabs_reps_le_factorial (X := X) hO hHv (posA_nodup n hal)
      (fun u hu => (hps u hu).2) fun g hg u hu => by
        have := hW g hg u (by rw [winA, WinData.denote_ofPoints]; exact hu)
        rwa [winA, WinData.denote_ofPoints] at this
    rwa [length_posA] at key

/-- The operations used by `kerOrbitsProg`. -/
def kerOrbitsOps (op : GroupOp) : Prop := op = .orbits

/-- **The backend's orbits on a window.** -/
theorem RunsWithin.kerOrbitsProg (hO : MeetsContractOn DV kerOrbitsOps X.O)
    (hPre : ∀ op x, kerOrbitsOps op → GroupPre DV op x → X.Pre op x) {ks : GensData}
    {e : D.denote} (hKv : GroupValid DV N ks e) {w : WinData} (hw : w.Valid N)
    (hW : IsInvariant (GensData.denote N ks) (w.denote N)) {s : ℕ}
    {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N s G₀) (hlen : ks.length ≤ s)
    (hG₀ : GensData.denote N ks ≤ G₀) :
    RunsWithin X body (CertProg.kerOrbitsProg (N, ks, e) w)
        (X.O.run GroupOp.orbits ((N, ks, e), w)) (B.Borb + 1) ∧
      IsOrbitPartition (GensData.denote N ks) w (X.O.run GroupOp.orbits ((N, ks, e), w)) := by
  have hpre : GroupPre DV .orbits ((N, ks, e), w) := ⟨hKv, hw, hW⟩
  refine ⟨?_, hO .orbits _ rfl hpre⟩
  have hB := B.orbits ks e w hlen hG₀ hpre
  refine RunsWithin.bind_le (RunsWithin.prim _ _) (RunsWithin.call (hPre _ _ rfl hpre)) ?_
  simp only [Prim.cost, Prim.eval]
  omega

theorem card_finsetOf {m : ℕ} {l : List ℕ} (hl : l.Nodup) (hlm : ∀ x ∈ l, x < m) :
    (finsetOf m l).card = l.length := by
  rw [← Fintype.card_coe, Fintype.card_congr (listEquiv hl hlm).symm, Fintype.card_fin]

theorem cp_kerOrbit_aux {al : List ℕ} {A : Finset (Fin (N - n))}
    {H : Subgroup (Perm (Fin N))} (hAc : A.card = al.length) (h5 : 5 ≤ al.length)
    (hsA : ∀ g ∈ H, ∀ hgG : g ∈ G, strR hC ⟨g, hgG⟩ ∈ stabA φ A) (hHG : H ≤ G)
    (hker : ∀ g (hgG : g ∈ G) (hs : strR hC ⟨g, hgG⟩ ∈ stabA φ A),
      g ∈ pointwiseStab H {v : Fin N | v.val ∈ posA n al} →
        (⟨strR hC ⟨g, hgG⟩, hs⟩ : stabA φ A) ∈ toStab φ A H ⊓ (psiA φ A).ker)
    (hgiant : IsGiantOn φ A (toStab φ A H)) {w : WinData} (hw : w.Valid N)
    (haff : ∀ j ∈ w.1, ∃ hj : j < n, (⟨j, hj⟩ : Fin n) ∈ aff φ A (toStab φ A H))
    {os : List (List ℕ)}
    (hos : IsOrbitPartition (pointwiseStab H {v : Fin N | v.val ∈ posA n al}) w os)
    {o : List ℕ} (ho : o ∈ os) : al.length * o.length ≤ n := by
  obtain ⟨hperm, hblk⟩ := hos
  obtain ⟨hne, hsame⟩ := hblk o ho
  have hflat : os.flatten.Nodup := hperm.nodup_iff.2 hw.nodup
  have hond : o.Nodup := (List.nodup_flatten.1 hflat).1 o ho
  obtain ⟨i, hio⟩ := List.exists_mem_of_ne_nil o hne
  have hiw : i ∈ w.1 := hperm.subset (List.mem_flatten.2 ⟨o, ho, hio⟩)
  obtain ⟨hin, haffi⟩ := haff i hiw
  set K := toStab φ A H ⊓ (psiA φ A).ker with hK
  -- the points of `o` lie in the orbit of `i` under `toStab φ A H ⊓ ker ψ_A`
  have hsub : ∀ j ∈ o, ∃ hj : j < n, (⟨j, hj⟩ : Fin n) ∈ orbit ↥K (⟨i, hin⟩ : Fin n) := by
    intro j hj
    obtain ⟨hi', hj', g, hg, hgi⟩ := (hsame i hio j).1 hj
    have hgG : g ∈ G := hHG hg.1
    have hjn : j < n := by
      have := hC.str g hgG ⟨i, hi'⟩ (show i < n from hin)
      rw [hgi] at this
      exact this
    refine ⟨hjn, ⟨⟨_, hker g hgG (hsA g hg.1 hgG) hg⟩, ?_⟩⟩
    apply Fin.ext
    show (((strR hC ⟨g, hgG⟩ : Perm (Fin n)) ⟨i, hin⟩ : Fin n) : ℕ) = j
    rw [strR_apply_val]
    exact congrArg Fin.val hgi
  have hcardo : (finsetOf n o).card = o.length := card_finsetOf hond fun j hj => (hsub j hj).1
  have hle1 : o.length ≤ Nat.card (orbit ↥K (⟨i, hin⟩ : Fin n)) := by
    rw [← hcardo, Nat.card_coe_set_eq, ← Set.ncard_coe_finset]
    refine Set.ncard_le_ncard (fun y hy => ?_) (Set.toFinite _)
    rw [Finset.mem_coe, mem_finsetOf] at hy
    exact (hsub y.val hy).2
  have hko := kernel_orbit_of_giant φ (toStab φ A H) (hAc ▸ h5) hgiant haffi
  have hcl := card_orbit_le_card φ (toStab φ A H) (⟨i, hin⟩ : Fin n)
  rw [Fintype.card_fin] at hcl
  calc al.length * o.length ≤ A.card * Nat.card (orbit ↥K (⟨i, hin⟩ : Fin n)) := by
        rw [hAc]
        exact Nat.mul_le_mul_left _ hle1
    _ ≤ n := hko.trans hcl

/-- **The orbit bound on data.** Let `H ≤ G_A` with `ψ_A(H)` a giant and `|A| ≥ 5`, and let
`N = H ∩ ker ψ_A` (the pointwise stabilizer of the positions of `A`). On a window of string
positions affected by `H`, every orbit of `N` has at most `n / |A|` points: `|A| · |o| ≤ n`. -/
theorem kerOrbit_length_le (hφ : IsPhi hC φ) {al : List ℕ} {H : Subgroup (Perm (Fin N))}
    (hH : StabsA hC al H) (h5 : 5 ≤ al.length) (hal : al.Nodup) (halm : ∀ x ∈ al, x < N - n)
    (hgiant : IsGiantOn φ (finsetOf (N - n) al) (toStab φ (finsetOf (N - n) al) H))
    {w : WinData} (hw : w.Valid N)
    (haff : ∀ j ∈ w.1, ∃ hj : j < n, (⟨j, hj⟩ : Fin n) ∈
      aff φ (finsetOf (N - n) al) (toStab φ (finsetOf (N - n) al) H))
    {os : List (List ℕ)}
    (hos : IsOrbitPartition (pointwiseStab H {v : Fin N | v.val ∈ posA n al}) w os)
    {o : List ℕ} (ho : o ∈ os) : al.length * o.length ≤ n :=
  cp_kerOrbit_aux (card_finsetOf hal halm) h5
    (fun g hg hgG => (mem_stabA_strR hφ _).2 (hH.2 ⟨g, hgG⟩ hg)) hH.1
    (fun g hgG hs hg => by rw [← toStab_kerA hφ, mem_toStab_strR]; exact hg) hgiant hw haff hos ho

end Spec

/-! ### Well-formedness -/

section Wf

variable {D : Ty} {rec : Ty × Ty} {var₁ var₂ : Ty → Type} {r : Bool} {Γ : WfCtx var₁ var₂}

theorem wf_kerAProg {H₁ : var₁ (Ty.group D)} {H₂ : var₂ (Ty.group D)}
    {pA₁ : var₁ (.list .nat)} {pA₂ : var₂ (.list .nat)} (hH : ⟨Ty.group D, H₁, H₂⟩ ∈ Γ)
    (hpA : ⟨.list .nat, pA₁, pA₂⟩ ∈ Γ) :
    Prog.Wf (rec := rec) r Γ (kerAProg H₁ pA₁) (kerAProg H₂ pA₂) :=
  Toolkit.wf_pointStabsProg hH hpA

theorem wf_kerOrbitsProg {K₁ : var₁ (Ty.group D)} {K₂ : var₂ (Ty.group D)}
    {w₁ : var₁ Ty.win} {w₂ : var₂ Ty.win} (hK : ⟨Ty.group D, K₁, K₂⟩ ∈ Γ)
    (hw : ⟨Ty.win, w₁, w₂⟩ ∈ Γ) :
    Prog.Wf (rec := rec) r Γ (kerOrbitsProg K₁ w₁) (kerOrbitsProg K₂ w₂) := by
  unfold kerOrbitsProg
  prog_wf

end Wf

end GraphIso.CertProg
