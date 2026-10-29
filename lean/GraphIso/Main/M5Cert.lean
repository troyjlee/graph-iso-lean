module

public import GraphIso.Main.StepsBase
public import GraphIso.Giant.Aggregate
public import GraphIso.Case2b.Case2bProg

/-!
# M5: certificates, the full group and the case decision

Stage 14j-4, items 2 and 4 (`PLAN-14.md` §14.4). The giant macro-step M5 runs, after the
restriction to the window and the base (item 1, `Main/M5Restrict.lean`), on a hinted instance
whose string positions `[0, n)` all lie in the window, whose coset representative is `1`, and
whose group `G` is faithful on the strings (`CertSetting`) with a giant base action.

* **Certificates with the hinted sub-solver** (`m5CertProg`): stage 14g's `fullProg` with the
  sub-solver `plainSub sub n₀ n`, so that every certificate sub-call is a hinted instance without
  a hint. `m5_stepSub` turns `HSubSolves` into the hypothesis `SubSolves … (StepSubP …)` of the
  certificate programs, at the uniform cost `C (n / k) none + 4`, assuming `C · none` monotone
  in the window size. `RunsWithin.m5CertProg`: the run and the full group `F` as the preimage of
  `fullGroupK` (`m5Fmap`). `fullCost_le_count`: the cost is at most `cnt · Cb + W` with
  `cnt = C(m, k) · n · k! · n` sub-calls (`certCount`): the children are counted by number,
  each a window of at most `n / k` points without a hint.
* **The full-group map** (`m5Fmap x = agPre (fullGroupK φ k (strOn x))`), in the form the case
  programs of stages 14g–14i take: inside `G` (`m5Fmap_le`), local to the window when the window
  contains every string position (`m5Fmap_loc`), canonical (`m5Fmap_relabel`, from
  `fullGroupK_relabel`), consisting of automorphisms (`m5Fmap_matches`), base-invariant.
* **The case decision** (`m5CaseProg`): stage 14g's `caseProg` (Case 1, 2 with the large orbit
  `Φ`, or 3) and, in Case 2, Case 2b's degree program on `Φ` to separate Case 2a from Case 2b:
  Case 2a when `ψ(F)` moves any `|Φ| − 2` points of `Φ` to any other. `m5Case_spec`: in Case 2a
  every even permutation of the positions of `Φ` is realized by `F` (`hFalt` of
  `case2aProg_canonical`), by `alt_le_of_tupTrans` (a `(k − 2)`-transitive group of degree `k`
  contains `Alt(k)`, mathlib's `IsMultiplyPretransitive.alternatingGroup_le`); in Case 2b,
  `ψ(F)` is not `(|Φ| − 2)`-transitive on `Φ` (`hngx` of `case2bProg_canonical'`).
* Well-formedness: `wf_m5CertProg`, `wf_m5CaseProg`.
-/

@[expose] public section

namespace GraphIso.Main

open Equiv MulAction Pointwise Cost GraphIso GraphIso.Toolkit GraphIso.Certificates
  GraphIso.CertProg GraphIso.Giant GraphIso.Solver GraphIso.Programs

/-! ### Programs -/

section Programs

variable {D : Ty} {rec : Ty × Ty} {var : Ty → Type}

/-- **The certificates** of the string `x`: `fullProg` with the sub-solver on instances
without a hint. -/
def m5CertProg (sub : var (hinstTy D) → Prog (groupSig D) rec var (Ty.answer D))
    (n₀ n N k : var .nat) (x : var Ty.str) (G : var (Ty.group D)) :
    Prog (groupSig D) rec var (Ty.group D) :=
  Giant.fullProg (fun J => plainSub sub n₀ n J) n N k x G

/-- **The case decision**: `caseProg`'s case and orbits, and, in Case 2, whether `ψ(F)` moves
any `|Φ| − 2` points of the large orbit `Φ` (Case 2a) or not (Case 2b), by the degree program
of Case 2b. -/
def m5CaseProg (n N : var .nat) (F : var (Ty.group D)) :
    Prog (groupSig D) rec var
      (.prod (.prod (.prod .nat (.list .nat)) (.list (.list .nat))) .bool) :=
  .bind (Giant.caseProg n N F) fun r => .bind (.op1 .fst r) fun cs =>
  .bind (.op1 .fst cs) fun tag => .bind (.op1 .snd cs) fun Φ =>
  .bind (.op0 (.natLit 2)) fun two => .bind (.op2 .natEq tag two) fun is2 =>
  .bind (.ite is2
      (.bind (Case2b.degProg N n F Φ) fun dg => .bind (.op1 .length Φ) fun l =>
        .bind (.op2 .sub l two) fun l2 => .bind (.op2 .natLt dg l2) fun lt => .op1 .not lt)
      (.op0 (.boolLit false))) fun isA =>
  .op2 .pair r isA

end Programs

/-! ### The certificate sub-calls -/

section Bridge

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}

/-- A certificate sub-call, without a hint, is a valid hinted instance: its group lies in the
faithful, base-preserving `G`. -/
theorem m5_hinstValid_step {N n k sIn : ℕ} {G : Subgroup (Perm (Fin N))} (hC : CertSetting G n)
    {xy : StrData × StrData} {J : InstData D} (hJ : StepSubP (DV := DV) G xy n k sIn J)
    (n₀ : ℕ) : HInstValid DV ((J, n₀, n, none) : HInstData D) := by
  obtain ⟨xy', w', σ', N', gs', d'⟩ := J
  obtain ⟨-, hv, hdeg, hw, -, hle, -⟩ := hJ
  change N' = N at hdeg
  subst hdeg
  refine sb_hinstValid_plain hv hC.le ?_ hw ?_
  · intro g hg u hu
    exact hC.base g (hle hg) u hu
  · intro g hg hfix
    exact hC.faithful g (hle hg) hfix

/-- **From hinted sub-solvers to the certificate sub-solver.** If every instance a certificate
passes is, without a hint, an instance satisfying `P`, and `C · none` is monotone in the window
size, the wrapped sub-solver solves the certificate sub-calls (`StepSubP`, windows of at most
`n / k` points) within `C (n / k) none + 4`. -/
theorem m5_stepSub {sub : HInstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)}
    {P : HInstData D → Prop} {C : ℕ → Option ℕ → ℕ} {s : ℕ}
    (hsub : HSubSolves X body DV sub P C s)
    (hCmono : ∀ a b, a ≤ b → C a none ≤ C b none) {N n k sIn n₀ : ℕ} (hk : 0 < k)
    {G : Subgroup (Perm (Fin N))} (hC : CertSetting G n) (xy : StrData × StrData)
    (hP : ∀ J : InstData D, StepSubP (DV := DV) G xy n k sIn J → P (J, n₀, n, none)) :
    SubSolves X body DV (fun J => Main.plainSub sub n₀ n J) (StepSubP (DV := DV) G xy n k sIn)
      (fun _ => C (n / k) none + 4) s := by
  intro J hJ
  obtain ⟨ans, hr, hok, hg⟩ := hsub _ (m5_hinstValid_step hC hJ n₀) (hP J hJ)
  refine ⟨ans, (RunsWithin.plainSub n₀ n J hr).mono ?_, hok, hg⟩
  have hlen : J.2.1.1.length ≤ n / k :=
    (Nat.le_div_iff_mul_le hk).2 (by rw [Nat.mul_comm]; exact hJ.2.2.2.2.1)
  have := hCmono _ _ hlen
  change C (HInstData.winSize ((J, n₀, n, none) : HInstData D)) none + 4 ≤ C (n / k) none + 4
  exact Nat.add_le_add_right this 4

end Bridge

/-! ### The full-group map -/

section Fmap

variable {N n : ℕ} {G : Subgroup (Perm (Fin N))} (hC : CertSetting G n)
  (φ : strGroup hC →* Perm (Fin (N - n))) (k : ℕ)

/-- **The full group of a string**: the elements of `G` whose restriction to the strings lies in
`fullGroupK φ k`, the group generated by the certificates passing the test. -/
def m5Fmap (x : Fin N → ℕ) : Subgroup (Perm (Fin N)) :=
  agPre hC (fullGroupK φ k (strOn hC.le x))

theorem m5Fmap_le (x : Fin N → ℕ) : m5Fmap hC φ k x ≤ G := agPre_le _

theorem m5Fmap_base (x : Fin N → ℕ) : IsInvariant (m5Fmap hC φ k x) (baseSet n N) :=
  fun g hg u hu => hC.base g (m5Fmap_le hC φ k x hg) u hu

/-- **Locality**: when the window contains every string position, the full group depends only
on the string on the window. -/
theorem m5Fmap_loc {W : Set (Fin N)} (hwS : ∀ u : Fin N, u.val < n → u ∈ W) :
    ∀ x x', (∀ u ∈ W, x u = x' u) → m5Fmap hC φ k x = m5Fmap hC φ k x' := by
  intro x x' h
  unfold m5Fmap
  congr 2
  funext j
  exact h _ (hwS _ j.2)

theorem m5_strOn_relabel {g : Perm (Fin N)} (hg : g ∈ G) (x : Fin N → ℕ) :
    strOn hC.le (relabel g x) = smulStr (strR hC ⟨g, hg⟩) (strOn hC.le x) := by
  funext j
  simp only [strOn, relabel_apply, smulStr]
  congr 1

/-- Conjugation commutes with the preimage. -/
theorem agPre_map_conj {g : Perm (Fin N)} (hg : g ∈ G) (C : Subgroup (strGroup hC)) :
    agPre hC (C.map (MulAut.conj (strR hC ⟨g, hg⟩)).toMonoidHom) =
      (agPre hC C).map (MulAut.conj g).toMonoidHom := by
  ext h
  rw [ag_mem_agPre]
  constructor
  · rintro ⟨hh, c, hc, hce⟩
    obtain ⟨h₀, rfl⟩ := strR_surjective hC c
    refine ⟨h₀.1, ag_mem_agPre.2 ⟨h₀.2, hc⟩, ?_⟩
    have : (⟨g, hg⟩ * h₀ * (⟨g, hg⟩ : G)⁻¹ : G) = ⟨h, hh⟩ := by
      apply strR_injective hC
      rw [← hce]
      simp [MulAut.conj_apply, map_mul, map_inv]
    have := congrArg Subtype.val this
    simpa [MulAut.conj_apply] using this
  · rintro ⟨h', hh', rfl⟩
    obtain ⟨hh'G, hc⟩ := ag_mem_agPre.1 hh'
    have hmem : g * h' * g⁻¹ ∈ G := G.mul_mem (G.mul_mem hg hh'G) (G.inv_mem hg)
    refine ⟨by simpa [MulAut.conj_apply] using hmem, strR hC ⟨h', hh'G⟩, hc, ?_⟩
    have : (⟨g * h' * g⁻¹, hmem⟩ : G) = ⟨g, hg⟩ * ⟨h', hh'G⟩ * (⟨g, hg⟩ : G)⁻¹ := rfl
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show (⟨g * h' * g⁻¹, _⟩ : G) = ⟨g * h' * g⁻¹, hmem⟩ from rfl, this, map_mul, map_mul,
      map_inv]

/-- **Canonicity**: relabelling the string by `g ∈ G` conjugates the full group. -/
theorem m5Fmap_relabel : ∀ g ∈ G, ∀ x : Fin N → ℕ,
    m5Fmap hC φ k (relabel g x) = (m5Fmap hC φ k x).map (MulAut.conj g).toMonoidHom := by
  intro g hg x
  unfold m5Fmap
  rw [m5_strOn_relabel hC hg x, fullGroupK_relabel, agPre_map_conj]

/-- **The full group consists of automorphisms** of the string on the string positions. -/
theorem m5Fmap_matches (x : Fin N → ℕ) {f : Perm (Fin N)} (hf : f ∈ m5Fmap hC φ k x)
    (u : Fin N) (hu : u.val < n) : x u = x (f u) := by
  obtain ⟨hfG, hfC⟩ := ag_mem_agPre.1 hf
  obtain ⟨-, -, hx⟩ := fullGroupK_le_autG φ k (strOn hC.le x) hfC
  have := hx ⟨u.val, hu⟩ trivial
  simp only [strOn] at this
  rw [show (strR hC ⟨f, hfG⟩ • (⟨u.val, hu⟩ : Fin n) : Fin n) =
    (strR hC ⟨f, hfG⟩ : Perm (Fin n)) ⟨u.val, hu⟩ from rfl] at this
  have hv := strR_apply_val hC ⟨f, hfG⟩ ⟨u.val, hu⟩
  have e1 : (⟨((strR hC ⟨f, hfG⟩ : Perm (Fin n)) ⟨u.val, hu⟩).val, by omega⟩ : Fin N) = f u := by
    apply Fin.ext
    rw [hv]
  rw [e1] at this
  exact this.symm

/-- **`hFaut`**: on a window of string positions, the full group consists of automorphisms. -/
theorem m5Fmap_matchesW (x : Fin N → ℕ) {W : Set (Fin N)} (hwn : ∀ u ∈ W, u.val < n) :
    ∀ f ∈ m5Fmap hC φ k x, Matches W f x x :=
  fun _ hf u hu => m5Fmap_matches hC φ k x hf u (hwn u hu)

end Fmap

/-! ### The certificates as a step -/

section CertSpec

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}

/-- **The certificates with the hinted sub-solver.** Under the hypotheses of
`RunsWithin.fullProg`, with its sub-solver replaced by a hinted sub-solver whose certificate
sub-calls (`StepSubP`, wrapped without a hint) satisfy `P`, and `C · none` monotone: the program
computes the full group `F = m5Fmap … x` within `fullCost` at the uniform sub-call cost
`C (n / k) none + 4`. -/
theorem RunsWithin.m5CertProg (hO : MeetsContractOn DV certOps X.O)
    (hPre : ∀ op x, certOps op → GroupPre DV op x → X.Pre op x) {N n : ℕ} {gs : GensData}
    {hC : CertSetting (GensData.denote N gs) n} {φ : strGroup hC →* Perm (Fin (N - n))}
    (hφ : IsPhi hC φ) {d : D.denote} (hGv : GroupValid DV N gs d)
    (hgiant : alternatingGroup (Fin (N - n)) ≤
      (baseHom (GensData.denote N gs) n hC.base).range)
    {k : ℕ} (h5 : 5 ≤ k) (hk : k + 2 ≤ N - n) (h2k : 2 * k ≤ N - n) (x : StrData) {s : ℕ}
    {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N s G₀) (hs : gs.length ≤ s)
    (hGG₀ : GensData.denote N gs ≤ G₀) {sk : ℕ} (Bk : BackendBounds X DV k sk ⊤)
    (hsk : s ≤ k * (sk + 1)) {Bgen Bl Bgs BF : ℕ}
    (hBg : ∀ gs' : GensData, GensData.AllValid N gs' →
      gs'.length ≤ k.factorial * (s + 1) → GensData.denote N gs' ≤ GensData.denote N gs →
        X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ Bgen)
    (hBl : ∀ π, X.B.call GroupOp.lift ((N, gs, d), (baseWin n N, π))
      (liftModel X.O n (N, gs, d) π) ≤ Bl)
    (hBgs : ∀ al ∈ ksubsD (N - n) k, ∀ b₁ b₂,
      X.B.call GroupOp.generate (N, giantGens X.O n (N, gs, d) al b₁ b₂)
        (giantSetStabModel X.O n (N, gs, d) al b₁ b₂) ≤ Bgs)
    (hBF : ∀ gs' : GensData, GensData.AllValid N gs' → gs'.length ≤ 2 * s →
      GensData.denote N gs' ≤ GensData.denote N gs →
        X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ BF)
    {sub : HInstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)}
    {P : HInstData D → Prop} {C : ℕ → Option ℕ → ℕ} (hsub : HSubSolves X body DV sub P C s)
    (hCmono : ∀ a b, a ≤ b → C a none ≤ C b none) (n₀ : ℕ)
    (hP : ∀ J : InstData D, StepSubP (DV := DV) (GensData.denote N gs) (x, x) n k s J →
      P (J, n₀, n, none)) :
    ∃ F : GroupData D.denote,
      RunsWithin X body (Main.m5CertProg sub n₀ n N k x (N, gs, d)) F
        (fullCost N n k s B.Bstab B.Btr B.Borb Bk.Bgen Bk.Borb Bk.Bstab Bgen
          (C (n / k) none + 4) Bl Bgs BF) ∧
      F.1 = N ∧ GroupValid DV N F.2.1 F.2.2 ∧ F.2.1.length ≤ s ∧
      GensData.denote N F.2.1 = m5Fmap hC φ k (x.denote N) := by
  obtain ⟨F, hrun, hN, hv, hlen, hden⟩ := RunsWithin.fullProg (body := body) hO hPre hφ hGv
    hgiant h5 hk h2k x B hs hGG₀ Bk hsk hBg hBl hBgs hBF
    (m5_stepSub hsub hCmono (by omega) hC (x, x) hP)
  exact ⟨F, hrun, hN, hv, hlen, ag_denotes_iff.1 hden⟩

/-- The number of certificate sub-calls: `C(m, k)` test sets, each with `n` rounds of `k!`
branches of at most `n` sub-calls. -/
def certCount (N n k : ℕ) : ℕ := (N - n).choose k * (n * (k.factorial * n))

/-- The work of the certificates besides their sub-calls. -/
def certWork (N n k s Bstab Btr Borb Bgen' Borb' Bstab' Bgen Bl Bgs BF : ℕ) : ℕ :=
  ksubsCost (N - n) k + BF + (N - n).choose k *
    (k.factorial * certPoly N n k s Bstab Btr Borb Bgen' Borb' Bstab' Bgen Bl Bgs +
      2 * N + 13 * k + s + BF + 31) + 10

/-- **The certificates by count**: `fullCost` is at most `certCount` sub-calls of cost `Cb`
each, plus the work `certWork`. -/
theorem fullCost_le_count (N n k s Bstab Btr Borb Bgen' Borb' Bstab' Bgen Cb Bl Bgs BF : ℕ) :
    fullCost N n k s Bstab Btr Borb Bgen' Borb' Bstab' Bgen Cb Bl Bgs BF ≤
      certCount N n k * Cb + certWork N n k s Bstab Btr Borb Bgen' Borb' Bstab' Bgen Bl Bgs BF := by
  have h1 := certCost_le N n k s Bstab Btr Borb Bgen' Borb' Bstab' Bgen Cb Bl Bgs
  unfold fullCost fullStepCost certCount certWork
  generalize certCost N n k s Bstab Btr Borb Bgen' Borb' Bstab' Bgen Cb Bl Bgs = A at h1
  generalize certPoly N n k s Bstab Btr Borb Bgen' Borb' Bstab' Bgen Bl Bgs = Q at h1 ⊢
  generalize (N - n).choose k = c
  have h2 : c * (A + 2 * N + 13 * k + s + BF + 30 + 1) ≤
      c * (k.factorial * Q + n * (k.factorial * (n * Cb)) + 2 * N + 13 * k + s + BF + 31) :=
    Nat.mul_le_mul_left _ (by omega)
  have h3 : c * (k.factorial * Q + n * (k.factorial * (n * Cb)) + 2 * N + 13 * k + s + BF + 31) =
      c * (n * (k.factorial * n)) * Cb +
        c * (k.factorial * Q + 2 * N + 13 * k + s + BF + 31) := by ring
  omega

end CertSpec

/-! ### Separating Case 2a from Case 2b -/

section Alt

/-- **A `(k − 2)`-transitive group contains the alternating group**: if `P` preserves `Φ` and
moves any `|Φ| − 2` points of `Φ` to any other, every even permutation of `Φ` is induced by an
element of `P` (mathlib's `IsMultiplyPretransitive.alternatingGroup_le`, through the numbered
action of `P` on `Φ`). -/
theorem alt_le_of_tupTrans {Γ : Type*} [DecidableEq Γ] {P : Subgroup (Perm Γ)} {Φ : Finset Γ}
    (hpres : ∀ g ∈ P, ∀ x ∈ Φ, g x ∈ Φ) (htt : Case2b.TupTrans P Φ (Φ.card - 2)) :
    ∀ π : Perm Φ, Perm.sign π = 1 → ∃ g ∈ P, ∀ v : Φ, g v = π v := by
  let e : Fin Φ.card ↪ Γ := ⟨fun j => (Φ.equivFin.symm j : Γ), fun i j hij =>
    Φ.equivFin.symm.injective (Subtype.ext hij)⟩
  have hΦ : ∀ v, v ∈ Φ ↔ ∃ j, e j = v := fun v =>
    ⟨fun hv => ⟨Φ.equivFin ⟨v, hv⟩, show (Φ.equivFin.symm (Φ.equivFin ⟨v, hv⟩) : Γ) = v by
      simp⟩, fun ⟨j, hj⟩ => hj ▸ (Φ.equivFin.symm j).2⟩
  have hmaps : ∀ g ∈ P, ∀ i, ∃ j, g (e i) = e j := fun g hg i =>
    ((hΦ _).1 (hpres g hg _ ((hΦ _).2 ⟨i, rfl⟩))).imp fun _ h => h.symm
  have hiff := Case2b.cp2_multTrans_iff (P := P) (Q := Case2b.fixGroup P ∅ e) (Φ := Φ)
    e.injective hΦ
    (fun p hp => by
      obtain ⟨q, hq, hqe⟩ := Case2b.cb_realize (S := ∅) hp
        (fun s hs => absurd hs (Finset.notMem_empty s)) (hmaps p hp)
      exact ⟨q, hq, hqe⟩)
    (fun q hq => by
      obtain ⟨p, hp, -, hpe⟩ := hq
      exact ⟨p, hp, hpe⟩) (Φ.card - 2)
  have hmt := hiff.2 htt
  rw [show Φ.card - 2 = Nat.card (Fin Φ.card) - 2 by simp] at hmt
  have halt := IsMultiplyPretransitive.alternatingGroup_le (Fin Φ.card) _ hmt
  intro π hπ
  let β : Φ ≃ Fin Φ.card := Φ.equivFin
  have hmem : β.permCongr π ∈ Case2b.fixGroup P ∅ e := by
    apply halt
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_permCongr, hπ]
  obtain ⟨p, hp, -, hpe⟩ := hmem
  refine ⟨p, hp, fun v => ?_⟩
  have hv : e (β v) = (v : Γ) := by
    show (Φ.equivFin.symm (Φ.equivFin v) : Γ) = v
    simp
  have h1 := hpe (β v)
  rw [hv] at h1
  rw [h1]
  show (Φ.equivFin.symm (β.permCongr π (β v)) : Γ) = π v
  simp [β, Equiv.permCongr_apply]

end Alt

/-! ### The case decision -/

section CaseFacts

theorem m5_mem_phiSet {N : ℕ} {l : List ℕ} {v : Fin N} : v ∈ phiSet N l ↔ v.val ∈ l := by
  simp [phiSet]

/-- The base indices of `Φ` and the positions of `Φ`. -/
def m5PhiEquiv {n N : ℕ} {Φ : List ℕ} (hΦl : ∀ i ∈ Φ, i < N - n) :
    ↥(SoJProg.setOf (N - n) Φ) ≃ ↥(phiSet N (Φ.map (n + ·))) where
  toFun j := ⟨basePos j.1, m5_mem_phiSet.2 (List.mem_map.2 ⟨j.1.val, SoJProg.mem_setOf.1 j.2,
    rfl⟩)⟩
  invFun v := ⟨⟨v.1.val - n, by
      obtain ⟨i, hi, hiv⟩ := List.mem_map.1 (m5_mem_phiSet.1 v.2)
      have := hΦl i hi
      omega⟩, by
      obtain ⟨i, hi, hiv⟩ := List.mem_map.1 (m5_mem_phiSet.1 v.2)
      rw [SoJProg.mem_setOf]
      simp only
      rw [← hiv, Nat.add_sub_cancel_left]
      exact hi⟩
  left_inv j := by
    apply Subtype.ext
    apply Fin.ext
    simp [basePos]
  right_inv v := by
    apply Subtype.ext
    apply Fin.ext
    obtain ⟨i, hi, hiv⟩ := List.mem_map.1 (m5_mem_phiSet.1 v.2)
    simp only [basePos]
    omega

/-- **Case 2a's `hFalt`**: if `ψ(F)` moves any `|Φ| − 2` points of its orbit `Φ` to any other,
every even permutation of the positions of `Φ` is realized by an element of `F`. -/
theorem m5_hFalt {N n : ℕ} {F : Subgroup (Perm (Fin N))} (hF : IsInvariant F (baseSet n N))
    {Φ : List ℕ} (hΦn : Φ.Nodup) (hΦl : ∀ i ∈ Φ, i < N - n)
    (hΦo : ∃ γ : Fin (N - n), ∀ δ : Fin (N - n),
      δ.val ∈ Φ ↔ δ ∈ MulAction.orbit (baseHom F n hF).range γ)
    (htt : Case2b.TupTrans (baseHom F n hF).range (SoJProg.setOf (N - n) Φ) (Φ.length - 2)) :
    ∀ π : Perm (phiSet N (Φ.map (n + ·))), Perm.sign π = 1 →
      ∃ f ∈ F, ∀ v : phiSet N (Φ.map (n + ·)), f v = π v := by
  obtain ⟨γ, hγ⟩ := hΦo
  have hpres : ∀ g ∈ (baseHom F n hF).range, ∀ x ∈ SoJProg.setOf (N - n) Φ,
      g x ∈ SoJProg.setOf (N - n) Φ := by
    intro g hg x hx
    rw [SoJProg.mem_setOf, hγ] at hx ⊢
    exact Case2b.cp2_orbit_pres hg hx
  have hcard : (SoJProg.setOf (N - n) Φ).card = Φ.length := SoJProg.card_setOf hΦn hΦl
  have halt := alt_le_of_tupTrans hpres (by rw [hcard]; exact htt)
  intro π hπ
  let γe := m5PhiEquiv (n := n) (N := N) hΦl
  obtain ⟨g, hg, hgv⟩ := halt (γe.symm.permCongr π) (by rw [Perm.sign_permCongr, hπ])
  obtain ⟨⟨f, hf⟩, rfl⟩ := hg
  refine ⟨f, hf, fun v => ?_⟩
  have hv : (v : Fin N) = basePos (γe.symm v).1 := by
    have := congrArg Subtype.val (γe.apply_symm_apply v)
    rw [← this]
    rfl
  have h1 := hgv (γe.symm v)
  rw [Equiv.permCongr_apply, Equiv.symm_symm, Equiv.apply_symm_apply] at h1
  rw [hv, ← baseHom_apply (hG := hF) ⟨f, hf⟩, h1]
  have := congrArg Subtype.val (γe.apply_symm_apply (π v))
  rw [← this]
  rfl

/-- **The degree decides Case 2a**: with `d` points moved and not `d + 1` (when `d < |Φ|`),
`P` moves any `|Φ| − 2` points of `Φ` exactly when `|Φ| − 2 ≤ d`. -/
theorem m5_tupTrans_iff {Γ : Type*} [DecidableEq Γ] {P : Subgroup (Perm Γ)} {Φ : Finset Γ}
    (hpres : ∀ g ∈ P, ∀ x ∈ Φ, g x ∈ Φ) {d : ℕ} (hd : d ≤ Φ.card)
    (htr : Case2b.TupTrans P Φ d) (hnot : d < Φ.card → ¬ Case2b.TupTrans P Φ (d + 1)) :
    Case2b.TupTrans P Φ (Φ.card - 2) ↔ Φ.card - 2 ≤ d := by
  constructor
  · intro h
    by_contra hlt
    exact hnot (by omega) (Case2b.cp2_tupTrans_mono hpres h (by omega) (by omega))
  · intro h
    exact Case2b.cp2_tupTrans_mono hpres htr h hd

end CaseFacts

/-! ### The case decision as a program -/

section CaseSpec

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}

/-- The operations of the case decision. -/
def m5CaseOps (op : GroupOp) : Prop := Giant.caseOps op ∨ Case2b.degOps op

/-- The orbits of `F` on the base, as base indices. -/
def m5Os (O : Oracle (groupSig D)) (n N : ℕ) (F : GroupData D.denote) : List (List ℕ) :=
  agShiftD n (O.run GroupOp.orbits (F, baseWin n N))

/-- The case and the large orbit `Φ`. -/
def m5Cs (O : Oracle (groupSig D)) (n N : ℕ) (F : GroupData D.denote) : ℕ × List ℕ :=
  caseD (N - n) (m5Os O n N F)

/-- Case 2a (as opposed to 2b): in Case 2, the degree of `ψ(F)` on `Φ` is at least `|Φ| − 2`. -/
def m5IsA (O : Oracle (groupSig D)) (n N : ℕ) (F : GroupData D.denote) : Bool :=
  cond ((m5Cs O n N F).1 == 2)
    (!decide (Case2b.degD O N n F (m5Cs O n N F).2 < (m5Cs O n N F).2.length - 2)) false

/-- The value of `m5CaseProg`. -/
def m5CaseD (O : Oracle (groupSig D)) (n N : ℕ) (F : GroupData D.denote) :
    ((ℕ × List ℕ) × List (List ℕ)) × Bool :=
  ((m5Cs O n N F, m5Os O n N F), m5IsA O n N F)

/-- The cost of `m5CaseProg`, with `ldeg` the cost of the degree program. -/
def m5CaseCost (n N Borb ldeg : ℕ) : ℕ := caseCost n N Borb + ldeg + (N - n) + 12

/-- **The case decision as a program**: `caseProg`'s value, and in Case 2 the Case 2a test,
within `caseCost` plus the degree program on `Φ`. -/
theorem RunsWithin.m5CaseProg (hO : MeetsContractOn DV m5CaseOps X.O)
    (hPre : ∀ op x, m5CaseOps op → GroupPre DV op x → X.Pre op x) {N n s : ℕ}
    {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N s G₀) {sm : ℕ → ℕ}
    (Bm : ∀ M, BackendBounds X DV M (sm M) ⊤) {fs : GensData} {fd : D.denote}
    (hFv : GroupValid DV N fs fd) (hs : fs.length ≤ s) (hG₀ : GensData.denote N fs ≤ G₀)
    (hF : IsInvariant (GensData.denote N fs) (baseSet n N)) {Bg : ℕ}
    (hBg : ∀ M ≤ N - n, ∀ gs' : GensData, GensData.AllValid M gs' → gs'.length ≤ s →
      X.B.call GroupOp.generate (M, gs') (X.O.run GroupOp.generate (M, gs')) ≤ Bg) :
    RunsWithin X body (Main.m5CaseProg n N (N, fs, fd)) (m5CaseD X.O n N (N, fs, fd))
      (m5CaseCost n N B.Borb (Case2b.degCost N n (m5Cs X.O n N (N, fs, fd)).2.length
        (m5Cs X.O n N (N, fs, fd)).2.length s B.Bstab Bg
        (Bm (m5Cs X.O n N (N, fs, fd)).2.length).Borb
        (Bm (m5Cs X.O n N (N, fs, fd)).2.length).Bstab)) := by
  obtain ⟨hrun, hos⟩ := RunsWithin.caseProg (body := body)
    (fun op x h hp => hO op x (Or.inl h) hp) (fun op x h hp => hPre op x (Or.inl h) hp)
    hFv hF B hs hG₀
  set Φ := (m5Cs X.O n N (N, fs, fd)).2 with hΦdef
  set dc := Case2b.degCost N n Φ.length Φ.length s B.Bstab Bg (Bm Φ.length).Borb
    (Bm Φ.length).Bstab with hdc
  have hite : RunsWithin X body
      (Prog.ite ((m5Cs X.O n N (N, fs, fd)).1 == 2)
        (.bind (Case2b.degProg N n (N, fs, fd) Φ) fun dg =>
          .bind (.op1 (Prim.length (a := .nat)) Φ) fun l => .bind (.op2 .sub l 2) fun l2 =>
          .bind (.op2 .natLt dg l2) fun lt => .op1 .not lt)
        (.op0 (.boolLit false)))
      (m5IsA X.O n N (N, fs, fd)) (dc + (N - n) + 6) := by
    by_cases h2 : (m5Cs X.O n N (N, fs, fd)).1 = 2
    · have hb : ((m5Cs X.O n N (N, fs, fd)).1 == 2) = true := by simp [h2]
      have hc := (caseD_spec hF hos).2.1 h2
      have hnd : Φ.Nodup := hc.1
      have hlt : ∀ i ∈ Φ, i < N - n := hc.2.1
      obtain ⟨γ, -, hγ⟩ := hc.2.2.2
      have hΦi := Case2b.cp2_inv_of_orbit (Φ := Φ) hF hlt ⟨γ, hγ⟩
      have hdeg := Case2b.RunsWithin.degProg_le (body := body)
        (fun op x h hp => hO op x (Or.inr h) hp) (fun op x h hp => hPre op x (Or.inr h) hp)
        B Bm hFv hs hG₀ hnd hlt hΦi hBg
      have hlen : Φ.length ≤ N - n := by
        have := SoJProg.card_setOf hnd hlt
        rw [← this]
        exact (Finset.card_le_univ _).trans (by simp)
      rw [hb]
      apply RunsWithin.mono
      case h =>
        apply RunsWithin.ite_true
        run_step hdeg
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        refine (RunsWithin.prim _ _).of_eq ?_
        simp only [Prim.eval, m5IsA, hb, Bool.cond_true, hΦdef]
      case hc =>
        simp [Prim.cost]
        omega
    · have hb : ((m5Cs X.O n N (N, fs, fd)).1 == 2) = false := by simp [h2]
      rw [hb]
      have hv : m5IsA X.O n N (N, fs, fd) = false := by simp [m5IsA, hb]
      rw [hv]
      apply RunsWithin.mono
      case h => exact RunsWithin.ite_false (RunsWithin.prim _ _)
      case hc =>
        simp only [Prim.cost]
        omega
  apply RunsWithin.mono
  case h =>
    unfold Main.m5CaseProg
    run_step hrun
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step hite
    exact RunsWithin.prim _ _
  case hc =>
    simp only [Prim.cost, m5CaseCost]
    omega

/-- **The meaning of the case decision.** The orbits are an exact orbit partition (so
`caseD_spec` applies to `m5Cs`); in Case 2, when the test says 2a, every even permutation of the
positions of `Φ` is realized by `F` (`hFalt` of `case2aProg_canonical`); when it says 2b,
`ψ(F)` does not move any `|Φ| − 2` points of `Φ` to any other (`hngx` of
`case2bProg_canonical'`). -/
theorem m5Case_spec (hO : MeetsContractOn DV m5CaseOps X.O)
    (hPre : ∀ op x, m5CaseOps op → GroupPre DV op x → X.Pre op x) {N n s : ℕ}
    {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N s G₀) {sm : ℕ → ℕ}
    (Bm : ∀ M, BackendBounds X DV M (sm M) ⊤) {fs : GensData} {fd : D.denote}
    (hFv : GroupValid DV N fs fd) (hs : fs.length ≤ s) (hG₀ : GensData.denote N fs ≤ G₀)
    (hF : IsInvariant (GensData.denote N fs) (baseSet n N)) :
    IsOrbitPartition (GensData.denote N fs) (baseWin n N)
        (X.O.run GroupOp.orbits ((N, fs, fd), baseWin n N)) ∧
      ((m5Cs X.O n N (N, fs, fd)).1 = 2 → m5IsA X.O n N (N, fs, fd) = true →
        ∀ π : Perm (phiSet N ((m5Cs X.O n N (N, fs, fd)).2.map (n + ·))), Perm.sign π = 1 →
          ∃ f ∈ GensData.denote N fs,
            ∀ v : phiSet N ((m5Cs X.O n N (N, fs, fd)).2.map (n + ·)), f v = π v) ∧
      ((m5Cs X.O n N (N, fs, fd)).1 = 2 → m5IsA X.O n N (N, fs, fd) = false →
        ¬ Case2b.TupTrans (baseHom (GensData.denote N fs) n hF).range
          (SoJProg.setOf (N - n) (m5Cs X.O n N (N, fs, fd)).2)
          ((m5Cs X.O n N (N, fs, fd)).2.length - 2)) := by
  obtain ⟨-, hos⟩ := RunsWithin.caseProg (X := X) (a := Ty.unit) (b := Ty.unit)
    (body := fun u => .ret u)
    (fun op x h hp => hO op x (Or.inl h) hp) (fun op x h hp => hPre op x (Or.inl h) hp)
    hFv hF B hs hG₀
  refine ⟨hos, ?_⟩
  set Φ := (m5Cs X.O n N (N, fs, fd)).2 with hΦdef
  -- the facts on `Φ` in Case 2
  have key : (m5Cs X.O n N (N, fs, fd)).1 = 2 →
      (Case2b.TupTrans (baseHom (GensData.denote N fs) n hF).range (SoJProg.setOf (N - n) Φ)
        (Φ.length - 2) ↔ m5IsA X.O n N (N, fs, fd) = true) ∧ Φ.Nodup ∧ (∀ i ∈ Φ, i < N - n) ∧
      ∃ γ : Fin (N - n), ∀ δ : Fin (N - n),
        δ.val ∈ Φ ↔ δ ∈ MulAction.orbit (baseHom (GensData.denote N fs) n hF).range γ := by
    intro h2
    have hc := (caseD_spec hF hos).2.1 h2
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
    refine ⟨?_, hnd, hlt, γ, hγ⟩
    rw [hiff]
    have hb : ((m5Cs X.O n N (N, fs, fd)).1 == 2) = true := by simp [h2]
    simp only [m5IsA, hb, Bool.cond_true, ← hΦdef, Bool.not_eq_true', decide_eq_false_iff_not,
      not_lt]
  refine ⟨fun h2 hA => ?_, fun h2 hA hT => ?_⟩
  · obtain ⟨hiff, hnd, hlt, hΦo⟩ := key h2
    exact m5_hFalt hF hnd hlt hΦo (hiff.2 hA)
  · obtain ⟨hiff, -, -, -⟩ := key h2
    rw [hiff.1 hT] at hA
    exact absurd hA (by simp)

end CaseSpec

/-! ### Well-formedness -/

section Wf

variable {D : Ty} {rec : Ty × Ty} {var₁ var₂ : Ty → Type} {r : Bool} {Γ : WfCtx var₁ var₂}

theorem wf_m5CertProg {sub₁ : var₁ (hinstTy D) → Prog (groupSig D) rec var₁ (Ty.answer D)}
    {sub₂ : var₂ (hinstTy D) → Prog (groupSig D) rec var₂ (Ty.answer D)}
    (hsub : WfFun r Γ sub₁ sub₂) {n₀₁ n₁ N₁ k₁ : var₁ .nat} {n₀₂ n₂ N₂ k₂ : var₂ .nat}
    {x₁ : var₁ Ty.str} {x₂ : var₂ Ty.str} {G₁ : var₁ (Ty.group D)} {G₂ : var₂ (Ty.group D)}
    (hn₀ : ⟨.nat, n₀₁, n₀₂⟩ ∈ Γ) (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (hN : ⟨.nat, N₁, N₂⟩ ∈ Γ)
    (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ) (hx : ⟨Ty.str, x₁, x₂⟩ ∈ Γ) (hG : ⟨Ty.group D, G₁, G₂⟩ ∈ Γ) :
    Prog.Wf r Γ (m5CertProg sub₁ n₀₁ n₁ N₁ k₁ x₁ G₁) (m5CertProg sub₂ n₀₂ n₂ N₂ k₂ x₂ G₂) :=
  wf_fullProg (wf_plainSub hsub hn₀ hn) hn hN hk hx hG

theorem wf_m5CaseProg {n₁ N₁ : var₁ .nat} {n₂ N₂ : var₂ .nat} {F₁ : var₁ (Ty.group D)}
    {F₂ : var₂ (Ty.group D)} (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (hN : ⟨.nat, N₁, N₂⟩ ∈ Γ)
    (hF : ⟨Ty.group D, F₁, F₂⟩ ∈ Γ) :
    Prog.Wf (rec := rec) r Γ (m5CaseProg n₁ N₁ F₁) (m5CaseProg n₂ N₂ F₂) := by
  unfold m5CaseProg
  refine .bind (wf_caseProg hn hN hF) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (.prim _ .nil) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) (.cons (List.Mem.head _) .nil))) fun _ _ => ?_
  refine .bind (.ite (List.Mem.head _) ?_ (.prim _ .nil)) fun _ _ => ?_
  · refine .bind (Case2b.wf_degProg (by simp [hN]) (by simp [hn]) (by simp [hF]) (by simp))
      fun _ _ => ?_
    refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
    refine .bind (.prim _ (.cons (List.Mem.head _) (.cons (by simp) .nil))) fun _ _ => ?_
    refine .bind (.prim _ (.cons (by simp) (.cons (List.Mem.head _) .nil))) fun _ _ => ?_
    exact .prim _ (.cons (List.Mem.head _) .nil)
  · exact .prim _ (.cons (by simp) (.cons (List.Mem.head _) .nil))

end Wf

end GraphIso.Main
