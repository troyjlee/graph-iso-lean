module

public import GraphIso.Main.M5Align
public import GraphIso.Main.M5Cert
public import GraphIso.Giant.Case1
public import GraphIso.Case3.Case3Prog

/-!
# M5: the four giant cases

Stage 14j-4, items 4–5 (`PLAN-14.md` §14.4). On a hinted instance after the restriction of item 1
(`Main/M5Restrict.lean`): the string positions `[0, n)` all lie in the window, the coset
representative is `1`, the group `G` is faithful on the strings with a giant base action and
transitive on the window, the labels are valid. The case programs of stages 14g–14i are run with
the main recursion's sub-solver:

* **Align with reduce-and-derive** (`m5_alignSub`): for any structure `X₀` and the aligned group
  `K = ψ⁻¹(Stab(X₀))` (`g1Model`), reduce-and-derive's per-coset program `rdBranch` meets Align's
  sub-solver hypothesis (one uniform cost: the most expensive branch, `ar_branch_max`), with
  `StepChild` children whose windows sum to at most `F · |W|` per call.
* **Case 1** (`m5Case1Prog`): `case1Prog` with `rdBranch`; `RunsWithin.m5Case1Prog` (factor
  `F`), and `RunsWithin.m5Case1Prog_ns`: under Case 1's conditions the orbit partition of `ψ(F)`
  is a colored `⌊m/2⌋`-partition (`orbitPart_valid`) preserved by `K`, so no orbit is stuck
  (`rd_ns_part`) and the factor is `m`.

**The children's generators** (stage 14j-5a, `PLAN-14.md` §14.6). Reduce-and-derive's children
have at most `sIn` generators (`SizeChild sIn`). Case 2a's pullback sub-calls are restricted to
their windows, so their groups are `generate` outputs at degrees at most `|W| / 2`:
`RunsWithin.m5Case2aProg` takes a fresh bound `sR` with the hypothesis `hgR` that `generate`
returns at most `sR` generators there, on valid inputs of at most `s` generators. Some `sR` meets
it for every backend (`m5_exists_genOut_le`: finitely many such inputs).
-/

@[expose] public section

namespace GraphIso.Main

open Equiv MulAction Pointwise Cost GraphIso GraphIso.Programs GraphIso.Toolkit
  GraphIso.Recursion GraphIso.SplitJohnson GraphIso.Solver GraphIso.Align GraphIso.Certificates
  GraphIso.CertProg

/-! ### Align with reduce-and-derive, as a sub-solver -/

section AlignSub

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}
  {sub : HInstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)}
  {C : ℕ → Option ℕ → ℕ} {s : ℕ} {xy : StrData × StrData} {w : WinData}
  {N : ℕ} {gs : GensData} {d : D.denote} {n₀ n : ℕ} {L : LabelData} {st : ℕ × CJData}
  {sIn Lg F Blift Bgen Bo Bk Bcr Bd W6 : ℕ}

/-- **Reduce-and-derive meets Align's sub-solver hypothesis.** For a structure `X₀` with the
aligned group `K = g1Model … S X₀` (`c2_g1_spec`) meeting `rd_branch`'s hypotheses, one children
list `ch₀` (`StepChild`, windows summing to at most `F · |W|`) bounds every branch, and
`rdBranch` solves every aligned coset `t • K` within `Σ_{ch₀} C + Wb`. -/
theorem m5_alignSub {τ O : Type} [MulAction (Perm (Fin (N - n))) O]
    (hOa : MeetsContractOn DV alignOps X.O)
    (hPa : ∀ op x, alignOps op → GroupPre DV op x → X.Pre op x)
    (hO : MeetsContractOn DV rdOps X.O)
    (hPre : ∀ op x, rdOps op → GroupPre DV op x → X.Pre op x)
    (hI : HInstValid DV (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D))
    (hG : IsInvariant (GensData.denote N gs) (baseSet n N))
    (halt : alternatingGroup (Fin (N - n)) ≤ (baseHom _ n hG).range)
    {s₀ : ℕ} {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N s₀ G₀)
    (hGG₀ : GensData.denote N gs ≤ G₀) (hs₀ : s₀ ≤ sIn)
    {S : StructOps (N - n) τ O} {Valid : τ → Prop} (hS : S.Spec Valid) {X₀ : τ}
    (hX : Valid X₀) {BlA : ℕ}
    (hBlA : ∀ π : PermData, X.B.call GroupOp.lift ((N, gs, d), (baseWin n N, π))
      (liftModel X.O n (N, gs, d) π) ≤ BlA)
    (hsub : HSubSolves X body DV sub
      (fun J => SizeChild sIn (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D)
        J ∧ StepChild w.1.length (N - n) (J.winSize, J.baseOpt)) C s)
    (hB : RDBounds X DV n N sIn Lg Blift Bgen Bo Bk Bcr) (hs : s ≤ sIn)
    (hLg : F * (sIn + 1) ≤ Lg) (hF1 : 1 ≤ F) (hFm : N - n ≤ F)
    (hD : ∀ gs' d' O',
      RDSet DV n N gs w L (Giant.g1Model X.O n (N, gs, d) S X₀).2.1 sIn gs' d' O' →
      RDOrbit X body DV n N w L st sIn Bd gs' d' O')
    (h5 : (N - n).factorial ≤ F ∨ ∀ gs' d' O',
      RDSet DV n N gs w L (Giant.g1Model X.O n (N, gs, d) S X₀).2.1 sIn gs' d' O' →
      (deriveModel X.O n N (N, gs', d') O' L st).1 = 5 →
        (deriveModel X.O n N (N, gs', d') O' L st).2.1.2.2.length ≤ F)
    (h6 : (∀ gs' d' O',
        RDSet DV n N gs w L (Giant.g1Model X.O n (N, gs, d) S X₀).2.1 sIn gs' d' O' →
        (deriveModel X.O n N (N, gs', d') O' L st).1 ≠ 6) ∨
      ((N - n).factorial ≤ F ∧ rd6Cost N n w.1.length s sIn Bk Bo Bcr Bgen ≤ W6)) :
    ∃ ch₀ : List (ℕ × Option ℕ),
      ((ch₀.map Prod.fst).sum ≤ F * w.1.length ∧
        (∀ x ∈ ch₀, StepChild w.1.length (N - n) x) ∧ ∀ x ∈ ch₀, 1 ≤ x.1) ∧
      SubSolves X body DV
        (Main.rdBranch (var := Ty.denote) (rec := (a, b)) (D := D) sub n₀ n L st)
        (fun I => I.1 = xy ∧ I.2.1 = w ∧
          I.2.2.2 = preModel X.O n (N, gs, d)
            (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d)) (S.gens X₀))) ∧ I.Valid DV)
        (fun _ => (ch₀.map fun x => C x.1 x.2).sum +
          (w.1.length * rdOrbitWork N n w.1.length s sIn F Bd Blift Bgen Bo W6 +
            dynSeqCost N w.1.length Bo + 5)) sIn := by
  have hGv : GroupValid DV N gs d := hI.valid.group
  obtain ⟨hdeg, hKv, hKden, hKs₀⟩ := Giant.c2_g1_spec hOa hPa B hGv hGG₀ hG halt hS hX hBlA
  have hKm' : preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
      (S.gens X₀))) = Giant.g1Model X.O n (N, gs, d) S X₀ := rfl
  rcases hKm : Giant.g1Model X.O n (N, gs, d) S X₀ with ⟨N', gsK, dK⟩
  rw [hKm] at hdeg hKv hKden hKs₀ hD h5 h6 hKm'
  change N' = N at hdeg
  subst hdeg
  have hKG : GensData.denote N' gsK ≤ GensData.denote N' gs := by
    rw [hKden]
    exact Subgroup.map_subtype_le _
  obtain ⟨ch₀, hgood, hbr⟩ := ar_branch_max (C := C) (Bk := Bk) (Bcr := Bcr) (W6 := W6) hO hPre
    hI hsub hB hs hLg hF1 hFm hKv hKG (hKs₀.trans hs₀) hD h5 h6
  refine ⟨ch₀, hgood, ?_⟩
  rintro ⟨xy', w', t, G'⟩ ⟨h1, h2, h3, hv⟩
  change xy' = xy at h1
  change w' = w at h2
  change G' = _ at h3
  rw [hKm'] at h3
  subst h1 h2 h3
  have ht : t.Valid N' := hv.rep
  obtain ⟨ans, hrun, hok, hg⟩ := hbr t ht
  exact ⟨ans, hrun, hok, hg⟩

/-- Copies of one children list: the sum of the windows. -/
theorem m5_replicate_childList {k F p m : ℕ} {ch₀ : List (ℕ × Option ℕ)}
    (hgood : (ch₀.map Prod.fst).sum ≤ F * p ∧ (∀ x ∈ ch₀, StepChild p m x) ∧ ∀ x ∈ ch₀, 1 ≤ x.1) :
    ChildList p (k * F) (StepChild p m) (List.replicate k ch₀).flatten := by
  refine ⟨?_, fun x hx => ?_, fun x hx => ?_⟩
  · rw [List.map_flatten, List.sum_flatten, List.map_replicate, List.map_replicate,
      List.sum_replicate, smul_eq_mul]
    calc k * (ch₀.map Prod.fst).sum ≤ k * (F * p) := Nat.mul_le_mul_left k hgood.1
      _ = k * F * p := (Nat.mul_assoc _ _ _).symm
  · obtain ⟨l, hl, hxl⟩ := List.mem_flatten.1 hx
    rw [List.eq_of_mem_replicate hl] at hxl
    exact hgood.2.1 x hxl
  · obtain ⟨l, hl, hxl⟩ := List.mem_flatten.1 hx
    rw [List.eq_of_mem_replicate hl] at hxl
    exact hgood.2.2 x hxl

/-- The children's cost of copies of one list. -/
theorem m5_replicate_cost {k : ℕ} {ch₀ : List (ℕ × Option ℕ)} :
    ((List.replicate k ch₀).flatten.map fun x => C x.1 x.2).sum =
      k * (ch₀.map fun x => C x.1 x.2).sum := by
  rw [List.map_flatten, List.sum_flatten, List.map_replicate, List.map_replicate,
    List.sum_replicate, smul_eq_mul]

end AlignSub

/-! ### Case 1 -/

section Case1Prog

variable {D : Ty} {rec : Ty × Ty} {var : Ty → Type}

/-- **Case 1 of M5**: stage 14g's `case1Prog` (the orbit partitions of `ψ(F(x))`, `ψ(F(y))`
aligned) with reduce-and-derive's per-coset program as Align's sub-solver. -/
def m5Case1Prog (sub : var (hinstTy D) → Prog (groupSig D) rec var (Ty.answer D))
    (n₀ n : var .nat) (L : var (.array (.list .nat))) (st : var stTy) (xy : var Ty.strs)
    (w : var Ty.win) (G Fx Fy : var (Ty.group D)) : Prog (groupSig D) rec var (Ty.answer D) :=
  Giant.case1Prog (fun J => Main.rdBranch sub n₀ n L st J) n xy w G Fx Fy

end Case1Prog

/-- Case 1's cost is affine in the cost of the one candidate. -/
theorem case1Cost_add (n N g k Box Boy BgP Bmem Bk Bl Bg1 Bgen A Cb s : ℕ) :
    Giant.case1Cost n N g k Box Boy BgP Bmem Bk Bl Bg1 Bgen (A + Cb) s =
      Giant.case1Cost n N g k Box Boy BgP Bmem Bk Bl Bg1 Bgen Cb s + A := by
  simp only [Giant.case1Cost, alignCost_add]
  ring

section Case1Spec

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}
  {sub : HInstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)}
  {C : ℕ → Option ℕ → ℕ} {s : ℕ} {xy : StrData × StrData} {w : WinData}
  {N : ℕ} {gs : GensData} {d : D.denote} {n₀ n : ℕ} {L : LabelData} {st : ℕ × CJData}
  {sIn Lg F Blift Bgen Bo Bk Bcr Bd W6 : ℕ}

/-- **Case 1 of M5.** Under `case1Prog`'s hypotheses (a canonical full-group map `Fmap` with
`Fx = F(x)`, `Fy = F(y)`), and reduce-and-derive's for the aligned group of the orbit partition
of `ψ(F(x))`: the answer is correct for `G` on `W`, and the children are `StepChild |W| m` with
windows summing to at most `F · |W|` (one candidate). -/
theorem RunsWithin.m5Case1Prog (hOc : MeetsContractOn DV Giant.case1Ops X.O)
    (hPc : ∀ op x, Giant.case1Ops op → GroupPre DV op x → X.Pre op x)
    (hO : MeetsContractOn DV rdOps X.O)
    (hPre : ∀ op x, rdOps op → GroupPre DV op x → X.Pre op x)
    (hI : HInstValid DV (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D))
    (hG : IsInvariant (GensData.denote N gs) (baseSet n N))
    (halt : alternatingGroup (Fin (N - n)) ≤ (baseHom _ n hG).range)
    {s₀ : ℕ} {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N s₀ G₀)
    (hGG₀ : GensData.denote N gs ≤ G₀) (hs₀ : s₀ ≤ sIn)
    {Fmap : (Fin N → ℕ) → Subgroup (Perm (Fin N))} (hFG : ∀ x, Fmap x ≤ GensData.denote N gs)
    (hloc : ∀ x x', (∀ u ∈ w.denote N, x u = x' u) → Fmap x = Fmap x')
    (heq : ∀ g ∈ GensData.denote N gs, ∀ x,
      Fmap (relabel g x) = (Fmap x).map (MulAut.conj g).toMonoidHom)
    {fxs fys : GensData} {ex ey : D.denote} (hFxv : GroupValid DV N fxs ex)
    (hFyv : GroupValid DV N fys ey) (hFx : GensData.denote N fxs = Fmap (xy.1.denote N))
    (hFy : GensData.denote N fys = Fmap (xy.2.denote N))
    {Box Boy BgP Bmem BkA BlA Bg1 : ℕ}
    (hBox : X.B.call GroupOp.orbits ((N, fxs, ex), baseWin n N)
      (Giant.baseOrbits X.O n N (N, fxs, ex)) ≤ Box)
    (hBoy : X.B.call GroupOp.orbits ((N, fys, ey), baseWin n N)
      (Giant.baseOrbits X.O n N (N, fys, ey)) ≤ Boy)
    (hBgP : X.B.call GroupOp.generate (N - n, gs.map (baseD n N))
      (X.O.run GroupOp.generate (N - n, gs.map (baseD n N))) ≤ BgP)
    (hBmem : ∀ g : PermData, g.Valid (N - n) → X.B.call GroupOp.mem (pModel X.O n (N, gs, d), g)
      (X.O.run GroupOp.mem (pModel X.O n (N, gs, d), g)) ≤ Bmem)
    (hBkA : X.B.call GroupOp.kernel ((N, gs, d), baseWin n N) (kerModel X.O n (N, gs, d)) ≤ BkA)
    (hBlA : ∀ π : PermData, X.B.call GroupOp.lift ((N, gs, d), (baseWin n N, π))
      (liftModel X.O n (N, gs, d) π) ≤ BlA)
    (hBg1 : X.B.call GroupOp.generate
      (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
        (partGensD (N - n) (Giant.orbitPartModel X.O n N (N, fxs, ex))))).map
        (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
      (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
        (partGensD (N - n) (Giant.orbitPartModel X.O n N (N, fxs, ex)))))) ≤ Bg1)
    (hsub : HSubSolves X body DV sub
      (fun J => SizeChild sIn (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D)
        J ∧ StepChild w.1.length (N - n) (J.winSize, J.baseOpt)) C s)
    (hB : RDBounds X DV n N sIn Lg Blift Bgen Bo Bk Bcr) (hs : s ≤ sIn)
    (hLg : F * (sIn + 1) ≤ Lg) (hF1 : 1 ≤ F) (hFm : N - n ≤ F)
    (hD : ∀ gs' d' O', RDSet DV n N gs w L (Giant.g1Model X.O n (N, gs, d) (partOps (N - n))
        (Giant.orbitPartModel X.O n N (N, fxs, ex))).2.1 sIn gs' d' O' →
      RDOrbit X body DV n N w L st sIn Bd gs' d' O')
    (h5 : (N - n).factorial ≤ F ∨ ∀ gs' d' O', RDSet DV n N gs w L
      (Giant.g1Model X.O n (N, gs, d) (partOps (N - n))
        (Giant.orbitPartModel X.O n N (N, fxs, ex))).2.1 sIn gs' d' O' →
      (deriveModel X.O n N (N, gs', d') O' L st).1 = 5 →
        (deriveModel X.O n N (N, gs', d') O' L st).2.1.2.2.length ≤ F)
    (h6 : (∀ gs' d' O', RDSet DV n N gs w L (Giant.g1Model X.O n (N, gs, d) (partOps (N - n))
        (Giant.orbitPartModel X.O n N (N, fxs, ex))).2.1 sIn gs' d' O' →
        (deriveModel X.O n N (N, gs', d') O' L st).1 ≠ 6) ∨
      ((N - n).factorial ≤ F ∧ rd6Cost N n w.1.length s sIn Bk Bo Bcr Bgen ≤ W6)) :
    ∃ (ans : AnswerData D) (ch : List (ℕ × Option ℕ)),
      RunsWithin X body
        (Main.m5Case1Prog sub n₀ n L st xy w (N, gs, d) (N, fxs, ex) (N, fys, ey)) ans
        ((ch.map fun x => C x.1 x.2).sum +
          Giant.case1Cost n N gs.length
            (partGensD (N - n) (Giant.orbitPartModel X.O n N (N, fxs, ex))).length
            Box Boy BgP Bmem BkA BlA Bg1 Bgen
            (w.1.length * rdOrbitWork N n w.1.length s sIn F Bd Blift Bgen Bo W6 +
              dynSeqCost N w.1.length Bo + 5) sIn) ∧
      AnsOK DV N (w.denote N) 1 (GensData.denote N gs) (xy.1.denote N) (xy.2.denote N) ans ∧
      (∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sIn) ∧
      ChildList w.1.length (1 * F) (StepChild w.1.length (N - n)) ch := by
  have hOa : MeetsContractOn DV alignOps X.O := fun op x h hx => hOc op x (Or.inl h) hx
  have hPa : ∀ op x, alignOps op → GroupPre DV op x → X.Pre op x :=
    fun op x h hx => hPc op x (Or.inl h) hx
  have hGv : GroupValid DV N gs d := hI.valid.group
  have hFxi : IsInvariant (GensData.denote N fxs) (baseSet n N) := hG.mono (hFx ▸ hFG _)
  have hprex : GroupPre DV .orbits ((N, fxs, ex), baseWin n N) :=
    ⟨hFxv, baseWin_valid n N, by rw [baseWin_denote]; exact hFxi⟩
  have hosx : IsOrbitPartition (GensData.denote N fxs) (baseWin n N)
      (Giant.baseOrbits X.O n N (N, fxs, ex)) := hOc .orbits _ (Or.inr rfl) hprex
  have hX : Giant.C1Valid (N - n) (Giant.orbitPartModel X.O n N (N, fxs, ex)) :=
    Giant.c1_valid_orbitPartD hFxi hosx
  obtain ⟨ch₀, hgood, hsubA⟩ := m5_alignSub (C := C) (W6 := W6) hOa hPa hO hPre hI hG halt B
    hGG₀ hs₀ (Giant.c1_spec (N - n)) hX hBlA hsub hB hs hLg hF1 hFm hD h5 h6
  have hBgen : ∀ gs' : GensData, GensData.AllValid N gs' → gs'.length ≤ 1 * (sIn + 1) →
      GensData.denote N gs' ≤ GensData.denote N gs →
      X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ Bgen :=
    fun gs' hv hl _ => hB.gen N le_rfl gs' hv (hl.trans (by nlinarith))
  obtain ⟨ans, hrun, hok, hg⟩ := Giant.RunsWithin.case1Prog (body := body) hOc hPc hGv hG halt
    hI.valid.win hI.valid.invariant hFG hloc heq hFxv hFyv hFx hFy hBox hBoy hBgP hBmem hBkA
    hBlA hBg1 hBgen hsubA
  refine ⟨ans, (List.replicate 1 ch₀).flatten, ?_, hok,
    hg sIn (fun hs' hv _ => hB.genOut N le_rfl hs' hv), m5_replicate_childList hgood⟩
  refine hrun.mono (le_of_eq ?_)
  rw [m5_replicate_cost, case1Cost_add]
  ring

/-- **Case 1 of M5 with no stuck orbit.** If `st` is not a coloured Johnson structure and
Case 1's conditions hold for `ψ(F(x))` (every orbit has at most `m/2` points, at least `m/2`
points are moved), the orbit partition is a colored `⌊m/2⌋`-partition (`orbitPart_valid`),
preserved by the aligned group, so no orbit is stuck (`rd_ns_part`) and the factor is `m`. -/
theorem RunsWithin.m5Case1Prog_ns (hOc : MeetsContractOn DV Giant.case1Ops X.O)
    (hPc : ∀ op x, Giant.case1Ops op → GroupPre DV op x → X.Pre op x)
    (hO : MeetsContractOn DV rdOps X.O)
    (hPre : ∀ op x, rdOps op → GroupPre DV op x → X.Pre op x)
    (hI : HInstValid DV (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D))
    (hG : IsInvariant (GensData.denote N gs) (baseSet n N))
    (halt : alternatingGroup (Fin (N - n)) ≤ (baseHom _ n hG).range)
    {s₀ : ℕ} {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N s₀ G₀)
    (hGG₀ : GensData.denote N gs ≤ G₀) (hs₀ : s₀ ≤ sIn)
    {Fmap : (Fin N → ℕ) → Subgroup (Perm (Fin N))} (hFG : ∀ x, Fmap x ≤ GensData.denote N gs)
    (hloc : ∀ x x', (∀ u ∈ w.denote N, x u = x' u) → Fmap x = Fmap x')
    (heq : ∀ g ∈ GensData.denote N gs, ∀ x,
      Fmap (relabel g x) = (Fmap x).map (MulAut.conj g).toMonoidHom)
    {fxs fys : GensData} {ex ey : D.denote} (hFxv : GroupValid DV N fxs ex)
    (hFyv : GroupValid DV N fys ey) (hFx : GensData.denote N fxs = Fmap (xy.1.denote N))
    (hFy : GensData.denote N fys = Fmap (xy.2.denote N))
    (hFxi : IsInvariant (GensData.denote N fxs) (baseSet n N))
    (hc1 : ∀ γ : Fin (N - n),
      2 * Nat.card (orbit (baseHom (GensData.denote N fxs) n hFxi).range γ) ≤ N - n)
    (hc2 : N - n ≤ 2 * Nat.card {γ : Fin (N - n) //
      1 < Nat.card (orbit (baseHom (GensData.denote N fxs) n hFxi).range γ)})
    {Box Boy BgP Bmem BkA BlA Bg1 : ℕ}
    (hBox : X.B.call GroupOp.orbits ((N, fxs, ex), baseWin n N)
      (Giant.baseOrbits X.O n N (N, fxs, ex)) ≤ Box)
    (hBoy : X.B.call GroupOp.orbits ((N, fys, ey), baseWin n N)
      (Giant.baseOrbits X.O n N (N, fys, ey)) ≤ Boy)
    (hBgP : X.B.call GroupOp.generate (N - n, gs.map (baseD n N))
      (X.O.run GroupOp.generate (N - n, gs.map (baseD n N))) ≤ BgP)
    (hBmem : ∀ g : PermData, g.Valid (N - n) → X.B.call GroupOp.mem (pModel X.O n (N, gs, d), g)
      (X.O.run GroupOp.mem (pModel X.O n (N, gs, d), g)) ≤ Bmem)
    (hBkA : X.B.call GroupOp.kernel ((N, gs, d), baseWin n N) (kerModel X.O n (N, gs, d)) ≤ BkA)
    (hBlA : ∀ π : PermData, X.B.call GroupOp.lift ((N, gs, d), (baseWin n N, π))
      (liftModel X.O n (N, gs, d) π) ≤ BlA)
    (hBg1 : X.B.call GroupOp.generate
      (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
        (partGensD (N - n) (Giant.orbitPartModel X.O n N (N, fxs, ex))))).map
        (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
      (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
        (partGensD (N - n) (Giant.orbitPartModel X.O n N (N, fxs, ex)))))) ≤ Bg1)
    (hsub : HSubSolves X body DV sub
      (fun J => SizeChild sIn (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D)
        J ∧ StepChild w.1.length (N - n) (J.winSize, J.baseOpt)) C s)
    (hB : RDBounds X DV n N sIn Lg Blift Bgen Bo Bk Bcr) (hs : s ≤ sIn)
    (hLg : (N - n) * (sIn + 1) ≤ Lg) (hm : 2 ≤ N - n) (hst : st.1 ≠ 2)
    (hD : ∀ gs' d' O', RDSet DV n N gs w L (Giant.g1Model X.O n (N, gs, d) (partOps (N - n))
        (Giant.orbitPartModel X.O n N (N, fxs, ex))).2.1 sIn gs' d' O' →
      RDOrbit X body DV n N w L st sIn Bd gs' d' O') :
    ∃ (ans : AnswerData D) (ch : List (ℕ × Option ℕ)),
      RunsWithin X body
        (Main.m5Case1Prog sub n₀ n L st xy w (N, gs, d) (N, fxs, ex) (N, fys, ey)) ans
        ((ch.map fun x => C x.1 x.2).sum +
          Giant.case1Cost n N gs.length
            (partGensD (N - n) (Giant.orbitPartModel X.O n N (N, fxs, ex))).length
            Box Boy BgP Bmem BkA BlA Bg1 Bgen
            (w.1.length * rdOrbitWork N n w.1.length s sIn (N - n) Bd Blift Bgen Bo 0 +
              dynSeqCost N w.1.length Bo + 5) sIn) ∧
      AnsOK DV N (w.denote N) 1 (GensData.denote N gs) (xy.1.denote N) (xy.2.denote N) ans ∧
      (∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sIn) ∧
      ChildList w.1.length (1 * (N - n)) (StepChild w.1.length (N - n)) ch := by
  have hOa : MeetsContractOn DV alignOps X.O := fun op x h hx => hOc op x (Or.inl h) hx
  have hPa : ∀ op x, alignOps op → GroupPre DV op x → X.Pre op x :=
    fun op x h hx => hPc op x (Or.inl h) hx
  have hO' : MeetsContractOn DV deriveOps X.O := fun op x h hx => hO op x (by
    rcases h with h | h | h | h <;> simp [rdOps, h]) hx
  have hGv : GroupValid DV N gs d := hI.valid.group
  have hprex : GroupPre DV .orbits ((N, fxs, ex), baseWin n N) :=
    ⟨hFxv, baseWin_valid n N, by rw [baseWin_denote]; exact hFxi⟩
  have hosx : IsOrbitPartition (GensData.denote N fxs) (baseWin n N)
      (Giant.baseOrbits X.O n N (N, fxs, ex)) := hOc .orbits _ (Or.inr rfl) hprex
  have hX : Giant.C1Valid (N - n) (Giant.orbitPartModel X.O n N (N, fxs, ex)) :=
    Giant.c1_valid_orbitPartD hFxi hosx
  have hpart := Giant.orbitPartD_spec hFxi hosx
  have hp : IsColPart Finset.univ ((N - n) / 2)
      (decPart (N - n) (Giant.orbitPartModel X.O n N (N, fxs, ex))) := by
    have := orbitPart_valid _ (by simpa using hc2) (by simpa using hc1) hpart
    rwa [Fintype.card_fin] at this
  obtain ⟨-, hKb, hfix⟩ := ar_g1_facts hOa hPa B hGv hGG₀ hG halt (Giant.c1_spec (N - n)) hX hBlA
  exact RunsWithin.m5Case1Prog hOc hPc hO hPre hI hG halt B hGG₀ hs₀ hFG hloc heq hFxv hFyv
    hFx hFy hBox hBoy hBgP hBmem hBkA hBlA hBg1 hsub hB hs hLg (by omega) le_rfl hD
    (Or.inr fun gs' d' O' _ h5 => absurd h5 (rd_free_ne5 hst))
    (Or.inl (rd_ns_part hO' hst hKb hp hfix (by omega) hm))

end Case1Spec

/-! ### Case 2a -/

section Case2aProg

variable {D : Ty} {rec : Ty × Ty} {var : Ty → Type}

/-- The hinted sub-solver on an instance whose positions are all string positions, without a
hint: its string positions are read from its degree. -/
def pbInner (sub : var (hinstTy D) → Prog (groupSig D) rec var (Ty.answer D)) (n₀ : var .nat)
    (J : var (Ty.inst D)) : Prog (groupSig D) rec var (Ty.answer D) :=
  .bind (.op1 .snd J) fun wc => .bind (.op1 .snd wc) fun c => .bind (.op1 .snd c) fun G =>
  .bind (.op1 .fst G) fun nd => plainSub sub n₀ nd J

/-- **The sub-solver of Case 2a's pullback**: milestone 1's restriction of the instance to its
window, then the hinted sub-solver without a hint on the restricted instance (all of whose
positions are string positions and lie in its window). The pullback's sub-solver hypothesis
(`PbSubP`) does not place the window among the string positions; after the restriction every
sub-call is a valid hinted instance. -/
def pbSubR (sub : var (hinstTy D) → Prog (groupSig D) rec var (Ty.answer D)) (n₀ : var .nat)
    (J : var (Ty.inst D)) : Prog (groupSig D) rec var (Ty.answer D) :=
  Programs.restrictProg (fun J' => pbInner sub n₀ J') J

/-- **Case 2a of M5**: stage 14g's `case2aProg` (Align of the large orbit `Φ`, then the pullback)
with `pbSubR` as the pullback's sub-solver. -/
def m5Case2aProg (sub : var (hinstTy D) → Prog (groupSig D) rec var (Ty.answer D))
    (n₀ n : var .nat) (xy : var Ty.strs) (w : var Ty.win) (G : var (Ty.group D))
    (Φx Φy : var (.list .nat)) (Fgs : var Ty.gens) : Prog (groupSig D) rec var (Ty.answer D) :=
  Giant.case2aProg (fun J => pbSubR sub n₀ J) n xy w G Φx Φy Fgs

end Case2aProg

/-- The restriction's cost is affine in the cost of its sub-call. -/
theorem restrictCost_add (n m s A C s' sK Bgm Blift Bker Bgn : ℕ) :
    restrictCost n m s (A + C) s' sK Bgm Blift Bker Bgn =
      restrictCost n m s C s' sK Bgm Blift Bker Bgn + A := by
  simp only [restrictCost]
  ring

theorem restrictCost_mono {n m m' s C C' s' sK Bgm Blift Bker Bgn : ℕ} (hm : m ≤ m')
    (hC : C ≤ C') :
    restrictCost n m s C s' sK Bgm Blift Bker Bgn ≤
      restrictCost n m' s C' s' sK Bgm Blift Bker Bgn := by
  simp only [restrictCost]
  have := Nat.mul_le_mul_left s (Nat.add_le_add_right (Nat.mul_le_mul_left 12 hm) 12)
  omega

/-- The pullback's cost is affine in the cost of one sub-call, with `(h + 1) · wl` sub-calls. -/
theorem pbCost_add (N s A Cb Bstab Borb Bgen p h wl : ℕ) :
    Giant.pbCost N s (A + Cb) Bstab Borb Bgen p h wl =
      Giant.pbCost N s Cb Bstab Borb Bgen p h wl + (h + 1) * wl * A := by
  simp only [Giant.pbCost, Giant.pbBranchCost]
  ring

/-- Case 2a's cost is affine in the cost of the one candidate. -/
theorem c2aCost_add (n N g k Φl BgP Bmem Bk Bl Bg1 Bgen A cP s : ℕ) :
    Giant.c2aCost n N g k Φl BgP Bmem Bk Bl Bg1 Bgen (A + cP) s =
      Giant.c2aCost n N g k Φl BgP Bmem Bk Bl Bg1 Bgen cP s + A := by
  simp only [Giant.c2aCost, alignCost_add]
  ring

section Case2aSpec

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}
  {sub : HInstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)}
  {C : ℕ → Option ℕ → ℕ} {s : ℕ}

theorem RunsWithin.pbInner (n₀ : ℕ) (J : InstData D) {ans : AnswerData D} {k : ℕ}
    (h : RunsWithin X body (sub (J, n₀, J.2.2.2.1, none)) ans k) :
    RunsWithin X body (Main.pbInner sub n₀ J) ans (k + 8) := by
  apply RunsWithin.mono
  case h =>
    unfold Main.pbInner
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.plainSub n₀ _ J h
  case hc =>
    simp only [Prim.cost]
    omega

/-- An instance all of whose positions are string positions, without a hint, is a valid hinted
instance. -/
theorem m5_hinstValid_all {J : InstData D} (hv : J.Valid DV) (n₀ : ℕ) :
    HInstValid DV ((J, n₀, J.degree, none) : HInstData D) := by
  refine sb_hinstValid_plain hv le_rfl ?_ (fun i hi => hv.win.lt i hi) ?_
  · intro g _ u hu
    exact absurd u.2 (by simp only [baseSet, Set.mem_ofPred_eq] at hu; omega)
  · intro g _ hfix
    exact Equiv.ext fun j => hfix j j.2

/-- **From hinted sub-solvers to the pullback's sub-solver.** Every instance of `PbSubP`
(windows of at most `wl / 2` points), restricted to its window, is a valid hinted instance
without a hint whose positions are all string positions, of degree its window size; if those
satisfy `P` and `C · none` is monotone, `pbSubR` solves every `PbSubP` instance within the
restriction's cost with `C (wl / 2) none + 8` for the sub-call. -/
theorem m5_pbSub (hO : MeetsContractOn DV restrictOps X.O)
    (hPre : ∀ op x, restrictOps op → GroupPre DV op x → X.Pre op x)
    {P : HInstData D → Prop} (hsub : HSubSolves X body DV sub P C s)
    (hCmono : ∀ a b, a ≤ b → C a none ≤ C b none) {N : ℕ} {G₀ : Subgroup (Perm (Fin N))}
    {xy : StrData × StrData} {wl sIn n₀ : ℕ}
    {sR : ℕ} (hgR : ∀ M ≤ wl / 2, ∀ hs : GensData, GensData.AllValid M hs → hs.length ≤ sIn →
      (X.O.run GroupOp.generate (M, hs)).2.1.length ≤ sR)
    (hP : ∀ J : HInstData D, J.lab = none → J.n = J.inst.degree → J.inst.degree = J.winSize →
      2 * J.winSize ≤ wl → J.n₀ = n₀ → J.inst.2.2.2.gens.length ≤ sR → P J)
    {sOut sK Bgm Blift Bker Bgn : ℕ}
    (hBgm : ∀ (w' : WinData) (σ' : PermData) (gs' : GensData) (d' : D.denote),
      Giant.PbSubP DV G₀ xy wl sIn (xy, w', σ', N, gs', d') →
      X.B.call GroupOp.generate (w'.1.length, GensData.restrictTo (WinData.pos N w') w'.1 gs')
        (X.O.run GroupOp.generate
          (w'.1.length, GensData.restrictTo (WinData.pos N w') w'.1 gs')) ≤ Bgm)
    (hBlift : ∀ (w' : WinData) (σ' : PermData) (gs' : GensData) (d' : D.denote),
      Giant.PbSubP DV G₀ xy wl sIn (xy, w', σ', N, gs', d') → ∀ π' : PermData,
      X.B.call GroupOp.lift ((N, gs', d'), (w', π'))
        (X.O.run GroupOp.lift ((N, gs', d'), (w', π'))) ≤ Blift)
    (hBker : ∀ (w' : WinData) (σ' : PermData) (gs' : GensData) (d' : D.denote),
      Giant.PbSubP DV G₀ xy wl sIn (xy, w', σ', N, gs', d') →
      X.B.call GroupOp.kernel ((N, gs', d'), w') (X.O.run GroupOp.kernel ((N, gs', d'), w')) ≤
        Bker)
    (hsK : ∀ (w' : WinData) (σ' : PermData) (gs' : GensData) (d' : D.denote),
      Giant.PbSubP DV G₀ xy wl sIn (xy, w', σ', N, gs', d') →
      (X.O.run GroupOp.kernel ((N, gs', d'), w')).2.1.length ≤ sK)
    (hBgn : ∀ hs : GensData, GensData.AllValid N hs → hs.length ≤ sK + s →
      GensData.denote N hs ≤ G₀ →
      X.B.call GroupOp.generate (N, hs) (X.O.run GroupOp.generate (N, hs)) ≤ Bgn)
    (hgo : ∀ hs : GensData, GensData.AllValid N hs → GensData.denote N hs ≤ G₀ →
      (X.O.run GroupOp.generate (N, hs)).2.1.length ≤ sOut) :
    SubSolves X body DV (fun J => Main.pbSubR sub n₀ J) (Giant.PbSubP DV G₀ xy wl sIn)
      (fun _ => restrictCost N (wl / 2) sIn (C (wl / 2) none + 8) s sK Bgm Blift Bker Bgn)
      sOut := by
  rintro ⟨xy', w', σ', N', gs', d'⟩ hI
  obtain ⟨h1, hv, hdeg, h2w, hgl, hle⟩ := hI
  change xy' = xy at h1
  change N' = N at hdeg
  change 2 * w'.1.length ≤ wl at h2w
  change gs'.length ≤ sIn at hgl
  subst h1 hdeg
  have hI' : Giant.PbSubP DV G₀ xy' wl sIn (xy', w', σ', N', gs', d') :=
    ⟨rfl, hv, rfl, h2w, hgl, hle⟩
  have hWG : IsInvariant (GensData.denote N' gs') (w'.denote N') := hv.invariant
  have hgv := GensData.allValid_restrictTo hWG hv.win hv.group.1
  obtain ⟨hdeg', -, -⟩ := hO .generate
    (w'.1.length, GensData.restrictTo (WinData.pos N' w') w'.1 gs') (Or.inl rfl) hgv
  have hlen : w'.1.length ≤ wl / 2 := by omega
  have hws : ∀ k, HInstData.winSize ((restrictInst X.O (xy', w', σ', N', gs', d'), n₀, k, none) :
      HInstData D) = w'.1.length := fun k => by
    simp [HInstData.winSize, HInstData.inst, restrictInst, WinData.ofPoints]
  have hinner : SubSolves X body DV (fun J => Main.pbInner sub n₀ J)
      (fun J => J = restrictInst X.O (xy', w', σ', N', gs', d') ∧ J.Valid DV)
      (fun _ => C (wl / 2) none + 8) s := by
    rintro J ⟨rfl, hJv⟩
    have hJdeg : (restrictInst X.O (xy', w', σ', N', gs', d')).degree = w'.1.length := hdeg'
    obtain ⟨ans, hr, hok, hg⟩ := hsub _ (m5_hinstValid_all hJv n₀)
      (hP _ rfl rfl (by rw [hws]; exact hJdeg) (by rw [hws]; exact h2w) rfl
        (hgR _ hlen _ hgv (by simp only [GensData.restrictTo, List.length_map]; exact hgl)))
    refine ⟨ans, (RunsWithin.pbInner n₀ _ hr).mono ?_, hok, hg⟩
    rw [hws]
    exact Nat.add_le_add_right (hCmono _ _ hlen) 8
  obtain ⟨ans, hrun, hok, hg⟩ := Programs.RunsWithin.restrictProg (body := body) hO hPre hv
    hinner (hBgm w' σ' gs' d' hI') (hBlift w' σ' gs' d' hI')
    (hBker w' σ' gs' d' hI') (hsK w' σ' gs' d' hI')
    (fun hs hv' hl hle' => hBgn hs hv' hl (hle'.trans hle))
  refine ⟨ans, hrun.mono (restrictCost_mono hlen le_rfl |>.trans ?_), hok,
    hg sOut (fun hs hv' hle' => hgo hs hv' (hle'.trans hle))⟩
  simp only [restrictCost]
  have := Nat.mul_le_mul_right (12 * (wl / 2) + 12) hgl
  omega

end Case2aSpec

/-- The work of Case 2a besides its sub-calls: Align, the pullback, and each sub-call's
restriction (`8` for the sub-call itself). -/
def c2aWork (n N g k Φl BgP Bmem Bk Bl Bg1 Bgen s Bstab Borb Bpb wl sH sK Bgm Blift Bker Bgn :
    ℕ) : ℕ :=
  Giant.c2aCost n N g k Φl BgP Bmem Bk Bl Bg1 Bgen
    (4 + Giant.pbCost N s (restrictCost N (wl / 2) s 8 sH sK Bgm Blift Bker Bgn) Bstab Borb Bpb
      Φl s wl) s

/-- **Case 2a by count**: `(s + 1) · wl` sub-calls of cost `A` each, plus `c2aWork`. -/
theorem c2aCost_count (n N g k Φl BgP Bmem Bk Bl Bg1 Bgen s Bstab Borb Bpb wl sH sK Bgm Blift
    Bker Bgn A : ℕ) :
    Giant.c2aCost n N g k Φl BgP Bmem Bk Bl Bg1 Bgen
      (4 + Giant.pbCost N s (restrictCost N (wl / 2) s (A + 8) sH sK Bgm Blift Bker Bgn) Bstab
        Borb Bpb Φl s wl) s =
      (s + 1) * wl * A +
        c2aWork n N g k Φl BgP Bmem Bk Bl Bg1 Bgen s Bstab Borb Bpb wl sH sK Bgm Blift Bker
          Bgn := by
  rw [restrictCost_add, Nat.add_comm (restrictCost _ _ _ _ _ _ _ _ _ _) A, pbCost_add]
  rw [show 4 + (Giant.pbCost N s (restrictCost N (wl / 2) s 8 sH sK Bgm Blift Bker Bgn) Bstab
      Borb Bpb Φl s wl + (s + 1) * wl * A) = (s + 1) * wl * A + (4 + Giant.pbCost N s
      (restrictCost N (wl / 2) s 8 sH sK Bgm Blift Bker Bgn) Bstab Borb Bpb Φl s wl) by ring,
    c2aCost_add, c2aWork]
  ring

section Case2aMain

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}
  {sub : HInstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)}
  {C : ℕ → Option ℕ → ℕ} {xy : StrData × StrData} {w : WinData}
  {N : ℕ} {gs : GensData} {d : D.denote} {n₀ n : ℕ} {L : LabelData}

/-- **Case 2a of M5.** Under `case2aProg_canonical`'s hypotheses, with the hinted sub-solver
for the children of M5 (`SizeChild`, `StepChild`) and `C · none` monotone: the answer is correct
for `G` on `W`, within `(s + 1) · |W|` sub-calls of cost `C (|W| / 2) none` each, plus the work
`c2aWork`. Each sub-call is, after its restriction, an instance without a hint of at most
`|W| / 2` points (`m5_pbSub`). -/
theorem RunsWithin.m5Case2aProg (hO : MeetsContractOn DV Giant.c2aOps X.O)
    (hPre : ∀ op x, Giant.c2aOps op → GroupPre DV op x → X.Pre op x)
    (hOr : MeetsContractOn DV restrictOps X.O)
    (hPr : ∀ op x, restrictOps op → GroupPre DV op x → X.Pre op x)
    (hI : HInstValid DV (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D))
    {s : ℕ} {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N s G₀)
    (hGG₀ : GensData.denote N gs ≤ G₀)
    (hG : IsInvariant (GensData.denote N gs) (baseSet n N))
    (halt : alternatingGroup (Fin (N - n)) ≤ (baseHom _ n hG).range) (h3 : 3 ≤ N - n)
    {lab : Fin N → Finset (Fin (N - n))}
    (he : Recursion.Equivar (baseHom _ n hG) (winFinset N w) lab)
    {t : ℕ} (ht : ∀ u ∈ winFinset N w, (lab u).card = t) (ht1 : 1 ≤ t) (ht2 : 2 * t ≤ N - n)
    {Fmap : (Fin N → ℕ) → Subgroup (Perm (Fin N))} (hFGm : ∀ x, Fmap x ≤ GensData.denote N gs)
    (hloc : ∀ x x', (∀ u ∈ w.denote N, x u = x' u) → Fmap x = Fmap x')
    (heq : ∀ g ∈ GensData.denote N gs, ∀ x,
      Fmap (relabel g x) = (Fmap x).map (MulAut.conj g).toMonoidHom)
    {Fgs : GensData} (hFv : GensData.AllValid N Fgs)
    (hFxe : GensData.denote N Fgs = Fmap (xy.1.denote N))
    (hFaut : ∀ f ∈ GensData.denote N Fgs,
      Matches (w.denote N) f (xy.1.denote N) (xy.1.denote N))
    {Fy : Subgroup (Perm (Fin N))} (hFye : Fy = Fmap (xy.2.denote N))
    (hFxi : IsInvariant (GensData.denote N Fgs) (baseSet n N))
    (hFyi : IsInvariant Fy (baseSet n N))
    {Φx Φy : List ℕ} (hΦxn : Φx.Nodup) (hΦxl : ∀ i ∈ Φx, i < N - n)
    (hΦx2 : N - n < 2 * Φx.length)
    (hΦxo : ∃ γ : Fin (N - n), γ.val ∈ Φx ∧ ∀ δ : Fin (N - n),
      δ.val ∈ Φx ↔ δ ∈ MulAction.orbit (baseHom (GensData.denote N Fgs) n hFxi).range γ)
    (hΦyn : Φy.Nodup) (hΦyl : ∀ i ∈ Φy, i < N - n) (hΦy2 : N - n < 2 * Φy.length)
    (hΦyo : ∃ γ : Fin (N - n), γ.val ∈ Φy ∧ ∀ δ : Fin (N - n),
      δ.val ∈ Φy ↔ δ ∈ MulAction.orbit (baseHom Fy n hFyi).range γ)
    (hFalt : ∀ π : Perm (Giant.phiSet N (Φx.map (n + ·))), Perm.sign π = 1 →
      ∃ f ∈ GensData.denote N Fgs, ∀ v : Giant.phiSet N (Φx.map (n + ·)), f v = π v)
    {BgP Bmem Bk Bl Bg1 Bgen Bpb : ℕ}
    (hBgP : X.B.call GroupOp.generate (N - n, gs.map (baseD n N))
      (X.O.run GroupOp.generate (N - n, gs.map (baseD n N))) ≤ BgP)
    (hBmem : ∀ g : PermData, g.Valid (N - n) → X.B.call GroupOp.mem (pModel X.O n (N, gs, d), g)
      (X.O.run GroupOp.mem (pModel X.O n (N, gs, d), g)) ≤ Bmem)
    (hBk : X.B.call GroupOp.kernel ((N, gs, d), baseWin n N) (kerModel X.O n (N, gs, d)) ≤ Bk)
    (hBl : ∀ π : PermData, X.B.call GroupOp.lift ((N, gs, d), (baseWin n N, π))
      (liftModel X.O n (N, gs, d) π) ≤ Bl)
    (hBg1 : X.B.call GroupOp.generate
      (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d)) ((setOps (N - n)).gens Φx))).map
        (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
      (Giant.g1Model X.O n (N, gs, d) (setOps (N - n)) Φx) ≤ Bg1)
    (hBgen : ∀ gs' : GensData, GensData.AllValid N gs' → gs'.length ≤ s + 1 →
      GensData.denote N gs' ≤ GensData.denote N gs →
      X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ Bgen)
    (hBpb : ∀ gs', GensData.AllValid N gs' →
      gs'.length ≤ (s + 1) * (s + 1) + s + Fgs.length → GensData.denote N gs' ≤ G₀ →
      X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ Bpb)
    {sR : ℕ} (hgR : ∀ M ≤ w.1.length / 2, ∀ hs : GensData, GensData.AllValid M hs →
      hs.length ≤ s → (X.O.run GroupOp.generate (M, hs)).2.1.length ≤ sR)
    {sH : ℕ} (hsub : HSubSolves X body DV sub
      (fun J => SizeChild sR (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D)
        J ∧ StepChild w.1.length (N - n) (J.winSize, J.baseOpt)) C sH)
    (hCmono : ∀ a b, a ≤ b → C a none ≤ C b none)
    {sK Bgm Blift Bker Bgn : ℕ}
    (hBgm : ∀ (w' : WinData) (σ' : PermData) (gs' : GensData) (d' : D.denote),
      Giant.PbSubP DV G₀ xy w.1.length s (xy, w', σ', N, gs', d') →
      X.B.call GroupOp.generate (w'.1.length, GensData.restrictTo (WinData.pos N w') w'.1 gs')
        (X.O.run GroupOp.generate
          (w'.1.length, GensData.restrictTo (WinData.pos N w') w'.1 gs')) ≤ Bgm)
    (hBlift : ∀ (w' : WinData) (σ' : PermData) (gs' : GensData) (d' : D.denote),
      Giant.PbSubP DV G₀ xy w.1.length s (xy, w', σ', N, gs', d') → ∀ π' : PermData,
      X.B.call GroupOp.lift ((N, gs', d'), (w', π'))
        (X.O.run GroupOp.lift ((N, gs', d'), (w', π'))) ≤ Blift)
    (hBker : ∀ (w' : WinData) (σ' : PermData) (gs' : GensData) (d' : D.denote),
      Giant.PbSubP DV G₀ xy w.1.length s (xy, w', σ', N, gs', d') →
      X.B.call GroupOp.kernel ((N, gs', d'), w') (X.O.run GroupOp.kernel ((N, gs', d'), w')) ≤
        Bker)
    (hsK : ∀ (w' : WinData) (σ' : PermData) (gs' : GensData) (d' : D.denote),
      Giant.PbSubP DV G₀ xy w.1.length s (xy, w', σ', N, gs', d') →
      (X.O.run GroupOp.kernel ((N, gs', d'), w')).2.1.length ≤ sK)
    (hBgn : ∀ hs : GensData, GensData.AllValid N hs → hs.length ≤ sK + sH →
      GensData.denote N hs ≤ G₀ →
      X.B.call GroupOp.generate (N, hs) (X.O.run GroupOp.generate (N, hs)) ≤ Bgn) :
    ∃ ans : AnswerData D,
      RunsWithin X body (Main.m5Case2aProg sub n₀ n xy w (N, gs, d) Φx Φy Fgs) ans
        ((s + 1) * w.1.length * C (w.1.length / 2) none +
          c2aWork n N gs.length ((setOps (N - n)).gens Φx).length Φx.length BgP Bmem Bk Bl Bg1
            Bgen s B.Bstab B.Borb Bpb w.1.length sH sK Bgm Blift Bker Bgn) ∧
      AnsOK DV N (w.denote N) 1 (GensData.denote N gs) (xy.1.denote N) (xy.2.denote N) ans ∧
      ∀ sGen, (∀ gs', GensData.AllValid N gs' → GensData.denote N gs' ≤ GensData.denote N gs →
          (X.O.run GroupOp.generate (N, gs')).2.1.length ≤ sGen) →
        ∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sGen := by
  have hwn : w.1.length ≤ n := Giant.c2_len_le ⟨hI.valid.win.nodup, hI.win_lt⟩
  have hP : ∀ J : HInstData D, J.lab = none → J.n = J.inst.degree →
      J.inst.degree = J.winSize → 2 * J.winSize ≤ w.1.length → J.n₀ = n₀ →
      J.inst.2.2.2.gens.length ≤ sR →
      (SizeChild sR (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D) J ∧
        StepChild w.1.length (N - n) (J.winSize, J.baseOpt)) := by
    intro J hl hn hdg h2 hn₀ hgl
    have hb : J.baseOpt = none := by simp [HInstData.baseOpt, hl]
    have hJn : J.n ≤ n := by omega
    refine ⟨⟨hn₀, hJn, ?_, hgl, SizeChild.lab_none hn₀ hJn hl⟩, ?_, Or.inr ⟨hb, h2⟩⟩
    · change J.inst.degree ≤ max N (2 * n)
      omega
    · change J.winSize ≤ w.1.length
      omega
  have hpb := m5_pbSub (body := body) (sOut := s) hOr hPr hsub hCmono (G₀ := G₀) (xy := xy)
    (wl := w.1.length) (sIn := s) hgR hP hBgm hBlift hBker hsK hBgn
    (fun hs hv hle => B.genOut hs hv hle)
  obtain ⟨ans, hrun, hok, hg⟩ := Giant.RunsWithin.case2aProg_canonical (body := body) hO hPre B
    hI.valid.group hGG₀ hG halt h3 hI.valid.win hI.valid.invariant he ht ht1 ht2 hFGm hloc heq
    hFv hFxe hFaut hFye hFxi hFyi hΦxn hΦxl hΦx2 hΦxo hΦyn hΦyl hΦy2 hΦyo hFalt hBgP hBmem hBk
    hBl hBg1 hBgen hBpb hpb
  refine ⟨ans, hrun.mono (le_of_eq ?_), hok, hg⟩
  exact c2aCost_count n N gs.length _ _ BgP Bmem Bk Bl Bg1 Bgen s B.Bstab B.Borb Bpb w.1.length
    sH sK Bgm Blift Bker Bgn _

/-- The lists of length `k` over `l`. -/
def m5ListsOver {α : Type} (l : List α) : ℕ → List (List α)
  | 0 => [[]]
  | k + 1 => l.flatMap fun x => (m5ListsOver l k).map (x :: ·)

theorem m5_mem_listsOver {α : Type} {l : List α} :
    ∀ {hs : List α}, (∀ g ∈ hs, g ∈ l) → hs ∈ m5ListsOver l hs.length
  | [], _ => List.mem_singleton_self _
  | g :: hs, h => List.mem_flatMap.2 ⟨g, h g List.mem_cons_self,
      List.mem_map.2 ⟨hs, m5_mem_listsOver fun g' hg' => h g' (List.mem_cons_of_mem _ hg'), rfl⟩⟩

/-- **Case 2a's generator hypothesis is satisfiable** for every backend (`hgR` of
`RunsWithin.m5Case2aProg`): at each degree there are finitely many valid generator lists of
bounded length, so some `sR` bounds `generate`'s output on all of them. -/
theorem m5_exists_genOut_le (O : Oracle (groupSig D)) (K s : ℕ) :
    ∃ sR, ∀ M ≤ K, ∀ hs : GensData, GensData.AllValid M hs → hs.length ≤ s →
      (O.run GroupOp.generate (M, hs)).2.1.length ≤ sR := by
  have one : ∀ M, ∃ b, ∀ hs : GensData, GensData.AllValid M hs → hs.length ≤ s →
      (O.run GroupOp.generate (M, hs)).2.1.length ≤ b := by
    intro M
    obtain ⟨l, -, hlm⟩ := exists_allPermsD M
    refine ⟨(((List.range (s + 1)).flatMap fun k => m5ListsOver l k).map
      fun hs => (O.run GroupOp.generate (M, hs)).2.1.length).foldr max 0, fun hs hv hl => ?_⟩
    refine le_foldr_max (List.mem_map.2 ⟨hs, List.mem_flatMap.2 ⟨hs.length,
      List.mem_range.2 (by omega), m5_mem_listsOver fun g hg => hlm g (hv g hg)⟩, rfl⟩)
  induction K with
  | zero =>
    obtain ⟨b, hb⟩ := one 0
    exact ⟨b, fun M hM => by obtain rfl : M = 0 := by omega
                             exact hb⟩
  | succ K ih =>
    obtain ⟨b, hb⟩ := ih
    obtain ⟨b', hb'⟩ := one (K + 1)
    refine ⟨max b b', fun M hM hs hv hl => ?_⟩
    rcases Nat.lt_or_ge M (K + 1) with h | h
    · exact (hb M (by omega) hs hv hl).trans (le_max_left _ _)
    · obtain rfl : M = K + 1 := by omega
      exact (hb' hs hv hl).trans (le_max_right _ _)

end Case2aMain

/-! ### Case 2b -/

section Case2bProg

variable {D : Ty} {rec : Ty × Ty} {var : Ty → Type}

/-- **Case 2b of M5**: stage 14h's `case2bProg` (the canonical choice tree of `ψ(F)` on the
large orbit, `x`'s first leaf aligned against all of `y`'s) with reduce-and-derive's per-coset
program as Align's sub-solver. The aligned leaf (a colored partition or a trimmed Johnson
structure) is not handed to `rdProg` as a coloured Johnson structure in this stage (14j-4b). -/
def m5Case2bProg (sub : var (hinstTy D) → Prog (groupSig D) rec var (Ty.answer D))
    (n₀ n : var .nat) (L : var (.array (.list .nat))) (st : var stTy) (xy : var Ty.strs)
    (w : var Ty.win) (G Fx Fy : var (Ty.group D)) (Φx Φy : var (.list .nat)) :
    Prog (groupSig D) rec var (Ty.answer D) :=
  Case2b.case2bProg (fun J => Main.rdBranch sub n₀ n L st J) n xy w G Fx Fy Φx Φy

end Case2bProg

/-- The first leaf of `x` in Case 2b. -/
abbrev m5Leaf2b {D : Ty} (O : Oracle (groupSig D)) (N n : ℕ) (F : GroupData D.denote)
    (Φ : List ℕ) : Option SoJTree.OutD :=
  Case2b.firstLeafD O N n F Φ (Case2b.degD O N n F Φ - 1)

/-- Case 2b's cost is affine in the cost of one candidate, with `c2bR` candidates. -/
theorem c2bCost_add (n N s g nx ny j k Bstab Bg Z BgP Bmem Bk Bl Bg1 Bgen A Cb : ℕ)
    (Bo Bs Bt : ℕ → ℕ) :
    Case2b.c2bCost n N s g nx ny j k Bstab Bg Z BgP Bmem Bk Bl Bg1 Bgen (A + Cb) Bo Bs Bt =
      Case2b.c2bCost n N s g nx ny j k Bstab Bg Z BgP Bmem Bk Bl Bg1 Bgen Cb Bo Bs Bt +
        Case2b.c2bR N n ny j Z * A := by
  simp only [Case2b.c2bCost, alignCost_add]
  ring

section Case2bSpec

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}
  {sub : HInstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)}
  {C : ℕ → Option ℕ → ℕ} {s : ℕ} {xy : StrData × StrData} {w : WinData}
  {N : ℕ} {gs : GensData} {d : D.denote} {n₀ n : ℕ} {L : LabelData} {st : ℕ × CJData}
  {sIn Lg F Blift Bgen Bo Bk Bcr Bd W6 : ℕ}

/-- **Case 2b of M5.** Under `case2bProg_canonical'`'s hypotheses (with the backend bounds at
the sub-solver's generator bound `sIn`) and reduce-and-derive's for the aligned group of
`x`'s first leaf `X₀`: the answer is correct for `G` on `W`, and the children are
`StepChild |W| m`, `c2bR` copies (the number of candidates) of one list with windows summing to
at most `F · |W|`. -/
theorem RunsWithin.m5Case2bProg (hOc : MeetsContractOn DV Case2b.c2bOps X.O)
    (hPc : ∀ op x, Case2b.c2bOps op → GroupPre DV op x → X.Pre op x)
    (hO : MeetsContractOn DV rdOps X.O)
    (hPre : ∀ op x, rdOps op → GroupPre DV op x → X.Pre op x)
    (hI : HInstValid DV (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D))
    {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N sIn G₀)
    (hGG₀ : GensData.denote N gs ≤ G₀)
    {sm : ℕ → ℕ} (Bm : ∀ M, BackendBounds X DV M (sm M) ⊤)
    (hG : IsInvariant (GensData.denote N gs) (baseSet n N))
    (halt : alternatingGroup (Fin (N - n)) ≤ (baseHom _ n hG).range)
    {Fmap : (Fin N → ℕ) → Subgroup (Perm (Fin N))}
    (hloc : ∀ x x', (∀ u ∈ w.denote N, x u = x' u) → Fmap x = Fmap x')
    (heq : ∀ g ∈ GensData.denote N gs, ∀ x,
      Fmap (relabel g x) = (Fmap x).map (MulAut.conj g).toMonoidHom)
    {fxs fys : GensData} {ex ey : D.denote} (hFxv : GroupValid DV N fxs ex)
    (hFyv : GroupValid DV N fys ey) (hFxs : fxs.length ≤ sIn) (hFys : fys.length ≤ sIn)
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
    (hngx : ¬ Case2b.TupTrans (baseHom _ n hFxi).range (SoJProg.setOf (N - n) Φx) (Φx.length - 2))
    (hngy : ¬ Case2b.TupTrans (baseHom _ n hFyi).range (SoJProg.setOf (N - n) Φy) (Φy.length - 2))
    {Bg BgP Bmem BkA BlA Bg1 Bgen' : ℕ}
    (hBg : ∀ M ≤ N - n, ∀ gs' : GensData, GensData.AllValid M gs' → gs'.length ≤ sIn →
      X.B.call GroupOp.generate (M, gs') (X.O.run GroupOp.generate (M, gs')) ≤ Bg)
    (hBgP : X.B.call GroupOp.generate (N - n, gs.map (baseD n N))
      (X.O.run GroupOp.generate (N - n, gs.map (baseD n N))) ≤ BgP)
    (hBmem : ∀ g : PermData, g.Valid (N - n) → X.B.call GroupOp.mem (pModel X.O n (N, gs, d), g)
      (X.O.run GroupOp.mem (pModel X.O n (N, gs, d), g)) ≤ Bmem)
    (hBkA : X.B.call GroupOp.kernel ((N, gs, d), baseWin n N) (kerModel X.O n (N, gs, d)) ≤ BkA)
    (hBlA : ∀ π : PermData, X.B.call GroupOp.lift ((N, gs, d), (baseWin n N, π))
      (liftModel X.O n (N, gs, d) π) ≤ BlA)
    (hBg1 : ∀ X₀ : SoJTree.OutD, m5Leaf2b X.O N n (N, fxs, ex) Φx = some X₀ →
      X.B.call GroupOp.generate
        (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (Case2b.outGensD (N - n) X₀))).map
          (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
        (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (Case2b.outGensD (N - n) X₀)))) ≤ Bg1)
    (hBgen : ∀ gs' : GensData, GensData.AllValid N gs' →
      gs'.length ≤ Case2b.c2bR N n Φy.length (Case2b.degD X.O N n (N, fys, ey) Φy - 1)
        (Case2b.sojZ (N - n)) * (sIn + 1) →
      GensData.denote N gs' ≤ GensData.denote N gs →
      X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ Bgen')
    (hsub : HSubSolves X body DV sub
      (fun J => SizeChild sIn (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D)
        J ∧ StepChild w.1.length (N - n) (J.winSize, J.baseOpt)) C s)
    (hB : RDBounds X DV n N sIn Lg Blift Bgen Bo Bk Bcr) (hs : s ≤ sIn)
    (hLg : F * (sIn + 1) ≤ Lg) (hF1 : 1 ≤ F) (hFm : N - n ≤ F)
    (hD : ∀ X₀, m5Leaf2b X.O N n (N, fxs, ex) Φx = some X₀ → ∀ gs' d' O', RDSet DV n N gs w L
      (Giant.g1Model X.O n (N, gs, d) (Case2b.outOps (N - n)) X₀).2.1 sIn gs' d' O' →
      RDOrbit X body DV n N w L st sIn Bd gs' d' O')
    (h5 : ∀ X₀, m5Leaf2b X.O N n (N, fxs, ex) Φx = some X₀ → (N - n).factorial ≤ F ∨
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (Case2b.outOps (N - n)) X₀).2.1 sIn gs' d' O' →
      (deriveModel X.O n N (N, gs', d') O' L st).1 = 5 →
        (deriveModel X.O n N (N, gs', d') O' L st).2.1.2.2.length ≤ F)
    (h6 : ∀ X₀, m5Leaf2b X.O N n (N, fxs, ex) Φx = some X₀ → (∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (Case2b.outOps (N - n)) X₀).2.1 sIn gs' d' O' →
        (deriveModel X.O n N (N, gs', d') O' L st).1 ≠ 6) ∨
      ((N - n).factorial ≤ F ∧ rd6Cost N n w.1.length s sIn Bk Bo Bcr Bgen ≤ W6)) :
    ∃ X₀ : SoJTree.OutD, m5Leaf2b X.O N n (N, fxs, ex) Φx = some X₀ ∧
      ∃ (ans : AnswerData D) (ch : List (ℕ × Option ℕ)),
        RunsWithin X body
          (Main.m5Case2bProg sub n₀ n L st xy w (N, gs, d) (N, fxs, ex) (N, fys, ey) Φx Φy) ans
          ((ch.map fun x => C x.1 x.2).sum +
            Case2b.c2bCost n N sIn gs.length Φx.length Φy.length
              (Case2b.degD X.O N n (N, fxs, ex) Φx - 1) (Case2b.outGensD (N - n) X₀).length
              B.Bstab Bg (Case2b.sojZ (N - n)) BgP Bmem BkA BlA Bg1 Bgen'
              (w.1.length * rdOrbitWork N n w.1.length s sIn F Bd Blift Bgen Bo W6 +
                dynSeqCost N w.1.length Bo + 5)
              (fun M => (Bm M).Borb) (fun M => (Bm M).Bstab) (fun M => (Bm M).Btr)) ∧
        AnsOK DV N (w.denote N) 1 (GensData.denote N gs) (xy.1.denote N) (xy.2.denote N) ans ∧
        (∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sIn) ∧
        ChildList w.1.length
          (Case2b.c2bR N n Φy.length (Case2b.degD X.O N n (N, fxs, ex) Φx - 1)
            (Case2b.sojZ (N - n)) * F) (StepChild w.1.length (N - n)) ch := by
  classical
  have hOa : MeetsContractOn DV alignOps X.O := fun op x h hx => hOc op x (Or.inr h) hx
  have hPa : ∀ op x, alignOps op → GroupPre DV op x → X.Pre op x :=
    fun op x h hx => hPc op x (Or.inr h) hx
  have hOd : MeetsContractOn DV Case2b.degOps X.O := fun op x h hp => hOc op x (Or.inl h) hp
  have hPd : ∀ op x, Case2b.degOps op → GroupPre DV op x → X.Pre op x := fun op x h hp =>
    hPc op x (Or.inl h) hp
  have hOch := Case2b.cp2_choiceOps_of_deg hOd
  have ⟨γx, _, hγx⟩ := hΦxo
  have hΦx := Case2b.cp2_inv_of_orbit hFxi hΦxl ⟨γx, hγx⟩
  obtain ⟨h1x, Hx⟩ := Case2b.case2bHyp_degD hOd hPd B hFxv hFxs hFx₀ hFxi hΦxn hΦxl hΦx (Bm _)
    ⟨γx, hγx⟩ hngx
  have Hx' : Case2b.Case2bHyp (baseHom _ n hFxi).range (SoJProg.setOf (N - n) Φx)
      (Case2b.degD X.O N n (N, fxs, ex) Φx - 1 + 1) := by
    rw [Nat.sub_add_cancel h1x]
    exact Hx
  -- the uniform branch cost, from the first leaf
  have hpack : ∃ Cb : ℕ, ∃ ch₀ : List (ℕ × Option ℕ),
      ((ch₀.map Prod.fst).sum ≤ F * w.1.length ∧ (∀ x ∈ ch₀, StepChild w.1.length (N - n) x) ∧
        ∀ x ∈ ch₀, 1 ≤ x.1) ∧
      Cb = (ch₀.map fun x => C x.1 x.2).sum +
        (w.1.length * rdOrbitWork N n w.1.length s sIn F Bd Blift Bgen Bo W6 +
          dynSeqCost N w.1.length Bo + 5) ∧
      ∀ X₀ : SoJTree.OutD, m5Leaf2b X.O N n (N, fxs, ex) Φx = some X₀ →
        SubSolves X body DV
          (Main.rdBranch (var := Ty.denote) (rec := (a, b)) (D := D) sub n₀ n L st)
          (fun I => I.1 = xy ∧ I.2.1 = w ∧
            I.2.2.2 = preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O
              (pModel X.O n (N, gs, d)) (Case2b.outGensD (N - n) X₀))) ∧ I.Valid DV)
          (fun _ => Cb) sIn := by
    rcases hfl : m5Leaf2b X.O N n (N, fxs, ex) Φx with _ | X₀₀
    · exact ⟨_, [], ⟨by simp, by simp, by simp⟩, rfl, fun X₀ h => absurd h (by simp)⟩
    · have hX₀₀ : Case2b.OutValid (N - n) X₀₀ :=
        Case2b.firstLeafD_valid (F := (N, fxs, ex)) (j := Case2b.degD X.O N n (N, fxs, ex) Φx - 1)
          hOch rfl hFxv hFxi hΦxn hΦxl Hx' hfl
      obtain ⟨ch₀, hgood, hsubA⟩ := m5_alignSub (C := C) (W6 := W6) hOa hPa hO hPre hI hG halt B
        hGG₀ le_rfl (Case2b.outOps_spec (N - n)) hX₀₀ hBlA hsub hB hs hLg hF1 hFm
        (hD X₀₀ hfl) (h5 X₀₀ hfl) (h6 X₀₀ hfl)
      refine ⟨_, ch₀, hgood, rfl, fun X₀ h => ?_⟩
      cases (Option.some.inj h).symm
      exact hsubA
  obtain ⟨Cb, ch₀, hgood, hCb, hsubA⟩ := hpack
  have hGv : GroupValid DV N gs d := hI.valid.group
  obtain ⟨X₀, hX₀, ans, hrun, hok, hg⟩ := Case2b.RunsWithin.case2bProg_canonical' (body := body)
    hOc hPc B Bm hGv hG halt hI.valid.win hI.valid.invariant hloc heq hFxv hFyv hFxs
    hFys hFx₀ hFy₀ hFxe hFye hFxi hFyi hΦxn hΦxl hΦx2 hΦxo hΦyn hΦyl hΦy2 hΦyo hngx hngy hBg
    hBgP hBmem hBkA hBlA hBg1
    hBgen hsubA
  refine ⟨X₀, hX₀, ans, (List.replicate (Case2b.c2bR N n Φy.length
    (Case2b.degD X.O N n (N, fxs, ex) Φx - 1) (Case2b.sojZ (N - n))) ch₀).flatten, ?_, hok,
    hg sIn (fun hs' hv _ => hB.genOut N le_rfl hs' hv), m5_replicate_childList hgood⟩
  refine hrun.mono (le_of_eq ?_)
  rw [hCb, m5_replicate_cost, c2bCost_add]
  ring

/-- **The first leaf of Case 2b is valid**: under Case 2b's hypotheses on `F(x)` and its large
orbit, the choice tree's hypothesis holds at the computed degree (`case2bHyp_degD`), so the
first leaf is a valid colored partition or trimmed Johnson structure (`firstLeafD_valid`). -/
theorem m5_leaf2b_valid (hOc : MeetsContractOn DV Case2b.c2bOps X.O)
    (hPc : ∀ op x, Case2b.c2bOps op → GroupPre DV op x → X.Pre op x)
    {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N sIn G₀)
    {sm : ℕ → ℕ} (Bm : ∀ M, BackendBounds X DV M (sm M) ⊤)
    {fxs : GensData} {ex : D.denote} (hFxv : GroupValid DV N fxs ex) (hFxs : fxs.length ≤ sIn)
    (hFx₀ : GensData.denote N fxs ≤ G₀)
    (hFxi : IsInvariant (GensData.denote N fxs) (baseSet n N))
    {Φx : List ℕ} (hΦxn : Φx.Nodup) (hΦxl : ∀ i ∈ Φx, i < N - n)
    (hΦxo : ∃ γ : Fin (N - n), γ.val ∈ Φx ∧ ∀ δ : Fin (N - n),
      δ.val ∈ Φx ↔ δ ∈ MulAction.orbit (baseHom _ n hFxi).range γ)
    (hngx : ¬ Case2b.TupTrans (baseHom _ n hFxi).range (SoJProg.setOf (N - n) Φx)
      (Φx.length - 2))
    {X₀ : SoJTree.OutD} (hX₀ : m5Leaf2b X.O N n (N, fxs, ex) Φx = some X₀) :
    Case2b.OutValid (N - n) X₀ := by
  classical
  have hOd : MeetsContractOn DV Case2b.degOps X.O := fun op x h hp => hOc op x (Or.inl h) hp
  have hPd : ∀ op x, Case2b.degOps op → GroupPre DV op x → X.Pre op x := fun op x h hp =>
    hPc op x (Or.inl h) hp
  have ⟨γx, _, hγx⟩ := hΦxo
  have hΦx := Case2b.cp2_inv_of_orbit hFxi hΦxl ⟨γx, hγx⟩
  obtain ⟨h1x, Hx⟩ := Case2b.case2bHyp_degD hOd hPd B hFxv hFxs hFx₀ hFxi hΦxn hΦxl hΦx (Bm _)
    ⟨γx, hγx⟩ hngx
  have Hx' : Case2b.Case2bHyp (baseHom _ n hFxi).range (SoJProg.setOf (N - n) Φx)
      (Case2b.degD X.O N n (N, fxs, ex) Φx - 1 + 1) := by
    rw [Nat.sub_add_cancel h1x]
    exact Hx
  exact Case2b.firstLeafD_valid (F := (N, fxs, ex)) (j := Case2b.degD X.O N n (N, fxs, ex) Φx - 1)
    (Case2b.cp2_choiceOps_of_deg hOd) rfl hFxv hFxi hΦxn hΦxl Hx' hX₀

/-- **Case 2b of M5 with a partition leaf and no stuck orbit.** If `st` is not a coloured
Johnson structure and `x`'s first leaf is a colored `t`-partition with `4t ≤ 3m`, the aligned
group preserves it, so no orbit is stuck (`rd_ns_part`) and the factor is `m`. -/
theorem RunsWithin.m5Case2bProg_part (hOc : MeetsContractOn DV Case2b.c2bOps X.O)
    (hPc : ∀ op x, Case2b.c2bOps op → GroupPre DV op x → X.Pre op x)
    (hO : MeetsContractOn DV rdOps X.O)
    (hPre : ∀ op x, rdOps op → GroupPre DV op x → X.Pre op x)
    (hI : HInstValid DV (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D))
    {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N sIn G₀)
    (hGG₀ : GensData.denote N gs ≤ G₀)
    {sm : ℕ → ℕ} (Bm : ∀ M, BackendBounds X DV M (sm M) ⊤)
    (hG : IsInvariant (GensData.denote N gs) (baseSet n N))
    (halt : alternatingGroup (Fin (N - n)) ≤ (baseHom _ n hG).range)
    {Fmap : (Fin N → ℕ) → Subgroup (Perm (Fin N))}
    (hloc : ∀ x x', (∀ u ∈ w.denote N, x u = x' u) → Fmap x = Fmap x')
    (heq : ∀ g ∈ GensData.denote N gs, ∀ x,
      Fmap (relabel g x) = (Fmap x).map (MulAut.conj g).toMonoidHom)
    {fxs fys : GensData} {ex ey : D.denote} (hFxv : GroupValid DV N fxs ex)
    (hFyv : GroupValid DV N fys ey) (hFxs : fxs.length ≤ sIn) (hFys : fys.length ≤ sIn)
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
    (hngx : ¬ Case2b.TupTrans (baseHom _ n hFxi).range (SoJProg.setOf (N - n) Φx)
      (Φx.length - 2))
    (hngy : ¬ Case2b.TupTrans (baseHom _ n hFyi).range (SoJProg.setOf (N - n) Φy)
      (Φy.length - 2))
    {Bg BgP Bmem BkA BlA Bg1 Bgen' : ℕ}
    (hBg : ∀ M ≤ N - n, ∀ gs' : GensData, GensData.AllValid M gs' → gs'.length ≤ sIn →
      X.B.call GroupOp.generate (M, gs') (X.O.run GroupOp.generate (M, gs')) ≤ Bg)
    (hBgP : X.B.call GroupOp.generate (N - n, gs.map (baseD n N))
      (X.O.run GroupOp.generate (N - n, gs.map (baseD n N))) ≤ BgP)
    (hBmem : ∀ g : PermData, g.Valid (N - n) → X.B.call GroupOp.mem (pModel X.O n (N, gs, d), g)
      (X.O.run GroupOp.mem (pModel X.O n (N, gs, d), g)) ≤ Bmem)
    (hBkA : X.B.call GroupOp.kernel ((N, gs, d), baseWin n N) (kerModel X.O n (N, gs, d)) ≤ BkA)
    (hBlA : ∀ π : PermData, X.B.call GroupOp.lift ((N, gs, d), (baseWin n N, π))
      (liftModel X.O n (N, gs, d) π) ≤ BlA)
    (hBg1 : ∀ X₀ : SoJTree.OutD, m5Leaf2b X.O N n (N, fxs, ex) Φx = some X₀ →
      X.B.call GroupOp.generate
        (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (Case2b.outGensD (N - n) X₀))).map
          (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
        (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (Case2b.outGensD (N - n) X₀)))) ≤ Bg1)
    (hBgen : ∀ gs' : GensData, GensData.AllValid N gs' →
      gs'.length ≤ Case2b.c2bR N n Φy.length (Case2b.degD X.O N n (N, fys, ey) Φy - 1)
        (Case2b.sojZ (N - n)) * (sIn + 1) →
      GensData.denote N gs' ≤ GensData.denote N gs →
      X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ Bgen')
    (hsub : HSubSolves X body DV sub
      (fun J => SizeChild sIn (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D)
        J ∧ StepChild w.1.length (N - n) (J.winSize, J.baseOpt)) C s)
    (hB : RDBounds X DV n N sIn Lg Blift Bgen Bo Bk Bcr) (hs : s ≤ sIn)
    (hLg : (N - n) * (sIn + 1) ≤ Lg) (hm : 2 ≤ N - n) (hst : st.1 ≠ 2)
    (hD : ∀ X₀, m5Leaf2b X.O N n (N, fxs, ex) Φx = some X₀ → ∀ gs' d' O', RDSet DV n N gs w L
      (Giant.g1Model X.O n (N, gs, d) (Case2b.outOps (N - n)) X₀).2.1 sIn gs' d' O' →
      RDOrbit X body DV n N w L st sIn Bd gs' d' O')
    (hpart : ∀ X₀, m5Leaf2b X.O N n (N, fxs, ex) Φx = some X₀ →
      ∃ (p : CPart (Fin (N - n))) (t : ℕ), (Case2b.outOps (N - n)).dec X₀ = some (Sum.inl p) ∧
        IsColPart Finset.univ t p ∧ 4 * t ≤ 3 * (N - n)) :
    ∃ X₀ : SoJTree.OutD, m5Leaf2b X.O N n (N, fxs, ex) Φx = some X₀ ∧
      ∃ (ans : AnswerData D) (ch : List (ℕ × Option ℕ)),
        RunsWithin X body
          (Main.m5Case2bProg sub n₀ n L st xy w (N, gs, d) (N, fxs, ex) (N, fys, ey) Φx Φy) ans
          ((ch.map fun x => C x.1 x.2).sum +
            Case2b.c2bCost n N sIn gs.length Φx.length Φy.length
              (Case2b.degD X.O N n (N, fxs, ex) Φx - 1) (Case2b.outGensD (N - n) X₀).length
              B.Bstab Bg (Case2b.sojZ (N - n)) BgP Bmem BkA BlA Bg1 Bgen'
              (w.1.length * rdOrbitWork N n w.1.length s sIn (N - n) Bd Blift Bgen Bo 0 +
                dynSeqCost N w.1.length Bo + 5)
              (fun M => (Bm M).Borb) (fun M => (Bm M).Bstab) (fun M => (Bm M).Btr)) ∧
        AnsOK DV N (w.denote N) 1 (GensData.denote N gs) (xy.1.denote N) (xy.2.denote N) ans ∧
        (∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sIn) ∧
        ChildList w.1.length
          (Case2b.c2bR N n Φy.length (Case2b.degD X.O N n (N, fxs, ex) Φx - 1)
            (Case2b.sojZ (N - n)) * (N - n)) (StepChild w.1.length (N - n)) ch := by
  have hOa : MeetsContractOn DV alignOps X.O := fun op x h hx => hOc op x (Or.inr h) hx
  have hPa : ∀ op x, alignOps op → GroupPre DV op x → X.Pre op x :=
    fun op x h hx => hPc op x (Or.inr h) hx
  have hO' : MeetsContractOn DV deriveOps X.O := fun op x h hx => hO op x (by
    rcases h with h | h | h | h <;> simp [rdOps, h]) hx
  refine RunsWithin.m5Case2bProg hOc hPc hO hPre hI B hGG₀ Bm hG halt hloc heq hFxv hFyv hFxs
    hFys hFx₀ hFy₀ hFxe hFye hFxi hFyi hΦxn hΦxl hΦx2 hΦxo hΦyn hΦyl hΦy2 hΦyo hngx hngy hBg
    hBgP hBmem hBkA hBlA hBg1 hBgen hsub hB hs hLg (by omega) le_rfl hD
    (fun _ _ => Or.inr fun gs' d' O' _ h5 => absurd h5 (rd_free_ne5 hst)) (fun X₀ hX₀ => ?_)
  have hXv := m5_leaf2b_valid hOc hPc B Bm hFxv hFxs hFx₀ hFxi hΦxn hΦxl hΦxo hngx hX₀
  obtain ⟨p, t, hdec, hp, ht⟩ := hpart X₀ hX₀
  obtain ⟨-, hKb, hfix⟩ := ar_g1_facts hOa hPa B hI.valid.group hGG₀ hG halt
    (Case2b.outOps_spec (N - n)) hXv hBlA
  refine Or.inl (rd_ns_part hO' hst hKb hp (fun g => ?_) ht hm)
  have h := hfix g
  rw [hdec, Option.smul_some, Sum.smul_inl] at h
  exact Sum.inl_injective (Option.some_injective _ h)

end Case2bSpec

/-! ### Case 3: the pieces -/

section Case3Data

/-- **`x`'s colouring depends only on the comparisons of repetition-free tuples.** -/
theorem m5_colXD_congr {c c' : List ℕ → List ℕ → Bool} {k m : ℕ}
    (h : ∀ di ∈ Coherent.tupList k m, ∀ dt ∈ Coherent.tupList k m, di.Nodup → dt.Nodup →
      c di dt = c' di dt) :
    Case3.colXD c k m = Case3.colXD c' k m := by
  unfold Case3.colXD
  congr 1
  apply List.map_congr_left
  intro dt hdt
  unfold Case3.colXVal
  split_ifs with hnd
  · rw [Case3.firstIdx_congr (Q := fun di => decide di.Nodup && c' di dt) (fun di hdi => ?_)]
    by_cases hdn : di.Nodup
    · simp only [hdn, decide_true, Bool.true_and]
      exact h di hdi dt hdt hdn hnd
    · simp [hdn]
  · rfl

/-- **The first structure of `x` is unique**: any two colourings characterized by certificate
equivalence (`ColChar`) give the same colouring of `x`, so the same first structure. -/
theorem m5_c3First_unique {N n : ℕ} {G : Subgroup (Perm (Fin N))} {hC : CertSetting G n}
    {φ : strGroup hC →* Perm (Fin (N - n))} {xs : Fin n → ℕ} {M k : ℕ} {Vx : List ℕ}
    {X₀ X₁ : SoJTree.OutD} (h₀ : Case3.C3First φ xs M k Vx X₀)
    (h₁ : Case3.C3First φ xs M k Vx X₁) : X₀ = X₁ := by
  obtain ⟨c, hc, hX₀⟩ := h₀
  obtain ⟨c', hc', hX₁⟩ := h₁
  have hcol : Case3.colXD c k Vx.length = Case3.colXD c' k Vx.length :=
    m5_colXD_congr fun di hdi dt hdt hn hn' =>
      Bool.eq_iff_iff.2 ((hc di hdi dt hdt hn hn').trans (hc' di hdi dt hdt hn hn').symm)
  rw [hcol, hX₁] at hX₀
  exact (Option.some.inj hX₀).symm

end Case3Data

section Case3Prog

variable {D : Ty} {rec : Ty × Ty} {var : Ty → Type}

/-- **Case 3's sub-solver.** `case3Prog` uses one sub-solver for the comparisons of the
colourings (windows of at most `n / k` points) and for Align's cosets (the whole window, of
`wl` points): the window's length decides between the hinted sub-solver without a hint and
reduce-and-derive's per-coset program. -/
def c3Sub (sub : var (hinstTy D) → Prog (groupSig D) rec var (Ty.answer D))
    (n₀ n : var .nat) (L : var (.array (.list .nat))) (st : var stTy) (wl : var .nat)
    (J : var (Ty.inst D)) : Prog (groupSig D) rec var (Ty.answer D) :=
  .bind (.op1 .snd J) fun wc => .bind (.op1 .fst wc) fun w' => .bind (.op1 .fst w') fun pts =>
  .bind (.op1 .length pts) fun l => .bind (.op2 .natEq l wl) fun same =>
  .ite same (Main.rdBranch sub n₀ n L st J) (plainSub sub n₀ n J)

/-- **Case 3 of M5**: stage 14i's `case3Prog` with `c3Sub`; on its fallback signal (no good list
of the Design Lemma), the kernel reduction `m3Prog` of the instance. -/
def m5Case3Prog (sub : var (hinstTy D) → Prog (groupSig D) rec var (Ty.answer D))
    (I : var (hinstTy D)) (n₀ n : var .nat) (L : var (.array (.list .nat))) (st : var stTy)
    (k : var .nat) (xy : var Ty.strs) (w : var Ty.win) (G : var (Ty.group D))
    (Vx Vy : var (.list .nat)) : Prog (groupSig D) rec var (Ty.answer D) :=
  .bind (.op1 .fst w) fun pts => .bind (.op1 .length pts) fun wl =>
  .bind (Case3.case3Prog (fun J => c3Sub sub n₀ n L st wl J) n k xy w G Vx Vy) fun res =>
  .caseOption res (Main.m3Prog sub I) fun ans => .ret ans

end Case3Prog

/-- Case 3's closed cost is monotone in the cost of one comparison. -/
theorem c3CostC_mono_CI {n N s g k mx my CI CI' Z BgP Bmem Bk Bl Bg1 Bgen Cb : ℕ}
    (h : CI ≤ CI') :
    Case3.c3CostC n N s g k mx my CI Z BgP Bmem Bk Bl Bg1 Bgen Cb ≤
      Case3.c3CostC n N s g k mx my CI' Z BgP Bmem Bk Bl Bg1 Bgen Cb := by
  unfold Case3.c3CostC Case3.c3Cost Case3.tupleColCost Case3.entryXCost Case3.entryYCost
    Case3.cmpCost Case3.firstIdxCost
  gcongr

/-- Case 3's closed cost is affine in the cost of one comparison, with `3 · mx^k · mx^k`
comparisons. -/
theorem c3CostC_add_CI (n N s g k mx my A CI Z BgP Bmem Bk Bl Bg1 Bgen Cb : ℕ) :
    Case3.c3CostC n N s g k mx my (A + CI) Z BgP Bmem Bk Bl Bg1 Bgen Cb =
      Case3.c3CostC n N s g k mx my CI Z BgP Bmem Bk Bl Bg1 Bgen Cb + 3 * mx ^ k * mx ^ k * A := by
  unfold Case3.c3CostC Case3.c3Cost Case3.tupleColCost Case3.entryXCost Case3.entryYCost
    Case3.cmpCost Case3.firstIdxCost
  ring

/-- Case 3's closed cost is affine in the cost of one candidate of Align, with `c3R`
candidates. -/
theorem c3CostC_add_Cb (n N s g k mx my CI Z BgP Bmem Bk Bl Bg1 Bgen A Cb : ℕ) :
    Case3.c3CostC n N s g k mx my CI Z BgP Bmem Bk Bl Bg1 Bgen (A + Cb) =
      Case3.c3CostC n N s g k mx my CI Z BgP Bmem Bk Bl Bg1 Bgen Cb + Case3.c3R k my Z * A := by
  unfold Case3.c3CostC Case3.c3Cost
  rw [alignCost_add]
  ring

section Case3Sub

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}
  {sub : HInstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)}
  {n₀ n : ℕ} {L : LabelData} {st : ℕ × CJData}

/-- `c3Sub` on a window of the full length: reduce-and-derive's per-coset program. -/
theorem RunsWithin.c3Sub_align {J : InstData D} {wl : ℕ} (hwl : J.2.1.1.length = wl)
    {ans : AnswerData D} {k : ℕ}
    (h : RunsWithin X body (Main.rdBranch sub n₀ n L st J) ans k) :
    RunsWithin X body (Main.c3Sub sub n₀ n L st wl J) ans (k + wl + 6) := by
  apply RunsWithin.mono
  case h =>
    unfold Main.c3Sub
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    have he : (J.2.1.1.length == wl) = true := beq_iff_eq.2 hwl
    simp only [Prim.eval, he]
    exact RunsWithin.ite_true h
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head]
    omega

/-- `c3Sub` on a shorter window: the hinted sub-solver without a hint. -/
theorem RunsWithin.c3Sub_cmp {J : InstData D} {wl : ℕ} (hwl : J.2.1.1.length < wl)
    {ans : AnswerData D} {k : ℕ}
    (h : RunsWithin X body (Main.plainSub sub n₀ n J) ans k) :
    RunsWithin X body (Main.c3Sub sub n₀ n L st wl J) ans (k + wl + 6) := by
  apply RunsWithin.mono
  case h =>
    unfold Main.c3Sub
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    have he : (J.2.1.1.length == wl) = false := by simpa using hwl.ne
    simp only [Prim.eval, he]
    exact RunsWithin.ite_false h
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head]
    omega

/-- A sub-solver's output bound can be raised. -/
theorem m5_subSolves_mono {sub' : InstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)}
    {P : InstData D → Prop} {Cf : InstData D → ℕ} {s₁ s₂ : ℕ}
    (h : SubSolves X body DV sub' P Cf s₁) (hs : s₁ ≤ s₂) : SubSolves X body DV sub' P Cf s₂ :=
  fun I hI => by
    obtain ⟨ans, hr, hok, hg⟩ := h I hI
    exact ⟨ans, hr, hok, fun c hc => (hg c hc).trans hs⟩

/-- **`c3Sub` meets Align's sub-solver hypothesis** where reduce-and-derive does: Align's
instances have the whole window, of `wl` points. -/
theorem m5_c3Sub_align {P : InstData D → Prop} {Cb s' wl : ℕ}
    (h : SubSolves X body DV (Main.rdBranch (var := Ty.denote) (rec := (a, b)) (D := D) sub n₀ n
      L st) P (fun _ => Cb) s') (hP : ∀ J, P J → J.2.1.1.length = wl) :
    SubSolves X body DV (fun J => Main.c3Sub sub n₀ n L st wl J) P (fun _ => Cb + wl + 6) s' :=
  fun J hJ => by
    obtain ⟨ans, hr, hok, hg⟩ := h J hJ
    exact ⟨ans, RunsWithin.c3Sub_align (hP J hJ) hr, hok, hg⟩

/-- **`c3Sub` meets the comparisons' sub-solver hypothesis** where the hinted sub-solver without
a hint does: the comparisons' windows are shorter than `wl`. -/
theorem m5_c3Sub_cmp {P : InstData D → Prop} {Cc s' wl : ℕ}
    (h : SubSolves X body DV (fun J => Main.plainSub sub n₀ n J) P (fun _ => Cc) s')
    (hP : ∀ J, P J → J.2.1.1.length < wl) :
    SubSolves X body DV (fun J => Main.c3Sub sub n₀ n L st wl J) P (fun _ => Cc + wl + 6) s' :=
  fun J hJ => by
    obtain ⟨ans, hr, hok, hg⟩ := h J hJ
    exact ⟨ans, RunsWithin.c3Sub_cmp (hP J hJ) hr, hok, hg⟩

end Case3Sub

/-- The number of the comparisons' sub-calls in Case 3: `3 · mx^k · mx^k` comparisons of at
most `n · k! · n` sub-calls each (`certIsoCost_le`). -/
def c3Count (mx k n : ℕ) : ℕ := 3 * mx ^ k * mx ^ k * (n * (k.factorial * n))

/-- The work of Case 3 besides its sub-calls: the closed cost `c3CostC` with each comparison at
its polynomial part plus `wl + 10` per sub-call (the dispatch of `c3Sub` and the wrapper), and
each candidate of Align at `Wb + wl + 6`. -/
def c3Work (n N s g k mx my Z BgP Bmem Bker Bl Bg1 Bgen Bstab Btr Borb Bgen' Borb' Bstab' Bgk
    Bgs wl Wb : ℕ) : ℕ :=
  Case3.c3CostC n N s g k mx my
    (k.factorial * certIsoPoly N n k s Bstab Btr Borb Bgen' Borb' Bstab' Bgk Bl Bgs +
      n * (k.factorial * (n * (wl + 10)))) Z BgP Bmem Bker Bl Bg1 Bgen (Wb + wl + 6)

/-- **Case 3's cost by count**: the comparisons' sub-calls at cost `A` each, Align's candidates
at `S₀` each, and the work `c3Work`. -/
theorem c3CostC_split (n N s g k mx my Z BgP Bmem Bker Bl Bg1 Bgen Bstab Btr Borb Bgen' Borb'
    Bstab' Bgk Bgs wl Wb A S₀ : ℕ) :
    Case3.c3CostC n N s g k mx my
        (certIsoCost N n k s Bstab Btr Borb Bgen' Borb' Bstab' Bgk (A + 4 + wl + 6) Bl Bgs) Z
        BgP Bmem Bker Bl Bg1 Bgen (S₀ + Wb + wl + 6) ≤
      Case3.c3R k my Z * S₀ + c3Count mx k n * A +
        c3Work n N s g k mx my Z BgP Bmem Bker Bl Bg1 Bgen Bstab Btr Borb Bgen' Borb' Bstab' Bgk
          Bgs wl Wb := by
  refine (c3CostC_mono_CI (certIsoCost_le _ _ _ _ _ _ _ _ _ _ _ _ _ _)).trans (le_of_eq ?_)
  rw [show k.factorial * certIsoPoly N n k s Bstab Btr Borb Bgen' Borb' Bstab' Bgk Bl Bgs +
      n * (k.factorial * (n * (A + 4 + wl + 6))) = n * (k.factorial * (n * A)) +
      (k.factorial * certIsoPoly N n k s Bstab Btr Borb Bgen' Borb' Bstab' Bgk Bl Bgs +
        n * (k.factorial * (n * (wl + 10)))) by ring, c3CostC_add_CI,
    show S₀ + Wb + wl + 6 = S₀ + (Wb + wl + 6) by ring, c3CostC_add_Cb, c3Count, c3Work]
  ring

/-- `n ≤ |W|` when every string position lies in the window. -/
theorem m5_n_le_win {N n : ℕ} {w : WinData} (hw : w.Valid N) (hnN : n ≤ N)
    (hwS : ∀ u : Fin N, u.val < n → u ∈ w.denote N) : n ≤ w.1.length := by
  have hsub : Finset.range n ⊆ w.1.toFinset := fun i hi => by
    have hi' := Finset.mem_range.1 hi
    exact List.mem_toFinset.2 (hwS ⟨i, by omega⟩ hi')
  have := Finset.card_le_card hsub
  rwa [Finset.card_range, List.toFinset_card_of_nodup hw.nodup] at this

section Case3Spec

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}
  {sub : HInstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)}
  {C : ℕ → Option ℕ → ℕ} {s : ℕ} {xy : StrData × StrData} {w : WinData}
  {N : ℕ} {gs : GensData} {d : D.denote} {n₀ n : ℕ} {L : LabelData} {st : ℕ × CJData}
  {sIn Lg Blift Bgen Bo Bk Bcr Bd : ℕ}

/-- **Case 3 of M5** (factor `m!` for the aligned cosets). Under `case3Prog_canonical`'s
hypotheses (the window contains every string position; `Vx`, `Vy` the fixed points of
`ψ(F(x))`, `ψ(F(y))`; backend bounds at the sub-solver's bound `sIn`), reduce-and-derive's for
the aligned group of `x`'s first structure, and the kernel reduction's charges: the answer is
correct for `G` on `W`. The comparisons make `c3Count` sub-calls without a hint on windows of at
most `n / k` points, of cost `C (n / k) none` each; the children of Align and of the fallback
(`m3Prog`, when `case3Prog` signals it) are `StepChild |W| m` with windows summing to at most
`(c3R · m! + m!) · |W|`. -/
theorem RunsWithin.m5Case3Prog (hOc : MeetsContractOn DV Case3.c3Ops X.O)
    (hPc : ∀ op x, Case3.c3Ops op → GroupPre DV op x → X.Pre op x)
    (hO : MeetsContractOn DV rdOps X.O)
    (hPre : ∀ op x, rdOps op → GroupPre DV op x → X.Pre op x)
    (hOk : MeetsContractOn DV kerRedOps X.O)
    (hPk : ∀ op x, kerRedOps op → GroupPre DV op x → X.Pre op x)
    (hI : HInstValid DV (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D))
    {hC : CertSetting (GensData.denote N gs) n} {φ : strGroup hC →* Perm (Fin (N - n))}
    (hφ : IsPhi hC φ)
    (halt : alternatingGroup (Fin (N - n)) ≤ (baseHom _ n hC.base).range)
    (hwS : ∀ u : Fin N, u.val < n → u ∈ w.denote N)
    {Fmap : (Fin N → ℕ) → Subgroup (Perm (Fin N))}
    (hloc : ∀ x x', (∀ u ∈ w.denote N, x u = x' u) → Fmap x = Fmap x')
    (heq : ∀ g ∈ GensData.denote N gs, ∀ x,
      Fmap (relabel g x) = (Fmap x).map (MulAut.conj g).toMonoidHom)
    {Fx Fy : Subgroup (Perm (Fin N))} (hFxe : Fx = Fmap (xy.1.denote N))
    (hFye : Fy = Fmap (xy.2.denote N)) (hFxi : IsInvariant Fx (baseSet n N))
    (hFyi : IsInvariant Fy (baseSet n N))
    {Vx Vy : List ℕ} (hVx : ∀ v ∈ Vx, v < N - n) (hVxn : Vx.Nodup)
    (hVy : ∀ v ∈ Vy, v < N - n) (hVyn : Vy.Nodup)
    (hVxF : ∀ v : Fin (N - n), v.val ∈ Vx ↔ ∀ f ∈ (baseHom Fx n hFxi).range, f v = v)
    (hVyF : ∀ v : Fin (N - n), v.val ∈ Vy ↔ ∀ f ∈ (baseHom Fy n hFyi).range, f v = v)
    (hm : 6 ≤ Vx.length) {k : ℕ} (h5 : 5 ≤ k) (hk : k + 2 ≤ N - n)
    {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N sIn G₀) (hgs : gs.length ≤ sIn)
    (hGG₀ : GensData.denote N gs ≤ G₀) {sk : ℕ} (Bk' : BackendBounds X DV k sk ⊤)
    (hsk : sIn ≤ k * (sk + 1)) {Bgk Bl Bgs : ℕ}
    (hBgk : ∀ gs' : GensData, GensData.AllValid N gs' →
      gs'.length ≤ k.factorial * (sIn + 1) → GensData.denote N gs' ≤ GensData.denote N gs →
        X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ Bgk)
    (hBl : ∀ π : PermData, X.B.call GroupOp.lift ((N, gs, d), (baseWin n N, π))
      (liftModel X.O n (N, gs, d) π) ≤ Bl)
    (hBgs : ∀ al : List ℕ, al.Nodup → al.length = k → (∀ a ∈ al, a < N - n) → ∀ b₁ b₂,
      X.B.call GroupOp.generate (N, giantGens X.O n (N, gs, d) al b₁ b₂)
        (giantSetStabModel X.O n (N, gs, d) al b₁ b₂) ≤ Bgs)
    {BgP Bmem Bker Bg1 Bgen' : ℕ}
    (hBgP : X.B.call GroupOp.generate (N - n, gs.map (baseD n N))
      (X.O.run GroupOp.generate (N - n, gs.map (baseD n N))) ≤ BgP)
    (hBmem : ∀ g : PermData, g.Valid (N - n) → X.B.call GroupOp.mem (pModel X.O n (N, gs, d), g)
      (X.O.run GroupOp.mem (pModel X.O n (N, gs, d), g)) ≤ Bmem)
    (hBker : X.B.call GroupOp.kernel ((N, gs, d), baseWin n N) (kerModel X.O n (N, gs, d)) ≤
      Bker)
    (hBg1 : ∀ X₀ : SoJTree.OutD, Case3.C3First φ (strOn hC.le (xy.1.denote N)) (N - n) k Vx X₀ →
      X.B.call GroupOp.generate
        (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (Case2b.outGensD (N - n) X₀))).map
          (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
        (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
          (Case2b.outGensD (N - n) X₀)))) ≤ Bg1)
    (hBgen : ∀ gs' : GensData, GensData.AllValid N gs' →
      gs'.length ≤ Case3.c3R k Vy.length (Case2b.sojZ (N - n)) * (sIn + 1) →
      GensData.denote N gs' ≤ GensData.denote N gs →
      X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ Bgen')
    (hsub : HSubSolves X body DV sub
      (fun J => SizeChild sIn (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D)
        J ∧ StepChild w.1.length (N - n) (J.winSize, J.baseOpt)) C s)
    (hCmono : ∀ a b, a ≤ b → C a none ≤ C b none)
    (hB : RDBounds X DV n N sIn Lg Blift Bgen Bo Bk Bcr) (hs : s ≤ sIn)
    (hLg : (N - n).factorial * (sIn + 1) ≤ Lg)
    (hD : ∀ X₀, Case3.C3First φ (strOn hC.le (xy.1.denote N)) (N - n) k Vx X₀ →
      ∀ gs' d' O', RDSet DV n N gs w L
        (Giant.g1Model X.O n (N, gs, d) (Case2b.outOps (N - n)) X₀).2.1 sIn gs' d' O' →
      RDOrbit X body DV n N w L st sIn Bd gs' d' O')
    {Bk3 Bo3 Bcr3 Bgen3 : ℕ}
    (hBk3 : X.B.call GroupOp.kernel ((N, gs, d), baseWin n N) (kerModel X.O n (N, gs, d)) ≤ Bk3)
    (hBo3 : X.B.call GroupOp.orbits (kerModel X.O n (N, gs, d), w)
      (krOrbits X.O n (N, gs, d) w) ≤ Bo3)
    (hBcr3 : X.B.call GroupOp.cosetReps ((N, gs, d), kerModel X.O n (N, gs, d))
      (kerReps X.O n (N, gs, d)) ≤ Bcr3)
    (hB3 : ∀ hs : GensData, GensData.AllValid N hs →
      hs.length ≤ (kerReps X.O n (N, gs, d)).length *
        (max s (kerModel X.O n (N, gs, d)).2.1.length + 1) →
      GensData.denote N hs ≤ GensData.denote N gs →
      X.B.call GroupOp.generate (N, hs) (X.O.run GroupOp.generate (N, hs)) ≤ Bgen3) :
    ∃ (ans : AnswerData D) (ch : List (ℕ × Option ℕ)),
      RunsWithin X body (Main.m5Case3Prog sub
          (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D) n₀ n L st k xy w
          (N, gs, d) Vx Vy) ans
        ((ch.map fun x => C x.1 x.2).sum + c3Count Vx.length k n * C (n / k) none +
          (c3Work n N sIn gs.length k Vx.length Vy.length (Case2b.sojZ (N - n)) BgP Bmem Bker Bl
            Bg1 Bgen' B.Bstab B.Btr B.Borb Bk'.Bgen Bk'.Borb Bk'.Bstab Bgk Bgs w.1.length
            (w.1.length * rdOrbitWork N n w.1.length s sIn (N - n).factorial Bd Blift Bgen Bo
              (rd6Cost N n w.1.length s sIn Bk Bo Bcr Bgen) + dynSeqCost N w.1.length Bo + 5) +
          (kerRedCost N n w.1.length (kerReps X.O n (N, gs, d)).length
            (kerModel X.O n (N, gs, d)).2.1.length s Bk3 Bo3 Bcr3 Bgen3 + 5) + w.1.length + 3)) ∧
      AnsOK DV N (w.denote N) 1 (GensData.denote N gs) (xy.1.denote N) (xy.2.denote N) ans ∧
      (∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sIn) ∧
      ChildList w.1.length
        (Case3.c3R k Vy.length (Case2b.sojZ (N - n)) * (N - n).factorial + (N - n).factorial)
        (StepChild w.1.length (N - n)) ch := by
  have hGv : GroupValid DV N gs d := hI.valid.group
  have hw : w.Valid N := hI.valid.win
  have hWG : IsInvariant (GensData.denote N gs) (w.denote N) := hI.valid.invariant
  have hOa : MeetsContractOn DV alignOps X.O := fun op x h hx => hOc op x (Or.inr h) hx
  have hPa : ∀ op x, alignOps op → GroupPre DV op x → X.Pre op x :=
    fun op x h hx => hPc op x (Or.inr h) hx
  have hnw : n ≤ w.1.length := m5_n_le_win hw hI.le hwS
  have hw1 : 1 ≤ w.1.length := by
    obtain ⟨i, hi, -⟩ := (hI.hint L rfl).1.nonconst
    exact List.length_pos_of_mem hi
  set Wb := w.1.length * rdOrbitWork N n w.1.length s sIn (N - n).factorial Bd Blift Bgen Bo
    (rd6Cost N n w.1.length s sIn Bk Bo Bcr Bgen) + dynSeqCost N w.1.length Bo + 5 with hWb
  -- the comparisons' sub-solver
  have hPcmp : ∀ (xy' : StrData × StrData) (J : InstData D),
      StepSubP (DV := DV) (GensData.denote N gs) xy' n k sIn J →
      SizeChild sIn (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D)
          ((J, n₀, n, none) : HInstData D) ∧
        StepChild w.1.length (N - n) (HInstData.winSize ((J, n₀, n, none) : HInstData D),
          HInstData.baseOpt ((J, n₀, n, none) : HInstData D)) := by
    intro xy' J hJ
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
  have hcmp : ∀ xy' : StrData × StrData,
      SubSolves X body DV (fun J => Main.c3Sub sub n₀ n L st w.1.length J)
        (StepSubP (DV := DV) (GensData.denote N gs) xy' n k sIn)
        (fun _ => C (n / k) none + 4 + w.1.length + 6) sIn := fun xy' =>
    m5_subSolves_mono (m5_c3Sub_cmp (m5_stepSub hsub hCmono (by omega) hC xy' (hPcmp xy'))
      (fun J hJ => by
        obtain ⟨-, -, -, -, hkw, -, -⟩ := hJ
        have := Nat.mul_le_mul_right J.2.1.1.length h5
        omega)) hs
  -- Align's sub-solver, from the unique first structure
  have hpack : ∃ ch₀ : List (ℕ × Option ℕ),
      ((ch₀.map Prod.fst).sum ≤ (N - n).factorial * w.1.length ∧
        (∀ x ∈ ch₀, StepChild w.1.length (N - n) x) ∧ ∀ x ∈ ch₀, 1 ≤ x.1) ∧
      ∀ X₀ : SoJTree.OutD, Case3.C3First φ (strOn hC.le (xy.1.denote N)) (N - n) k Vx X₀ →
        SubSolves X body DV (fun J => Main.c3Sub sub n₀ n L st w.1.length J)
          (fun I => I.1 = xy ∧ I.2.1 = w ∧
            I.2.2.2 = preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O
              (pModel X.O n (N, gs, d)) (Case2b.outGensD (N - n) X₀))) ∧ I.Valid DV)
          (fun _ => (ch₀.map fun x => C x.1 x.2).sum + Wb + w.1.length + 6) sIn := by
    by_cases hex : ∃ X₀₀, Case3.C3First φ (strOn hC.le (xy.1.denote N)) (N - n) k Vx X₀₀
    · obtain ⟨X₀₀, hX₀₀⟩ := hex
      have hXv : Case2b.OutValid (N - n) X₀₀ := by
        obtain ⟨c, -, hfs⟩ := hX₀₀
        exact Case3.c3p_allStructsD_valid hVx hVxn _ hm X₀₀ (Case3.firstStructD_mem hfs)
      obtain ⟨ch₀, hgood, hsubA⟩ := m5_alignSub (C := C) (Bk := Bk) (Bcr := Bcr)
        (W6 := rd6Cost N n w.1.length s sIn Bk Bo Bcr Bgen) hOa hPa hO hPre hI hC.base halt B
        hGG₀ le_rfl (Case2b.outOps_spec (N - n)) hXv hBl hsub hB hs hLg (Nat.factorial_pos _)
        (Nat.self_le_factorial _) (hD X₀₀ hX₀₀) (Or.inl le_rfl) (Or.inr ⟨le_rfl, le_rfl⟩)
      refine ⟨ch₀, hgood, fun X₀ hX₀ => ?_⟩
      obtain rfl := m5_c3First_unique hX₀ hX₀₀
      exact m5_c3Sub_align hsubA (fun J hJ => by rw [hJ.2.1])
    · exact ⟨[], ⟨by simp, by simp, by simp⟩, fun X₀ hX₀ => absurd ⟨X₀, hX₀⟩ hex⟩
  obtain ⟨ch₀, hgood, hsubA⟩ := hpack
  obtain ⟨res, hrun, -, hsome⟩ := Case3.RunsWithin.case3Prog_canonical (body := body)
    (sub := fun J => Main.c3Sub sub n₀ n L st w.1.length J) hOc hPc hφ hGv halt hw hWG hwS
    hloc heq hFxe hFye hFxi hFyi hVx hVxn hVy hVyn hVxF hVyF hm h5 hk B hgs hGG₀ Bk' hsk hBgk
    hBl hBgs (hcmp _) (hcmp _) (hcmp _) hBgP hBmem hBker hBg1 hBgen hsubA
  -- the run of the whole program, from the two parts
  have hcomp : ∀ (ans : AnswerData D) (c₂ : ℕ),
      RunsWithin X body (.caseOption res (Main.m3Prog sub
        (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D))
        fun a => .ret a) ans c₂ →
      RunsWithin X body (Main.m5Case3Prog sub
          (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D) n₀ n L st k xy w
          (N, gs, d) Vx Vy) ans
        (Case3.c3CostC n N sIn gs.length k Vx.length Vy.length
          (certIsoCost N n k sIn B.Bstab B.Btr B.Borb Bk'.Bgen Bk'.Borb Bk'.Bstab Bgk
            (C (n / k) none + 4 + w.1.length + 6) Bl Bgs)
          (Case2b.sojZ (N - n)) BgP Bmem Bker Bl Bg1 Bgen'
          ((ch₀.map fun x => C x.1 x.2).sum + Wb + w.1.length + 6) + c₂ + w.1.length + 2) := by
    intro ans c₂ h2
    apply RunsWithin.mono
    case h =>
      unfold Main.m5Case3Prog
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step hrun
      exact h2
    case hc =>
      simp only [Prim.cost, Prim.eval, Args.head]
      omega
  have hsplit := c3CostC_split n N sIn gs.length k Vx.length Vy.length (Case2b.sojZ (N - n)) BgP
    Bmem Bker Bl Bg1 Bgen' B.Bstab B.Btr B.Borb Bk'.Bgen Bk'.Borb Bk'.Bstab Bgk Bgs w.1.length
    Wb (C (n / k) none) (ch₀.map fun x => C x.1 x.2).sum
  have hrep := m5_replicate_childList (k := Case3.c3R k Vy.length (Case2b.sojZ (N - n))) hgood
  have hrepc := m5_replicate_cost (C := C) (k := Case3.c3R k Vy.length (Case2b.sojZ (N - n)))
    (ch₀ := ch₀)
  rcases res with _ | ans
  · -- the fallback: the kernel reduction
    have hkg : (kerModel X.O n (N, gs, d)).2.1.length ≤ sIn := hB.kerGens gs d hGv hgs
    obtain ⟨ans, ch₃, hrun₃, hok₃, hg₃, hch₃, hreps⟩ := RunsWithin.m3Prog hOk hPk hI
      (hsub.mono fun J hJ => ⟨hJ.1.mono (max_le hs hkg), hJ.2⟩) hBk3 hBo3 hBcr3 hB3
    refine ⟨ans, (List.replicate (Case3.c3R k Vy.length (Case2b.sojZ (N - n))) ch₀).flatten ++
      ch₃, (hcomp ans _ (RunsWithin.caseOption_none hrun₃)).mono ?_, ?_,
      hg₃ sIn (fun hs' hv _ => hB.genOut N le_rfl hs' hv), ⟨?_, ?_, ?_⟩⟩
    · rw [List.map_append, List.sum_append, hrepc]
      generalize (ch₃.map fun x => C x.1 x.2).sum = A₃ at *
      omega
    · have h : AnsOK DV N (w.denote N) (PermData.denote N (PermData.one N)) (GensData.denote N gs)
          (xy.1.denote N) (xy.2.denote N) ans := hok₃
      rwa [PermData.denote_one] at h
    · rw [List.map_append, List.sum_append, Nat.add_mul]
      have h1 := hrep.sum_le
      have h2 := hch₃.sum_le
      have h3 := Nat.mul_le_mul_right w.1.length hreps
      omega
    · intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact hrep.pred x hx
      · exact hch₃.pred x hx
    · intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact hrep.pos x hx
      · exact hch₃.pos x hx
  · -- an answer of `case3Prog`
    obtain ⟨hok, hg⟩ := hsome ans rfl
    refine ⟨ans, (List.replicate (Case3.c3R k Vy.length (Case2b.sojZ (N - n))) ch₀).flatten,
      (hcomp ans _ (RunsWithin.caseOption_some
        (RunsWithin.ret (X := X) (body := body) (t := Ty.answer D) ans))).mono ?_, hok,
      hg sIn (fun hs' hv _ => hB.genOut N le_rfl hs' hv), ⟨?_, hrep.pred, hrep.pos⟩⟩
    · rw [hrepc]
      omega
    · have h1 := hrep.sum_le
      rw [Nat.add_mul]
      omega

end Case3Spec

/-! ### Well-formedness -/

section Wf

variable {D : Ty} {rec : Ty × Ty} {var₁ var₂ : Ty → Type} {r : Bool} {Γ : WfCtx var₁ var₂}

local macro "m5_mem" : tactic =>
  `(tactic| repeat (first | exact List.mem_cons_self | assumption | apply List.mem_cons_of_mem))

theorem wf_m5Case1Prog {sub₁ : var₁ (hinstTy D) → Prog (groupSig D) rec var₁ (Ty.answer D)}
    {sub₂ : var₂ (hinstTy D) → Prog (groupSig D) rec var₂ (Ty.answer D)}
    (hsub : WfFun r Γ sub₁ sub₂) {n₀₁ n₁ : var₁ .nat} {n₀₂ n₂ : var₂ .nat}
    {L₁ : var₁ (.array (.list .nat))} {L₂ : var₂ (.array (.list .nat))} {st₁ : var₁ stTy}
    {st₂ : var₂ stTy} {xy₁ : var₁ Ty.strs} {xy₂ : var₂ Ty.strs} {w₁ : var₁ Ty.win}
    {w₂ : var₂ Ty.win} {G₁ Fx₁ Fy₁ : var₁ (Ty.group D)} {G₂ Fx₂ Fy₂ : var₂ (Ty.group D)}
    (hn₀ : ⟨.nat, n₀₁, n₀₂⟩ ∈ Γ) (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ)
    (hL : ⟨.array (.list .nat), L₁, L₂⟩ ∈ Γ) (hst : ⟨stTy, st₁, st₂⟩ ∈ Γ)
    (hxy : ⟨Ty.strs, xy₁, xy₂⟩ ∈ Γ) (hw : ⟨Ty.win, w₁, w₂⟩ ∈ Γ)
    (hG : ⟨Ty.group D, G₁, G₂⟩ ∈ Γ) (hFx : ⟨Ty.group D, Fx₁, Fx₂⟩ ∈ Γ)
    (hFy : ⟨Ty.group D, Fy₁, Fy₂⟩ ∈ Γ) :
    Prog.Wf r Γ (m5Case1Prog sub₁ n₀₁ n₁ L₁ st₁ xy₁ w₁ G₁ Fx₁ Fy₁)
      (m5Case1Prog sub₂ n₀₂ n₂ L₂ st₂ xy₂ w₂ G₂ Fx₂ Fy₂) :=
  Giant.wf_case1Prog (wf_rdBranch hsub hn₀ hn hL hst) hn hxy hw hG hFx hFy

theorem wf_pbInner {sub₁ : var₁ (hinstTy D) → Prog (groupSig D) rec var₁ (Ty.answer D)}
    {sub₂ : var₂ (hinstTy D) → Prog (groupSig D) rec var₂ (Ty.answer D)}
    (hsub : WfFun r Γ sub₁ sub₂) {n₀₁ : var₁ .nat} {n₀₂ : var₂ .nat}
    (hn₀ : ⟨.nat, n₀₁, n₀₂⟩ ∈ Γ) : WfFun r Γ (pbInner sub₁ n₀₁) (pbInner sub₂ n₀₂) := by
  intro Γ' hΓ J₁ J₂ hJ
  have hn₀' := hΓ hn₀
  unfold pbInner
  refine .bind (.prim _ (.cons hJ .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  exact wf_plainSub (hsub.mono fun y hy => by have := hΓ hy; m5_mem) (by m5_mem)
    (List.Mem.head _) _ (fun y hy => hy) _ _ (by m5_mem)

theorem wf_pbSubR {sub₁ : var₁ (hinstTy D) → Prog (groupSig D) rec var₁ (Ty.answer D)}
    {sub₂ : var₂ (hinstTy D) → Prog (groupSig D) rec var₂ (Ty.answer D)}
    (hsub : WfFun r Γ sub₁ sub₂) {n₀₁ : var₁ .nat} {n₀₂ : var₂ .nat}
    (hn₀ : ⟨.nat, n₀₁, n₀₂⟩ ∈ Γ) : WfFun r Γ (pbSubR sub₁ n₀₁) (pbSubR sub₂ n₀₂) := by
  intro Γ' hΓ J₁ J₂ hJ
  exact wf_restrictProg (wf_pbInner (hsub.mono hΓ) (hΓ hn₀)) hJ

theorem wf_m5Case2aProg {sub₁ : var₁ (hinstTy D) → Prog (groupSig D) rec var₁ (Ty.answer D)}
    {sub₂ : var₂ (hinstTy D) → Prog (groupSig D) rec var₂ (Ty.answer D)}
    (hsub : WfFun r Γ sub₁ sub₂) {n₀₁ n₁ : var₁ .nat} {n₀₂ n₂ : var₂ .nat}
    {xy₁ : var₁ Ty.strs} {xy₂ : var₂ Ty.strs} {w₁ : var₁ Ty.win} {w₂ : var₂ Ty.win}
    {G₁ : var₁ (Ty.group D)} {G₂ : var₂ (Ty.group D)} {Φx₁ Φy₁ : var₁ (.list .nat)}
    {Φx₂ Φy₂ : var₂ (.list .nat)} {F₁ : var₁ Ty.gens} {F₂ : var₂ Ty.gens}
    (hn₀ : ⟨.nat, n₀₁, n₀₂⟩ ∈ Γ) (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (hxy : ⟨Ty.strs, xy₁, xy₂⟩ ∈ Γ)
    (hw : ⟨Ty.win, w₁, w₂⟩ ∈ Γ) (hG : ⟨Ty.group D, G₁, G₂⟩ ∈ Γ)
    (hΦx : ⟨.list .nat, Φx₁, Φx₂⟩ ∈ Γ) (hΦy : ⟨.list .nat, Φy₁, Φy₂⟩ ∈ Γ)
    (hF : ⟨Ty.gens, F₁, F₂⟩ ∈ Γ) :
    Prog.Wf r Γ (m5Case2aProg sub₁ n₀₁ n₁ xy₁ w₁ G₁ Φx₁ Φy₁ F₁)
      (m5Case2aProg sub₂ n₀₂ n₂ xy₂ w₂ G₂ Φx₂ Φy₂ F₂) :=
  Giant.wf_case2aProg (wf_pbSubR hsub hn₀) hn hxy hw hG hΦx hΦy hF

theorem wf_m5Case2bProg {sub₁ : var₁ (hinstTy D) → Prog (groupSig D) rec var₁ (Ty.answer D)}
    {sub₂ : var₂ (hinstTy D) → Prog (groupSig D) rec var₂ (Ty.answer D)}
    (hsub : WfFun r Γ sub₁ sub₂) {n₀₁ n₁ : var₁ .nat} {n₀₂ n₂ : var₂ .nat}
    {L₁ : var₁ (.array (.list .nat))} {L₂ : var₂ (.array (.list .nat))} {st₁ : var₁ stTy}
    {st₂ : var₂ stTy} {xy₁ : var₁ Ty.strs} {xy₂ : var₂ Ty.strs} {w₁ : var₁ Ty.win}
    {w₂ : var₂ Ty.win} {G₁ Fx₁ Fy₁ : var₁ (Ty.group D)} {G₂ Fx₂ Fy₂ : var₂ (Ty.group D)}
    {Φx₁ Φy₁ : var₁ (.list .nat)} {Φx₂ Φy₂ : var₂ (.list .nat)}
    (hn₀ : ⟨.nat, n₀₁, n₀₂⟩ ∈ Γ) (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ)
    (hL : ⟨.array (.list .nat), L₁, L₂⟩ ∈ Γ) (hst : ⟨stTy, st₁, st₂⟩ ∈ Γ)
    (hxy : ⟨Ty.strs, xy₁, xy₂⟩ ∈ Γ) (hw : ⟨Ty.win, w₁, w₂⟩ ∈ Γ)
    (hG : ⟨Ty.group D, G₁, G₂⟩ ∈ Γ) (hFx : ⟨Ty.group D, Fx₁, Fx₂⟩ ∈ Γ)
    (hFy : ⟨Ty.group D, Fy₁, Fy₂⟩ ∈ Γ) (hΦx : ⟨.list .nat, Φx₁, Φx₂⟩ ∈ Γ)
    (hΦy : ⟨.list .nat, Φy₁, Φy₂⟩ ∈ Γ) :
    Prog.Wf r Γ (m5Case2bProg sub₁ n₀₁ n₁ L₁ st₁ xy₁ w₁ G₁ Fx₁ Fy₁ Φx₁ Φy₁)
      (m5Case2bProg sub₂ n₀₂ n₂ L₂ st₂ xy₂ w₂ G₂ Fx₂ Fy₂ Φx₂ Φy₂) :=
  Case2b.wf_case2bProg (wf_rdBranch hsub hn₀ hn hL hst) hn hxy hw hG hFx hFy hΦx hΦy

theorem wf_c3Sub {sub₁ : var₁ (hinstTy D) → Prog (groupSig D) rec var₁ (Ty.answer D)}
    {sub₂ : var₂ (hinstTy D) → Prog (groupSig D) rec var₂ (Ty.answer D)}
    (hsub : WfFun r Γ sub₁ sub₂) {n₀₁ n₁ wl₁ : var₁ .nat} {n₀₂ n₂ wl₂ : var₂ .nat}
    {L₁ : var₁ (.array (.list .nat))} {L₂ : var₂ (.array (.list .nat))} {st₁ : var₁ stTy}
    {st₂ : var₂ stTy} (hn₀ : ⟨.nat, n₀₁, n₀₂⟩ ∈ Γ) (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ)
    (hL : ⟨.array (.list .nat), L₁, L₂⟩ ∈ Γ) (hst : ⟨stTy, st₁, st₂⟩ ∈ Γ)
    (hwl : ⟨.nat, wl₁, wl₂⟩ ∈ Γ) :
    WfFun r Γ (c3Sub sub₁ n₀₁ n₁ L₁ st₁ wl₁) (c3Sub sub₂ n₀₂ n₂ L₂ st₂ wl₂) := by
  intro Γ' hΓ J₁ J₂ hJ
  have hn₀' := hΓ hn₀
  have hn' := hΓ hn
  have hL' := hΓ hL
  have hst' := hΓ hst
  have hwl' := hΓ hwl
  unfold c3Sub
  refine .bind (.prim _ (.cons hJ .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) (.cons (by m5_mem) .nil))) fun _ _ => ?_
  refine .ite (List.Mem.head _) ?_ ?_
  · exact wf_rdBranch (hsub.mono fun y hy => by have := hΓ hy; m5_mem) (by m5_mem) (by m5_mem)
      (by m5_mem) (by m5_mem) _ (fun y hy => hy) _ _ (by m5_mem)
  · exact wf_plainSub (hsub.mono fun y hy => by have := hΓ hy; m5_mem) (by m5_mem) (by m5_mem)
      _ (fun y hy => hy) _ _ (by m5_mem)

theorem wf_m5Case3Prog {sub₁ : var₁ (hinstTy D) → Prog (groupSig D) rec var₁ (Ty.answer D)}
    {sub₂ : var₂ (hinstTy D) → Prog (groupSig D) rec var₂ (Ty.answer D)}
    (hsub : WfFun r Γ sub₁ sub₂) {I₁ : var₁ (hinstTy D)} {I₂ : var₂ (hinstTy D)}
    {n₀₁ n₁ k₁ : var₁ .nat} {n₀₂ n₂ k₂ : var₂ .nat}
    {L₁ : var₁ (.array (.list .nat))} {L₂ : var₂ (.array (.list .nat))} {st₁ : var₁ stTy}
    {st₂ : var₂ stTy} {xy₁ : var₁ Ty.strs} {xy₂ : var₂ Ty.strs} {w₁ : var₁ Ty.win}
    {w₂ : var₂ Ty.win} {G₁ : var₁ (Ty.group D)} {G₂ : var₂ (Ty.group D)}
    {Vx₁ Vy₁ : var₁ (.list .nat)} {Vx₂ Vy₂ : var₂ (.list .nat)}
    (hI : ⟨hinstTy D, I₁, I₂⟩ ∈ Γ) (hn₀ : ⟨.nat, n₀₁, n₀₂⟩ ∈ Γ) (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ)
    (hL : ⟨.array (.list .nat), L₁, L₂⟩ ∈ Γ) (hst : ⟨stTy, st₁, st₂⟩ ∈ Γ)
    (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ) (hxy : ⟨Ty.strs, xy₁, xy₂⟩ ∈ Γ) (hw : ⟨Ty.win, w₁, w₂⟩ ∈ Γ)
    (hG : ⟨Ty.group D, G₁, G₂⟩ ∈ Γ) (hVx : ⟨.list .nat, Vx₁, Vx₂⟩ ∈ Γ)
    (hVy : ⟨.list .nat, Vy₁, Vy₂⟩ ∈ Γ) :
    Prog.Wf r Γ (m5Case3Prog sub₁ I₁ n₀₁ n₁ L₁ st₁ k₁ xy₁ w₁ G₁ Vx₁ Vy₁)
      (m5Case3Prog sub₂ I₂ n₀₂ n₂ L₂ st₂ k₂ xy₂ w₂ G₂ Vx₂ Vy₂) := by
  unfold m5Case3Prog
  refine .bind (.prim _ (.cons hw .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (Case3.wf_case3Prog (wf_c3Sub (hsub.mono fun y hy => by m5_mem) (by m5_mem)
    (by m5_mem) (by m5_mem) (by m5_mem) (List.Mem.head _)) (by m5_mem) (by m5_mem) (by m5_mem)
    (by m5_mem) (by m5_mem) (by m5_mem) (by m5_mem)) fun _ _ => ?_
  refine .caseOption (List.Mem.head _)
    (wf_m3Prog (hsub.mono fun y hy => by m5_mem) (by m5_mem)) fun _ _ => ?_
  exact .ret (List.Mem.head _)

end Wf

end GraphIso.Main
