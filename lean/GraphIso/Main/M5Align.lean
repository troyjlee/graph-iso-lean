module

public import GraphIso.Main.RD
public import GraphIso.Giant.Case2a

/-!
# Align with reduce-and-derive

Stage 14j-4, item 3 (`PLAN-14.md` §14.4). The giant cases of M5 (Cases 1, 2b, 3) align a
structure `X(x)` on the base with the candidates for `y` (`alignProg`, stage 14f), and solve
each aligned coset `t • K`, `K = ψ⁻¹(Stab(X(x)))` (`c2_g1_spec`), by reduce-and-derive's
per-coset part (`rdBranch`, stage 14j-2): the dynamic chain over the window with the derived
hints of the orbits for the structure `st` that `K` preserves.

* **Uniform cost.** Align's sub-solver hypothesis has one cost for every valid representative
  `t`, while `rd_branch` bounds each branch by the costs of its own children. The valid
  representatives of degree `N` are finitely many (`exists_allPermsD`: every valid datum is
  `ofPerm` of its denotation), so a most expensive branch exists (`ml_exists_max`); its
  children `ch₀` bound every branch (`ar_branch_max`).
* **`RunsWithin.alignRd`**: for a hinted parent `(1 • G, W, L)` whose base action contains
  `Alt`, a structure `X₀` with candidates `Ys` such that every isomorphism carries `X₀` to a
  candidate (`halign`), the answer is correct for `G` on `W`, at the cost of the children plus
  `alignCost` with the branch work, and the children are `|Ys|` copies of `ch₀`:
  `StepChild |W| m` children whose windows sum to at most `|Ys| · F · |W|`. The hypotheses are
  Align's and `rd_branch`'s, the latter for `K = g1Model …`.
* **Corollaries.** `RunsWithin.alignRd_general` (`F = m!`); `RunsWithin.alignRd_part_ns` (the
  stabilizer of `X₀` preserves a colored `t`-partition with `4t ≤ 3m`: no stuck orbit, factor
  `m`); `RunsWithin.alignRd_cj_ns` (it preserves a coloured Johnson structure: no stuck orbit,
  factor `max m uB!`). The preservation is stated for permutations of the base fixing
  `S.dec X₀` (`hpS`, `hcjS`), and transferred to `K` by its denotation (`ar_K_fix`,
  `ar_g1_facts`).
* Well-formedness: `wf_alignRdProg`.
-/

@[expose] public section

namespace GraphIso.Main

open Equiv Cost GraphIso GraphIso.Programs GraphIso.Toolkit GraphIso.Recursion
  GraphIso.SplitJohnson GraphIso.Solver GraphIso.Align

/-! ### Valid representatives, and the most expensive branch -/

section Reps

/-- **The valid representatives of degree `N` are finitely many**: every valid datum is
`ofPerm` of its denotation. -/
theorem exists_allPermsD (N : ℕ) :
    ∃ l : List PermData, (∀ t ∈ l, t.Valid N) ∧ ∀ t : PermData, t.Valid N → t ∈ l := by
  refine ⟨(Finset.univ : Finset (Perm (Fin N))).toList.map PermData.ofPerm, fun t ht => ?_,
    fun t ht => ?_⟩
  · obtain ⟨π, -, rfl⟩ := List.mem_map.1 ht
    exact PermData.valid_ofPerm π
  · rw [PermData.eq_ofPerm_denote ht]
    exact List.mem_map.2 ⟨PermData.denote N t, Finset.mem_toList.2 (Finset.mem_univ _), rfl⟩

/-- Align's cost is affine in the cost of one candidate. -/
theorem alignCost_add (n N g k r cG cI BgP Bmem Bk Bl Bg1 Bgen A Cb s : ℕ) :
    alignCost n N g k r cG cI BgP Bmem Bk Bl Bg1 Bgen (A + Cb) s =
      alignCost n N g k r cG cI BgP Bmem Bk Bl Bg1 Bgen Cb s + r * A := by
  simp only [alignCost, alignCallCost]
  ring

end Reps

section Spec

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}
  {sub : HInstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)}
  {C : ℕ → Option ℕ → ℕ} {s : ℕ} {xy : StrData × StrData} {w : WinData}
  {N : ℕ} {gs : GensData} {d : D.denote} {n₀ n : ℕ} {L : LabelData} {st : ℕ × CJData}
  {sIn Lg F Blift Bgen Bo Bk Bcr Bd W6 : ℕ} {gsK : GensData} {dK : D.denote}

/-- **The most expensive branch.** For a coset group `K = (N, gsK, dK)` meeting `rd_branch`'s
hypotheses, one children list `ch₀` bounds the branch of every valid representative. -/
theorem ar_branch_max (hO : MeetsContractOn DV rdOps X.O)
    (hPre : ∀ op x, rdOps op → GroupPre DV op x → X.Pre op x)
    (hI : HInstValid DV (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D))
    (hsub : HSubSolves X body DV sub
      (fun J => SizeChild sIn (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D)
        J ∧ StepChild w.1.length (N - n) (J.winSize, J.baseOpt)) C s)
    (hB : RDBounds X DV n N sIn Lg Blift Bgen Bo Bk Bcr) (hs : s ≤ sIn)
    (hLg : F * (sIn + 1) ≤ Lg) (hF1 : 1 ≤ F) (hFm : N - n ≤ F)
    (hKv : GroupValid DV N gsK dK) (hKG : GensData.denote N gsK ≤ GensData.denote N gs)
    (hKs : gsK.length ≤ sIn)
    (hD : ∀ gs' d' O', RDSet DV n N gs w L gsK sIn gs' d' O' →
      RDOrbit X body DV n N w L st sIn Bd gs' d' O')
    (h5 : (N - n).factorial ≤ F ∨ ∀ gs' d' O', RDSet DV n N gs w L gsK sIn gs' d' O' →
      (deriveModel X.O n N (N, gs', d') O' L st).1 = 5 →
        (deriveModel X.O n N (N, gs', d') O' L st).2.1.2.2.length ≤ F)
    (h6 : (∀ gs' d' O', RDSet DV n N gs w L gsK sIn gs' d' O' →
        (deriveModel X.O n N (N, gs', d') O' L st).1 ≠ 6) ∨
      ((N - n).factorial ≤ F ∧ rd6Cost N n w.1.length s sIn Bk Bo Bcr Bgen ≤ W6)) :
    ∃ ch₀ : List (ℕ × Option ℕ),
      ((ch₀.map Prod.fst).sum ≤ F * w.1.length ∧ (∀ x ∈ ch₀, StepChild w.1.length (N - n) x) ∧
        ∀ x ∈ ch₀, 1 ≤ x.1) ∧
      ∀ t : PermData, t.Valid N → ∃ ans : AnswerData D,
        RunsWithin X body (Main.rdBranch sub n₀ n L st (xy, (w, (t, (N, gsK, dK))))) ans
          ((ch₀.map fun x => C x.1 x.2).sum +
            (w.1.length * rdOrbitWork N n w.1.length s sIn F Bd Blift Bgen Bo W6 +
              dynSeqCost N w.1.length Bo + 5)) ∧
        AnsOK DV N (ptsSet N w.1) (PermData.denote N t) (GensData.denote N gsK)
          (xy.1.denote N) (xy.2.denote N) ans ∧
        ∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sIn := by
  set Wb := w.1.length * rdOrbitWork N n w.1.length s sIn F Bd Blift Bgen Bo W6 +
    dynSeqCost N w.1.length Bo + 5 with hWb
  set Pb : PermData → List (ℕ × Option ℕ) → Prop := fun t ch =>
    (∃ ans : AnswerData D,
      RunsWithin X body (Main.rdBranch sub n₀ n L st (xy, (w, (t, (N, gsK, dK))))) ans
        ((ch.map fun x => C x.1 x.2).sum + Wb) ∧
      AnsOK DV N (ptsSet N w.1) (PermData.denote N t) (GensData.denote N gsK)
        (xy.1.denote N) (xy.2.denote N) ans ∧
      ∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sIn) ∧
    (ch.map Prod.fst).sum ≤ F * w.1.length ∧ (∀ x ∈ ch, StepChild w.1.length (N - n) x) ∧
      ∀ x ∈ ch, 1 ≤ x.1 with hPb
  obtain ⟨l, hlv, hlm⟩ := exists_allPermsD N
  have hbr : ∀ t ∈ l, ∃ ch, Pb t ch := by
    intro t ht
    obtain ⟨ans, ch, hrun, hok, hg, hsum, hch⟩ := rd_branch (σd := PermData.one N) (dG := d) hO
      hPre hI hsub hB hs hLg hF1 hFm hKv hKG hKs hD h5 h6 (hlv t ht)
    exact ⟨ch, ⟨ans, hrun, hok, hg⟩, hsum, hch⟩
  obtain ⟨ch₀, hch₀, hmax⟩ := ml_exists_max (fun ch : List (ℕ × Option ℕ) =>
    (ch.map fun x => C x.1 x.2).sum) [] Pb l hbr
  have hgood : (ch₀.map Prod.fst).sum ≤ F * w.1.length ∧
      (∀ x ∈ ch₀, StepChild w.1.length (N - n) x) ∧ ∀ x ∈ ch₀, 1 ≤ x.1 := by
    rcases hch₀ with rfl | ⟨r, -, h⟩
    · simp
    · exact h.2
  refine ⟨ch₀, hgood, fun t ht => ?_⟩
  obtain ⟨ch, ⟨⟨ans, hrun, hok, hg⟩, -⟩, hle⟩ := hmax t (hlm t ht)
  refine ⟨ans, hrun.mono ?_, hok, hg⟩
  omega

/-- **The aligned group's elements fix the structure**: by the denotation of `G₁` from
`c2_g1_spec`, every element of `K` acts on the base by a permutation fixing `S.dec X₀`. -/
theorem ar_K_fix {τ O : Type} [MulAction (Perm (Fin (N - n))) O]
    (hG : IsInvariant (GensData.denote N gs) (baseSet n N)) {S : StructOps (N - n) τ O}
    {X₀ : τ} (hKden : GensData.denote N gsK =
      ((MulAction.stabilizer (Perm (Fin (N - n))) (S.dec X₀)).comap
        (baseHom _ n hG)).map (GensData.denote N gs).subtype)
    (hKb : IsInvariant (GensData.denote N gsK) (baseSet n N)) (g : ↥(GensData.denote N gsK)) :
    baseHom (GensData.denote N gsK) n hKb g • S.dec X₀ = S.dec X₀ := by
  obtain ⟨π, hπ⟩ := g
  have hπ' := hπ
  rw [hKden] at hπ'
  obtain ⟨⟨π', hπ'G⟩, hmem, rfl⟩ := Subgroup.mem_map.1 hπ'
  have hKG : GensData.denote N gsK ≤ GensData.denote N gs := by
    rw [hKden]
    exact Subgroup.map_subtype_le _
  rw [dv_baseHom_le hKG hG hKb hπ]
  exact hmem

end Spec

/-! ### Align with reduce-and-derive -/

section Main

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}
  {sub : HInstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)}
  {C : ℕ → Option ℕ → ℕ} {s : ℕ} {xy : StrData × StrData} {w : WinData}
  {N : ℕ} {gs : GensData} {d : D.denote} {n₀ n : ℕ} {L : LabelData} {st : ℕ × CJData}
  {sIn Lg F Blift Bgen Bo Bk Bcr Bd W6 : ℕ}

/-- **Align with reduce-and-derive.** The hinted parent `(1 • G, W, L)` has a base action
containing `Alt`; `X₀` is the structure for `x`, `Ys` the candidates for `y`, and every
isomorphism carries `X₀` to a candidate (`halign`). Each aligned coset `t • K`,
`K = ψ⁻¹(Stab(X₀))` (`g1Model`), is solved by `rdBranch` with the structure `st` (`hD`, `h5`,
`h6` for `K`). The answer is correct for `G` on `W`; the children are `StepChild |W| m`, with
windows summing to at most `|Ys| · F · |W|`. -/
theorem RunsWithin.alignRd {τ : Ty} {O : Type} [MulAction (Perm (Fin (N - n))) O]
    (hOa : MeetsContractOn DV alignOps X.O)
    (hPa : ∀ op x, alignOps op → GroupPre DV op x → X.Pre op x)
    (hO : MeetsContractOn DV rdOps X.O)
    (hPre : ∀ op x, rdOps op → GroupPre DV op x → X.Pre op x)
    (hI : HInstValid DV (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D))
    (hG : IsInvariant (GensData.denote N gs) (baseSet n N))
    (halt : alternatingGroup (Fin (N - n)) ≤ (baseHom _ n hG).range)
    {s₀ : ℕ} {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N s₀ G₀)
    (hGG₀ : GensData.denote N gs ≤ G₀) (hs₀ : s₀ ≤ sIn)
    {S : StructOps (N - n) τ.denote O} {Valid : τ.denote → Prop} (hS : S.Spec Valid)
    {gensP : τ.denote → Prog (groupSig D) (a, b) Ty.denote Ty.gens} {cG : ℕ}
    (hgensP : ∀ x, Valid x → RunsWithin X body (gensP x) (S.gens x) cG)
    {isoP : τ.denote → τ.denote → Prog (groupSig D) (a, b) Ty.denote (.option Ty.perm)}
    {cI : ℕ} (hisoP : ∀ x y, Valid x → Valid y → RunsWithin X body (isoP x y) (S.iso x y) cI)
    {X₀ : τ.denote} {Ys : List τ.denote} (hX : Valid X₀) (hYs : ∀ Y ∈ Ys, Valid Y)
    (halign : ∀ g ∈ iso (w.denote N) 1 (GensData.denote N gs) (xy.1.denote N) (xy.2.denote N),
      ∃ Y ∈ Ys, ∃ h : g ∈ GensData.denote N gs, baseHom _ n hG ⟨g, h⟩ • S.dec X₀ = S.dec Y)
    {BgP Bmem BkA BlA Bg1 : ℕ}
    (hBgP : X.B.call GroupOp.generate (N - n, gs.map (baseD n N))
      (X.O.run GroupOp.generate (N - n, gs.map (baseD n N))) ≤ BgP)
    (hBmem : ∀ g : PermData, g.Valid (N - n) → X.B.call GroupOp.mem (pModel X.O n (N, gs, d), g)
      (X.O.run GroupOp.mem (pModel X.O n (N, gs, d), g)) ≤ Bmem)
    (hBkA : X.B.call GroupOp.kernel ((N, gs, d), baseWin n N) (kerModel X.O n (N, gs, d)) ≤ BkA)
    (hBlA : ∀ π : PermData, X.B.call GroupOp.lift ((N, gs, d), (baseWin n N, π))
      (liftModel X.O n (N, gs, d) π) ≤ BlA)
    (hBg1 : X.B.call GroupOp.generate
      (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d)) (S.gens X₀))).map
        (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
      (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
        (S.gens X₀)))) ≤ Bg1)
    (hsub : HSubSolves X body DV sub
      (fun J => SizeChild sIn (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D)
        J ∧ StepChild w.1.length (N - n) (J.winSize, J.baseOpt)) C s)
    (hB : RDBounds X DV n N sIn Lg Blift Bgen Bo Bk Bcr) (hs : s ≤ sIn)
    (hLg : F * (sIn + 1) ≤ Lg) (hF1 : 1 ≤ F) (hFm : N - n ≤ F)
    (hLY : Ys.length * (sIn + 1) ≤ Lg)
    (hD : ∀ gs' d' O', RDSet DV n N gs w L (Giant.g1Model X.O n (N, gs, d) S X₀).2.1 sIn gs' d' O' →
      RDOrbit X body DV n N w L st sIn Bd gs' d' O')
    (h5 : (N - n).factorial ≤ F ∨ ∀ gs' d' O',
      RDSet DV n N gs w L (Giant.g1Model X.O n (N, gs, d) S X₀).2.1 sIn gs' d' O' →
      (deriveModel X.O n N (N, gs', d') O' L st).1 = 5 →
        (deriveModel X.O n N (N, gs', d') O' L st).2.1.2.2.length ≤ F)
    (h6 : (∀ gs' d' O',
        RDSet DV n N gs w L (Giant.g1Model X.O n (N, gs, d) S X₀).2.1 sIn gs' d' O' →
        (deriveModel X.O n N (N, gs', d') O' L st).1 ≠ 6) ∨
      ((N - n).factorial ≤ F ∧ rd6Cost N n w.1.length s sIn Bk Bo Bcr Bgen ≤ W6)) :
    ∃ (ans : AnswerData D) (ch : List (ℕ × Option ℕ)),
      RunsWithin X body
        (Align.alignProg (Main.rdBranch sub n₀ n L st) gensP isoP n xy w (N, gs, d) X₀ Ys) ans
        ((ch.map fun x => C x.1 x.2).sum +
          alignCost n N gs.length (S.gens X₀).length Ys.length cG cI BgP Bmem BkA BlA Bg1 Bgen
            (w.1.length * rdOrbitWork N n w.1.length s sIn F Bd Blift Bgen Bo W6 +
              dynSeqCost N w.1.length Bo + 5) sIn) ∧
      AnsOK DV N (w.denote N) 1 (GensData.denote N gs) (xy.1.denote N) (xy.2.denote N) ans ∧
      (∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sIn) ∧
      ChildList w.1.length (Ys.length * F) (StepChild w.1.length (N - n)) ch := by
  have hGv : GroupValid DV N gs d := hI.valid.group
  have hw : w.Valid N := hI.valid.win
  have hWG : IsInvariant (GensData.denote N gs) (w.denote N) := hI.valid.invariant
  -- the aligned group
  obtain ⟨hdeg, hKv, hKden, hKs₀⟩ := Giant.c2_g1_spec hOa hPa B hGv hGG₀ hG
    halt hS hX hBlA
  have hKm' : preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
      (S.gens X₀))) = Giant.g1Model X.O n (N, gs, d) S X₀ := rfl
  rcases hKm : Giant.g1Model X.O n (N, gs, d) S X₀ with ⟨N', gsK, dK⟩
  rw [hKm] at hdeg hKv hKden hKs₀ hD h5 h6 hKm'
  change N' = N at hdeg
  subst hdeg
  have hKG : GensData.denote N' gsK ≤ GensData.denote N' gs := by
    rw [hKden]
    exact Subgroup.map_subtype_le _
  -- the most expensive branch
  obtain ⟨ch₀, hgood, hbr⟩ := ar_branch_max (C := C) (Bk := Bk) (Bcr := Bcr) (W6 := W6) hO hPre
    hI hsub hB hs hLg hF1 hFm hKv hKG (hKs₀.trans hs₀) hD h5 h6
  set Wb := w.1.length * rdOrbitWork N' n w.1.length s sIn F Bd Blift Bgen Bo W6 +
    dynSeqCost N' w.1.length Bo + 5 with hWb
  set Cb := (ch₀.map fun x => C x.1 x.2).sum + Wb with hCb
  have hsubA : SubSolves X body DV
      (Main.rdBranch (var := Ty.denote) (rec := (a, b)) (D := D) sub n₀ n L st)
      (fun I => I.1 = xy ∧ I.2.1 = w ∧
        I.2.2.2 = preModel X.O n (N', gs, d)
          (stabInPL (flagsModel X.O (pModel X.O n (N', gs, d)) (S.gens X₀))) ∧ I.Valid DV)
      (fun _ => Cb) sIn := by
    rintro ⟨xy', w', t, G'⟩ ⟨h1, h2, h3, hv⟩
    change xy' = xy at h1
    change w' = w at h2
    change G' = _ at h3
    rw [hKm'] at h3
    subst h1 h2 h3
    have ht : t.Valid N' := hv.rep
    obtain ⟨ans, hrun, hok, hg⟩ := hbr t ht
    exact ⟨ans, hrun, hok, hg⟩
  obtain ⟨ans, hrun, hok, hg⟩ := Align.RunsWithin.alignProg (body := body) (Cb := Cb) hOa hPa hGv
    hG halt hS hgensP hisoP hX hYs hw hWG halign hBgP hBmem hBkA hBlA hBg1
    (fun gs' hv hl _ => hB.gen N' le_rfl gs' hv (hl.trans hLY)) hsubA
  refine ⟨ans, (List.replicate Ys.length ch₀).flatten, ?_, hok,
    hg sIn (fun hs' hv _ => hB.genOut N' le_rfl hs' hv), ?_, ?_, ?_⟩
  · refine hrun.mono ?_
    rw [ml_sum_replicate, hCb, alignCost_add]
    omega
  · rw [ml_sum_replicate]
    have := Nat.mul_le_mul_left Ys.length hgood.1
    rw [Nat.mul_assoc]
    exact this
  · intro x hx
    obtain ⟨l, hl, hxl⟩ := List.mem_flatten.1 hx
    rw [List.eq_of_mem_replicate hl] at hxl
    exact hgood.2.1 x hxl
  · intro x hx
    obtain ⟨l, hl, hxl⟩ := List.mem_flatten.1 hx
    rw [List.eq_of_mem_replicate hl] at hxl
    exact hgood.2.2 x hxl

/-- **Align with reduce-and-derive, general factor**: `F = m!`, no hypothesis on the tags. -/
theorem RunsWithin.alignRd_general {τ : Ty} {O : Type} [MulAction (Perm (Fin (N - n))) O]
    (hOa : MeetsContractOn DV alignOps X.O)
    (hPa : ∀ op x, alignOps op → GroupPre DV op x → X.Pre op x)
    (hO : MeetsContractOn DV rdOps X.O)
    (hPre : ∀ op x, rdOps op → GroupPre DV op x → X.Pre op x)
    (hI : HInstValid DV (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D))
    (hG : IsInvariant (GensData.denote N gs) (baseSet n N))
    (halt : alternatingGroup (Fin (N - n)) ≤ (baseHom _ n hG).range)
    {s₀ : ℕ} {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N s₀ G₀)
    (hGG₀ : GensData.denote N gs ≤ G₀) (hs₀ : s₀ ≤ sIn)
    {S : StructOps (N - n) τ.denote O} {Valid : τ.denote → Prop} (hS : S.Spec Valid)
    {gensP : τ.denote → Prog (groupSig D) (a, b) Ty.denote Ty.gens} {cG : ℕ}
    (hgensP : ∀ x, Valid x → RunsWithin X body (gensP x) (S.gens x) cG)
    {isoP : τ.denote → τ.denote → Prog (groupSig D) (a, b) Ty.denote (.option Ty.perm)}
    {cI : ℕ} (hisoP : ∀ x y, Valid x → Valid y → RunsWithin X body (isoP x y) (S.iso x y) cI)
    {X₀ : τ.denote} {Ys : List τ.denote} (hX : Valid X₀) (hYs : ∀ Y ∈ Ys, Valid Y)
    (halign : ∀ g ∈ iso (w.denote N) 1 (GensData.denote N gs) (xy.1.denote N) (xy.2.denote N),
      ∃ Y ∈ Ys, ∃ h : g ∈ GensData.denote N gs, baseHom _ n hG ⟨g, h⟩ • S.dec X₀ = S.dec Y)
    {BgP Bmem BkA BlA Bg1 : ℕ}
    (hBgP : X.B.call GroupOp.generate (N - n, gs.map (baseD n N))
      (X.O.run GroupOp.generate (N - n, gs.map (baseD n N))) ≤ BgP)
    (hBmem : ∀ g : PermData, g.Valid (N - n) → X.B.call GroupOp.mem (pModel X.O n (N, gs, d), g)
      (X.O.run GroupOp.mem (pModel X.O n (N, gs, d), g)) ≤ Bmem)
    (hBkA : X.B.call GroupOp.kernel ((N, gs, d), baseWin n N) (kerModel X.O n (N, gs, d)) ≤ BkA)
    (hBlA : ∀ π : PermData, X.B.call GroupOp.lift ((N, gs, d), (baseWin n N, π))
      (liftModel X.O n (N, gs, d) π) ≤ BlA)
    (hBg1 : X.B.call GroupOp.generate
      (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d)) (S.gens X₀))).map
        (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
      (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
        (S.gens X₀)))) ≤ Bg1)
    (hsub : HSubSolves X body DV sub
      (fun J => SizeChild sIn (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D)
        J ∧ StepChild w.1.length (N - n) (J.winSize, J.baseOpt)) C s)
    (hB : RDBounds X DV n N sIn Lg Blift Bgen Bo Bk Bcr) (hs : s ≤ sIn)
    (hLY : Ys.length * (sIn + 1) ≤ Lg)
    (hD : ∀ gs' d' O', RDSet DV n N gs w L (Giant.g1Model X.O n (N, gs, d) S X₀).2.1 sIn gs' d' O' →
      RDOrbit X body DV n N w L st sIn Bd gs' d' O')
    (hLg : (N - n).factorial * (sIn + 1) ≤ Lg) :
    ∃ (ans : AnswerData D) (ch : List (ℕ × Option ℕ)),
      RunsWithin X body
        (Align.alignProg (Main.rdBranch sub n₀ n L st) gensP isoP n xy w (N, gs, d) X₀ Ys) ans
        ((ch.map fun x => C x.1 x.2).sum +
          alignCost n N gs.length (S.gens X₀).length Ys.length cG cI BgP Bmem BkA BlA Bg1 Bgen
            (w.1.length * rdOrbitWork N n w.1.length s sIn (N - n).factorial Bd Blift Bgen Bo
              (rd6Cost N n w.1.length s sIn Bk Bo Bcr Bgen) + dynSeqCost N w.1.length Bo + 5) sIn) ∧
      AnsOK DV N (w.denote N) 1 (GensData.denote N gs) (xy.1.denote N) (xy.2.denote N) ans ∧
      (∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sIn) ∧
      ChildList w.1.length (Ys.length * (N - n).factorial) (StepChild w.1.length (N - n)) ch :=
  RunsWithin.alignRd hOa hPa hO hPre hI hG halt B hGG₀ hs₀ hS hgensP hisoP hX hYs halign hBgP
    hBmem hBkA hBlA hBg1 hsub hB hs hLg (Nat.factorial_pos _) (Nat.self_le_factorial _) hLY hD
    (Or.inl le_rfl) (Or.inr ⟨le_rfl, le_rfl⟩)

/-- **The aligned group of a structure**: degree, validity, denotation, `K ≤ G` and base
invariance, from `c2_g1_spec`. -/
theorem ar_g1_facts {τ O : Type} [MulAction (Perm (Fin (N - n))) O]
    (hOa : MeetsContractOn DV alignOps X.O)
    (hPa : ∀ op x, alignOps op → GroupPre DV op x → X.Pre op x)
    {s₀ : ℕ} {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N s₀ G₀)
    (hGv : GroupValid DV N gs d) (hGG₀ : GensData.denote N gs ≤ G₀)
    (hG : IsInvariant (GensData.denote N gs) (baseSet n N))
    (halt : alternatingGroup (Fin (N - n)) ≤ (baseHom _ n hG).range)
    {S : StructOps (N - n) τ O} {Valid : τ → Prop} (hS : S.Spec Valid) {X₀ : τ} (hX : Valid X₀)
    {BlA : ℕ} (hBlA : ∀ π : PermData, X.B.call GroupOp.lift ((N, gs, d), (baseWin n N, π))
      (liftModel X.O n (N, gs, d) π) ≤ BlA) :
    GensData.denote N (Giant.g1Model X.O n (N, gs, d) S X₀).2.1 =
        ((MulAction.stabilizer (Perm (Fin (N - n))) (S.dec X₀)).comap
          (baseHom _ n hG)).map (GensData.denote N gs).subtype ∧
      ∃ hKb : IsInvariant (GensData.denote N (Giant.g1Model X.O n (N, gs, d) S X₀).2.1)
        (baseSet n N), ∀ g : ↥(GensData.denote N (Giant.g1Model X.O n (N, gs, d) S X₀).2.1),
          baseHom _ n hKb g • S.dec X₀ = S.dec X₀ := by
  obtain ⟨-, -, hKden, -⟩ := Giant.c2_g1_spec hOa hPa B hGv hGG₀ hG halt hS hX hBlA
  have hKG : GensData.denote N (Giant.g1Model X.O n (N, gs, d) S X₀).2.1 ≤
      GensData.denote N gs := by
    rw [hKden]
    exact Subgroup.map_subtype_le _
  have hKb : IsInvariant (GensData.denote N (Giant.g1Model X.O n (N, gs, d) S X₀).2.1)
      (baseSet n N) := fun g hg => hG g (hKG hg)
  exact ⟨hKden, hKb, ar_K_fix hG hKden hKb⟩

/-- **Align with reduce-and-derive, a preserved colored partition**: if every permutation of
the base fixing `S.dec X₀` preserves a colored `t`-partition `p` with `4t ≤ 3m` (`hpS`; for
`partOps`, `p` is the aligned structure itself), no orbit is stuck (`rd_ns_part`) and the
factor is `m`. -/
theorem RunsWithin.alignRd_part_ns {τ : Ty} {O : Type} [MulAction (Perm (Fin (N - n))) O]
    (hOa : MeetsContractOn DV alignOps X.O)
    (hPa : ∀ op x, alignOps op → GroupPre DV op x → X.Pre op x)
    (hO : MeetsContractOn DV rdOps X.O)
    (hPre : ∀ op x, rdOps op → GroupPre DV op x → X.Pre op x)
    (hI : HInstValid DV (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D))
    (hG : IsInvariant (GensData.denote N gs) (baseSet n N))
    (halt : alternatingGroup (Fin (N - n)) ≤ (baseHom _ n hG).range)
    {s₀ : ℕ} {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N s₀ G₀)
    (hGG₀ : GensData.denote N gs ≤ G₀) (hs₀ : s₀ ≤ sIn)
    {S : StructOps (N - n) τ.denote O} {Valid : τ.denote → Prop} (hS : S.Spec Valid)
    {gensP : τ.denote → Prog (groupSig D) (a, b) Ty.denote Ty.gens} {cG : ℕ}
    (hgensP : ∀ x, Valid x → RunsWithin X body (gensP x) (S.gens x) cG)
    {isoP : τ.denote → τ.denote → Prog (groupSig D) (a, b) Ty.denote (.option Ty.perm)}
    {cI : ℕ} (hisoP : ∀ x y, Valid x → Valid y → RunsWithin X body (isoP x y) (S.iso x y) cI)
    {X₀ : τ.denote} {Ys : List τ.denote} (hX : Valid X₀) (hYs : ∀ Y ∈ Ys, Valid Y)
    (halign : ∀ g ∈ iso (w.denote N) 1 (GensData.denote N gs) (xy.1.denote N) (xy.2.denote N),
      ∃ Y ∈ Ys, ∃ h : g ∈ GensData.denote N gs, baseHom _ n hG ⟨g, h⟩ • S.dec X₀ = S.dec Y)
    {BgP Bmem BkA BlA Bg1 : ℕ}
    (hBgP : X.B.call GroupOp.generate (N - n, gs.map (baseD n N))
      (X.O.run GroupOp.generate (N - n, gs.map (baseD n N))) ≤ BgP)
    (hBmem : ∀ g : PermData, g.Valid (N - n) → X.B.call GroupOp.mem (pModel X.O n (N, gs, d), g)
      (X.O.run GroupOp.mem (pModel X.O n (N, gs, d), g)) ≤ Bmem)
    (hBkA : X.B.call GroupOp.kernel ((N, gs, d), baseWin n N) (kerModel X.O n (N, gs, d)) ≤ BkA)
    (hBlA : ∀ π : PermData, X.B.call GroupOp.lift ((N, gs, d), (baseWin n N, π))
      (liftModel X.O n (N, gs, d) π) ≤ BlA)
    (hBg1 : X.B.call GroupOp.generate
      (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d)) (S.gens X₀))).map
        (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
      (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
        (S.gens X₀)))) ≤ Bg1)
    (hsub : HSubSolves X body DV sub
      (fun J => SizeChild sIn (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D)
        J ∧ StepChild w.1.length (N - n) (J.winSize, J.baseOpt)) C s)
    (hB : RDBounds X DV n N sIn Lg Blift Bgen Bo Bk Bcr) (hs : s ≤ sIn)
    (hLY : Ys.length * (sIn + 1) ≤ Lg)
    (hD : ∀ gs' d' O', RDSet DV n N gs w L (Giant.g1Model X.O n (N, gs, d) S X₀).2.1 sIn gs' d' O' →
      RDOrbit X body DV n N w L st sIn Bd gs' d' O')
    (hLg : (N - n) * (sIn + 1) ≤ Lg) (hst : st.1 ≠ 2) {p : CPart (Fin (N - n))} {t : ℕ}
    (hp : IsColPart Finset.univ t p)
    (hpS : ∀ π : Perm (Fin (N - n)), π • S.dec X₀ = S.dec X₀ → π • p = p)
    (ht : 4 * t ≤ 3 * (N - n)) (hm : 2 ≤ N - n) :
    ∃ (ans : AnswerData D) (ch : List (ℕ × Option ℕ)),
      RunsWithin X body
        (Align.alignProg (Main.rdBranch sub n₀ n L st) gensP isoP n xy w (N, gs, d) X₀ Ys) ans
        ((ch.map fun x => C x.1 x.2).sum +
          alignCost n N gs.length (S.gens X₀).length Ys.length cG cI BgP Bmem BkA BlA Bg1 Bgen
            (w.1.length * rdOrbitWork N n w.1.length s sIn (N - n) Bd Blift Bgen Bo
              0 + dynSeqCost N w.1.length Bo + 5) sIn) ∧
      AnsOK DV N (w.denote N) 1 (GensData.denote N gs) (xy.1.denote N) (xy.2.denote N) ans ∧
      (∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sIn) ∧
      ChildList w.1.length (Ys.length * (N - n)) (StepChild w.1.length (N - n)) ch := by
  have hO' : MeetsContractOn DV deriveOps X.O := fun op x h hx => hO op x (by
    rcases h with h | h | h | h <;> simp [rdOps, h]) hx
  obtain ⟨-, hKb, hfix⟩ := ar_g1_facts hOa hPa B hI.valid.group hGG₀ hG halt hS hX hBlA
  exact RunsWithin.alignRd hOa hPa hO hPre hI hG halt B hGG₀ hs₀ hS hgensP hisoP hX hYs halign
    hBgP hBmem hBkA hBlA hBg1 hsub hB hs hLg (by omega) le_rfl hLY hD
    (Or.inr fun gs' d' O' _ h5 => absurd h5 (rd_free_ne5 hst))
    (Or.inl (rd_ns_part hO' hst hKb hp (fun g => hpS _ (hfix g)) ht hm))

/-- **Align with reduce-and-derive, a preserved coloured Johnson structure**: if every
permutation of the base fixing `S.dec X₀` preserves the coloured Johnson structure `st.2`
(`hcjS`; for `cjohnOps`, `st.2` is the aligned structure itself), no orbit is stuck
(`rd_ns_cj`), and the factor is `max m uB!`, where `uB` bounds the union cells at the first
point of every orbit that can occur (`rd_cj_reps5`). -/
theorem RunsWithin.alignRd_cj_ns {τ : Ty} {O : Type} [MulAction (Perm (Fin (N - n))) O]
    (hOa : MeetsContractOn DV alignOps X.O)
    (hPa : ∀ op x, alignOps op → GroupPre DV op x → X.Pre op x)
    (hO : MeetsContractOn DV rdOps X.O)
    (hPre : ∀ op x, rdOps op → GroupPre DV op x → X.Pre op x)
    (hI : HInstValid DV (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D))
    (hG : IsInvariant (GensData.denote N gs) (baseSet n N))
    (halt : alternatingGroup (Fin (N - n)) ≤ (baseHom _ n hG).range)
    {s₀ : ℕ} {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N s₀ G₀)
    (hGG₀ : GensData.denote N gs ≤ G₀) (hs₀ : s₀ ≤ sIn)
    {S : StructOps (N - n) τ.denote O} {Valid : τ.denote → Prop} (hS : S.Spec Valid)
    {gensP : τ.denote → Prog (groupSig D) (a, b) Ty.denote Ty.gens} {cG : ℕ}
    (hgensP : ∀ x, Valid x → RunsWithin X body (gensP x) (S.gens x) cG)
    {isoP : τ.denote → τ.denote → Prog (groupSig D) (a, b) Ty.denote (.option Ty.perm)}
    {cI : ℕ} (hisoP : ∀ x y, Valid x → Valid y → RunsWithin X body (isoP x y) (S.iso x y) cI)
    {X₀ : τ.denote} {Ys : List τ.denote} (hX : Valid X₀) (hYs : ∀ Y ∈ Ys, Valid Y)
    (halign : ∀ g ∈ iso (w.denote N) 1 (GensData.denote N gs) (xy.1.denote N) (xy.2.denote N),
      ∃ Y ∈ Ys, ∃ h : g ∈ GensData.denote N gs, baseHom _ n hG ⟨g, h⟩ • S.dec X₀ = S.dec Y)
    {BgP Bmem BkA BlA Bg1 : ℕ}
    (hBgP : X.B.call GroupOp.generate (N - n, gs.map (baseD n N))
      (X.O.run GroupOp.generate (N - n, gs.map (baseD n N))) ≤ BgP)
    (hBmem : ∀ g : PermData, g.Valid (N - n) → X.B.call GroupOp.mem (pModel X.O n (N, gs, d), g)
      (X.O.run GroupOp.mem (pModel X.O n (N, gs, d), g)) ≤ Bmem)
    (hBkA : X.B.call GroupOp.kernel ((N, gs, d), baseWin n N) (kerModel X.O n (N, gs, d)) ≤ BkA)
    (hBlA : ∀ π : PermData, X.B.call GroupOp.lift ((N, gs, d), (baseWin n N, π))
      (liftModel X.O n (N, gs, d) π) ≤ BlA)
    (hBg1 : X.B.call GroupOp.generate
      (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d)) (S.gens X₀))).map
        (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
      (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
        (S.gens X₀)))) ≤ Bg1)
    (hsub : HSubSolves X body DV sub
      (fun J => SizeChild sIn (((xy, w, PermData.one N, N, gs, d), n₀, n, some L) : HInstData D)
        J ∧ StepChild w.1.length (N - n) (J.winSize, J.baseOpt)) C s)
    (hB : RDBounds X DV n N sIn Lg Blift Bgen Bo Bk Bcr) (hs : s ≤ sIn)
    (hLY : Ys.length * (sIn + 1) ≤ Lg)
    (hD : ∀ gs' d' O', RDSet DV n N gs w L (Giant.g1Model X.O n (N, gs, d) S X₀).2.1 sIn gs' d' O' →
      RDOrbit X body DV n N w L st sIn Bd gs' d' O')
    {uB : ℕ} (hLg : max (N - n) uB.factorial * (sIn + 1) ≤ Lg) (hst : st.1 = 2)
    (hJv : Align.JValid (N - n) st.2.1) {t : ℕ}
    (hJ : IsJohnson Finset.univ t (Align.jdec (N - n) st.2.1))
    (hcjS : ∀ π : Perm (Fin (N - n)), π • S.dec X₀ = S.dec X₀ →
      π • cjdec (N - n) st.2 = cjdec (N - n) st.2)
    (hq : ∀ c, 2 * (Finset.univ.filter fun γ =>
      γ ∉ (Align.jdec (N - n) st.2.1).V0 ∧ cjcol (N - n) st.2 γ = c).card ≤ N - n)
    (hm : 5 ≤ N - n)
    (hu : ∀ gs' d' O',
      RDSet DV n N gs w L (Giant.g1Model X.O n (N, gs, d) S X₀).2.1 sIn gs' d' O' →
      ((labJUD st.2.1.2.1.length (markArr (N - n) st.2.1.1) st.2.1.2.2.2 L O').getD
        (O'.headD 0) []).length ≤ uB) :
    ∃ (ans : AnswerData D) (ch : List (ℕ × Option ℕ)),
      RunsWithin X body
        (Align.alignProg (Main.rdBranch sub n₀ n L st) gensP isoP n xy w (N, gs, d) X₀ Ys) ans
        ((ch.map fun x => C x.1 x.2).sum +
          alignCost n N gs.length (S.gens X₀).length Ys.length cG cI BgP Bmem BkA BlA Bg1 Bgen
            (w.1.length * rdOrbitWork N n w.1.length s sIn (max (N - n) uB.factorial) Bd Blift
              Bgen Bo 0 + dynSeqCost N w.1.length Bo + 5) sIn) ∧
      AnsOK DV N (w.denote N) 1 (GensData.denote N gs) (xy.1.denote N) (xy.2.denote N) ans ∧
      (∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sIn) ∧
      ChildList w.1.length (Ys.length * (max (N - n) uB.factorial))
        (StepChild w.1.length (N - n)) ch := by
  have hO' : MeetsContractOn DV deriveOps X.O := fun op x h hx => hO op x (by
    rcases h with h | h | h | h <;> simp [rdOps, h]) hx
  obtain ⟨-, hKb, hfix⟩ := ar_g1_facts hOa hPa B hI.valid.group hGG₀ hG halt hS hX hBlA
  have hK := fun g => hcjS _ (hfix g)
  refine RunsWithin.alignRd hOa hPa hO hPre hI hG halt B hGG₀ hs₀ hS hgensP hisoP hX hYs halign
    hBgP hBmem hBkA hBlA hBg1 hsub hB hs hLg (le_max_of_le_right (Nat.factorial_pos _))
    (le_max_left _ _) hLY hD (Or.inr fun gs' d' O' hset h5 => ?_)
    (Or.inl (rd_ns_cj hO' hst hKb hJv hJ hK hq hm))
  have huB := hu gs' d' O' hset
  obtain ⟨hS', -, hle⟩ := hset
  have hKj : ∀ g : ↥(GensData.denote N gs'),
      baseHom (GensData.denote N gs') n hS'.base_inv g • Align.jdec (N - n) st.2.1 =
        Align.jdec (N - n) st.2.1 := by
    rintro ⟨π, hπ⟩
    rw [dv_baseHom_le hle hKb hS'.base_inv hπ]
    exact ((cj_smul_eq_iff' _ _ _).1 (hK ⟨π, hle hπ⟩)).1
  exact (rd_cj_reps5 hO' hS' hst hJv hKj h5).trans
    ((Nat.factorial_le huB).trans (le_max_right _ _))

end Main

/-! ### Well-formedness -/

section Wf

variable {D : Ty} {rec : Ty × Ty} {var₁ var₂ : Ty → Type} {r : Bool} {Γ : WfCtx var₁ var₂}

theorem wf_alignRdProg {τ : Ty}
    {sub₁ : var₁ (hinstTy D) → Prog (groupSig D) rec var₁ (Ty.answer D)}
    {sub₂ : var₂ (hinstTy D) → Prog (groupSig D) rec var₂ (Ty.answer D)}
    {gensP₁ : var₁ τ → Prog (groupSig D) rec var₁ Ty.gens}
    {gensP₂ : var₂ τ → Prog (groupSig D) rec var₂ Ty.gens}
    {isoP₁ : var₁ τ → var₁ τ → Prog (groupSig D) rec var₁ (.option Ty.perm)}
    {isoP₂ : var₂ τ → var₂ τ → Prog (groupSig D) rec var₂ (.option Ty.perm)}
    (hsub : WfFun r Γ sub₁ sub₂) (hgens : WfFun r Γ gensP₁ gensP₂)
    (hiso : WfFun2 r Γ isoP₁ isoP₂)
    {n₀₁ n₁ : var₁ .nat} {n₀₂ n₂ : var₂ .nat}
    {L₁ : var₁ (.array (.list .nat))} {L₂ : var₂ (.array (.list .nat))} {st₁ : var₁ stTy}
    {st₂ : var₂ stTy} {xy₁ : var₁ Ty.strs} {xy₂ : var₂ Ty.strs}
    {w₁ : var₁ Ty.win} {w₂ : var₂ Ty.win} {G₁ : var₁ (Ty.group D)} {G₂ : var₂ (Ty.group D)}
    {X₁ : var₁ τ} {X₂ : var₂ τ} {Ys₁ : var₁ (.list τ)} {Ys₂ : var₂ (.list τ)}
    (hn₀ : ⟨.nat, n₀₁, n₀₂⟩ ∈ Γ) (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ)
    (hL : ⟨.array (.list .nat), L₁, L₂⟩ ∈ Γ) (hst : ⟨stTy, st₁, st₂⟩ ∈ Γ)
    (hxy : ⟨Ty.strs, xy₁, xy₂⟩ ∈ Γ) (hw : ⟨Ty.win, w₁, w₂⟩ ∈ Γ)
    (hG : ⟨Ty.group D, G₁, G₂⟩ ∈ Γ) (hX : ⟨τ, X₁, X₂⟩ ∈ Γ) (hYs : ⟨.list τ, Ys₁, Ys₂⟩ ∈ Γ) :
    Prog.Wf r Γ (Align.alignProg (rdBranch sub₁ n₀₁ n₁ L₁ st₁) gensP₁ isoP₁ n₁ xy₁ w₁ G₁ X₁ Ys₁)
      (Align.alignProg (rdBranch sub₂ n₀₂ n₂ L₂ st₂) gensP₂ isoP₂ n₂ xy₂ w₂ G₂ X₂ Ys₂) :=
  Align.wf_alignProg (wf_rdBranch hsub hn₀ hn hL hst) hgens hiso hn hxy hw hG hX hYs

end Wf

end GraphIso.Main
