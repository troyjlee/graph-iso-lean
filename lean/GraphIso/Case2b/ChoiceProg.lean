module

public import GraphIso.Case2b.PipelineProg
public import GraphIso.Toolkit.Reduce

/-!
# Case 2b on data: the programs of one choice and of all choices

Stage 14h, item 3 (`PLAN-14.md` §12), the programs with backend calls. `choiceProg` computes the
leaves of one choice `(S, (a, b))` (`choiceLeavesD`): the pointwise stabilizer of `S`
(`iterStabProg`), its restriction to the positions of `Φ ∖ S` generated at degree `m'`, the
orbital array (`orbitalProg`), the colouring of the orbital of `(a, b)` (`tcolProg`), the 2-ary
Weisfeiler–Leman refinement (`wlProg`), the leaves (`leavesOfProg`) and their extension to the
base (`extProg`). `allLeavesProg` and `firstLeafProg` enumerate the choices (`allLeavesD`,
`firstLeafD`).

* `leavesOfD_decode_comp`, `leavesOfD_decode_soj`: the decoded leaves of a colouring are the
  components leaf of the least disconnected colour, or the trimmed leaves of `soj`.
* `outSize_leavesOfD`, `length_leavesOfD_le`: the leaves have data size at most
  `outB m ((m + 3) / 2)`, and there are at most `sojSz + 1` of them (`sojSz`: the size of the
  `soj` tree when it is built, `0` when a colour is disconnected).
* `RunsWithin.choiceProg`: the program computes `choiceLeavesD` at the explicit cost
  `choiceCost`, with the backend charges bounded by `BackendBounds` at degree `N` (the
  stabilizers) and at degree `m'` (the orbital array), and the charge of the generation at
  degree `m'` as a hypothesis. Its hypotheses: `F` valid with at most `s` generators, the
  positions of `Φ` invariant under `F`, and `Φ ∖ S` nonempty.
* `RunsWithin.allLeavesProg`, `RunsWithin.firstLeafProg`: the enumerations, given a cost bound
  `Cc` for every choice and a bound `Lc` on its number of leaves; at most `|Φ|^j` tuples and
  `m'²` pairs.
-/

@[expose] public section

namespace GraphIso.Case2b

open Equiv GraphIso GraphIso.Cost GraphIso.Programs GraphIso.SplitJohnson GraphIso.SoJProg
  GraphIso.SoJTree GraphIso.Toolkit GraphIso.Sims GraphIso.Solver

/-! ### The leaves of a colouring -/

section Leaves

theorem outSize_trimD_le (m : ℕ) (o : OutD) : outSize (trimD m o) ≤ outSize o := by
  unfold trimD
  split_ifs with h
  · unfold outSize
    simp only [johnD]
    have hfA : ldMaxLen ((List.range m).map fun v =>
        if v ∈ o.2.2.1 then o.2.2.2.2.2.getD v [] else []).toArray.toList ≤ outSize o :=
      ld_maxLen_map_range_le m _ fun x _ => by
        split_ifs
        · exact outSize_fA o x
        · simp
    have h1 := outSize_V0 o
    have h2 := outSize_cs o
    have h3 : ldMaxLen o.2.2.2.1 ≤ outSize o := ld_maxLen_le fun c hc => outSize_cell o hc
    simp only [ldMaxLen, List.map_nil, List.foldr_nil, max_le_iff, Nat.zero_le, true_and]
    exact ⟨h1, h2, h3, hfA⟩
  · exact le_rfl

theorem outSize_compLeafD_le (m : ℕ) (C : Array ℕ) (r : ℕ) :
    outSize (compLeafD m C r) ≤ m * m + 1 := by
  unfold compLeafD outSize
  simp only [partD, compPart, partLeaf]
  have hb : ldMaxLen ((List.range m).map (compD (colFn m C) (List.range m) r)).toArray.toList ≤
      m * m + 1 :=
    ld_maxLen_map_range_le m _ fun x _ => by
      have := length_compD_le (colFn m C) (List.range m) r x
      simpa using this
  simp only [List.length_nil, ldMaxLen, List.map_nil, List.foldr_nil, max_le_iff, Nat.zero_le,
    and_true]
  exact hb

/-- **The leaves of a colouring are small.** -/
theorem outSize_leavesOfD (m : ℕ) (C : Array ℕ) :
    ∀ o ∈ leavesOfD m C, outSize o ≤ outB m ((m + 3) / 2) := by
  intro o ho
  unfold leavesOfD at ho
  split at ho
  · rw [List.mem_singleton] at ho
    subst ho
    exact (outSize_compLeafD_le m C _).trans (by unfold outB; omega)
  · obtain ⟨o', ho', rfl⟩ := List.mem_map.1 ho
    exact (outSize_trimD_le m o').trans
      (sojProg_outSize (m := m) (t := (m + 3) / 2) C (by omega) o' ho')

theorem length_leavesOfD_le (m : ℕ) (C : Array ℕ) :
    (leavesOfD m C).length ≤ sojSz m C + 1 := by
  unfold leavesOfD sojSz
  rcases disconnD (colFn m C) (List.range m) with _ | ⟨r, rs⟩
  · simp only [List.length_map, length_sojD]
    exact (cp2_count_le_size _).trans (Nat.le_succ _)
  · simp

/-- **Decoding, disconnected case**: the components leaf of the least disconnected colour. -/
theorem leavesOfD_decode_comp (m : ℕ) (C : Array ℕ)
    (h : (disconn Finset.univ (colOf m C)).Nonempty) :
    (leavesOfD m C).map (decodeOut m) =
      [some (.inl ⟨fun _ => 0, Coherent.comp Finset.univ (colOf m C)
        ((disconn Finset.univ (colOf m C)).min' h)⟩)] := by
  have hd := disconn_wlCol m C
  unfold leavesOfD
  split
  · rename_i r rs hrs
    simp only [List.map_cons, List.map_nil, decodeOut_compLeafD]
    rw [min'_eq_minD (by rw [hd, hrs]) h]
  · rename_i hnil
    rw [hd, hnil] at h
    simp at h

/-- **Decoding, uniprimitive case**: the trimmed leaves of `soj`. -/
theorem leavesOfD_decode_soj (m : ℕ) (C : Array ℕ)
    (h : disconn Finset.univ (colOf m C) = ∅) :
    ((leavesOfD m C).map (decodeOut m) : Multiset (Option (Out (Fin m)))) =
      (soj (colOf m C) ((m + 3) / 2)).leafMs.map GraphIso.Align.trimOut := by
  have hd := disconn_wlCol m C
  unfold leavesOfD
  split
  · rename_i r rs hrs
    rw [hd, hrs] at h
    simp at h
  · rw [List.map_map, ← sojD_leafMs, Multiset.map_coe, List.map_map]
    congr 1
    exact List.map_congr_left fun o _ => decodeOut_trimD m o

end Leaves

/-! ### The group of one choice -/

section Programs

variable {D : Ty} {rec : Ty × Ty} {var : Ty → Type}

/-- `resModel`: `F_(S)` restricted to the positions of `Φ ∖ S`, generated at degree `m'`. -/
def resProg (N n : var .nat) (F : var (Ty.group D)) (ΦS Sl : var (.list .nat)) (m' : var .nat) :
    Prog (groupSig D) rec var (Ty.group D) :=
  .bind (ptsProg n Sl) fun pS => .bind (iterStabProg F pS) fun FS =>
  .bind (ptsProg n ΦS) fun pΦ => .bind (posProg N pΦ) fun pos =>
  .bind (.op1 .snd FS) fun gd => .bind (.op1 .fst gd) fun gs =>
  .bind (mapList gs fun g => restrictPermProg pos pΦ g) fun rgs =>
  .bind (.op2 .pair m' rgs) fun arg => Prog.call (S := groupSig D) GroupOp.generate arg

/-- `wlColOf`: the orbital array, the colouring of `(a, b)` and its refinement. -/
def colProg (G' : var (Ty.group D)) (m' a b : var .nat) :
    Prog (groupSig D) rec var (.array .nat) :=
  .bind (.op0 (.natLit 0)) fun z => .bind (orbitalProg z G') fun L =>
  .bind (tcolProg L m' a b) fun T => .bind (.op0 (.natLit 2)) fun two =>
  .bind (Coherent.wlProg two m' T) fun WP => .bind (.op1 .fst WP) fun W => transProg m' W

/-- **The leaves of one choice** `(S, (a, b))`, extended to the base. -/
def choiceProg (N n : var .nat) (F : var (Ty.group D)) (Φ Sl : var (.list .nat))
    (a b : var .nat) : Prog (groupSig D) rec var (.list outTy) :=
  .bind (.op2 .sub N n) fun m => .bind (phiSProg m Φ Sl) fun ΦS =>
  .bind (.op1 .length ΦS) fun m' =>
  .bind (resProg N n F ΦS Sl m') fun G' =>
  .bind (colProg G' m' a b) fun C =>
  .bind (leavesOfProg m' C) fun ls =>
  mapList ls fun o => extProg m ΦS o

/-- **All leaves**: every tuple of `j` distinct points of `Φ`, every pair of distinct indices. -/
def allLeavesProg (N n : var .nat) (F : var (Ty.group D)) (Φ : var (.list .nat))
    (j : var .nat) : Prog (groupSig D) rec var (.list outTy) :=
  .bind (tuplesProg Φ j) fun Ts =>
  Align.joFlatMap Ts fun Sl =>
    .bind (.op2 .sub N n) fun m => .bind (phiSProg m Φ Sl) fun ΦS =>
    .bind (.op1 .length ΦS) fun m' => .bind (pairsProg m') fun ps =>
    Align.joFlatMap ps fun ab => .bind (.op1 .fst ab) fun a => .bind (.op1 .snd ab) fun b =>
      choiceProg N n F Φ Sl a b

/-- **The first leaf**: the first tuple, the pair `(0, 1)`, the first leaf. -/
def firstLeafProg (N n : var .nat) (F : var (Ty.group D)) (Φ : var (.list .nat))
    (j : var .nat) : Prog (groupSig D) rec var (.option outTy) :=
  .bind (tuplesProg Φ j) fun Ts =>
  .caseList Ts (.op0 .none) fun Sl _ =>
    .bind (.op0 (.natLit 0)) fun z => .bind (.op0 (.natLit 1)) fun one =>
    .bind (choiceProg N n F Φ Sl z one) fun ls =>
    .caseList ls (.op0 .none) fun o _ => .op1 .some o

end Programs

section Specs

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}

/-- The operations of `choiceProg`. -/
def choiceOps (op : GroupOp) : Prop :=
  op = .stabilizer ∨ op = .orbitTransversal ∨ op = .orbits ∨ op = .generate

theorem cp2_iterStab_gens_le (hO : MeetsContractOn DV stabOps X.O) {M s : ℕ}
    {G₀ : Subgroup (Perm (Fin M))} (B : BackendBounds X DV M s G₀) :
    ∀ (ps : List ℕ) (H : GroupData D.denote), (∀ u ∈ ps, u < M) → H.1 = M →
      GroupValid DV M H.2.1 H.2.2 → H.2.1.length ≤ s → GensData.denote M H.2.1 ≤ G₀ →
      (iterStabModel X.O H ps).2.1.length ≤ s := by
  intro ps
  induction ps with
  | nil => intro H _ _ _ h _; exact h
  | cons u ps ih =>
    intro H hps hdeg hv hlen hle
    obtain ⟨M', ks, e⟩ := H
    change M' = M at hdeg
    subst hdeg
    have hu : u < M' := hps u List.mem_cons_self
    have hpre : GroupPre DV .stabilizer ((M', ks, e), u) := ⟨hv, hu⟩
    have hpost := hO .stabilizer _ (Or.inl rfl) hpre
    have hout := B.stabOut ks e u hle hpre
    rcases hS : X.O.run GroupOp.stabilizer ((M', ks, e), u) with ⟨M'', ks', e'⟩
    rw [hS] at hpost hout
    obtain ⟨hM'', hv', hden⟩ := hpost
    change M'' = M' at hM''
    subst hM''
    have hstep :
        iterStabModel X.O (M'', ks, e) (u :: ps) = iterStabModel X.O (M'', ks', e') ps := by
      show List.foldl _ (X.O.run GroupOp.stabilizer ((M'', ks, e), u)) ps = _
      rw [hS]
      rfl
    rw [hstep]
    refine ih _ (fun v hv => hps v (List.mem_cons_of_mem _ hv)) rfl hv' hout ?_
    change GensData.denote M'' ks' ≤ G₀
    rw [hden hu]
    exact inf_le_left.trans hle

theorem mem_phiSD {m : ℕ} {Φ Sl : List ℕ} {v : ℕ} :
    v ∈ phiSD m Φ Sl ↔ v < m ∧ v ∈ Φ ∧ v ∉ Sl := by
  simp [phiSD]

theorem phiSD_nodup (m : ℕ) (Φ Sl : List ℕ) : (phiSD m Φ Sl).Nodup :=
  List.nodup_range.filter _

theorem length_phiSD_le (m : ℕ) (Φ Sl : List ℕ) : (phiSD m Φ Sl).length ≤ m :=
  (List.length_filter_le _ _).trans (by simp)

/-- The cost of `resProg`. -/
def resCost (N nS m' s Bstab Bg : ℕ) : ℕ :=
  4 * nS + 2 + nS * (Bstab + 2) + (4 * m' + 2) + (2 * N + 9 * m' + 8) + 2 +
    (s * (12 * m' + 9 + 3) + 2) + 1 + Bg

/-- **The group of one choice.** -/
theorem RunsWithin.resProg (hO : MeetsContractOn DV choiceOps X.O)
    (hPre : ∀ op x, choiceOps op → GroupPre DV op x → X.Pre op x)
    {N n s : ℕ} {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N s G₀)
    {gs : GensData} {d : D.denote} (hGv : GroupValid DV N gs d) (hs : gs.length ≤ s)
    (hG₀ : GensData.denote N gs ≤ G₀) {Φ Sl : List ℕ}
    (hΦ : IsInvariant (GensData.denote N gs) {u | u.val ∈ ptsD n Φ})
    (hS : ∀ v ∈ Sl, v < N - n) {Bg : ℕ}
    (hBg : X.B.call GroupOp.generate ((phiSD (N - n) Φ Sl).length,
        rgensD N n (fsModel X.O n (N, gs, d) Sl).2.1 (phiSD (N - n) Φ Sl))
      (resModel X.O N n (N, gs, d) Φ Sl) ≤ Bg) :
    RunsWithin X body (Case2b.resProg N n (N, gs, d) (phiSD (N - n) Φ Sl) Sl
        (phiSD (N - n) Φ Sl).length) (resModel X.O N n (N, gs, d) Φ Sl)
        (resCost N Sl.length (phiSD (N - n) Φ Sl).length s B.Bstab Bg) ∧
      (resModel X.O N n (N, gs, d) Φ Sl).1 = (phiSD (N - n) Φ Sl).length ∧
      GroupValid DV (phiSD (N - n) Φ Sl).length (resModel X.O N n (N, gs, d) Φ Sl).2.1
        (resModel X.O N n (N, gs, d) Φ Sl).2.2 ∧
      GensData.AllValid (phiSD (N - n) Φ Sl).length
        (rgensD N n (fsModel X.O n (N, gs, d) Sl).2.1 (phiSD (N - n) Φ Sl)) := by
  set ΦS := phiSD (N - n) Φ Sl with hΦS
  have hOs : MeetsContractOn DV stabOps X.O := fun op x h hp =>
    hO op x (h.elim (fun h => Or.inl h) fun h => Or.inr (Or.inl h)) hp
  have hPs : ∀ op x, stabOps op → GroupPre DV op x → X.Pre op x := fun op x h hp =>
    hPre op x (h.elim (fun h => Or.inl h) fun h => Or.inr (Or.inl h)) hp
  have hpS : ∀ u ∈ ptsD n Sl, u < N := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hu
    have := hS v hv
    omega
  obtain ⟨hrun, hdeg, hFSv, hFSden⟩ := RunsWithin.iterStabProg (X := X) (body := body) hOs hPs
    hGv hpS B hs hG₀
  have hFSlen := cp2_iterStab_gens_le hOs B (ptsD n Sl) (N, gs, d) hpS rfl hGv hs hG₀
  set FS := iterStabModel X.O (N, gs, d) (ptsD n Sl) with hFSdef
  -- the window of `Φ ∖ S`
  set w := WinData.ofPoints N (ptsD n ΦS) with hw
  have hwnd : (ptsD n ΦS).Nodup := (phiSD_nodup _ _ _).map fun x y h => by omega
  have hwlt : ∀ u ∈ ptsD n ΦS, u < N := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hu
    have := (mem_phiSD.1 hv).1
    omega
  have hwv : w.Valid N := WinData.valid_ofPoints hwnd hwlt
  have hWinv : IsInvariant (GensData.denote N FS.2.1) (w.denote N) := by
    intro g hg u hu
    rw [hFSden] at hg
    obtain ⟨hgF, hgS⟩ := hg
    change u.val ∈ ptsD n ΦS at hu
    obtain ⟨v, hv, hvu⟩ := List.mem_map.1 hu
    obtain ⟨hvm, hvΦ, hvS⟩ := mem_phiSD.1 hv
    have hgu := hΦ g hgF u (show u.val ∈ ptsD n Φ from hvu ▸ List.mem_map_of_mem hvΦ)
    change (g u).val ∈ ptsD n Φ at hgu
    obtain ⟨v', hv'Φ, hv'u⟩ := List.mem_map.1 hgu
    change (g u).val ∈ ptsD n ΦS
    refine hv'u ▸ List.mem_map_of_mem (mem_phiSD.2 ⟨?_, hv'Φ, fun hv'S => ?_⟩)
    · have := (g u).isLt
      omega
    · have hfix := hgS (g u) (show (g u).val ∈ ptsD n Sl from hv'u ▸ List.mem_map_of_mem hv'S)
      have := g.injective (hfix.trans rfl)
      have hu' : u = g u := by
        have h1 : g (g u) = g u := hfix
        exact (g.injective h1).symm
      rw [← hu'] at hv'u
      rw [← hvu] at hv'u
      have : v' = v := by omega
      exact hvS (this ▸ hv'S)
  have hrv : GensData.AllValid ΦS.length (rgensD N n FS.2.1 ΦS) := by
    have := GensData.allValid_restrictTo hWinv hwv hFSv.1
    simpa [rgensD, hw, ptsD] using this
  have hpre : GroupPre DV GroupOp.generate (ΦS.length, rgensD N n FS.2.1 ΦS) := hrv
  have hpost := hO GroupOp.generate _ (Or.inr (Or.inr (Or.inr rfl))) hpre
  refine ⟨?_, hpost.1, hpost.2.1, hrv⟩
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.ptsProg n Sl)
    run_step hrun
    run_step (RunsWithin.ptsProg n ΦS)
    run_step (RunsWithin.posProg N w)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.mapList_le (a' := Ty.perm) (b' := Ty.perm)
      (F := PermData.restrictTo (WinData.pos N w) (ptsD n ΦS)) (c := 12 * (ptsD n ΦS).length + 9)
      fun g _ => RunsWithin.restrictPermProg _ _ g)
    run_step (RunsWithin.prim _ _)
    exact (RunsWithin.call (hPre _ _ (Or.inr (Or.inr (Or.inr rfl))) hpre))
  case hc =>
    simp only [Prim.cost, Prim.eval, resCost, ptsD, List.length_map]
    have := Nat.mul_le_mul_right (12 * ΦS.length + 9 + 3) hFSlen
    have hBg' : X.B.call GroupOp.generate (ΦS.length, List.map (PermData.restrictTo
        (WinData.pos N w) (List.map (fun x => n + x) ΦS)) FS.2.1) (X.O.run GroupOp.generate
        (ΦS.length, List.map (PermData.restrictTo (WinData.pos N w)
          (List.map (fun x => n + x) ΦS)) FS.2.1)) ≤ Bg := hBg
    have hp : w.1.length = ΦS.length := by simp [hw, WinData.ofPoints, ptsD]
    omega

/-- The cost of `colProg` at degree `m'`. -/
def colCost (m' a Btr Bstab Borb : ℕ) : ℕ :=
  1 + orbitalCost m' m' Btr Bstab Borb + (3 * a + 4 + matrixCost m' (3 * m' + 9)) + 1 +
    Coherent.wlCost 2 m' + 1 + matrixCost m' (3 * m' + 4)

/-- **The colouring of one choice.** -/
theorem RunsWithin.colProg (hO : MeetsContractOn DV orbitalOps X.O)
    (hPre : ∀ op x, orbitalOps op → GroupPre DV op x → X.Pre op x) {m' sm : ℕ}
    (Bm : BackendBounds X DV m' sm ⊤) {G' : GroupData D.denote} (hdeg : G'.1 = m')
    (hG : GroupValid DV m' G'.2.1 G'.2.2) (hs : G'.2.1.length ≤ sm) (hm : 0 < m') (a' b' : ℕ) :
    RunsWithin X body (Case2b.colProg G' m' a' b')
      (wlColD m' (tcolD (orbitalModel X.O 0 G') m' a' b'))
      (colCost m' a' Bm.Btr Bm.Bstab Bm.Borb) := by
  obtain ⟨M, gs', e⟩ := G'
  change M = m' at hdeg
  subst hdeg
  have hinv : IsInvariant (GensData.denote M gs') (baseSet 0 M) := fun _ _ u _ =>
    Nat.zero_le _
  have horb := RunsWithin.orbitalProg (X := X) (body := body) hO hPre Bm hG hs le_top hinv hm
  rw [Nat.sub_zero] at horb
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step horb
    run_step (RunsWithin.tcolProg _ M a' b')
    run_step (RunsWithin.prim _ _)
    run_step (Coherent.RunsWithin.wlProg 2 M _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.transProg M _
  case hc =>
    simp only [Prim.cost, colCost]
    omega

theorem extCost_mono (m P : ℕ) {L L' : ℕ} (h : L ≤ L') : extCost m P L ≤ extCost m P L' := by
  unfold extCost
  have h1 := Nat.mul_le_mul_left m (show 32 * P + 9 * L + 40 ≤ 32 * P + 9 * L' + 40 by omega)
  have h2 := Nat.mul_le_mul h (show 9 * L + 8 ≤ 9 * L' + 8 by omega)
  omega

/-- The cost of `choiceProg`: `N`, `n`, `s` generators, `|Φ|`, `|S|`, `m' = |Φ ∖ S|`, the
index `a`, the charges, and the size `sz` of the choice's `soj` tree. -/
def choiceCost (N n s nΦ nS m' a Bstab Bg Btr' Bstab' Borb' sz : ℕ) : ℕ :=
  1 + ((N - n) * (3 * nΦ + 3 * nS + 9) + (N - n) + 4) + (m' + 1) +
    resCost N nS m' s Bstab Bg + colCost m' a Btr' Bstab' Borb' + leavesOfCost m' sz +
    ((sz + 1) * (extCost (N - n) m' (outB m' ((m' + 3) / 2)) + 3) + 2)

/-- **The leaves of one choice**, by the program. -/
theorem RunsWithin.choiceProg (hO : MeetsContractOn DV choiceOps X.O)
    (hPre : ∀ op x, choiceOps op → GroupPre DV op x → X.Pre op x)
    {N n s : ℕ} {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N s G₀)
    {gs : GensData} {d : D.denote} (hGv : GroupValid DV N gs d) (hs : gs.length ≤ s)
    (hG₀ : GensData.denote N gs ≤ G₀) {Φ Sl : List ℕ}
    (hΦ : IsInvariant (GensData.denote N gs) {u | u.val ∈ ptsD n Φ})
    (hS : ∀ v ∈ Sl, v < N - n) (hm' : 0 < (phiSD (N - n) Φ Sl).length) {sm : ℕ}
    (Bm : BackendBounds X DV (phiSD (N - n) Φ Sl).length sm ⊤) {Bg : ℕ}
    (hBg : X.B.call GroupOp.generate ((phiSD (N - n) Φ Sl).length,
        rgensD N n (fsModel X.O n (N, gs, d) Sl).2.1 (phiSD (N - n) Φ Sl))
      (resModel X.O N n (N, gs, d) Φ Sl) ≤ Bg) (a' b' : ℕ) :
    RunsWithin X body (Case2b.choiceProg N n (N, gs, d) Φ Sl a' b')
      (choiceLeavesD X.O N n (N, gs, d) Φ Sl a' b')
      (choiceCost N n s Φ.length Sl.length (phiSD (N - n) Φ Sl).length a' B.Bstab Bg Bm.Btr
        Bm.Bstab Bm.Borb (sojSz (phiSD (N - n) Φ Sl).length
          (wlColOf X.O N n (N, gs, d) Φ Sl a' b'))) := by
  obtain ⟨hres, hdeg, hGv', hrv⟩ := RunsWithin.resProg (X := X) (body := body) hO hPre B hGv hs
    hG₀ hΦ hS hBg
  have hOo : MeetsContractOn DV orbitalOps X.O := fun op x h hp => hO op x
    (h.elim (fun h => Or.inr (Or.inl h)) fun h => h.elim (fun h => Or.inl h)
      fun h => Or.inr (Or.inr (Or.inl h))) hp
  have hPo : ∀ op x, orbitalOps op → GroupPre DV op x → X.Pre op x := fun op x h hp => hPre op x
    (h.elim (fun h => Or.inr (Or.inl h)) fun h => h.elim (fun h => Or.inl h)
      fun h => Or.inr (Or.inr (Or.inl h))) hp
  have hgen : (resModel X.O N n (N, gs, d) Φ Sl).2.1.length ≤ sm := Bm.genOut _ hrv le_top
  have hcol := RunsWithin.colProg (X := X) (body := body) hOo hPo Bm hdeg hGv' hgen hm' a' b'
  have hlen := length_leavesOfD_le (phiSD (N - n) Φ Sl).length
    (wlColOf X.O N n (N, gs, d) Φ Sl a' b')
  have hout := outSize_leavesOfD (phiSD (N - n) Φ Sl).length
    (wlColOf X.O N n (N, gs, d) Φ Sl a' b')
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.phiSProg (N - n) Φ Sl)
    run_step (RunsWithin.prim _ _)
    run_step hres
    run_step hcol
    run_step (RunsWithin.leavesOfProg (phiSD (N - n) Φ Sl).length
      (wlColOf X.O N n (N, gs, d) Φ Sl a' b'))
    exact RunsWithin.mapList_le (a' := outTy) (b' := outTy)
      (F := extD (N - n) (phiSD (N - n) Φ Sl))
      (c := extCost (N - n) (phiSD (N - n) Φ Sl).length
        (outB (phiSD (N - n) Φ Sl).length (((phiSD (N - n) Φ Sl).length + 3) / 2)))
      fun o ho => (RunsWithin.extProg (N - n) _ o).mono (extCost_mono _ _ (hout o ho))
  case hc =>
    simp only [Prim.cost, Args.head, choiceCost]
    have := Nat.mul_le_mul_right (extCost (N - n) (phiSD (N - n) Φ Sl).length
      (outB (phiSD (N - n) Φ Sl).length (((phiSD (N - n) Φ Sl).length + 3) / 2)) + 3) hlen
    omega

theorem pairsCost_mono {m m' : ℕ} (h : m' ≤ m) : pairsCost m' ≤ pairsCost m := by
  unfold pairsCost
  have := Nat.mul_le_mul h (show m' * 10 + 6 + m' + 6 ≤ m * 10 + 6 + m + 6 by omega)
  omega

/-- The cost of one tuple's choices in `allLeavesProg`: `m = N - n`, `|Φ| = nΦ`, `|S| = j`, every
choice within `Cc` with at most `Lc` leaves. -/
def tupleCost (m nΦ j Cc Lc : ℕ) : ℕ :=
  1 + (m * (3 * nΦ + 3 * j + 9) + m + 4) + (m + 1) + pairsCost m +
    (m * m * (Cc + 2 + Lc + 6) + 4)

/-- The cost of `allLeavesProg`. -/
def allCost (m nΦ j Cc Lc : ℕ) : ℕ :=
  tuplesCost nΦ j + (nΦ ^ j * (tupleCost m nΦ j Cc Lc + m * m * Lc + 6) + 4)

/-- **All leaves**, given a uniform bound `Cc` on the cost of every choice and `Lc` on its
number of leaves. -/
theorem RunsWithin.allLeavesProg {N n : ℕ} {F : GroupData D.denote} {Φ : List ℕ} {j Cc Lc : ℕ}
    (hc : ∀ Sl ∈ tuplesD Φ j, ∀ ab ∈ pairsD (phiSD (N - n) Φ Sl).length,
      RunsWithin X body (Case2b.choiceProg N n F Φ Sl ab.1 ab.2)
        (choiceLeavesD X.O N n F Φ Sl ab.1 ab.2) Cc)
    (hL : ∀ Sl ∈ tuplesD Φ j, ∀ ab ∈ pairsD (phiSD (N - n) Φ Sl).length,
      (choiceLeavesD X.O N n F Φ Sl ab.1 ab.2).length ≤ Lc) :
    RunsWithin X body (Case2b.allLeavesProg N n F Φ j) (allLeavesD X.O N n F Φ j)
      (allCost (N - n) Φ.length j Cc Lc) := by
  have hm' : ∀ Sl, (phiSD (N - n) Φ Sl).length ≤ N - n := fun Sl => length_phiSD_le _ _ _
  have hpair : ∀ Sl, (pairsD (phiSD (N - n) Φ Sl).length).length ≤ (N - n) * (N - n) := fun Sl =>
    (length_pairsD_le _).trans (Nat.mul_le_mul (hm' Sl) (hm' Sl))
  have htup := RunsWithin.tuplesProg (X := X) (body := body) Φ j
  apply RunsWithin.mono
  case h =>
    run_step htup
    refine Align.RunsWithin.joFlatMap (a' := .list .nat) (b' := outTy)
      (F := fun Sl => (pairsD (phiSD (N - n) Φ Sl).length).flatMap fun ab =>
        choiceLeavesD X.O N n F Φ Sl ab.1 ab.2)
      (c := tupleCost (N - n) Φ.length j Cc Lc) (L := (N - n) * (N - n) * Lc)
      (fun Sl hSl => ?_) fun Sl hSl => ?_
    · have hSlen : Sl.length = j := mem_tuplesD_length hSl
      apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.phiSProg (N - n) Φ Sl)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.pairsProg _)
        exact Align.RunsWithin.joFlatMap (a' := .prod .nat .nat) (b' := outTy)
          (F := fun ab => choiceLeavesD X.O N n F Φ Sl ab.1 ab.2) (c := Cc + 2) (L := Lc)
          (fun ab hab => by
            apply RunsWithin.mono
            case h =>
              run_step (RunsWithin.prim _ _)
              run_step (RunsWithin.prim _ _)
              exact hc Sl hSl ab hab
            case hc => simp [Prim.cost]; omega)
          fun ab hab => hL Sl hSl ab hab
      case hc =>
        simp only [Prim.cost, Prim.eval, Args.head, tupleCost]
        have h1 := pairsCost_mono (hm' Sl)
        have h2 := Nat.mul_le_mul_right (Cc + 2 + Lc + 6) (hpair Sl)
        have h3 := hm' Sl
        rw [hSlen]
        omega
    · rw [List.length_flatMap]
      calc ((pairsD (phiSD (N - n) Φ Sl).length).map fun ab =>
              (choiceLeavesD X.O N n F Φ Sl ab.1 ab.2).length).sum ≤
            ((pairsD (phiSD (N - n) Φ Sl).length).map fun _ => Lc).sum :=
            List.sum_le_sum fun ab hab => hL Sl hSl ab hab
        _ = (pairsD (phiSD (N - n) Φ Sl).length).length * Lc := by
            rw [List.map_const', List.sum_replicate, smul_eq_mul]
        _ ≤ (N - n) * (N - n) * Lc := Nat.mul_le_mul_right _ (hpair Sl)
  case hc =>
    simp only [allCost]
    have := Nat.mul_le_mul_right (tupleCost (N - n) Φ.length j Cc Lc + (N - n) * (N - n) * Lc + 6)
      (length_tuplesD_le Φ j)
    omega

/-- **The first leaf**, given the cost `Cc` of the first tuple's choice `(0, 1)`. -/
theorem RunsWithin.firstLeafProg {N n : ℕ} {F : GroupData D.denote} {Φ : List ℕ} {j Cc : ℕ}
    (hc : ∀ Sl ∈ tuplesD Φ j, RunsWithin X body (Case2b.choiceProg N n F Φ Sl 0 1)
      (choiceLeavesD X.O N n F Φ Sl 0 1) Cc) :
    RunsWithin X body (Case2b.firstLeafProg N n F Φ j) (firstLeafD X.O N n F Φ j)
      (tuplesCost Φ.length j + Cc + 8) := by
  unfold firstLeafD
  rcases hT : tuplesD Φ j with _ | ⟨Sl, Ts⟩
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.tuplesProg Φ j)
      run_with Coherent.RunsWithin.caseList_eq_nil hT _
      exact RunsWithin.prim _ _
    case hc => simp [Prim.cost]; omega
  · have hcS := hc Sl (by rw [hT]; exact List.mem_cons_self)
    rcases hL : choiceLeavesD X.O N n F Φ Sl 0 1 with _ | ⟨o, os⟩
    · apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.tuplesProg Φ j)
        run_with Coherent.RunsWithin.caseList_eq_cons hT _
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step hcS
        run_with Coherent.RunsWithin.caseList_eq_nil hL _
        exact (RunsWithin.prim _ _).of_eq (by simp [hL, Prim.eval])
      case hc => simp [Prim.cost]; omega
    · apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.tuplesProg Φ j)
        run_with Coherent.RunsWithin.caseList_eq_cons hT _
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step hcS
        run_with Coherent.RunsWithin.caseList_eq_cons hL _
        exact (RunsWithin.prim _ _).of_eq (by simp [hL, Prim.eval])
      case hc => simp [Prim.cost]; omega

end Specs

/-! ### Well-formedness -/

section Wf

variable {D : Ty} {rec : Ty × Ty} {var₁ var₂ : Ty → Type} {r : Bool} {Γ : WfCtx var₁ var₂}

theorem cp2_wf_posProg {N₁ : var₁ .nat} {N₂ : var₂ .nat} {p₁ : var₁ (.list .nat)}
    {p₂ : var₂ (.list .nat)} (hN : ⟨.nat, N₁, N₂⟩ ∈ Γ) (hp : ⟨.list .nat, p₁, p₂⟩ ∈ Γ) :
    Prog.Wf (S := groupSig D) (rec := rec) r Γ (posProg N₁ p₁) (posProg N₂ p₂) := by
  unfold posProg mapList
  prog_wf

theorem cp2_wf_restrictPermProg {pos₁ : var₁ (.array .nat)} {pos₂ : var₂ (.array .nat)}
    {ps₁ : var₁ (.list .nat)} {ps₂ : var₂ (.list .nat)} {g₁ : var₁ Ty.perm} {g₂ : var₂ Ty.perm}
    (hpos : ⟨.array .nat, pos₁, pos₂⟩ ∈ Γ) (hps : ⟨.list .nat, ps₁, ps₂⟩ ∈ Γ)
    (hg : ⟨Ty.perm, g₁, g₂⟩ ∈ Γ) :
    Prog.Wf (S := groupSig D) (rec := rec) r Γ (restrictPermProg pos₁ ps₁ g₁)
      (restrictPermProg pos₂ ps₂ g₂) := by
  unfold restrictPermProg
  refine .bind (.prim _ (.cons hg .nil)) fun _ _ => .bind (.prim _ (.cons (by simp [hg]) .nil))
    fun _ _ => .bind (wf_mapList (by simp [hps]) fun Γ' hΓ u₁ u₂ hu =>
      .bind (.prim _ (.cons (hΓ (by simp)) (.cons hu .nil))) fun _ _ =>
        .prim _ (.cons (List.mem_cons_of_mem _ (hΓ (by simp [hpos]))) (.cons (by simp) .nil)))
    fun _ _ => .bind (wf_mapList (by simp [hps]) fun Γ' hΓ u₁ u₂ hu =>
      .bind (.prim _ (.cons (hΓ (by simp)) (.cons hu .nil))) fun _ _ =>
        .prim _ (.cons (List.mem_cons_of_mem _ (hΓ (by simp [hpos]))) (.cons (by simp) .nil)))
    fun _ _ => .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
      .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
        .prim _ (.cons (by simp) (.cons (by simp) .nil))

theorem wf_resProg {N₁ n₁ m₁ : var₁ .nat} {N₂ n₂ m₂ : var₂ .nat} {F₁ : var₁ (Ty.group D)}
    {F₂ : var₂ (Ty.group D)} {Φ₁ S₁ : var₁ (.list .nat)} {Φ₂ S₂ : var₂ (.list .nat)}
    (hN : ⟨.nat, N₁, N₂⟩ ∈ Γ) (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (hF : ⟨Ty.group D, F₁, F₂⟩ ∈ Γ)
    (hΦ : ⟨.list .nat, Φ₁, Φ₂⟩ ∈ Γ) (hS : ⟨.list .nat, S₁, S₂⟩ ∈ Γ) (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) :
    Prog.Wf (S := groupSig D) (rec := rec) r Γ (resProg N₁ n₁ F₁ Φ₁ S₁ m₁)
      (resProg N₂ n₂ F₂ Φ₂ S₂ m₂) := by
  unfold resProg
  refine .bind (wf_ptsProg hn hS) fun _ _ => .bind (wf_iterStabProg (by simp [hF]) (by simp))
    fun _ _ => .bind (wf_ptsProg (by simp [hn]) (by simp [hΦ])) fun _ _ =>
    .bind (cp2_wf_posProg (by simp [hN]) (by simp)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => .bind (.prim _ (.cons (by simp) .nil))
    fun _ _ => .bind (wf_mapList (by simp) fun Γ' hΓ g₁ g₂ hg =>
      cp2_wf_restrictPermProg (hΓ (by simp)) (hΓ (by simp)) hg) fun _ _ =>
    .bind (.prim _ (.cons (by simp [hm]) (.cons (by simp) .nil))) fun _ _ =>
    .call _ List.mem_cons_self

theorem wf_colProg {G₁ : var₁ (Ty.group D)} {G₂ : var₂ (Ty.group D)} {m₁ a₁ b₁ : var₁ .nat}
    {m₂ a₂ b₂ : var₂ .nat} (hG : ⟨Ty.group D, G₁, G₂⟩ ∈ Γ) (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ)
    (ha : ⟨.nat, a₁, a₂⟩ ∈ Γ) (hb : ⟨.nat, b₁, b₂⟩ ∈ Γ) :
    Prog.Wf (S := groupSig D) (rec := rec) r Γ (colProg G₁ m₁ a₁ b₁) (colProg G₂ m₂ a₂ b₂) := by
  unfold colProg
  exact .bind (.prim _ .nil) fun _ _ => .bind (wf_orbitalProg (by simp) (by simp [hG])) fun _ _ =>
    .bind (wf_tcolProg (by simp) (by simp [hm]) (by simp [ha]) (by simp [hb])) fun _ _ =>
    .bind (.prim _ .nil) fun _ _ =>
    .bind (Coherent.wf_wlProg (by simp) (by simp [hm]) (by simp)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => wf_transProg (by simp [hm]) (by simp)

theorem wf_choiceProg {N₁ n₁ a₁ b₁ : var₁ .nat} {N₂ n₂ a₂ b₂ : var₂ .nat}
    {F₁ : var₁ (Ty.group D)} {F₂ : var₂ (Ty.group D)} {Φ₁ S₁ : var₁ (.list .nat)}
    {Φ₂ S₂ : var₂ (.list .nat)} (hN : ⟨.nat, N₁, N₂⟩ ∈ Γ) (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ)
    (hF : ⟨Ty.group D, F₁, F₂⟩ ∈ Γ) (hΦ : ⟨.list .nat, Φ₁, Φ₂⟩ ∈ Γ)
    (hS : ⟨.list .nat, S₁, S₂⟩ ∈ Γ) (ha : ⟨.nat, a₁, a₂⟩ ∈ Γ) (hb : ⟨.nat, b₁, b₂⟩ ∈ Γ) :
    Prog.Wf (S := groupSig D) (rec := rec) r Γ (choiceProg N₁ n₁ F₁ Φ₁ S₁ a₁ b₁)
      (choiceProg N₂ n₂ F₂ Φ₂ S₂ a₂ b₂) := by
  unfold choiceProg
  exact .bind (.prim _ (.cons hN (.cons hn .nil))) fun _ _ =>
    .bind (wf_phiSProg (by simp) (by simp [hΦ]) (by simp [hS])) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (wf_resProg (by simp [hN]) (by simp [hn]) (by simp [hF]) (by simp) (by simp [hS])
      (by simp)) fun _ _ =>
    .bind (wf_colProg (by simp) (by simp) (by simp [ha]) (by simp [hb])) fun _ _ =>
    .bind (wf_leavesOfProg (by simp) (by simp)) fun _ _ =>
    wf_mapList (by simp) fun Γ' hΓ o₁ o₂ ho => wf_extProg (hΓ (by simp)) (hΓ (by simp)) ho

theorem wf_allLeavesProg {N₁ n₁ j₁ : var₁ .nat} {N₂ n₂ j₂ : var₂ .nat}
    {F₁ : var₁ (Ty.group D)} {F₂ : var₂ (Ty.group D)} {Φ₁ : var₁ (.list .nat)}
    {Φ₂ : var₂ (.list .nat)} (hN : ⟨.nat, N₁, N₂⟩ ∈ Γ) (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ)
    (hF : ⟨Ty.group D, F₁, F₂⟩ ∈ Γ) (hΦ : ⟨.list .nat, Φ₁, Φ₂⟩ ∈ Γ) (hj : ⟨.nat, j₁, j₂⟩ ∈ Γ) :
    Prog.Wf (S := groupSig D) (rec := rec) r Γ (allLeavesProg N₁ n₁ F₁ Φ₁ j₁)
      (allLeavesProg N₂ n₂ F₂ Φ₂ j₂) := by
  unfold allLeavesProg
  refine .bind (wf_tuplesProg hΦ hj) fun _ _ => Align.wf_joFlatMap (by simp)
    fun Γ' hΓ S₁ S₂ hS => ?_
  have hN' : (⟨.nat, N₁, N₂⟩ : Σ t : Ty, var₁ t × var₂ t) ∈ Γ' := hΓ (List.mem_cons_of_mem _ hN)
  have hn' : (⟨.nat, n₁, n₂⟩ : Σ t : Ty, var₁ t × var₂ t) ∈ Γ' := hΓ (List.mem_cons_of_mem _ hn)
  have hF' : (⟨Ty.group D, F₁, F₂⟩ : Σ t : Ty, var₁ t × var₂ t) ∈ Γ' :=
    hΓ (List.mem_cons_of_mem _ hF)
  have hΦ' : (⟨.list .nat, Φ₁, Φ₂⟩ : Σ t : Ty, var₁ t × var₂ t) ∈ Γ' :=
    hΓ (List.mem_cons_of_mem _ hΦ)
  refine .bind (.prim _ (.cons hN' (.cons hn' .nil))) fun _ _ =>
    .bind (wf_phiSProg (by simp) (by simp [hΦ']) (by simp [hS])) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => .bind (wf_pairsProg (by simp)) fun _ _ =>
    Align.wf_joFlatMap (by simp) fun Γ'' hΓ' ab₁ ab₂ hab => ?_
  have hN'' : (⟨.nat, N₁, N₂⟩ : Σ t : Ty, var₁ t × var₂ t) ∈ Γ'' := hΓ' (by simp [hN'])
  have hn'' : (⟨.nat, n₁, n₂⟩ : Σ t : Ty, var₁ t × var₂ t) ∈ Γ'' := hΓ' (by simp [hn'])
  have hF'' : (⟨Ty.group D, F₁, F₂⟩ : Σ t : Ty, var₁ t × var₂ t) ∈ Γ'' := hΓ' (by simp [hF'])
  have hΦ'' : (⟨.list .nat, Φ₁, Φ₂⟩ : Σ t : Ty, var₁ t × var₂ t) ∈ Γ'' := hΓ' (by simp [hΦ'])
  have hS'' : (⟨.list .nat, S₁, S₂⟩ : Σ t : Ty, var₁ t × var₂ t) ∈ Γ'' := hΓ' (by simp [hS])
  exact .bind (.prim _ (.cons hab .nil)) fun _ _ => .bind (.prim _ (.cons (by simp [hab]) .nil))
    fun _ _ => wf_choiceProg (by simp [hN'']) (by simp [hn'']) (by simp [hF'']) (by simp [hΦ''])
      (by simp [hS'']) (by simp) (by simp)

theorem wf_firstLeafProg {N₁ n₁ j₁ : var₁ .nat} {N₂ n₂ j₂ : var₂ .nat}
    {F₁ : var₁ (Ty.group D)} {F₂ : var₂ (Ty.group D)} {Φ₁ : var₁ (.list .nat)}
    {Φ₂ : var₂ (.list .nat)} (hN : ⟨.nat, N₁, N₂⟩ ∈ Γ) (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ)
    (hF : ⟨Ty.group D, F₁, F₂⟩ ∈ Γ) (hΦ : ⟨.list .nat, Φ₁, Φ₂⟩ ∈ Γ) (hj : ⟨.nat, j₁, j₂⟩ ∈ Γ) :
    Prog.Wf (S := groupSig D) (rec := rec) r Γ (firstLeafProg N₁ n₁ F₁ Φ₁ j₁)
      (firstLeafProg N₂ n₂ F₂ Φ₂ j₂) := by
  unfold firstLeafProg
  exact .bind (wf_tuplesProg hΦ hj) fun _ _ => .caseList (by simp) (.prim _ .nil)
    fun _ _ _ _ => .bind (.prim _ .nil) fun _ _ => .bind (.prim _ .nil) fun _ _ =>
    .bind (wf_choiceProg (by simp [hN]) (by simp [hn]) (by simp [hF]) (by simp [hΦ]) (by simp)
      (by simp) (by simp)) fun _ _ =>
    .caseList (by simp) (.prim _ .nil) fun _ _ _ _ => .prim _ (.cons (by simp) .nil)

end Wf

end GraphIso.Case2b
