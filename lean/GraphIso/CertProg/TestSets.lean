module

public import GraphIso.CertProg.Setting
public import GraphIso.Toolkit.Transitivity
public import GraphIso.Reductions.RestrictionProg
public import GraphIso.Toolkit.Labels
public import GraphIso.Sims.SiftProg

/-!
# Test sets: `ψ_A`, the giant test, `G_A` and moving `A` to `A'`

Stage 14e, item 2 (`PLAN-14.md` §9). A test set is a duplicate-free list `al` of `k` base
indices `< m = N - n`; its positions are `posA n al = [n + a | a ∈ al]`, and milestone 13's set
is `finsetOf m al`.

* **`ψ_A` as a restriction.** For a group `H ≤ G` whose base action stabilizes `A`, the positions
  of `A` form an `H`-invariant window, and the restriction to it in list order (`ρ_A`,
  milestone 3's `restrictHom`) is milestone 13's `ψ_A` transported along the list order
  `listEquiv` (`psiA_eq_permCongr`). So `IsGiantOn φ A (toStab φ A H)` holds exactly when the
  restricted generators generate a giant of degree `k` (`isGiantOn_toStab_iff`).
* `restrictAProg`: the generators restricted to the positions (`GensData.restrictTo`).
* `giantAProg`: restrict, `generate` at degree `k`, and the toolkit's giant test
  (`giantProg` with base `[0, k)`). `giantAModel_iff`: the answer is `IsGiantOn`.
* `stabSetProg`: two base points outside `A`, then the toolkit's `giantSetStabProg`; for a giant
  base action the result is all of `G_A` (`toStab_stabSet`).
* `moveProg`: for lists `al`, `al'` of `k ≤ m - 2` distinct base points, an even permutation of
  the base mapping `al[i]` to `al'[i]` (transpositions, with a parity fix outside `al'`), lifted to
  `G`; `RunsWithin.moveProg`.
-/

@[expose] public section

namespace GraphIso.CertProg

open Equiv MulAction Pointwise GraphIso GraphIso.Toolkit GraphIso.Certificates Cost
  GraphIso.Programs GraphIso.Solver

/-! ### Positions of a test set -/

/-- The positions of the listed base points. -/
def posA (n : ℕ) (al : List ℕ) : List ℕ := al.map (n + ·)

/-- The window of the positions. -/
def winA (N n : ℕ) (al : List ℕ) : WinData := WinData.ofPoints N (posA n al)

theorem length_posA (n : ℕ) (al : List ℕ) : (posA n al).length = al.length := by simp [posA]

theorem mem_posA {n : ℕ} {al : List ℕ} {u : ℕ} : u ∈ posA n al ↔ ∃ a ∈ al, u = n + a := by
  simp [posA, eq_comm]

theorem posA_nodup (n : ℕ) {al : List ℕ} (hal : al.Nodup) : (posA n al).Nodup :=
  hal.map fun a b h => by simpa using h

theorem getD_posA {n : ℕ} {al : List ℕ} {j : ℕ} (hj : j < al.length) :
    (posA n al).getD j 0 = n + al[j] := by
  simp [posA, List.getD_eq_getElem?_getD, hj]

theorem winA_valid {N n : ℕ} {al : List ℕ} (hal : al.Nodup) (halm : ∀ a ∈ al, a < N - n) :
    (winA N n al).Valid N := by
  refine WinData.valid_ofPoints (posA_nodup n hal) fun u hu => ?_
  obtain ⟨a, ha, rfl⟩ := mem_posA.1 hu
  have := halm a ha
  omega

/-- **The list order of a test set.** -/
def listEquiv {m : ℕ} {al : List ℕ} (hal : al.Nodup) (halm : ∀ a ∈ al, a < m) :
    Fin al.length ≃ ↥(finsetOf m al) where
  toFun j := ⟨⟨al[j], halm _ (List.getElem_mem _)⟩, mem_finsetOf.2 (List.getElem_mem _)⟩
  invFun a := ⟨al.idxOf a.1.val, List.idxOf_lt_length_of_mem (mem_finsetOf.1 a.2)⟩
  left_inv j := Fin.ext (hal.idxOf_getElem _ _)
  right_inv a := Subtype.ext (Fin.ext (List.getElem_idxOf _))

theorem listEquiv_val {m : ℕ} {al : List ℕ} (hal : al.Nodup) (halm : ∀ a ∈ al, a < m)
    (j : Fin al.length) : ((listEquiv hal halm j : Fin m) : ℕ) = al[j] := rfl

variable {N n : ℕ} {G : Subgroup (Perm (Fin N))} {hC : CertSetting G n}
  {φ : strGroup hC →* Perm (Fin (N - n))}

/-- A subgroup `H ≤ G` whose base action stabilizes `A`. -/
def StabsA (hC : CertSetting G n) (al : List ℕ) (H : Subgroup (Perm (Fin N))) : Prop :=
  H ≤ G ∧ ∀ g : G, (g : Perm (Fin N)) ∈ H → baseHom G n hC.base g • finsetOf (N - n) al =
    finsetOf (N - n) al

/-- The positions of `A` are invariant under a group stabilizing `A`. -/
theorem isInvariant_winA {al : List ℕ} {H : Subgroup (Perm (Fin N))} (hH : StabsA hC al H) :
    IsInvariant H ((winA N n al).denote N) := by
  intro g hg u hu
  rw [winA, WinData.denote_ofPoints] at hu ⊢
  obtain ⟨a, ha, hua⟩ := mem_posA.1 hu
  have hu' : u = basePos (n := n) ⟨a, by have := u.2; omega⟩ := Fin.ext hua
  set g' : G := ⟨g, hH.1 hg⟩
  have hmem : baseHom G n hC.base g' ⟨a, by have := u.2; omega⟩ ∈ finsetOf (N - n) al := by
    rw [← hH.2 g' hg]
    exact Finset.smul_mem_smul_finset (mem_finsetOf.2 ha)
  have e := baseHom_apply (hG := hC.base) g' ⟨a, by have := u.2; omega⟩
  show (g u).val ∈ posA n al
  rw [hu', ← show g'.1 = g from rfl, ← e]
  exact mem_posA.2 ⟨_, mem_finsetOf.1 hmem, rfl⟩

theorem length_winA (al : List ℕ) : (winA N n al).1.length = al.length := by
  simp [winA, length_posA]

/-- The list order of a test set, indexed by its window. -/
def listEquivW {al : List ℕ} (hal : al.Nodup) (halm : ∀ a ∈ al, a < N - n) :
    Fin (winA N n al).1.length ≃ ↥(finsetOf (N - n) al) :=
  (finCongr (length_winA al)).trans (listEquiv hal halm)

theorem val_listEquivW {al : List ℕ} (hal : al.Nodup) (halm : ∀ a ∈ al, a < N - n)
    (i : Fin (winA N n al).1.length) :
    ((listEquivW hal halm i : Fin (N - n)) : ℕ) = al.getD i 0 := by
  have hi : (i : ℕ) < al.length := by
    have h1 := i.2
    have h2 := length_winA (N := N) (n := n) al
    omega
  rw [List.getD_eq_getElem _ _ hi]
  rfl

theorem getD_winA {al : List ℕ} {j : ℕ} (hj : j < (winA N n al).1.length) :
    (winA N n al).1.getD j 0 = n + al.getD j 0 := by
  have hj' : j < al.length := by
    have h2 := length_winA (N := N) (n := n) al
    omega
  rw [winA, WinData.ofPoints_fst, getD_posA hj', List.getD_eq_getElem _ _ hj']

/-- **`ψ_A` as a restriction**: `H` restricted to the positions of `A`, in list order. -/
def rhoA {al : List ℕ} (hal : al.Nodup) (halm : ∀ a ∈ al, a < N - n)
    {H : Subgroup (Perm (Fin N))} (hH : StabsA hC al H) : ↥H →* Perm (Fin (winA N n al).1.length) :=
  restrictHom (isInvariant_winA hH) (WinData.reindex (winA_valid hal halm))

/-- **`ψ_A` is the restriction to the positions of `A`**, transported along the list order. -/
theorem psiA_eq_permCongr (hφ : IsPhi hC φ) {al : List ℕ} (hal : al.Nodup)
    (halm : ∀ a ∈ al, a < N - n) {H : Subgroup (Perm (Fin N))} (hH : StabsA hC al H) (g : H)
    (hs : strR hC ⟨g.1, hH.1 g.2⟩ ∈ stabA φ (finsetOf (N - n) al)) :
    psiA φ (finsetOf (N - n) al) ⟨_, hs⟩ =
      (listEquivW hal halm).permCongr (rhoA hal halm hH g) := by
  ext a
  obtain ⟨j, rfl⟩ := (listEquivW hal halm).surjective a
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
  set g' : G := ⟨g.1, hH.1 g.2⟩
  have hjl : (j : ℕ) < al.length := by
    have h1 := j.2
    have h2 := length_winA (N := N) (n := n) al
    omega
  have haj : al.getD j 0 < N - n := by
    rw [List.getD_eq_getElem _ _ hjl]
    exact halm _ (List.getElem_mem _)
  have hja : (listEquivW hal halm j : Fin (N - n)) = ⟨al.getD j 0, haj⟩ :=
    Fin.ext (val_listEquivW hal halm j)
  -- the left side: the base action
  have hl : ((psiA φ (finsetOf (N - n) al) ⟨_, hs⟩ (listEquivW hal halm j) : Fin (N - n)) :
      ℕ) = (baseHom G n hC.base g' ⟨al.getD j 0, haj⟩ : ℕ) := by
    rw [psiA_apply_coe]
    show ((φ (strR hC g') _ : Fin (N - n)) : ℕ) = _
    rw [hφ, hja]
  -- the right side: the restriction
  have hr := restrictHom_apply (isInvariant_winA hH) (WinData.reindex (winA_valid hal halm)) g j
  have hr' := congrArg Fin.val hr
  rw [WinData.reindex_val,
    getD_winA (restrictHom (isInvariant_winA hH) (WinData.reindex (winA_valid hal halm)) g j).2]
    at hr'
  have hb := congrArg Fin.val (baseHom_apply (hG := hC.base) g' ⟨al.getD j 0, haj⟩)
  simp only [basePos] at hb
  rw [hl, val_listEquivW]
  show _ = al.getD (rhoA hal halm hH g j : ℕ) 0
  have e1 : (g.1 ⟨n + al.getD j 0, by omega⟩ : ℕ) =
      ((WinData.reindex (winA_valid hal halm) j : Fin N) |> g.1 |>.val) := by
    congr 2
    apply Fin.ext
    rw [WinData.reindex_val, getD_winA j.2]
  have e2 : ((g.1 (WinData.reindex (winA_valid hal halm) j : Fin N)) : ℕ) =
      n + al.getD (rhoA hal halm hH g j : ℕ) 0 := by
    rw [← hr']
    rfl
  have := hb.trans (e1.trans e2)
  omega

/-- `ψ_A` maps `toStab φ A H` onto the restriction of `H`, transported along the list order. -/
theorem map_psiA_toStab (hφ : IsPhi hC φ) {al : List ℕ} (hal : al.Nodup)
    (halm : ∀ a ∈ al, a < N - n) {H : Subgroup (Perm (Fin N))} (hH : StabsA hC al H) :
    (toStab φ (finsetOf (N - n) al) H).map (psiA φ (finsetOf (N - n) al)) =
      (rhoA hal halm hH).range.map (listEquivW hal halm).permCongrHom.toMonoidHom := by
  have hmem : ∀ g : H, strR hC ⟨g.1, hH.1 g.2⟩ ∈ stabA φ (finsetOf (N - n) al) := fun g => by
    rw [mem_stabA_strR hφ]
    exact hH.2 _ g.2
  ext y
  constructor
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨g, hg⟩ := strR_surjective hC s.1
    have hgH : (g : Perm (Fin N)) ∈ H := mem_toStab.1 hs g hg
    have hse : s = ⟨strR hC ⟨(⟨g.1, hgH⟩ : H).1, hH.1 hgH⟩, hmem ⟨g.1, hgH⟩⟩ :=
      Subtype.ext hg.symm
    refine ⟨rhoA hal halm hH ⟨g.1, hgH⟩, ⟨_, rfl⟩, ?_⟩
    rw [hse, psiA_eq_permCongr hφ hal halm hH]
    rfl
  · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
    refine ⟨⟨_, hmem g⟩, (mem_toStab_strR _ (hmem g)).2 g.2, ?_⟩
    rw [psiA_eq_permCongr hφ hal halm hH]
    rfl

/-- **The giant test of `ψ_A` on the restriction.** -/
theorem isGiantOn_toStab_iff (hφ : IsPhi hC φ) {al : List ℕ} (hal : al.Nodup)
    (halm : ∀ a ∈ al, a < N - n) {H : Subgroup (Perm (Fin N))} (hH : StabsA hC al H) :
    IsGiantOn φ (finsetOf (N - n) al) (toStab φ (finsetOf (N - n) al) H) ↔
      alternatingGroup (Fin (winA N n al).1.length) ≤ (rhoA hal halm hH).range := by
  rw [IsGiantOn, map_psiA_toStab hφ hal halm hH]
  exact alternatingGroup_le_map_permCongr _ _

/-- With base `[0, k)`, the base action is the group itself. -/
theorem baseHom_zero_apply {k : ℕ} (K : Subgroup (Perm (Fin k))) (h : IsInvariant K (baseSet 0 k))
    (g : K) : (baseHom K 0 h g : Perm (Fin k)) = g.1 := by
  ext j
  have := congrArg Fin.val (baseHom_apply (hG := h) g j)
  simp only [basePos, Nat.zero_add] at this
  rw [this]
  rfl

theorem alt_le_baseHom_zero_iff {k : ℕ} (K : Subgroup (Perm (Fin k)))
    (h : IsInvariant K (baseSet 0 k)) :
    alternatingGroup (Fin (k - 0)) ≤ (baseHom K 0 h).range ↔ alternatingGroup (Fin k) ≤ K := by
  have hr : (baseHom K 0 h).range = K := by
    ext π
    constructor
    · rintro ⟨g, rfl⟩
      rw [baseHom_zero_apply]
      exact g.2
    · intro hπ
      exact ⟨⟨π, hπ⟩, baseHom_zero_apply K h ⟨π, hπ⟩⟩
  rw [hr]
  exact Iff.rfl

theorem isInvariant_baseSet_zero {k : ℕ} (K : Subgroup (Perm (Fin k))) :
    IsInvariant K (baseSet 0 k) := fun g _ u _ => Nat.zero_le (g u).val

/-! ### The giant test of `ψ_A` as a program -/

section Programs

variable {D : Ty} {rec : Ty × Ty} {var : Ty → Type}

/-- The generators restricted to the listed positions. -/
def restrictAProg (pos : var (.array .nat)) (pA : var (.list .nat)) (gs : var Ty.gens) :
    Prog (groupSig D) rec var Ty.gens :=
  mapList gs fun g => restrictPermProg pos pA g

/-- **The giant test of `ψ_A(H)`**: restrict the generators to the positions of `A`, generate at
degree `k`, and run the toolkit's giant test with base `[0, k)`. -/
def giantAProg (pos : var (.array .nat)) (pA : var (.list .nat)) (gs : var Ty.gens) :
    Prog (groupSig D) rec var .bool :=
  .bind (restrictAProg pos pA gs) fun rgs =>
  .bind (.op1 .length pA) fun k =>
  .bind (.op2 .pair k rgs) fun a =>
  .bind (Prog.call (S := groupSig D) GroupOp.generate a) fun K =>
  .bind (.op0 (.natLit 0)) fun z => giantProg z K

end Programs

section GiantSpec

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}

/-- The restricted group, as generated by the backend. -/
def restrictAGroup (O : Oracle (groupSig D)) (pos : Array ℕ) (pA : List ℕ) (gs : GensData) :
    GroupData D.denote :=
  O.run GroupOp.generate (pA.length, GensData.restrictTo pos pA gs)

/-- The model of `giantAProg`. -/
def giantAModel (O : Oracle (groupSig D)) (pos : Array ℕ) (pA : List ℕ) (gs : GensData) :
    Bool :=
  giantModel O 0 (restrictAGroup O pos pA gs)

/-- The operations used by `giantAProg`. -/
def giantAOps (op : GroupOp) : Prop := op = .generate ∨ op = .orbits ∨ op = .stabilizer

/-- The cost of `giantAProg`: `k` positions, `s` generators, and the charges at degree `k`. -/
def giantACost (k s Bgen Borb Bstab : ℕ) : ℕ :=
  s * (12 * k + 12) + k + Bgen + degreeCost k (k - 0 - 2) Borb Bstab + 16

theorem RunsWithin.restrictAProg (pos : Array ℕ) (pA : List ℕ) (gs : GensData) :
    RunsWithin X body (CertProg.restrictAProg pos pA gs) (GensData.restrictTo pos pA gs)
      (gs.length * (12 * pA.length + 12) + 2) :=
  RunsWithin.mapList_le fun g _ => RunsWithin.restrictPermProg pos pA g

/-- **The giant test of `ψ_A`**: the program decides whether the restriction of `G = ⟨gs⟩` to
the listed window contains the alternating group. -/
theorem RunsWithin.giantAProg (hO : MeetsContractOn DV giantAOps X.O)
    (hPre : ∀ op x, giantAOps op → GroupPre DV op x → X.Pre op x) {N : ℕ} {w : WinData}
    (hw : w.Valid N) {gs : GensData} (hgs : GensData.AllValid N gs)
    (hW : IsInvariant (GensData.denote N gs) (w.denote N)) {sk : ℕ}
    (Bk : BackendBounds X DV w.1.length sk ⊤) (hs : gs.length ≤ w.1.length * (sk + 1)) :
    RunsWithin X body (CertProg.giantAProg (WinData.pos N w) w.1 gs)
        (giantAModel X.O (WinData.pos N w) w.1 gs)
        (giantACost w.1.length gs.length Bk.Bgen Bk.Borb Bk.Bstab) ∧
      (giantAModel X.O (WinData.pos N w) w.1 gs = true ↔
        alternatingGroup (Fin w.1.length) ≤ (restrictHom hW (WinData.reindex hw)).range) := by
  set rgs := GensData.restrictTo (WinData.pos N w) w.1 gs with hrgs
  have hrv : GensData.AllValid w.1.length rgs := GensData.allValid_restrictTo hW hw hgs
  have hrden : GensData.denote w.1.length rgs = (restrictHom hW (WinData.reindex hw)).range :=
    GensData.denote_restrictTo hW hw hgs
  have hOg : MeetsContractOn DV (· = .generate) X.O := fun op x hop hx =>
    hO op x (Or.inl hop) hx
  have hpre : GroupPre DV .generate (w.1.length, rgs) := hrv
  have hpost := hO .generate (w.1.length, rgs) (Or.inl rfl) hpre
  have hlen : rgs.length ≤ w.1.length * (sk + 1) := by simpa [hrgs, GensData.restrictTo] using hs
  have hBg := Bk.generate rgs hrv hlen le_top
  have hout := Bk.genOut rgs hrv le_top
  rcases hK : X.O.run GroupOp.generate (w.1.length, rgs) with ⟨k', hs', e⟩
  rw [hK] at hpost hBg hout
  obtain ⟨hk', hv, hden⟩ := hpost
  change k' = w.1.length at hk'
  subst hk'
  have hOd : MeetsContractOn DV degreeOps X.O := fun op x hop hx =>
    hO op x (by rcases hop with h | h <;> simp [giantAOps, h]) hx
  have hPred : ∀ op x, degreeOps op → GroupPre DV op x → X.Pre op x := fun op x hop hx =>
    hPre op x (by rcases hop with h | h <;> simp [giantAOps, h]) hx
  have hmodel :
      giantAModel X.O (WinData.pos N w) w.1 gs = giantModel X.O 0 (w.1.length, hs', e) := by
    simp only [giantAModel, restrictAGroup]
    rw [← hrgs, hK]
  refine ⟨?_, ?_⟩
  · have hg := RunsWithin.giantProg (X := X) (body := body) hOd hPred Bk hv hout le_top
      (isInvariant_baseSet_zero _) (Nat.zero_le _)
    rw [hmodel]
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.restrictAProg _ _ gs)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.call (hPre _ _ (Or.inl rfl) hpre))
      simp only [Prim.eval]
      rw [← hrgs, hK]
      run_step (RunsWithin.prim _ _)
      exact hg
    case hc =>
      have hp : Prim.eval (Prim.pair (a := .nat) (b := Ty.gens))
          (Args.cons (Prim.eval (Prim.length (a := .nat)) (Args.cons w.1 Args.nil))
            (Args.cons rgs Args.nil)) = (w.1.length, rgs) := rfl
      simp only [Prim.cost, giantACost, Args.head]
      rw [hp, hK]
      omega
  · rw [hmodel, giantModel_iff hOd Bk hv hout le_top (isInvariant_baseSet_zero _)
      (Nat.zero_le _), alt_le_baseHom_zero_iff, hden, hrden]

end GiantSpec

/-- **The giant test of `ψ_A` on a test set**, in milestone 13's terms. -/
theorem giantAModel_iff {D : Ty} {O : Oracle (groupSig D)}
    (hφ : IsPhi hC φ) {al : List ℕ} (hal : al.Nodup) (halm : ∀ a ∈ al, a < N - n)
    {gs : GensData} (hH : StabsA hC al (GensData.denote N gs))
    (hiff : giantAModel O (WinData.pos N (winA N n al)) (winA N n al).1 gs = true ↔
      alternatingGroup (Fin (winA N n al).1.length) ≤
        (restrictHom (isInvariant_winA hH) (WinData.reindex (winA_valid hal halm))).range) :
    giantAModel O (WinData.pos N (winA N n al)) (winA N n al).1 gs = true ↔
      IsGiantOn φ (finsetOf (N - n) al) (toStab φ (finsetOf (N - n) al) (GensData.denote N gs)) :=
  hiff.trans (isGiantOn_toStab_iff hφ hal halm hH).symm

/-! ### Base points outside a test set -/

/-- The base points `< m` not in `al`, in increasing order. -/
def outsideD (m : ℕ) (al : List ℕ) : List ℕ := (List.range m).filter fun j => !al.any (· == j)

theorem mem_outsideD {m : ℕ} {al : List ℕ} {j : ℕ} : j ∈ outsideD m al ↔ j < m ∧ j ∉ al := by
  simp only [outsideD, List.mem_filter, List.mem_range, Bool.not_eq_true', List.any_eq_false,
    beq_iff_eq]
  exact and_congr Iff.rfl ⟨fun h hj => h j hj rfl, fun h x hx e => h (e ▸ hx)⟩

theorem outsideD_nodup (m : ℕ) (al : List ℕ) : (outsideD m al).Nodup :=
  List.nodup_range.filter _

theorem length_outsideD {m : ℕ} {al : List ℕ} (hal : al.Nodup) (halm : ∀ a ∈ al, a < m) :
    (outsideD m al).length + al.length = m := by
  have h1 := List.length_eq_length_filter_add (l := List.range m)
    (fun j => !al.any (· == j))
  have h2 : ((List.range m).filter fun j => !!al.any (· == j)).length = al.length := by
    refine ((List.perm_ext_iff_of_nodup (List.nodup_range.filter _) hal).2 fun j => ?_).length_eq
    simp only [List.mem_filter, List.mem_range, Bool.not_not, List.any_eq_true, beq_iff_eq,
      exists_eq_right]
    exact ⟨fun h => h.2, fun h => ⟨halm j h, h⟩⟩
  rw [List.length_range] at h1
  rw [outsideD]
  omega

/-- **Two base points outside a test set**, when there is room for them. -/
theorem exists_outside {m : ℕ} {al : List ℕ} (hal : al.Nodup) (halm : ∀ a ∈ al, a < m)
    (hk : al.length + 2 ≤ m) :
    ∃ b₁ b₂ rest, outsideD m al = b₁ :: b₂ :: rest ∧ b₁ ≠ b₂ ∧ b₁ < m ∧ b₂ < m ∧ b₁ ∉ al ∧
      b₂ ∉ al := by
  have hlen := length_outsideD hal halm
  have hnd := outsideD_nodup m al
  rcases h : outsideD m al with _ | ⟨b₁, _ | ⟨b₂, rest⟩⟩
  · rw [h] at hlen; simp at hlen; omega
  · rw [h] at hlen; simp at hlen; omega
  · rw [h] at hnd
    have h₁ := mem_outsideD.1 (show b₁ ∈ outsideD m al by rw [h]; simp)
    have h₂ := mem_outsideD.1 (show b₂ ∈ outsideD m al by rw [h]; simp)
    refine ⟨b₁, b₂, rest, rfl, fun e => ?_, h₁.1, h₂.1, h₁.2, h₂.2⟩
    subst e
    simp at hnd

section OutsideProgram

variable {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- Membership of `x` in a list, as a program. -/
def cpMemProg (x : var .nat) (l : var (.list .nat)) : Prog S rec var .bool :=
  anyList l fun y => .op2 .natEq y x

/-- The base points `< m` not in `al`. -/
def outsideProg (m : var .nat) (al : var (.list .nat)) : Prog S rec var (.list .nat) :=
  .bind (.op1 .range m) fun rs =>
  Toolkit.filterList rs fun j => .bind (cpMemProg j al) fun c => .op1 .not c

end OutsideProgram

section OutsideSpec

variable {S : Signature} {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

theorem RunsWithin.cpMemProg (x : ℕ) (l : List ℕ) :
    RunsWithin X body (CertProg.cpMemProg x l) (l.any (· == x)) (3 * l.length + 1) :=
  (RunsWithin.anyList_le (c := 1) fun _ _ => RunsWithin.prim _ _).mono (by omega)

/-- The cost of `outsideProg`. -/
def outsideCost (m k : ℕ) : ℕ := m * (3 * k + 8) + m + 4

theorem RunsWithin.outsideProg (m : ℕ) (al : List ℕ) :
    RunsWithin X body (CertProg.outsideProg m al) (outsideD m al) (outsideCost m al.length) := by
  have hf := RunsWithin.filterList (X := X) (body := body) (a' := .nat) (xs := List.range m)
    (P := fun j => !al.any (· == j)) (c := 3 * al.length + 3)
    (p := fun j => .bind (CertProg.cpMemProg j al) fun c => .op1 .not c) fun j _ =>
      RunsWithin.bind_le (RunsWithin.cpMemProg j al) (RunsWithin.prim _ _)
        (by simp [Prim.cost])
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    exact hf
  case hc =>
    simp only [Prim.cost, Args.head, List.length_range, outsideCost]
    ring_nf
    omega

end OutsideSpec

/-! ### The setwise stabilizer of a test set -/

section StabSetProgram

variable {D : Ty} {rec : Ty × Ty} {var : Ty → Type}

/-- **The setwise stabilizer `G_A` of a test set**, for a giant base action: two base points
outside `A`, then the toolkit's `giantSetStabProg` (if there are fewer than two, the input group,
which does not happen under the hypotheses). -/
def stabSetProg (n : var .nat) (G : var (Ty.group D)) (al : var (.list .nat)) :
    Prog (groupSig D) rec var (Ty.group D) :=
  .bind (.op1 .fst G) fun N => .bind (.op2 .sub N n) fun m =>
  .bind (outsideProg m al) fun os =>
  .caseList os (.ret G) fun b₁ r => .caseList r (.ret G) fun b₂ _ =>
    giantSetStabProg n G al b₁ b₂

end StabSetProgram

section StabSetSpec

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}

/-- The model of `stabSetProg`. -/
def stabSetModel (O : Oracle (groupSig D)) (n : ℕ) (G : GroupData D.denote) (al : List ℕ) :
    GroupData D.denote :=
  match outsideD (G.1 - n) al with
  | b₁ :: b₂ :: _ => giantSetStabModel O n G al b₁ b₂
  | _ => G

/-- **The setwise stabilizer of a test set, for a giant base action.** -/
theorem RunsWithin.stabSetProg (hO : MeetsContractOn DV giantOps X.O)
    (hPre : ∀ op x, giantOps op → GroupPre DV op x → X.Pre op x)
    {N : ℕ} {gs : GensData} {d : D.denote} (hGv : GroupValid DV N gs d)
    (hG : IsInvariant (GensData.denote N gs) (baseSet n N))
    (hgiant : alternatingGroup (Fin (N - n)) ≤ (baseHom (GensData.denote N gs) n hG).range)
    {al : List ℕ} (hal : al.Nodup) (halm : ∀ x ∈ al, x < N - n) (hk : al.length + 2 ≤ N - n)
    {s : ℕ} {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N s G₀) (hs : gs.length ≤ s)
    (hG₀ : GensData.denote N gs ≤ G₀) {Bl Bg : ℕ}
    (hBl : ∀ π, X.B.call GroupOp.lift ((N, gs, d), (baseWin n N, π))
      (liftModel X.O n (N, gs, d) π) ≤ Bl)
    (hBg : ∀ b₁ b₂, X.B.call GroupOp.generate (N, giantGens X.O n (N, gs, d) al b₁ b₂)
      (giantSetStabModel X.O n (N, gs, d) al b₁ b₂) ≤ Bg) :
    RunsWithin X body (CertProg.stabSetProg n (N, gs, d) al) (stabSetModel X.O n (N, gs, d) al)
        (outsideCost (N - n) al.length + giantSetStabCost n N al.length B.Bstab Bl Bg + 6) ∧
      (stabSetModel X.O n (N, gs, d) al).1 = N ∧
      GroupValid DV N (stabSetModel X.O n (N, gs, d) al).2.1
        (stabSetModel X.O n (N, gs, d) al).2.2 ∧
      GensData.denote N (stabSetModel X.O n (N, gs, d) al).2.1 =
        (Recursion.blockStab (baseHom (GensData.denote N gs) n hG) (finsetOf (N - n) al)).map
          (GensData.denote N gs).subtype := by
  obtain ⟨b₁, b₂, rest, hos, hb, hb₁, hb₂, hbA₁, hbA₂⟩ := exists_outside hal halm hk
  obtain ⟨hrun, hN, hv, hden⟩ := RunsWithin.giantSetStabProg (X := X) (body := body) hO hPre hGv
    hG hgiant hal halm hb hb₁ hb₂ hbA₁ hbA₂ B hs hG₀ hBl (hBg b₁ b₂)
  have hmodel : stabSetModel X.O n (N, gs, d) al = giantSetStabModel X.O n (N, gs, d) al b₁ b₂ := by
    simp only [stabSetModel]
    rw [hos]
  rw [hmodel]
  refine ⟨?_, hN, hv, hden⟩
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.outsideProg _ al)
    simp only [Prim.eval]
    rw [hos]
    run_with RunsWithin.caseList_cons _
    run_with RunsWithin.caseList_cons _
    exact hrun
  case hc =>
    simp only [Prim.cost, Prim.eval]
    omega

end StabSetSpec

/-- **`G_A` in milestone 13's terms**: the setwise stabilizer computed for a test set is all of
`G_A = stabA φ A`. -/
theorem toStab_stabSet (hφ : IsPhi hC φ) {al : List ℕ} {K : Subgroup (Perm (Fin N))}
    (hK : K = (Recursion.blockStab (baseHom G n hC.base) (finsetOf (N - n) al)).map G.subtype) :
    toStab φ (finsetOf (N - n) al) K = ⊤ := by
  refine toStab_eq_top hφ fun g hg => ?_
  rw [hK]
  exact ⟨g, hg, rfl⟩

/-! ### Moving a test set onto another -/

/-- The transposition `(x y)` of `[0, m)` as data. -/
def swapD (m x y : ℕ) : PermData := swapPair m x y x y

theorem sp_self (x y z : ℕ) : sp x y x y z = Equiv.swap x y z := by
  unfold sp
  rw [Equiv.swap_apply_def]
  by_cases h₁ : z = x <;> by_cases h₂ : z = y <;> simp [h₁, h₂]

theorem get_swapD_fst {m x y z : ℕ} (hz : z < m) : get (swapD m x y).1 z = Equiv.swap x y z := by
  rw [swapD, get_swapPair_fst hz, sp_self]

theorem swapD_valid {m x y : ℕ} (hx : x < m) (hy : y < m) : (swapD m x y).Valid m := by
  have hlt : ∀ z < m, Equiv.swap x y z < m := fun z hz => by
    rw [Equiv.swap_apply_def]; split_ifs <;> omega
  refine ⟨by simp [swapD, swapPair], by simp [swapD, swapPair], fun z hz => ?_, fun z hz => ?_,
    fun z hz => ?_, fun z hz => ?_⟩
  · rw [get_swapD_fst hz]; exact hlt z hz
  · rw [swapD, get_swapPair_snd hz, sp_self]; exact hlt z hz
  · rw [get_swapD_fst hz, swapD, get_swapPair_snd (hlt z hz), sp_self, Equiv.swap_apply_self]
  · rw [swapD, get_swapPair_snd hz, sp_self, ← swapD, get_swapD_fst (hlt z hz),
      Equiv.swap_apply_self]

theorem denote_swapD {m x y : ℕ} (hx : x < m) (hy : y < m) :
    PermData.denote m (swapD m x y) = Equiv.swap (⟨x, hx⟩ : Fin m) ⟨y, hy⟩ := by
  ext z
  rw [PermData.val_denote_apply (swapD_valid hx hy), get_swapD_fst z.2, Equiv.swap_apply_def,
    Equiv.swap_apply_def]
  by_cases h₁ : z.val = x <;> by_cases h₂ : z.val = y <;> simp [h₁, h₂, Fin.ext_iff]
  split_ifs <;> simp

theorem get_mul_fst {m : ℕ} {g h : PermData} (hg : g.Valid m) (hh : h.Valid m) {z : ℕ}
    (hz : z < m) : get (PermData.mul g h).1 z = get g.1 (get h.1 z) := by
  have e := congrArg (fun π : Perm (Fin m) => (π ⟨z, hz⟩ : ℕ)) (PermData.denote_mul hg hh)
  simp only [Perm.mul_apply] at e
  rw [PermData.val_denote_apply (hg.mul hh), PermData.val_denote_apply hg] at e
  rw [e, PermData.val_denote_apply hh]

/-- One step of the move: map `al[j]` to `al'[j]` by a transposition, tracking the parity. -/
def moveStep (m : ℕ) (al al' : List ℕ) (st : PermData × Bool) (j : ℕ) : PermData × Bool :=
  if get st.1.1 (al.getD j 0) = al'.getD j 0 then st
  else (PermData.mul (swapD m (get st.1.1 (al.getD j 0)) (al'.getD j 0)) st.1, !st.2)

/-- The parity fix: a transposition of two base points outside `al'`. -/
def moveFix (m : ℕ) (al' : List ℕ) (p : PermData) : PermData :=
  match outsideD m al' with
  | b₁ :: b₂ :: _ => PermData.mul (swapD m b₁ b₂) p
  | _ => p

/-- The permutations after the steps. -/
def moveSt (m : ℕ) (al al' : List ℕ) : PermData × Bool :=
  (List.range al.length).foldl (moveStep m al al') (PermData.one m, false)

/-- **An even permutation of the base mapping `al[i]` to `al'[i]`.** -/
def moveD (m : ℕ) (al al' : List ℕ) : PermData :=
  if (moveSt m al al').2 then moveFix m al' (moveSt m al al').1 else (moveSt m al al').1

/-- The invariant of the move after `j` steps. -/
def MoveInv (m : ℕ) (al al' : List ℕ) (st : PermData × Bool) (j : ℕ) : Prop :=
  st.1.Valid m ∧ (∀ i < j, get st.1.1 (al.getD i 0) = al'.getD i 0) ∧
    Perm.sign (PermData.denote m st.1) = if st.2 then -1 else 1

theorem get_lt_of_valid {m : ℕ} {p : PermData} (hp : p.Valid m) {z : ℕ} (hz : z < m) :
    get p.1 z < m := hp.fwd_lt z hz

theorem getD_lt {m : ℕ} {l : List ℕ} (hl : ∀ a ∈ l, a < m) {i : ℕ} (hi : i < l.length) :
    l.getD i 0 < m := by
  rw [List.getD_eq_getElem _ _ hi]
  exact hl _ (List.getElem_mem _)

theorem moveStep_inv {m : ℕ} {al al' : List ℕ} (hal : al.Nodup) (hal' : al'.Nodup)
    (hlen : al'.length = al.length) (halm : ∀ a ∈ al, a < m) (halm' : ∀ a ∈ al', a < m)
    {st : PermData × Bool} {j : ℕ} (hj : j < al.length) (h : MoveInv m al al' st j) :
    MoveInv m al al' (moveStep m al al' st j) (j + 1) := by
  obtain ⟨hv, hmap, hsign⟩ := h
  have ha : al.getD j 0 < m := getD_lt halm hj
  have hy : al'.getD j 0 < m := getD_lt halm' (by omega)
  have hx : get st.1.1 (al.getD j 0) < m := get_lt_of_valid hv ha
  unfold moveStep
  split_ifs with hxy
  · refine ⟨hv, fun i hi => ?_, hsign⟩
    rcases Nat.lt_or_ge i j with hij | hij
    · exact hmap i hij
    · obtain rfl : i = j := by omega
      exact hxy
  · have hsv := swapD_valid hx hy
    refine ⟨hsv.mul hv, fun i hi => ?_, ?_⟩
    · have hil : i < al.length := by omega
      have hai : al.getD i 0 < m := getD_lt halm hil
      rw [get_mul_fst hsv hv hai, get_swapD_fst (get_lt_of_valid hv hai)]
      rcases Nat.lt_or_ge i j with hij | hij
      · rw [hmap i hij]
        apply Equiv.swap_apply_of_ne_of_ne
        · -- `al'[i] ≠ p(al[j])`, by injectivity of `p`
          intro e
          rw [← hmap i hij] at e
          have e' := congrArg (get st.1.2) e
          rw [hv.inv_fwd _ hai, hv.inv_fwd _ ha] at e'
          rw [List.getD_eq_getElem _ _ hil, List.getD_eq_getElem _ _ hj] at e'
          exact absurd ((hal.getElem_inj_iff).1 e') (by omega)
        · intro e
          rw [List.getD_eq_getElem _ _ (by omega : i < al'.length),
            List.getD_eq_getElem _ _ (by omega : j < al'.length)] at e
          exact absurd ((hal'.getElem_inj_iff).1 e) (by omega)
      · obtain rfl : i = j := by omega
        exact Equiv.swap_apply_left _ _
    · rw [PermData.denote_mul hsv hv, Perm.sign_mul, denote_swapD hx hy,
        Perm.sign_swap (fun e => hxy (congrArg Fin.val e)), hsign]
      cases st.2 <;> simp

theorem moveSt_inv {m : ℕ} {al al' : List ℕ} (hal : al.Nodup) (hal' : al'.Nodup)
    (hlen : al'.length = al.length) (halm : ∀ a ∈ al, a < m) (halm' : ∀ a ∈ al', a < m) :
    MoveInv m al al' (moveSt m al al') al.length := by
  have key : ∀ j ≤ al.length,
      MoveInv m al al' ((List.range j).foldl (moveStep m al al') (PermData.one m, false)) j := by
    intro j hj
    induction j with
    | zero =>
      refine ⟨PermData.valid_one m, fun i hi => absurd hi (Nat.not_lt_zero _), ?_⟩
      simp
    | succ j ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      exact moveStep_inv hal hal' hlen halm halm' (by omega) (ih (by omega))
  exact key al.length le_rfl

/-- **The move is an even permutation mapping `al[i]` to `al'[i]`.** -/
theorem moveD_spec {m : ℕ} {al al' : List ℕ} (hal : al.Nodup) (hal' : al'.Nodup)
    (hlen : al'.length = al.length) (halm : ∀ a ∈ al, a < m) (halm' : ∀ a ∈ al', a < m)
    (hk : al.length + 2 ≤ m) :
    (moveD m al al').Valid m ∧ (∀ i < al.length, get (moveD m al al').1 (al.getD i 0) =
      al'.getD i 0) ∧ PermData.denote m (moveD m al al') ∈ alternatingGroup (Fin m) := by
  obtain ⟨hv, hmap, hsign⟩ := moveSt_inv hal hal' hlen halm halm'
  unfold moveD
  split_ifs with hpar
  · obtain ⟨b₁, b₂, rest, hos, hb, hb₁, hb₂, hbA₁, hbA₂⟩ :=
      exists_outside hal' halm' (by omega)
    have hfix : moveFix m al' (moveSt m al al').1 =
        PermData.mul (swapD m b₁ b₂) (moveSt m al al').1 := by
      simp only [moveFix]
      rw [hos]
    rw [hfix]
    have hsv := swapD_valid hb₁ hb₂
    refine ⟨hsv.mul hv, fun i hi => ?_, ?_⟩
    · rw [get_mul_fst hsv hv (getD_lt halm hi), get_swapD_fst (get_lt_of_valid hv
        (getD_lt halm hi)), hmap i hi]
      have hmem : al'.getD i 0 ∈ al' := by
        rw [List.getD_eq_getElem _ _ (by omega)]
        exact List.getElem_mem _
      exact Equiv.swap_apply_of_ne_of_ne (fun e => hbA₁ (e ▸ hmem)) (fun e => hbA₂ (e ▸ hmem))
    · rw [Perm.mem_alternatingGroup, PermData.denote_mul hsv hv, Perm.sign_mul,
        denote_swapD hb₁ hb₂, Perm.sign_swap (fun e => hb (congrArg Fin.val e)), hsign, hpar]
      rfl
  · refine ⟨hv, hmap, ?_⟩
    rw [Perm.mem_alternatingGroup, hsign]
    simp [hpar]

section MovePrograms

variable {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- One step of the move, as a program. -/
def moveStepProg (m : var .nat) (aa ab : var (.array .nat)) (st : var (.prod Ty.perm .bool))
    (j : var .nat) : Prog S rec var (.prod Ty.perm .bool) :=
  .bind (.op1 .fst st) fun p => .bind (.op1 .snd st) fun par =>
  .bind (.op2 .arrayGet aa j) fun a => .bind (.op2 .arrayGet ab j) fun y =>
  .bind (.op1 .fst p) fun pf => .bind (.op2 .arrayGet pf a) fun x =>
  .bind (.op2 .natEq x y) fun e =>
  .ite e (.ret st)
    (.bind (swapPairProg m x y x y) fun sw => .bind (permMul sw p) fun p' =>
      .bind (.op1 .not par) fun par' => .op2 .pair p' par')

/-- The parity fix, as a program. -/
def moveFixProg (m : var .nat) (al' : var (.list .nat)) (p : var Ty.perm) :
    Prog S rec var Ty.perm :=
  .bind (outsideProg m al') fun os =>
  .caseList os (.ret p) fun b₁ r => .caseList r (.ret p) fun b₂ _ =>
    .bind (swapPairProg m b₁ b₂ b₁ b₂) fun sw => permMul sw p

/-- The move as data, as a program. -/
def moveDataProg (m : var .nat) (al al' : var (.list .nat)) : Prog S rec var Ty.perm :=
  .bind (.op1 .arrayOfList al) fun aa => .bind (.op1 .arrayOfList al') fun ab =>
  .bind (.op1 .length al) fun k => .bind (.op1 .range k) fun js =>
  .bind (permOne m) fun p0 => .bind (.op0 (.boolLit false)) fun f =>
  .bind (.op2 .pair p0 f) fun st0 =>
  .bind (.foldList js st0 fun st j => moveStepProg m aa ab st j) fun st =>
  .bind (.op1 .fst st) fun p => .bind (.op1 .snd st) fun par =>
  .ite par (moveFixProg m al' p) (.ret p)

end MovePrograms

section MoveProgram

variable {D : Ty} {rec : Ty × Ty} {var : Ty → Type}

/-- **Move a test set onto another**: an even permutation of the base mapping `al[i]` to
`al'[i]`, lifted to `G`. -/
def moveProg (n : var .nat) (G : var (Ty.group D)) (al al' : var (.list .nat)) :
    Prog (groupSig D) rec var Ty.perm :=
  .bind (.op1 .fst G) fun N => .bind (.op2 .sub N n) fun m =>
  .bind (moveDataProg m al al') fun π => liftProg n G π

end MoveProgram

section MoveDataSpecs

variable {S : Signature} {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

/-- The cost of one step of the move. -/
def moveStepCost (m : ℕ) : ℕ := swapPairCost m + 12 * m + 30

theorem RunsWithin.moveStepProg {m : ℕ} {al al' : List ℕ} {st : PermData × Bool}
    (hv : st.1.Valid m) {j : ℕ} (ha : al.getD j 0 < m) (hy : al'.getD j 0 < m) :
    RunsWithin X body (CertProg.moveStepProg m al.toArray al'.toArray st j)
      (moveStep m al al' st j) (moveStepCost m) := by
  have hx : get st.1.1 (al.getD j 0) < m := get_lt_of_valid hv ha
  have e₁ : al.toArray.getD j Ty.nat.default = al.getD j 0 := get_toArray al j
  have e₂ : al'.toArray.getD j Ty.nat.default = al'.getD j 0 := get_toArray al' j
  unfold CertProg.moveStepProg
  by_cases hxy : get st.1.1 (al.getD j 0) = al'.getD j 0
  · have hmodel : moveStep m al al' st j = st := by
      unfold moveStep
      split_ifs
      rfl
    rw [hmodel]
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      refine Sims.RunsWithin.ite_pos ?_ (RunsWithin.ret _)
      simp only [Prim.eval]
      rw [e₁, e₂]
      exact beq_iff_eq.2 hxy
    case hc =>
      simp only [Prim.cost, moveStepCost, swapPairCost]
      omega
  · have hmodel : moveStep m al al' st j = (PermData.mul (swapD m (get st.1.1 (al.getD j 0))
        (al'.getD j 0)) st.1, !st.2) := by
      unfold moveStep
      split_ifs
      rfl
    rw [hmodel]
    have hsv := swapD_valid hx hy
    have hrest : RunsWithin X body
        (.bind (swapPairProg (S := S) (rec := (a, b)) (var := Ty.denote) m
          (get st.1.1 (al.getD j 0)) (al'.getD j 0) (get st.1.1 (al.getD j 0)) (al'.getD j 0))
          fun sw => .bind (permMul sw st.1) fun p' => .bind (.op1 .not st.2) fun par' =>
            .op2 .pair p' par')
        (PermData.mul (swapD m (get st.1.1 (al.getD j 0)) (al'.getD j 0)) st.1, !st.2)
        (swapPairCost m + 12 * m + 16) := by
      apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.swapPairProg _ _ _ _ _)
        run_step (RunsWithin.permMul hsv hv)
        run_step (RunsWithin.prim _ _)
        exact RunsWithin.prim_le rfl le_rfl
      case hc =>
        simp only [Prim.cost]
        omega
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      refine Sims.RunsWithin.ite_neg (k := swapPairCost m + 12 * m + 16) ?_ ?_
      · simp only [Prim.eval]
        rw [e₁, e₂]
        exact beq_eq_false_iff_ne.2 hxy
      · simp only [Prim.eval]
        rw [e₁, e₂]
        exact hrest
    case hc =>
      simp only [Prim.cost, moveStepCost]
      omega

/-- The cost of the parity fix. -/
def moveFixCost (m k : ℕ) : ℕ := outsideCost m k + swapPairCost m + 12 * m + 20

theorem RunsWithin.moveFixProg {m : ℕ} (al' : List ℕ) {p : PermData} (hp : p.Valid m) :
    RunsWithin X body (CertProg.moveFixProg m al' p) (moveFix m al' p)
      (moveFixCost m al'.length) := by
  unfold CertProg.moveFixProg
  rcases hos : outsideD m al' with _ | ⟨b₁, _ | ⟨b₂, rest⟩⟩
  · have hmodel : moveFix m al' p = p := by simp [moveFix, hos]
    rw [hmodel]
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.outsideProg m al')
      rw [hos]
      exact RunsWithin.caseList_nil (RunsWithin.ret _)
    case hc =>
      simp only [moveFixCost]
      omega
  · have hmodel : moveFix m al' p = p := by simp [moveFix, hos]
    rw [hmodel]
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.outsideProg m al')
      rw [hos]
      exact RunsWithin.caseList_cons (RunsWithin.caseList_nil (RunsWithin.ret _))
    case hc =>
      simp only [moveFixCost]
      omega
  · have hmodel : moveFix m al' p = PermData.mul (swapD m b₁ b₂) p := by simp [moveFix, hos]
    rw [hmodel]
    have h₁ := (mem_outsideD.1 (show b₁ ∈ outsideD m al' by rw [hos]; simp)).1
    have h₂ := (mem_outsideD.1 (show b₂ ∈ outsideD m al' by rw [hos]; simp)).1
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.outsideProg m al')
      rw [hos]
      run_with RunsWithin.caseList_cons _
      run_with RunsWithin.caseList_cons _
      run_step (RunsWithin.swapPairProg _ _ _ _ _)
      exact RunsWithin.permMul (swapD_valid h₁ h₂) hp
    case hc =>
      simp only [moveFixCost]
      omega

/-- The cost of the move as data. -/
def moveDataCost (m k k' : ℕ) : ℕ := k * (moveStepCost m + 1) + moveFixCost m k' + 3 * k + k' +
  2 * m + 20

theorem RunsWithin.moveDataProg {m : ℕ} {al al' : List ℕ} (hlen : al'.length = al.length)
    (halm : ∀ a ∈ al, a < m) (halm' : ∀ a ∈ al', a < m) :
    RunsWithin X body (CertProg.moveDataProg m al al') (moveD m al al')
      (moveDataCost m al.length al'.length) := by
  have hfold := RunsWithin.foldList_inv (X := X) (body := body) (a' := .nat)
    (b' := .prod Ty.perm .bool) (I := fun st => PermData.Valid m st.1) (c := moveStepCost m)
    (f := fun st j => CertProg.moveStepProg m al.toArray al'.toArray st j)
    (F := moveStep m al al') (List.range al.length) (PermData.one m, false)
    (fun st hst j hj => by
      have hjl := List.mem_range.1 hj
      refine ⟨RunsWithin.moveStepProg hst (getD_lt halm hjl) (getD_lt halm' (by omega)), ?_⟩
      unfold moveStep
      split_ifs
      · exact hst
      · exact (swapD_valid (get_lt_of_valid hst (getD_lt halm hjl))
          (getD_lt halm' (by omega))).mul hst) (PermData.valid_one m)
  obtain ⟨hrun, hv⟩ := hfold
  have hms : (List.range al.length).foldl (moveStep m al al') (PermData.one m, false) =
      moveSt m al al' := rfl
  rw [hms] at hrun hv
  have htail : RunsWithin X body
      (.bind (.op1 (Prim.fst (a := Ty.perm) (b := .bool)) (moveSt m al al')) fun p =>
        .bind (.op1 (Prim.snd (a := Ty.perm) (b := .bool)) (moveSt m al al')) fun par =>
        Prog.ite par (CertProg.moveFixProg (S := S) (rec := (a, b)) (var := Ty.denote) m al' p)
          (.ret p)) (moveD m al al') (moveFixCost m al'.length + 3) := by
    unfold moveD
    by_cases hpar : (moveSt m al al').2 = true
    · simp only [hpar, ↓reduceIte]
      apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        exact Sims.RunsWithin.ite_pos hpar (RunsWithin.moveFixProg al' hv)
      case hc =>
        simp only [Prim.cost]
        omega
    · simp only [hpar, ↓reduceIte, Bool.false_eq_true]
      apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        exact Sims.RunsWithin.ite_neg (Bool.eq_false_iff.2 hpar) (RunsWithin.ret _)
      case hc =>
        simp only [Prim.cost]
        omega
  unfold CertProg.moveDataProg
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.permOne m)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    simp only [Prim.eval]
    run_step hrun
    exact htail
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head, List.length_range, moveDataCost]
    omega

end MoveDataSpecs

section MoveSpec

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}

/-- The model of `moveProg`. -/
def moveModel (O : Oracle (groupSig D)) (n : ℕ) (G : GroupData D.denote) (al al' : List ℕ) :
    PermData :=
  liftModel O n G (moveD (G.1 - n) al al')

/-- **Moving a test set onto another.** For a giant base action and duplicate-free lists `al`,
`al'` of `k ≤ m - 2` base points, the program returns `τ ∈ G` whose base action maps `al[i]` to
`al'[i]`. -/
theorem RunsWithin.moveProg (hO : MeetsContractOn DV liftOps X.O)
    (hPre : ∀ op x, liftOps op → GroupPre DV op x → X.Pre op x) {n N : ℕ} {gs : GensData}
    {d : D.denote} (hGv : GroupValid DV N gs d)
    (hG : IsInvariant (GensData.denote N gs) (baseSet n N))
    (hgiant : alternatingGroup (Fin (N - n)) ≤ (baseHom (GensData.denote N gs) n hG).range)
    {al al' : List ℕ} (hal : al.Nodup) (hal' : al'.Nodup) (hlen : al'.length = al.length)
    (halm : ∀ x ∈ al, x < N - n) (halm' : ∀ x ∈ al', x < N - n) (hk : al.length + 2 ≤ N - n)
    {Bl : ℕ} (hBl : ∀ π, X.B.call GroupOp.lift ((N, gs, d), (baseWin n N, π))
      (liftModel X.O n (N, gs, d) π) ≤ Bl) :
    RunsWithin X body (CertProg.moveProg n (N, gs, d) al al') (moveModel X.O n (N, gs, d) al al')
        (moveDataCost (N - n) al.length al'.length + baseWinCost n N + Bl + 6) ∧
      PermData.Valid N (moveModel X.O n (N, gs, d) al al') ∧
      ∃ h : PermData.denote N (moveModel X.O n (N, gs, d) al al') ∈ GensData.denote N gs,
        ∀ i (hi : i < al.length), ((baseHom (GensData.denote N gs) n hG ⟨_, h⟩
          ⟨al.getD i 0, getD_lt halm hi⟩ : Fin (N - n)) : ℕ) = al'.getD i 0 := by
  obtain ⟨hπv, hπmap, hπalt⟩ := moveD_spec hal hal' hlen halm halm' hk
  obtain ⟨hrun, hv, hmem, hbase⟩ := RunsWithin.liftProg (X := X) (body := body) hO hPre hGv hG
    hπv (hgiant hπalt) (hBl _)
  refine ⟨?_, hv, hmem, fun i hi => ?_⟩
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      simp only [Prim.eval]
      run_step (RunsWithin.moveDataProg hlen halm halm')
      exact hrun
    case hc =>
      simp only [Prim.cost]
      omega
  · simp only [moveModel] at hbase ⊢
    rw [hbase, PermData.val_denote_apply hπv]
    exact hπmap i hi

/-- The move maps the test set onto the other, as sets. -/
theorem baseHom_smul_finsetOf {m : ℕ} {σ : Perm (Fin m)} {al al' : List ℕ}
    (hlen : al'.length = al.length) (halm : ∀ x ∈ al, x < m)
    (hmap : ∀ i (hi : i < al.length), ((σ ⟨al.getD i 0, getD_lt halm hi⟩ : Fin m) : ℕ) =
      al'.getD i 0) : σ • finsetOf m al = finsetOf m al' := by
  ext b
  rw [Finset.mem_smul_finset, mem_finsetOf]
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨i, hi, hai⟩ := List.getElem_of_mem (mem_finsetOf.1 ha)
    have ha' : a = ⟨al.getD i 0, getD_lt halm hi⟩ :=
      Fin.ext (by show (a : ℕ) = al.getD i 0; rw [List.getD_eq_getElem _ _ hi, hai])
    rw [ha', Perm.smul_def, hmap i hi, List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _
  · intro hb
    obtain ⟨i, hi, hbi⟩ := List.getElem_of_mem hb
    have hi' : i < al.length := by omega
    refine ⟨⟨al.getD i 0, getD_lt halm hi'⟩, mem_finsetOf.2 ?_, ?_⟩
    · show al.getD i 0 ∈ al
      rw [List.getD_eq_getElem _ _ hi']
      exact List.getElem_mem _
    · apply Fin.ext
      rw [Perm.smul_def, hmap i hi', List.getD_eq_getElem _ _ hi, hbi]

end MoveSpec

/-! ### Well-formedness -/

section Wf

variable {D : Ty} {S : Signature} {rec : Ty × Ty} {var₁ var₂ : Ty → Type} {r : Bool}
  {Γ : WfCtx var₁ var₂}

theorem cp_wf_restrictPermProg {pos₁ : var₁ (.array .nat)} {pos₂ : var₂ (.array .nat)}
    {ps₁ : var₁ (.list .nat)} {ps₂ : var₂ (.list .nat)} {g₁ : var₁ Ty.perm} {g₂ : var₂ Ty.perm}
    (hpos : ⟨.array .nat, pos₁, pos₂⟩ ∈ Γ) (hps : ⟨.list .nat, ps₁, ps₂⟩ ∈ Γ)
    (hg : ⟨Ty.perm, g₁, g₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (restrictPermProg pos₁ ps₁ g₁)
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

theorem wf_restrictAProg {pos₁ : var₁ (.array .nat)} {pos₂ : var₂ (.array .nat)}
    {pA₁ : var₁ (.list .nat)} {pA₂ : var₂ (.list .nat)} {gs₁ : var₁ Ty.gens} {gs₂ : var₂ Ty.gens}
    (hpos : ⟨.array .nat, pos₁, pos₂⟩ ∈ Γ) (hpA : ⟨.list .nat, pA₁, pA₂⟩ ∈ Γ)
    (hgs : ⟨Ty.gens, gs₁, gs₂⟩ ∈ Γ) :
    Prog.Wf (S := groupSig D) (rec := rec) r Γ (restrictAProg pos₁ pA₁ gs₁)
      (restrictAProg pos₂ pA₂ gs₂) :=
  wf_mapList hgs fun _ hΓ _ _ hg => cp_wf_restrictPermProg (hΓ hpos) (hΓ hpA) hg

theorem wf_giantAProg {pos₁ : var₁ (.array .nat)} {pos₂ : var₂ (.array .nat)}
    {pA₁ : var₁ (.list .nat)} {pA₂ : var₂ (.list .nat)} {gs₁ : var₁ Ty.gens} {gs₂ : var₂ Ty.gens}
    (hpos : ⟨.array .nat, pos₁, pos₂⟩ ∈ Γ) (hpA : ⟨.list .nat, pA₁, pA₂⟩ ∈ Γ)
    (hgs : ⟨Ty.gens, gs₁, gs₂⟩ ∈ Γ) :
    Prog.Wf (S := groupSig D) (rec := rec) r Γ (giantAProg pos₁ pA₁ gs₁)
      (giantAProg pos₂ pA₂ gs₂) := by
  unfold giantAProg
  refine .bind (wf_restrictAProg hpos hpA hgs) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp [hpA]) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ => ?_
  refine .bind (by prog_wf) fun _ _ => ?_
  exact .bind (.prim _ .nil) fun _ _ => wf_giantProg (by simp) (.tail _ (.head _))

theorem wf_cpMemProg {x₁ : var₁ .nat} {x₂ : var₂ .nat} {l₁ : var₁ (.list .nat)}
    {l₂ : var₂ (.list .nat)} (hx : ⟨.nat, x₁, x₂⟩ ∈ Γ) (hl : ⟨.list .nat, l₁, l₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (cpMemProg x₁ l₁) (cpMemProg x₂ l₂) :=
  wf_anyList hl fun _ hΓ _ _ hy => .prim _ (.cons hy (.cons (hΓ hx) .nil))

theorem wf_outsideProg {m₁ : var₁ .nat} {m₂ : var₂ .nat} {al₁ : var₁ (.list .nat)}
    {al₂ : var₂ (.list .nat)} (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) (hal : ⟨.list .nat, al₁, al₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (outsideProg m₁ al₁) (outsideProg m₂ al₂) := by
  unfold outsideProg
  exact .bind (.prim _ (.cons hm .nil)) fun _ _ => Toolkit.wf_filterList (by simp)
    fun _ hΓ _ _ hj => .bind (wf_cpMemProg hj (hΓ (by simp [hal]))) fun _ _ =>
      .prim _ (.cons (by simp) .nil)

theorem wf_stabSetProg {n₁ : var₁ .nat} {n₂ : var₂ .nat} {G₁ : var₁ (Ty.group D)}
    {G₂ : var₂ (Ty.group D)} {al₁ : var₁ (.list .nat)} {al₂ : var₂ (.list .nat)}
    (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (hG : ⟨Ty.group D, G₁, G₂⟩ ∈ Γ)
    (hal : ⟨.list .nat, al₁, al₂⟩ ∈ Γ) :
    Prog.Wf (rec := rec) r Γ (stabSetProg n₁ G₁ al₁) (stabSetProg n₂ G₂ al₂) := by
  unfold stabSetProg
  refine .bind (.prim _ (.cons hG .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) (.cons (by simp [hn]) .nil))) fun _ _ => ?_
  refine .bind (wf_outsideProg (by simp) (by simp [hal])) fun _ _ => ?_
  refine .caseList (by simp) (.ret (by simp [hG])) fun _ _ _ _ => ?_
  refine .caseList (by simp) (.ret (by simp [hG])) fun _ _ _ _ => ?_
  exact wf_giantSetStabProg (by simp [hn]) (by simp [hG]) (by simp [hal]) (by simp) (by simp)

theorem wf_moveStepProg {m₁ j₁ : var₁ .nat} {m₂ j₂ : var₂ .nat}
    {aa₁ ab₁ : var₁ (.array .nat)} {aa₂ ab₂ : var₂ (.array .nat)}
    {st₁ : var₁ (.prod Ty.perm .bool)} {st₂ : var₂ (.prod Ty.perm .bool)}
    (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) (haa : ⟨.array .nat, aa₁, aa₂⟩ ∈ Γ)
    (hab : ⟨.array .nat, ab₁, ab₂⟩ ∈ Γ) (hst : ⟨.prod Ty.perm .bool, st₁, st₂⟩ ∈ Γ)
    (hj : ⟨.nat, j₁, j₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (moveStepProg m₁ aa₁ ab₁ st₁ j₁)
      (moveStepProg m₂ aa₂ ab₂ st₂ j₂) := by
  unfold moveStepProg
  refine .bind (.prim _ (.cons hst .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp [hst]) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp [haa]) (.cons (by simp [hj]) .nil))) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp [hab]) (.cons (by simp [hj]) .nil))) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ => ?_
  refine .ite (by simp) (.ret (by simp [hst])) ?_
  refine .bind (wf_swapPairProg (by simp [hm]) (by simp) (by simp) (by simp) (by simp))
    fun _ _ => ?_
  refine .bind (wf_permMul (by simp) (by simp)) fun _ _ => ?_
  exact .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .prim _ (.cons (by simp) (.cons (by simp) .nil))

theorem wf_moveFixProg {m₁ : var₁ .nat} {m₂ : var₂ .nat} {al₁ : var₁ (.list .nat)}
    {al₂ : var₂ (.list .nat)} {p₁ : var₁ Ty.perm} {p₂ : var₂ Ty.perm}
    (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) (hal : ⟨.list .nat, al₁, al₂⟩ ∈ Γ) (hp : ⟨Ty.perm, p₁, p₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (moveFixProg m₁ al₁ p₁) (moveFixProg m₂ al₂ p₂) := by
  unfold moveFixProg
  refine .bind (wf_outsideProg hm hal) fun _ _ => ?_
  refine .caseList (by simp) (.ret (by simp [hp])) fun _ _ _ _ => ?_
  refine .caseList (by simp) (.ret (by simp [hp])) fun _ _ _ _ => ?_
  exact .bind (wf_swapPairProg (by simp [hm]) (by simp) (by simp) (by simp) (by simp))
    fun _ _ => wf_permMul (by simp) (by simp [hp])

theorem wf_moveDataProg {m₁ : var₁ .nat} {m₂ : var₂ .nat} {al₁ al'₁ : var₁ (.list .nat)}
    {al₂ al'₂ : var₂ (.list .nat)} (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) (hal : ⟨.list .nat, al₁, al₂⟩ ∈ Γ)
    (hal' : ⟨.list .nat, al'₁, al'₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (moveDataProg m₁ al₁ al'₁) (moveDataProg m₂ al₂ al'₂) := by
  unfold moveDataProg
  refine .bind (.prim _ (.cons hal .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp [hal']) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp [hal]) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (wf_permOne (by simp [hm])) fun _ _ => ?_
  refine .bind (.prim _ .nil) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ => ?_
  refine .bind (.foldList (by simp) (by simp) fun _ _ _ _ => wf_moveStepProg (by simp [hm])
    (by simp) (by simp) (by simp) (by simp)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  exact .ite (by simp) (wf_moveFixProg (by simp [hm]) (by simp [hal']) (by simp))
    (.ret (by simp))

theorem wf_moveProg {n₁ : var₁ .nat} {n₂ : var₂ .nat} {G₁ : var₁ (Ty.group D)}
    {G₂ : var₂ (Ty.group D)} {al₁ al'₁ : var₁ (.list .nat)} {al₂ al'₂ : var₂ (.list .nat)}
    (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (hG : ⟨Ty.group D, G₁, G₂⟩ ∈ Γ)
    (hal : ⟨.list .nat, al₁, al₂⟩ ∈ Γ) (hal' : ⟨.list .nat, al'₁, al'₂⟩ ∈ Γ) :
    Prog.Wf (rec := rec) r Γ (moveProg n₁ G₁ al₁ al'₁) (moveProg n₂ G₂ al₂ al'₂) := by
  unfold moveProg
  refine .bind (.prim _ (.cons hG .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) (.cons (by simp [hn]) .nil))) fun _ _ => ?_
  exact .bind (wf_moveDataProg (by simp) (by simp [hal]) (by simp [hal'])) fun _ _ =>
    wf_liftProg (by simp [hn]) (by simp [hG]) (by simp)

end Wf

end GraphIso.CertProg
