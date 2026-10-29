module

public import GraphIso.Main.SimsM4
public import GraphIso.Main.M5StepCJ

/-!
# M5 with the Schreier–Sims backend

Stage 14j-5c, items 1–4 (`PLAN-14.md` §14.8), for M5: `RunsWithin.m5StepCJProg_ss`, the step
`RunsWithin.m5StepCJProg_jp` at `ssCtx` with every backend hypothesis proved.

* **The bounds** `ssM5β`: every charge of M5 is a Schreier–Sims charge at degree at most `N` (the
  restricted instance's degree) or `m` (its base), on generator lists bounded by `sIn ≥ N²`.
  - The aligned groups' generators are the lifts of `stabInPL` of the structure's generators
    plus the kernel's (`stabInPL_length_le`): a partition's generators number at most `m² + m`
    whatever the data (`partGensD_length_le`), a valid coloured Johnson structure's at most `3m²`
    (`length_cjohnGensD_le`).
  - Case 2b's and Case 3's partition routes take their charges only for a leaf that is not a
    Johnson leaf (`X₀.1 ≠ 2`), the Johnson routes only with the pair's facts (`CJFacts`): the
    premises of stage 14j-5c's `_jp` theorems (§14.8 item 4).
* **The per-orbit `RDOrbit`**: `rd_orbit_free_ssU` for the partition routes, and for the Johnson
  routes `rd_orbit_cj_ssU` with the invariance of the aligned group from `ar_g1_facts`.
-/

@[expose] public section

namespace GraphIso.Main

open Equiv MulAction Pointwise Cost GraphIso GraphIso.Programs GraphIso.Toolkit
  GraphIso.Recursion GraphIso.SplitJohnson GraphIso.Solver GraphIso.Align GraphIso.Certificates
  GraphIso.CertProg Sims

attribute [local gcongr] buildCost_mono₂ genCost_mono₂ kerCost_mono₂ rd_liftCost_mono₂
  rd_orbitsCost_mono₂

/-! ### Lengths of generator lists -/

section Lengths

theorem stabInPL_length_le (gfs : List (PermData × Bool)) :
    (stabInPL gfs).length ≤ 2 * gfs.length := by
  unfold stabInPL
  split
  · rw [List.length_map]
    omega
  · rename_i ρ _
    rw [List.length_flatMap]
    have h : ∀ p ∈ gfs, (schreierPair ρ p).length = 2 := by
      intro p _
      unfold schreierPair
      split <;> rfl
    rw [List.map_congr_left h, List.map_const', List.sum_replicate, smul_eq_mul, Nat.mul_comm]

theorem flagsModel_length {D : Ty} (O : Oracle (groupSig D)) (P : GroupData D.denote)
    (gs : GensData) : (flagsModel O P gs).length = gs.length :=
  List.length_map _

/-- **The generators of a colored partition's stabilizer** number at most `m² + m`, whatever the
data: the blocks are read through `blkL`, a filter of `[0, m)`. -/
theorem partGensD_length_le (m : ℕ) (x : Array ℕ × Array (List ℕ)) :
    (partGensD m x).length ≤ m * m + m := by
  have hr : (repsD m x.2).length ≤ m := (List.length_filter_le _ _).trans (by simp)
  have hw : (withinGensD m x.2).length ≤ m * m := by
    unfold withinGensD
    rw [List.length_flatMap]
    calc ((repsD m x.2).map fun r =>
          (((blkL m x.2 r).filter fun w => w != r).map (Align.swapD m r)).length).sum
        ≤ ((repsD m x.2).map fun _ => m).sum := List.sum_le_sum fun r _ => by
          rw [List.length_map]
          exact (List.length_filter_le _ _).trans ((List.length_filter_le _ _).trans (by simp))
      _ = (repsD m x.2).length * m := by
          rw [List.map_const', List.sum_replicate, smul_eq_mul]
      _ ≤ m * m := Nat.mul_le_mul_right _ hr
  have he : (exchGensD m x.1 x.2).length ≤ m := by
    unfold exchGensD
    rw [List.length_map]
    exact (List.length_filter_le _ _).trans hr
  unfold partGensD
  rw [List.length_append]
  omega

/-- The generators of a leaf that is not a Johnson leaf: a partition's, or none. -/
theorem outGensD_length_le {m : ℕ} {o : SoJTree.OutD} (h : o.1 ≠ 2) :
    (Case2b.outGensD m o).length ≤ m * m + m := by
  unfold Case2b.outGensD
  split_ifs with h1
  · exact partGensD_length_le m _
  · simp

/-- **The aligned group's generators**: the lifts of `stabInPL` of the flagged structure
generators, and the kernel's. -/
theorem aligned_length_le {D : Ty} (O : Oracle (groupSig D)) (n : ℕ) (G : GroupData D.denote)
    (P : GroupData D.denote) (gs' : GensData) :
    ((stabInPL (flagsModel O P gs')).map (Toolkit.liftModel O n G) ++ (kerModel O n G).2.1).length
      ≤ 2 * gs'.length + (kerModel O n G).2.1.length := by
  rw [List.length_append, List.length_map]
  have := stabInPL_length_le (flagsModel O P gs')
  rw [flagsModel_length] at this
  omega

end Lengths


/-! ### The data the work depends on -/

section Data

/-- The degree program counts at most one level per round. -/
theorem degreeModel_le {D : Ty} (O : Oracle (groupSig D)) (n cap : ℕ) (G : GroupData D.denote) :
    degreeModel O n cap G ≤ cap := by
  have key : ∀ (l : List ℕ) (st : ℕ × Bool × GroupData D.denote),
      (l.foldl (fun st _ => degStep O n st) st).1 ≤ st.1 + l.length := by
    intro l
    induction l with
    | nil => intro st; simp
    | cons a l ih =>
      intro st
      rw [List.foldl_cons, List.length_cons]
      refine (ih _).trans ?_
      have : (degStep O n st).1 ≤ st.1 + 1 := by
        unfold degStep
        split_ifs <;> simp
      omega
  have := key (List.range cap) (0, false, G)
  simp only [List.length_range, zero_add] at this
  exact this

/-- Case 2b's degree is at most the base size. -/
theorem degD_le {D : Ty} (O : Oracle (groupSig D)) (N n : ℕ) (F : GroupData D.denote)
    (Φ : List ℕ) : Case2b.degD O N n F Φ ≤ N - n :=
  (degreeModel_le _ _ _ _).trans (Case2b.length_phiSD_le _ _ _)

/-- The base orbits of a valid group keeping the base invariant, with Schreier–Sims. -/
theorem ss_baseOrbits {n N : ℕ} {fs : GensData} {e : Unit} (hfs : GensData.AllValid N fs)
    (hb : IsInvariant (GensData.denote N fs) (baseSet n N)) :
    IsOrbitPartition (GensData.denote N fs) (baseWin n N)
      (ssCtx.O.run GroupOp.orbits ((N, fs, e), baseWin n N)) :=
  ssOracle_meets .orbits _ ⟨⟨hfs, trivial⟩, baseWin_valid n N, by rw [baseWin_denote]; exact hb⟩

/-- The large orbit `Φ` of M5's case decision has at most `m` points. -/
theorem ss_m5Cs_le {n N : ℕ} {fs : GensData} {e : Unit} (hfs : GensData.AllValid N fs)
    (hb : IsInvariant (GensData.denote N fs) (baseSet n N)) :
    (m5Cs ssCtx.O n N (N, fs, e)).2.length ≤ N - n := by
  obtain ⟨-, hob⟩ := m5_os_bounds (ss_baseOrbits (e := e) hfs hb)
  unfold m5Cs Giant.caseD
  rcases hf : Giant.agFindD (N - n) (m5Os ssCtx.O n N (N, fs, e)) with _ | o
  · dsimp only
    split_ifs <;> simp
  · dsimp only
    have := ((Giant.ag_foldFind (m := N - n) (m5Os ssCtx.O n N (N, fs, e)) none).1 o hf)
    rcases this with h | ⟨ho, -⟩
    · cases h
    · exact hob o ho

/-- The fixed points of the base action number at most `m`. -/
theorem ss_fixPts_le {n N : ℕ} {fs : GensData} {e : Unit} (hfs : GensData.AllValid N fs)
    (hb : IsInvariant (GensData.denote N fs) (baseSet n N)) :
    (fixPtsD (m5Os ssCtx.O n N (N, fs, e))).length ≤ N - n := by
  have hp := Giant.ag_bos_flatten (ss_baseOrbits (e := e) hfs hb)
  have h1 := ((List.filter_sublist (p := fun o : List ℕ => o.length == 1)
    (l := m5Os ssCtx.O n N (N, fs, e))).flatten).length_le
  have h2 := hp.length_eq
  rw [List.length_range] at h2
  unfold fixPtsD
  change _ ≤ (m5Os ssCtx.O n N (N, fs, e)).flatten.length at h1
  change (m5Os ssCtx.O n N (N, fs, e)).flatten.length = N - n at h2
  omega

/-- The kernel of the base action has at most `m!` coset representatives. -/
theorem ss_kerReps_le {n N : ℕ} {gs : GensData} (hgs : GensData.AllValid N gs)
    (hb : IsInvariant (GensData.denote N gs) (baseSet n N)) :
    (kerReps ssCtx.O n (N, gs, ())).length ≤ (N - n).factorial := by
  obtain ⟨-, -, -, -, -, -, -, hrlen⟩ := RunsWithin.kerProg (X := ssCtx) (DV := ssDV)
    (a := Ty.unit) (b := Ty.unit)
    (body := fun x => (Prog.ret x : Prog (groupSig Ty.unit) (Ty.unit, Ty.unit) Ty.denote Ty.unit))
    (n := n) (fun op x _ hx => ssOracle_meets op x hx) (fun _ _ _ h => h)
    (show GroupValid (D := Ty.unit) ssDV N gs () from ⟨hgs, trivial⟩) hb le_rfl le_rfl
  rw [hrlen]
  calc Nat.card (baseHom (GensData.denote N gs) n hb).range
      ≤ Nat.card (Perm (Fin (N - n))) := Subgroup.card_le_card_group _
    _ = (N - n).factorial := by
        rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]

/-- The iterated point stabilizers of a group of at most `S ≥ N²` generators have at most `S`
generators (by `iterStab_spec` for the invariant `ssBnd S`). -/
theorem ss_iterStab_le {N S : ℕ} (hS : N * N ≤ S) {gs : GensData} (hgs : GensData.AllValid N gs)
    (hl : gs.length ≤ S) {ps : List ℕ} (hps : ∀ u ∈ ps, u < N) :
    (iterStabModel ssCtx.O (N, gs, ()) ps).2.1.length ≤ S := by
  obtain ⟨-, -, hv, -⟩ := iterStab_spec (X := ssCtxB S) (DV := ssBnd S) (a := Ty.unit)
    (b := Ty.unit)
    (body := fun x => (Prog.ret x : Prog (groupSig Ty.unit) (Ty.unit, Ty.unit) Ty.denote Ty.unit))
    (fun op x _ hx => ssOracle_meets_bnd S op x hx) (fun _ _ _ h => h) (ssBoundsB S N S ⊤ hS)
    ps hps gs () ⟨hgs, show gs.length ≤ max S (N * N) from le_max_of_le_left hl⟩ hl le_top
  exact hv.2.trans (max_le le_rfl hS)

/-- The generators of the set stabilizer of a `k`-set in a giant. -/
theorem ss_giantGens_le {n N S : ℕ} (hS : N * N ≤ S) {gs : GensData}
    (hgs : GensData.AllValid N gs) (hl : gs.length ≤ S) {A : List ℕ}
    (hA : ∀ a ∈ A, a < N - n) (b₁ b₂ : ℕ) :
    (giantGens ssCtx.O n (N, gs, ()) A b₁ b₂).length ≤ A.length + S := by
  unfold giantGens
  rw [List.length_append]
  have h1 : (giantLifts ssCtx.O n (N, gs, ()) b₁ b₂ A).length ≤ A.length := by
    unfold giantLifts
    split
    · simp
    · simp
  have h2 := ss_iterStab_le hS hgs hl (ps := A.map (n + ·)) (by
    intro u hu
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hu
    have := hA a ha
    omega)
  omega

end Data


/-! ### The bounds of M5 -/

section Bounds

/-- **The bound on Case 2b's candidates** for base size `m`: `c2bR` with at most `m` points in
`Φ` and degree at most `m`. -/
def c2bRU (m : ℕ) : ℕ := (m + 1) ^ m * (m * m * (Case2b.sojZ m + 1))

theorem c2bR_le {N n nΦ j : ℕ} (hΦ : nΦ ≤ N - n) (hj : j ≤ N - n) :
    Case2b.c2bR N n nΦ j (Case2b.sojZ (N - n)) ≤ c2bRU (N - n) := by
  unfold Case2b.c2bR c2bRU
  refine Nat.mul_le_mul_right _ ((Nat.pow_le_pow_left (show nΦ ≤ N - n + 1 by omega) j).trans ?_)
  exact Nat.pow_le_pow_right (by omega) hj

theorem c3R_mono {k m m' Z : ℕ} (h : m ≤ m') : Case3.c3R k m Z ≤ Case3.c3R k m' Z := by
  unfold Case3.c3R
  have := Nat.pow_le_pow_left h k
  gcongr

/-- **M5's bounds with Schreier–Sims**, for the restricted degree `N`, base size `m`, certificate
size `k`, `sIn ≥ N²` and sub-solver answers of at most `s` generators. -/
def ssM5β (N m k sIn s : ℕ) : M5Bounds where
  Box := orbitsCost N sIn m + 5
  Boy := orbitsCost N sIn m + 5
  BgP := genCost m sIn + 2
  Bmem := memCost m (m * m) + 5
  BkA := kerCost N sIn N + 5
  BlA := Sims.liftCost N sIn m + 7
  Bg1₁ := genCost N (2 * (m * m + m) + N * N) + 2
  Bg1₂ₐ := genCost N (2 * (m * m + m) + N * N) + 2
  Bg1₂ᵦ := genCost N (2 * (m * m + m) + N * N) + 2
  Bg1₃ := genCost N (2 * (m * m + m) + N * N) + 2
  Bgen₂ₐ := genCost N (sIn + 1) + 2
  Bgen₂ᵦ := genCost N (c2bRU m * (sIn + 1)) + 2
  Bgen₃ := genCost N (Case3.c3R k m (Case2b.sojZ m) * (sIn + 1)) + 2
  Bpb := genCost N ((sIn + 1) * (sIn + 1) + sIn + sIn) + 2
  sK := N * N
  Bgm := genCost N sIn + 2
  Blift := Sims.liftCost N sIn N + 7
  Bker := kerCost N sIn N + 5
  Bgn := genCost N (N * N + s) + 2
  Bg := genCost m sIn + 2
  Bgk := genCost N (k.factorial * (sIn + 1)) + 2
  Bgs := genCost N (k + sIn) + 2
  Bk3 := kerCost N sIn N + 5
  Bo3 := orbitsCost N sIn N + 5
  Bcr3 := Sims.repsCost N sIn (N * N) m.factorial + 7
  Bgen3 := genCost N (m.factorial * (sIn + 1)) + 2
  BF := genCost N (2 * sIn) + 2

/-- The charge of the coloured Johnson routes' aligned group with Schreier–Sims. -/
def ssBg1J (N m : ℕ) : ℕ := genCost N (2 * (3 * (m * m)) + N * N) + 2

/-- **The restricted instance with Schreier–Sims** (`m5s_giant`, `rbHInst_valid`): the restricted
degree `|w| + m` is at most the parent's, the restricted generators are valid, the restricted
hinted instance is valid, and its base action is a giant. -/
theorem ss_m5_rb {xyP : StrData × StrData} {wP : WinData} {σP : PermData} {NP : ℕ}
    {gsP : GensData} {n₀ nP : ℕ} {LP : LabelData}
    (hIP : HInstValid ssDV
      (((xyP, (wP, (σP, (NP, gsP, ())))), (n₀, (nP, some LP))) : HInstData Ty.unit))
    {hBP : IsInvariant (GensData.denote NP gsP) (baseSet nP NP)}
    (haltP : alternatingGroup (Fin (NP - nP)) ≤ (baseHom (GensData.denote NP gsP) nP hBP).range)
    (hm : 4 ≤ NP - nP) :
    (rbPts nP NP wP).length ≤ NP ∧ (rbPts nP NP wP).length - wP.1.length = NP - nP ∧
      GensData.AllValid (rbPts nP NP wP).length (rbGens nP NP wP gsP) ∧
      ∃ hI' : HInstValid ssDV (rbHInst ssCtx.O xyP wP σP NP gsP n₀ nP LP),
        alternatingGroup (Fin ((rbPts nP NP wP).length - wP.1.length)) ≤
          (baseHom _ wP.1.length hI'.base_inv).range := by
  obtain ⟨⟨hwP, -, hgvP, hWP⟩, hleP, hBP', hwinP, -, -⟩ := id hIP
  change WinData.Valid NP wP at hwP
  change GroupValid (D := Ty.unit) ssDV NP gsP () at hgvP
  change IsInvariant (GensData.denote NP gsP) (wP.denote NP) at hWP
  change nP ≤ NP at hleP
  change IsInvariant (GensData.denote NP gsP) (baseSet nP NP) at hBP'
  change ∀ i ∈ wP.1, i < nP at hwinP
  have hwlen : wP.1.length ≤ nP := mf_length_le_of_nodup hwP.nodup hwinP
  have hlen : (rbPts nP NP wP).length = wP.1.length + (NP - nP) := rb_length
  have hUv := rb_valid (n := nP) hwP hwinP
  have hU := rb_inv (n := nP) hWP hBP'
  have hg'v := GensData.allValid_restrictTo hU hUv hgvP.1
  have hg'den := GensData.denote_restrictTo hU hUv hgvP.1
  have hOg : MeetsContractOn ssDV (· = .generate) ssCtx.O := fun op x _ hx => ssOracle_meets op x hx
  have hI' := rbHInst_valid (hB := hBP) hOg hIP haltP hm
  refine ⟨by omega, by omega, hg'v, hI', ?_⟩
  have hden : GensData.denote (rbU nP NP wP).1.length
      (generateModel (rbPts nP NP wP).length (rbGens nP NP wP gsP)) =
      (restrictHom hU (WinData.reindex hUv)).range :=
    (generateModel_spec hg'v).2.1.trans hg'den
  exact m5s_giant hUv hU hwinP hBP' haltP hden hI'.base_inv

end Bounds



/-! ### The leaves' generators, by their size -/

section LeafGens

theorem pairsD_length_le (l : List ℕ) : (Align.pairsD l).length ≤ l.length * l.length := by
  unfold Align.pairsD
  rw [List.length_flatMap]
  calc (l.map fun a => ((l.filter fun b => b != a).map fun b => (a, b)).length).sum
      ≤ (l.map fun _ => l.length).sum := List.sum_le_sum fun a _ => by
        rw [List.length_map]
        exact List.length_filter_le _ _
    _ = l.length * l.length := by rw [List.map_const', List.sum_replicate, smul_eq_mul]

theorem cells_pairs_le {m B : ℕ} {d : JData} (h : JBound B d) :
    (d.2.1.map fun c => ((Align.pairsD c).map fun p => swapPD m p.1 p.2).length).sum ≤
      B * (B * B) := by
  calc (d.2.1.map fun c => ((Align.pairsD c).map fun p => swapPD m p.1 p.2).length).sum
      ≤ (d.2.1.map fun _ => B * B).sum := List.sum_le_sum fun c hc => by
        rw [List.length_map]
        exact (pairsD_length_le c).trans (Nat.mul_le_mul (h.cell c hc) (h.cell c hc))
    _ = d.2.1.length * (B * B) := by rw [List.map_const', List.sum_replicate, smul_eq_mul]
    _ ≤ B * (B * B) := Nat.mul_le_mul_right _ h.k

theorem cellSwaps_le {B : ℕ} {d : JData} (h : JBound B d) (f : ℕ → ℕ → PermData)
    (q : ℕ → ℕ → Bool) :
    ((List.range d.2.1.length).map fun i =>
      (((List.range d.2.1.length).filter (q i)).map (f i)).length).sum ≤ B * B := by
  calc ((List.range d.2.1.length).map fun i =>
        (((List.range d.2.1.length).filter (q i)).map (f i)).length).sum
      ≤ ((List.range d.2.1.length).map fun _ => B).sum := List.sum_le_sum fun i _ => by
        rw [List.length_map]
        exact (List.length_filter_le _ _).trans (by rw [List.length_range]; exact h.k)
    _ = d.2.1.length * B := by
        rw [List.map_const', List.sum_replicate, smul_eq_mul, List.length_range]
    _ ≤ B * B := Nat.mul_le_mul_right _ h.k

theorem jrest_length_le (m : ℕ) (d : JData) : (jrest m d).length ≤ m :=
  (List.length_filter_le _ _).trans (by simp)

/-- **A Johnson structure's generators, by its size**, whatever its validity. -/
theorem johnGensD_length_le_bound {m B : ℕ} {d : JData} (h : JBound B d) :
    (johnGensD m d).length ≤ B * (B * B) + m * m + B * B := by
  unfold johnGensD
  rw [List.length_append, List.length_append, List.length_flatMap, List.length_flatMap,
    List.length_map]
  have h2 : (Align.pairsD (jrest m d)).length ≤ m * m :=
    (pairsD_length_le _).trans (Nat.mul_le_mul (jrest_length_le m d) (jrest_length_le m d))
  have h1 := cells_pairs_le (m := m) h
  have h3 := cellSwaps_le h (fun i j => cellSwapPD m d i j)
    (fun i j => i != j && (d.2.1.getD i []).length == (d.2.1.getD j []).length)
  omega

/-- **A coloured Johnson structure's generators, by its size.** -/
theorem cjohnGensD_length_le_bound {m B : ℕ} {e : CJData} (h : JBound B e.1) :
    (cjohnGensD m e).length ≤ B * (B * B) + m * m + B * B := by
  unfold cjohnGensD
  rw [List.length_append, List.length_append, List.length_flatMap, List.length_flatMap,
    List.length_map]
  have h2 : (cjRestPairs m e).length ≤ m * m :=
    (List.length_filter_le _ _).trans ((pairsD_length_le _).trans
      (Nat.mul_le_mul (jrest_length_le m e.1) (jrest_length_le m e.1)))
  have h1 := cells_pairs_le (m := m) h
  have h3 := cellSwaps_le h (fun i j => cellSwapPD m e.1 i j)
    (fun i j => i != j && (e.1.2.1.getD i []).length == (e.1.2.1.getD j []).length)
  omega

/-- **A leaf's generators, by its size.** -/
theorem outGensD_length_le_bound {m B : ℕ} {o : SoJTree.OutD} (h : SoJTree.outSize o ≤ B) :
    (Case2b.outGensD m o).length ≤ m * m + m + (B * (B * B) + m * m + B * B) := by
  unfold Case2b.outGensD
  split_ifs
  · have := partGensD_length_le m o.2.1
    omega
  · have := johnGensD_length_le_bound (m := m) (Case2b.cp2_jbound_le h)
    omega
  · simp

end LeafGens


/-! ### The work of M5 -/

section Work

/-- **M5's dispatch work as a function of its data**: the sum of every case's work (`m5WCJ`), at
the data `g` (the generators of `G`), `P₁`, `P₂` (the generators of Case 1's partition and Case
2a's set), `nΦ` (Case 2a's orbit), `mx`, `my` (Case 3's fixed points), `R`, `K` (the kernel's
representatives and generators), `nx`, `ny`, `j` (Case 2b's orbits and degree) and `cl`, `ol`
(the generators of Case 2b's leaf, as a coloured Johnson pair or as a leaf). -/
def m5DispNum (n N k s sIn Bgen Blift Bo Bk Bcr Bd wl : ℕ) (β : M5Bounds)
    (Bst Btr Borb Bkg Bko Bks : ℕ) (Bo' Bs' Bt' : ℕ → ℕ) (uB Bg1J₂ Bg1J₃ : ℕ)
    (g P₁ P₂ nΦ mx my R K nx ny j cl ol : ℕ) : ℕ :=
  (Giant.case1Cost n N g P₁ β.Box β.Boy β.BgP β.Bmem β.BkA β.BlA β.Bg1₁ Bgen
    (m5Wb N n wl s sIn (N - n) Bd Blift Bgen Bo 0) sIn + 16) +
  (c2aWork n N g P₂ nΦ β.BgP β.Bmem β.BkA β.BlA β.Bg1₂ₐ β.Bgen₂ₐ sIn Bst Borb β.Bpb wl s
    β.sK β.Bgm β.Blift β.Bker β.Bgn + 30) +
  (c3Work n N sIn g k mx my (Case2b.sojZ (N - n)) β.BgP β.Bmem β.BkA β.BlA β.Bg1₃
      β.Bgen₃ Bst Btr Borb Bkg Bko Bks β.Bgk β.Bgs wl
      (m5Wb N n wl s sIn (N - n).factorial Bd Blift Bgen Bo
        (rd6Cost N n wl s sIn Bk Bo Bcr Bgen)) +
    (kerRedCost N n wl R K s β.Bk3 β.Bo3 β.Bcr3 β.Bgen3 + 5) + wl + 3 +
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
        β.BlA β.Bg1₂ᵦ β.Bgen₂ᵦ
        (m5Wb N n wl s sIn (N - n).factorial Bd Blift Bgen Bo
          (rd6Cost N n wl s sIn Bk Bo Bcr Bgen)) Bo' Bs' Bt') + 28) + 28

/-- **The dispatch's work is at most `m5DispNum` at its data.** -/
theorem m5WCJ_le {D : Ty} (O : Oracle (groupSig D)) (n N k s sIn Bgen Blift Bo Bk Bcr Bd : ℕ)
    (G Fx Fy : GroupData D.denote) (wl : ℕ) (β : M5Bounds) (Bst Btr Borb Bkg Bko Bks : ℕ)
    (Bo' Bs' Bt' : ℕ → ℕ) (uB Bg1J₂ Bg1J₃ : ℕ) :
    m5WCJ O n N k s sIn Bgen Blift Bo Bk Bcr Bd G Fx Fy wl β Bst Btr Borb Bkg Bko Bks Bo' Bs'
        Bt' uB Bg1J₂ Bg1J₃ ≤
      m5DispNum n N k s sIn Bgen Blift Bo Bk Bcr Bd wl β Bst Btr Borb Bkg Bko Bks Bo' Bs' Bt' uB
        Bg1J₂ Bg1J₃ G.2.1.length (partGensD (N - n) (Giant.orbitPartModel O n N Fx)).length
        ((setOps (N - n)).gens (m5Cs O n N Fx).2).length (m5Cs O n N Fx).2.length
        (fixPtsD (m5Os O n N Fx)).length (fixPtsD (m5Os O n N Fy)).length (kerReps O n G).length
        (kerModel O n G).2.1.length (m5Cs O n N Fx).2.length (m5Cs O n N Fy).2.length
        (Case2b.degD O N n Fx (m5Cs O n N Fx).2 - 1)
        (((m5Leaf2b O N n Fx (m5Cs O n N Fx).2).map fun X₀ =>
          (cjohnGensD (N - n) (cjFirst2bD N n (m5Cs O n N Fx).2
            (Case2b.degD O N n Fx (m5Cs O n N Fx).2 - 1) X₀)).length).getD 0)
        (((m5Leaf2b O N n Fx (m5Cs O n N Fx).2).map fun X₀ =>
          (Case2b.outGensD (N - n) X₀).length).getD 0) := by
  unfold m5WCJ m5DispNum
  split
  · omega
  · omega
  · omega
  · rcases hX : m5Leaf2b O N n Fx (m5Cs O n N Fx).2 with _ | X₀
    · simp only [Option.map_none, Option.getD_none]
      omega
    · simp only [Option.map_some, Option.getD_some]
      split_ifs <;> omega
  · omega


/-- The bound on the generators of Case 2b's first leaf, for base size `m`, as a coloured
Johnson pair (`cjB`) and as a leaf (`olB`): the leaf has size at most `leafB m`. -/
def cjB (m : ℕ) : ℕ := Case2b.leafB m * (Case2b.leafB m * Case2b.leafB m) + m * m +
  Case2b.leafB m * Case2b.leafB m

/-- See `cjB`. -/
def olB (m : ℕ) : ℕ := m * m + m + cjB m

/-- **M5's work with Schreier–Sims at given sizes**: the certificates, the two case decisions
(at the worst orbit size `a ≤ m`), and the envelope of the dispatch's work over its data, for
`n` string positions, base size `m` (degree `n + m`), certificate size `k`, a window of `p`
points, sub-solver answers of at most `s` generators, `sIn`, `Lg` and `uB`. -/
def m5WorkRaw (n m k p s sIn Lg uB : ℕ) : ℕ :=
  2 * (certCount (n + m) n k * 4 +
      certWork (n + m) n k sIn (stabCost (n + m) sIn + 5) (transCost (n + m) sIn + 5)
        (orbitsCost (n + m) sIn (n + m) + 5) (genCost k (k * (sIn + 1)) + 2)
        (orbitsCost k sIn k + 5) (stabCost k sIn + 5) (ssM5β (n + m) m k sIn s).Bgk
        (ssM5β (n + m) m k sIn s).BlA (ssM5β (n + m) m k sIn s).Bgs
        (ssM5β (n + m) m k sIn s).BF) +
    2 * supTo (fun a => m5CaseCost n (n + m) (orbitsCost (n + m) sIn (n + m) + 5)
      (Case2b.degCost (n + m) n a a sIn (stabCost (n + m) sIn + 5) (ssM5β (n + m) m k sIn s).Bg
        (orbitsCost a (a * a) a + 5) (stabCost a (a * a) + 5))) m +
    envSup [sIn, m * m + m, m * m + m, m, m, m, m.factorial, (n + m) * (n + m), m, m, m, cjB m,
        olB m] (fun ds =>
      m5DispNum n (n + m) k s sIn (genCost (n + m) Lg + 2) (Sims.liftCost (n + m) sIn n + 7)
        (orbitsCost (n + m) sIn (n + m) + 5) (kerCost (n + m) sIn (n + m) + 5)
        (Sims.repsCost (n + m) sIn ((n + m) * (n + m)) m.factorial + 7)
        (ssBdF n (n + m) p sIn + ssBdJ n (n + m) p p sIn) p (ssM5β (n + m) m k sIn s)
        (stabCost (n + m) sIn + 5) (transCost (n + m) sIn + 5)
        (orbitsCost (n + m) sIn (n + m) + 5) (genCost k (k * (sIn + 1)) + 2)
        (orbitsCost k sIn k + 5) (stabCost k sIn + 5) (fun M => orbitsCost M (M * M) M + 5)
        (fun M => stabCost M (M * M) + 5) (fun M => transCost M (M * M) + 5) uB
        (ssBg1J (n + m) m) (ssBg1J (n + m) m) (ds.getD 0 0) (ds.getD 1 0) (ds.getD 2 0)
        (ds.getD 3 0) (ds.getD 4 0) (ds.getD 5 0) (ds.getD 6 0) (ds.getD 7 0) (ds.getD 8 0)
        (ds.getD 9 0) (ds.getD 10 0) (ds.getD 11 0) (ds.getD 12 0)) + 15

/-- **The work of M5 with Schreier–Sims**: the monotone envelope of `m5WorkRaw`. -/
def m5WorkSS (n m k p s sIn Lg uB : ℕ) : ℕ :=
  envSup [n, m, k, p, s, sIn, Lg, uB] fun xs =>
    m5WorkRaw (xs.getD 0 0) (xs.getD 1 0) (xs.getD 2 0) (xs.getD 3 0) (xs.getD 4 0)
      (xs.getD 5 0) (xs.getD 6 0) (xs.getD 7 0)

theorem m5WorkSS_mono {n n' m m' k k' p p' s s' sIn sIn' Lg Lg' uB uB' : ℕ} (hn : n ≤ n')
    (hm : m ≤ m') (hk : k ≤ k') (hp : p ≤ p') (hs : s ≤ s') (hI : sIn ≤ sIn') (hg : Lg ≤ Lg')
    (hu : uB ≤ uB') :
    m5WorkSS n m k p s sIn Lg uB ≤ m5WorkSS n' m' k' p' s' sIn' Lg' uB' :=
  envSup_mono (.cons hn (.cons hm (.cons hk (.cons hp (.cons hs (.cons hI (.cons hg
    (.cons hu .nil)))))))) _

theorem le_m5WorkSS (n m k p s sIn Lg uB : ℕ) :
    m5WorkRaw n m k p s sIn Lg uB ≤ m5WorkSS n m k p s sIn Lg uB := by
  unfold m5WorkSS
  refine le_of_eq_of_le ?_ (le_envSup (forall₂_le_refl _) _)
  simp only [List.getD_cons_zero, List.getD_cons_succ]

/-- **M5's core work with Schreier–Sims is at most `m5WorkRaw`**, given the bounds on its data:
the generators of `G`, the large orbits, the fixed points, the kernel and the first leaf. -/
theorem m5CoreWorkCJ_le {n m k s sIn Lg uB : ℕ} {G Fx Fy : GroupData Unit} {p : ℕ}
    (hg : G.2.1.length ≤ sIn) (hΦx : (m5Cs ssCtx.O n (n + m) Fx).2.length ≤ m)
    (hΦy : (m5Cs ssCtx.O n (n + m) Fy).2.length ≤ m)
    (hmx : (fixPtsD (m5Os ssCtx.O n (n + m) Fx)).length ≤ m)
    (hmy : (fixPtsD (m5Os ssCtx.O n (n + m) Fy)).length ≤ m)
    (hR : (kerReps ssCtx.O n G).length ≤ m.factorial)
    (hK : (kerModel ssCtx.O n G).2.1.length ≤ (n + m) * (n + m)) :
    m5CoreWorkCJ ssCtx.O n (n + m) k s sIn (genCost (n + m) Lg + 2)
        (Sims.liftCost (n + m) sIn n + 7) (orbitsCost (n + m) sIn (n + m) + 5)
        (kerCost (n + m) sIn (n + m) + 5)
        (Sims.repsCost (n + m) sIn ((n + m) * (n + m)) m.factorial + 7)
        (ssBdF n (n + m) p sIn + ssBdJ n (n + m) p p sIn) G Fx Fy p (ssM5β (n + m) m k sIn s)
        (stabCost (n + m) sIn + 5) (transCost (n + m) sIn + 5)
        (orbitsCost (n + m) sIn (n + m) + 5) (genCost k (k * (sIn + 1)) + 2)
        (orbitsCost k sIn k + 5) (stabCost k sIn + 5) (fun M => orbitsCost M (M * M) M + 5)
        (fun M => stabCost M (M * M) + 5) (fun M => transCost M (M * M) + 5) uB
        (ssBg1J (n + m) m) (ssBg1J (n + m) m) ≤ m5WorkRaw n m k p s sIn Lg uB := by
  have hm : n + m - n = m := by omega
  have hdisp := m5WCJ_le ssCtx.O n (n + m) k s sIn (genCost (n + m) Lg + 2)
    (Sims.liftCost (n + m) sIn n + 7) (orbitsCost (n + m) sIn (n + m) + 5)
    (kerCost (n + m) sIn (n + m) + 5)
    (Sims.repsCost (n + m) sIn ((n + m) * (n + m)) m.factorial + 7)
    (ssBdF n (n + m) p sIn + ssBdJ n (n + m) p p sIn) G Fx Fy p (ssM5β (n + m) m k sIn s)
    (stabCost (n + m) sIn + 5) (transCost (n + m) sIn + 5) (orbitsCost (n + m) sIn (n + m) + 5)
    (genCost k (k * (sIn + 1)) + 2) (orbitsCost k sIn k + 5) (stabCost k sIn + 5)
    (fun M => orbitsCost M (M * M) M + 5) (fun M => stabCost M (M * M) + 5)
    (fun M => transCost M (M * M) + 5) uB (ssBg1J (n + m) m) (ssBg1J (n + m) m)
  have hj : Case2b.degD ssCtx.O (n + m) n Fx (m5Cs ssCtx.O n (n + m) Fx).2 - 1 ≤ m :=
    (Nat.sub_le _ 1).trans ((degD_le _ _ _ _ _).trans (by omega))
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
  have henv := le_envSup (as := [sIn, m * m + m, m * m + m, m, m, m, m.factorial,
      (n + m) * (n + m), m, m, m, cjB m, olB m]) (.cons hg (.cons hP₁ (.cons hP₂ (.cons hΦx
      (.cons hmx (.cons hmy (.cons hR (.cons hK (.cons hΦx (.cons hΦy (.cons hj (.cons hcl
        (.cons hol .nil)))))))))))))
    (fun ds =>
      m5DispNum n (n + m) k s sIn (genCost (n + m) Lg + 2) (Sims.liftCost (n + m) sIn n + 7)
        (orbitsCost (n + m) sIn (n + m) + 5) (kerCost (n + m) sIn (n + m) + 5)
        (Sims.repsCost (n + m) sIn ((n + m) * (n + m)) m.factorial + 7)
        (ssBdF n (n + m) p sIn + ssBdJ n (n + m) p p sIn) p (ssM5β (n + m) m k sIn s)
        (stabCost (n + m) sIn + 5) (transCost (n + m) sIn + 5)
        (orbitsCost (n + m) sIn (n + m) + 5) (genCost k (k * (sIn + 1)) + 2)
        (orbitsCost k sIn k + 5) (stabCost k sIn + 5) (fun M => orbitsCost M (M * M) M + 5)
        (fun M => stabCost M (M * M) + 5) (fun M => transCost M (M * M) + 5) uB
        (ssBg1J (n + m) m) (ssBg1J (n + m) m) (ds.getD 0 0) (ds.getD 1 0) (ds.getD 2 0)
        (ds.getD 3 0) (ds.getD 4 0) (ds.getD 5 0) (ds.getD 6 0) (ds.getD 7 0) (ds.getD 8 0)
        (ds.getD 9 0) (ds.getD 10 0) (ds.getD 11 0) (ds.getD 12 0))
  simp only [List.getD_cons_zero, List.getD_cons_succ] at henv
  have hdx : m5DecCost ssCtx.O n (n + m) sIn (stabCost (n + m) sIn + 5)
      (orbitsCost (n + m) sIn (n + m) + 5) (ssM5β (n + m) m k sIn s).Bg
      (fun M => orbitsCost M (M * M) M + 5) (fun M => stabCost M (M * M) + 5) Fx ≤
      supTo (fun a => m5CaseCost n (n + m) (orbitsCost (n + m) sIn (n + m) + 5)
        (Case2b.degCost (n + m) n a a sIn (stabCost (n + m) sIn + 5) (ssM5β (n + m) m k sIn s).Bg
          (orbitsCost a (a * a) a + 5) (stabCost a (a * a) + 5))) m :=
    le_supTo (f := fun a => m5CaseCost n (n + m) (orbitsCost (n + m) sIn (n + m) + 5)
      (Case2b.degCost (n + m) n a a sIn (stabCost (n + m) sIn + 5) (ssM5β (n + m) m k sIn s).Bg
        (orbitsCost a (a * a) a + 5) (stabCost a (a * a) + 5))) hΦx
  have hdy : m5DecCost ssCtx.O n (n + m) sIn (stabCost (n + m) sIn + 5)
      (orbitsCost (n + m) sIn (n + m) + 5) (ssM5β (n + m) m k sIn s).Bg
      (fun M => orbitsCost M (M * M) M + 5) (fun M => stabCost M (M * M) + 5) Fy ≤
      supTo (fun a => m5CaseCost n (n + m) (orbitsCost (n + m) sIn (n + m) + 5)
        (Case2b.degCost (n + m) n a a sIn (stabCost (n + m) sIn + 5) (ssM5β (n + m) m k sIn s).Bg
          (orbitsCost a (a * a) a + 5) (stabCost a (a * a) + 5))) m :=
    le_supTo (f := fun a => m5CaseCost n (n + m) (orbitsCost (n + m) sIn (n + m) + 5)
      (Case2b.degCost (n + m) n a a sIn (stabCost (n + m) sIn + 5) (ssM5β (n + m) m k sIn s).Bg
        (orbitsCost a (a * a) a + 5) (stabCost a (a * a) + 5))) hΦy
  unfold m5CoreWorkCJ m5WorkRaw
  omega

end Work

/-! ### The charges of M5

Every backend hypothesis of `RunsWithin.m5StepCJProg_jp` at `ssCtx` with `ssM5β`, stated on a
restricted instance `(N, gs)` with string positions `[0, n)`, window `w`, labels `L` and
certificate size `k`. Each needs only the facts it names: validity of `gs`, at most `sIn` of them,
`N * N ≤ sIn`, the invariant base and, for the Johnson routes, the giant base action. The step
`RunsWithin.m5StepCJProg_ss₀` invokes them; the variant without stuck orbits can reuse them. -/

section Charges

variable {N n k sIn s : ℕ} {gs : GensData} {xy : StrData × StrData} {w : WinData}
  {L : LabelData} {st : ℕ × CJData} {a b : Ty}
  {body : a.denote → Prog (groupSig Ty.unit) (a, b) Ty.denote b}
  {NP nP n₀ : ℕ} {wP : WinData} {gsP : GensData} {xyP : StrData × StrData} {σP : PermData}
  {LP : LabelData}

/-- A full group of M5 keeps the base invariant. -/
theorem M5Full.base_inv {N n k sIn : ℕ} {gs : GensData} {hC : CertSetting (GensData.denote N gs) n}
    {φ : strGroup hC →* Perm (Fin (N - n))} {x : StrData} {fs : GensData} {e : Ty.unit.denote}
    (h : M5Full (D := Ty.unit) ssDV hC φ k sIn x fs e) :
    IsInvariant (GensData.denote N fs) (baseSet n N) := by
  rw [h.2.2]
  exact m5Fmap_base hC φ k _

/-- The base action's `generate` (`hBgP`). -/
theorem ss_m5_hBgP (hgsl : gs.length ≤ sIn) :
    ssCtx.B.call GroupOp.generate (N - n, gs.map (baseD n N)) (ssCtx.O.run GroupOp.generate (N - n,
      gs.map (baseD n N))) ≤ (ssM5β N (N - n) k sIn s).BgP :=
  ssB_generate_le le_rfl (by rw [List.length_map]; exact hgsl) _

/-- The base group's `mem` (`hBmem`). -/
theorem ss_m5_hBmem (hgsv : GensData.AllValid N gs) (hG : IsInvariant (GensData.denote N gs)
    (baseSet n N)) :
    ∀ g : PermData, g.Valid (N - n) → ssCtx.B.call GroupOp.mem (pModel ssCtx.O n (N, gs, ()), g)
      (ssCtx.O.run GroupOp.mem (pModel ssCtx.O n (N, gs, ()), g)) ≤ (ssM5β N (N - n) k sIn s).Bmem
      := by
  intro g _
  have hl := (generateModel_spec (allValid_baseGens hG hgsv)).2.2
  change memCost (N - n) (generateModel (N - n) (gs.map (baseD n N))).length + 5 ≤
    memCost (N - n) ((N - n) * (N - n)) + 5
  unfold memCost
  gcongr

/-- The lifts from the base (`hBlA`). -/
theorem ss_m5_hBlA (hgsl : gs.length ≤ sIn) :
    ∀ π : PermData, ssCtx.B.call GroupOp.lift ((N, gs, ()), (baseWin n N, π)) (liftModel ssCtx.O n
      (N, gs, ()) π) ≤ (ssM5β N (N - n) k sIn s).BlA := by
  intro π
  change Sims.liftCost N gs.length (baseWin n N).1.length + 7 ≤ _
  rw [baseWin_length]
  exact Nat.add_le_add_right (rd_liftCost_mono₂ le_rfl hgsl le_rfl) 7

/-- `generate` at the base's degrees (`hBg`). -/
theorem ss_m5_hBg :
    ∀ M ≤ N - n, ∀ gs' : GensData, GensData.AllValid M gs' → gs'.length ≤ sIn → ssCtx.B.call
      GroupOp.generate (M, gs') (ssCtx.O.run GroupOp.generate (M, gs')) ≤ (ssM5β N (N - n) k sIn
      s).Bg :=
  fun _ hM _ _ hl => ssB_generate_le hM hl _

/-- The certificates' `generate` (`hBgk`). -/
theorem ss_m5_hBgk :
    ∀ gs' : GensData, GensData.AllValid N gs' → gs'.length ≤ k.factorial * (sIn + 1) →
      GensData.denote N gs' ≤ GensData.denote N gs → ssCtx.B.call GroupOp.generate (N, gs')
      (ssCtx.O.run GroupOp.generate (N, gs')) ≤ (ssM5β N (N - n) k sIn s).Bgk :=
  fun _ _ hl _ => ssB_generate_le le_rfl hl _

/-- The giant set stabilizers' `generate` (`hBgs`). -/
theorem ss_m5_hBgs (hNs : N * N ≤ sIn) (hgsv : GensData.AllValid N gs) (hgsl : gs.length ≤ sIn) :
    ∀ al : List ℕ, al.Nodup → al.length = k → (∀ a ∈ al, a < N - n) → ∀ b₁ b₂, ssCtx.B.call
      GroupOp.generate (N, giantGens ssCtx.O n (N, gs, ()) al b₁ b₂) (giantSetStabModel ssCtx.O n
      (N, gs, ()) al b₁ b₂) ≤ (ssM5β N (N - n) k sIn s).Bgs := by
  intro al _ hal hlt b₁ b₂
  exact ssB_generate_le le_rfl ((ss_giantGens_le hNs hgsv hgsl hlt b₁ b₂).trans
    (by rw [hal])) _

/-- The full group's `generate` (`hBF`). -/
theorem ss_m5_hBF :
    ∀ gs' : GensData, GensData.AllValid N gs' → gs'.length ≤ 2 * sIn → GensData.denote N gs' ≤
      GensData.denote N gs → ssCtx.B.call GroupOp.generate (N, gs') (ssCtx.O.run GroupOp.generate
      (N, gs')) ≤ (ssM5β N (N - n) k sIn s).BF :=
  fun _ _ hl _ => ssB_generate_le le_rfl hl _

/-- The kernel reduction's `generate` in M5's fallback (`hB3`). -/
theorem ss_m5_hB3 (hgsv : GensData.AllValid N gs) (hG : IsInvariant (GensData.denote N gs) (baseSet
    n N)) (hs : s ≤ sIn) (hNs : N * N ≤ sIn) :
    ∀ hs : GensData, GensData.AllValid N hs → hs.length ≤ (kerReps ssCtx.O n (N, gs, ())).length *
      (max s (kerModel ssCtx.O n (N, gs, ())).2.1.length + 1) → GensData.denote N hs ≤
      GensData.denote N gs → ssCtx.B.call GroupOp.generate (N, hs) (ssCtx.O.run GroupOp.generate (N,
      hs)) ≤ (ssM5β N (N - n) k sIn s).Bgen3 := by
  intro hs' _ hl _
  have hkerl : (kerModel ssCtx.O n (N, gs, ())).2.1.length ≤ N * N :=
    ss_kernel_gens_le hgsv (baseWin_valid n N)
  have hr := ss_kerReps_le hgsv hG
  exact ssB_generate_le le_rfl (hl.trans (Nat.mul_le_mul hr (by
    have := max_le hs (hkerl.trans hNs)
    omega))) _

/-- Case 1: the full group's base orbits for `x` (`hBox`). -/
theorem ss_m5_hBox :
    ∀ (hC : CertSetting (GensData.denote N gs) n) (φ : strGroup hC →* Perm (Fin (N - n))), IsPhi hC
      φ → ∀ fs e, M5Full (D := Ty.unit) ssDV hC φ k sIn xy.1 fs e → ssCtx.B.call GroupOp.orbits ((N,
      fs, e), baseWin n N) (Giant.baseOrbits ssCtx.O n N (N, fs, e)) ≤ (ssM5β N (N - n) k sIn s).Box
      := by
  intro hC φ hφ fs e hF
  change orbitsCost N fs.length (baseWin n N).1.length + 5 ≤ _
  rw [baseWin_length]
  exact Nat.add_le_add_right (rd_orbitsCost_mono₂ le_rfl hF.2.1 le_rfl) 5

/-- Case 1: the full group's base orbits for `y` (`hBoy`). -/
theorem ss_m5_hBoy :
    ∀ (hC : CertSetting (GensData.denote N gs) n) (φ : strGroup hC →* Perm (Fin (N - n))), IsPhi hC
      φ → ∀ fs e, M5Full (D := Ty.unit) ssDV hC φ k sIn xy.2 fs e → ssCtx.B.call GroupOp.orbits ((N,
      fs, e), baseWin n N) (Giant.baseOrbits ssCtx.O n N (N, fs, e)) ≤ (ssM5β N (N - n) k sIn s).Boy
      := by
  intro hC φ hφ fs e hF
  change orbitsCost N fs.length (baseWin n N).1.length + 5 ≤ _
  rw [baseWin_length]
  exact Nat.add_le_add_right (rd_orbitsCost_mono₂ le_rfl hF.2.1 le_rfl) 5

/-- Case 1: the aligned group's `generate` (`hBg1₁`). -/
theorem ss_m5_hBg1₁ (hgsv : GensData.AllValid N gs) :
    ∀ (hC : CertSetting (GensData.denote N gs) n) (φ : strGroup hC →* Perm (Fin (N - n))), IsPhi hC
      φ → ∀ fs e, M5Full (D := Ty.unit) ssDV hC φ k sIn xy.1 fs e → ssCtx.B.call GroupOp.generate
      (N, (stabInPL (flagsModel ssCtx.O (pModel ssCtx.O n (N, gs, ())) (partGensD (N - n)
      (Giant.orbitPartModel ssCtx.O n N (N, fs, e))))).map (liftModel ssCtx.O n (N, gs, ())) ++
      (kerModel ssCtx.O n (N, gs, ())).2.1) (preModel ssCtx.O n (N, gs, ()) (stabInPL (flagsModel
      ssCtx.O (pModel ssCtx.O n (N, gs, ())) (partGensD (N - n) (Giant.orbitPartModel ssCtx.O n N
      (N, fs, e)))))) ≤ (ssM5β N (N - n) k sIn s).Bg1₁ := by
  intro hC φ hφ fs e hF
  have hkerl : (kerModel ssCtx.O n (N, gs, ())).2.1.length ≤ N * N :=
    ss_kernel_gens_le hgsv (baseWin_valid n N)
  exact ssB_generate_le le_rfl ((aligned_length_le _ _ _ _ _).trans (by
    have := partGensD_length_le (N - n) (Giant.orbitPartModel ssCtx.O n N (N, fs, e))
    omega)) _

/-- Case 1: every orbit of reduce-and-derive (`hD₁`). -/
theorem ss_m5_hD₁ (hst : st.1 ≠ 2) (hNs : N * N ≤ sIn) {Bd : ℕ} (hBd : ssBdF n N w.1.length sIn ≤
    Bd) :
    ∀ (hC : CertSetting (GensData.denote N gs) n) (φ : strGroup hC →* Perm (Fin (N - n))), IsPhi hC
      φ → ∀ fs e, M5Full (D := Ty.unit) ssDV hC φ k sIn xy.1 fs e → ∀ gs' d' O', RDSet (D :=
      Ty.unit) ssDV n N gs w L (Giant.g1Model ssCtx.O n (N, gs, ()) (partOps (N - n))
      (Giant.orbitPartModel ssCtx.O n N (N, fs, e))).2.1 sIn gs' d' O' → RDOrbit ssCtx body ssDV n N
      w L st sIn Bd gs' d' O' := by
  intro hC φ hφ fs e hF gs' d' O' hset
  exact (rd_orbit_free_ssU hst hNs gs' d' O' hset).mono hBd

/-- Case 2a: the aligned group's `generate` (`hBg1₂ₐ`). -/
theorem ss_m5_hBg1₂ₐ (hgsv : GensData.AllValid N gs) :
    ∀ (hC : CertSetting (GensData.denote N gs) n) (φ : strGroup hC →* Perm (Fin (N - n))), IsPhi hC
      φ → ∀ fs e, M5Full (D := Ty.unit) ssDV hC φ k sIn xy.1 fs e → ssCtx.B.call GroupOp.generate
      (N, (stabInPL (flagsModel ssCtx.O (pModel ssCtx.O n (N, gs, ())) ((setOps (N - n)).gens (m5Cs
      ssCtx.O n N (N, fs, e)).2))).map (liftModel ssCtx.O n (N, gs, ())) ++ (kerModel ssCtx.O n (N,
      gs, ())).2.1) (Giant.g1Model ssCtx.O n (N, gs, ()) (setOps (N - n)) (m5Cs ssCtx.O n N (N, fs,
      e)).2) ≤ (ssM5β N (N - n) k sIn s).Bg1₂ₐ := by
  intro hC φ hφ fs e hF
  have hkerl : (kerModel ssCtx.O n (N, gs, ())).2.1.length ≤ N * N :=
    ss_kernel_gens_le hgsv (baseWin_valid n N)
  exact ssB_generate_le le_rfl ((aligned_length_le _ _ _ _ _).trans (by
    have : ((setOps (N - n)).gens (m5Cs ssCtx.O n N (N, fs, e)).2).length ≤
        (N - n) * (N - n) + (N - n) := partGensD_length_le _ _
    omega)) _

/-- Case 2a: `generate` on the pullback's generators (`hBgen₂ₐ`). -/
theorem ss_m5_hBgen₂ₐ :
    ∀ gs' : GensData, GensData.AllValid N gs' → gs'.length ≤ sIn + 1 → GensData.denote N gs' ≤
      GensData.denote N gs → ssCtx.B.call GroupOp.generate (N, gs') (ssCtx.O.run GroupOp.generate
      (N, gs')) ≤ (ssM5β N (N - n) k sIn s).Bgen₂ₐ :=
  fun _ _ hl _ => ssB_generate_le le_rfl hl _

/-- Case 2a: the pullback's `generate` (`hBpb`). -/
theorem ss_m5_hBpb :
    ∀ gs', GensData.AllValid N gs' → gs'.length ≤ (sIn + 1) * (sIn + 1) + sIn + sIn →
      GensData.denote N gs' ≤ ⊤ → ssCtx.B.call GroupOp.generate (N, gs') (ssCtx.O.run
      GroupOp.generate (N, gs')) ≤ (ssM5β N (N - n) k sIn s).Bpb :=
  fun _ _ hl _ => ssB_generate_le le_rfl hl _

/-- Case 2a: the restricted sub-instances' `generate` (`hBgm`). -/
theorem ss_m5_hBgm :
    ∀ (w' : WinData) (σ' : PermData) (gs' : GensData) (d' : Ty.unit.denote), Giant.PbSubP (D :=
      Ty.unit) ssDV (⊤ : Subgroup (Perm (Fin N))) xy w.1.length sIn (xy, w', σ', N, gs', d') →
      ssCtx.B.call GroupOp.generate (w'.1.length, GensData.restrictTo (WinData.pos N w') w'.1 gs')
      (ssCtx.O.run GroupOp.generate (w'.1.length, GensData.restrictTo (WinData.pos N w') w'.1 gs'))
      ≤ (ssM5β N (N - n) k sIn s).Bgm := by
  rintro w' σ' gs' d' ⟨-, hv, hdeg, -, hgl, -⟩
  have hw' : w'.Valid N := hv.win
  exact ssB_generate_le (WinData.length_le hw')
    (by unfold GensData.restrictTo; rw [List.length_map]; exact hgl) _

/-- Case 2a: the sub-instances' lifts (`hBlift`). -/
theorem ss_m5_hBlift :
    ∀ (w' : WinData) (σ' : PermData) (gs' : GensData) (d' : Ty.unit.denote), Giant.PbSubP (D :=
      Ty.unit) ssDV (⊤ : Subgroup (Perm (Fin N))) xy w.1.length sIn (xy, w', σ', N, gs', d') → ∀ π'
      : PermData, ssCtx.B.call GroupOp.lift ((N, gs', d'), (w', π')) (ssCtx.O.run GroupOp.lift ((N,
      gs', d'), (w', π'))) ≤ (ssM5β N (N - n) k sIn s).Blift := by
  rintro w' σ' gs' d' ⟨-, hv, hdeg, -, hgl, -⟩ π'
  have hw' : w'.Valid N := hv.win
  change Sims.liftCost N gs'.length w'.1.length + 7 ≤ _
  exact Nat.add_le_add_right (rd_liftCost_mono₂ le_rfl hgl (WinData.length_le hw')) 7

/-- Case 2a: the sub-instances' kernels (`hBker`). -/
theorem ss_m5_hBker :
    ∀ (w' : WinData) (σ' : PermData) (gs' : GensData) (d' : Ty.unit.denote), Giant.PbSubP (D :=
      Ty.unit) ssDV (⊤ : Subgroup (Perm (Fin N))) xy w.1.length sIn (xy, w', σ', N, gs', d') →
      ssCtx.B.call GroupOp.kernel ((N, gs', d'), w') (ssCtx.O.run GroupOp.kernel ((N, gs', d'), w'))
      ≤ (ssM5β N (N - n) k sIn s).Bker := by
  rintro w' σ' gs' d' ⟨-, hv, hdeg, -, hgl, -⟩
  have hw' : w'.Valid N := hv.win
  change kerCost N gs'.length w'.1.length + 5 ≤ _
  exact Nat.add_le_add_right (kerCost_mono₂ le_rfl hgl (WinData.length_le hw')) 5

/-- Case 2a: `generate` on the combined generators (`hBgn`). -/
theorem ss_m5_hBgn :
    ∀ hs : GensData, GensData.AllValid N hs → hs.length ≤ (ssM5β N (N - n) k sIn s).sK + s →
      GensData.denote N hs ≤ ⊤ → ssCtx.B.call GroupOp.generate (N, hs) (ssCtx.O.run GroupOp.generate
      (N, hs)) ≤ (ssM5β N (N - n) k sIn s).Bgn :=
  fun _ _ hl _ => ssB_generate_le le_rfl hl _

/-- Case 2b, partition leaves: the aligned group's `generate` (`hBg1₂ᵦ`). -/
theorem ss_m5_hBg1₂ᵦ (hgsv : GensData.AllValid N gs) :
    ∀ (hC : CertSetting (GensData.denote N gs) n) (φ : strGroup hC →* Perm (Fin (N - n))), IsPhi hC
      φ → ∀ fs e, M5Full (D := Ty.unit) ssDV hC φ k sIn xy.1 fs e → (m5Cs ssCtx.O n N (N, fs, e)).1
      = 2 → m5IsA ssCtx.O n N (N, fs, e) = false → ∀ X₀ : SoJTree.OutD, m5Leaf2b ssCtx.O N n (N, fs,
      e) (m5Cs ssCtx.O n N (N, fs, e)).2 = some X₀ → X₀.1 ≠ 2 → ssCtx.B.call GroupOp.generate (N,
      (stabInPL (flagsModel ssCtx.O (pModel ssCtx.O n (N, gs, ())) (Case2b.outGensD (N - n)
      X₀))).map (liftModel ssCtx.O n (N, gs, ())) ++ (kerModel ssCtx.O n (N, gs, ())).2.1) (preModel
      ssCtx.O n (N, gs, ()) (stabInPL (flagsModel ssCtx.O (pModel ssCtx.O n (N, gs, ()))
      (Case2b.outGensD (N - n) X₀)))) ≤ (ssM5β N (N - n) k sIn s).Bg1₂ᵦ := by
  intro hC φ hφ fs e hF _ _ X₀ _ hne
  have hkerl : (kerModel ssCtx.O n (N, gs, ())).2.1.length ≤ N * N :=
    ss_kernel_gens_le hgsv (baseWin_valid n N)
  exact ssB_generate_le le_rfl ((aligned_length_le _ _ _ _ _).trans (by
    have := outGensD_length_le (m := N - n) hne
    omega)) _

/-- Case 2b: `generate` over the leaves of `y` (`hBgen₂ᵦ`). -/
theorem ss_m5_hBgen₂ᵦ :
    ∀ (hC : CertSetting (GensData.denote N gs) n) (φ : strGroup hC →* Perm (Fin (N - n))), IsPhi hC
      φ → ∀ fs e, M5Full (D := Ty.unit) ssDV hC φ k sIn xy.2 fs e → ∀ gs' : GensData,
      GensData.AllValid N gs' → gs'.length ≤ Case2b.c2bR N n (m5Cs ssCtx.O n N (N, fs, e)).2.length
      (Case2b.degD ssCtx.O N n (N, fs, e) (m5Cs ssCtx.O n N (N, fs, e)).2 - 1) (Case2b.sojZ (N - n))
      * (sIn + 1) → GensData.denote N gs' ≤ GensData.denote N gs → ssCtx.B.call GroupOp.generate (N,
      gs') (ssCtx.O.run GroupOp.generate (N, gs')) ≤ (ssM5β N (N - n) k sIn s).Bgen₂ᵦ := by
  intro hC φ hφ fs e hF gs' _ hl _
  have hc := c2bR_le (ss_m5Cs_le (e := e) hF.1.1 hF.base_inv)
    ((Nat.sub_le _ 1).trans
      (degD_le ssCtx.O N n (N, fs, e) (m5Cs ssCtx.O n N (N, fs, e)).2))
  exact ssB_generate_le le_rfl (hl.trans (Nat.mul_le_mul_right _ hc)) _

/-- Case 2b: every orbit of reduce-and-derive (`hD₂ᵦ`). -/
theorem ss_m5_hD₂ᵦ (hst : st.1 ≠ 2) (hNs : N * N ≤ sIn) {Bd : ℕ} (hBd : ssBdF n N w.1.length sIn ≤
    Bd) :
    ∀ (hC : CertSetting (GensData.denote N gs) n) (φ : strGroup hC →* Perm (Fin (N - n))), IsPhi hC
      φ → ∀ fs e, M5Full (D := Ty.unit) ssDV hC φ k sIn xy.1 fs e → ∀ X₀, m5Leaf2b ssCtx.O N n (N,
      fs, e) (m5Cs ssCtx.O n N (N, fs, e)).2 = some X₀ → ∀ gs' d' O', RDSet (D := Ty.unit) ssDV n N
      gs w L (Giant.g1Model ssCtx.O n (N, gs, ()) (Case2b.outOps (N - n)) X₀).2.1 sIn gs' d' O' →
      RDOrbit ssCtx body ssDV n N w L st sIn Bd gs' d' O' := by
  intro hC φ hφ fs e hF X₀ _ gs' d' O' hset
  exact (rd_orbit_free_ssU hst hNs gs' d' O' hset).mono hBd

/-- Case 3, partition leaves: the aligned group's `generate` (`hBg1₃`). -/
theorem ss_m5_hBg1₃ (hgsv : GensData.AllValid N gs) :
    ∀ (hC : CertSetting (GensData.denote N gs) n) (φ : strGroup hC →* Perm (Fin (N - n))), IsPhi hC
      φ → ∀ fs e, M5Full (D := Ty.unit) ssDV hC φ k sIn xy.1 fs e → (m5Cs ssCtx.O n N (N, fs, e)).1
      ≠ 1 → (m5Cs ssCtx.O n N (N, fs, e)).1 ≠ 2 → ∀ X₀ : SoJTree.OutD, Case3.C3First φ (strOn hC.le
      (xy.1.denote N)) (N - n) k (fixPtsD (m5Os ssCtx.O n N (N, fs, e))) X₀ → X₀.1 ≠ 2 →
      ssCtx.B.call GroupOp.generate (N, (stabInPL (flagsModel ssCtx.O (pModel ssCtx.O n (N, gs, ()))
      (Case2b.outGensD (N - n) X₀))).map (liftModel ssCtx.O n (N, gs, ())) ++ (kerModel ssCtx.O n
      (N, gs, ())).2.1) (preModel ssCtx.O n (N, gs, ()) (stabInPL (flagsModel ssCtx.O (pModel
      ssCtx.O n (N, gs, ())) (Case2b.outGensD (N - n) X₀)))) ≤ (ssM5β N (N - n) k sIn s).Bg1₃ := by
  intro hC φ hφ fs e hF _ _ X₀ _ hne
  have hkerl : (kerModel ssCtx.O n (N, gs, ())).2.1.length ≤ N * N :=
    ss_kernel_gens_le hgsv (baseWin_valid n N)
  exact ssB_generate_le le_rfl ((aligned_length_le _ _ _ _ _).trans (by
    have := outGensD_length_le (m := N - n) hne
    omega)) _

/-- Case 3: `generate` over the leaves of `y` (`hBgen₃`). -/
theorem ss_m5_hBgen₃ :
    ∀ (hC : CertSetting (GensData.denote N gs) n) (φ : strGroup hC →* Perm (Fin (N - n))), IsPhi hC
      φ → ∀ fs e, M5Full (D := Ty.unit) ssDV hC φ k sIn xy.2 fs e → ∀ gs' : GensData,
      GensData.AllValid N gs' → gs'.length ≤ Case3.c3R k (fixPtsD (m5Os ssCtx.O n N (N, fs,
      e))).length (Case2b.sojZ (N - n)) * (sIn + 1) → GensData.denote N gs' ≤ GensData.denote N gs →
      ssCtx.B.call GroupOp.generate (N, gs') (ssCtx.O.run GroupOp.generate (N, gs')) ≤ (ssM5β N (N -
      n) k sIn s).Bgen₃ := by
  intro hC φ hφ fs e hF gs' _ hl _
  have hc := c3R_mono (k := k) (Z := Case2b.sojZ (N - n))
    (ss_fixPts_le (e := e) hF.1.1 hF.base_inv)
  exact ssB_generate_le le_rfl (hl.trans (Nat.mul_le_mul_right _ hc)) _

/-- Case 3: every orbit of reduce-and-derive (`hD₃`). -/
theorem ss_m5_hD₃ (hst : st.1 ≠ 2) (hNs : N * N ≤ sIn) {Bd : ℕ} (hBd : ssBdF n N w.1.length sIn ≤
    Bd) :
    ∀ (hC : CertSetting (GensData.denote N gs) n) (φ : strGroup hC →* Perm (Fin (N - n))), IsPhi hC
      φ → ∀ fs e, M5Full (D := Ty.unit) ssDV hC φ k sIn xy.1 fs e → ∀ X₀, Case3.C3First φ (strOn
      hC.le (xy.1.denote N)) (N - n) k (fixPtsD (m5Os ssCtx.O n N (N, fs, e))) X₀ → ∀ gs' d' O',
      RDSet (D := Ty.unit) ssDV n N gs w L (Giant.g1Model ssCtx.O n (N, gs, ()) (Case2b.outOps (N -
      n)) X₀).2.1 sIn gs' d' O' → RDOrbit ssCtx body ssDV n N w L st sIn Bd gs' d' O' := by
  intro hC φ hφ fs e hF X₀ _ gs' d' O' hset
  exact (rd_orbit_free_ssU hst hNs gs' d' O' hset).mono hBd

/-- Case 2b, Johnson leaves: the aligned group's `generate` (`hBg1J₂`). -/
theorem ss_m5_hBg1J₂ (hgsv : GensData.AllValid N gs) :
    ∀ (hC : CertSetting (GensData.denote N gs) n) (φ : strGroup hC →* Perm (Fin (N - n))), IsPhi hC
      φ → ∀ fs e, M5Full (D := Ty.unit) ssDV hC φ k sIn xy.1 fs e → (m5Cs ssCtx.O n N (N, fs, e)).1
      = 2 → m5IsA ssCtx.O n N (N, fs, e) = false → ∀ X₀ : SoJTree.OutD, m5Leaf2b ssCtx.O N n (N, fs,
      e) (m5Cs ssCtx.O n N (N, fs, e)).2 = some X₀ → X₀.1 = 2 → CJFacts (N - n) (cjFirst2bD N n
      (m5Cs ssCtx.O n N (N, fs, e)).2 (Case2b.degD ssCtx.O N n (N, fs, e) (m5Cs ssCtx.O n N (N, fs,
      e)).2 - 1) X₀) → ssCtx.B.call GroupOp.generate (N, (stabInPL (flagsModel ssCtx.O (pModel
      ssCtx.O n (N, gs, ())) (cjohnGensD (N - n) (cjFirst2bD N n (m5Cs ssCtx.O n N (N, fs, e)).2
      (Case2b.degD ssCtx.O N n (N, fs, e) (m5Cs ssCtx.O n N (N, fs, e)).2 - 1) X₀)))).map (liftModel
      ssCtx.O n (N, gs, ())) ++ (kerModel ssCtx.O n (N, gs, ())).2.1) (preModel ssCtx.O n (N, gs,
      ()) (stabInPL (flagsModel ssCtx.O (pModel ssCtx.O n (N, gs, ())) (cjohnGensD (N - n)
      (cjFirst2bD N n (m5Cs ssCtx.O n N (N, fs, e)).2 (Case2b.degD ssCtx.O N n (N, fs, e) (m5Cs
      ssCtx.O n N (N, fs, e)).2 - 1) X₀))))) ≤ ssBg1J N (N - n) := by
  intro hC φ hφ fs e hF _ _ X₀ _ _ hcj
  have hkerl : (kerModel ssCtx.O n (N, gs, ())).2.1.length ≤ N * N :=
    ss_kernel_gens_le hgsv (baseWin_valid n N)
  exact ssB_generate_le le_rfl ((aligned_length_le _ _ _ _ _).trans (by
    have := length_cjohnGensD_le hcj.1
    omega)) _

/-- Case 2b: the leaves of `y` within `Lg` (`hLY₂`). -/
theorem ss_m5_hLY₂ {Lg : ℕ} (hLY : c2bRU (N - n) * (sIn + 1) ≤ Lg) :
    ∀ (hC : CertSetting (GensData.denote N gs) n) (φ : strGroup hC →* Perm (Fin (N - n))), IsPhi hC
      φ → ∀ fs e, M5Full (D := Ty.unit) ssDV hC φ k sIn xy.2 fs e → Case2b.c2bR N n (m5Cs ssCtx.O n
      N (N, fs, e)).2.length (Case2b.degD ssCtx.O N n (N, fs, e) (m5Cs ssCtx.O n N (N, fs, e)).2 -
      1) (Case2b.sojZ (N - n)) * (sIn + 1) ≤ Lg := by
  intro hC φ hφ fs e hF
  have hc := c2bR_le (ss_m5Cs_le (e := e) hF.1.1 hF.base_inv)
    ((Nat.sub_le _ 1).trans
      (degD_le ssCtx.O N n (N, fs, e) (m5Cs ssCtx.O n N (N, fs, e)).2))
  exact (Nat.mul_le_mul_right _ hc).trans hLY

/-- Case 2b, Johnson leaves: every orbit of reduce-and-derive (`hDJ₂`). -/
theorem ss_m5_hDJ₂ (hNs : N * N ≤ sIn) (hgsv : GensData.AllValid N gs) (hgsl : gs.length ≤ sIn) (hG
    : IsInvariant (GensData.denote N gs) (baseSet n N)) (halt : alternatingGroup (Fin (N - n)) ≤
    (baseHom (GensData.denote N gs) n hG).range) {Bd : ℕ} (hBd : ssBdJ n N w.1.length L.size sIn ≤
    Bd) :
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
  exact (rd_orbit_cj_ssU (st := (2, _)) rfl hKb hcj.1 hJ hfix hNs gs' d' O' hset).mono hBd

/-- Case 2b, Johnson leaves: the union cell within `uB` (`hu₂`). -/
theorem ss_m5_hu₂ {uB : ℕ} (huB : N - n ≤ uB) :
    ∀ (hC : CertSetting (GensData.denote N gs) n) (φ : strGroup hC →* Perm (Fin (N - n))), IsPhi hC
      φ → ∀ fs e, M5Full (D := Ty.unit) ssDV hC φ k sIn xy.1 fs e → (m5Cs ssCtx.O n N (N, fs, e)).1
      = 2 → m5IsA ssCtx.O n N (N, fs, e) = false → ∀ X₀, m5Leaf2b ssCtx.O N n (N, fs, e) (m5Cs
      ssCtx.O n N (N, fs, e)).2 = some X₀ → X₀.1 = 2 → CJFacts (N - n) (cjFirst2bD N n (m5Cs ssCtx.O
      n N (N, fs, e)).2 (Case2b.degD ssCtx.O N n (N, fs, e) (m5Cs ssCtx.O n N (N, fs, e)).2 - 1) X₀)
      → ∀ gs' d' O', RDSet (D := Ty.unit) ssDV n N gs w L (Giant.g1Model ssCtx.O n (N, gs, ())
      (cjohnOps (N - n)) (cjFirst2bD N n (m5Cs ssCtx.O n N (N, fs, e)).2 (Case2b.degD ssCtx.O N n
      (N, fs, e) (m5Cs ssCtx.O n N (N, fs, e)).2 - 1) X₀)).2.1 sIn gs' d' O' → ((labJUD
      X₀.2.2.2.1.length (markArr (N - n) X₀.2.2.1) X₀.2.2.2.2.2 L O').getD (O'.headD 0) []).length ≤
      uB := by
  intro hC φ hφ fs e hF _ _ X₀ _ _ hcj gs' d' O' hset
  exact (ss_union_le hset.1.nodup hset.1.ne).trans ((ss_cells_le hcj.1).trans (by omega))

/-- Case 3, Johnson leaves: the aligned group's `generate` (`hBg1J₃`). -/
theorem ss_m5_hBg1J₃ (hgsv : GensData.AllValid N gs) :
    ∀ (hC : CertSetting (GensData.denote N gs) n) (φ : strGroup hC →* Perm (Fin (N - n))), IsPhi hC
      φ → ∀ fs e, M5Full (D := Ty.unit) ssDV hC φ k sIn xy.1 fs e → (m5Cs ssCtx.O n N (N, fs, e)).1
      ≠ 1 → (m5Cs ssCtx.O n N (N, fs, e)).1 ≠ 2 → ∀ cXX X₀, Case3.ColChar φ (strOn hC.le
      (xy.1.denote N)) (strOn hC.le (xy.1.denote N)) k (fixPtsD (m5Os ssCtx.O n N (N, fs,
      e))).length (fixPtsD (m5Os ssCtx.O n N (N, fs, e))) (fixPtsD (m5Os ssCtx.O n N (N, fs, e)))
      cXX → Case3.firstStructD (N - n) k (fixPtsD (m5Os ssCtx.O n N (N, fs, e))) (Case3.colXD cXX k
      (fixPtsD (m5Os ssCtx.O n N (N, fs, e))).length) = some X₀ → X₀.1 = 2 → CJFacts (N - n)
      (cjFirst3D (N - n) k (fixPtsD (m5Os ssCtx.O n N (N, fs, e))) (Case3.colXD cXX k (fixPtsD (m5Os
      ssCtx.O n N (N, fs, e))).length) X₀) → ssCtx.B.call GroupOp.generate (N, (stabInPL (flagsModel
      ssCtx.O (pModel ssCtx.O n (N, gs, ())) (cjohnGensD (N - n) (cjFirst3D (N - n) k (fixPtsD (m5Os
      ssCtx.O n N (N, fs, e))) (Case3.colXD cXX k (fixPtsD (m5Os ssCtx.O n N (N, fs, e))).length)
      X₀)))).map (liftModel ssCtx.O n (N, gs, ())) ++ (kerModel ssCtx.O n (N, gs, ())).2.1)
      (preModel ssCtx.O n (N, gs, ()) (stabInPL (flagsModel ssCtx.O (pModel ssCtx.O n (N, gs, ()))
      (cjohnGensD (N - n) (cjFirst3D (N - n) k (fixPtsD (m5Os ssCtx.O n N (N, fs, e))) (Case3.colXD
      cXX k (fixPtsD (m5Os ssCtx.O n N (N, fs, e))).length) X₀))))) ≤ ssBg1J N (N - n) := by
  intro hC φ hφ fs e hF _ _ cXX X₀ _ _ _ hcj
  have hkerl : (kerModel ssCtx.O n (N, gs, ())).2.1.length ≤ N * N :=
    ss_kernel_gens_le hgsv (baseWin_valid n N)
  exact ssB_generate_le le_rfl ((aligned_length_le _ _ _ _ _).trans (by
    have := length_cjohnGensD_le hcj.1
    omega)) _

/-- Case 3: the leaves of `y` within `Lg` (`hLY₃`). -/
theorem ss_m5_hLY₃ {Lg : ℕ} (hLY : Case3.c3R k (N - n) (Case2b.sojZ (N - n)) * (sIn + 1) ≤ Lg) :
    ∀ (hC : CertSetting (GensData.denote N gs) n) (φ : strGroup hC →* Perm (Fin (N - n))), IsPhi hC
      φ → ∀ fs e, M5Full (D := Ty.unit) ssDV hC φ k sIn xy.2 fs e → Case3.c3R k (fixPtsD (m5Os
      ssCtx.O n N (N, fs, e))).length (Case2b.sojZ (N - n)) * (sIn + 1) ≤ Lg := by
  intro hC φ hφ fs e hF
  have hc := c3R_mono (k := k) (Z := Case2b.sojZ (N - n))
    (ss_fixPts_le (e := e) hF.1.1 hF.base_inv)
  exact (Nat.mul_le_mul_right _ hc).trans hLY

/-- Case 3, Johnson leaves: every orbit of reduce-and-derive (`hDJ₃`). -/
theorem ss_m5_hDJ₃ (hNs : N * N ≤ sIn) (hgsv : GensData.AllValid N gs) (hgsl : gs.length ≤ sIn) (hG
    : IsInvariant (GensData.denote N gs) (baseSet n N)) (halt : alternatingGroup (Fin (N - n)) ≤
    (baseHom (GensData.denote N gs) n hG).range) {Bd : ℕ} (hBd : ssBdJ n N w.1.length L.size sIn ≤
    Bd) :
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
  exact (rd_orbit_cj_ssU (st := (2, _)) rfl hKb hcj.1 hJ hfix hNs gs' d' O' hset).mono hBd

/-- Case 3, Johnson leaves: the union cell within `uB` (`hu₃`). -/
theorem ss_m5_hu₃ {uB : ℕ} (huB : N - n ≤ uB) :
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
      O').getD (O'.headD 0) []).length ≤ uB := by
  intro hC φ hφ fs e hF _ _ cXX X₀ _ _ _ hcj gs' d' O' hset
  exact (ss_union_le hset.1.nodup hset.1.ne).trans ((ss_cells_le hcj.1).trans (by omega))

/-- The restriction: `generate` on the restricted generators (`hBgmR`). -/
theorem ss_m5_hBgmR (hgsP : gsP.length ≤ sIn) :
    ssCtx.B.call GroupOp.generate ((rbPts nP NP wP).length, rbGens nP NP wP gsP) (ssCtx.O.run
      GroupOp.generate ((rbPts nP NP wP).length, rbGens nP NP wP gsP)) ≤ genCost (rbPts nP NP
      wP).length sIn + 2 := by
  refine ssB_generate_le le_rfl ?_ _
  unfold rbGens GensData.restrictTo
  rw [List.length_map]
  exact hgsP

/-- The restriction: the lifts (`hBliftR`). -/
theorem ss_m5_hBliftR (hgsP : gsP.length ≤ sIn) (hNle : (rbPts nP NP wP).length ≤ NP) :
    ∀ π' : PermData, ssCtx.B.call GroupOp.lift ((NP, gsP, ()), (rbU nP NP wP, π')) (ssCtx.O.run
      GroupOp.lift ((NP, gsP, ()), (rbU nP NP wP, π'))) ≤ Sims.liftCost NP sIn NP + 7 := by
  intro π'
  change Sims.liftCost NP gsP.length (rbU nP NP wP).1.length + 7 ≤ _
  exact Nat.add_le_add_right (rd_liftCost_mono₂ le_rfl hgsP
    (by rw [rbU, WinData.ofPoints_fst]; exact hNle)) 7

/-- The restriction: the kernel (`hBkerR`). -/
theorem ss_m5_hBkerR (hgsP : gsP.length ≤ sIn) (hNle : (rbPts nP NP wP).length ≤ NP) :
    ssCtx.B.call GroupOp.kernel ((NP, gsP, ()), rbU nP NP wP) (ssCtx.O.run GroupOp.kernel ((NP, gsP,
      ()), rbU nP NP wP)) ≤ kerCost NP sIn NP + 5 := by
  change kerCost NP gsP.length (rbU nP NP wP).1.length + 5 ≤ _
  exact Nat.add_le_add_right (kerCost_mono₂ le_rfl hgsP
    (by rw [rbU, WinData.ofPoints_fst]; exact hNle)) 5

/-- The restriction: the kernel's generator count (`hsKR`). -/
theorem ss_m5_hsKR (hIP : HInstValid ssDV
      (((xyP, (wP, (σP, (NP, gsP, ())))), (n₀, (nP, some LP))) : HInstData Ty.unit)) :
    (ssCtx.O.run GroupOp.kernel ((NP, gsP, ()), rbU nP NP wP)).2.1.length ≤ NP * NP := by
  obtain ⟨⟨hwP, -, hgvP, -⟩, -, -, hwinP, -, -⟩ := id hIP
  exact (kernelModel_spec hgvP.1 (rb_valid (n := nP) hwP hwinP)).2.2

/-- The restriction: `generate` on the parent's answer (`hBgnR`). -/
theorem ss_m5_hBgnR :
    ∀ hs : GensData, GensData.AllValid NP hs → hs.length ≤ NP * NP + sIn → GensData.denote NP hs ≤
      GensData.denote NP gsP → ssCtx.B.call GroupOp.generate (NP, hs) (ssCtx.O.run GroupOp.generate
      (NP, hs)) ≤ genCost NP (NP * NP + sIn) + 2 :=
  fun _ _ hl _ => ssB_generate_le le_rfl hl _

end Charges

/-! ### The step -/

section Step

variable {a b : Ty} {body : a.denote → Prog (groupSig Ty.unit) (a, b) Ty.denote b}
  {sub : HInstData Ty.unit → Prog (groupSig Ty.unit) (a, b) Ty.denote (Ty.answer Ty.unit)}

/-- **M5 with Schreier–Sims, before the explicit work** (`RunsWithin.m5StepCJProg_jp` at `ssCtx`
with `ssM5β`): every backend hypothesis is proved, for a parent of at most `sIn ≥ NP²`
generators, and `Lg` large enough for `generate`'s inputs. -/
theorem RunsWithin.m5StepCJProg_ss₀ {C : ℕ → Option ℕ → ℕ} {s : ℕ}
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
    {Lg : ℕ} (hLg : (NP - nP).factorial * (sIn + 1) ≤ Lg)
    {uB : ℕ} (huB : NP - nP ≤ uB) (hLgJ : max (NP - nP) uB.factorial * (sIn + 1) ≤ Lg)
    (hLY : (c2bRU (NP - nP) + Case3.c3R k (NP - nP) (Case2b.sojZ (NP - nP))) * (sIn + 1) ≤ Lg)
    {st : ℕ × CJData} (hst : st.1 ≠ 2) :
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
            m5CoreWorkCJ ssCtx.O wP.1.length (rbPts nP NP wP).length k s sIn
              (genCost (rbPts nP NP wP).length Lg + 2)
              (Sims.liftCost (rbPts nP NP wP).length sIn wP.1.length + 7)
              (orbitsCost (rbPts nP NP wP).length sIn (rbPts nP NP wP).length + 5)
              (kerCost (rbPts nP NP wP).length sIn (rbPts nP NP wP).length + 5)
              (Sims.repsCost (rbPts nP NP wP).length sIn
                ((rbPts nP NP wP).length * (rbPts nP NP wP).length)
                ((rbPts nP NP wP).length - wP.1.length).factorial + 7)
              (ssBdF wP.1.length (rbPts nP NP wP).length wP.1.length sIn +
                ssBdJ wP.1.length (rbPts nP NP wP).length wP.1.length wP.1.length sIn)
              ((rbPts nP NP wP).length,
                generateModel (rbPts nP NP wP).length (rbGens nP NP wP gsP), ())
              ((rbPts nP NP wP).length, fxs, ex) ((rbPts nP NP wP).length, fys, ey)
              (WinData.ofPoints (rbPts nP NP wP).length (List.range wP.1.length)).1.length
              (ssM5β (rbPts nP NP wP).length ((rbPts nP NP wP).length - wP.1.length) k sIn s)
              (stabCost (rbPts nP NP wP).length sIn + 5) (transCost (rbPts nP NP wP).length sIn + 5)
              (orbitsCost (rbPts nP NP wP).length sIn (rbPts nP NP wP).length + 5)
              (genCost k (k * (sIn + 1)) + 2) (orbitsCost k sIn k + 5) (stabCost k sIn + 5)
              (fun M => orbitsCost M (M * M) M + 5) (fun M => stabCost M (M * M) + 5)
              (fun M => transCost M (M * M) + 5) uB
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
      ChildList wP.1.length (m5CFCJ ssCtx.O wP.1.length (rbPts nP NP wP).length k
          ((rbPts nP NP wP).length, fxs, ex) ((rbPts nP NP wP).length, fys, ey) uB)
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
  have hwv := hI'.valid.win
  have hLY₂' : c2bRU ((rbPts nP NP wP).length - wP.1.length) * (sIn + 1) ≤ Lg := by
    rw [hm]
    exact (Nat.mul_le_mul_right _ (Nat.le_add_right _ _)).trans hLY
  have hLY₃' : Case3.c3R k ((rbPts nP NP wP).length - wP.1.length)
      (Case2b.sojZ ((rbPts nP NP wP).length - wP.1.length)) * (sIn + 1) ≤ Lg := by
    rw [hm]
    exact (Nat.mul_le_mul_right _ (Nat.le_add_left _ _)).trans hLY
  have hBd : ∀ x : ℕ, ssBdF wP.1.length (rbPts nP NP wP).length
      (WinData.ofPoints (rbPts nP NP wP).length (List.range wP.1.length)).1.length sIn ≤
      ssBdF wP.1.length (rbPts nP NP wP).length wP.1.length sIn + x := by
    intro x
    rw [WinData.ofPoints_fst, List.length_range]
    exact Nat.le_add_right _ _
  have hBdJ : ssBdJ wP.1.length (rbPts nP NP wP).length
      (WinData.ofPoints (rbPts nP NP wP).length (List.range wP.1.length)).1.length
      (rbLabels wP LP).size sIn ≤
      ssBdF wP.1.length (rbPts nP NP wP).length wP.1.length sIn +
        ssBdJ wP.1.length (rbPts nP NP wP).length wP.1.length wP.1.length sIn := by
    rw [WinData.ofPoints_fst, List.length_range]
    have : (rbLabels wP LP).size = wP.1.length := by simp [rbLabels]
    rw [this]
    exact Nat.le_add_left _ _
  exact RunsWithin.m5StepCJProg_jp (X := ssCtx) (body := body) (sub := sub) (C := C) (s := s)
    (Bd := ssBdF wP.1.length (rbPts nP NP wP).length wP.1.length sIn +
      ssBdJ wP.1.length (rbPts nP NP wP).length wP.1.length wP.1.length sIn)
    (Bg1J₂ := ssBg1J (rbPts nP NP wP).length ((rbPts nP NP wP).length - wP.1.length))
    (Bg1J₃ := ssBg1J (rbPts nP NP wP).length ((rbPts nP NP wP).length - wP.1.length))
    (sKR := NP * NP) (BgmR := genCost (rbPts nP NP wP).length sIn + 2)
    (BliftR := Sims.liftCost NP sIn NP + 7) (BkerR := kerCost NP sIn NP + 5)
    (BgnR := genCost NP (NP * NP + sIn) + 2)
    (fun op x _ hx => ssOracle_meets op x hx) (fun _ _ _ h => h) hIP haltP (sm := fun M => M * M)
    hsubP rfl rfl rfl rfl rfl h5 hk h2k hm12 (ssBoundsS _ sIn ⊤ hNs) hgsl le_top
    (ssBoundsS k sIn ⊤ hks) hsk ssBm hCmono hs hB hLg hst
    (ssM5β (rbPts nP NP wP).length ((rbPts nP NP wP).length - wP.1.length) k sIn s)
    (ss_m5_hBgP hgsl) (ss_m5_hBmem hgsv hG) (hB.kernel _ () ⟨hgsv, trivial⟩ hgsl) (ss_m5_hBlA hgsl)
    ss_m5_hBg ss_m5_hBgk (ss_m5_hBgs hNs hgsv hgsl) ss_m5_hBF (hB.kernel _ () ⟨hgsv, trivial⟩ hgsl)
    (hB.kerOrbits _ () _ ⟨hgsv, trivial⟩ hgsl hwv) (hB.cosetReps _ () ⟨hgsv, trivial⟩ hgsl hG)
    (ss_m5_hB3 hgsv hG hs hNs) ss_m5_hBox ss_m5_hBoy (ss_m5_hBg1₁ hgsv) (ss_m5_hD₁ hst hNs (hBd _))
    (ss_m5_hBg1₂ₐ hgsv) ss_m5_hBgen₂ₐ ss_m5_hBpb ss_m5_hBgm ss_m5_hBlift ss_m5_hBker ss_hsK
    ss_m5_hBgn (ss_m5_hBg1₂ᵦ hgsv) ss_m5_hBgen₂ᵦ (ss_m5_hD₂ᵦ hst hNs (hBd _)) (ss_m5_hBg1₃ hgsv)
    ss_m5_hBgen₃ (ss_m5_hD₃ hst hNs (hBd _)) hLgJ (ss_m5_hBg1J₂ hgsv) (ss_m5_hLY₂ hLY₂')
    (ss_m5_hDJ₂ hNs hgsv hgsl hG halt' hBdJ) (ss_m5_hu₂ (by omega)) (ss_m5_hBg1J₃ hgsv)
    (ss_m5_hLY₃ hLY₃') (ss_m5_hDJ₃ hNs hgsv hgsl hG halt' hBdJ) (ss_m5_hu₃ (by omega))
    (ss_m5_hBgmR hgsP) (ss_m5_hBliftR hgsP hNle) (ss_m5_hBkerR hgsP hNle) (ss_m5_hsKR hIP)
    ss_m5_hBgnR

/-- **M5 with Schreier–Sims** (`RunsWithin.m5StepCJProg_jp` at `ssCtx`). For a valid hinted
instance whose base action is a giant, with M5's numeric conditions on `k`, at most `sIn ≥ NP²`
generators, a sub-solver with the spec's predicate (with `sm M = M²`) whose cost is monotone in
the window, `s ≤ sIn`, `Lg` large enough for `generate`'s inputs (`hLg`, `hLgJ`, `hLY`), a
union-cell bound `uB ≥ m` and a state `st` without a Johnson structure: the spec's conclusion, with
M5's work `m5WorkSS |W| m k |W| s sIn Lg uB` and the counted calls (`certCount`, `m5CKCJ`, `m5CH`).
No charge, generator-count, `BackendBounds`, `RDBounds` or `RDOrbit` hypothesis. -/
theorem RunsWithin.m5StepCJProg_ss {C : ℕ → Option ℕ → ℕ} {s : ℕ}
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
    {Lg : ℕ} (hLg : (NP - nP).factorial * (sIn + 1) ≤ Lg)
    {uB : ℕ} (huB : NP - nP ≤ uB) (hLgJ : max (NP - nP) uB.factorial * (sIn + 1) ≤ Lg)
    (hLY : (c2bRU (NP - nP) + Case3.c3R k (NP - nP) (Case2b.sojZ (NP - nP))) * (sIn + 1) ≤ Lg)
    {st : ℕ × CJData} (hst : st.1 ≠ 2) :
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
            m5WorkSS wP.1.length (NP - nP) k wP.1.length s sIn Lg uB)
          sIn (NP * NP) (genCost (rbPts nP NP wP).length sIn + 2) (Sims.liftCost NP sIn NP + 7)
          (kerCost NP sIn NP + 5) (genCost NP (NP * NP + sIn) + 2)) ∧
      AnsOK ssDV NP (wP.denote NP) (PermData.denote NP σP) (GensData.denote NP gsP)
        (xyP.1.denote NP) (xyP.2.denote NP) ans ∧
      (∀ sGen, (∀ hs, GensData.AllValid NP hs →
          GensData.denote NP hs ≤ GensData.denote NP gsP →
          (ssCtx.O.run GroupOp.generate (NP, hs)).2.1.length ≤ sGen) →
        ∀ c : CosetData Ty.unit, ans = some c → c.2.gens.length ≤ sGen) ∧
      ChildList wP.1.length (m5CFCJ ssCtx.O wP.1.length (rbPts nP NP wP).length k
          ((rbPts nP NP wP).length, fxs, ex) ((rbPts nP NP wP).length, fys, ey) uB)
        (StepChild wP.1.length (NP - nP)) ch := by
  obtain ⟨fxs, fys, ex, ey, ans, ch, ⟨hC, φ, hφ, hFx, hFy⟩, hrun, hok, hg, hch⟩ :=
    RunsWithin.m5StepCJProg_ss₀ (body := body) (sub := sub) hIP haltP hsubP h5 hk h2k hm12 hN
      hgsP hCmono hs hLg huB hLgJ hLY hst
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
  have hGb : IsInvariant (GensData.denote (rbPts nP NP wP).length
      (generateModel (rbPts nP NP wP).length (rbGens nP NP wP gsP)))
      (baseSet wP.1.length (rbPts nP NP wP).length) := hI'.base_inv
  have hR := ss_kerReps_le hgsv hGb
  have hK := ss_kernel_gens_le hgsv (baseWin_valid wP.1.length (rbPts nP NP wP).length)
  have hΦx := ss_m5Cs_le (e := ex) hFx.1.1 hFxb
  have hΦy := ss_m5Cs_le (e := ey) hFy.1.1 hFyb
  have hmx := ss_fixPts_le (e := ex) hFx.1.1 hFxb
  have hmy := ss_fixPts_le (e := ey) hFy.1.1 hFyb
  revert hgsl hR hK hΦx hΦy hmx hmy
  generalize (rbPts nP NP wP).length = N at hlen hm ⊢
  subst hlen
  intro hgsl hR hK hΦx hΦy hmx hmy
  rw [Nat.add_sub_cancel_left] at hR hΦx hΦy hmx hmy ⊢
  have h0 := m5CoreWorkCJ_le (n := wP.1.length) (m := NP - nP) (k := k) (s := s) (sIn := sIn)
    (Lg := Lg) (uB := uB) (p := wP.1.length) hgsl hΦx hΦy hmx hmy hR hK
  have h1 := le_m5WorkSS wP.1.length (NP - nP) k wP.1.length s sIn Lg uB
  unfold rbCost
  omega

end Step

/-! ### Parameter choices -/

section Params

/-- The bound on `generate`'s inputs for M5 on base size `m` with certificates of size `k`. -/
def ssLgM5 (m k sIn : ℕ) : ℕ :=
  (m.factorial + c2bRU m + Case3.c3R k m (Case2b.sojZ m)) * (sIn + 1)

/-- **M5's parameters**: for a certificate size `k` with `5 ≤ k` and `2k ≤ m` on a base of
`m = NP − nP ≥ 12` points, `sIn = ssSIn NP s |gsP|`, `uB = m` and `Lg = ssLgM5 m k sIn` meet the
numeric hypotheses of `RunsWithin.m5StepCJProg_ss`: `h5`, `hk`, `h2k`, `hm12`, `hN`, `hgsP`,
`hs`, `hLg`, `huB`, `hLgJ` and `hLY`. -/
theorem m5_params (NP nP k s g : ℕ) (h5 : 5 ≤ k) (h2k : 2 * k ≤ NP - nP) (hm : 12 ≤ NP - nP) :
    5 ≤ k ∧ k + 2 ≤ NP - nP ∧ 2 * k ≤ NP - nP ∧ 12 ≤ NP - nP ∧
      NP * NP ≤ ssSIn NP s g ∧ g ≤ ssSIn NP s g ∧ s ≤ ssSIn NP s g ∧
      (NP - nP).factorial * (ssSIn NP s g + 1) ≤ ssLgM5 (NP - nP) k (ssSIn NP s g) ∧
      NP - nP ≤ NP - nP ∧
      max (NP - nP) (NP - nP).factorial * (ssSIn NP s g + 1) ≤
        ssLgM5 (NP - nP) k (ssSIn NP s g) ∧
      (c2bRU (NP - nP) + Case3.c3R k (NP - nP) (Case2b.sojZ (NP - nP))) *
        (ssSIn NP s g + 1) ≤ ssLgM5 (NP - nP) k (ssSIn NP s g) := by
  obtain ⟨h1, h2, h3⟩ := ssSIn_spec NP s g
  have hf := Nat.self_le_factorial (NP - nP)
  refine ⟨h5, by omega, h2k, hm, h1, h3, h2, Nat.mul_le_mul_right _ (by omega), le_rfl,
    Nat.mul_le_mul_right _ (by omega), Nat.mul_le_mul_right _ (by omega)⟩

/-- `k = 5` is a certificate size for M5 on every base of at least `12` points. -/
theorem m5_params_five (NP nP s g : ℕ) (hm : 12 ≤ NP - nP) :
    5 ≤ 5 ∧ 5 + 2 ≤ NP - nP ∧ 2 * 5 ≤ NP - nP ∧ 12 ≤ NP - nP ∧
      NP * NP ≤ ssSIn NP s g ∧ g ≤ ssSIn NP s g ∧ s ≤ ssSIn NP s g ∧
      (NP - nP).factorial * (ssSIn NP s g + 1) ≤ ssLgM5 (NP - nP) 5 (ssSIn NP s g) ∧
      NP - nP ≤ NP - nP ∧
      max (NP - nP) (NP - nP).factorial * (ssSIn NP s g + 1) ≤
        ssLgM5 (NP - nP) 5 (ssSIn NP s g) ∧
      (c2bRU (NP - nP) + Case3.c3R 5 (NP - nP) (Case2b.sojZ (NP - nP))) *
        (ssSIn NP s g + 1) ≤ ssLgM5 (NP - nP) 5 (ssSIn NP s g) :=
  m5_params NP nP 5 s g le_rfl (by omega) hm

end Params

end GraphIso.Main
