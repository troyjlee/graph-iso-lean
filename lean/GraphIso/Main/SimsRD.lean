module

public import GraphIso.Main.SimsSteps

/-!
# Reduce-and-derive with the Schreier–Sims backend

Stage 14j-5c, item 2 (`PLAN-14.md` §14.8), for reduce-and-derive: the per-orbit hypothesis
`RDOrbit` holds for every orbit in `RDSet`, with an explicit bound `Bd` on the derived hint's work
(`rd_orbit_free_ssU`, `rd_orbit_cj_ssU`). The charges of `rd_orbit_free_ss` and `rd_orbit_cj_ss`
(stage 14j-5b) are proved for every orbit, not only for the orbits where the derive programs make
the calls: `M1Charges`, `BlkCharges`, the re-basing onto the Johnson cells and the union-cell bound.

* **The orbit M1 picks** is an orbit of the base action (`ss_m1O_facts`), since the base is
  nonempty under a hint (`HintValid.base_pos`). So M1's child is valid, with at most `N²`
  generators, and transitive on its base of at least one point (`ss_m1_child`).
* **The maximal blocks** of that base are a block list permuted by the group
  (`ss_mbD_facts`): from `dv_maxBlocks_list` on at least two points, and `[[n]]` on one. So the
  block stabilizer's sizes are those of `ss_blockStab_sizes`, and every charge of `BlkCharges` is
  bounded at degree `2N` (`ss_blkCharges`).
* **The Johnson cells**: a group preserving the Johnson structure permutes them
  (`dv_cellPos_perm`), so their re-basing is valid with at most `(n + |cells|)²` generators, and
  there are at most `N − n` cells (`ss_cells`). The union labels have at most `|cells|` entries
  (`ss_union_le`).
* **The union labels by the labels** (stage 14j-6b-1, `PLAN-14.md` §14.11 item 4): for a valid
  Johnson structure with parameter `s` on `m` points, at most `labLen L · s ≤ labLen L · λ(m)`
  entries (`ss_union_le_lab`, through `labLen_labJUD_le` and `s_le_lam`).
-/

@[expose] public section

namespace GraphIso.Main

open Equiv Cost GraphIso GraphIso.Programs GraphIso.Toolkit GraphIso.Recursion Sims Solver

attribute [local gcongr] buildCost_mono₂ genCost_mono₂ kerCost_mono₂ rd_liftCost_mono₂
  rd_orbitsCost_mono₂

/-- Under a hint, the base is nonempty: some label is nonempty. -/
theorem _root_.GraphIso.Toolkit.HintValid.base_pos {n N : ℕ} {gs : GensData} {w : WinData}
    {L : LabelData} (h : HintValid n N gs w L) : n < N := by
  obtain ⟨i, hi, j, hj, hne⟩ := h.nonconst
  by_contra hc
  have hm : N - n = 0 := by omega
  have e : ∀ u ∈ w.1, L.getD u [] = [] := by
    intro u hu
    cases hl : L.getD u [] with
    | nil => rfl
    | cons a t =>
      have := h.lab_lt u hu a (by rw [hl]; exact List.mem_cons_self)
      omega
  exact hne (by rw [e i hi, e j hj])

/-! ### The orbit and the child of M1 -/

section M1Child

variable {n N : ℕ} {gs : GensData} {d : Unit} {w : WinData} {L : LabelData}

theorem pickD_mem {n m : ℕ} {L : LabelData} {pts : List ℕ} {os : List (List ℕ)}
    (h : os ≠ []) : pickD n m L pts os ∈ os := by
  unfold pickD
  rcases hf : os.filter (ncD n m L pts) with _ | ⟨b, t⟩
  · rcases os with _ | ⟨a, t'⟩
    · exact absurd rfl h
    · exact List.mem_cons_self
  · have hb : b ∈ os.filter (ncD n m L pts) := by rw [hf]; exact List.mem_cons_self
    exact (List.mem_filter.1 hb).1

/-- **The orbit M1 picks, with Schreier–Sims and any labels**: an orbit of the base action. -/
theorem ss_m1O_facts (hgs : GensData.AllValid N gs)
    (hb : IsInvariant (GensData.denote N gs) (baseSet n N)) (hnN : n < N) :
    (m1O ssCtx.O n N (N, gs, d) w L).Nodup ∧
      (∀ x ∈ m1O ssCtx.O n N (N, gs, d) w L, n ≤ x ∧ x < N) ∧
      (m1O ssCtx.O n N (N, gs, d) w L).length ≤ N - n ∧
      (∀ i ∈ m1O ssCtx.O n N (N, gs, d) w L, ∀ j,
        j ∈ m1O ssCtx.O n N (N, gs, d) w L ↔ SameOrbit (GensData.denote N gs) i j) ∧
      m1O ssCtx.O n N (N, gs, d) w L ≠ [] := by
  have hos : IsOrbitPartition (GensData.denote N gs) (baseWin n N)
      (ssCtx.O.run GroupOp.orbits ((N, gs, d), baseWin n N)) :=
    ssOracle_meets .orbits _ ⟨⟨hgs, trivial⟩, baseWin_valid n N,
      by rw [baseWin_denote]; exact hb⟩
  have hne : ssCtx.O.run GroupOp.orbits ((N, gs, d), baseWin n N) ≠ [] := by
    intro h
    have hl := hos.1.length_eq
    rw [h, baseWin_length] at hl
    simp at hl
    omega
  have hmem := pickD_mem (n := n) (m := N - n) (L := L) (pts := w.1) hne
  obtain ⟨hnd, hbs, hlen, horb⟩ := mf_orbit hos hmem
  exact ⟨hnd, hbs, hlen, horb, (hos.2 _ hmem).1⟩

/-- **The child of M1, with Schreier–Sims and any labels**: degree `n + k` for the orbit's
`1 ≤ k ≤ N − n` points, valid with at most `(n + k)²` generators, keeping its base `[n, n + k)`
invariant and transitive on it. -/
theorem ss_m1_child (hgs : GensData.AllValid N gs)
    (hb : IsInvariant (GensData.denote N gs) (baseSet n N)) (hnN : n < N) :
    (m1Model ssCtx.O n N (N, gs, d) w L).1.1 = n + (m1O ssCtx.O n N (N, gs, d) w L).length ∧
      1 ≤ (m1O ssCtx.O n N (N, gs, d) w L).length ∧
      (m1O ssCtx.O n N (N, gs, d) w L).length ≤ N - n ∧
      GensData.AllValid (m1Model ssCtx.O n N (N, gs, d) w L).1.1
        (m1Model ssCtx.O n N (N, gs, d) w L).1.2.1 ∧
      (m1Model ssCtx.O n N (N, gs, d) w L).1.2.1.length ≤
        (m1Model ssCtx.O n N (N, gs, d) w L).1.1 * (m1Model ssCtx.O n N (N, gs, d) w L).1.1 ∧
      IsInvariant (GensData.denote (m1Model ssCtx.O n N (N, gs, d) w L).1.1
          (m1Model ssCtx.O n N (N, gs, d) w L).1.2.1)
        (baseSet n (m1Model ssCtx.O n N (N, gs, d) w L).1.1) ∧
      IsTransOn (GensData.denote (m1Model ssCtx.O n N (N, gs, d) w L).1.1
          (m1Model ssCtx.O n N (N, gs, d) w L).1.2.1)
        (baseSet n (m1Model ssCtx.O n N (N, gs, d) w L).1.1) := by
  obtain ⟨hnd, hbO, hlen, horb, hne⟩ := ss_m1O_facts (d := d) (w := w) (L := L) hgs hb hnN
  set Ob := m1O ssCtx.O n N (N, gs, d) w L with hObdef
  have hn : n ≤ N := hnN.le
  have hwO : (WinData.ofPoints N Ob).Valid N :=
    WinData.valid_ofPoints hnd fun x hx => (hbO x hx).2
  have hbs : IsBlockList (WinData.ofPoints N Ob) (singD Ob) := mf_sing_isBlockList
  have hGb : PermutesBlocks (GensData.denote N gs) (singD Ob) := mf_sing_permutes horb
  have hO : MeetsContractOn ssDV rebaseOps ssCtx.O := fun op x _ hx => ssOracle_meets op x hx
  obtain ⟨-, hdeg, hval, hden⟩ := RunsWithin.rebaseProg (X := ssCtx) (a := Ty.unit)
    (b := Ty.unit)
    (body := fun x => (Prog.ret x : Prog (groupSig Ty.unit) (Ty.unit, Ty.unit) Ty.denote Ty.unit))
    (DV := ssDV) hO (fun _ _ _ h => h) hn hb hwO hbs hGb hgs le_rfl
  have hm : (m1Model ssCtx.O n N (N, gs, d) w L).1 = rebaseModel ssCtx.O n N (singD Ob) gs :=
    rfl
  have hk : (singD Ob).length = Ob.length := length_singD Ob
  have hlen1 : 1 ≤ Ob.length := List.length_pos_iff.2 hne
  have hgl : (rebaseModel ssCtx.O n N (singD Ob) gs).2.1.length ≤
      (n + (singD Ob).length) * (n + (singD Ob).length) :=
    ss_generate_gens_le (allValid_rebaseGens hn hb hwO hbs hGb hgs)
  rw [hm, hdeg]
  refine ⟨by rw [hk], hlen1, hlen, hval.1, hgl, ?_, ?_⟩
  · rw [hden]
    exact (rebase_invariant hn (isInvariant_strSet hb) hwO hbs hGb).1
  · rw [hden]
    intro u hu v hv
    change n ≤ u.val at hu
    change n ≤ v.val at hv
    have hu' : u.val - n < Ob.length := by have := u.2; omega
    have hv' : v.val - n < Ob.length := by have := v.2; omega
    obtain ⟨h1, h2, g, hg, e⟩ := (horb _ (List.getElem_mem hu') Ob[v.val - n]).1
      (List.getElem_mem hv')
    refine ⟨_, ⟨⟨g, hg⟩, rfl⟩, ?_⟩
    apply Fin.ext
    rw [rebaseHom_ge _ _ _ _ _ _ hu]
    obtain ⟨hbm, hbmeq⟩ := mf_blockMap_sing hwO hGb hg hu'
    have h2 : Ob[blockMap N (singD Ob) g (u.val - n)] = Ob[v.val - n] := by
      rw [← hbmeq]
      exact congrArg Fin.val e
    have := (hnd.getElem_inj_iff).1 h2
    rw [this]
    omega

end M1Child

/-! ### The maximal blocks of a transitive base -/

section Blocks

/-- **The maximal blocks of a transitive base of at least one point**: a nonempty block list of
the base, permuted by the group. -/
theorem ss_mbD_facts {n N₁ : ℕ} {gs₁ : GensData} (hgs : GensData.AllValid N₁ gs₁)
    (hinv : IsInvariant (GensData.denote N₁ gs₁) (baseSet n N₁))
    (htr : IsTransOn (GensData.denote N₁ gs₁) (baseSet n N₁)) (h1 : n < N₁) :
    IsBlockList (WinData.ofPoints N₁ (basePts n N₁)) (mbD n N₁ gs₁) ∧
      PermutesBlocks (GensData.denote N₁ gs₁) (mbD n N₁ gs₁) ∧
      0 < (mbD n N₁ gs₁).length ∧ (mbD n N₁ gs₁).length ≤ N₁ - n := by
  have key : ∀ {bs : List (List ℕ)}, IsBlockList (WinData.ofPoints N₁ (basePts n N₁)) bs →
      0 < bs.length ∧ bs.length ≤ N₁ - n := by
    intro bs hbs
    refine ⟨?_, ?_⟩
    · rcases Nat.eq_zero_or_pos bs.length with h | h
      · have hl := hbs.1.length_eq
        rw [List.length_eq_zero_iff.1 h, WinData.ofPoints_fst, length_basePts] at hl
        simp at hl
        omega
      · exact h
    · have := IsBlockList.length_le hbs
      rwa [WinData.ofPoints_fst, length_basePts] at this
  by_cases h2 : 2 ≤ N₁ - n
  · obtain ⟨hbs, hG⟩ := dv_maxBlocks_list hgs hinv htr h2
    exact ⟨hbs, hG, key hbs⟩
  · have hN : N₁ = n + 1 := by omega
    subst hN
    have hpts : basePts n (n + 1) = [n] := by
      simp [basePts]
    have hmb : mbD n (n + 1) gs₁ = [[n]] := by
      simp only [mbD, hpts, Luks.maxBlocks, Luks.maxLabels, List.foldl_cons, List.foldl_nil,
        Luks.mbStep, Luks.blocksOf, Luks.leaders, Luks.discrete]
      simp [get]
    have hbs : IsBlockList (WinData.ofPoints (n + 1) (basePts n (n + 1))) [[n]] := by
      rw [hpts]
      exact ⟨by simp, fun b hb => by simp at hb; simp [hb]⟩
    refine ⟨hmb ▸ hbs, ?_, key (hmb ▸ hbs)⟩
    rw [hmb]
    intro g hg b hb
    simp only [List.mem_singleton] at hb
    subst hb
    refine ⟨[n], List.mem_singleton_self _, fun u hu => ?_⟩
    simp only [List.mem_singleton] at hu ⊢
    have hgu := hinv g hg u (show n ≤ u.val by omega)
    have := (g u).2
    change n ≤ (g u).val at hgu
    omega

end Blocks


/-! ### The charges -/

section Charges

/-- **M1's charges with Schreier–Sims**, for a group of at most `S` generators. -/
theorem ss_m1Charges {n N S : ℕ} {gs : GensData} {d : Unit} {w : WinData} {L : LabelData}
    (hgs : GensData.AllValid N gs) (hb : IsInvariant (GensData.denote N gs) (baseSet n N))
    (hnN : n < N) (hl : gs.length ≤ S) :
    M1Charges ssCtx n N gs d w L (orbitsCost N S (N - n) + 5) (genCost N S + 2) := by
  obtain ⟨-, -, hk, -⟩ := ss_m1O_facts (d := d) (w := w) (L := L) hgs hb hnN
  refine ⟨?_, ssB_generate_le (by rw [length_singD]; omega)
    (by rw [rebaseGens_length]; exact hl) _⟩
  change orbitsCost N gs.length (baseWin n N).1.length + 5 ≤ _
  rw [baseWin_length]
  exact Nat.add_le_add_right (rd_orbitsCost_mono₂ le_rfl hl le_rfl) 5

/-- **The block step's charges with Schreier–Sims**, on a valid group `(N₁, gs₁)` of at most
`N₁²` generators, transitive on a base of `1 ≤ N₁ − n` points, with `N₁ ≤ N`: the extended degree
is at most `2N`. -/
theorem ss_blkCharges_of {n N N₁ : ℕ} {gs₁ : GensData} (hgs : GensData.AllValid N₁ gs₁)
    (hl : gs₁.length ≤ N₁ * N₁) (hinv : IsInvariant (GensData.denote N₁ gs₁) (baseSet n N₁))
    (htr : IsTransOn (GensData.denote N₁ gs₁) (baseSet n N₁)) (h1 : n < N₁) (hN : N₁ ≤ N) :
    BlkCharges ssCtx n N₁ gs₁ (N * N) (genCost N (N * N) + 2) (genCost (2 * N) (N * N) + 2)
      (stabCost (2 * N) (2 * N * (2 * N)) + 5) (transCost (2 * N) (2 * N * (2 * N)) + 5)
      (genCost N (2 * N * (2 * N)) + 2) (2 * N * (2 * N)) (2 * N) (N * N)
      (genCost N (N * N) + 2) := by
  obtain ⟨hbs, hGb, hpos, hbl⟩ := ss_mbD_facts hgs hinv htr h1
  have hwbv : (WinData.ofPoints N₁ (basePts n N₁)).Valid N₁ :=
    WinData.valid_ofPoints (basePts_nodup _ _) fun i hi => (mem_basePts.1 hi).2
  have hwbn : ∀ i ∈ (WinData.ofPoints N₁ (basePts n N₁)).1, n ≤ i :=
    fun i hi => (mem_basePts.1 hi).1
  obtain ⟨hse, hss, hst, hsH, -⟩ := ss_blockStab_sizes (t := 0) hinv hwbv hwbn hbs hGb hgs hpos
  have hflat : (mbD n N₁ gs₁).flatten.length = N₁ - n := by
    rw [hbs.1.length_eq, WinData.ofPoints_fst, length_basePts]
  have hkle : (((mbD n N₁ gs₁).toArray.getD 0 []).map fun p => [p]).length ≤ N₁ - n := by
    rw [List.length_map, ← hflat, mr_getD_toArray', List.getD_eq_getElem _ _ hpos,
      List.length_flatten]
    exact List.le_sum_of_mem (List.mem_map.2 ⟨_, List.getElem_mem hpos, rfl⟩)
  have e2 : N₁ + (mbD n N₁ gs₁).length ≤ 2 * N := by omega
  have hNN : N₁ * N₁ ≤ N * N := Nat.mul_le_mul hN hN
  have h22 : (N₁ + (mbD n N₁ gs₁).length) * (N₁ + (mbD n N₁ gs₁).length) ≤ 2 * N * (2 * N) :=
    Nat.mul_le_mul e2 e2
  refine ⟨hl.trans hNN,
    ssB_generate_le (by omega) (by rw [rebaseGens_length]; exact hl.trans hNN) _,
    ssB_generate_le e2 (by rw [extendGens_length]; exact hl.trans hNN) _, ?_, ?_,
    ssB_generate_le hN ((List.length_map _).trans_le (hss.trans h22)) _,
    ssB_generate_le (by omega) (by rw [rebaseGens_length]; exact hsH.trans hNN) _,
    hss.trans h22, hst.trans e2, hsH.trans hNN⟩
  · change stabCost (N₁ + (mbD n N₁ gs₁).length)
      (extGroup ssCtx.O N₁ (mbD n N₁ gs₁) gs₁).2.1.length + 5 ≤ _
    unfold stabCost
    gcongr
    exact hse.trans h22
  · change transCost (N₁ + (mbD n N₁ gs₁).length)
      (extGroup ssCtx.O N₁ (mbD n N₁ gs₁) gs₁).2.1.length + 5 ≤ _
    unfold transCost
    gcongr
    exact hse.trans h22

/-- **The block step's charges with Schreier–Sims** on the child of M1, for any labels. -/
theorem ss_blkCharges {n N : ℕ} {gs : GensData} {d : Unit} {w : WinData} {L : LabelData}
    (hgs : GensData.AllValid N gs) (hb : IsInvariant (GensData.denote N gs) (baseSet n N))
    (hnN : n < N) :
    BlkCharges ssCtx n (m1Model ssCtx.O n N (N, gs, d) w L).1.1
      (m1Model ssCtx.O n N (N, gs, d) w L).1.2.1 (N * N) (genCost N (N * N) + 2)
      (genCost (2 * N) (N * N) + 2) (stabCost (2 * N) (2 * N * (2 * N)) + 5)
      (transCost (2 * N) (2 * N * (2 * N)) + 5) (genCost N (2 * N * (2 * N)) + 2)
      (2 * N * (2 * N)) (2 * N) (N * N) (genCost N (N * N) + 2) := by
  obtain ⟨hdeg, hk1, hkm, hval, hgl, hinv, htr⟩ := ss_m1_child (d := d) (w := w) (L := L) hgs hb hnN
  exact ss_blkCharges_of hval hgl hinv htr (by omega) (by omega)

end Charges

/-! ### Every orbit without a coloured Johnson structure -/

section Free

/-- **The work of the derived hint without a structure, with Schreier–Sims**: `deriveFreeCost` at
the charges of `ss_m1Charges` and `ss_blkCharges`, on an orbit of at most `p` points of a group
of at most `S` generators. -/
def ssBdF (n N p S : ℕ) : ℕ :=
  deriveFreeCost n N p S (orbitsCost N S (N - n) + 5) (genCost N S + 2) (N * N)
    (2 * N * (2 * N)) (2 * N) (N * N) (genCost N (N * N) + 2) (genCost (2 * N) (N * N) + 2)
    (stabCost (2 * N) (2 * N * (2 * N)) + 5) (transCost (2 * N) (2 * N * (2 * N)) + 5)
    (genCost N (2 * N * (2 * N)) + 2) (genCost N (N * N) + 2) + 5

theorem deriveFreeCost_mono_ps {n N p p' s s' Borb Bgen s₁ sS Lt sH Bgen₂ Bge Bst Btr Bgt
    Bgen₃ : ℕ} (hp : p ≤ p') (hs : s ≤ s') :
    deriveFreeCost n N p s Borb Bgen s₁ sS Lt sH Bgen₂ Bge Bst Btr Bgt Bgen₃ ≤
      deriveFreeCost n N p' s' Borb Bgen s₁ sS Lt sH Bgen₂ Bge Bst Btr Bgt Bgen₃ := by
  unfold deriveFreeCost m1ContCost m1Cost blocksCost ncBCost neqCost m2aCost m2bCost
    rebaseCost pickCost labM1Cost ncCost
  gcongr

/-- An orbit inside the window has at most `|W|` points. -/
theorem DSetting.orbit_length_le {DV : ℕ → GensData → Ty.unit.denote → Prop} {n N : ℕ}
    {gsG gs : GensData} {w : WinData} {L : LabelData} {d : Ty.unit.denote} {O : List ℕ}
    (h : DSetting (D := Ty.unit) DV n N gsG w L gs d O) :
    O.length ≤ w.1.length :=
  (h.nodup.subperm fun x hx => h.sub x hx).length_le

variable {a b : Ty} {body : a.denote → Prog (groupSig Ty.unit) (a, b) Ty.denote b}
  {n N S : ℕ} {gsG gsK : GensData} {w : WinData} {L : LabelData}

/-- **`RDOrbit` for every orbit, without a coloured Johnson structure** (`rd_orbit_free_ss` with
every charge proved), at the work `ssBdF n N |W| S`. -/
theorem rd_orbit_free_ssU {st : ℕ × CJData} (hst : st.1 ≠ 2) (hS : N * N ≤ S) :
    ∀ gs d O, RDSet ssDV n N gsG w L gsK S gs d O →
      RDOrbit ssCtx body ssDV n N w L st S (ssBdF n N w.1.length S) gs d O :=
  rd_orbit_free_ss hst hS fun _ _ _ hset =>
    ⟨ss_m1Charges hset.1.kvalid.1 hset.1.base_inv hset.1.hint.base_pos hset.2.1,
      ss_blkCharges hset.1.kvalid.1 hset.1.base_inv hset.1.hint.base_pos,
      Nat.add_le_add_right (deriveFreeCost_mono_ps hset.1.orbit_length_le hset.2.1) 5⟩

end Free


/-! ### Every orbit with a coloured Johnson structure -/

section CJ

/-- A valid Johnson structure on `m` points has at most `m` cells. -/
theorem ss_cells_le {n N : ℕ} {jd : Align.JData} (hJv : Align.JValid (N - n) jd) :
    jd.2.1.length ≤ N - n := by
  have hnd : jd.2.1.flatten.Nodup := List.nodup_flatten.2
    ⟨fun c hc => hJv.cell_nodup c hc, hJv.cell_disj.imp fun h a ha hb => h a ha hb⟩
  have hlt : ∀ a ∈ jd.2.1.flatten, a < N - n := fun a ha => by
    obtain ⟨c, hc, hac⟩ := List.mem_flatten.1 ha
    exact hJv.cell_lt c hc a hac
  have h1 := mf_length_le_of_nodup hnd hlt
  have h2 := mf_length_le_of_isBlockList (dv_cellPos_blocks (N := N) (n := n) hJv)
  rw [dv_length_cellPos, WinData.ofPoints_fst, dv_flatten_cellPos, List.length_map] at h2
  omega

/-- The union labels have at most `nc` entries: they are cell indices below `nc`. -/
theorem ss_union_le {nc : ℕ} {v0 : Array Bool} {fA : Array (List ℕ)} {L : LabelData}
    {O : List ℕ} (hO : O.Nodup) (hne : O ≠ []) :
    ((labJUD nc v0 fA L O).getD (O.headD 0) []).length ≤ nc := by
  have hi : O.headD 0 ∈ O := by
    rcases O with _ | ⟨a, t⟩
    · exact absurd rfl hne
    · exact List.mem_cons_self
  have hF : jUnionData nc v0 fA [] = [] := by
    unfold jUnionData
    refine List.filter_eq_nil_iff.2 fun j _ h => ?_
    rw [getB_markArr] at h
    simp at h
  unfold labJUD
  rw [dv_getD_mapLabels hO hF hi]
  unfold jUnionData
  exact (List.length_filter_le _ _).trans (by rw [List.length_range])

/-- **The union labels are bounded by the labels**: for valid Johnson data on `m` points whose
decoding is a Johnson embedding, every union label at the points of `O` has at most
`labLen L · λ(m)` entries: the cells have `s` points each, and `s ≤ λ(m)` (`s_le_lam`). -/
theorem ss_union_le_lab {m t : ℕ} {V : Finset (Fin m)} {jd : Align.JData}
    (hJv : Align.JValid m jd) (hJ : SplitJohnson.IsJohnson V t (Align.jdec m jd)) {L : LabelData}
    {O : List ℕ} (hO : O.Nodup) (i : ℕ) :
    ((labJUD jd.2.1.length (markArr m jd.1) jd.2.2.2 L O).getD i []).length ≤
      labLen L * lam m := by
  have h2 : 2 ≤ jd.2.2.1 := hJ.two_le
  have hs : jd.2.2.1 ≤ lam m := by
    refine s_le_lam (dv_cj_choose_le hJv hJ) ?_
    rw [← dv_jdec_card hJv]
    exact hJ.le_half
  refine (length_getD_le_labLen _ i).trans ((labLen_labJUD_le hO (by omega)
    fun j hj => le_of_eq (hJv.f_len j ((getB_markArr _ _ _).1 hj).2)).trans ?_)
  exact Nat.mul_le_mul_left _ hs

/-- **The work of the derived hint with a coloured Johnson structure, with Schreier–Sims**:
`deriveCJCost` at the charges of `ss_m1Charges`, `ss_blkCharges`, the re-basing onto the cells
(`generate` at degree at most `N`) and the backend bounds at degree `N`, with at most `N − n`
union cells, on an orbit of at most `p` points of a group of at most `S` generators and a label
array of size `Ls`. -/
def ssBdJ (n N p Ls S : ℕ) : ℕ :=
  deriveCJCost n N p Ls S (orbitsCost N S (N - n) + 5) (genCost N S + 2) (N * N)
    (2 * N * (2 * N)) (2 * N) (N * N) (genCost N (N * N) + 2) (genCost (2 * N) (N * N) + 2)
    (stabCost (2 * N) (2 * N * (2 * N)) + 5) (transCost (2 * N) (2 * N * (2 * N)) + 5)
    (genCost N (2 * N * (2 * N)) + 2) (genCost N (N * N) + 2) (genCost N S + 2) (N - n)
    (transCost N (N * N) + 5) (stabCost N (N * N) + 5) + 5

/-- **`ssBdJ` at a union-cell bound `u`** (stage 14j-6b-1): the Johnson fallback branches over at
most `u!` cosets (`jfallbackCost`), so this work has no factorial of `N − n` when `u` is the
labels' bound `labLen L · λ(N − n)`. `ssBdJ` is the case `u = N − n` (`ssBdJ_eq`). -/
def ssBdJU (n N p Ls S u : ℕ) : ℕ :=
  deriveCJCost n N p Ls S (orbitsCost N S (N - n) + 5) (genCost N S + 2) (N * N)
    (2 * N * (2 * N)) (2 * N) (N * N) (genCost N (N * N) + 2) (genCost (2 * N) (N * N) + 2)
    (stabCost (2 * N) (2 * N * (2 * N)) + 5) (transCost (2 * N) (2 * N * (2 * N)) + 5)
    (genCost N (2 * N * (2 * N)) + 2) (genCost N (N * N) + 2) (genCost N S + 2) u
    (transCost N (N * N) + 5) (stabCost N (N * N) + 5) + 5

theorem ssBdJ_eq (n N p Ls S : ℕ) : ssBdJ n N p Ls S = ssBdJU n N p Ls S (N - n) := rfl

theorem deriveCJCost_mono {n N p p' Ls s s' Borb Bgen s₁ sS Lt sH Bgen₂ Bge Bst Btr Bgt Bgen₃
    Bgen₄ uB Bt Bt' Bs Bs' : ℕ} (hp : p ≤ p') (hs : s ≤ s') (ht : Bt ≤ Bt') (hb : Bs ≤ Bs') :
    deriveCJCost n N p Ls s Borb Bgen s₁ sS Lt sH Bgen₂ Bge Bst Btr Bgt Bgen₃ Bgen₄ uB Bt Bs ≤
      deriveCJCost n N p' Ls s' Borb Bgen s₁ sS Lt sH Bgen₂ Bge Bst Btr Bgt Bgen₃ Bgen₄ uB Bt'
        Bs' := by
  unfold deriveCJCost johnStepCost jfallbackCost CertProg.kerACost m1ContCost m1Cost blocksCost
    ncBCost neqCost m2aCost m2bCost rebaseCost pickCost labM1Cost ncCost
  gcongr

variable {a b : Ty} {body : a.denote → Prog (groupSig Ty.unit) (a, b) Ty.denote b}
  {n N S : ℕ} {gsG gsK : GensData} {w : WinData} {L : LabelData}

/-- **`RDOrbit` for every orbit, with a coloured Johnson structure, at a union-cell bound `u`**
(stage 14j-6b-1): `rd_orbit_cj_ss` with every charge proved, under `rd_orbit_cj`'s structure
hypotheses and `u` bounding the union labels of every orbit, at the work
`ssBdJU n N |W| |L| S u`. -/
theorem rd_orbit_cj_ssUB {st : ℕ × CJData} (hst : st.1 = 2)
    (hKb : IsInvariant (GensData.denote N gsK) (baseSet n N)) (hJv : Align.JValid (N - n) st.2.1)
    {V : Finset (Fin (N - n))} {t : ℕ}
    (hJ : SplitJohnson.IsJohnson V t (Align.jdec (N - n) st.2.1))
    (hK : ∀ g : ↥(GensData.denote N gsK),
      baseHom (GensData.denote N gsK) n hKb g • cjdec (N - n) st.2 = cjdec (N - n) st.2)
    (hS : N * N ≤ S) {u : ℕ}
    (hu : ∀ O : List ℕ, O.Nodup → O ≠ [] →
      ((labJUD st.2.1.2.1.length (markArr (N - n) st.2.1.1) st.2.1.2.2.2 L O).getD (O.headD 0)
        []).length ≤ u) :
    ∀ gs d O, RDSet ssDV n N gsG w L gsK S gs d O →
      RDOrbit ssCtx body ssDV n N w L st S (ssBdJU n N w.1.length L.size S u) gs d O := by
  have hc := ss_cells_le hJv
  refine rd_orbit_cj_ss hst hKb hJv hJ hK hS (Borb := orbitsCost N S (N - n) + 5)
    (Bgen := genCost N S + 2) (s₁ := N * N) (Bgen₂ := genCost N (N * N) + 2)
    (Bge := genCost (2 * N) (N * N) + 2) (Bst := stabCost (2 * N) (2 * N * (2 * N)) + 5)
    (Btr := transCost (2 * N) (2 * N * (2 * N)) + 5) (Bgt := genCost N (2 * N * (2 * N)) + 2)
    (sS := 2 * N * (2 * N)) (Lt := 2 * N) (sH := N * N) (Bgen₃ := genCost N (N * N) + 2)
    (Bgen₄ := genCost N S + 2) (uB := u) fun gs d O hset => ?_
  have hD := hset.1
  have hgs := hD.kvalid.1
  have hnN := hD.hint.base_pos
  have hcp : (cellPosD n st.2.1.2.1).length ≤ N - n := by rw [dv_length_cellPos]; exact hc
  have hKH : ∀ g : ↥(GensData.denote N gs),
      baseHom (GensData.denote N gs) n hD.base_inv g • Align.jdec (N - n) st.2.1 =
        Align.jdec (N - n) st.2.1 := by
    rintro ⟨π, hπ⟩
    rw [dv_baseHom_le hset.2.2 hKb hD.base_inv hπ]
    exact ((cj_smul_eq_iff' _ _ _).1 (hK ⟨π, hset.2.2 hπ⟩)).1
  have hval := allValid_rebaseGens hnN.le hD.base_inv (dv_cellPos_valid hJv hnN.le)
    (dv_cellPos_blocks hJv) (dv_cellPos_perm hD.base_inv hJv hKH) hgs
  set M := n + (cellPosD n st.2.1.2.1).length with hM
  have hMN : M ≤ N := by omega
  refine ⟨ss_m1Charges hgs hD.base_inv hnN hset.2.1, ss_blkCharges hgs hD.base_inv hnN,
    ssB_generate_le hMN (by rw [rebaseGens_length]; exact hset.2.1) _,
    hu O hD.nodup hD.ne,
    ⟨M * M, ⊤, ssBounds M ⊤, ss_generate_gens_le hval, le_top, ?_⟩⟩
  refine Nat.add_le_add_right (deriveCJCost_mono hD.orbit_length_le hset.2.1 ?_ ?_) 5
  · change transCost M (M * M) + 5 ≤ _
    unfold transCost
    gcongr
  · change stabCost M (M * M) + 5 ≤ _
    unfold stabCost
    gcongr

/-- **`RDOrbit` for every orbit, with a coloured Johnson structure** (`rd_orbit_cj_ss` with every
charge proved), under `rd_orbit_cj`'s structure hypotheses, at the work
`ssBdJ n N |W| |L| S`: the union labels have at most `N − n` entries (`ss_union_le`,
`ss_cells_le`). -/
theorem rd_orbit_cj_ssU {st : ℕ × CJData} (hst : st.1 = 2)
    (hKb : IsInvariant (GensData.denote N gsK) (baseSet n N)) (hJv : Align.JValid (N - n) st.2.1)
    {V : Finset (Fin (N - n))} {t : ℕ}
    (hJ : SplitJohnson.IsJohnson V t (Align.jdec (N - n) st.2.1))
    (hK : ∀ g : ↥(GensData.denote N gsK),
      baseHom (GensData.denote N gsK) n hKb g • cjdec (N - n) st.2 = cjdec (N - n) st.2)
    (hS : N * N ≤ S) :
    ∀ gs d O, RDSet ssDV n N gsG w L gsK S gs d O →
      RDOrbit ssCtx body ssDV n N w L st S (ssBdJ n N w.1.length L.size S) gs d O :=
  rd_orbit_cj_ssUB hst hKb hJv hJ hK hS fun _ hO hne =>
    (ss_union_le hO hne).trans (ss_cells_le hJv)

/-- **`RDOrbit` for every orbit, with a coloured Johnson structure, with the union cells bounded
by the labels** (stage 14j-6b-1): at the work `ssBdJU n N |W| |L| S (labLen L · λ(N − n))`
(`ss_union_le_lab`). -/
theorem rd_orbit_cj_ssL {st : ℕ × CJData} (hst : st.1 = 2)
    (hKb : IsInvariant (GensData.denote N gsK) (baseSet n N)) (hJv : Align.JValid (N - n) st.2.1)
    {V : Finset (Fin (N - n))} {t : ℕ}
    (hJ : SplitJohnson.IsJohnson V t (Align.jdec (N - n) st.2.1))
    (hK : ∀ g : ↥(GensData.denote N gsK),
      baseHom (GensData.denote N gsK) n hKb g • cjdec (N - n) st.2 = cjdec (N - n) st.2)
    (hS : N * N ≤ S) :
    ∀ gs d O, RDSet ssDV n N gsG w L gsK S gs d O →
      RDOrbit ssCtx body ssDV n N w L st S
        (ssBdJU n N w.1.length L.size S (labLen L * lam (N - n))) gs d O :=
  rd_orbit_cj_ssUB hst hKb hJv hJ hK hS fun _ hO _ => ss_union_le_lab hJv hJ hO _

end CJ

end GraphIso.Main
