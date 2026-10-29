module

public import GraphIso.Main.HInst
public import GraphIso.Luks.Primitive
public import GraphIso.Luks.MaxBlocksProg
public import GraphIso.Toolkit.BaseBlocks
public import GraphIso.Toolkit.Labels
public import GraphIso.Reductions.BlockKernelProg
public import GraphIso.Programs.Window
public import GraphIso.SoJTree.LeafProg
public import GraphIso.Toolkit.Reduce

/-!
# The free coarsenings M0, M1 and M2a

Stage 14j-1, item 2 (`PLAN-14.md` §14.1). Each coarsening re-bases the group onto a new base
(stage 14b's `rebaseProg`, which keeps the action on the string positions, `rebase_iso`) and
computes the new labels. Each spec gives `HintValid` for the new data, the invariance of the new
base, faithfulness on the string positions, the window's validity, invariance and transitivity,
and the new base size.

* `hintValid_of_forall`: hint data is valid for a generating list once the labels are
  equivariant for every element of the generated group (the re-based groups come from the
  backend, so their generators are only known to generate the image of `rebaseHom`).
* **M0** `m0Prog`: a group transitive on its window without a hint gets the maximal block
  system of the window (milestone 3) as its base, with labels `u ↦ {block of u}`; the new base
  has between `2` and `|W|` points (`RunsWithin.m0Prog`).
* **M1** `m1Prog`: a hinted group gets an orbit `O` of its base action on which the labels are
  not constant (one exists, `mf_exists_ncD`, the data form of `exists_nonConst_inter`; the
  backend's `orbits` computes the orbits) as its base, with labels `lab ∩ O` at the window
  points (empty elsewhere, so labels off the window cost nothing). The new base has
  `k ≤ m` points, and `k < m` when the base action is intransitive (`RunsWithin.m1Prog`).
* **M2a** `m2aProg`: for a hinted group with a block system `bs` of its transitive base action
  (blocks of at least two points, e.g. from `baseBlocksProg`), given as an input, and a window
  label not equidistributed over the blocks, the blocks become the base and the labels become
  the block labels (`blockLab`, at the window points). Equivariance comes from stage 14a's
  `blockLabel_smul`, non-constancy from `hint_blockLabel`; `2 k ≤ m` (`RunsWithin.m2aProg`).
  The cost depends on the size of the label array (`mapLabelsProg`).
-/

@[expose] public section

namespace GraphIso.Main

open Equiv Cost GraphIso GraphIso.Toolkit GraphIso.Recursion GraphIso.Programs Pointwise

/-! ### Validity from the group -/

/-- `π` on a natural number: `π i` below `N`, the identity above. -/
def pAt {N : ℕ} (π : Perm (Fin N)) (i : ℕ) : ℕ := if h : i < N then (π ⟨i, h⟩).val else i

theorem pAt_of_lt {N : ℕ} (π : Perm (Fin N)) {i : ℕ} (h : i < N) :
    pAt π i = (π ⟨i, h⟩).val := by
  simp [pAt, h]

theorem get_eq_pAt {N : ℕ} {g : PermData} (hg : g.Valid N) {i : ℕ} (hi : i < N) :
    get g.1 i = pAt (PermData.denote N g) i := by
  rw [pAt_of_lt _ hi, PermData.val_denote_apply hg]

/-- **Hint data is valid for a generating list** once the labels are equivariant for every
element of the generated group. -/
theorem hintValid_of_forall {n N : ℕ} {hs : GensData} {w : WinData} {L : LabelData}
    (hle : n ≤ N) (hhs : GensData.AllValid N hs)
    (hbase : IsInvariant (GensData.denote N hs) (baseSet n N))
    (hwin : ∀ i ∈ w.1, i < n) (hlt : ∀ i ∈ w.1, ∀ j ∈ L.getD i [], j < N - n)
    (hnd : ∀ i ∈ w.1, (L.getD i []).Nodup)
    (heq : ∀ π ∈ GensData.denote N hs, ∀ i ∈ w.1,
      (L.getD (pAt π i) []).toFinset = ((L.getD i []).map fun j => pAt π (n + j) - n).toFinset)
    (hnc : ∃ i ∈ w.1, ∃ j ∈ w.1, (L.getD i []).toFinset ≠ (L.getD j []).toFinset) :
    HintValid n N hs w L := by
  refine ⟨hle, hbase, hwin, hlt, hnd, fun g hg i hi => ?_, hnc⟩
  have hgv := hhs g hg
  have hmem : PermData.denote N g ∈ GensData.denote N hs :=
    Subgroup.subset_closure ⟨g, hg, rfl⟩
  have hiN : i < N := by have := hwin i hi; omega
  rw [get_eq_pAt hgv hiN, heq _ hmem i hi]
  congr 1
  refine List.map_congr_left fun j hj => ?_
  have hj' := hlt i hi j hj
  rw [get_eq_pAt hgv (by omega)]

/-! ### M0: the maximal blocks of the window -/

section M0Prog

variable {D : Ty} {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- The labels of M0: the block index of every string position. -/
def labM0D (n : ℕ) (bidx : Array ℕ) : LabelData :=
  ((List.range n).map fun i => [get bidx i]).toArray

/-- The label of one position. -/
def labM0El (bidx : var (.array .nat)) (i : var .nat) : Prog S rec var (.list .nat) :=
  .bind (.op2 .arrayGet bidx i) fun b => .bind (.op0 .nil) fun nil => .op2 .cons b nil

/-- The labels of M0. -/
def labM0Prog (n : var .nat) (bidx : var (.array .nat)) : Prog S rec var (.array (.list .nat)) :=
  .bind (.op1 .range n) fun is => .bind (mapList is fun i => labM0El bidx i) fun ls =>
  .op1 .arrayOfList ls

/-- **M0**: re-base onto the maximal blocks of the window, with labels `u ↦ {block of u}`.
Returns the group, the window at the new degree, and the labels. -/
def m0Prog (n N : var .nat) (gs : var Ty.gens) (w : var Ty.win) :
    Prog (groupSig D) rec var (.prod (Ty.group D) (.prod Ty.win (.array (.list .nat)))) :=
  .bind (.op1 .fst w) fun pts =>
  .bind (Luks.maxBlocksProg N gs pts) fun bs =>
  .bind (Toolkit.rebaseProg n N gs bs) fun G' =>
  .bind (blockIdxProg N bs) fun bidx =>
  .bind (.op1 .length bs) fun k => .bind (.op2 .add n k) fun nk =>
  .bind (mkWindow nk pts) fun w' =>
  .bind (labM0Prog n bidx) fun L' =>
  .bind (.op2 .pair w' L') fun wl => .op2 .pair G' wl

end M0Prog

section M0Spec

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}

/-- The data M0 computes. -/
def m0Model (O : Oracle (groupSig D)) (n N : ℕ) (gs : GensData) (w : WinData) :
    GroupData D.denote × (WinData × LabelData) :=
  (rebaseModel O n N (Luks.maxBlocks N gs w.1) gs,
    (WinData.ofPoints (n + (Luks.maxBlocks N gs w.1).length) w.1,
      labM0D n (blockIdx N (Luks.maxBlocks N gs w.1))))

/-- The cost of M0 for `p` window points and `s` generators. -/
def m0Cost (n N p s Bgen : ℕ) : ℕ :=
  1 + Luks.maxBlocksCost N p s + rebaseCost n N p p s Bgen + (2 * N + 15 * p + 6) + (p + 1) +
    1 + (2 * (n + p) + 5 * p + 7) + (8 * n + 4) + 2

theorem RunsWithin.labM0El (bidx : Array ℕ) (i : ℕ) :
    RunsWithin X body (Main.labM0El bidx i) [get bidx i] 3 := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim _ _
  case hc => simp [Prim.cost]

theorem RunsWithin.labM0Prog (n : ℕ) (bidx : Array ℕ) :
    RunsWithin X body (Main.labM0Prog n bidx) (labM0D n bidx) (8 * n + 4) := by
  have hm := RunsWithin.mapList_le (X := X) (body := body) (a' := .nat) (b' := .list .nat)
    (xs := List.range n) (c := 3) (F := fun i => [get bidx i]) (f := fun i => Main.labM0El bidx i)
    fun i _ => RunsWithin.labM0El bidx i
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step hm
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, Args.head_cons, List.length_range, List.length_map]
    omega

theorem getD_labM0D {n : ℕ} {bidx : Array ℕ} {i : ℕ} (hi : i < n) :
    (labM0D n bidx).getD i [] = [get bidx i] := by
  simp [labM0D, Array.getD_eq_getD_getElem?, hi]

/-- The window points lie in blocks, and their block indices are below the number of blocks. -/
theorem mf_block_of_mem {N : ℕ} {w : WinData} {bs : List (List ℕ)} (hw : w.Valid N)
    (hbs : IsBlockList w bs) {i : ℕ} (hi : i ∈ w.1) :
    ∃ t, ∃ ht : t < bs.length, i ∈ bs[t] ∧ get (blockIdx N bs) i = t := by
  obtain ⟨t, ht, hit⟩ := exists_block hbs hi
  exact ⟨t, ht, hit, get_blockIdx hw hbs ht hit⟩

theorem mf_length_le_of_isBlockList {w : WinData} {bs : List (List ℕ)} (hbs : IsBlockList w bs) :
    bs.length ≤ w.1.length := by
  rw [← hbs.1.length_eq, List.length_flatten]
  have : ∀ b ∈ bs, 1 ≤ b.length := fun b hb =>
    List.length_pos_iff.2 (hbs.2 b hb)
  calc bs.length = (bs.map fun _ => 1).sum := by simp
    _ ≤ (bs.map List.length).sum := List.sum_le_sum fun b hb => this b hb

/-- **M0.** -/
theorem RunsWithin.m0Prog (hO : MeetsContractOn DV rebaseOps X.O)
    (hPre : ∀ op x, rebaseOps op → GroupPre DV op x → X.Pre op x) {n N : ℕ} {gs : GensData}
    {w : WinData} (hn : n ≤ N) (hbase : IsInvariant (GensData.denote N gs) (baseSet n N))
    (hw : w.Valid N) (hwin : ∀ i ∈ w.1, i < n) (hgs : GensData.AllValid N gs)
    (hinv : IsInvariant (GensData.denote N gs) (w.denote N))
    (hfaith : ∀ g ∈ GensData.denote N gs, (∀ j : Fin N, j.val < n → g j = j) → g = 1)
    (htr : IsTransOn (GensData.denote N gs) (w.denote N)) (h2 : 2 ≤ w.1.length) {Bgen : ℕ}
    (hB : X.B.call GroupOp.generate (n + (Luks.maxBlocks N gs w.1).length,
        rebaseGens n N (Luks.maxBlocks N gs w.1) gs)
      (rebaseModel X.O n N (Luks.maxBlocks N gs w.1) gs) ≤ Bgen) :
    RunsWithin X body (Main.m0Prog n N gs w) (m0Model X.O n N gs w)
        (m0Cost n N w.1.length gs.length Bgen) ∧
      (m0Model X.O n N gs w).1.1 = n + (Luks.maxBlocks N gs w.1).length ∧
      GroupValid DV (n + (Luks.maxBlocks N gs w.1).length) (m0Model X.O n N gs w).1.2.1
        (m0Model X.O n N gs w).1.2.2 ∧
      HintValid n (n + (Luks.maxBlocks N gs w.1).length) (m0Model X.O n N gs w).1.2.1
        (m0Model X.O n N gs w).2.1 (m0Model X.O n N gs w).2.2 ∧
      (∀ g ∈ GensData.denote (n + (Luks.maxBlocks N gs w.1).length) (m0Model X.O n N gs w).1.2.1,
        (∀ j : Fin (n + (Luks.maxBlocks N gs w.1).length), j.val < n → g j = j) → g = 1) ∧
      (m0Model X.O n N gs w).2.1.Valid (n + (Luks.maxBlocks N gs w.1).length) ∧
      IsInvariant
        (GensData.denote (n + (Luks.maxBlocks N gs w.1).length) (m0Model X.O n N gs w).1.2.1)
        ((m0Model X.O n N gs w).2.1.denote (n + (Luks.maxBlocks N gs w.1).length)) ∧
      IsTransOn
        (GensData.denote (n + (Luks.maxBlocks N gs w.1).length) (m0Model X.O n N gs w).1.2.1)
        ((m0Model X.O n N gs w).2.1.denote (n + (Luks.maxBlocks N gs w.1).length)) ∧
      2 ≤ (Luks.maxBlocks N gs w.1).length ∧ (Luks.maxBlocks N gs w.1).length ≤ w.1.length ∧
      ∃ θ : ↥(GensData.denote N gs) ≃*
          ↥(GensData.denote (n + (Luks.maxBlocks N gs w.1).length) (m0Model X.O n N gs w).1.2.1),
        ∀ (g : ↥(GensData.denote N gs)) (j : ℕ) (hj : j < n),
          ((θ g : Perm (Fin (n + (Luks.maxBlocks N gs w.1).length))) ⟨j, by omega⟩).val =
            (g.1 ⟨j, by omega⟩).val := by
  set G := GensData.denote N gs with hGdef
  set bs := Luks.maxBlocks N gs w.1 with hbsdef
  -- transitivity in the form of `maxBlocks_spec`
  obtain ⟨u, rest, hpts⟩ : ∃ u rest, w.1 = u :: rest := by
    rcases h : w.1 with _ | ⟨u, rest⟩
    · rw [h] at h2; simp at h2
    · exact ⟨u, rest, rfl⟩
  have hrest : rest ≠ [] := by
    intro h
    rw [hpts, h] at h2
    simp at h2
  have hu : u ∈ w.1 := hpts ▸ List.mem_cons_self
  have htr' : ∀ j, j ∈ w.1 ↔ SameOrbit G u j := by
    intro j
    constructor
    · intro hj
      obtain ⟨g, hg, hgu⟩ := htr ⟨u, hw.lt u hu⟩ hu ⟨j, hw.lt j hj⟩ hj
      exact ⟨hw.lt u hu, hw.lt j hj, g, hg, hgu⟩
    · rintro ⟨hu', hj', g, hg, hgu⟩
      have := hinv g hg ⟨u, hu'⟩ hu
      rw [hgu] at this
      exact this
  obtain ⟨hbs, hGb, h2k, -, -⟩ := Luks.maxBlocks_spec hw hgs hinv hpts hrest htr'
  rw [← hbsdef] at hbs hGb h2k
  obtain ⟨hrun, hdeg, hval, hden⟩ := RunsWithin.rebaseProg (D := D) (X := X) (body := body)
    (DV := DV) hO hPre hn hbase hw hbs hGb hgs hB
  have hkp : bs.length ≤ w.1.length := mf_length_le_of_isBlockList hbs
  have hflat : bs.flatten.length = w.1.length := hbs.1.length_eq
  set G' := (rebaseModel X.O n N bs gs) with hG'def
  set k := bs.length with hkdef
  have hstr := isInvariant_strSet hbase
  have hlenk : (Luks.maxBlocks N gs w.1).length = k := rfl
  have hmodel : m0Model X.O n N gs w = (G', (WinData.ofPoints (n + k) w.1,
      labM0D n (blockIdx N bs))) := rfl
  rw [hmodel]
  dsimp only
  -- the run
  refine ⟨?_, hdeg, hval, ?_⟩
  · have hmb := Luks.RunsWithin.maxBlocksProg (X := X) (body := body)
      (Luks.win_of_valid hw hgs hinv)
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step hmb
      run_step hrun
      run_step (RunsWithin.blockIdxProg N bs)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.mkWindow _ _)
      run_step (RunsWithin.labM0Prog n _)
      run_step (RunsWithin.prim _ _)
      exact RunsWithin.prim _ _
    case hc =>
      simp only [Prim.cost, Prim.eval, Args.head_cons, m0Cost]
      rw [hflat]
      have hrc : rebaseCost n N w.1.length k gs.length Bgen ≤
          rebaseCost n N w.1.length w.1.length gs.length Bgen := by
        simp only [rebaseCost]
        have := Nat.mul_le_mul_left gs.length (show 6 * N + 12 * n + 26 * k + 25 ≤
          6 * N + 12 * n + 26 * w.1.length + 25 by omega)
        omega
      omega
  -- the semantics
  have hmemR : ∀ π ∈ GensData.denote (n + k) G'.2.1,
      ∃ g : ↥G, π = rebaseHom hn hstr hw hbs hGb g := by
    intro π hπ
    rw [hden] at hπ
    obtain ⟨g, rfl⟩ := hπ
    exact ⟨g, rfl⟩
  have hval' : GensData.AllValid (n + k) G'.2.1 := hval.1
  have hpAt_lt : ∀ (g : ↥G) {i : ℕ} (hi : i < n),
      pAt (rebaseHom hn hstr hw hbs hGb g) i = (g.1 ⟨i, by omega⟩).val := by
    intro g i hi
    rw [pAt_of_lt _ (by omega), rebaseHom_lt hn hstr hw hbs hGb g (show i < n from hi)]
  have hpAt_ge : ∀ (g : ↥G) {t : ℕ} (ht : t < k),
      pAt (rebaseHom hn hstr hw hbs hGb g) (n + t) - n = blockMap N bs g t := by
    intro g t ht
    rw [pAt_of_lt _ (by omega), rebaseHom_ge hn hstr hw hbs hGb g (show n ≤ n + t by omega)]
    simp
  have hbinv : IsInvariant (GensData.denote (n + k) G'.2.1) (baseSet n (n + k)) := by
    rw [hden]; exact (rebase_invariant hn hstr hw hbs hGb).1
  have hwv : (WinData.ofPoints (n + k) w.1).Valid (n + k) :=
    WinData.valid_ofPoints hw.nodup fun i hi => by have := hwin i hi; omega
  refine ⟨?_, ?_, hwv, ?_, ?_, h2k, hkp, ?_⟩
  · -- the hint data
    refine hintValid_of_forall (by omega) hval' hbinv (by simpa using hwin) ?_ ?_ ?_ ?_
    · intro i hi j hj
      simp only [WinData.ofPoints_fst] at hi
      rw [getD_labM0D (hwin i hi), List.mem_singleton] at hj
      obtain ⟨t, ht, -, hbt⟩ := mf_block_of_mem hw hbs hi
      rw [hj, hbt]
      omega
    · intro i hi
      simp only [WinData.ofPoints_fst] at hi
      rw [getD_labM0D (hwin i hi)]
      exact List.nodup_singleton _
    · intro π hπ i hi
      simp only [WinData.ofPoints_fst] at hi
      obtain ⟨g, rfl⟩ := hmemR π hπ
      have hin := hwin i hi
      rw [hpAt_lt g hin]
      have hgi : (g.1 ⟨i, hw.lt i hi⟩).val ∈ w.1 := hinv g.1 g.2 ⟨i, hw.lt i hi⟩ hi
      rw [getD_labM0D (hwin _ hgi), getD_labM0D hin]
      obtain ⟨t, ht, hit, hbt⟩ := mf_block_of_mem hw hbs hi
      rw [hbt, List.map_singleton, hpAt_ge g ht,
        blockMap_eq hw hbs hGb g.2 ht (u := ⟨i, hw.lt i hi⟩) hit]
    · obtain ⟨b0, hb0, rfl⟩ : ∃ b0 ∈ bs, b0 = bs[0] := ⟨_, List.getElem_mem (by omega), rfl⟩
      obtain ⟨v0, hv0⟩ := List.exists_mem_of_ne_nil _ (hbs.2 _ hb0)
      obtain ⟨v1, hv1⟩ := List.exists_mem_of_ne_nil _ (hbs.2 _ (List.getElem_mem
        (show 1 < bs.length by omega)))
      have hw0 := mem_of_block hbs (by omega) hv0
      have hw1 := mem_of_block hbs (show 1 < bs.length by omega) hv1
      refine ⟨v0, by simpa using hw0, v1, by simpa using hw1, ?_⟩
      rw [getD_labM0D (hwin _ hw0), getD_labM0D (hwin _ hw1),
        get_blockIdx hw hbs (by omega) hv0, get_blockIdx hw hbs (by omega) hv1]
      simp
  · -- faithfulness
    rw [hden]
    exact rebase_faithful hn hstr hw hbs hGb hfaith
  · -- invariance of the window
    intro π hπ x hx
    obtain ⟨g, rfl⟩ := hmemR π hπ
    change x.val ∈ (WinData.ofPoints (n + k) w.1).1 at hx
    simp only [WinData.ofPoints_fst] at hx
    change (rebaseHom hn hstr hw hbs hGb g x).val ∈ (WinData.ofPoints (n + k) w.1).1
    simp only [WinData.ofPoints_fst]
    rw [rebaseHom_lt hn hstr hw hbs hGb g (show x.val < n from hwin _ hx)]
    exact hinv g.1 g.2 ⟨x.val, hw.lt _ hx⟩ hx
  · -- transitivity on the window
    intro x hx y hy
    change x.val ∈ (WinData.ofPoints (n + k) w.1).1 at hx
    change y.val ∈ (WinData.ofPoints (n + k) w.1).1 at hy
    simp only [WinData.ofPoints_fst] at hx hy
    obtain ⟨g, hg, hgxy⟩ := htr ⟨x.val, hw.lt _ hx⟩ hx ⟨y.val, hw.lt _ hy⟩ hy
    refine ⟨rebaseHom hn hstr hw hbs hGb ⟨g, hg⟩, by rw [hden]; exact ⟨_, rfl⟩, ?_⟩
    apply Fin.ext
    rw [rebaseHom_lt hn hstr hw hbs hGb ⟨g, hg⟩ (show x.val < n from hwin _ hx)]
    exact congrArg Fin.val hgxy
  · -- the isomorphism
    obtain ⟨θ, hθ, -, -⟩ := rebase_iso hn hstr hw hbs hGb hfaith hden
    exact ⟨θ, hθ⟩

end M0Spec

section M0Wf

variable {D : Ty} {S : Signature} {rec : Ty × Ty} {var₁ var₂ : Ty → Type} {r : Bool}
  {Γ : WfCtx var₁ var₂}

theorem wf_labM0Prog {n₁ : var₁ .nat} {n₂ : var₂ .nat} {b₁ : var₁ (.array .nat)}
    {b₂ : var₂ (.array .nat)} (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (hb : ⟨.array .nat, b₁, b₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (labM0Prog n₁ b₁) (labM0Prog n₂ b₂) := by
  unfold labM0Prog labM0El mapList
  prog_wf

theorem wf_m0Prog {n₁ N₁ : var₁ .nat} {n₂ N₂ : var₂ .nat} {g₁ : var₁ Ty.gens}
    {g₂ : var₂ Ty.gens} {w₁ : var₁ Ty.win} {w₂ : var₂ Ty.win} (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ)
    (hN : ⟨.nat, N₁, N₂⟩ ∈ Γ) (hg : ⟨Ty.gens, g₁, g₂⟩ ∈ Γ) (hw : ⟨Ty.win, w₁, w₂⟩ ∈ Γ) :
    Prog.Wf (rec := rec) r Γ (m0Prog (D := D) n₁ N₁ g₁ w₁) (m0Prog (D := D) n₂ N₂ g₂ w₂) := by
  unfold m0Prog
  refine .bind (.prim _ (.cons hw .nil)) fun p₁ p₂ => ?_
  refine .bind (Luks.wf_maxBlocksProg (by simp [hN]) (by simp [hg]) (List.Mem.head _))
    fun b₁ b₂ => ?_
  refine .bind (wf_rebaseProg (by simp [hn]) (by simp [hN]) (by simp [hg]) (List.Mem.head _))
    fun G₁ G₂ => ?_
  refine .bind (by unfold blockIdxProg mapList; prog_wf) fun i₁ i₂ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun k₁ k₂ => ?_
  refine .bind (.prim _ (.cons (by simp [hn]) (.cons (List.Mem.head _) .nil))) fun c₁ c₂ => ?_
  refine .bind (wf_mkWindow (List.Mem.head _) (by simp)) fun v₁ v₂ => ?_
  refine .bind (wf_labM0Prog (by simp [hn]) (by simp)) fun l₁ l₂ => ?_
  refine .bind (.prim _ (.cons (by simp) (.cons (List.Mem.head _) .nil))) fun q₁ q₂ => ?_
  exact .prim _ (.cons (by simp) (.cons (List.Mem.head _) .nil))

end M0Wf

/-! ### Facts shared by M1 and M2a -/

section Shared

variable {N n : ℕ} {w : WinData} {bs : List (List ℕ)} {G : Subgroup (Perm (Fin N))}

theorem pAt_rebaseHom_lt (hn : n ≤ N) (hG : IsInvariant G (strSet n N)) (hw : w.Valid N)
    (hbs : IsBlockList w bs) (hGb : PermutesBlocks G bs) (g : ↥G) {i : ℕ} (hi : i < n) :
    pAt (rebaseHom hn hG hw hbs hGb g) i = (g.1 ⟨i, by omega⟩).val := by
  rw [pAt_of_lt _ (by omega), rebaseHom_lt hn hG hw hbs hGb g (show i < n from hi)]

theorem pAt_rebaseHom_ge (hn : n ≤ N) (hG : IsInvariant G (strSet n N)) (hw : w.Valid N)
    (hbs : IsBlockList w bs) (hGb : PermutesBlocks G bs) (g : ↥G) {t : ℕ}
    (ht : t < bs.length) :
    pAt (rebaseHom hn hG hw hbs hGb g) (n + t) - n = blockMap N bs g t := by
  rw [pAt_of_lt _ (by omega), rebaseHom_ge hn hG hw hbs hGb g (show n ≤ n + t by omega)]
  simp

/-- **The labels' equivariance on data**, for every element of the group. -/
theorem mf_lab_mem_iff {gs : GensData} {L : LabelData} (hL : HintValid n N gs w L)
    (hgs : GensData.AllValid N gs) (hw : w.Valid N)
    (hinv : IsInvariant (GensData.denote N gs) (w.denote N)) {g : Perm (Fin N)}
    (hg : g ∈ GensData.denote N gs) {i : ℕ} (hi : i ∈ w.1) {j : ℕ} :
    j ∈ L.getD (g ⟨i, hw.lt i hi⟩).val [] ↔
      ∃ j' ∈ L.getD i [], ∃ h : n + j' < N, (g ⟨n + j', h⟩).val = n + j := by
  have hh := hL.isHint hgs hw hinv
  have he := hh.equivar ⟨g, hg⟩ ⟨i, hw.lt i hi⟩ (mem_winFinset.2 hi)
  have hgi : (g ⟨i, hw.lt i hi⟩).val ∈ w.1 := hinv g hg ⟨i, hw.lt i hi⟩ hi
  constructor
  · intro hj
    have hjm : j < N - n := hL.lab_lt _ hgi j hj
    have hmem : (⟨j, hjm⟩ : Fin (N - n)) ∈ labOf n N L (g ⟨i, hw.lt i hi⟩) := mem_labOf.2 hj
    have hmem' : (⟨j, hjm⟩ : Fin (N - n)) ∈
        baseHom (GensData.denote N gs) n hL.base_inv ⟨g, hg⟩ • labOf n N L ⟨i, hw.lt i hi⟩ := by
      rw [← he]; exact hmem
    obtain ⟨x, hx, hxj⟩ := Finset.mem_smul_finset.1 hmem'
    have hb := baseHom_apply (hG := hL.base_inv) ⟨g, hg⟩ x
    refine ⟨x.val, mem_labOf.1 hx, by have := x.2; omega, ?_⟩
    have := congrArg Fin.val hb
    rw [show baseHom (GensData.denote N gs) n hL.base_inv ⟨g, hg⟩ x = ⟨j, hjm⟩ from hxj] at this
    exact this.symm
  · rintro ⟨j', hj', hlt, hgj⟩
    have hj'm : j' < N - n := by omega
    have hx : (⟨j', hj'm⟩ : Fin (N - n)) ∈ labOf n N L ⟨i, hw.lt i hi⟩ := mem_labOf.2 hj'
    have hb := congrArg Fin.val (baseHom_apply (hG := hL.base_inv) ⟨g, hg⟩ ⟨j', hj'm⟩)
    have hjm : j < N - n := by have := (g ⟨n + j', hlt⟩).2; omega
    have hval : (baseHom (GensData.denote N gs) n hL.base_inv ⟨g, hg⟩ ⟨j', hj'm⟩) =
        ⟨j, hjm⟩ := by
      apply Fin.ext
      dsimp only
      change n + (baseHom _ n _ ⟨g, hg⟩ ⟨j', hj'm⟩).val = (g ⟨n + j', _⟩).val at hb
      omega
    have : (⟨j, hjm⟩ : Fin (N - n)) ∈
        baseHom (GensData.denote N gs) n hL.base_inv ⟨g, hg⟩ • labOf n N L ⟨i, hw.lt i hi⟩ :=
      Finset.mem_smul_finset.2 ⟨_, hx, hval⟩
    rw [← he] at this
    exact mem_labOf.1 this

/-- A duplicate-free list of numbers below `m` has at most `m` entries. -/
theorem mf_length_le_of_nodup {l : List ℕ} {m : ℕ} (hnd : l.Nodup) (hlt : ∀ j ∈ l, j < m) :
    l.length ≤ m := by
  have hsub : l.toFinset ⊆ Finset.range m := fun j hj =>
    Finset.mem_range.2 (hlt j (List.mem_toFinset.1 hj))
  rw [← List.toFinset_card_of_nodup hnd]
  simpa using Finset.card_le_card hsub

end Shared

/-! ### M1: an orbit of the base action -/

section M1Data

/-- The label `l` restricted to the base points of the orbit `o` (listed as positions). -/
def interO (n : ℕ) (o : List ℕ) (l : List ℕ) : List ℕ := l.filter fun j => decide (n + j ∈ o)

/-- The labels restricted to the orbit `o` are not constant on the window points `pts`. -/
def ncD (n m : ℕ) (L : LabelData) (pts : List ℕ) (o : List ℕ) : Bool :=
  pts.any fun i => pts.any fun j =>
    !SoJTree.setEqD m (interO n o (L.getD i [])) (interO n o (L.getD j []))

/-- The chosen orbit: the first on which the labels are not constant. -/
def pickD (n m : ℕ) (L : LabelData) (pts : List ℕ) (os : List (List ℕ)) : List ℕ :=
  (os.filter (ncD n m L pts)).headD (os.headD [])

/-- The singleton blocks of a list of points. -/
def singD (O : List ℕ) : List (List ℕ) := O.map fun p => [p]

/-- The labels of M1: at a window position (mask `mk`), the indices `t` with `O[t] − n` in the
label; elsewhere empty, so that labels off the window cost nothing. -/
def labM1D (n : ℕ) (O : List ℕ) (L : LabelData) (mk : Array Bool) : LabelData :=
  ((List.range n).map fun i => if getB mk i then
    (List.range O.length).filter fun t => decide (O.getD t 0 - n ∈ L.getD i []) else []).toArray

theorem mem_interO {n : ℕ} {o l : List ℕ} {j : ℕ} : j ∈ interO n o l ↔ j ∈ l ∧ n + j ∈ o := by
  simp [interO]

theorem getD_labM1D {n : ℕ} {O : List ℕ} {L : LabelData} {mk : Array Bool} {i : ℕ}
    (hi : i < n) (hm : getB mk i = true) :
    (labM1D n O L mk).getD i [] =
      (List.range O.length).filter fun t => decide (O.getD t 0 - n ∈ L.getD i []) := by
  simp [labM1D, Array.getD_eq_getD_getElem?, hi, hm]

theorem mem_labM1D {n : ℕ} {O : List ℕ} {L : LabelData} {mk : Array Bool} {i : ℕ} (hi : i < n)
    (hm : getB mk i = true) {t : ℕ} :
    t ∈ (labM1D n O L mk).getD i [] ↔ t < O.length ∧ O.getD t 0 - n ∈ L.getD i [] := by
  rw [getD_labM1D hi hm]
  simp

theorem flatten_singD (O : List ℕ) : (singD O).flatten = O := by
  induction O with
  | nil => rfl
  | cons p O ih => simp [singD] at ih ⊢; exact ih

theorem length_singD (O : List ℕ) : (singD O).length = O.length := by simp [singD]

end M1Data

section M1Prog

variable {D : Ty} {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- `interO` as a program. -/
def interOProg (n : var .nat) (o l : var (.list .nat)) : Prog S rec var (.list .nat) :=
  Toolkit.filterList l fun j => .bind (.op2 .add n j) fun p => SoJProg.memProg p o

/-- Whether the labels of `i` and `j`, restricted to `o`, differ. -/
def ncPairProg (n m : var .nat) (L : var (.array (.list .nat))) (o : var (.list .nat))
    (i j : var .nat) : Prog S rec var .bool :=
  .bind (.op2 .arrayGet L i) fun li => .bind (.op2 .arrayGet L j) fun lj =>
  .bind (interOProg n o li) fun a' => .bind (interOProg n o lj) fun b' =>
  .bind (SoJTree.setEqProg m a' b') fun e => .op1 .not e

/-- `ncD` as a program. -/
def ncProg (n m : var .nat) (L : var (.array (.list .nat))) (pts o : var (.list .nat)) :
    Prog S rec var .bool :=
  anyList pts fun i => anyList pts fun j => ncPairProg n m L o i j

/-- `pickD` as a program. -/
def pickProg (n m : var .nat) (L : var (.array (.list .nat))) (pts : var (.list .nat))
    (os : var (.list (.list .nat))) : Prog S rec var (.list .nat) :=
  .bind (Toolkit.filterList os fun o => ncProg n m L pts o) fun fs =>
  .caseList fs (.caseList os (.op0 .nil) fun o _ => .ret o) fun o _ => .ret o

/-- The label of M1 at one position. -/
def labM1El (n : var .nat) (OA : var (.array .nat)) (ts : var (.list .nat))
    (L : var (.array (.list .nat))) (mk : var (.array .bool)) (i : var .nat) :
    Prog S rec var (.list .nat) :=
  .bind (.op2 .arrayGet mk i) fun b => .ite b
    (.bind (.op2 .arrayGet L i) fun li =>
      Toolkit.filterList ts fun t => .bind (.op2 .arrayGet OA t) fun p =>
        .bind (.op2 .sub p n) fun j => SoJProg.memProg j li)
    (.op0 .nil)

/-- The labels of M1. -/
def labM1Prog (n : var .nat) (O : var (.list .nat)) (L : var (.array (.list .nat)))
    (mk : var (.array .bool)) : Prog S rec var (.array (.list .nat)) :=
  .bind (.op1 .arrayOfList O) fun OA => .bind (.op1 .length O) fun k =>
  .bind (.op1 .range k) fun ts => .bind (.op1 .range n) fun is =>
  .bind (mapList is fun i => labM1El n OA ts L mk i) fun ls => .op1 .arrayOfList ls

/-- The singleton blocks. -/
def singProg (O : var (.list .nat)) : Prog S rec var (.list (.list .nat)) :=
  mapList O fun p => .bind (.op0 .nil) fun e => .op2 .cons p e

/-- **M1**: re-base onto an orbit of the base action on which the labels are not constant. -/
def m1Prog (n N : var .nat) (G : var (Ty.group D)) (w : var Ty.win)
    (L : var (.array (.list .nat))) :
    Prog (groupSig D) rec var (.prod (Ty.group D) (.prod Ty.win (.array (.list .nat)))) :=
  .bind (baseWinProg n N) fun bw =>
  .bind (.op2 .pair G bw) fun a' =>
  .bind (Prog.call (S := groupSig D) GroupOp.orbits a') fun os =>
  .bind (.op1 .fst w) fun pts =>
  .bind (.op2 .sub N n) fun m =>
  .bind (pickProg n m L pts os) fun O =>
  .bind (singProg O) fun bs =>
  .bind (.op1 .snd G) fun gd => .bind (.op1 .fst gd) fun gs =>
  .bind (Toolkit.rebaseProg n N gs bs) fun G' =>
  .bind (.op1 .length bs) fun k => .bind (.op2 .add n k) fun nk =>
  .bind (mkWindow nk pts) fun w' =>
  .bind (.op1 .snd w) fun mk =>
  .bind (labM1Prog n O L mk) fun L' =>
  .bind (.op2 .pair w' L') fun wl => .op2 .pair G' wl

end M1Prog

section M1Costs

/-- The cost of `interOProg` on a label of at most `Lb` entries and an orbit of at most `m`
points. -/
def interOCost (m Lb : ℕ) : ℕ := Lb * (3 * m + 6) + 3

/-- The cost of `ncPairProg`. -/
def ncPairCost (m Lb : ℕ) : ℕ := 2 * interOCost m Lb + SoJTree.setEqCost m Lb + 3

/-- The cost of `ncProg` on `p` window points. -/
def ncCost (p m Lb : ℕ) : ℕ := p * (p * (ncPairCost m Lb + 2) + 3) + 1

/-- The cost of `pickProg` on at most `m` orbits. -/
def pickCost (p m Lb : ℕ) : ℕ := m * (ncCost p m Lb + 4) + 6

/-- The cost of `labM1Prog` for `n` positions, an orbit of `k ≤ m` points and labels of at most
`Lb` entries. -/
def labM1Cost (n m Lb : ℕ) : ℕ :=
  3 * (m + 1) + (n + 1) + (n * (m * (3 * Lb + 7) + 10) + 2) + (n + 1)

/-- The cost of M1: `p` window points, `s` generators, the charges of `orbits` and `generate`. -/
def m1Cost (n N p s Borb Bgen : ℕ) : ℕ :=
  baseWinCost n N + 1 + Borb + 2 + pickCost p (N - n) (N - n) + ((N - n) * 5 + 2) + 2 +
    rebaseCost n N (N - n) (N - n) s Bgen + (N - n + 1) + 1 +
    (2 * (n + (N - n)) + 5 * p + 7) + 1 + labM1Cost n (N - n) (N - n) + 2

end M1Costs

section M1Spec

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}

theorem RunsWithin.interOProg (n : ℕ) {o l : List ℕ} {m Lb : ℕ} (ho : o.length ≤ m)
    (hl : l.length ≤ Lb) :
    RunsWithin X body (Main.interOProg n o l) (interO n o l) (interOCost m Lb) := by
  have hf := RunsWithin.filterList (X := X) (body := body) (a' := .nat) (xs := l)
    (c := 3 * m + 2) (P := fun j => decide (n + j ∈ o))
    (p := fun j => Prog.bind (Prog.op2 Prim.add n j) fun p => SoJProg.memProg p o)
    fun j _ => by
      refine (RunsWithin.bind (RunsWithin.prim _ _) (SoJProg.RunsWithin.memProg _ o)).mono ?_
      simp only [Prim.cost]
      omega
  refine hf.mono ?_
  simp only [interOCost]
  have : l.length * (3 * m + 2 + 4) ≤ Lb * (3 * m + 6) :=
    Nat.mul_le_mul hl (by omega)
  omega

theorem RunsWithin.ncPairProg (n m : ℕ) (L : LabelData) {o : List ℕ} {Lb : ℕ}
    (ho : o.length ≤ m) {i j : ℕ} (hi : (L.getD i []).length ≤ Lb)
    (hj : (L.getD j []).length ≤ Lb) :
    RunsWithin X body (Main.ncPairProg n m L o i j)
      (!SoJTree.setEqD m (interO n o (L.getD i [])) (interO n o (L.getD j [])))
      (ncPairCost m Lb) := by
  have hi' : (interO n o (L.getD i [])).length ≤ Lb :=
    (List.length_filter_le _ _).trans hi
  have hj' : (interO n o (L.getD j [])).length ≤ Lb :=
    (List.length_filter_le _ _).trans hj
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    simp only [Prim.eval]
    run_step (RunsWithin.interOProg n ho hi)
    run_step (RunsWithin.interOProg n ho hj)
    run_step (SoJTree.RunsWithin.setEqProg (X := X) (body := body) m hi' hj')
    exact RunsWithin.prim _ _
  case hc =>
    simp only [Prim.cost, ncPairCost]
    omega

theorem RunsWithin.ncProg (n m : ℕ) (L : LabelData) {pts o : List ℕ} {Lb : ℕ}
    (ho : o.length ≤ m) (hL : ∀ i ∈ pts, (L.getD i []).length ≤ Lb) :
    RunsWithin X body (Main.ncProg n m L pts o) (ncD n m L pts o) (ncCost pts.length m Lb) := by
  have h := RunsWithin.anyList_le (X := X) (body := body) (a' := .nat) (xs := pts)
    (c := pts.length * (ncPairCost m Lb + 2) + 1)
    (P := fun i => pts.any fun j =>
      !SoJTree.setEqD m (interO n o (L.getD i [])) (interO n o (L.getD j [])))
    (p := fun i => anyList (a' := .nat) pts fun j => Main.ncPairProg n m L o i j) fun i hi =>
      RunsWithin.anyList_le (a' := .nat) fun j hj =>
        RunsWithin.ncPairProg n m L ho (hL i hi) (hL j hj)
  refine h.mono ?_
  simp only [ncCost]
  have : pts.length * (pts.length * (ncPairCost m Lb + 2) + 1 + 2) =
      pts.length * (pts.length * (ncPairCost m Lb + 2) + 3) := by ring
  omega

theorem RunsWithin.pickProg (n m : ℕ) (L : LabelData) {pts : List ℕ}
    {os : List (List ℕ)} {Lb : ℕ} (hos : ∀ o ∈ os, o.length ≤ m) (hosl : os.length ≤ m)
    (hL : ∀ i ∈ pts, (L.getD i []).length ≤ Lb) :
    RunsWithin X body (Main.pickProg n m L pts os) (pickD n m L pts os)
      (pickCost pts.length m Lb) := by
  have hf := RunsWithin.filterList (X := X) (body := body) (a' := .list .nat) (xs := os)
    (c := ncCost pts.length m Lb) (P := ncD n m L pts)
    (p := fun o => Main.ncProg n m L pts o) fun o ho => RunsWithin.ncProg n m L (hos o ho) hL
  refine RunsWithin.bind_le hf ?_ ?_ (c₂ := 3)
  · unfold pickD
    cases os.filter (ncD n m L pts) with
    | nil =>
      cases os with
      | nil => exact (RunsWithin.caseList_nil (RunsWithin.caseList_nil
          (RunsWithin.prim _ _))).mono (by simp [Prim.cost])
      | cons o os' => exact (RunsWithin.caseList_nil (RunsWithin.caseList_cons
          (RunsWithin.ret _))).mono (by omega)
    | cons o rest => exact (RunsWithin.caseList_cons (RunsWithin.ret _)).mono (by omega)
  · simp only [pickCost]
    have := Nat.mul_le_mul_right (ncCost pts.length m Lb + 4) hosl
    omega

theorem RunsWithin.labM1El (n : ℕ) (O : List ℕ) (L : LabelData) (mk : Array Bool) {i Lb : ℕ}
    (hi : getB mk i = true → (L.getD i []).length ≤ Lb) :
    RunsWithin X body (Main.labM1El n O.toArray (List.range O.length) L mk i)
      (if getB mk i then
        (List.range O.length).filter fun t => decide (O.getD t 0 - n ∈ L.getD i []) else [])
      (2 + (1 + (O.length * (3 * Lb + 7) + 3))) := by
  refine RunsWithin.bind_le (RunsWithin.prim _ _) ?_ (le_of_eq (by simp [Prim.cost]; omega))
    (c₂ := 1 + (1 + (O.length * (3 * Lb + 7) + 3)))
  have hb : Prim.eval (Prim.arrayGet (a := .bool)) (Args.cons (var := Ty.denote) mk
      (Args.cons i Args.nil)) = getB mk i := rfl
  rw [hb]
  cases hm : getB mk i with
  | false =>
    exact (RunsWithin.ite_false (RunsWithin.prim _ _)).mono (by simp only [Prim.cost]; omega)
  | true =>
  have hi := hi hm
  refine RunsWithin.ite_true ?_
  refine RunsWithin.bind (RunsWithin.prim _ _) ?_
  simp only [Prim.eval]
  refine (RunsWithin.filterList (a' := .nat) (c := 3 * Lb + 3)
    (P := fun t => decide (O.getD t 0 - n ∈ L.getD i [])) fun t _ => ?_).mono ?_
  · refine (RunsWithin.bind (RunsWithin.prim _ _)
      (RunsWithin.bind (RunsWithin.prim _ _) (SoJProg.RunsWithin.memProg _ _))).of_eq ?_ |>.mono ?_
    · simp [Prim.eval, Ty.default, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
    · simp only [Prim.cost, Ty.default]
      omega
  · simp

theorem RunsWithin.labM1Prog (n : ℕ) (O : List ℕ) (L : LabelData) (mk : Array Bool) {m Lb : ℕ}
    (hO : O.length ≤ m) (hL : ∀ i < n, getB mk i = true → (L.getD i []).length ≤ Lb) :
    RunsWithin X body (Main.labM1Prog n O L mk) (labM1D n O L mk) (labM1Cost n m Lb) := by
  have hm := RunsWithin.mapList_le (X := X) (body := body) (a' := .nat) (b' := .list .nat)
    (xs := List.range n) (c := 2 + (1 + (m * (3 * Lb + 7) + 3)))
    (F := fun i => if getB mk i then
      (List.range O.length).filter fun t => decide (O.getD t 0 - n ∈ L.getD i []) else [])
    (f := fun i => Main.labM1El n O.toArray (List.range O.length) L mk i) fun i hi =>
      (RunsWithin.labM1El n O L mk (hL i (List.mem_range.1 hi))).mono (by
        have := Nat.mul_le_mul_right (3 * Lb + 7) hO
        omega)
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    simp only [Prim.eval]
    run_step hm
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head_cons, List.length_range, List.length_map,
      labM1Cost]
    have : n * (2 + (1 + (m * (3 * Lb + 7) + 3)) + 3) ≤ n * (m * (3 * Lb + 7) + 10) :=
      Nat.mul_le_mul_left _ (by omega)
    omega

theorem RunsWithin.singProg (O : List ℕ) :
    RunsWithin X body (Main.singProg O) (singD O) (O.length * 5 + 2) := by
  have hm := RunsWithin.mapList_le (X := X) (body := body) (a' := .nat) (b' := .list .nat)
    (xs := O) (c := 2) (F := fun p => [p])
    (f := fun p => Prog.bind (Prog.op0 Prim.nil) fun e => Prog.op2 Prim.cons p e)
    fun p _ => (RunsWithin.bind (RunsWithin.prim _ _) (RunsWithin.prim _ _)).mono
      (by simp [Prim.cost])
  exact hm

end M1Spec

section M1Facts

variable {n N : ℕ}

/-- An orbit on which the labels are not constant exists. -/
theorem mf_exists_ncD {gs : GensData} {w : WinData} {L : LabelData} (hL : HintValid n N gs w L)
    {os : List (List ℕ)} (hos : os.flatten.Perm (basePts n N)) :
    ∃ o ∈ os, ncD n (N - n) L w.1 o = true := by
  obtain ⟨i, hi, j, hj, hne⟩ := hL.nonconst
  obtain ⟨x, hx⟩ : ∃ x, ¬(x ∈ L.getD i [] ↔ x ∈ L.getD j []) := by
    by_contra hcon
    push Not at hcon
    exact hne (Finset.ext fun x => by simpa only [List.mem_toFinset] using hcon x)
  have hxm : x < N - n := by
    by_cases h : x ∈ L.getD i []
    · exact hL.lab_lt i hi x h
    · exact hL.lab_lt j hj x (by tauto)
  have hxb : n + x ∈ os.flatten := hos.mem_iff.2 (mem_basePts.2 ⟨by omega, by omega⟩)
  obtain ⟨o, ho, hxo⟩ := List.mem_flatten.1 hxb
  refine ⟨o, ho, List.any_eq_true.2 ⟨i, hi, List.any_eq_true.2 ⟨j, hj, ?_⟩⟩⟩
  rw [Bool.not_eq_true']
  rw [← Bool.not_eq_true]
  intro hse
  rw [SoJTree.setEqD, List.all_eq_true] at hse
  have := hse x (List.mem_range.2 hxm)
  simp only [decide_eq_true_eq, mem_interO] at this
  exact hx ⟨fun h => (this.1 ⟨h, hxo⟩).1, fun h => (this.2 ⟨h, hxo⟩).1⟩

/-- The chosen orbit is an orbit with non-constant labels. -/
theorem mf_pickD_spec {m : ℕ} {L : LabelData} {pts : List ℕ} {os : List (List ℕ)}
    (h : ∃ o ∈ os, ncD n m L pts o = true) :
    pickD n m L pts os ∈ os ∧ ncD n m L pts (pickD n m L pts os) = true := by
  obtain ⟨o, ho, hnc⟩ := h
  have hmem : o ∈ os.filter (ncD n m L pts) := List.mem_filter.2 ⟨ho, hnc⟩
  unfold pickD
  cases hf : os.filter (ncD n m L pts) with
  | nil => rw [hf] at hmem; simp at hmem
  | cons o' rest =>
    have : o' ∈ os.filter (ncD n m L pts) := hf ▸ List.mem_cons_self
    rw [List.headD_cons]
    exact List.mem_filter.1 this

/-- The facts about an orbit of the base action. -/
theorem mf_orbit {G : Subgroup (Perm (Fin N))} {os : List (List ℕ)}
    (hos : IsOrbitPartition G (baseWin n N) os) {o : List ℕ} (ho : o ∈ os) :
    o.Nodup ∧ (∀ x ∈ o, n ≤ x ∧ x < N) ∧ o.length ≤ N - n ∧
      ∀ i ∈ o, ∀ j, j ∈ o ↔ SameOrbit G i j := by
  have hp : os.flatten.Perm (basePts n N) := hos.1
  have hsub := List.sublist_flatten_of_mem ho
  refine ⟨(hp.nodup_iff.2 (basePts_nodup n N)).sublist hsub,
    fun x hx => mem_basePts.1 (hp.mem_iff.1 (List.mem_flatten.2 ⟨o, ho, hx⟩)), ?_,
    (hos.2 o ho).2⟩
  rw [← length_basePts n N, ← hp.length_eq]
  exact hsub.length_le

theorem mf_sing_isBlockList {O : List ℕ} : IsBlockList (WinData.ofPoints N O) (singD O) := by
  refine ⟨by rw [flatten_singD]; exact List.Perm.refl _, fun b hb => ?_⟩
  simp only [singD, List.mem_map] at hb
  obtain ⟨p, -, rfl⟩ := hb
  simp

theorem mf_sing_permutes {G : Subgroup (Perm (Fin N))} {O : List ℕ}
    (horb : ∀ i ∈ O, ∀ j, j ∈ O ↔ SameOrbit G i j) : PermutesBlocks G (singD O) := by
  intro g hg b hb
  simp only [singD, List.mem_map] at hb
  obtain ⟨p, hp, rfl⟩ := hb
  obtain ⟨hpN, -, -⟩ := (horb p hp p).1 hp
  have hgp : (g ⟨p, hpN⟩).val ∈ O :=
    (horb p hp _).2 ⟨hpN, (g ⟨p, hpN⟩).2, g, hg, rfl⟩
  refine ⟨[(g ⟨p, hpN⟩).val], List.mem_map.2 ⟨_, hgp, rfl⟩, fun u hu => ?_⟩
  rw [List.mem_singleton] at hu ⊢
  rw [show u = ⟨p, hpN⟩ from Fin.ext hu]

theorem mf_getElem_singD {O : List ℕ} {t : ℕ} (ht : t < (singD O).length) :
    (singD O)[t] = [O[t]'(by rwa [length_singD] at ht)] := by
  simp [singD]

/-- For singleton blocks, the block map is the action on the listed points. -/
theorem mf_blockMap_sing {G : Subgroup (Perm (Fin N))} {O : List ℕ}
    (hw : (WinData.ofPoints N O).Valid N) (hGb : PermutesBlocks G (singD O))
    {g : Perm (Fin N)} (hg : g ∈ G) {s : ℕ} (hs : s < O.length) :
    ∃ h : blockMap N (singD O) g s < O.length,
      (g ⟨O[s], hw.lt _ (List.getElem_mem hs)⟩).val = O[blockMap N (singD O) g s] := by
  have hs' : s < (singD O).length := by rw [length_singD]; exact hs
  obtain ⟨ht', himg⟩ := blockMap_spec hw mf_sing_isBlockList hGb hg hs'
  have := himg ⟨O[s], hw.lt _ (List.getElem_mem hs)⟩
    (by rw [mf_getElem_singD hs']; exact List.mem_singleton_self _)
  rw [mf_getElem_singD ht', List.mem_singleton] at this
  exact ⟨by rwa [length_singD] at ht', this⟩

end M1Facts

section M1Main

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}

/-- The backend operations used by M1. -/
def m1Ops (op : GroupOp) : Prop := op = .orbits ∨ op = .generate

/-- The orbit M1 chooses. -/
def m1O (O : Oracle (groupSig D)) (n N : ℕ) (G : GroupData D.denote) (w : WinData)
    (L : LabelData) : List ℕ :=
  pickD n (N - n) L w.1 (O.run GroupOp.orbits (G, baseWin n N))

/-- The data M1 computes. -/
def m1Model (O : Oracle (groupSig D)) (n N : ℕ) (G : GroupData D.denote) (w : WinData)
    (L : LabelData) : GroupData D.denote × (WinData × LabelData) :=
  (rebaseModel O n N (singD (m1O O n N G w L)) G.2.1,
    (WinData.ofPoints (n + (singD (m1O O n N G w L)).length) w.1,
      labM1D n (m1O O n N G w L) L w.2))

/-- **M1**: for valid hint data, re-base onto an orbit `O` of the base action on which the
labels are not constant, with labels `lab ∩ O`. The new base has `k = |O| ≤ N − n` points, and
`k < N − n` when the base action is not transitive. -/
theorem RunsWithin.m1Prog (hO : MeetsContractOn DV m1Ops X.O)
    (hPre : ∀ op x, m1Ops op → GroupPre DV op x → X.Pre op x) {n N : ℕ} {gs : GensData}
    {d : D.denote} {w : WinData} {L : LabelData} (hGv : GroupValid DV N gs d) (hw : w.Valid N)
    (hinv : IsInvariant (GensData.denote N gs) (w.denote N))
    (hfaith : ∀ g ∈ GensData.denote N gs, (∀ j : Fin N, j.val < n → g j = j) → g = 1)
    (htr : IsTransOn (GensData.denote N gs) (w.denote N)) (hL : HintValid n N gs w L)
    {Borb Bgen : ℕ}
    (hBo : X.B.call GroupOp.orbits ((N, gs, d), baseWin n N)
      (X.O.run GroupOp.orbits ((N, gs, d), baseWin n N)) ≤ Borb)
    (hB : X.B.call GroupOp.generate (n + (singD (m1O X.O n N (N, gs, d) w L)).length,
        rebaseGens n N (singD (m1O X.O n N (N, gs, d) w L)) gs)
      (rebaseModel X.O n N (singD (m1O X.O n N (N, gs, d) w L)) gs) ≤ Bgen) :
    RunsWithin X body (Main.m1Prog n N (N, gs, d) w L) (m1Model X.O n N (N, gs, d) w L)
        (m1Cost n N w.1.length gs.length Borb Bgen) ∧
      (m1Model X.O n N (N, gs, d) w L).1.1 = n + (singD (m1O X.O n N (N, gs, d) w L)).length ∧
      GroupValid DV (n + (singD (m1O X.O n N (N, gs, d) w L)).length)
        (m1Model X.O n N (N, gs, d) w L).1.2.1 (m1Model X.O n N (N, gs, d) w L).1.2.2 ∧
      HintValid n (n + (singD (m1O X.O n N (N, gs, d) w L)).length)
        (m1Model X.O n N (N, gs, d) w L).1.2.1 (m1Model X.O n N (N, gs, d) w L).2.1
        (m1Model X.O n N (N, gs, d) w L).2.2 ∧
      (∀ g ∈ GensData.denote (n + (singD (m1O X.O n N (N, gs, d) w L)).length)
          (m1Model X.O n N (N, gs, d) w L).1.2.1,
        (∀ j : Fin (n + (singD (m1O X.O n N (N, gs, d) w L)).length), j.val < n → g j = j) →
          g = 1) ∧
      (m1Model X.O n N (N, gs, d) w L).2.1.Valid
        (n + (singD (m1O X.O n N (N, gs, d) w L)).length) ∧
      IsInvariant
        (GensData.denote (n + (singD (m1O X.O n N (N, gs, d) w L)).length)
          (m1Model X.O n N (N, gs, d) w L).1.2.1)
        ((m1Model X.O n N (N, gs, d) w L).2.1.denote
          (n + (singD (m1O X.O n N (N, gs, d) w L)).length)) ∧
      IsTransOn
        (GensData.denote (n + (singD (m1O X.O n N (N, gs, d) w L)).length)
          (m1Model X.O n N (N, gs, d) w L).1.2.1)
        ((m1Model X.O n N (N, gs, d) w L).2.1.denote
          (n + (singD (m1O X.O n N (N, gs, d) w L)).length)) ∧
      (singD (m1O X.O n N (N, gs, d) w L)).length ≤ N - n ∧
      (¬ IsTransOn (GensData.denote N gs) (baseSet n N) →
        (singD (m1O X.O n N (N, gs, d) w L)).length < N - n) ∧
      ∃ θ : ↥(GensData.denote N gs) ≃*
          ↥(GensData.denote (n + (singD (m1O X.O n N (N, gs, d) w L)).length)
            (m1Model X.O n N (N, gs, d) w L).1.2.1),
        ∀ (g : ↥(GensData.denote N gs)) (j : ℕ) (hj : j < n),
          ((θ g : Perm (Fin (n + (singD (m1O X.O n N (N, gs, d) w L)).length)))
            ⟨j, by omega⟩).val = (g.1 ⟨j, by have := hL.le; omega⟩).val := by
  have hn := hL.le
  have hbase := hL.base_inv
  have hwin := hL.win_lt
  set G := GensData.denote N gs with hGdef
  have hpre : GroupPre DV .orbits ((N, gs, d), baseWin n N) :=
    ⟨hGv, baseWin_valid n N, by rw [baseWin_denote]; exact hbase⟩
  have hos : IsOrbitPartition G (baseWin n N) (X.O.run GroupOp.orbits ((N, gs, d), baseWin n N)) :=
    hO .orbits _ (Or.inl rfl) hpre
  set os : List (List ℕ) := X.O.run GroupOp.orbits ((N, gs, d), baseWin n N) with hosdef
  obtain ⟨hOmem, hOnc⟩ := mf_pickD_spec (mf_exists_ncD hL (os := os) hos.1)
  have hOdef : m1O X.O n N (N, gs, d) w L = pickD n (N - n) L w.1 os := rfl
  set O := m1O X.O n N (N, gs, d) w L with hOdef'
  rw [← hOdef] at hOmem hOnc
  obtain ⟨hOnd, hObase, hOlen, horb⟩ := mf_orbit hos hOmem
  have hwO : (WinData.ofPoints N O).Valid N :=
    WinData.valid_ofPoints hOnd fun x hx => (hObase x hx).2
  have hbs : IsBlockList (WinData.ofPoints N O) (singD O) := mf_sing_isBlockList
  have hGb : PermutesBlocks G (singD O) := mf_sing_permutes horb
  obtain ⟨hrun, hdeg, hval, hden⟩ := RunsWithin.rebaseProg (D := D) (X := X) (body := body)
    (DV := DV) (fun op x hop hx => hO op x (Or.inr hop) hx)
    (fun op x hop hx => hPre op x (Or.inr hop) hx) hn hbase hwO hbs hGb hGv.1 hB
  set G' := rebaseModel X.O n N (singD O) gs with hG'def
  set k := (singD O).length with hkdef
  have hkO : k = O.length := length_singD O
  have hk' : (singD (m1O X.O n N (N, gs, d) w L)).length = k := rfl
  have hstr := isInvariant_strSet hbase
  have hmodel : m1Model X.O n N (N, gs, d) w L = (G', (WinData.ofPoints (n + k) w.1,
      labM1D n O L w.2)) := rfl
  rw [hmodel]
  dsimp only
  -- bounds on the data
  have hosl : os.length ≤ N - n := by
    have := mf_length_le_of_isBlockList (w := baseWin n N) ⟨hos.1, fun o ho => (hos.2 o ho).1⟩
    rwa [show (baseWin n N).1 = basePts n N from rfl, length_basePts] at this
  have hosb : ∀ o ∈ os, o.length ≤ N - n := fun o ho => (mf_orbit hos ho).2.2.1
  have hLb : ∀ i ∈ w.1, (L.getD i []).length ≤ N - n := fun i hi =>
    mf_length_le_of_nodup (hL.lab_nodup i hi) (hL.lab_lt i hi)
  have hmask : ∀ i < N, getB w.2 i = true ↔ i ∈ w.1 := hw.mask_iff
  -- the run
  refine ⟨?_, hdeg, hval, ?_⟩
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.baseWinProg n N)
      run_step (RunsWithin.prim _ _)
      simp only [Prim.eval]
      run_step (RunsWithin.call (hPre _ _ (Or.inl rfl) hpre))
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      simp only [Prim.eval]
      run_step (RunsWithin.pickProg n (N - n) L hosb hosl hLb)
      run_step (RunsWithin.singProg _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      simp only [Prim.eval]
      run_step hrun
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      simp only [Prim.eval]
      run_step (RunsWithin.mkWindow _ _)
      run_step (RunsWithin.prim _ _)
      simp only [Prim.eval]
      run_step (RunsWithin.labM1Prog n _ L w.2 (m := N - n) (Lb := N - n) hOlen
        fun i hi hm => hLb i ((hmask i (by have := hL.le; omega)).1 hm))
      run_step (RunsWithin.prim _ _)
      exact RunsWithin.prim _ _
    case hc =>
      simp only [Prim.cost, Args.head_cons, m1Cost, flatten_singD]
      have hq : X.B.call GroupOp.orbits ((N, gs, d), baseWin n N)
          (X.O.run GroupOp.orbits ((N, gs, d), baseWin n N)) ≤ Borb := hBo
      have hs1 : (pickD n (N - n) L w.1
          (X.O.run GroupOp.orbits ((N, gs, d), baseWin n N))).length = O.length := rfl
      have hs2 : (singD (pickD n (N - n) L w.1
          (X.O.run GroupOp.orbits ((N, gs, d), baseWin n N)))).length = k := rfl
      have hrc : rebaseCost n N O.length k gs.length Bgen ≤
          rebaseCost n N (N - n) (N - n) gs.length Bgen := by
        simp only [rebaseCost]
        have := Nat.mul_le_mul_left gs.length (show 6 * N + 12 * n + 26 * k + 25 ≤
          6 * N + 12 * n + 26 * (N - n) + 25 by omega)
        omega
      omega
  -- the semantics
  have hmemR : ∀ π ∈ GensData.denote (n + k) G'.2.1,
      ∃ g : ↥G, π = rebaseHom hn hstr hwO hbs hGb g := by
    intro π hπ
    rw [hden] at hπ
    obtain ⟨g, rfl⟩ := hπ
    exact ⟨g, rfl⟩
  have hval' : GensData.AllValid (n + k) G'.2.1 := hval.1
  have hpAt_lt : ∀ (g : ↥G) {i : ℕ} (hi : i < n),
      pAt (rebaseHom hn hstr hwO hbs hGb g) i = (g.1 ⟨i, by omega⟩).val :=
    fun g _ hi => pAt_rebaseHom_lt hn hstr hwO hbs hGb g hi
  have hpAt_ge : ∀ (g : ↥G) {t : ℕ} (ht : t < k),
      pAt (rebaseHom hn hstr hwO hbs hGb g) (n + t) - n = blockMap N (singD O) g t :=
    fun g _ ht => pAt_rebaseHom_ge hn hstr hwO hbs hGb g ht
  have hbinv : IsInvariant (GensData.denote (n + k) G'.2.1) (baseSet n (n + k)) := by
    rw [hden]; exact (rebase_invariant hn hstr hwO hbs hGb).1
  have hwv : (WinData.ofPoints (n + k) w.1).Valid (n + k) :=
    WinData.valid_ofPoints hw.nodup fun i hi => by have := hwin i hi; omega
  have hOget : ∀ {t : ℕ} (ht : t < O.length), O.getD t 0 = O[t] := fun ht => by
    simp [List.getD_eq_getElem?_getD, ht]
  have hmw : ∀ i ∈ w.1, getB w.2 i = true := fun i hi => (hmask i (hw.lt i hi)).2 hi
  refine ⟨?_, ?_, hwv, ?_, ?_, by omega, ?_, ?_⟩
  · -- the hint data
    refine hintValid_of_forall (by omega) hval' hbinv (by simpa using hwin) ?_ ?_ ?_ ?_
    · intro i hi t ht
      simp only [WinData.ofPoints_fst] at hi
      rw [mem_labM1D (hwin i hi) (hmw i hi)] at ht
      omega
    · intro i hi
      simp only [WinData.ofPoints_fst] at hi
      rw [getD_labM1D (hwin i hi) (hmw i hi)]
      exact List.nodup_range.filter _
    · intro π hπ i hi
      simp only [WinData.ofPoints_fst] at hi
      obtain ⟨g, rfl⟩ := hmemR π hπ
      have hin := hwin i hi
      rw [hpAt_lt g hin]
      have hiN := hw.lt i hi
      have hgi : (g.1 ⟨i, hiN⟩).val ∈ w.1 := hinv g.1 g.2 ⟨i, hiN⟩ hi
      ext t
      simp only [List.mem_toFinset, List.mem_map]
      rw [mem_labM1D (hwin _ hgi) (hmw _ hgi)]
      constructor
      · rintro ⟨ht, htl⟩
        rw [hOget ht] at htl
        obtain ⟨j', hj', hlt, hgj⟩ := (mf_lab_mem_iff hL hGv.1 hw hinv g.2 hi).1 htl
        have hOt := hObase _ (List.getElem_mem ht)
        have hgj' : g.1 ⟨n + j', hlt⟩ = ⟨O[t], hOt.2⟩ := Fin.ext (by
          rw [hgj]; dsimp only; omega)
        have hnj : n + j' ∈ O := by
          refine (horb _ (List.getElem_mem ht) _).2 ⟨hOt.2, hlt, g.1⁻¹, G.inv_mem g.2, ?_⟩
          rw [← hgj']
          simp
        obtain ⟨s, hs, hsO⟩ := List.getElem_of_mem hnj
        obtain ⟨hbm, hbmeq⟩ := mf_blockMap_sing hwO hGb g.2 hs
        refine ⟨s, (mem_labM1D hin (hmw i hi)).2 ⟨hs, ?_⟩, ?_⟩
        · rw [hOget hs, hsO]
          simpa using hj'
        · rw [hpAt_ge g (by omega : s < k)]
          have hfin : (⟨O[s], hwO.lt _ (List.getElem_mem hs)⟩ : Fin N) = ⟨n + j', hlt⟩ :=
            Fin.ext hsO
          rw [hfin, hgj'] at hbmeq
          have h2 : O[blockMap N (singD O) g s] = O[t] := by rw [← hbmeq]
          exact (hOnd.getElem_inj_iff).1 h2
      · rintro ⟨s, hs, rfl⟩
        rw [mem_labM1D hin (hmw i hi)] at hs
        obtain ⟨hsl, hsL⟩ := hs
        rw [hOget hsl] at hsL
        obtain ⟨hbm, hbmeq⟩ := mf_blockMap_sing hwO hGb g.2 hsl
        rw [hpAt_ge g (by omega : s < k)]
        refine ⟨hbm, ?_⟩
        rw [hOget hbm]
        have hOs := hObase _ (List.getElem_mem hsl)
        refine (mf_lab_mem_iff hL hGv.1 hw hinv g.2 hi).2 ⟨O[s] - n, hsL, by omega, ?_⟩
        have hfin : (⟨n + (O[s] - n), by omega⟩ : Fin N) =
            ⟨O[s], hwO.lt _ (List.getElem_mem hsl)⟩ := Fin.ext (by dsimp only; omega)
        rw [hfin, hbmeq]
        have := hObase _ (List.getElem_mem hbm)
        omega
    · -- the labels are not constant
      obtain ⟨i, hi, j, hj, hne⟩ : ∃ i ∈ w.1, ∃ j ∈ w.1, SoJTree.setEqD (N - n)
          (interO n O (L.getD i [])) (interO n O (L.getD j [])) = false := by
        simp only [ncD, List.any_eq_true, Bool.not_eq_true'] at hOnc
        exact hOnc
      obtain ⟨x, hxm, hx⟩ : ∃ x < N - n,
          ¬(x ∈ interO n O (L.getD i []) ↔ x ∈ interO n O (L.getD j [])) := by
        by_contra hcon
        push Not at hcon
        rw [← Bool.not_eq_true] at hne
        apply hne
        rw [SoJTree.setEqD, List.all_eq_true]
        intro y hy
        simpa using hcon y (List.mem_range.1 hy)
      have hxO : n + x ∈ O := by
        simp only [mem_interO] at hx
        tauto
      obtain ⟨s, hs, hsO⟩ := List.getElem_of_mem hxO
      have hsx : O.getD s 0 - n = x := by rw [hOget hs, hsO]; omega
      refine ⟨i, by simpa using hi, j, by simpa using hj, fun heq => hx ?_⟩
      have := congrArg (s ∈ ·) heq
      simp only [List.mem_toFinset, eq_iff_iff] at this
      rw [mem_labM1D (hwin i hi) (hmw i hi), mem_labM1D (hwin j hj) (hmw j hj), hsx] at this
      simp only [mem_interO, hxO, and_true]
      exact ⟨fun h => (this.1 ⟨hs, h⟩).2, fun h => (this.2 ⟨hs, h⟩).2⟩
  · -- faithfulness
    rw [hden]
    exact rebase_faithful hn hstr hwO hbs hGb hfaith
  · -- invariance of the window
    intro π hπ x hx
    obtain ⟨g, rfl⟩ := hmemR π hπ
    change x.val ∈ (WinData.ofPoints (n + k) w.1).1 at hx
    simp only [WinData.ofPoints_fst] at hx
    change (rebaseHom hn hstr hwO hbs hGb g x).val ∈ (WinData.ofPoints (n + k) w.1).1
    simp only [WinData.ofPoints_fst]
    rw [rebaseHom_lt hn hstr hwO hbs hGb g (show x.val < n from hwin _ hx)]
    exact hinv g.1 g.2 ⟨x.val, hw.lt _ hx⟩ hx
  · -- transitivity on the window
    intro x hx y hy
    change x.val ∈ (WinData.ofPoints (n + k) w.1).1 at hx
    change y.val ∈ (WinData.ofPoints (n + k) w.1).1 at hy
    simp only [WinData.ofPoints_fst] at hx hy
    obtain ⟨g, hg, hgxy⟩ := htr ⟨x.val, hw.lt _ hx⟩ hx ⟨y.val, hw.lt _ hy⟩ hy
    refine ⟨rebaseHom hn hstr hwO hbs hGb ⟨g, hg⟩, by rw [hden]; exact ⟨_, rfl⟩, ?_⟩
    apply Fin.ext
    rw [rebaseHom_lt hn hstr hwO hbs hGb ⟨g, hg⟩ (show x.val < n from hwin _ hx)]
    exact congrArg Fin.val hgxy
  · -- a proper orbit when the base action is intransitive
    intro hnt
    by_contra hge
    apply hnt
    have hsub : O.toFinset ⊆ (basePts n N).toFinset := fun x hx =>
      List.mem_toFinset.2 (mem_basePts.2 (hObase x (List.mem_toFinset.1 hx)))
    have heq := Finset.eq_of_subset_of_card_le hsub (by
      rw [List.toFinset_card_of_nodup hOnd, List.toFinset_card_of_nodup (basePts_nodup n N),
        length_basePts]
      omega)
    have hall : ∀ u : Fin N, n ≤ u.val → u.val ∈ O := fun u hu => by
      have : u.val ∈ (basePts n N).toFinset := List.mem_toFinset.2 (mem_basePts.2 ⟨hu, u.2⟩)
      rw [← heq] at this
      exact List.mem_toFinset.1 this
    intro u hu v hv
    obtain ⟨hu', hv', g, hg, hgv⟩ := (horb u.val (hall u hu) v.val).1 (hall v hv)
    exact ⟨g, hg, hgv⟩
  · -- the isomorphism
    obtain ⟨θ, hθ, -, -⟩ := rebase_iso hn hstr hwO hbs hGb hfaith hden
    exact ⟨θ, hθ⟩


/-- **M1's orbit** has no repetition and lies in the base (stage 14j-6a: the length of M1's
labels). -/
theorem m1O_facts (hO : MeetsContractOn DV m1Ops X.O) {n N : ℕ} {gs : GensData}
    {d : D.denote} {w : WinData} {L : LabelData} (hGv : GroupValid DV N gs d)
    (hL : HintValid n N gs w L) :
    (m1O X.O n N (N, gs, d) w L).Nodup ∧ ∀ p ∈ m1O X.O n N (N, gs, d) w L, n ≤ p := by
  have hpre : GroupPre DV .orbits ((N, gs, d), baseWin n N) :=
    ⟨hGv, baseWin_valid n N, by rw [baseWin_denote]; exact hL.base_inv⟩
  have hos : IsOrbitPartition (GensData.denote N gs) (baseWin n N)
      (X.O.run GroupOp.orbits ((N, gs, d), baseWin n N)) := hO .orbits _ (Or.inl rfl) hpre
  obtain ⟨hOmem, -⟩ := mf_pickD_spec (mf_exists_ncD hL
    (os := X.O.run GroupOp.orbits ((N, gs, d), baseWin n N)) hos.1)
  obtain ⟨hOnd, hObase, -, -⟩ := mf_orbit hos hOmem
  exact ⟨hOnd, fun p hp => (hObase p hp).1⟩
end M1Main

section M1Wf

variable {D : Ty} {S : Signature} {rec : Ty × Ty} {var₁ var₂ : Ty → Type} {r : Bool}
  {Γ : WfCtx var₁ var₂}

theorem wf_interOProg {n₁ : var₁ .nat} {n₂ : var₂ .nat} {o₁ l₁ : var₁ (.list .nat)}
    {o₂ l₂ : var₂ (.list .nat)} (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (ho : ⟨.list .nat, o₁, o₂⟩ ∈ Γ)
    (hl : ⟨.list .nat, l₁, l₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (interOProg n₁ o₁ l₁) (interOProg n₂ o₂ l₂) := by
  unfold interOProg
  refine Toolkit.wf_filterList hl fun Γ' hΓ j₁ j₂ hj => ?_
  refine .bind (.prim _ (.cons (hΓ hn) (.cons hj .nil))) fun p₁ p₂ => ?_
  exact SoJProg.wf_memProg (List.Mem.head _) (by simp [hΓ ho])

theorem wf_ncPairProg {n₁ m₁ i₁ j₁ : var₁ .nat} {n₂ m₂ i₂ j₂ : var₂ .nat}
    {L₁ : var₁ (.array (.list .nat))} {L₂ : var₂ (.array (.list .nat))}
    {o₁ : var₁ (.list .nat)} {o₂ : var₂ (.list .nat)} (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ)
    (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) (hL : ⟨.array (.list .nat), L₁, L₂⟩ ∈ Γ)
    (ho : ⟨.list .nat, o₁, o₂⟩ ∈ Γ) (hi : ⟨.nat, i₁, i₂⟩ ∈ Γ) (hj : ⟨.nat, j₁, j₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (ncPairProg n₁ m₁ L₁ o₁ i₁ j₁)
      (ncPairProg n₂ m₂ L₂ o₂ i₂ j₂) := by
  unfold ncPairProg
  refine .bind (.prim _ (.cons hL (.cons hi .nil))) fun a₁ a₂ => ?_
  refine .bind (.prim _ (.cons (by simp [hL]) (.cons (by simp [hj]) .nil))) fun b₁ b₂ => ?_
  refine .bind (wf_interOProg (by simp [hn]) (by simp [ho]) (by simp)) fun c₁ c₂ => ?_
  refine .bind (wf_interOProg (by simp [hn]) (by simp [ho]) (by simp)) fun e₁ e₂ => ?_
  refine .bind (SoJTree.wf_setEqProg (by simp [hm]) (by simp) (List.Mem.head _)) fun f₁ f₂ => ?_
  exact .prim _ (.cons (List.Mem.head _) .nil)

theorem wf_ncProg {n₁ m₁ : var₁ .nat} {n₂ m₂ : var₂ .nat}
    {L₁ : var₁ (.array (.list .nat))} {L₂ : var₂ (.array (.list .nat))}
    {p₁ o₁ : var₁ (.list .nat)} {p₂ o₂ : var₂ (.list .nat)} (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ)
    (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) (hL : ⟨.array (.list .nat), L₁, L₂⟩ ∈ Γ)
    (hp : ⟨.list .nat, p₁, p₂⟩ ∈ Γ) (ho : ⟨.list .nat, o₁, o₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (ncProg n₁ m₁ L₁ p₁ o₁) (ncProg n₂ m₂ L₂ p₂ o₂) := by
  unfold ncProg
  refine wf_anyList hp fun Γ' hΓ i₁ i₂ hi => wf_anyList (hΓ hp) fun Γ'' hΓ' j₁ j₂ hj => ?_
  exact wf_ncPairProg (hΓ' (hΓ hn)) (hΓ' (hΓ hm)) (hΓ' (hΓ hL)) (hΓ' (hΓ ho)) (hΓ' hi) hj

theorem wf_pickProg {n₁ m₁ : var₁ .nat} {n₂ m₂ : var₂ .nat}
    {L₁ : var₁ (.array (.list .nat))} {L₂ : var₂ (.array (.list .nat))}
    {p₁ : var₁ (.list .nat)} {p₂ : var₂ (.list .nat)} {os₁ : var₁ (.list (.list .nat))}
    {os₂ : var₂ (.list (.list .nat))} (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ)
    (hL : ⟨.array (.list .nat), L₁, L₂⟩ ∈ Γ) (hp : ⟨.list .nat, p₁, p₂⟩ ∈ Γ)
    (hos : ⟨.list (.list .nat), os₁, os₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (pickProg n₁ m₁ L₁ p₁ os₁) (pickProg n₂ m₂ L₂ p₂ os₂) := by
  unfold pickProg
  refine .bind (Toolkit.wf_filterList hos fun Γ' hΓ o₁ o₂ ho =>
    wf_ncProg (hΓ hn) (hΓ hm) (hΓ hL) (hΓ hp) ho) fun f₁ f₂ => ?_
  prog_wf

theorem wf_labM1El {n₁ i₁ : var₁ .nat} {n₂ i₂ : var₂ .nat} {OA₁ : var₁ (.array .nat)}
    {OA₂ : var₂ (.array .nat)} {ts₁ : var₁ (.list .nat)} {ts₂ : var₂ (.list .nat)}
    {L₁ : var₁ (.array (.list .nat))} {L₂ : var₂ (.array (.list .nat))}
    {mk₁ : var₁ (.array .bool)} {mk₂ : var₂ (.array .bool)} (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ)
    (hOA : ⟨.array .nat, OA₁, OA₂⟩ ∈ Γ) (hts : ⟨.list .nat, ts₁, ts₂⟩ ∈ Γ)
    (hL : ⟨.array (.list .nat), L₁, L₂⟩ ∈ Γ) (hmk : ⟨.array .bool, mk₁, mk₂⟩ ∈ Γ)
    (hi : ⟨.nat, i₁, i₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (labM1El n₁ OA₁ ts₁ L₁ mk₁ i₁)
      (labM1El n₂ OA₂ ts₂ L₂ mk₂ i₂) := by
  unfold labM1El
  refine .bind (.prim _ (.cons hmk (.cons hi .nil))) fun b₁ b₂ => ?_
  refine .ite (List.Mem.head _) ?_ (.prim _ .nil)
  refine .bind (.prim _ (.cons (by simp [hL]) (.cons (by simp [hi]) .nil))) fun c₁ c₂ => ?_
  refine Toolkit.wf_filterList (by simp [hts]) fun Γ' hΓ y₁ y₂ hy => ?_
  have h2 : ∀ {x}, x ∈ Γ → x ∈ Γ' := fun h =>
    hΓ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))
  have hc : ⟨.list .nat, c₁, c₂⟩ ∈ Γ' := hΓ List.mem_cons_self
  refine .bind (.prim _ (.cons (h2 hOA) (.cons hy .nil))) fun p₁ p₂ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) (.cons (List.mem_cons_of_mem _ (h2 hn))
    .nil))) fun j₁ j₂ => ?_
  exact SoJProg.wf_memProg (List.Mem.head _)
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hc))

theorem wf_labM1Prog {n₁ : var₁ .nat} {n₂ : var₂ .nat} {O₁ : var₁ (.list .nat)}
    {O₂ : var₂ (.list .nat)} {L₁ : var₁ (.array (.list .nat))} {L₂ : var₂ (.array (.list .nat))}
    {mk₁ : var₁ (.array .bool)} {mk₂ : var₂ (.array .bool)} (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ)
    (hO : ⟨.list .nat, O₁, O₂⟩ ∈ Γ) (hL : ⟨.array (.list .nat), L₁, L₂⟩ ∈ Γ)
    (hmk : ⟨.array .bool, mk₁, mk₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (labM1Prog n₁ O₁ L₁ mk₁) (labM1Prog n₂ O₂ L₂ mk₂) := by
  unfold labM1Prog
  refine .bind (.prim _ (.cons hO .nil)) fun a₁ a₂ => ?_
  refine .bind (.prim _ (.cons (by simp [hO]) .nil)) fun k₁ k₂ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun t₁ t₂ => ?_
  refine .bind (.prim _ (.cons (by simp [hn]) .nil)) fun i₁ i₂ => ?_
  refine .bind (wf_mapList (List.Mem.head _) fun Γ' hΓ x₁ x₂ hx =>
    wf_labM1El (hΓ (by simp [hn])) (hΓ (by simp)) (hΓ (by simp)) (hΓ (by simp [hL]))
      (hΓ (by simp [hmk])) hx) fun l₁ l₂ => ?_
  exact .prim _ (.cons (List.Mem.head _) .nil)

theorem wf_singProg {O₁ : var₁ (.list .nat)} {O₂ : var₂ (.list .nat)}
    (hO : ⟨.list .nat, O₁, O₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (singProg O₁) (singProg O₂) := by
  unfold singProg mapList
  prog_wf

theorem wf_m1Prog {n₁ N₁ : var₁ .nat} {n₂ N₂ : var₂ .nat} {G₁ : var₁ (Ty.group D)}
    {G₂ : var₂ (Ty.group D)} {w₁ : var₁ Ty.win} {w₂ : var₂ Ty.win}
    {L₁ : var₁ (.array (.list .nat))} {L₂ : var₂ (.array (.list .nat))}
    (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (hN : ⟨.nat, N₁, N₂⟩ ∈ Γ) (hG : ⟨Ty.group D, G₁, G₂⟩ ∈ Γ)
    (hw : ⟨Ty.win, w₁, w₂⟩ ∈ Γ) (hL : ⟨.array (.list .nat), L₁, L₂⟩ ∈ Γ) :
    Prog.Wf (rec := rec) r Γ (m1Prog n₁ N₁ G₁ w₁ L₁) (m1Prog n₂ N₂ G₂ w₂ L₂) := by
  unfold m1Prog
  refine .bind (wf_baseWinProg hn hN) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp [hG]) (.cons (List.Mem.head _) .nil))) fun _ _ => ?_
  refine .bind (.call _ (List.Mem.head _)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp [hw]) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp [hN]) (.cons (by simp [hn]) .nil))) fun _ _ => ?_
  refine .bind (wf_pickProg (by simp [hn]) (List.Mem.head _) (by simp [hL]) (by simp)
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.Mem.head _)))) fun _ _ => ?_
  refine .bind (wf_singProg (List.Mem.head _)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp [hG]) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (wf_rebaseProg (by simp [hn]) (by simp [hN]) (List.Mem.head _) (by simp))
    fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp [hn]) (.cons (List.Mem.head _) .nil))) fun _ _ => ?_
  refine .bind (wf_mkWindow (List.Mem.head _) (by simp)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp [hw]) .nil)) fun _ _ => ?_
  refine .bind (wf_labM1Prog (by simp [hn]) (by simp) (by simp [hL]) (List.Mem.head _))
    fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) (.cons (List.Mem.head _) .nil))) fun _ _ => ?_
  exact .prim _ (.cons (by simp) (.cons (List.Mem.head _) .nil))

end M1Wf

/-! ### M2a: block labels -/

section M2aData

variable {n N : ℕ} {bs : List (List ℕ)}

/-- The block index of every base point, indexed by base indices. -/
def m2aIdx (n N : ℕ) (bs : List (List ℕ)) : Array ℕ :=
  ((List.range (N - n)).map fun j => get (blockIdx N bs) (n + j)).toArray

/-- The labels of M2a: the block label at every window point. -/
def labM2aD (n N : ℕ) (bs : List (List ℕ)) (L : LabelData) (w : List ℕ) : LabelData :=
  mapLabels L w (blockLab bs.length (m2aIdx n N bs))

theorem mf_get_m2aIdx {j : ℕ} (hj : j < N - n) :
    get (m2aIdx n N bs) j = get (blockIdx N bs) (n + j) := by
  simp [m2aIdx, get, Array.getD_eq_getD_getElem?, hj]

theorem mf_blockLab_nil (k : ℕ) (bidx : Array ℕ) : blockLab k bidx [] = [] := by
  have h0 : ∀ i, blockCount bidx [] i = 0 := fun _ => rfl
  unfold blockLab
  split_ifs with h
  · rcases k with _ | k
    · rfl
    · exfalso
      have := List.all_eq_true.1 h 0 (by simp [blockCounts, h0]; exact ⟨0, Nat.zero_le _⟩)
      simp at this
  · simp [h0]

theorem mf_getD_labM2aD {L : LabelData} {w : List ℕ} (hw : w.Nodup) {i : ℕ} (hi : i ∈ w) :
    (labM2aD n N bs L w).getD i [] = blockLab bs.length (m2aIdx n N bs) (L.getD i []) := by
  rw [labM2aD, getD_mapLabels hw]
  by_cases h : i < L.size
  · rw [if_pos' ⟨hi, h⟩]
  · rw [if_neg' fun h' => h h'.2]
    have : L.getD i [] = [] := by
      simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (Nat.le_of_not_lt h)]
    rw [this, mf_blockLab_nil]

variable (hbs : IsBlockList (WinData.ofPoints N (basePts n N)) bs)
include hbs

/-- Block `t` of the index array is the block `bs[t]`, read as base points. -/
theorem mf_blockSet_eq {t : ℕ} (ht : t < bs.length) :
    blockSet (N - n) (m2aIdx n N bs) t = baseBlockSet n N bs[t] := by
  have hw := baseWin_valid n N
  ext x
  simp only [blockSet, Finset.mem_filter, Finset.mem_univ, true_and, mem_baseBlockSet]
  rw [mf_get_m2aIdx x.2]
  constructor
  · intro h
    obtain ⟨b, hb, hxb⟩ := exists_baseBlock hbs x
    obtain ⟨t', ht', rfl⟩ := List.getElem_of_mem hb
    have := get_blockIdx hw hbs ht' hxb
    rw [h] at this
    subst this
    exact hxb
  · exact get_blockIdx hw hbs ht

/-- The blocks of the index array are the blocks of `bs`. -/
theorem mf_blockFamily_eq :
    blockFamily (N - n) bs.length (m2aIdx n N bs) = blockFam n N bs := by
  ext B
  rw [mem_blockFamily]
  simp only [blockFam, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨bs[t], List.getElem_mem ht, (mf_blockSet_eq hbs ht).symm⟩
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hb
    exact ⟨t, ht, mf_blockSet_eq hbs ht⟩

/-- Every block of the index array is nonempty. -/
theorem mf_blockSet_ne {t : ℕ} (ht : t < bs.length) :
    ∃ x : Fin (N - n), get (m2aIdx n N bs) x.val = t := by
  obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ (hbs.2 _ (List.getElem_mem ht))
  have hpb := block_sub_base hbs (List.getElem_mem ht) hp
  refine ⟨⟨p - n, by omega⟩, ?_⟩
  rw [mf_get_m2aIdx (by dsimp only; omega), show n + (p - n) = p by omega]
  exact get_blockIdx (baseWin_valid n N) hbs ht hp

end M2aData

section M2aFacts

variable {n N : ℕ} {bs : List (List ℕ)} {gs : GensData} {w : WinData} {L : LabelData}

/-- The base action maps block `t` onto block `blockMap g t`. -/
theorem mf_smul_blockSet (hbs : IsBlockList (WinData.ofPoints N (basePts n N)) bs)
    {G : Subgroup (Perm (Fin N))} (hbase : IsInvariant G (baseSet n N))
    (hGb : PermutesBlocks G bs) (hΨ : IsBlockSys (baseHom G n hbase) (blockFam n N bs))
    (g : ↥G) {t : ℕ} (ht : t < bs.length) :
    blockMap N bs g.1 t < bs.length ∧
      baseHom G n hbase g • blockSet (N - n) (m2aIdx n N bs) t =
        blockSet (N - n) (m2aIdx n N bs) (blockMap N bs g.1 t) := by
  obtain ⟨ht', himg⟩ := blockMap_spec (baseWin_valid n N) hbs hGb g.2 ht
  refine ⟨ht', ?_⟩
  rw [mf_blockSet_eq hbs ht, mf_blockSet_eq hbs ht']
  have hX : baseHom G n hbase g • baseBlockSet n N bs[t] ∈ blockFam n N bs :=
    hΨ.inv g _ (List.mem_toFinset.2 (List.mem_map.2 ⟨_, List.getElem_mem ht, rfl⟩))
  have hY : baseBlockSet n N bs[blockMap N bs g.1 t] ∈ blockFam n N bs :=
    List.mem_toFinset.2 (List.mem_map.2 ⟨_, List.getElem_mem ht', rfl⟩)
  have hsub : baseHom G n hbase g • baseBlockSet n N bs[t] ⊆
      baseBlockSet n N bs[blockMap N bs g.1 t] := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_smul_finset.1 hx
    rw [mem_baseBlockSet] at hy ⊢
    have h1 := himg (basePos y) hy
    rw [← baseHom_apply (hG := hbase)] at h1
    exact h1
  obtain ⟨x, hx⟩ := hΨ.nonempty _ hX
  by_contra hne
  exact Finset.disjoint_left.1 (hΨ.disj _ hX _ hY hne) hx (hsub hx)

/-- Data block labels against stage 14a's `blockLabel`, at a window point. -/
theorem mf_mem_blockLab (hL : HintValid n N gs w L)
    (hbs : IsBlockList (WinData.ofPoints N (basePts n N)) bs) {v : Fin N} (hv : v.val ∈ w.1)
    {t : ℕ} (ht : t < bs.length) :
    t ∈ blockLab bs.length (m2aIdx n N bs) (L.getD v.val []) ↔
      blockSet (N - n) (m2aIdx n N bs) t ∈ blockLabel (blockFam n N bs) (labOf n N L v) := by
  rw [mem_blockLab_iff (hL.lab_nodup _ hv) (fun x => mem_labOf) (hL.lab_lt _ hv) ht,
    mf_blockFamily_eq hbs]

/-- **Equivariance of the block labels**, on data. -/
theorem mf_blockLab_equivar (hL : HintValid n N gs w L) (hgs : GensData.AllValid N gs)
    (hw : w.Valid N) (hinv : IsInvariant (GensData.denote N gs) (w.denote N))
    (hbs : IsBlockList (WinData.ofPoints N (basePts n N)) bs)
    (hGb : PermutesBlocks (GensData.denote N gs) bs)
    (hΨ : IsBlockSys (baseHom (GensData.denote N gs) n hL.base_inv) (blockFam n N bs))
    (g : ↥(GensData.denote N gs)) {u : ℕ} (hu : u ∈ w.1) {t' : ℕ} :
    t' ∈ blockLab bs.length (m2aIdx n N bs) (L.getD (g.1 ⟨u, hw.lt u hu⟩).val []) ↔
      ∃ t ∈ blockLab bs.length (m2aIdx n N bs) (L.getD u []), blockMap N bs g.1 t = t' := by
  have hh := hL.isHint hgs hw hinv
  have hgu : (g.1 ⟨u, hw.lt u hu⟩).val ∈ w.1 := hinv g.1 g.2 _ hu
  have hBL : blockLabel (blockFam n N bs) (labOf n N L (g.1 ⟨u, hw.lt u hu⟩)) =
      baseHom (GensData.denote N gs) n hL.base_inv g •
        blockLabel (blockFam n N bs) (labOf n N L ⟨u, hw.lt u hu⟩) := by
    rw [← blockLabel_smul (hΨ.smul_mem_iff g)]
    exact congrArg _ (hh.equivar g ⟨u, hw.lt u hu⟩ (mem_winFinset.2 hu))
  constructor
  · intro ht'
    have ht'k := blockLab_lt ht'
    have h1 := (mf_mem_blockLab hL hbs hgu ht'k).1 ht'
    rw [hBL] at h1
    obtain ⟨X, hX, hXe⟩ := Finset.mem_smul_finset.1 h1
    have hXΨ : X ∈ blockFamily (N - n) bs.length (m2aIdx n N bs) := by
      rw [mf_blockFamily_eq hbs]
      exact blockLabel_subset _ _ hX
    obtain ⟨t, ht, rfl⟩ := mem_blockFamily.1 hXΨ
    obtain ⟨hbm, hsm⟩ := mf_smul_blockSet hbs hL.base_inv hGb hΨ g ht
    refine ⟨t, (mf_mem_blockLab hL hbs (v := ⟨u, hw.lt u hu⟩) hu ht).2 hX, ?_⟩
    rw [hsm] at hXe
    exact blockSet_inj (fun _ hi => mf_blockSet_ne hbs hi) hbm hXe
  · rintro ⟨t, ht, rfl⟩
    have htk := blockLab_lt ht
    obtain ⟨hbm, hsm⟩ := mf_smul_blockSet hbs hL.base_inv hGb hΨ g htk
    refine (mf_mem_blockLab hL hbs hgu hbm).2 ?_
    rw [hBL, ← hsm]
    exact Finset.smul_mem_smul_finset
      ((mf_mem_blockLab hL hbs (v := ⟨u, hw.lt u hu⟩) hu htk).1 ht)

/-- **The block labels are not constant** when some label is not equidistributed over the
blocks (by `hint_blockLabel`). -/
theorem mf_blockLab_nonconst (hL : HintValid n N gs w L) (hgs : GensData.AllValid N gs)
    (hw : w.Valid N) (hinv : IsInvariant (GensData.denote N gs) (w.denote N))
    (hbs : IsBlockList (WinData.ofPoints N (basePts n N)) bs)
    (hΨ : IsBlockSys (baseHom (GensData.denote N gs) n hL.base_inv) (blockFam n N bs))
    (htrB : ∀ γ δ : Fin (N - n), ∃ g : ↥(GensData.denote N gs),
      baseHom (GensData.denote N gs) n hL.base_inv g γ = δ)
    (hne : ∃ u ∈ w.1, equidistB bs.length (m2aIdx n N bs) (L.getD u []) = false) :
    ∃ i ∈ w.1, ∃ j ∈ w.1, (blockLab bs.length (m2aIdx n N bs) (L.getD i [])).toFinset ≠
      (blockLab bs.length (m2aIdx n N bs) (L.getD j [])).toFinset := by
  have hh := hL.isHint hgs hw hinv
  obtain ⟨u₀, hu₀, he₀⟩ := hne
  have hne' : ¬ Equidist (blockFam n N bs) (labOf n N L ⟨u₀, hw.lt u₀ hu₀⟩) := by
    rw [← mf_blockFamily_eq hbs, ← equidistB_iff (hL.lab_nodup _ hu₀) (fun x => mem_labOf)
      (hL.lab_lt _ hu₀), he₀]
    simp
  have hWinv : Invariant ↥(GensData.denote N gs) (winFinset N w) := fun g u hu =>
    mem_winFinset.2 (hinv g.1 g.2 u (mem_winFinset.1 hu))
  obtain ⟨u, hu, v, hv, huv⟩ := (hint_blockLabel hΨ htrB hWinv hh
    (u₀ := ⟨u₀, hw.lt u₀ hu₀⟩) (mem_winFinset.2 hu₀) hne').nonconst
  rw [mem_winFinset] at hu hv
  refine ⟨u.val, hu, v.val, hv, fun heq => huv ?_⟩
  show subLab _ (blockLabel _ _) = subLab _ (blockLabel _ _)
  congr 1
  have key : ∀ X, X ∈ blockLabel (blockFam n N bs) (labOf n N L u) →
      X ∈ blockLabel (blockFam n N bs) (labOf n N L v) := by
    intro X hX
    have hXΨ : X ∈ blockFamily (N - n) bs.length (m2aIdx n N bs) := by
      rw [mf_blockFamily_eq hbs]
      exact blockLabel_subset _ _ hX
    obtain ⟨t, ht, rfl⟩ := mem_blockFamily.1 hXΨ
    have := (mf_mem_blockLab hL hbs hu ht).2 hX
    rw [← List.mem_toFinset, heq, List.mem_toFinset] at this
    exact (mf_mem_blockLab hL hbs hv ht).1 this
  have key' : ∀ X, X ∈ blockLabel (blockFam n N bs) (labOf n N L v) →
      X ∈ blockLabel (blockFam n N bs) (labOf n N L u) := by
    intro X hX
    have hXΨ : X ∈ blockFamily (N - n) bs.length (m2aIdx n N bs) := by
      rw [mf_blockFamily_eq hbs]
      exact blockLabel_subset _ _ hX
    obtain ⟨t, ht, rfl⟩ := mem_blockFamily.1 hXΨ
    have := (mf_mem_blockLab hL hbs hv ht).2 hX
    rw [← List.mem_toFinset, ← heq, List.mem_toFinset] at this
    exact (mf_mem_blockLab hL hbs hu ht).1 this
  exact Finset.ext fun X => ⟨key X, key' X⟩

end M2aFacts

section M2aProg

variable {D : Ty} {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- `m2aIdx` as a program, from the block-index array of the positions. -/
def m2aIdxProg (n N : var .nat) (bi : var (.array .nat)) : Prog S rec var (.array .nat) :=
  .bind (.op2 .sub N n) fun m => .bind (.op1 .range m) fun js =>
  .bind (mapList js fun j => .bind (.op2 .add n j) fun p => .op2 .arrayGet bi p) fun l =>
  .op1 .arrayOfList l

/-- **M2a**: re-base onto the blocks `bs` of the base, with the block labels. -/
def m2aProg (n N : var .nat) (gs : var Ty.gens) (w : var Ty.win)
    (L : var (.array (.list .nat))) (bs : var (.list (.list .nat))) :
    Prog (groupSig D) rec var (.prod (Ty.group D) (.prod Ty.win (.array (.list .nat)))) :=
  .bind (Toolkit.rebaseProg n N gs bs) fun G' =>
  .bind (blockIdxProg N bs) fun bi =>
  .bind (m2aIdxProg n N bi) fun bidx =>
  .bind (.op1 .length bs) fun k =>
  .bind (.op1 .fst w) fun pts =>
  .bind (mapLabelsProg L pts fun li => blockLabProg k bidx li) fun L' =>
  .bind (.op2 .add n k) fun nk =>
  .bind (mkWindow nk pts) fun w' =>
  .bind (.op2 .pair w' L') fun wl => .op2 .pair G' wl

end M2aProg

section M2aSpec

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}

/-- The data M2a computes. -/
def m2aModel (O : Oracle (groupSig D)) (n N : ℕ) (gs : GensData) (w : WinData) (L : LabelData)
    (bs : List (List ℕ)) : GroupData D.denote × (WinData × LabelData) :=
  (rebaseModel O n N bs gs, (WinData.ofPoints (n + bs.length) w.1, labM2aD n N bs L w.1))

/-- The cost of M2a: `p` window points, `s` generators, a label array of size `Ls`. -/
def m2aCost (n N p s Ls Bgen : ℕ) : ℕ :=
  rebaseCost n N (N - n) (N - n) s Bgen + (2 * N + 15 * (N - n) + 6) + (7 * (N - n) + 5) +
    (N - n + 1) + 1 + (p * (blockLabCost (N - n) (N - n) + 6) + Ls + 3) + 1 +
    (2 * (n + (N - n)) + 5 * p + 7) + 2

theorem RunsWithin.m2aIdxProg (n N : ℕ) (bi : Array ℕ) :
    RunsWithin X body (Main.m2aIdxProg n N bi)
      ((List.range (N - n)).map fun j => get bi (n + j)).toArray (7 * (N - n) + 5) := by
  have hm := RunsWithin.mapList_le (X := X) (body := body) (a' := .nat) (b' := .nat)
    (xs := List.range (N - n)) (c := 2) (F := fun j => get bi (n + j))
    (f := fun j => Prog.bind (Prog.op2 Prim.add n j) fun p => Prog.op2 Prim.arrayGet bi p)
    fun j _ => (RunsWithin.bind (RunsWithin.prim _ _) (RunsWithin.prim _ _)).of_eq
      (by simp [Prim.eval, get, Ty.default]) |>.mono (by simp [Prim.cost])
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    simp only [Prim.eval]
    run_step hm
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head_cons, List.length_range, List.length_map]
    omega

theorem mf_two_mul_length_le {bs : List (List ℕ)} (hsz : ∀ b ∈ bs, 2 ≤ b.length) :
    2 * bs.length ≤ bs.flatten.length := by
  rw [List.length_flatten]
  calc 2 * bs.length = (bs.map fun _ => 2).sum := by simp [Nat.mul_comm]
    _ ≤ (bs.map List.length).sum := List.sum_le_sum fun b hb => hsz b hb

/-- **M2a.** For valid hint data whose base action is transitive with the block system `bs`
(blocks of at least two points), if some window label is not equidistributed over the blocks,
re-base onto the blocks with the block labels: valid hint data again, with `2 k ≤ N − n` for
the `k` blocks. -/
theorem RunsWithin.m2aProg (hO : MeetsContractOn DV rebaseOps X.O)
    (hPre : ∀ op x, rebaseOps op → GroupPre DV op x → X.Pre op x) {n N : ℕ} {gs : GensData}
    {w : WinData} {L : LabelData} {bs : List (List ℕ)} (hgs : GensData.AllValid N gs)
    (hw : w.Valid N) (hinv : IsInvariant (GensData.denote N gs) (w.denote N))
    (hfaith : ∀ g ∈ GensData.denote N gs, (∀ j : Fin N, j.val < n → g j = j) → g = 1)
    (htr : IsTransOn (GensData.denote N gs) (w.denote N)) (hL : HintValid n N gs w L)
    (hbs : IsBlockList (WinData.ofPoints N (basePts n N)) bs)
    (hGb : PermutesBlocks (GensData.denote N gs) bs)
    (hΨ : IsBlockSys (baseHom (GensData.denote N gs) n hL.base_inv) (blockFam n N bs))
    (htrB : ∀ γ δ : Fin (N - n), ∃ g : ↥(GensData.denote N gs),
      baseHom (GensData.denote N gs) n hL.base_inv g γ = δ)
    (hsz : ∀ b ∈ bs, 2 ≤ b.length)
    (hne : ∃ u ∈ w.1, equidistB bs.length (m2aIdx n N bs) (L.getD u []) = false) {Bgen : ℕ}
    (hB : X.B.call GroupOp.generate (n + bs.length, rebaseGens n N bs gs)
      (rebaseModel X.O n N bs gs) ≤ Bgen) :
    RunsWithin X body (Main.m2aProg n N gs w L bs) (m2aModel X.O n N gs w L bs)
        (m2aCost n N w.1.length gs.length L.size Bgen) ∧
      (m2aModel X.O n N gs w L bs).1.1 = n + bs.length ∧
      GroupValid DV (n + bs.length) (m2aModel X.O n N gs w L bs).1.2.1
        (m2aModel X.O n N gs w L bs).1.2.2 ∧
      HintValid n (n + bs.length) (m2aModel X.O n N gs w L bs).1.2.1
        (m2aModel X.O n N gs w L bs).2.1 (m2aModel X.O n N gs w L bs).2.2 ∧
      (∀ g ∈ GensData.denote (n + bs.length) (m2aModel X.O n N gs w L bs).1.2.1,
        (∀ j : Fin (n + bs.length), j.val < n → g j = j) → g = 1) ∧
      (m2aModel X.O n N gs w L bs).2.1.Valid (n + bs.length) ∧
      IsInvariant (GensData.denote (n + bs.length) (m2aModel X.O n N gs w L bs).1.2.1)
        ((m2aModel X.O n N gs w L bs).2.1.denote (n + bs.length)) ∧
      IsTransOn (GensData.denote (n + bs.length) (m2aModel X.O n N gs w L bs).1.2.1)
        ((m2aModel X.O n N gs w L bs).2.1.denote (n + bs.length)) ∧
      2 * bs.length ≤ N - n ∧
      ∃ θ : ↥(GensData.denote N gs) ≃*
          ↥(GensData.denote (n + bs.length) (m2aModel X.O n N gs w L bs).1.2.1),
        ∀ (g : ↥(GensData.denote N gs)) (j : ℕ) (hj : j < n),
          ((θ g : Perm (Fin (n + bs.length))) ⟨j, by omega⟩).val =
            (g.1 ⟨j, by have := hL.le; omega⟩).val := by
  have hn := hL.le
  have hbase := hL.base_inv
  have hwin := hL.win_lt
  set G := GensData.denote N gs with hGdef
  have hwb : (WinData.ofPoints N (basePts n N)).Valid N := baseWin_valid n N
  obtain ⟨hrun, hdeg, hval, hden⟩ := RunsWithin.rebaseProg (D := D) (X := X) (body := body)
    (DV := DV) hO hPre hn hbase hwb hbs hGb hgs hB
  have hflat : bs.flatten.length = N - n := by
    rw [hbs.1.length_eq]
    exact length_basePts n N
  have h2k : 2 * bs.length ≤ N - n := hflat ▸ mf_two_mul_length_le hsz
  set G' := rebaseModel X.O n N bs gs with hG'def
  set k := bs.length with hkdef
  have hstr := isInvariant_strSet hbase
  have hmodel : m2aModel X.O n N gs w L bs = (G', (WinData.ofPoints (n + k) w.1,
      labM2aD n N bs L w.1)) := rfl
  rw [hmodel]
  dsimp only
  have hLb : ∀ i ∈ w.1, (L.getD i []).length ≤ N - n := fun i hi =>
    mf_length_le_of_nodup (hL.lab_nodup i hi) (hL.lab_lt i hi)
  -- the run
  refine ⟨?_, hdeg, hval, ?_⟩
  · have hml := RunsWithin.mapLabelsProg (X := X) (body := body) (L := L) (w := w.1)
      (f := fun li => Toolkit.blockLabProg k (m2aIdx n N bs) li)
      (F := blockLab k (m2aIdx n N bs)) (c := blockLabCost (N - n) (N - n)) fun i hi =>
        (RunsWithin.blockLabProg k (m2aIdx n N bs) (L.getD i [])).mono (by
          simp only [blockLabCost]
          have := Nat.mul_le_mul (show k ≤ N - n by omega)
            (show 6 * (L.getD i []).length + 21 ≤ 6 * (N - n) + 21 by have := hLb i hi; omega)
          omega)
    apply RunsWithin.mono
    case h =>
      run_step hrun
      run_step (RunsWithin.blockIdxProg N bs)
      run_step (RunsWithin.m2aIdxProg n N _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      simp only [Prim.eval]
      run_step hml
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.mkWindow _ _)
      run_step (RunsWithin.prim _ _)
      exact RunsWithin.prim _ _
    case hc =>
      simp only [Prim.cost, Prim.eval, Args.head_cons, m2aCost]
      rw [hflat]
      have hrc : rebaseCost n N (N - n) k gs.length Bgen ≤
          rebaseCost n N (N - n) (N - n) gs.length Bgen := by
        simp only [rebaseCost]
        have := Nat.mul_le_mul_left gs.length (show 6 * N + 12 * n + 26 * k + 25 ≤
          6 * N + 12 * n + 26 * (N - n) + 25 by omega)
        omega
      omega
  -- the semantics
  have hmemR : ∀ π ∈ GensData.denote (n + k) G'.2.1,
      ∃ g : ↥G, π = rebaseHom hn hstr hwb hbs hGb g := by
    intro π hπ
    rw [hden] at hπ
    obtain ⟨g, rfl⟩ := hπ
    exact ⟨g, rfl⟩
  have hval' : GensData.AllValid (n + k) G'.2.1 := hval.1
  have hpAt_lt : ∀ (g : ↥G) {i : ℕ} (hi : i < n),
      pAt (rebaseHom hn hstr hwb hbs hGb g) i = (g.1 ⟨i, by omega⟩).val :=
    fun g _ hi => pAt_rebaseHom_lt hn hstr hwb hbs hGb g hi
  have hpAt_ge : ∀ (g : ↥G) {t : ℕ} (ht : t < k),
      pAt (rebaseHom hn hstr hwb hbs hGb g) (n + t) - n = blockMap N bs g t :=
    fun g _ ht => pAt_rebaseHom_ge hn hstr hwb hbs hGb g ht
  have hbinv : IsInvariant (GensData.denote (n + k) G'.2.1) (baseSet n (n + k)) := by
    rw [hden]; exact (rebase_invariant hn hstr hwb hbs hGb).1
  have hwv : (WinData.ofPoints (n + k) w.1).Valid (n + k) :=
    WinData.valid_ofPoints hw.nodup fun i hi => by have := hwin i hi; omega
  have hlab : ∀ i ∈ w.1, (labM2aD n N bs L w.1).getD i [] =
      blockLab k (m2aIdx n N bs) (L.getD i []) := fun i hi => mf_getD_labM2aD hw.nodup hi
  refine ⟨?_, ?_, hwv, ?_, ?_, h2k, ?_⟩
  · -- the hint data
    refine hintValid_of_forall (by omega) hval' hbinv (by simpa using hwin) ?_ ?_ ?_ ?_
    · intro i hi t ht
      simp only [WinData.ofPoints_fst] at hi
      rw [hlab i hi] at ht
      have := blockLab_lt ht
      omega
    · intro i hi
      simp only [WinData.ofPoints_fst] at hi
      rw [hlab i hi]
      exact nodup_blockLab _ _ _
    · intro π hπ i hi
      simp only [WinData.ofPoints_fst] at hi
      obtain ⟨g, rfl⟩ := hmemR π hπ
      have hin := hwin i hi
      rw [hpAt_lt g hin]
      have hgi : (g.1 ⟨i, hw.lt i hi⟩).val ∈ w.1 := hinv g.1 g.2 ⟨i, hw.lt i hi⟩ hi
      rw [hlab _ hgi, hlab i hi]
      ext t'
      simp only [List.mem_toFinset, List.mem_map]
      rw [mf_blockLab_equivar hL hgs hw hinv hbs hGb hΨ g hi]
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact ⟨t, ht, hpAt_ge g (blockLab_lt ht)⟩
      · rintro ⟨t, ht, rfl⟩
        exact ⟨t, ht, (hpAt_ge g (blockLab_lt ht)).symm⟩
    · obtain ⟨i, hi, j, hj, hij⟩ := mf_blockLab_nonconst hL hgs hw hinv hbs hΨ htrB hne
      refine ⟨i, by simpa using hi, j, by simpa using hj, ?_⟩
      rw [hlab i hi, hlab j hj]
      exact hij
  · -- faithfulness
    rw [hden]
    exact rebase_faithful hn hstr hwb hbs hGb hfaith
  · -- invariance of the window
    intro π hπ x hx
    obtain ⟨g, rfl⟩ := hmemR π hπ
    change x.val ∈ (WinData.ofPoints (n + k) w.1).1 at hx
    simp only [WinData.ofPoints_fst] at hx
    change (rebaseHom hn hstr hwb hbs hGb g x).val ∈ (WinData.ofPoints (n + k) w.1).1
    simp only [WinData.ofPoints_fst]
    rw [rebaseHom_lt hn hstr hwb hbs hGb g (show x.val < n from hwin _ hx)]
    exact hinv g.1 g.2 ⟨x.val, hw.lt _ hx⟩ hx
  · -- transitivity on the window
    intro x hx y hy
    change x.val ∈ (WinData.ofPoints (n + k) w.1).1 at hx
    change y.val ∈ (WinData.ofPoints (n + k) w.1).1 at hy
    simp only [WinData.ofPoints_fst] at hx hy
    obtain ⟨g, hg, hgxy⟩ := htr ⟨x.val, hw.lt _ hx⟩ hx ⟨y.val, hw.lt _ hy⟩ hy
    refine ⟨rebaseHom hn hstr hwb hbs hGb ⟨g, hg⟩, by rw [hden]; exact ⟨_, rfl⟩, ?_⟩
    apply Fin.ext
    rw [rebaseHom_lt hn hstr hwb hbs hGb ⟨g, hg⟩ (show x.val < n from hwin _ hx)]
    exact congrArg Fin.val hgxy
  · -- the isomorphism
    obtain ⟨θ, hθ, -, -⟩ := rebase_iso hn hstr hwb hbs hGb hfaith hden
    exact ⟨θ, hθ⟩

end M2aSpec

section M2aWf

variable {D : Ty} {S : Signature} {rec : Ty × Ty} {var₁ var₂ : Ty → Type} {r : Bool}
  {Γ : WfCtx var₁ var₂}

theorem wf_m2aIdxProg {n₁ N₁ : var₁ .nat} {n₂ N₂ : var₂ .nat} {b₁ : var₁ (.array .nat)}
    {b₂ : var₂ (.array .nat)} (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (hN : ⟨.nat, N₁, N₂⟩ ∈ Γ)
    (hb : ⟨.array .nat, b₁, b₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (m2aIdxProg n₁ N₁ b₁) (m2aIdxProg n₂ N₂ b₂) := by
  unfold m2aIdxProg mapList
  prog_wf

theorem wf_m2aProg {n₁ N₁ : var₁ .nat} {n₂ N₂ : var₂ .nat} {g₁ : var₁ Ty.gens}
    {g₂ : var₂ Ty.gens} {w₁ : var₁ Ty.win} {w₂ : var₂ Ty.win}
    {L₁ : var₁ (.array (.list .nat))} {L₂ : var₂ (.array (.list .nat))}
    {bs₁ : var₁ (.list (.list .nat))} {bs₂ : var₂ (.list (.list .nat))}
    (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (hN : ⟨.nat, N₁, N₂⟩ ∈ Γ) (hg : ⟨Ty.gens, g₁, g₂⟩ ∈ Γ)
    (hw : ⟨Ty.win, w₁, w₂⟩ ∈ Γ) (hL : ⟨.array (.list .nat), L₁, L₂⟩ ∈ Γ)
    (hbs : ⟨.list (.list .nat), bs₁, bs₂⟩ ∈ Γ) :
    Prog.Wf (rec := rec) r Γ (m2aProg (D := D) n₁ N₁ g₁ w₁ L₁ bs₁)
      (m2aProg (D := D) n₂ N₂ g₂ w₂ L₂ bs₂) := by
  unfold m2aProg
  refine .bind (wf_rebaseProg hn hN hg hbs) fun _ _ => ?_
  refine .bind (by unfold blockIdxProg mapList; prog_wf) fun _ _ => ?_
  refine .bind (wf_m2aIdxProg (by simp [hn]) (by simp [hN]) (List.Mem.head _)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp [hbs]) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp [hw]) .nil)) fun _ _ => ?_
  refine .bind (wf_mapLabelsProg (by simp [hL]) (List.Mem.head _)
    fun Γ' hΓ x₁ x₂ hx => wf_blockLabProg (hΓ (by simp)) (hΓ (by simp)) hx) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp [hn]) (.cons (by simp) .nil))) fun _ _ => ?_
  refine .bind (wf_mkWindow (List.Mem.head _) (by simp)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) (.cons (by simp) .nil))) fun _ _ => ?_
  exact .prim _ (.cons (by simp) (.cons (List.Mem.head _) .nil))

end M2aWf


/-! ### Label lengths (stage 14j-6a) -/

section LabLen

/-- **M0's labels** are singletons. -/
theorem labLen_labM0D (n : ℕ) (bidx : Array ℕ) : labLen (labM0D n bidx) ≤ 1 :=
  labLen_le_of_getD fun i hi => by
    have hi' : i < n := by simpa [labM0D] using hi
    rw [getD_labM0D hi']
    rfl

/-- **M1's labels**: the positions in `O` of the label's points, for `O` without repetitions
in the base. -/
theorem labLen_labM1D_le {n : ℕ} {O : List ℕ} (hO : O.Nodup) (hOn : ∀ p ∈ O, n ≤ p)
    (L : LabelData) (mk : Array Bool) : labLen (labM1D n O L mk) ≤ labLen L := by
  refine labLen_le_of_getD fun i hi => ?_
  have hi' : i < n := by simpa [labM1D] using hi
  by_cases hm : getB mk i = true
  · rw [getD_labM1D hi' hm]
    refine le_trans ?_ (length_getD_le_labLen L i)
    have hnd := (List.nodup_range (n := O.length)).filter
      (fun t => decide (O.getD t 0 - n ∈ L.getD i []))
    rw [← List.toFinset_card_of_nodup hnd]
    refine le_trans (Finset.card_le_card_of_injOn (fun t => O.getD t 0 - n) ?_ ?_)
      (List.toFinset_card_le (L.getD i []))
    · intro t ht
      simp only [Finset.mem_coe, List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at ht ⊢
      exact ht.2
    · intro t ht t' ht' he
      simp only [Finset.mem_coe, List.mem_toFinset, List.mem_filter, List.mem_range,
        decide_eq_true_eq] at ht ht'
      simp only at he
      rw [List.getD_eq_getElem _ _ ht.1, List.getD_eq_getElem _ _ ht'.1] at he
      have h1 := hOn _ (List.getElem_mem ht.1)
      have h2 := hOn _ (List.getElem_mem ht'.1)
      exact (hO.getElem_inj_iff).1 (by omega)
  · simp [labM1D, Array.getD_eq_getD_getElem?, hi', hm]

/-- **M2a's labels**: block labels. -/
theorem labLen_labM2aD_le {w : List ℕ} (hw : w.Nodup) (n N : ℕ) (bs : List (List ℕ))
    (L : LabelData) : labLen (labM2aD n N bs L w) ≤ labLen L :=
  labLen_mapLabels_short hw fun l => length_blockLab_le _ _ l

end LabLen

end GraphIso.Main
