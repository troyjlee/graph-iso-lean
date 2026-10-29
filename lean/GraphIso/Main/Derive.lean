module

public import GraphIso.Main.Free
public import GraphIso.Main.Reduce
public import GraphIso.Main.CJohnOps
public import GraphIso.Main.DeriveModel

/-!
# Derived hints as a program

Stage 14j-1, item 4 at the program level (`PLAN-14.md` §14.1). A reduced group `K ≤ G` of a
hinted instance `(G, w, L)` (the group after an alignment or a leaf stabilizer) and a `K`-orbit
`O` of the window give the child of `O`. The program finds the case on data.

* `DSetting`: the parent hint, `K` and the orbit `O`. `ChildOK`: a hinted child (valid group
  data, `HintValid`, the window invariant and the group transitive on it, faithful on the string
  positions, isomorphic to `K` with the same action on them). `DOutcome`: the outcomes, as
  properties of the output `(tag, ((P, (R, reps)), (G', (w', L'))))`, the reduction (`reps`
  cover `P` by cosets of `R`, tags 3 and 5) and the child. The child window is always `O`
  (`w'.1 = O`), so it has at most the parent's `|w|` points (`DSetting.len_le`).
* `deriveFreeProg` (no structure, or a colored partition, which the program does not read):
  no hint when the labels are constant on `O` (tag 0, `2|O| ≤ |w|`); otherwise M1 (`m1Prog`) on
  the first base orbit with non-constant labels, and its child when it has at most `3m/4` points
  (tag 1); otherwise the maximal blocks of the child's base (`baseBlocksProg`) and, if they are
  proper, block labels (M2a, tag 2, when some label is not equidistributed) or the stabilizer of
  the first block (M2b, tag 3, a cover by at most `m` cosets); otherwise tag 6 (`stuck`).
* `deriveCJProg` (a coloured Johnson structure, `CJData`): no hint; M1 and the block step on the
  labels outside `V₀` when those are not constant on `O`; otherwise the Johnson union labels
  re-based onto the cells (tag 4), or the Johnson fallback (tag 5: in the group re-based onto
  the cells, the pointwise stabilizer of the positions of the `u` cells of the union at a point
  of `O`, which fixes each union cell as a set; at most `u!` cosets, with `u ≤ |L u₀| · s`
  (`jfallback_cells_le`); its orbits in `O` of at most `|O|/2` points).
* `deriveProg`: the dispatch on the structure tag (`2`: a coloured Johnson structure).
* Specs (`RunsWithin.deriveFreeProg`, `RunsWithin.deriveCJProg`, `RunsWithin.deriveProg_free`,
  `RunsWithin.deriveProg_cj`): the run, an explicit cost (backend charges as specific-input
  hypotheses `M1Charges`, `BlkCharges` and the re-basing charge `Bgen₄`, and `BackendBounds`
  for the fallback, at the degree of the group re-based onto the cells), and the outcome.
* **Label lengths** (stage 14j-6a, `PLAN-14.md` §14.10): `DOutcome`'s hinted children have
  labels no longer than `L` (tags 1–3: M1's labels `labLen_labM1D_le`, block labels
  `labLen_labM2aD_le`, the block's labels `labLen_m2bLabels_le`; `m1ContProg` and `blocksProg`
  take the comparison of their input labels with `L` as a premise), or, for tag 4, at most `s`
  times longer (`labLen_labJUD_le`), where `s` is the Johnson parameter of `nc` cells with
  `C(nc, s) ≤ m` (`dv_cj_choose_le`), `2 ≤ s` and `2s ≤ nc`.
* Progress: `derivePart_ne_stuck` (a preserved colored `t`-partition with `4t ≤ 3m`: its blocks
  cut a large base orbit into a nontrivial block system, so the M1 child's base action is not
  primitive, `dv_not_prim`) and `deriveCJ_ne_stuck` (colour classes outside `V₀` of at most
  `m/2` points, `m ≥ 5`) exclude `stuck`.
* Well-formedness: `wf_deriveProg` and the lemmas of the pieces.
-/

@[expose] public section

namespace GraphIso.Main

open Equiv Cost GraphIso GraphIso.Toolkit GraphIso.Recursion GraphIso.Programs Pointwise
  GraphIso.SplitJohnson GraphIso.Solver

/-! ### Constancy and the bound `4k ≤ 3m` on data -/

section Data

/-- The labels are not constant on the points `O`. -/
def ncBD (n N : ℕ) (L : LabelData) (O : List ℕ) : Bool := ncD n (N - n) L O (basePts n N)

/-- `4 k ≤ 3 m`, on data. -/
def leQD (k m : ℕ) : Bool := !decide (m + m + m < k + k + k + k)

theorem leQD_iff {k m : ℕ} : leQD k m = true ↔ 4 * k ≤ 3 * m := by
  simp only [leQD, Bool.not_eq_true', decide_eq_false_iff_not, not_lt]
  omega

theorem dv_setOf_interO (n N : ℕ) (l : List ℕ) :
    SoJProg.setOf (N - n) (interO n (basePts n N) l) = SoJProg.setOf (N - n) l := by
  ext x
  have := x.2
  simp only [SoJProg.mem_setOf, mem_interO, mem_basePts]
  exact ⟨fun h => h.1, fun h => ⟨h, by omega, by omega⟩⟩

theorem dv_ncBD_iff {n N : ℕ} {L : LabelData} {O : List ℕ} :
    ncBD n N L O = true ↔ ∃ i ∈ O, ∃ j ∈ O,
      SoJProg.setOf (N - n) (L.getD i []) ≠ SoJProg.setOf (N - n) (L.getD j []) := by
  simp only [ncBD, ncD, List.any_eq_true, Bool.not_eq_true', ← Bool.not_eq_true,
    SoJTree.setEqD_iff, dv_setOf_interO]

end Data

/-! ### The setting and the outcomes -/

section Setting

variable {D : Ty} {DV : ℕ → GensData → D.denote → Prop}

/-- **The setting of a derived hint.** The parent: valid hint data `L` for `G = ⟨gsG⟩` on the
window `w` at degree `N` (string positions `[0, n)`), with `G` transitive on `w` and faithful
on the string positions. The reduced group `K = ⟨gs⟩ ≤ G` (valid, backend data `d`), and a
`K`-orbit `O ⊆ w` of the window, as a duplicate-free nonempty list. -/
structure DSetting (DV : ℕ → GensData → D.denote → Prop) (n N : ℕ) (gsG : GensData)
    (w : WinData) (L : LabelData) (gs : GensData) (d : D.denote) (O : List ℕ) : Prop where
  hint : HintValid n N gsG w L
  gvalid : GensData.AllValid N gsG
  win : w.Valid N
  inv : IsInvariant (GensData.denote N gsG) (w.denote N)
  trans : IsTransOn (GensData.denote N gsG) (w.denote N)
  faithful : ∀ g ∈ GensData.denote N gsG, (∀ j : Fin N, j.val < n → g j = j) → g = 1
  kvalid : GroupValid DV N gs d
  le : GensData.denote N gs ≤ GensData.denote N gsG
  nodup : O.Nodup
  sub : ∀ i ∈ O, i ∈ w.1
  orbit : ∀ i ∈ O, ∀ j, j ∈ O ↔ SameOrbit (GensData.denote N gs) i j
  ne : O ≠ []

namespace DSetting

variable {n N : ℕ} {gsG gs : GensData} {w : WinData} {L : LabelData} {d : D.denote}
  {O : List ℕ} (h : DSetting DV n N gsG w L gs d O)
include h

theorem base_inv : IsInvariant (GensData.denote N gs) (baseSet n N) :=
  fun g hg => h.hint.base_inv g (h.le hg)

theorem kfaith : ∀ g ∈ GensData.denote N gs, (∀ j : Fin N, j.val < n → g j = j) → g = 1 :=
  fun g hg => h.faithful g (h.le hg)

theorem owin : (WinData.ofPoints N O).Valid N :=
  WinData.valid_ofPoints h.nodup fun i hi => h.win.lt i (h.sub i hi)

theorem oinv : IsInvariant (GensData.denote N gs) ((WinData.ofPoints N O).denote N) := by
  intro g hg u hu
  change u.val ∈ O at hu
  change (g u).val ∈ O
  exact (h.orbit u.val hu (g u).val).2 ⟨u.2, (g u).2, g, hg, rfl⟩

theorem otrans : IsTransOn (GensData.denote N gs) ((WinData.ofPoints N O).denote N) := by
  intro u hu v hv
  change u.val ∈ O at hu
  change v.val ∈ O at hv
  obtain ⟨hu', hv', g, hg, e⟩ := (h.orbit u.val hu v.val).1 hv
  exact ⟨g, hg, e⟩

theorem lab_lt : ∀ i ∈ O, ∀ j ∈ L.getD i [], j < N - n :=
  fun i hi => h.hint.lab_lt i (h.sub i hi)

theorem lab_nodup : ∀ i ∈ O, (L.getD i []).Nodup :=
  fun i hi => h.hint.lab_nodup i (h.sub i hi)

theorem lab_len : ∀ i ∈ O, (L.getD i []).length ≤ N - n :=
  fun i hi => mf_length_le_of_nodup (h.lab_nodup i hi) (h.lab_lt i hi)

theorem win_lt : ∀ i ∈ O, i < n := fun i hi => h.hint.win_lt i (h.sub i hi)

theorem len_le : O.length ≤ w.1.length := by
  rw [← List.toFinset_card_of_nodup h.nodup, ← List.toFinset_card_of_nodup h.win.nodup]
  exact Finset.card_le_card fun i hi => List.mem_toFinset.2 (h.sub i (List.mem_toFinset.1 hi))

/-- **No hint**: if the labels are constant on `O`, then `O` has at most half of the window
(`card_le_of_const`). -/
theorem half (hc : ncBD n N L O = false) : 2 * O.length ≤ w.1.length := by
  have hh := h.hint.isHint h.gvalid h.win h.inv
  have hW : Invariant ↥(GensData.denote N gsG) (winFinset N w) := by
    intro g u hu
    rw [mem_winFinset] at hu ⊢
    exact h.inv g.1 g.2 u hu
  have hT : Transitive ↥(GensData.denote N gsG) (winFinset N w) := by
    intro u hu v hv
    rw [mem_winFinset] at hu hv
    obtain ⟨g, hg, e⟩ := h.trans u hu v hv
    exact ⟨⟨g, hg⟩, e⟩
  have hsub : winFinset N (WinData.ofPoints N O) ⊆ winFinset N w := by
    intro u hu
    rw [mem_winFinset] at hu ⊢
    exact h.sub _ hu
  have hnc : ¬ NonConst (winFinset N (WinData.ofPoints N O)) (labOf n N L) := by
    rintro ⟨u, hu, v, hv, hne⟩
    rw [mem_winFinset] at hu hv
    have : ncBD n N L O = true := by
      rw [dv_ncBD_iff]
      refine ⟨u.val, hu, v.val, hv, ?_⟩
      rwa [← mr_labOf_eq_setOf, ← mr_labOf_eq_setOf]
    rw [hc] at this
    exact Bool.false_ne_true this
  have := card_le_of_const hW hT hh hsub hnc
  rwa [show (winFinset N (WinData.ofPoints N O)).card = O.length from
      SoJProg.card_setOf h.nodup fun i hi => h.win.lt i (h.sub i hi),
    show (winFinset N w).card = w.1.length from SoJProg.card_setOf h.win.nodup h.win.lt] at this

omit h in
/-- The labels are constant on `O` when the test fails. -/
theorem const (hc : ncBD n N L O = false) : ∀ i ∈ O, ∀ j ∈ O,
    SoJProg.setOf (N - n) (L.getD i []) = SoJProg.setOf (N - n) (L.getD j []) := by
  intro i hi j hj
  by_contra hne
  have : ncBD n N L O = true := dv_ncBD_iff.2 ⟨i, hi, j, hj, hne⟩
  rw [hc] at this
  exact Bool.false_ne_true this

/-- **Restriction**: labels `L'` equivariant for `G` on `w` (as the labels of a valid hint for
`G` are) and not constant on `O` are valid hint data for `K` on `O`. -/
theorem hintOf {L' : LabelData}
    (hlt : ∀ i ∈ O, ∀ j ∈ L'.getD i [], j < N - n) (hnd : ∀ i ∈ O, (L'.getD i []).Nodup)
    (heq : ∀ π ∈ GensData.denote N gs, ∀ i ∈ O, ∀ j,
      j ∈ L'.getD (pAt π i) [] ↔ ∃ j' ∈ L'.getD i [], pAt π (n + j') - n = j)
    (hc : ncBD n N L' O = true) : HintValid n N gs (WinData.ofPoints N O) L' := by
  refine hintValid_of_forall h.hint.le h.kvalid.1 h.base_inv (by simpa using h.win_lt)
    (by simpa using hlt) (by simpa using hnd) ?_ ?_
  · intro π hπ i hi
    ext j
    simp only [List.mem_toFinset, List.mem_map]
    exact heq π hπ i (by simpa using hi) j
  · obtain ⟨i, hi, j, hj, hne⟩ := dv_ncBD_iff.1 hc
    refine ⟨i, by simpa using hi, j, by simpa using hj, fun he => hne ?_⟩
    ext x
    simp only [SoJProg.mem_setOf]
    rw [← List.mem_toFinset, he, List.mem_toFinset]

/-- The labels of the parent are equivariant for every element of `K`, on data. -/
theorem lab_equivar : ∀ π ∈ GensData.denote N gs, ∀ i ∈ O, ∀ j,
    j ∈ L.getD (pAt π i) [] ↔ ∃ j' ∈ L.getD i [], pAt π (n + j') - n = j := by
  intro π hπ i hi j
  have hiw := h.sub i hi
  have hiN := h.win.lt i hiw
  rw [pAt_of_lt _ hiN, mf_lab_mem_iff h.hint h.gvalid h.win h.inv (h.le hπ) hiw]
  constructor
  · rintro ⟨j', hj', hlt, e⟩
    exact ⟨j', hj', by rw [pAt_of_lt _ hlt, e]; omega⟩
  · rintro ⟨j', hj', e⟩
    have hlt := h.hint.lab_lt i hiw j' hj'
    have hlt' : n + j' < N := by omega
    refine ⟨j', hj', hlt', ?_⟩
    rw [pAt_of_lt _ hlt'] at e
    have hb : n ≤ (π ⟨n + j', hlt'⟩).val :=
      h.base_inv π hπ ⟨n + j', hlt'⟩ (show n ≤ n + j' by omega)
    omega

/-- **The restricted hint**: the parent's labels are valid hint data for `K` on `O` when they
are not constant on `O`. -/
theorem hintK (hc : ncBD n N L O = true) : HintValid n N gs (WinData.ofPoints N O) L :=
  h.hintOf h.lab_lt h.lab_nodup h.lab_equivar hc

end DSetting

/-- **A hinted child** at degree `N'` with string positions `[0, n)`: valid group data, valid
hint data on a valid window, the window invariant and the group transitive on it, the group
faithful on the string positions, and isomorphic to `K = ⟨gs⟩` (degree `N`) with the same
action on the string positions. -/
structure ChildOK (DV : ℕ → GensData → D.denote → Prop) (n N : ℕ) (gs : GensData)
    (N' : ℕ) (gs' : GensData) (d' : D.denote) (w' : WinData) (L' : LabelData) : Prop where
  valid : GroupValid DV N' gs' d'
  hint : HintValid n N' gs' w' L'
  win : w'.Valid N'
  inv : IsInvariant (GensData.denote N' gs') (w'.denote N')
  trans : IsTransOn (GensData.denote N' gs') (w'.denote N')
  faithful : ∀ g ∈ GensData.denote N' gs', (∀ j : Fin N', j.val < n → g j = j) → g = 1
  iso : ∃ θ : ↥(GensData.denote N gs) ≃* ↥(GensData.denote N' gs'),
    ∀ (g : ↥(GensData.denote N gs)) (j : ℕ) (hj : j < N) (hj' : j < N'), j < n →
      ((θ g : Perm (Fin N')) ⟨j, hj'⟩).val = (g.1 ⟨j, hj⟩).val

/-- The output of `deriveProg`: a tag, the reduction `(P, (R, reps))` and the child
`(G', (w', L'))`. -/
abbrev deriveTy (D : Ty) : Ty :=
  .prod .nat (.prod (.prod (Ty.group D) (.prod (Ty.group D) (.list Ty.perm)))
    (.prod (Ty.group D) (.prod Ty.win (.array (.list .nat)))))

/-- The output as a value. -/
abbrev DOut (D : Ty) : Type :=
  ℕ × ((GroupData D.denote × (GroupData D.denote × List PermData)) ×
    (GroupData D.denote × (WinData × LabelData)))

/-- **The outcomes of a derived hint**, for the setting `(n, N, w, L, K = (N, gs, d), O)` with
`m = N − n`. Each constructor fixes the shape of the output and states what the child
guarantees, in the measure of `pot_step`: no hint with `2|O| ≤ |w|`, or a hint with base
`m' ≤ 3m/4`; a reduction (tags 3 and 5) has its cover and its factor. A hinted child's labels
are no longer than `L` (tags 1–3), or at most `s` times longer for a Johnson parameter `s`
(tag 4): the facts the label invariant needs (stage 14j-6a, `PLAN-14.md` §14.10). -/
inductive DOutcome (DV : ℕ → GensData → D.denote → Prop) (n N : ℕ) (w : WinData)
    (L : LabelData) (gs : GensData) (d : D.denote) (O : List ℕ) : DOut D → Prop
  /-- No hint: the labels are constant on `O`, which has at most half of the window. -/
  | noHint
      (hc : ∀ i ∈ O, ∀ j ∈ O,
        SoJProg.setOf (N - n) (L.getD i []) = SoJProg.setOf (N - n) (L.getD j []))
      (hhalf : 2 * O.length ≤ w.1.length) :
      DOutcome DV n N w L gs d O
        (0, (((N, gs, d), ((N, gs, d), [])), ((N, gs, d), (WinData.ofPoints N O, #[]))))
  /-- M1: the labels restricted to a base orbit of at most `3m/4` points, no longer than the
  parent's (stage 14j-6a). -/
  | inter {N' : ℕ} {gs' : GensData} {d' : D.denote} {w' : WinData} {L' : LabelData}
      (hc : ChildOK DV n N gs N' gs' d' w' L') (hw : w'.1 = O)
      (hm : 4 * (N' - n) ≤ 3 * (N - n)) (hlab : labLen L' ≤ labLen L) :
      DOutcome DV n N w L gs d O
        (1, (((N', gs', d'), ((N', gs', d'), [])), ((N', gs', d'), (w', L'))))
  /-- M2a: block labels on at most `m/2` blocks, no longer than the parent's labels. -/
  | blockLab {N' : ℕ} {gs' : GensData} {d' : D.denote} {w' : WinData} {L' : LabelData}
      (hc : ChildOK DV n N gs N' gs' d' w' L') (hw : w'.1 = O)
      (hm : 2 * (N' - n) ≤ N - n) (hlab : labLen L' ≤ labLen L) :
      DOutcome DV n N w L gs d O
        (2, (((N', gs', d'), ((N', gs', d'), [])), ((N', gs', d'), (w', L'))))
  /-- M2b: `P` is the M1 child (a hinted instance with the labels `L₁`), `R` the stabilizer
  of a block, `reps` a left cover of `P` by at most `m` cosets of `R`. The child is `R`
  re-based onto the block, of at most `m/2` points, with the labels intersected with the
  block: valid hint data on every nonempty `R`-invariant part of `O` (`R` need not be
  transitive on `O`), no longer than the parent's labels. -/
  | blockStab {N₁ : ℕ} {gs₁ : GensData} {d₁ : D.denote} {w₁ : WinData} {L₁ : LabelData}
      {Rgs : GensData} {Rd : D.denote} {reps : List PermData} {N' : ℕ} {gs' : GensData}
      {d' : D.denote} {L' : LabelData}
      (hP : ChildOK DV n N gs N₁ gs₁ d₁ w₁ L₁) (hw₁ : w₁.1 = O)
      (hR : GroupValid DV N₁ Rgs Rd)
      (hRP : GensData.denote N₁ Rgs ≤ GensData.denote N₁ gs₁)
      (hreps : ∀ r ∈ reps, PermData.Valid N₁ r)
      (hcov : IsLeftCover (GensData.denote N₁ gs₁) (GensData.denote N₁ Rgs)
        (fun i : Fin reps.length => PermData.denote N₁ (reps.get i)))
      (hlen : reps.length ≤ N - n)
      (hG' : GroupValid DV N' gs' d') (hm : 2 * (N' - n) ≤ N - n)
      (hfaith : ∀ g ∈ GensData.denote N' gs', (∀ j : Fin N', j.val < n → g j = j) → g = 1)
      (hinv : IsInvariant (GensData.denote N' gs') ((WinData.ofPoints N' O).denote N'))
      (hiso : ∃ θ : ↥(GensData.denote N₁ Rgs) ≃* ↥(GensData.denote N' gs'),
        ∀ (g : ↥(GensData.denote N₁ Rgs)) (j : ℕ) (hj : j < N₁) (hj' : j < N'), j < n →
          ((θ g : Perm (Fin N')) ⟨j, hj'⟩).val = (g.1 ⟨j, hj⟩).val)
      (hhint : ∀ wO : WinData, (∀ i ∈ wO.1, i ∈ O) → wO.1 ≠ [] →
        IsInvariant (GensData.denote N₁ Rgs) (wO.denote N₁) → HintValid n N' gs' wO L')
      (hlab : labLen L' ≤ labLen L) :
      DOutcome DV n N w L gs d O
        (3, (((N₁, gs₁, d₁), ((N₁, Rgs, Rd), reps)),
          ((N', gs', d'), (WinData.ofPoints N' O, L'))))
  /-- The Johnson union, re-based onto the cells: at most `3m/4` cells. The labels are at most
  `s` times longer than the parent's, for the Johnson parameter `s` of the `m' = N' − n` cells:
  `C(m', s) ≤ m`, `2 ≤ s` and `2s ≤ m'` (stage 14j-6a). -/
  | johnUnion {N' : ℕ} {gs' : GensData} {d' : D.denote} {w' : WinData} {L' : LabelData}
      (hc : ChildOK DV n N gs N' gs' d' w' L') (hw : w'.1 = O)
      (hm : 4 * (N' - n) ≤ 3 * (N - n))
      (hlab : ∃ s, labLen L' ≤ labLen L * s ∧ (N' - n).choose s ≤ N - n ∧ 2 ≤ s ∧
        2 * s ≤ N' - n) :
      DOutcome DV n N w L gs d O
        (4, (((N', gs', d'), ((N', gs', d'), [])), ((N', gs', d'), (w', L'))))
  /-- The Johnson fallback: `P` is `K` re-based onto the cells (degree `N'`; faithful, `O`
  invariant, isomorphic to `K` with the same action on the string positions), `R` the
  pointwise stabilizer in `P` of the positions of the `u` cells of the union at a point of `O`
  (so `R` fixes each union cell as a set), `reps` a left cover of `P` by at most `u!` cosets of
  `R`. The labels are constant on `O`, so the child has no hint; every part of `O` on which
  `R` is transitive has at most `|O|/2` points. -/
  | johnFallback {N' : ℕ} {Pgs : GensData} {Pd : D.denote} {Rgs : GensData} {Rd : D.denote}
      {reps : List PermData} {u : ℕ} (hN' : n ≤ N')
      (hP : GroupValid DV N' Pgs Pd)
      (hPfaith : ∀ g ∈ GensData.denote N' Pgs, (∀ j : Fin N', j.val < n → g j = j) → g = 1)
      (hPinv : IsInvariant (GensData.denote N' Pgs) ((WinData.ofPoints N' O).denote N'))
      (hPiso : ∃ θ : ↥(GensData.denote N gs) ≃* ↥(GensData.denote N' Pgs),
        ∀ (g : ↥(GensData.denote N gs)) (j : ℕ) (hj : j < N) (hj' : j < N'), j < n →
          ((θ g : Perm (Fin N')) ⟨j, hj'⟩).val = (g.1 ⟨j, hj⟩).val)
      (hR : GroupValid DV N' Rgs Rd) (hRP : GensData.denote N' Rgs ≤ GensData.denote N' Pgs)
      (hreps : ∀ r ∈ reps, PermData.Valid N' r)
      (hcov : IsLeftCover (GensData.denote N' Pgs) (GensData.denote N' Rgs)
        (fun i : Fin reps.length => PermData.denote N' (reps.get i)))
      (hlen : reps.length ≤ u.factorial) (hu : u ≤ N - n)
      (hRinv : IsInvariant (GensData.denote N' Rgs) ((WinData.ofPoints N' O).denote N'))
      (hhalf : ∀ O' : List ℕ, O'.Nodup → (∀ v ∈ O', v ∈ O) →
        (∀ v ∈ O', ∀ v' ∈ O', SameOrbit (GensData.denote N' Rgs) v v') →
        2 * O'.length ≤ O.length) :
      DOutcome DV n N w L gs d O
        (5, (((N', Pgs, Pd), ((N', Rgs, Rd), reps)),
          ((N', Rgs, Rd), (WinData.ofPoints N' O, #[]))))
  /-- No progress: excluded by the progress lemmas (`derivePart_ne_stuck`,
  `deriveCJ_ne_stuck`). -/
  | stuck (r : DOut D) (h : r.1 = 6) : DOutcome DV n N w L gs d O r

end Setting

/-! ### Re-based groups and the group of M1 -/

section Rebased

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b}
  {DV : ℕ → GensData → D.denote → Prop}

/-- **The charges of M1** on the window `w` and the labels `L`: at most `Borb` for the orbits of
the base and `Bgen` for the re-based group. -/
def M1Charges (X : Ctx (groupSig D)) (n N : ℕ) (gs : GensData) (d : D.denote) (w : WinData)
    (L : LabelData) (Borb Bgen : ℕ) : Prop :=
  X.B.call GroupOp.orbits ((N, gs, d), baseWin n N)
      (X.O.run GroupOp.orbits ((N, gs, d), baseWin n N)) ≤ Borb ∧
    X.B.call GroupOp.generate (n + (singD (m1O X.O n N (N, gs, d) w L)).length,
        rebaseGens n N (singD (m1O X.O n N (N, gs, d) w L)) gs)
      (rebaseModel X.O n N (singD (m1O X.O n N (N, gs, d) w L)) gs) ≤ Bgen

/-- **The re-based group as the backend generates it**: its degree, validity and denotation
(the facts of `RunsWithin.rebaseProg`, without the run). -/
theorem dv_rebase_den (hO : MeetsContractOn DV rebaseOps X.O) {n N : ℕ} {w : WinData}
    {bs : List (List ℕ)} {gs : GensData} (hn : n ≤ N)
    (hbase : IsInvariant (GensData.denote N gs) (baseSet n N)) (hw : w.Valid N)
    (hbs : IsBlockList w bs) (hGb : PermutesBlocks (GensData.denote N gs) bs)
    (hgs : GensData.AllValid N gs) :
    (rebaseModel X.O n N bs gs).1 = n + bs.length ∧
      GroupValid DV (n + bs.length) (rebaseModel X.O n N bs gs).2.1
        (rebaseModel X.O n N bs gs).2.2 ∧
      GensData.denote (n + bs.length) (rebaseModel X.O n N bs gs).2.1 =
        (rebaseHom hn (isInvariant_strSet hbase) hw hbs hGb).range := by
  have hval := allValid_rebaseGens hn hbase hw hbs hGb hgs
  have hden := denote_rebaseGens hn hbase hw hbs hGb hgs
  have hpost := hO .generate (n + bs.length, rebaseGens n N bs gs) rfl hval
  rcases hm : rebaseModel X.O n N bs gs with ⟨n', hs, d⟩
  rw [rebaseModel] at hm
  rw [hm] at hpost
  exact ⟨hpost.1, hpost.2.1, hpost.2.2.trans hden⟩

/-- **The facts of a re-based group** on a window `O` of string positions: the window is valid
and invariant, transitivity passes on, the group is faithful on the string positions, and it is
isomorphic to the old one with the same action on them. -/
theorem dv_rebase_facts {N n : ℕ} {G : Subgroup (Perm (Fin N))} {wb : WinData}
    {bs : List (List ℕ)} (hn : n ≤ N) (hbase : IsInvariant G (baseSet n N)) (hwb : wb.Valid N)
    (hbs : IsBlockList wb bs) (hGb : PermutesBlocks G bs)
    (hfaith : ∀ g ∈ G, (∀ j : Fin N, j.val < n → g j = j) → g = 1) {hs : GensData}
    (hden : GensData.denote (n + bs.length) hs =
      (rebaseHom hn (isInvariant_strSet hbase) hwb hbs hGb).range)
    {O : List ℕ} (hOn : ∀ i ∈ O, i < n) (hOnd : O.Nodup)
    (hOinv : IsInvariant G ((WinData.ofPoints N O).denote N)) :
    (WinData.ofPoints (n + bs.length) O).Valid (n + bs.length) ∧
      IsInvariant (GensData.denote (n + bs.length) hs)
        ((WinData.ofPoints (n + bs.length) O).denote (n + bs.length)) ∧
      (IsTransOn G ((WinData.ofPoints N O).denote N) →
        IsTransOn (GensData.denote (n + bs.length) hs)
          ((WinData.ofPoints (n + bs.length) O).denote (n + bs.length))) ∧
      (∀ g ∈ GensData.denote (n + bs.length) hs,
        (∀ j : Fin (n + bs.length), j.val < n → g j = j) → g = 1) ∧
      ∃ θ : ↥G ≃* ↥(GensData.denote (n + bs.length) hs),
        ∀ (g : ↥G) (j : ℕ) (hj : j < N) (hj' : j < n + bs.length), j < n →
          ((θ g : Perm (Fin (n + bs.length))) ⟨j, hj'⟩).val = (g.1 ⟨j, hj⟩).val := by
  have hstr := isInvariant_strSet hbase
  refine ⟨WinData.valid_ofPoints hOnd fun i hi => by have := hOn i hi; omega, ?_, ?_, ?_, ?_⟩
  · intro π hπ x hx
    rw [hden] at hπ
    obtain ⟨g, rfl⟩ := hπ
    change x.val ∈ O at hx
    change (rebaseHom hn hstr hwb hbs hGb g x).val ∈ O
    rw [rebaseHom_lt hn hstr hwb hbs hGb g (show x.val < n from hOn _ hx)]
    exact hOinv g.1 g.2 ⟨x.val, by have := hOn _ hx; omega⟩ hx
  · intro htr x hx y hy
    change x.val ∈ O at hx
    change y.val ∈ O at hy
    obtain ⟨g, hg, hgxy⟩ := htr ⟨x.val, by have := hOn _ hx; omega⟩ hx
      ⟨y.val, by have := hOn _ hy; omega⟩ hy
    refine ⟨rebaseHom hn hstr hwb hbs hGb ⟨g, hg⟩, by rw [hden]; exact ⟨_, rfl⟩, ?_⟩
    apply Fin.ext
    rw [rebaseHom_lt hn hstr hwb hbs hGb ⟨g, hg⟩ (show x.val < n from hOn _ hx)]
    exact congrArg Fin.val hgxy
  · rw [hden]
    exact rebase_faithful hn hstr hwb hbs hGb hfaith
  · obtain ⟨θ, hθ, -, -⟩ := rebase_iso hn hstr hwb hbs hGb hfaith hden
    exact ⟨θ, fun g j _ _ hjn => hθ g j hjn⟩

/-- Transitivity on the base in the form of `baseHom`. -/
theorem dv_baseHom_trans {N n : ℕ} {G : Subgroup (Perm (Fin N))}
    (hinv : IsInvariant G (baseSet n N)) (htr : IsTransOn G (baseSet n N)) :
    ∀ γ δ : Fin (N - n), ∃ g : ↥G, baseHom G n hinv g γ = δ := by
  intro γ δ
  obtain ⟨g, hg, e⟩ := htr (basePos γ) (basePos_mem γ) (basePos δ) (basePos_mem δ)
  refine ⟨⟨g, hg⟩, ?_⟩
  apply Fin.ext
  have h := congrArg Fin.val (baseHom_apply (hG := hinv) ⟨g, hg⟩ γ)
  change n + (baseHom G n hinv ⟨g, hg⟩ γ).val = (g (basePos γ)).val at h
  rw [e] at h
  change n + _ = n + δ.val at h
  omega

/-- **The orbit M1 chooses** is an orbit of the base action: duplicate-free, nonempty, of base
positions. -/
theorem dv_m1O (hO : MeetsContractOn DV m1Ops X.O) {n N : ℕ} {gs : GensData} {d : D.denote}
    {w : WinData} {L : LabelData} (hGv : GroupValid DV N gs d) (hL : HintValid n N gs w L) :
    (m1O X.O n N (N, gs, d) w L).Nodup ∧
      (∀ x ∈ m1O X.O n N (N, gs, d) w L, n ≤ x ∧ x < N) ∧
      (∀ i ∈ m1O X.O n N (N, gs, d) w L, ∀ j,
        j ∈ m1O X.O n N (N, gs, d) w L ↔ SameOrbit (GensData.denote N gs) i j) ∧
      m1O X.O n N (N, gs, d) w L ≠ [] := by
  have hpre : GroupPre DV .orbits ((N, gs, d), baseWin n N) :=
    ⟨hGv, baseWin_valid n N, by rw [baseWin_denote]; exact hL.base_inv⟩
  have hos : IsOrbitPartition (GensData.denote N gs) (baseWin n N)
      (X.O.run GroupOp.orbits ((N, gs, d), baseWin n N)) := hO .orbits _ (Or.inl rfl) hpre
  obtain ⟨hOmem, -⟩ := mf_pickD_spec (mf_exists_ncD hL hos.1)
  obtain ⟨hnd, hb, -, horb⟩ := mf_orbit hos hOmem
  exact ⟨hnd, hb, horb, (hos.2 _ hOmem).1⟩

/-- **The base action of the M1 child is transitive**: its base is the chosen orbit. -/
theorem dv_m1_trans (hO : MeetsContractOn DV m1Ops X.O) {n N : ℕ} {gs : GensData}
    {d : D.denote} {w : WinData} {L : LabelData} (hGv : GroupValid DV N gs d)
    (hL : HintValid n N gs w L) :
    IsTransOn (GensData.denote (m1Model X.O n N (N, gs, d) w L).1.1
        (m1Model X.O n N (N, gs, d) w L).1.2.1)
      (baseSet n (m1Model X.O n N (N, gs, d) w L).1.1) := by
  obtain ⟨hnd, hb, horb, -⟩ := dv_m1O hO hGv hL
  set Ob := m1O X.O n N (N, gs, d) w L with hObdef
  have hwO : (WinData.ofPoints N Ob).Valid N :=
    WinData.valid_ofPoints hnd fun x hx => (hb x hx).2
  have hGb : PermutesBlocks (GensData.denote N gs) (singD Ob) := mf_sing_permutes horb
  obtain ⟨hdeg, -, hden⟩ := dv_rebase_den (X := X) (DV := DV)
    (fun op x hop hx => hO op x (Or.inr hop) hx) hL.le hL.base_inv hwO mf_sing_isBlockList hGb
    hGv.1
  have hm : (m1Model X.O n N (N, gs, d) w L).1 = rebaseModel X.O n N (singD Ob) gs := rfl
  rw [hm, hdeg, hden]
  have hk : (singD Ob).length = Ob.length := length_singD Ob
  intro u hu v hv
  change n ≤ u.val at hu
  change n ≤ v.val at hv
  have hu' : u.val - n < Ob.length := by have := u.2; omega
  have hv' : v.val - n < Ob.length := by have := v.2; omega
  have hOt := hb _ (List.getElem_mem hu')
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

end Rebased

/-! ### The maximal blocks of a transitive base -/

section MaxBlocks

/-- The maximal blocks of the base `[n, N)` of the group `⟨gs⟩`. -/
abbrev mbD (n N : ℕ) (gs : GensData) : List (List ℕ) := Luks.maxBlocks N gs (basePts n N)

/-- The block test: at least two base points, and maximal blocks of at least two points. -/
def blkOKD (k : ℕ) (bs : List (List ℕ)) : Bool :=
  !decide (k < 2) && !decide ((bs.headD []).length < 2)

theorem blkOKD_iff {k : ℕ} {bs : List (List ℕ)} :
    blkOKD k bs = true ↔ 2 ≤ k ∧ 2 ≤ (bs.headD []).length := by
  simp only [blkOKD, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, not_lt]

/-- Some label of the points `pts` is not equidistributed over the blocks `bs` of `[n, N)`. -/
def neqD (n N : ℕ) (bs : List (List ℕ)) (L : LabelData) (pts : List ℕ) : Bool :=
  pts.any fun u => !equidistB bs.length (m2aIdx n N bs) (L.getD u [])

theorem dv_maxBlocks_len {N : ℕ} {gs : GensData} {pts : List ℕ} :
    ∀ b ∈ Luks.maxBlocks N gs pts, b.length ≤ pts.length := by
  intro b hb
  unfold Luks.maxBlocks at hb
  split at hb
  · simp at hb
  · obtain ⟨l, -, rfl⟩ := Luks.mem_blocksOf.1 hb
    exact List.length_filter_le _ _

theorem dv_headD_len {N : ℕ} {gs : GensData} {pts : List ℕ} :
    ((Luks.maxBlocks N gs pts).headD []).length ≤ pts.length := by
  cases h : Luks.maxBlocks N gs pts with
  | nil => simp
  | cons b rest =>
    exact dv_maxBlocks_len b (by rw [h]; exact List.mem_cons_self)

/-- **The maximal blocks of a transitive base action** on at least two points: a block list of
the whole base, permuted by the group. -/
theorem dv_maxBlocks_list {N n : ℕ} {gs : GensData} (hgs : GensData.AllValid N gs)
    (hinv : IsInvariant (GensData.denote N gs) (baseSet n N))
    (htr : IsTransOn (GensData.denote N gs) (baseSet n N)) (h2 : 2 ≤ N - n) :
    IsBlockList (WinData.ofPoints N (basePts n N)) (mbD n N gs) ∧
      PermutesBlocks (GensData.denote N gs) (mbD n N gs) := by
  have hw : (WinData.ofPoints N (basePts n N)).Valid N :=
    WinData.valid_ofPoints (basePts_nodup _ _) fun i hi => (mem_basePts.1 hi).2
  have hinvw : IsInvariant (GensData.denote N gs)
      ((WinData.ofPoints N (basePts n N)).denote N) := by
    rw [denote_basePts]; exact hinv
  have hpts : (WinData.ofPoints N (basePts n N)).1 = n :: basePts (n + 1) N :=
    basePts_cons (by omega)
  have hrest : basePts (n + 1) N ≠ [] := by
    intro h
    have := congrArg List.length h
    rw [length_basePts] at this
    simp at this
    omega
  have htr' : ∀ j, j ∈ (WinData.ofPoints N (basePts n N)).1 ↔
      SameOrbit (GensData.denote N gs) n j := by
    intro j
    constructor
    · intro hj
      rw [WinData.ofPoints_fst, mem_basePts] at hj
      obtain ⟨g, hg, e⟩ := htr ⟨n, by omega⟩ (show n ≤ n from le_rfl) ⟨j, hj.2⟩ hj.1
      exact ⟨by omega, hj.2, g, hg, e⟩
    · intro h
      exact h.mem_of_invariant hinvw (by rw [hpts]; exact List.mem_cons_self)
  obtain ⟨hbs, hG, -, -, -⟩ := Luks.maxBlocks_spec hw hgs hinvw hpts hrest htr'
  exact ⟨hbs, hG⟩

/-- **The maximal blocks of a transitive base action** with at least two points and blocks of
at least two points: a block list of the whole base, permuted by the group, forming a block
system with at least two blocks of at least two points. -/
theorem dv_blocks_facts {N n : ℕ} {gs : GensData} (hgs : GensData.AllValid N gs)
    (hinv : IsInvariant (GensData.denote N gs) (baseSet n N))
    (htr : IsTransOn (GensData.denote N gs) (baseSet n N)) (h2 : 2 ≤ N - n)
    (hh : 2 ≤ ((mbD n N gs).headD []).length) :
    IsBlockList (WinData.ofPoints N (basePts n N)) (mbD n N gs) ∧
      PermutesBlocks (GensData.denote N gs) (mbD n N gs) ∧
      IsBlockSys (baseHom (GensData.denote N gs) n hinv) (blockFam n N (mbD n N gs)) ∧
      2 ≤ (blockFam n N (mbD n N gs)).card ∧ (∀ b ∈ mbD n N gs, 2 ≤ b.length) := by
  have htrB := dv_baseHom_trans hinv htr
  obtain ⟨-, hequal, -, hsys⟩ := baseBlocks_spec hgs hinv (by omega) htrB
  obtain ⟨hΨ, hc, -⟩ := hsys hh
  obtain ⟨hbs, hG⟩ := dv_maxBlocks_list hgs hinv htr h2
  exact ⟨hbs, hG, hΨ, hc, fun b hb => (hequal b hb).symm ▸ hh⟩

/-- **A primitive base action**: when the maximal blocks are single points. -/
theorem dv_blocks_prim {N n : ℕ} {gs : GensData} (hgs : GensData.AllValid N gs)
    (hinv : IsInvariant (GensData.denote N gs) (baseSet n N))
    (htr : IsTransOn (GensData.denote N gs) (baseSet n N)) (h2 : 2 ≤ N - n)
    (hh : ((mbD n N gs).headD []).length < 2) :
    MulAction.IsPreprimitive (baseHom (GensData.denote N gs) n hinv).range (Fin (N - n)) := by
  have htrB := dv_baseHom_trans hinv htr
  obtain ⟨hlen, -, hprim, -⟩ := baseBlocks_spec hgs hinv (by omega) htrB
  obtain ⟨hbs, -⟩ := dv_maxBlocks_list hgs hinv htr h2
  apply hprim
  simp only [mbD] at hh hbs
  have hne : Luks.maxBlocks N gs (basePts n N) ≠ [] := by
    intro h
    rw [h] at hlen
    simp at hlen
  obtain ⟨b, rest, hb⟩ := List.exists_cons_of_ne_nil hne
  have hbm : b ∈ Luks.maxBlocks N gs (basePts n N) := by rw [hb]; exact List.mem_cons_self
  have := List.length_pos_of_ne_nil (hbs.2 b hbm)
  rw [hb] at hh ⊢
  simp only [List.headD_cons] at hh ⊢
  omega

end MaxBlocks

/-! ### Common pieces: programs -/

section CommonProgs

variable {D : Ty} {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- The output `(tag, ((P, (R, reps)), (G', (w', L'))))`. -/
def outProg (tag : ℕ) (P R : var (Ty.group D)) (reps : var (.list Ty.perm))
    (G' : var (Ty.group D)) (w' : var Ty.win) (L' : var (.array (.list .nat))) :
    Prog S rec var (deriveTy D) :=
  .bind (.op0 (.natLit tag)) fun tg =>
  .bind (.op2 .pair R reps) fun rr => .bind (.op2 .pair P rr) fun prr =>
  .bind (.op2 .pair w' L') fun wl => .bind (.op2 .pair G' wl) fun gwl =>
  .bind (.op2 .pair prr gwl) fun p => .op2 .pair tg p

/-- `leQD` as a program. -/
def leQProg (k m : var .nat) : Prog S rec var .bool :=
  .bind (.op2 .add k k) fun k2 => .bind (.op2 .add k2 k) fun k3 =>
  .bind (.op2 .add k3 k) fun k4 => .bind (.op2 .add m m) fun m2 =>
  .bind (.op2 .add m2 m) fun m3 => .bind (.op2 .natLt m3 k4) fun b => .op1 .not b

/-- `ncBD` as a program. -/
def ncBProg (n N : var .nat) (L : var (.array (.list .nat))) (O : var (.list .nat)) :
    Prog S rec var .bool :=
  .bind (baseWinProg n N) fun bw => .bind (.op1 .fst bw) fun bp =>
  .bind (.op2 .sub N n) fun m => ncProg n m L O bp

/-- The output without a hint. -/
def noHintProg (K : var (Ty.group D)) (w : var Ty.win) : Prog S rec var (deriveTy D) :=
  .bind (.op0 .nil) fun nil => .bind (.op0 .nil) fun e0 => .bind (.op1 .arrayOfList e0) fun e =>
  outProg 0 K K nil K w e

/-- `blkOKD` as a program. -/
def blkOKProg (k : var .nat) (bs : var (.list (.list .nat))) : Prog S rec var .bool :=
  .bind (.caseList bs (.op0 (.natLit 0)) fun b _ => .op1 .length b) fun hl =>
  .bind (.op0 (.natLit 2)) fun two =>
  .bind (.op2 .natLt k two) fun b1 => .bind (.op1 .not b1) fun c1 =>
  .bind (.op2 .natLt hl two) fun b2 => .bind (.op1 .not b2) fun c2 =>
  .op2 .and c1 c2

/-- `neqD` as a program. -/
def neqProg (n N : var .nat) (bs : var (.list (.list .nat))) (L : var (.array (.list .nat)))
    (pts : var (.list .nat)) : Prog S rec var .bool :=
  .bind (blockIdxProg N bs) fun bi => .bind (m2aIdxProg n N bi) fun bidx =>
  .bind (.op1 .length bs) fun k =>
  anyList pts fun u => .bind (.op2 .arrayGet L u) fun li =>
    .bind (Toolkit.equidistProg k bidx li) fun e => .op1 .not e

/-- The output of M2a. -/
def m2aOutProg (r2 : var (.prod (Ty.group D) (.prod Ty.win (.array (.list .nat))))) :
    Prog S rec var (deriveTy D) :=
  .bind (.op1 .fst r2) fun G2 => .bind (.op1 .snd r2) fun wl => .bind (.op1 .fst wl) fun w2 =>
  .bind (.op1 .snd wl) fun L2 => .bind (.op0 .nil) fun nil => outProg 2 G2 G2 nil G2 w2 L2

/-- The output of M2b: the M1 child `G1`, the block stabilizer with its representatives, and
its re-basing with the window `pts`. -/
def m2bOutProg (G1 : var (Ty.group D)) (pts : var (.list .nat))
    (r3 : var (.prod (.prod (Ty.group D) (.list Ty.perm))
      (.prod (Ty.group D) (.array (.list .nat))))) :
    Prog S rec var (deriveTy D) :=
  .bind (.op1 .fst r3) fun Hr => .bind (.op1 .fst Hr) fun H => .bind (.op1 .snd Hr) fun reps =>
  .bind (.op1 .snd r3) fun hl => .bind (.op1 .fst hl) fun H' => .bind (.op1 .snd hl) fun L' =>
  .bind (.op1 .fst H') fun N' => .bind (mkWindow N' pts) fun w' => outProg 3 G1 H reps H' w' L'

end CommonProgs

section BlockProgs

variable {D : Ty} {rec : Ty × Ty} {var : Ty → Type}

/-- **The block step** after M1, on the child `(G1, w1, L1)`: the maximal blocks of its base;
if they are proper (at least two base points, blocks of at least two points), block labels
(M2a) when some label is not equidistributed, otherwise the stabilizer of the first block
(M2b); if not, tag `6`. -/
def blocksProg (n : var .nat) (G1 : var (Ty.group D)) (w1 : var Ty.win)
    (L1 : var (.array (.list .nat))) : Prog (groupSig D) rec var (deriveTy D) :=
  .bind (.op1 .fst G1) fun N1 => .bind (.op1 .snd G1) fun gd => .bind (.op1 .fst gd) fun gs1 =>
  .bind (.op1 .fst w1) fun pts => .bind (.op2 .sub N1 n) fun k =>
  .bind (baseBlocksProg n G1) fun bs =>
  .bind (blkOKProg k bs) fun ok =>
  .bind (.op0 .nil) fun nil =>
  .ite ok
    (.bind (neqProg n N1 bs L1 pts) fun ne =>
      .ite ne (.bind (m2aProg n N1 gs1 w1 L1 bs) fun r2 => m2aOutProg r2)
        (.bind (.op0 (.natLit 0)) fun z =>
          .bind (m2bProg n N1 gs1 bs z L1 pts) fun r3 => m2bOutProg G1 pts r3))
    (outProg 6 G1 G1 nil G1 w1 L1)

/-- **M1 and what follows**: M1 on the window `w`; its child (tag `1`) when the new base has at
most `3m/4` points, otherwise the block step. -/
def m1ContProg (n N : var .nat) (K : var (Ty.group D)) (w : var Ty.win)
    (L : var (.array (.list .nat))) : Prog (groupSig D) rec var (deriveTy D) :=
  .bind (m1Prog n N K w L) fun r =>
  .bind (.op1 .fst r) fun G1 => .bind (.op1 .fst G1) fun N1 =>
  .bind (.op2 .sub N1 n) fun k => .bind (.op2 .sub N n) fun m =>
  .bind (leQProg k m) fun b =>
  .bind (.op1 .snd r) fun wl => .bind (.op1 .fst wl) fun w1 => .bind (.op1 .snd wl) fun L1 =>
  .bind (.op0 .nil) fun nil =>
  .ite b (outProg 1 G1 G1 nil G1 w1 L1) (blocksProg n G1 w1 L1)

/-- **No structure, or a colored partition**: no hint when the labels are constant on `O`,
otherwise M1 and the block step. -/
def deriveFreeProg (n N : var .nat) (K : var (Ty.group D)) (O : var (.list .nat))
    (L : var (.array (.list .nat))) : Prog (groupSig D) rec var (deriveTy D) :=
  .bind (ncBProg n N L O) fun c => .bind (mkWindow N O) fun w =>
  .ite c (m1ContProg n N K w L) (noHintProg K w)

end BlockProgs

/-! ### Common pieces: models and specs -/

section CommonSpecs

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b}
  {DV : ℕ → GensData → D.denote → Prop}

/-- The output as a value. -/
def outD (tag : ℕ) (P R : GroupData D.denote) (reps : List PermData) (G' : GroupData D.denote)
    (w' : WinData) (L' : LabelData) : DOut D :=
  (tag, ((P, (R, reps)), (G', (w', L'))))

/-- The output without a hint. -/
def noHintD (K : GroupData D.denote) (w : WinData) : DOut D := outD 0 K K [] K w #[]

/-- The cost of `ncBProg` on `p` points with labels of at most `Lb` entries. -/
def ncBCost (n N p Lb : ℕ) : ℕ := baseWinCost n N + 2 + ncCost p (N - n) Lb

theorem RunsWithin.outProg (tag : ℕ) (P R : GroupData D.denote) (reps : List PermData)
    (G' : GroupData D.denote) (w' : WinData) (L' : LabelData) :
    RunsWithin X body (Main.outProg tag P R reps G' w' L') (outD tag P R reps G' w' L') 7 := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim _ _
  case hc => simp [Prim.cost]

theorem RunsWithin.leQProg (k m : ℕ) :
    RunsWithin X body (Main.leQProg k m) (leQD k m) 7 := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim _ _
  case hc => simp [Prim.cost]

theorem RunsWithin.ncBProg (n N : ℕ) (L : LabelData) (O : List ℕ) {Lb : ℕ}
    (hL : ∀ i ∈ O, (L.getD i []).length ≤ Lb) :
    RunsWithin X body (Main.ncBProg n N L O) (ncBD n N L O) (ncBCost n N O.length Lb) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.baseWinProg n N)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    simp only [Prim.eval]
    exact RunsWithin.ncProg n (N - n) L (by simp [baseWin, length_basePts]) hL
  case hc => simp [Prim.cost, ncBCost]; omega

theorem RunsWithin.noHintProg (K : GroupData D.denote) (w : WinData) :
    RunsWithin X body (Main.noHintProg K w) (noHintD K w) 10 := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.outProg 0 K K [] K w _
  case hc => simp [Prim.cost, Prim.eval]

/-- **M1 as a hinted child**: `RunsWithin.m1Prog`, with the child's facts as `ChildOK`. -/
theorem dv_m1 (hO : MeetsContractOn DV m1Ops X.O)
    (hPre : ∀ op x, m1Ops op → GroupPre DV op x → X.Pre op x) {n N : ℕ} {gs : GensData}
    {d : D.denote} {w : WinData} {L : LabelData} (hGv : GroupValid DV N gs d) (hw : w.Valid N)
    (hinv : IsInvariant (GensData.denote N gs) (w.denote N))
    (hfaith : ∀ g ∈ GensData.denote N gs, (∀ j : Fin N, j.val < n → g j = j) → g = 1)
    (htr : IsTransOn (GensData.denote N gs) (w.denote N)) (hL : HintValid n N gs w L)
    {Borb Bgen : ℕ} (hB : M1Charges X n N gs d w L Borb Bgen) :
    RunsWithin X body (Main.m1Prog n N (N, gs, d) w L) (m1Model X.O n N (N, gs, d) w L)
        (m1Cost n N w.1.length gs.length Borb Bgen) ∧
      ChildOK DV n N gs (m1Model X.O n N (N, gs, d) w L).1.1
        (m1Model X.O n N (N, gs, d) w L).1.2.1 (m1Model X.O n N (N, gs, d) w L).1.2.2
        (m1Model X.O n N (N, gs, d) w L).2.1 (m1Model X.O n N (N, gs, d) w L).2.2 ∧
      (m1Model X.O n N (N, gs, d) w L).1.1 = n + (m1O X.O n N (N, gs, d) w L).length ∧
      (m1O X.O n N (N, gs, d) w L).length ≤ N - n := by
  obtain ⟨hrun, hdeg, hval, hhint, hfa, hwv, hinv', htr', hk, -, θ, hθ⟩ :=
    RunsWithin.m1Prog (body := body) hO hPre hGv hw hinv hfaith htr hL hB.1 hB.2
  refine ⟨hrun, ?_, by rw [hdeg, length_singD], by rw [← length_singD]; exact hk⟩
  rw [hdeg]
  exact ⟨hval, hhint, hwv, hinv', htr', hfa, θ, fun g j _ _ hjn => hθ g j hjn⟩

end CommonSpecs

/-! ### The block step: models, costs, charges -/

section BlockModels

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b}
  {DV : ℕ → GensData → D.denote → Prop}

/-- The output of M2a. -/
def m2aOutD (r2 : GroupData D.denote × (WinData × LabelData)) : DOut D :=
  outD 2 r2.1 r2.1 [] r2.1 r2.2.1 r2.2.2

/-- The output of M2b. -/
def m2bOutD (G1 : GroupData D.denote) (pts : List ℕ)
    (r3 : (GroupData D.denote × List PermData) × (GroupData D.denote × LabelData)) : DOut D :=
  outD 3 G1 r3.1.1 r3.1.2 r3.2.1 (WinData.ofPoints r3.2.1.1 pts) r3.2.2

/-- The value of `blocksProg`. -/
def blocksD (Or : Oracle (groupSig D)) (n : ℕ) (G1 : GroupData D.denote) (w1 : WinData)
    (L1 : LabelData) : DOut D :=
  cond (blkOKD (G1.1 - n) (mbD n G1.1 G1.2.1))
    (cond (neqD n G1.1 (mbD n G1.1 G1.2.1) L1 w1.1)
      (m2aOutD (m2aModel Or n G1.1 G1.2.1 w1 L1 (mbD n G1.1 G1.2.1)))
      (m2bOutD G1 w1.1 (m2bModel Or n G1.1 G1.2.1 (mbD n G1.1 G1.2.1) 0 L1 w1.1)))
    (outD 6 G1 G1 [] G1 w1 L1)

/-- The value of `m1ContProg`. -/
def m1ContD (Or : Oracle (groupSig D)) (n N : ℕ)
    (r : GroupData D.denote × (WinData × LabelData)) : DOut D :=
  cond (leQD (r.1.1 - n) (N - n)) (outD 1 r.1 r.1 [] r.1 r.2.1 r.2.2)
    (blocksD Or n r.1 r.2.1 r.2.2)

/-- The value of `deriveFreeProg`. -/
def deriveFreeModel (Or : Oracle (groupSig D)) (n N : ℕ) (K : GroupData D.denote) (O : List ℕ)
    (L : LabelData) : DOut D :=
  cond (ncBD n N L O) (m1ContD Or n N (m1Model Or n N K (WinData.ofPoints N O) L))
    (noHintD K (WinData.ofPoints N O))

/-- The cost of `neqProg`: degree `N`, base size `m`, `f` points in `k` blocks, `p` points
with labels of at most `T` entries. -/
def neqCost (N m f k p T : ℕ) : ℕ :=
  (2 * N + 6 * f + 9 * k + 6) + (7 * m + 5) + (k + 1) + (p * (equidistCost k T + 4) + 1)

/-- The cost of the block step on `p` window points, below degree `N` with base size at most
`m = N − n`: `s₁` generators of the M1 child, the charges of M2a (`Bgen₂`) and of M2b (the
block stabilizer's `Bge`, `Bst`, `Btr`, `Bgt` with sizes `sS`, `Lt`, `sH`, and `Bgen₃`). -/
def blocksCost (n N p s₁ sS Lt sH Bgen₂ Bge Bst Btr Bgt Bgen₃ : ℕ) : ℕ :=
  baseBlocksCost N (N - n) s₁ + neqCost N (N - n) (N - n) (N - n) p (N - n) +
    m2aCost n N p s₁ n Bgen₂ +
    m2bCost N n (N - n) (N - n) s₁ sS Lt Bge Bst Btr Bgt (N - n) sH Bgen₃ p (N - n) n +
    2 * N + 6 * p + (N - n) + 80

/-- The cost of `m1ContProg`. -/
def m1ContCost (n N p s Borb Bgen s₁ sS Lt sH Bgen₂ Bge Bst Btr Bgt Bgen₃ : ℕ) : ℕ :=
  m1Cost n N p s Borb Bgen + blocksCost n N p s₁ sS Lt sH Bgen₂ Bge Bst Btr Bgt Bgen₃ + 30

/-- The cost of `deriveFreeProg`. -/
def deriveFreeCost (n N p s Borb Bgen s₁ sS Lt sH Bgen₂ Bge Bst Btr Bgt Bgen₃ : ℕ) : ℕ :=
  ncBCost n N p (N - n) + (2 * N + 5 * p + 7) +
    m1ContCost n N p s Borb Bgen s₁ sS Lt sH Bgen₂ Bge Bst Btr Bgt Bgen₃ + 12

/-- **The charges of the block step** on the M1 child `(N₁, gs₁)` with labels `L₁`, for the
maximal blocks `bs = mbD n N₁ gs₁` of its base: at most `s₁` generators; `Bgen₂` for M2a's
re-basing; for M2b the four charges of the stabilizer of block `0` (`blockStabProg`), the
sizes `sS`, `Lt`, `sH` of its stabilizer, transversal and result, and `Bgen₃` for its
re-basing. -/
structure BlkCharges (X : Ctx (groupSig D)) (n N₁ : ℕ) (gs₁ : GensData)
    (s₁ Bgen₂ Bge Bst Btr Bgt sS Lt sH Bgen₃ : ℕ) : Prop where
  gens : gs₁.length ≤ s₁
  m2a : X.B.call GroupOp.generate (n + (mbD n N₁ gs₁).length,
      rebaseGens n N₁ (mbD n N₁ gs₁) gs₁) (rebaseModel X.O n N₁ (mbD n N₁ gs₁) gs₁) ≤
        Bgen₂
  ge : X.B.call GroupOp.generate
      (N₁ + (mbD n N₁ gs₁).length, extendGens N₁ (mbD n N₁ gs₁) gs₁)
      (extGroup X.O N₁ (mbD n N₁ gs₁) gs₁) ≤ Bge
  st : X.B.call GroupOp.stabilizer (extGroup X.O N₁ (mbD n N₁ gs₁) gs₁, N₁ + 0)
      (bsStab X.O N₁ (mbD n N₁ gs₁) gs₁ 0) ≤ Bst
  tr : X.B.call GroupOp.orbitTransversal (extGroup X.O N₁ (mbD n N₁ gs₁) gs₁, N₁ + 0)
      (bsTrans X.O N₁ (mbD n N₁ gs₁) gs₁ 0) ≤ Btr
  gt : X.B.call GroupOp.generate
      (N₁, (bsStab X.O N₁ (mbD n N₁ gs₁) gs₁ 0).2.1.map (PermData.truncTo N₁))
      (blockStabModel X.O N₁ (mbD n N₁ gs₁) gs₁ 0).1 ≤ Bgt
  gen3 : X.B.call GroupOp.generate
      (n + (((mbD n N₁ gs₁).toArray.getD 0 []).map fun p => [p]).length,
        rebaseGens n N₁ (((mbD n N₁ gs₁).toArray.getD 0 []).map fun p => [p])
          (blockStabModel X.O N₁ (mbD n N₁ gs₁) gs₁ 0).1.2.1)
      (rebaseModel X.O n N₁ (((mbD n N₁ gs₁).toArray.getD 0 []).map fun p => [p])
        (blockStabModel X.O N₁ (mbD n N₁ gs₁) gs₁ 0).1.2.1) ≤ Bgen₃
  sS : (bsStab X.O N₁ (mbD n N₁ gs₁) gs₁ 0).2.1.length ≤ sS
  Lt : (bsTrans X.O N₁ (mbD n N₁ gs₁) gs₁ 0).length ≤ Lt
  sH : (blockStabModel X.O N₁ (mbD n N₁ gs₁) gs₁ 0).1.2.1.length ≤ sH

theorem baseBlocksCost_mono {N N' m m' s s' : ℕ} (hN : N ≤ N') (hm : m ≤ m') (hs : s ≤ s') :
    baseBlocksCost N m s ≤ baseBlocksCost N' m' s' := by
  unfold baseBlocksCost Luks.maxBlocksCost Luks.mbCost Luks.closureCost
  gcongr

theorem m2aCost_mono {n N N' p s s' Ls Ls' B : ℕ} (hN : N ≤ N') (hs : s ≤ s')
    (hL : Ls ≤ Ls') :
    m2aCost n N p s Ls B ≤ m2aCost n N' p s' Ls' B := by
  unfold m2aCost rebaseCost blockLabCost
  gcongr

theorem m2bCost_mono {N N' n mb mb' kb kb' s s' sS sS' Lt Lt' Bge Bst Btr Bgt k k' sH sH' B wl
    T T' Ls Ls' : ℕ} (hN : N ≤ N') (hmb : mb ≤ mb') (hkb : kb ≤ kb') (hs : s ≤ s')
    (hsS : sS ≤ sS') (hLt : Lt ≤ Lt') (hk : k ≤ k') (hsH : sH ≤ sH') (hT : T ≤ T')
    (hLs : Ls ≤ Ls') :
    m2bCost N n mb kb s sS Lt Bge Bst Btr Bgt k sH B wl T Ls ≤
      m2bCost N' n mb' kb' s' sS' Lt' Bge Bst Btr Bgt k' sH' B wl T' Ls' := by
  unfold m2bCost blockStabCost rebaseCost markCost interCost
  gcongr

theorem RunsWithin.blkOKProg (k : ℕ) (bs : List (List ℕ)) :
    RunsWithin X body (Main.blkOKProg k bs) (blkOKD k bs) ((bs.headD []).length + 8) := by
  have hc : RunsWithin X body
      (Prog.caseList (a := .list .nat) bs (.op0 (.natLit 0)) fun b _ => .op1 .length b)
      (bs.headD []).length ((bs.headD []).length + 2) := by
    cases bs with
    | nil => exact (RunsWithin.caseList_nil (RunsWithin.prim _ _)).mono (by simp [Prim.cost])
    | cons b rest =>
      exact (RunsWithin.caseList_cons (RunsWithin.prim _ _)).mono (by simp [Prim.cost]; omega)
  apply RunsWithin.mono
  case h =>
    run_step hc
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le (by simp [Prim.eval, blkOKD]) le_rfl
  case hc => simp [Prim.cost]

theorem RunsWithin.neqProg (n N : ℕ) (bs : List (List ℕ)) (L : LabelData) (pts : List ℕ)
    {T : ℕ} (hT : ∀ u ∈ pts, (L.getD u []).length ≤ T) :
    RunsWithin X body (Main.neqProg n N bs L pts) (neqD n N bs L pts)
      (neqCost N (N - n) bs.flatten.length bs.length pts.length T) := by
  have hany := RunsWithin.anyList_le (X := X) (body := body) (a' := .nat) (xs := pts)
    (c := equidistCost bs.length T + 2)
    (P := fun u => !equidistB bs.length (m2aIdx n N bs) (L.getD u []))
    (p := fun u => Prog.bind (Prog.op2 Prim.arrayGet L u) fun li =>
      Prog.bind (Toolkit.equidistProg bs.length (m2aIdx n N bs) li) fun e => Prog.op1 Prim.not e)
    fun u hu => by
      refine RunsWithin.bind_le (RunsWithin.prim _ _) (RunsWithin.bind_le
        (RunsWithin.equidistProg _ _ _) (RunsWithin.prim _ _) le_rfl) ?_
      simp only [Prim.cost, equidistCost]
      have := Nat.mul_le_mul_left bs.length (show 6 * (L.getD u []).length + 8 ≤ 6 * T + 8 by
        have := hT u hu; omega)
      simp only [Prim.eval, Ty.default] at this ⊢
      omega
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.blockIdxProg N bs)
    run_step (RunsWithin.m2aIdxProg n N _)
    run_step (RunsWithin.prim _ _)
    exact hany
  case hc =>
    have e : ∀ x : ℕ, x + 2 + 2 = x + 4 := fun x => by omega
    simp only [Prim.cost, neqCost, e, Args.head_cons]
    omega

theorem RunsWithin.m2aOutProg (r2 : GroupData D.denote × (WinData × LabelData)) :
    RunsWithin X body (Main.m2aOutProg r2) (m2aOutD r2) 12 := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.outProg _ _ _ _ _ _ _
  case hc => simp [Prim.cost]

theorem RunsWithin.m2bOutProg (G1 : GroupData D.denote) (pts : List ℕ)
    (r3 : (GroupData D.denote × List PermData) × (GroupData D.denote × LabelData)) :
    RunsWithin X body (Main.m2bOutProg G1 pts r3) (m2bOutD G1 pts r3)
      (2 * r3.2.1.1 + 5 * pts.length + 21) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    simp only [Prim.eval]
    run_step (RunsWithin.mkWindow _ _)
    exact RunsWithin.outProg _ _ _ _ _ _ _
  case hc => simp [Prim.cost]; omega

end BlockModels

/-! ### The block step: the spec -/

section BlockSpec

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b}
  {DV : ℕ → GensData → D.denote → Prop}

/-- Isomorphisms keeping the action on the string positions compose. -/
theorem dv_iso_trans {N N₁ N₂ n : ℕ} {G : Subgroup (Perm (Fin N))}
    {G₁ : Subgroup (Perm (Fin N₁))} {G₂ : Subgroup (Perm (Fin N₂))} (hn : n ≤ N₁)
    (h1 : ∃ θ : ↥G ≃* ↥G₁,
      ∀ (g : ↥G) (j : ℕ) (hj : j < N) (hj' : j < N₁), j < n →
      ((θ g : Perm (Fin N₁)) ⟨j, hj'⟩).val = (g.1 ⟨j, hj⟩).val)
    (h2 : ∃ θ : ↥G₁ ≃* ↥G₂,
      ∀ (g : ↥G₁) (j : ℕ) (hj : j < N₁) (hj' : j < N₂), j < n →
      ((θ g : Perm (Fin N₂)) ⟨j, hj'⟩).val = (g.1 ⟨j, hj⟩).val) :
    ∃ θ : ↥G ≃* ↥G₂, ∀ (g : ↥G) (j : ℕ) (hj : j < N) (hj' : j < N₂), j < n →
      ((θ g : Perm (Fin N₂)) ⟨j, hj'⟩).val = (g.1 ⟨j, hj⟩).val := by
  obtain ⟨θ₁, h₁⟩ := h1
  obtain ⟨θ₂, h₂⟩ := h2
  exact ⟨θ₁.trans θ₂, fun g j hj hj' hjn => by
    rw [MulEquiv.trans_apply, h₂ _ j (by omega) hj' hjn, h₁ g j hj (by omega) hjn]⟩

theorem dv_getD_len {N : ℕ} {gs : GensData} {pts : List ℕ} (c : ℕ) :
    ((Luks.maxBlocks N gs pts).toArray.getD c []).length ≤ pts.length := by
  rw [mr_getD_toArray']
  by_cases h : c < (Luks.maxBlocks N gs pts).length
  · rw [List.getD_eq_getElem _ _ h]
    exact dv_maxBlocks_len _ (List.getElem_mem h)
  · rw [List.getD_eq_default _ _ (by omega)]
    simp

/-- **The block step.** On a hinted M1 child `(N₁, gs₁, w₁, L₁)` of `K` whose base action is
transitive, the result is M2a's child (`blockLab`), M2b's reduction and child (`blockStab`),
or `stuck` when the maximal blocks are not proper. -/
theorem RunsWithin.blocksProg (hO : MeetsContractOn DV blockStabOps X.O)
    (hPre : ∀ op x, blockStabOps op → GroupPre DV op x → X.Pre op x)
    {n N : ℕ} {gs : GensData} {w : WinData} {L : LabelData} {d : D.denote} {O : List ℕ}
    {N₁ : ℕ} {gs₁ : GensData} {d₁ : D.denote} {w₁ : WinData} {L₁ : LabelData}
    (hc : ChildOK DV n N gs N₁ gs₁ d₁ w₁ L₁) (hw₁ : w₁.1 = O) (hO0 : O ≠ [])
    (hN₁ : N₁ ≤ N) (hLs : L₁.size ≤ n) (hLL : labLen L₁ ≤ labLen L)
    (htrB : IsTransOn (GensData.denote N₁ gs₁) (baseSet n N₁))
    {s₁ Bgen₂ Bge Bst Btr Bgt sS Lt sH Bgen₃ : ℕ}
    (hB : BlkCharges X n N₁ gs₁ s₁ Bgen₂ Bge Bst Btr Bgt sS Lt sH Bgen₃) :
    RunsWithin X body (Main.blocksProg n (N₁, gs₁, d₁) w₁ L₁)
        (blocksD X.O n (N₁, gs₁, d₁) w₁ L₁)
        (blocksCost n N O.length s₁ sS Lt sH Bgen₂ Bge Bst Btr Bgt Bgen₃) ∧
      DOutcome DV n N w L gs d O (blocksD X.O n (N₁, gs₁, d₁) w₁ L₁) := by
  subst hw₁
  have hn : n ≤ N₁ := hc.hint.le
  have hbase := hc.hint.base_inv
  have hgs := hc.valid.1
  have hT1 : ∀ u ∈ w₁.1, (L₁.getD u []).length ≤ N₁ - n := fun u hu =>
    mf_length_le_of_nodup (hc.hint.lab_nodup u hu) (hc.hint.lab_lt u hu)
  have hbb := RunsWithin.baseBlocksProg (X := X) (body := body) (d := d₁) hgs hbase
  have hok := RunsWithin.blkOKProg (X := X) (body := body) (N₁ - n) (mbD n N₁ gs₁)
  have hhd : ((mbD n N₁ gs₁).headD []).length ≤ N₁ - n := by
    have := dv_headD_len (N := N₁) (gs := gs₁) (pts := basePts n N₁)
    rwa [length_basePts] at this
  have hbbc : baseBlocksCost N₁ (N₁ - n) gs₁.length ≤ baseBlocksCost N (N - n) s₁ :=
    baseBlocksCost_mono hN₁ (by omega) hB.gens
  cases hok' : blkOKD (N₁ - n) (mbD n N₁ gs₁)
  · -- not proper: stuck
    have hm : blocksD X.O n (N₁, gs₁, d₁) w₁ L₁ =
        outD 6 (N₁, gs₁, d₁) (N₁, gs₁, d₁) []
        (N₁, gs₁, d₁) w₁ L₁ := by
      simp only [blocksD, hok', Bool.cond_false]
    rw [hm]
    refine ⟨?_, .stuck _ rfl⟩
    rw [hok'] at hok
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      simp only [Prim.eval]
      run_step hbb
      run_step hok
      run_step (RunsWithin.prim _ _)
      exact RunsWithin.ite_false (RunsWithin.outProg _ _ _ _ _ _ _)
    case hc =>
      simp only [Prim.cost, blocksCost]
      omega
  obtain ⟨h2k, hh⟩ := blkOKD_iff.1 hok'
  obtain ⟨hbs, hGb, hΨ, hcard, hsz⟩ := dv_blocks_facts hgs hbase htrB h2k hh
  have hflat : (mbD n N₁ gs₁).flatten.length = N₁ - n := by
    rw [hbs.1.length_eq]
    exact length_basePts n N₁
  have h2bs : 2 * (mbD n N₁ gs₁).length ≤ N₁ - n := hflat ▸ mf_two_mul_length_le hsz
  have hneq := RunsWithin.neqProg (X := X) (body := body) n N₁ (mbD n N₁ gs₁) L₁ w₁.1 hT1
  have hneqc : neqCost N₁ (N₁ - n) (mbD n N₁ gs₁).flatten.length (mbD n N₁ gs₁).length
      w₁.1.length (N₁ - n) ≤ neqCost N (N - n) (N - n) (N - n) w₁.1.length (N - n) := by
    unfold neqCost equidistCost
    rw [hflat]
    gcongr <;> omega
  have htrB' := dv_baseHom_trans hbase htrB
  rw [hok'] at hok
  cases hne : neqD n N₁ (mbD n N₁ gs₁) L₁ w₁.1
  · -- every label is equidistributed: M2b
    have hall : ∀ u ∈ w₁.1, equidistB (mbD n N₁ gs₁).length (m2aIdx n N₁ (mbD n N₁ gs₁))
        (L₁.getD u []) = true := by
      intro u hu
      by_contra hcon
      have : neqD n N₁ (mbD n N₁ gs₁) L₁ w₁.1 = true :=
        List.any_eq_true.2 ⟨u, hu, by simpa using hcon⟩
      rw [hne] at this
      exact Bool.false_ne_true this
    have hbs0 : 0 < (mbD n N₁ gs₁).length := by
      have h1 := List.toFinset_card_le ((mbD n N₁ gs₁).map (baseBlockSet n N₁))
      rw [List.length_map] at h1
      have h2 : 2 ≤ (blockFam n N₁ (mbD n N₁ gs₁)).card := hcard
      simp only [blockFam] at h2
      omega
    obtain ⟨u₀, hu₀⟩ := List.exists_mem_of_ne_nil _ hO0
    have hu₀N : u₀ < N₁ := hc.win.lt u₀ hu₀
    have heq : Equidist (blockFam n N₁ (mbD n N₁ gs₁))
        (labOf n N₁ L₁ ⟨u₀, hu₀N⟩) := by
      rw [← mf_blockFamily_eq hbs]
      exact (equidistB_iff (hc.hint.lab_nodup u₀ hu₀) (fun x => mem_labOf)
        (hc.hint.lab_lt u₀ hu₀)).1 (hall u₀ hu₀)
    have hwbv : (WinData.ofPoints N₁ (basePts n N₁)).Valid N₁ :=
      WinData.valid_ofPoints (basePts_nodup _ _) fun i hi => (mem_basePts.1 hi).2
    have hwbn : ∀ i ∈ (WinData.ofPoints N₁ (basePts n N₁)).1, n ≤ i :=
      fun i hi => (mem_basePts.1 hi).1
    obtain ⟨hrun3, hHN, hHv, hHden, hrv, hcov, hrl, hdeg3, hval3, hHb, hGb', hw', hden3⟩ :=
      RunsWithin.m2bProg (X := X) (body := body) (DV := DV) hO hPre hn hbase hwbv hwbn hbs hGb
        hgs hbs0 hB.ge hB.st hB.tr hB.gt hB.gen3 L₁ w₁.1 hT1
    have hm : blocksD X.O n (N₁, gs₁, d₁) w₁ L₁ =
        m2bOutD (N₁, gs₁, d₁) w₁.1
          (m2bModel X.O n N₁ gs₁ (mbD n N₁ gs₁) 0 L₁ w₁.1) := by
      simp only [blocksD, hok', hne, Bool.cond_true, Bool.cond_false]
    have hB0 : ((mbD n N₁ gs₁).toArray.getD 0 []).length ≤ N₁ - n := by
      have := dv_getD_len (N := N₁) (gs := gs₁) (pts := basePts n N₁) 0
      rwa [length_basePts] at this
    have hRP : GensData.denote N₁ (blockStabModel X.O N₁ (mbD n N₁ gs₁) gs₁ 0).1.2.1 ≤
        GensData.denote N₁ gs₁ := by
      rw [hHden]
      exact Subgroup.map_subtype_le _
    rw [hm]
    refine ⟨?_, ?_⟩
    · rw [hne] at hneq
      apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        simp only [Prim.eval]
        run_step hbb
        run_step hok
        run_step (RunsWithin.prim _ _)
        apply RunsWithin.ite_true
        run_step hneq
        apply RunsWithin.ite_false
        run_step (RunsWithin.prim _ _)
        run_step hrun3
        exact RunsWithin.m2bOutProg _ _ _
      case hc =>
        have h3 := m2bCost_mono (n := n) (Bge := Bge) (Bst := Bst) (Btr := Btr) (Bgt := Bgt)
          (B := Bgen₃) (wl := w₁.1.length) hN₁
          (show (mbD n N₁ gs₁).flatten.length ≤ N - n by omega)
          (show (mbD n N₁ gs₁).length ≤ N - n by omega) hB.gens hB.sS hB.Lt
          (show ((mbD n N₁ gs₁).toArray.getD 0 []).length ≤ N - n by omega) hB.sH
          (show N₁ - n ≤ N - n by omega) hLs
        have h4 : (m2bModel X.O n N₁ gs₁ (mbD n N₁ gs₁) 0 L₁ w₁.1).2.1.1 ≤ N := by
          rw [hdeg3]
          omega
        simp only [Prim.cost, blocksCost]
        omega
    · have e1 : (m2bModel X.O n N₁ gs₁ (mbD n N₁ gs₁) 0 L₁ w₁.1).1.1 = (N₁,
          (blockStabModel X.O N₁ (mbD n N₁ gs₁) gs₁ 0).1.2.1,
          (blockStabModel X.O N₁ (mbD n N₁ gs₁) gs₁ 0).1.2.2) :=
        Prod.ext hHN rfl
      unfold m2bOutD outD
      rw [e1]
      have hOn : ∀ i ∈ w₁.1, i < n := hc.hint.win_lt
      obtain ⟨-, hinv', -, hfa', hiso'⟩ := dv_rebase_facts hn hHb hw' mr_isBlockList_singletons
        hGb' (fun g hg => hc.faithful g (hRP hg)) hden3 hOn hc.win.nodup
        (fun g hg => hc.inv g (hRP hg))
      rw [List.length_map] at hinv' hfa' hiso'
      refine DOutcome.blockStab (Rgs := (blockStabModel X.O N₁ (mbD n N₁ gs₁) gs₁ 0).1.2.1)
        (Rd := (blockStabModel X.O N₁ (mbD n N₁ gs₁) gs₁ 0).1.2.2)
        (reps := (blockStabModel X.O N₁ (mbD n N₁ gs₁) gs₁ 0).2)
        (N' := (m2bModel X.O n N₁ gs₁ (mbD n N₁ gs₁) 0 L₁ w₁.1).2.1.1)
        (gs' := (m2bModel X.O n N₁ gs₁ (mbD n N₁ gs₁) 0 L₁ w₁.1).2.1.2.1)
        (d' := (m2bModel X.O n N₁ gs₁ (mbD n N₁ gs₁) 0 L₁ w₁.1).2.1.2.2)
        (L' := (m2bModel X.O n N₁ gs₁ (mbD n N₁ gs₁) 0 L₁ w₁.1).2.2)
        hc rfl hHv hRP hrv hcov (by
          have hrl' : (blockStabModel X.O N₁ (mbD n N₁ gs₁) gs₁ 0).2.length ≤
            (mbD n N₁ gs₁).length := hrl
          omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · rw [hdeg3]; exact hval3
      · rw [hdeg3]
        have := m2b_card hbs hΨ htrB' hcard hbs0
        omega
      · rw [hdeg3]; exact hfa'
      · rw [hdeg3]; exact hinv'
      · rw [hdeg3]; exact hiso'
      · intro wO hwO hwO0 hOinv
        rw [hdeg3]
        have hT : Transitive ↥(GensData.denote N₁ gs₁) (winFinset N₁ w₁) := by
          intro u hu v hv
          rw [mem_winFinset] at hu hv
          obtain ⟨g, hg, e⟩ := hc.trans u hu v hv
          exact ⟨⟨g, hg⟩, e⟩
        exact m2b_hintValid hc.hint hgs hc.win hc.inv hT htrB' hbs hΨ
          (u₀ := ⟨u₀, hu₀N⟩) hu₀ heq hbs0 hHden hHb hGb' hw' hval3.1 hden3 hwO hwO0
          hOinv
      · exact (labLen_m2bLabels_le hc.win.nodup n N₁ _ 0 L₁).trans hLL
  · -- some label is not equidistributed: M2a
    obtain ⟨u, hu, hu'⟩ := List.any_eq_true.1 hne
    have hne' : ∃ u ∈ w₁.1, equidistB (mbD n N₁ gs₁).length (m2aIdx n N₁ (mbD n N₁ gs₁))
        (L₁.getD u []) = false :=
      ⟨u, hu, by simpa using hu'⟩
    obtain ⟨hrun2, hdeg2, hval2, hhint2, hfa2, hwv2, hinv2, htr2, h2k2, θ2, hθ2⟩ :=
      RunsWithin.m2aProg (X := X) (body := body) (DV := DV)
        (fun op x hop hx => hO op x (Or.inl hop) hx) (fun op x hop hx => hPre op x (Or.inl hop) hx)
        hgs hc.win hc.inv hc.faithful hc.trans hc.hint hbs hGb hΨ htrB' hsz hne' hB.m2a
    have hm : blocksD X.O n (N₁, gs₁, d₁) w₁ L₁ =
        m2aOutD (m2aModel X.O n N₁ gs₁ w₁ L₁ (mbD n N₁ gs₁)) := by
      simp only [blocksD, hok', hne, Bool.cond_true]
    rw [hm]
    refine ⟨?_, ?_⟩
    · rw [hne] at hneq
      apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        simp only [Prim.eval]
        run_step hbb
        run_step hok
        run_step (RunsWithin.prim _ _)
        apply RunsWithin.ite_true
        run_step hneq
        apply RunsWithin.ite_true
        run_step hrun2
        exact RunsWithin.m2aOutProg _
      case hc =>
        have h2 : m2aCost n N₁ w₁.1.length gs₁.length L₁.size Bgen₂ ≤
            m2aCost n N w₁.1.length s₁ n Bgen₂ :=
          m2aCost_mono hN₁ hB.gens hLs
        simp only [Prim.cost, blocksCost]
        omega
    · refine .blockLab ?_ rfl ?_ ?_
      · show ChildOK DV n N gs (m2aModel X.O n N₁ gs₁ w₁ L₁ (mbD n N₁ gs₁)).1.1 _ _ _ _
        rw [hdeg2]
        exact ⟨hval2, hhint2, hwv2, hinv2, htr2, hfa2, dv_iso_trans hn hc.iso
          ⟨θ2, fun g j _ _ hjn => hθ2 g j hjn⟩⟩
      · show 2 * ((m2aModel X.O n N₁ gs₁ w₁ L₁ (mbD n N₁ gs₁)).1.1 - n) ≤ N - n
        rw [hdeg2]
        omega
      · exact (labLen_labM2aD_le hc.win.nodup n N₁ _ L₁).trans hLL

end BlockSpec

/-! ### No structure, or a colored partition: the spec -/

section FreeSpec

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b}
  {DV : ℕ → GensData → D.denote → Prop}

/-- The backend operations of `deriveProg`. -/
def deriveOps (op : GroupOp) : Prop :=
  op = .orbits ∨ op = .generate ∨ op = .stabilizer ∨ op = .orbitTransversal

theorem deriveOps_of_m1 {op : GroupOp} (h : m1Ops op) : deriveOps op := by
  rcases h with h | h <;> simp [deriveOps, h]

theorem deriveOps_of_bs {op : GroupOp} (h : blockStabOps op) : deriveOps op := by
  rcases h with h | h | h <;> simp [deriveOps, h]

theorem deriveOps_of_stab {op : GroupOp} (h : stabOps op) : deriveOps op := by
  rcases h with h | h <;> simp [deriveOps, h]

theorem size_labM1D (n : ℕ) (O : List ℕ) (L : LabelData) (mk : Array Bool) :
    (labM1D n O L mk).size = n := by
  simp [labM1D]

/-- **M1 and what follows**: on hint data `L'` for `K` on `O`, the result is M1's child
(`inter`) when its base has at most `3m/4` points, otherwise the block step (`blockLab`,
`blockStab` or `stuck`). -/
theorem RunsWithin.m1ContProg (hO : MeetsContractOn DV deriveOps X.O)
    (hPre : ∀ op x, deriveOps op → GroupPre DV op x → X.Pre op x) {n N : ℕ} {gs : GensData}
    {d : D.denote} {O : List ℕ} {L' : LabelData} {w : WinData} {L : LabelData}
    (hGv : GroupValid DV N gs d) (hOw : (WinData.ofPoints N O).Valid N)
    (hinv : IsInvariant (GensData.denote N gs) ((WinData.ofPoints N O).denote N))
    (hfaith : ∀ g ∈ GensData.denote N gs, (∀ j : Fin N, j.val < n → g j = j) → g = 1)
    (htr : IsTransOn (GensData.denote N gs) ((WinData.ofPoints N O).denote N))
    (hL : HintValid n N gs (WinData.ofPoints N O) L') (hO0 : O ≠ [])
    (hLL : labLen L' ≤ labLen L)
    {Borb Bgen s₁ Bgen₂ Bge Bst Btr Bgt sS Lt sH Bgen₃ : ℕ}
    (hB : M1Charges X n N gs d (WinData.ofPoints N O) L' Borb Bgen)
    (hB' : BlkCharges X n (m1Model X.O n N (N, gs, d) (WinData.ofPoints N O) L').1.1
      (m1Model X.O n N (N, gs, d) (WinData.ofPoints N O) L').1.2.1
      s₁ Bgen₂ Bge Bst Btr Bgt sS Lt sH Bgen₃) :
    RunsWithin X body (Main.m1ContProg n N (N, gs, d) (WinData.ofPoints N O) L')
        (m1ContD X.O n N (m1Model X.O n N (N, gs, d) (WinData.ofPoints N O) L'))
        (m1ContCost n N O.length gs.length Borb Bgen s₁ sS Lt sH Bgen₂ Bge Bst Btr Bgt
          Bgen₃) ∧
      DOutcome DV n N w L gs d O
        (m1ContD X.O n N (m1Model X.O n N (N, gs, d) (WinData.ofPoints N O) L')) := by
  have hO1 : MeetsContractOn DV m1Ops X.O := fun op x h => hO op x (deriveOps_of_m1 h)
  have hPre1 : ∀ op x, m1Ops op → GroupPre DV op x → X.Pre op x :=
    fun op x h => hPre op x (deriveOps_of_m1 h)
  have hO2 : MeetsContractOn DV blockStabOps X.O := fun op x h => hO op x (deriveOps_of_bs h)
  have hPre2 : ∀ op x, blockStabOps op → GroupPre DV op x → X.Pre op x :=
    fun op x h => hPre op x (deriveOps_of_bs h)
  obtain ⟨hrun, hch, hdeg, hk⟩ := dv_m1 (body := body) hO1 hPre1 hGv hOw hinv hfaith htr hL hB
  set r := m1Model X.O n N (N, gs, d) (WinData.ofPoints N O) L' with hrdef
  have hrL : labLen r.2.2 ≤ labLen L := by
    obtain ⟨hOnd, hOn⟩ := m1O_facts (X := X) hO1 hGv hL
    exact (labLen_labM1D_le hOnd hOn L' _).trans hLL
  have hq := RunsWithin.leQProg (X := X) (body := body) (r.1.1 - n) (N - n)
  cases hq' : leQD (r.1.1 - n) (N - n)
  · have hm : m1ContD X.O n N r = blocksD X.O n r.1 r.2.1 r.2.2 := by
      simp only [m1ContD, hq', Bool.cond_false]
    rw [hm]
    have htrB := dv_m1_trans (X := X) hO1 hGv hL
    obtain ⟨hrunB, hout⟩ := RunsWithin.blocksProg (body := body) (w := w) (L := L) (O := O)
      hO2 hPre2 (N₁ := r.1.1) (gs₁ := r.1.2.1) (d₁ := r.1.2.2) (w₁ := r.2.1) (L₁ := r.2.2) hch
      rfl hO0
      (by have := hL.le; rw [hdeg]; omega) (le_of_eq (size_labM1D _ _ _ _)) hrL htrB hB'
    refine ⟨?_, hout⟩
    rw [hq'] at hq
    apply RunsWithin.mono
    case h =>
      run_step hrun
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      simp only [Prim.eval]
      run_step hq
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      simp only [Prim.eval]
      exact RunsWithin.ite_false hrunB
    case hc =>
      simp only [Prim.cost, m1ContCost, WinData.ofPoints_fst]
      omega
  · have hm : m1ContD X.O n N r = outD 1 r.1 r.1 [] r.1 r.2.1 r.2.2 := by
      simp only [m1ContD, hq', Bool.cond_true]
    rw [hm]
    refine ⟨?_, .inter hch rfl (leQD_iff.1 hq') hrL⟩
    rw [hq'] at hq
    apply RunsWithin.mono
    case h =>
      run_step hrun
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      simp only [Prim.eval]
      run_step hq
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      simp only [Prim.eval]
      exact RunsWithin.ite_true (RunsWithin.outProg _ _ _ _ _ _ _)
    case hc =>
      simp only [Prim.cost, m1ContCost, WinData.ofPoints_fst]
      omega

/-- **No structure, or a colored partition**: no hint (`noHint`), or M1 and the block step
(`inter`, `blockLab`, `blockStab`, or `stuck`, which `derivePart_ne_stuck` excludes for a
colored partition). -/
theorem RunsWithin.deriveFreeProg (hO : MeetsContractOn DV deriveOps X.O)
    (hPre : ∀ op x, deriveOps op → GroupPre DV op x → X.Pre op x) {n N : ℕ}
    {gsG gs : GensData} {w : WinData} {L : LabelData} {d : D.denote} {O : List ℕ}
    (hS : DSetting DV n N gsG w L gs d O)
    {Borb Bgen s₁ Bgen₂ Bge Bst Btr Bgt sS Lt sH Bgen₃ : ℕ}
    (hB : M1Charges X n N gs d (WinData.ofPoints N O) L Borb Bgen)
    (hB' : BlkCharges X n (m1Model X.O n N (N, gs, d) (WinData.ofPoints N O) L).1.1
      (m1Model X.O n N (N, gs, d) (WinData.ofPoints N O) L).1.2.1
      s₁ Bgen₂ Bge Bst Btr Bgt sS Lt sH Bgen₃) :
    RunsWithin X body (Main.deriveFreeProg n N (N, gs, d) O L)
        (deriveFreeModel X.O n N (N, gs, d) O L)
        (deriveFreeCost n N O.length gs.length Borb Bgen s₁ sS Lt sH Bgen₂ Bge Bst Btr Bgt
          Bgen₃) ∧
      DOutcome DV n N w L gs d O (deriveFreeModel X.O n N (N, gs, d) O L) := by
  have hnc := RunsWithin.ncBProg (X := X) (body := body) n N L O hS.lab_len
  have hmk := RunsWithin.mkWindow (X := X) (body := body) N O
  cases hc : ncBD n N L O
  · have hm : deriveFreeModel X.O n N (N, gs, d) O L =
        noHintD (N, gs, d) (WinData.ofPoints N O) := by
      simp [deriveFreeModel, hc]
    rw [hm]
    refine ⟨?_, .noHint (DSetting.const hc) (hS.half hc)⟩
    rw [hc] at hnc
    apply RunsWithin.mono
    case h =>
      run_step hnc
      run_step hmk
      exact RunsWithin.ite_false (RunsWithin.noHintProg _ _)
    case hc => simp only [deriveFreeCost]; omega
  · obtain ⟨hrun, hout⟩ := RunsWithin.m1ContProg (body := body) (w := w) (L := L) hO hPre
      hS.kvalid hS.owin hS.oinv hS.kfaith hS.otrans (hS.hintK hc) hS.ne le_rfl hB hB'
    have hm : deriveFreeModel X.O n N (N, gs, d) O L =
        m1ContD X.O n N (m1Model X.O n N (N, gs, d) (WinData.ofPoints N O) L) := by
      simp [deriveFreeModel, hc]
    rw [hm]
    refine ⟨?_, hout⟩
    rw [hc] at hnc
    apply RunsWithin.mono
    case h =>
      run_step hnc
      run_step hmk
      exact RunsWithin.ite_true hrun
    case hc => simp only [deriveFreeCost]; omega

end FreeSpec

/-! ### Coloured Johnson structures: data -/

section CJData

/-- The cells as lists of positions. -/
def cellPosD (n : ℕ) (cs : List (List ℕ)) : List (List ℕ) := cs.map fun c => c.map (n + ·)

/-- The labels outside `V₀` (marked in `v0`), at the points of `O`. -/
def labDiffD (v0 : Array Bool) (L : LabelData) (O : List ℕ) : LabelData :=
  mapLabels L O fun l => l.filter fun j => !getB v0 j

/-- The Johnson union labels (cell indices), at the points of `O`. -/
def labJUD (nc : ℕ) (v0 : Array Bool) (fA : Array (List ℕ)) (L : LabelData) (O : List ℕ) :
    LabelData :=
  mapLabels L O (jUnionData nc v0 fA)

/-- **The Johnson union labels** at the points of `O`: at most `s` times longer, when every
marked point lies in at most `s ≥ 1` cells. -/
theorem labLen_labJUD_le {nc : ℕ} {v0 : Array Bool} {fA : Array (List ℕ)} {L : LabelData}
    {O : List ℕ} (hO : O.Nodup) {s : ℕ} (hs1 : 1 ≤ s)
    (hs : ∀ j, getB v0 j = true → (fA.getD j []).length ≤ s) :
    labLen (labJUD nc v0 fA L O) ≤ labLen L * s :=
  labLen_mapLabels_le hO (Nat.le_mul_of_pos_right _ hs1) fun i _ =>
    (length_jUnionData_le _ _ _ _ fun j _ hj => hs j hj).trans
      (Nat.mul_le_mul_right _ (length_getD_le_labLen L i))

/-- **The difference labels.** -/
theorem labLen_labDiffD_le {O : List ℕ} (hO : O.Nodup) (v0 : Array Bool) (L : LabelData) :
    labLen (labDiffD v0 L O) ≤ labLen L :=
  labLen_mapLabels_short hO fun _ => List.length_filter_le _ _
theorem dv_getD_mapLabels {L : LabelData} {O : List ℕ} (hO : O.Nodup) {F : List ℕ → List ℕ}
    (hF : F [] = []) {i : ℕ} (hi : i ∈ O) : (mapLabels L O F).getD i [] = F (L.getD i []) := by
  rw [getD_mapLabels hO]
  by_cases h : i < L.size
  · simp [hi, h]
  · simp only [hi, h, and_false, ite_false]
    have : L.getD i [] = [] := by
      simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (Nat.le_of_not_lt h)]
    rw [this, hF]

theorem dv_jUnionData_nil (nc : ℕ) (v0 : Array Bool) (fA : Array (List ℕ)) :
    jUnionData nc v0 fA [] = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro c hc
  obtain ⟨-, j, hj, -⟩ := (mem_jUnionData nc v0 fA [] c).1 hc
  simp at hj

theorem dv_getD_labDiff {v0 : Array Bool} {L : LabelData} {O : List ℕ} (hO : O.Nodup) {i : ℕ}
    (hi : i ∈ O) : (labDiffD v0 L O).getD i [] = (L.getD i []).filter fun j => !getB v0 j :=
  dv_getD_mapLabels hO List.filter_nil hi

theorem dv_getD_labJU {nc : ℕ} {v0 : Array Bool} {fA : Array (List ℕ)} {L : LabelData}
    {O : List ℕ} (hO : O.Nodup) {i : ℕ} (hi : i ∈ O) :
    (labJUD nc v0 fA L O).getD i [] = jUnionData nc v0 fA (L.getD i []) :=
  dv_getD_mapLabels hO (dv_jUnionData_nil nc v0 fA) hi

theorem dv_flatten_cellPos (n : ℕ) (cs : List (List ℕ)) :
    (cellPosD n cs).flatten = cs.flatten.map (n + ·) := by
  simp [cellPosD, List.map_flatten]

theorem dv_length_cellPos (n : ℕ) (cs : List (List ℕ)) :
    (cellPosD n cs).length = cs.length := by
  simp [cellPosD]

/-- The base action of an element, on data. -/
theorem dv_baseHom_val {N n : ℕ} {G : Subgroup (Perm (Fin N))}
    (hinv : IsInvariant G (baseSet n N)) {π : Perm (Fin N)} (hπ : π ∈ G) (γ : Fin (N - n)) :
    (baseHom G n hinv ⟨π, hπ⟩ γ).val = pAt π (n + γ.val) - n := by
  have h := congrArg Fin.val (baseHom_apply (hG := hinv) ⟨π, hπ⟩ γ)
  change n + (baseHom G n hinv ⟨π, hπ⟩ γ).val = (π (basePos γ)).val at h
  rw [pAt_of_lt _ (show n + γ.val < N by have := γ.2; omega)]
  change _ = (π (basePos γ)).val - n
  omega

/-- The base actions of a subgroup and of the group agree. -/
theorem dv_baseHom_le {N n : ℕ} {G H : Subgroup (Perm (Fin N))} (hHG : H ≤ G)
    (hG : IsInvariant G (baseSet n N)) (hH : IsInvariant H (baseSet n N)) {π : Perm (Fin N)}
    (hπ : π ∈ H) : baseHom H n hH ⟨π, hπ⟩ = baseHom G n hG ⟨π, hHG hπ⟩ :=
  Equiv.ext fun _ => Fin.ext rfl

end CJData

/-! ### Coloured Johnson structures: the labels on data -/

section CJFacts

variable {D : Ty} {DV : ℕ → GensData → D.denote → Prop} {n N : ℕ} {gsG gs : GensData}
  {w : WinData} {L : LabelData} {d : D.denote} {O : List ℕ} {e : CJData}

/-- **`V₀` is invariant**, on data: the mask of `V₀` is constant along the base action. -/
theorem dv_v0_inv {G : Subgroup (Perm (Fin N))} (hinv : IsInvariant G (baseSet n N))
    {jd : Align.JData}
    (hK : ∀ g : ↥G, baseHom G n hinv g • Align.jdec (N - n) jd = Align.jdec (N - n) jd)
    {π : Perm (Fin N)} (hπ : π ∈ G) {j : ℕ} (hj : j < N - n) :
    getB (markArr (N - n) jd.1) (pAt π (n + j) - n) = getB (markArr (N - n) jd.1) j := by
  have hV := jemb_V0 (ψ := baseHom G n hinv) hK ⟨π, hπ⟩
  have hval := dv_baseHom_val hinv hπ ⟨j, hj⟩
  set σ := baseHom G n hinv ⟨π, hπ⟩
  have h3 : σ ⟨j, hj⟩ ∈ (Align.jdec (N - n) jd).V0 ↔
      (⟨j, hj⟩ : Fin (N - n)) ∈ (Align.jdec (N - n) jd).V0 := by
    conv_lhs => rw [← hV]
    exact Finset.smul_mem_smul_finset_iff σ
  have h1 : (⟨j, hj⟩ : Fin (N - n)) ∈ (Align.jdec (N - n) jd).V0 ↔ j ∈ jd.1 :=
    SoJProg.mem_setOf
  have h2 : σ ⟨j, hj⟩ ∈ (Align.jdec (N - n) jd).V0 ↔ (σ ⟨j, hj⟩).val ∈ jd.1 :=
    SoJProg.mem_setOf
  have hlt := (σ ⟨j, hj⟩).2
  rw [hval] at h2 hlt
  apply Bool.eq_iff_iff.2
  rw [getB_markArr, getB_markArr]
  constructor
  · rintro ⟨-, h⟩
    exact ⟨hj, h1.1 (h3.1 (h2.2 h))⟩
  · rintro ⟨-, h⟩
    exact ⟨hlt, h2.1 (h3.2 (h1.2 h))⟩

/-- **The labels outside `V₀` are a hint** for `K` on `O`, when they are not constant on it. -/
theorem dv_labDiff_hint (hS : DSetting DV n N gsG w L gs d O) {jd : Align.JData}
    (hK : ∀ g : ↥(GensData.denote N gs),
      baseHom (GensData.denote N gs) n hS.base_inv g • Align.jdec (N - n) jd =
        Align.jdec (N - n) jd)
    (hc : ncBD n N (labDiffD (markArr (N - n) jd.1) L O) O = true) :
    HintValid n N gs (WinData.ofPoints N O) (labDiffD (markArr (N - n) jd.1) L O) := by
  have hget := fun {i} (hi : i ∈ O) => dv_getD_labDiff (v0 := markArr (N - n) jd.1) (L := L)
    hS.nodup hi
  refine hS.hintOf ?_ ?_ ?_ hc
  · intro i hi j hj
    rw [hget hi] at hj
    exact hS.lab_lt i hi j (List.mem_of_mem_filter hj)
  · intro i hi
    rw [hget hi]
    exact (hS.lab_nodup i hi).filter _
  · intro π hπ i hi j
    have hiN : i < N := hS.owin.lt i hi
    have hπi : pAt π i ∈ O := by
      rw [pAt_of_lt _ hiN]
      exact hS.oinv π hπ ⟨i, hiN⟩ hi
    rw [hget hπi, List.mem_filter, hS.lab_equivar π hπ i hi j]
    constructor
    · rintro ⟨⟨j', hj', e⟩, hv⟩
      refine ⟨j', ?_, e⟩
      rw [hget hi, List.mem_filter]
      refine ⟨hj', ?_⟩
      rw [← dv_v0_inv hS.base_inv hK hπ (hS.lab_lt i hi j' hj'), e]
      exact hv
    · rintro ⟨j', hj', e⟩
      rw [hget hi, List.mem_filter] at hj'
      refine ⟨⟨j', hj'.1, e⟩, ?_⟩
      rw [← e, dv_v0_inv hS.base_inv hK hπ (hS.lab_lt i hi j' hj'.1)]
      exact hj'.2

/-- **The labels outside `V₀` are constant** on `O` when the test fails. -/
theorem dv_labDiff_const (hS : DSetting DV n N gsG w L gs d O) {jd : Align.JData}
    (hc : ncBD n N (labDiffD (markArr (N - n) jd.1) L O) O = false) :
    ¬ NonConst (winFinset N (WinData.ofPoints N O))
      fun u => labOf n N L u \ (Align.jdec (N - n) jd).V0 := by
  rintro ⟨u, hu, v, hv, hne⟩
  rw [mem_winFinset] at hu hv
  apply hne
  have hconst := DSetting.const hc u.val hu v.val hv
  have key : ∀ x : Fin N, x.val ∈ O → labOf n N L x \ (Align.jdec (N - n) jd).V0 =
      SoJProg.setOf (N - n) ((labDiffD (markArr (N - n) jd.1) L O).getD x.val []) := by
    intro x hx
    ext γ
    rw [dv_getD_labDiff hS.nodup hx, Finset.mem_sdiff, mem_labOf, SoJProg.mem_setOf,
      List.mem_filter]
    have : γ ∈ (Align.jdec (N - n) jd).V0 ↔ γ.val ∈ jd.1 := SoJProg.mem_setOf
    rw [this, Bool.not_eq_true', ← Bool.not_eq_true, getB_markArr]
    have := γ.2
    tauto
  show labOf n N L u \ _ = labOf n N L v \ _
  rw [key u hu, key v hv, hconst]

end CJFacts

/-! ### Coloured Johnson structures: the union and the cells on data -/

section CJCells

variable {D : Ty} {DV : ℕ → GensData → D.denote → Prop} {n N : ℕ} {gsG gs : GensData}
  {w : WinData} {L : LabelData} {d : D.denote} {O : List ℕ}

/-- The cells of the Johnson union are listed cells. -/
theorem dv_jUnion_cell {m : ℕ} {jd : Align.JData} (hJv : Align.JValid m jd)
    {T a : Finset (Fin m)} (ha : a ∈ jUnion (Align.jdec m jd) T) :
    ∃ c < jd.2.1.length, SoJProg.cellAt m jd.2.1 c = a := by
  simp only [jUnion, Finset.mem_biUnion] at ha
  obtain ⟨x, hx, hax⟩ := ha
  have hxV : x.val ∈ jd.1 := SoJProg.mem_setOf.1 (Finset.mem_inter.1 hx).2
  obtain ⟨c, hc, rfl⟩ := SoJProg.mem_famIdx.1 hax
  exact ⟨c, hJv.f_lt x.val hxV c hc, rfl⟩

/-- **The Johnson union on data**: cell `c` is in the union labels exactly when it is a cell of
the Johnson union. -/
theorem dv_mem_jUnionData {m : ℕ} {jd : Align.JData} (hJv : Align.JValid m jd) {Lu : List ℕ}
    (hLu : ∀ j ∈ Lu, j < m) {c : ℕ} (hc : c < jd.2.1.length) :
    c ∈ jUnionData jd.2.1.length (markArr m jd.1) jd.2.2.2 Lu ↔
      SoJProg.cellAt m jd.2.1 c ∈ jUnion (Align.jdec m jd) (SoJProg.setOf m Lu) := by
  refine mem_jUnionData_iff (fun x => SoJProg.mem_setOf) hLu (fun x => ?_)
    (fun x hx c hc => ?_) (fun x _ => ?_)
    (fun c hc c' hc' h => Align.jcells_distinct hJv c hc c' hc' h) hc
  · rw [getB_markArr]
    exact ⟨fun h => ⟨x.2, SoJProg.mem_setOf.1 h⟩, fun h => SoJProg.mem_setOf.2 h.2⟩
  · exact hJv.f_lt x.val (SoJProg.mem_setOf.1 hx) c hc
  · simp only [Align.jdec, SoJProg.jembOf, SoJProg.famIdx]
    ext a
    simp [SoJProg.cellAt]

/-- **The Johnson union is constant** on `O` when the test on its labels fails. -/
theorem dv_labJU_const (hS : DSetting DV n N gsG w L gs d O) {jd : Align.JData}
    (hJv : Align.JValid (N - n) jd)
    (hc : ncBD n (n + jd.2.1.length)
      (labJUD jd.2.1.length (markArr (N - n) jd.1) jd.2.2.2 L O) O = false) :
    ¬ NonConst (winFinset N (WinData.ofPoints N O))
      fun u => jUnion (Align.jdec (N - n) jd) (labOf n N L u) := by
  rintro ⟨u, hu, v, hv, hne⟩
  rw [mem_winFinset] at hu hv
  apply hne
  have hconst := DSetting.const hc u.val hu v.val hv
  have key : ∀ x : Fin N, x.val ∈ O → ∀ c < jd.2.1.length,
      (c ∈ (labJUD jd.2.1.length (markArr (N - n) jd.1) jd.2.2.2 L O).getD x.val [] ↔
        SoJProg.cellAt (N - n) jd.2.1 c ∈ jUnion (Align.jdec (N - n) jd) (labOf n N L x)) := by
    intro x hx c hc
    rw [dv_getD_labJU hS.nodup hx, mr_labOf_eq_setOf]
    exact dv_mem_jUnionData hJv (hS.lab_lt x.val hx) hc
  have hmem : ∀ c < jd.2.1.length,
      (c ∈ (labJUD jd.2.1.length (markArr (N - n) jd.1) jd.2.2.2 L O).getD u.val [] ↔
        c ∈ (labJUD jd.2.1.length (markArr (N - n) jd.1) jd.2.2.2 L O).getD v.val []) := by
    intro c hc
    have h := congrArg (fun T => (⟨c, by omega⟩ : Fin (n + jd.2.1.length - n)) ∈ T) hconst
    simpa only [SoJProg.mem_setOf, eq_iff_iff] using h
  show jUnion _ (labOf n N L u) = jUnion _ (labOf n N L v)
  ext a
  constructor
  · intro ha
    obtain ⟨c, hc, rfl⟩ := dv_jUnion_cell hJv ha
    exact (key v hv c hc).1 ((hmem c hc).1 ((key u hu c hc).2 ha))
  · intro ha
    obtain ⟨c, hc, rfl⟩ := dv_jUnion_cell hJv ha
    exact (key u hu c hc).1 ((hmem c hc).2 ((key v hv c hc).2 ha))

/-- The cells as positions form a valid window. -/
theorem dv_cellPos_valid {jd : Align.JData} (hJv : Align.JValid (N - n) jd) (hn : n ≤ N) :
    (WinData.ofPoints N (cellPosD n jd.2.1).flatten).Valid N := by
  refine WinData.valid_ofPoints ?_ ?_
  · rw [dv_flatten_cellPos]
    refine List.Nodup.map (fun a b h => by simpa using h) ?_
    exact List.nodup_flatten.2 ⟨fun c hc => hJv.cell_nodup c hc,
      hJv.cell_disj.imp fun h a ha hb => h a ha hb⟩
  · intro x hx
    rw [dv_flatten_cellPos] at hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
    obtain ⟨c, hc, hac⟩ := List.mem_flatten.1 ha
    have := hJv.cell_lt c hc a hac
    omega

/-- The cells as positions are a block list of their points. -/
theorem dv_cellPos_blocks {jd : Align.JData} (hJv : Align.JValid (N - n) jd) :
    IsBlockList (WinData.ofPoints N (cellPosD n jd.2.1).flatten) (cellPosD n jd.2.1) := by
  refine ⟨List.Perm.refl _, fun b hb => ?_⟩
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hb
  simpa using hJv.cell_ne c hc

/-- A group preserving the Johnson structure maps every cell onto a listed cell. -/
theorem dv_cell_image {G : Subgroup (Perm (Fin N))} (hinv : IsInvariant G (baseSet n N))
    {jd : Align.JData}
    (hK : ∀ g : ↥G, baseHom G n hinv g • Align.jdec (N - n) jd = Align.jdec (N - n) jd)
    {π : Perm (Fin N)} (hπ : π ∈ G) {c : List ℕ} (hc : c ∈ jd.2.1) :
    ∃ c' ∈ jd.2.1, SoJProg.setOf (N - n) c' =
      baseHom G n hinv ⟨π, hπ⟩ • SoJProg.setOf (N - n) c := by
  have hΛ := jemb_Λ (ψ := baseHom G n hinv) hK ⟨π, hπ⟩
  have hcΛ : SoJProg.setOf (N - n) c ∈ (Align.jdec (N - n) jd).Λ :=
    SoJProg.mem_famOf.2 ⟨c, hc, rfl⟩
  have : baseHom G n hinv ⟨π, hπ⟩ • SoJProg.setOf (N - n) c ∈
      (Align.jdec (N - n) jd).Λ := by
    rw [← hΛ]
    exact Finset.smul_mem_smul_finset hcΛ
  exact SoJProg.mem_famOf.1 this

/-- The position of a base point under an element of a group preserving the base. -/
theorem dv_pAt_base {G : Subgroup (Perm (Fin N))} (hinv : IsInvariant G (baseSet n N))
    {π : Perm (Fin N)} (hπ : π ∈ G) (γ : Fin (N - n)) :
    pAt π (n + γ.val) = n + (baseHom G n hinv ⟨π, hπ⟩ γ).val := by
  rw [dv_baseHom_val hinv hπ γ]
  have hlt : n + γ.val < N := by have := γ.2; omega
  have : n ≤ pAt π (n + γ.val) := by
    rw [pAt_of_lt _ hlt]
    exact hinv π hπ ⟨n + γ.val, hlt⟩ (show n ≤ n + γ.val by omega)
  omega

/-- **A group preserving the Johnson structure permutes the cells** (as positions). -/
theorem dv_cellPos_perm {G : Subgroup (Perm (Fin N))} (hinv : IsInvariant G (baseSet n N))
    {jd : Align.JData} (hJv : Align.JValid (N - n) jd)
    (hK : ∀ g : ↥G, baseHom G n hinv g • Align.jdec (N - n) jd = Align.jdec (N - n) jd) :
    PermutesBlocks G (cellPosD n jd.2.1) := by
  intro π hπ b hb
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hb
  obtain ⟨c', hc', hc'e⟩ := dv_cell_image hinv hK hπ hc
  refine ⟨c'.map (n + ·), List.mem_map.2 ⟨c', hc', rfl⟩, fun u hu => ?_⟩
  obtain ⟨x, hx, hxu⟩ := List.mem_map.1 hu
  have hxm : x < N - n := hJv.cell_lt c hc x hx
  have hσ : baseHom G n hinv ⟨π, hπ⟩ ⟨x, hxm⟩ ∈ SoJProg.setOf (N - n) c' := by
    rw [hc'e]
    exact Finset.smul_mem_smul_finset (SoJProg.mem_setOf.2 hx)
  have hp := dv_pAt_base hinv hπ ⟨x, hxm⟩
  have hu' : u = ⟨n + x, by omega⟩ := Fin.ext hxu.symm
  rw [pAt_of_lt _ (by omega)] at hp
  rw [hu']
  exact List.mem_map.2 ⟨_, SoJProg.mem_setOf.1 hσ, hp.symm⟩

theorem dv_mem_cellPos {cs : List (List ℕ)} {t : ℕ} (ht : t < (cellPosD n cs).length)
    {x : ℕ} :
    x ∈ (cellPosD n cs)[t] ↔ ∃ y ∈ cs.getD t [], n + y = x := by
  rw [dv_length_cellPos] at ht
  simp only [cellPosD, List.getElem_map, List.mem_map]
  rw [List.getD_eq_getElem _ _ ht]

/-- **The block action on the cells is the action on the cells**: `blockMap` sends cell `c` to
the index of its image. -/
theorem dv_blockMap_cell {G : Subgroup (Perm (Fin N))} (hinv : IsInvariant G (baseSet n N))
    {jd : Align.JData} (hJv : Align.JValid (N - n) jd) (hn : n ≤ N)
    (hK : ∀ g : ↥G, baseHom G n hinv g • Align.jdec (N - n) jd = Align.jdec (N - n) jd)
    {π : Perm (Fin N)} (hπ : π ∈ G) {c : ℕ} (hc : c < jd.2.1.length) :
    blockMap N (cellPosD n jd.2.1) π c < jd.2.1.length ∧
      SoJProg.cellAt (N - n) jd.2.1 (blockMap N (cellPosD n jd.2.1) π c) =
        baseHom G n hinv ⟨π, hπ⟩ • SoJProg.cellAt (N - n) jd.2.1 c := by
  have hcl : c < (cellPosD n jd.2.1).length := by rw [dv_length_cellPos]; exact hc
  obtain ⟨ht', himg⟩ := blockMap_spec (dv_cellPos_valid hJv hn) (dv_cellPos_blocks hJv)
    (dv_cellPos_perm hinv hJv hK) hπ hcl
  have ht'' : blockMap N (cellPosD n jd.2.1) π c < jd.2.1.length := by
    rw [dv_length_cellPos] at ht'
    exact ht'
  refine ⟨ht'', ?_⟩
  have hcmem := Align.getD_mem_cell hc
  obtain ⟨c'', hc'', hc''e⟩ := dv_cell_image hinv hK hπ hcmem
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc''
  -- the images of the points of cell `c` are in cell `blockMap π c` and in cell `i`
  have hmap : ∀ x ∈ jd.2.1.getD c [], ∃ hx : x < N - n,
      (baseHom G n hinv ⟨π, hπ⟩ ⟨x, hx⟩).val ∈
        jd.2.1.getD (blockMap N (cellPosD n jd.2.1) π c) [] := by
    intro x hx
    have hxm : x < N - n := hJv.cell_lt _ hcmem x hx
    refine ⟨hxm, ?_⟩
    have hu : (⟨n + x, by omega⟩ : Fin N).val ∈ (cellPosD n jd.2.1)[c] :=
      (dv_mem_cellPos hcl).2 ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hye⟩ := (dv_mem_cellPos ht').1 (himg _ hu)
    have hp := dv_pAt_base hinv hπ ⟨x, hxm⟩
    rw [pAt_of_lt _ (by omega)] at hp
    have : y = (baseHom G n hinv ⟨π, hπ⟩ ⟨x, hxm⟩).val := by
      change n + y = (π ⟨n + x, _⟩).val at hye
      change (π ⟨n + x, _⟩).val = _ at hp
      omega
    rw [← this]
    exact hy
  have hci : i = blockMap N (cellPosD n jd.2.1) π c := by
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ (hJv.cell_ne _ hcmem)
    obtain ⟨hxm, hxc'⟩ := hmap x hx
    have hxi : (baseHom G n hinv ⟨π, hπ⟩ ⟨x, hxm⟩).val ∈ jd.2.1.getD i [] := by
      rw [List.getD_eq_getElem _ _ hi]
      have : baseHom G n hinv ⟨π, hπ⟩ ⟨x, hxm⟩ ∈ SoJProg.setOf (N - n) jd.2.1[i] := by
        rw [hc''e]
        exact Finset.smul_mem_smul_finset (SoJProg.mem_setOf.2 hx)
      exact SoJProg.mem_setOf.1 this
    by_contra hne
    exact Align.jo_cells_disj hJv.cell_disj hi ht'' hne hxi hxc'
  rw [← hci]
  unfold SoJProg.cellAt
  rw [List.getD_eq_getElem _ _ hi]
  exact hc''e

theorem dv_cells_flatten_nodup {m : ℕ} {jd : Align.JData} (hJv : Align.JValid m jd) :
    jd.2.1.flatten.Nodup :=
  List.nodup_flatten.2 ⟨fun c hc => hJv.cell_nodup c hc,
    hJv.cell_disj.imp fun h a ha hb => h a ha hb⟩

/-- At most `m` cells. -/
theorem dv_nc_le {m : ℕ} {jd : Align.JData} (hJv : Align.JValid m jd) : jd.2.1.length ≤ m := by
  have h1 : jd.2.1.length ≤ jd.2.1.flatten.length := by
    rw [List.length_flatten]
    calc jd.2.1.length = (jd.2.1.map fun _ => 1).sum := by simp
      _ ≤ (jd.2.1.map List.length).sum :=
        List.sum_le_sum fun c hc => List.length_pos_of_ne_nil (hJv.cell_ne c hc)
  have h2 : jd.2.1.flatten.length ≤ m := mf_length_le_of_nodup (dv_cells_flatten_nodup hJv)
    fun a ha => by
      obtain ⟨c, hc, hac⟩ := List.mem_flatten.1 ha
      exact hJv.cell_lt c hc a hac
  omega

/-- The cell lists of a point have at most `|Λ|` entries. -/
theorem dv_fl_len {m : ℕ} {jd : Align.JData} (hJv : Align.JValid m jd) (j : ℕ) :
    (jd.2.2.2.getD j []).length ≤ jd.2.1.length := by
  by_cases hj : j ∈ jd.1
  · exact mf_length_le_of_nodup (hJv.f_nodup j hj) (hJv.f_lt j hj)
  · have := hJv.trim j hj
    simp only [Align.jfl] at this
    rw [this]
    exact Nat.zero_le _

end CJCells

/-! ### Coloured Johnson structures: the union re-based onto the cells -/

section CJRebase

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)} {DV : ℕ → GensData → D.denote → Prop}
  {n N : ℕ} {gsG gs : GensData} {w : WinData} {L : LabelData} {d : D.denote} {O : List ℕ}

/-- The labels are equivariant for `K`, as sets. -/
theorem DSetting.lab_smul (hS : DSetting DV n N gsG w L gs d O) {g : Perm (Fin N)}
    (hg : g ∈ GensData.denote N gs) {u : Fin N} (hu : u.val ∈ O) :
    labOf n N L (g u) =
      baseHom (GensData.denote N gs) n hS.base_inv ⟨g, hg⟩ • labOf n N L u := by
  have hh := hS.hint.isHint hS.gvalid hS.win hS.inv
  have := hh.equivar ⟨g, hS.le hg⟩ u (mem_winFinset.2 (hS.sub _ hu))
  rw [dv_baseHom_le hS.le hS.hint.base_inv hS.base_inv hg]
  exact this

/-- **The union labels on data**: at a point of `O`, cell `c` is a union label exactly when it
is a listed cell of the Johnson union of the label. -/
theorem dv_mem_labJU (hS : DSetting DV n N gsG w L gs d O) {jd : Align.JData}
    (hJv : Align.JValid (N - n) jd) {i : ℕ} (hi : i ∈ O) (c : ℕ) :
    c ∈ (labJUD jd.2.1.length (markArr (N - n) jd.1) jd.2.2.2 L O).getD i [] ↔
      c < jd.2.1.length ∧ SoJProg.cellAt (N - n) jd.2.1 c ∈
        jUnion (Align.jdec (N - n) jd) (SoJProg.setOf (N - n) (L.getD i [])) := by
  rw [dv_getD_labJU hS.nodup hi]
  constructor
  · intro hc
    have hcl := ((mem_jUnionData _ _ _ _ c).1 hc).1
    exact ⟨hcl, (dv_mem_jUnionData hJv (hS.lab_lt i hi) hcl).1 hc⟩
  · rintro ⟨hcl, hc⟩
    exact (dv_mem_jUnionData hJv (hS.lab_lt i hi) hcl).2 hc

/-- **The union labels are equivariant for the action on the cells**: the union labels at
`g u` are the images under the block action on the cells of those at `u`. -/
theorem dv_labJU_equivar (hS : DSetting DV n N gsG w L gs d O) {jd : Align.JData}
    (hJv : Align.JValid (N - n) jd)
    (hK : ∀ g : ↥(GensData.denote N gs),
      baseHom (GensData.denote N gs) n hS.base_inv g • Align.jdec (N - n) jd =
        Align.jdec (N - n) jd)
    {g : Perm (Fin N)} (hg : g ∈ GensData.denote N gs) {i : ℕ} (hi : i ∈ O) (hiN : i < N)
    (c : ℕ) :
    c ∈ (labJUD jd.2.1.length (markArr (N - n) jd.1) jd.2.2.2 L O).getD (g ⟨i, hiN⟩).val [] ↔
      ∃ c' ∈ (labJUD jd.2.1.length (markArr (N - n) jd.1) jd.2.2.2 L O).getD i [],
        blockMap N (cellPosD n jd.2.1) g c' = c := by
  have hn := hS.hint.le
  have hbase := hS.base_inv
  have hgi : (g ⟨i, hiN⟩).val ∈ O := hS.oinv g hg ⟨i, hiN⟩ hi
  have hlab := hS.lab_smul hg (u := ⟨i, hiN⟩) hi
  rw [mr_labOf_eq_setOf, mr_labOf_eq_setOf] at hlab
  rw [dv_mem_labJU hS hJv hgi, hlab, jUnion_smul (ψ := baseHom (GensData.denote N gs) n hbase) hK]
  constructor
  · rintro ⟨hc, hcm⟩
    obtain ⟨a, ha, hac⟩ := Finset.mem_smul_finset.1 hcm
    obtain ⟨c', hc', rfl⟩ := dv_jUnion_cell hJv ha
    obtain ⟨hbm, hbme⟩ := dv_blockMap_cell hbase hJv hn hK hg hc'
    refine ⟨c', (dv_mem_labJU hS hJv hi c').2 ⟨hc', ha⟩, ?_⟩
    refine Align.jcells_distinct hJv _ hbm _ hc ?_
    show SoJProg.cellAt (N - n) jd.2.1 _ = SoJProg.cellAt (N - n) jd.2.1 c
    rw [← hac]
    exact hbme
  · rintro ⟨c', hc', rfl⟩
    obtain ⟨hc'l, hc'm⟩ := (dv_mem_labJU hS hJv hi c').1 hc'
    obtain ⟨hbm, hbme⟩ := dv_blockMap_cell hbase hJv hn hK hg hc'l
    refine ⟨hbm, ?_⟩
    rw [hbme]
    exact Finset.smul_mem_smul_finset hc'm

/-- **The Johnson union re-based onto the cells** is a hinted child: when `K` preserves the
Johnson structure and the union labels are not constant on `O`, the re-based group (degree
`n + |Λ|`, the cells `cellPosD` as the new base), the window `O` and the union labels (cell
indices) satisfy `ChildOK`. -/
theorem dv_cells_child (hO : MeetsContractOn DV rebaseOps X.O)
    (hS : DSetting DV n N gsG w L gs d O) {jd : Align.JData} (hJv : Align.JValid (N - n) jd)
    (hK : ∀ g : ↥(GensData.denote N gs),
      baseHom (GensData.denote N gs) n hS.base_inv g • Align.jdec (N - n) jd =
        Align.jdec (N - n) jd)
    (hcU : ncBD n (n + jd.2.1.length)
      (labJUD jd.2.1.length (markArr (N - n) jd.1) jd.2.2.2 L O) O = true) :
    ChildOK DV n N gs (n + (cellPosD n jd.2.1).length)
      (rebaseModel X.O n N (cellPosD n jd.2.1) gs).2.1
      (rebaseModel X.O n N (cellPosD n jd.2.1) gs).2.2
      (WinData.ofPoints (n + (cellPosD n jd.2.1).length) O)
      (labJUD jd.2.1.length (markArr (N - n) jd.1) jd.2.2.2 L O) := by
  have hn := hS.hint.le
  have hbase := hS.base_inv
  have hw := dv_cellPos_valid (n := n) hJv hn
  have hbs := dv_cellPos_blocks (N := N) (n := n) hJv
  have hGb := dv_cellPos_perm hbase hJv hK
  obtain ⟨-, hval, hden⟩ := dv_rebase_den (X := X) (DV := DV) hO hn hbase hw hbs hGb
    hS.kvalid.1
  have hk : (cellPosD n jd.2.1).length = jd.2.1.length := dv_length_cellPos _ _
  obtain ⟨hwv, hinv', htr', hfa', hiso'⟩ := dv_rebase_facts hn hbase hw hbs hGb hS.kfaith
    hden hS.win_lt hS.nodup hS.oinv
  refine ⟨hval, ?_, hwv, hinv', htr' hS.otrans, hfa', hiso'⟩
  have hstr := isInvariant_strSet hbase
  refine hintValid_of_forall (by omega) hval.1
    (by rw [hden]; exact (rebase_invariant hn hstr hw hbs hGb).1)
    (by simpa using hS.win_lt) ?_ ?_ ?_ ?_
  · intro i hi c hc
    simp only [WinData.ofPoints_fst] at hi
    have := ((dv_mem_labJU hS hJv hi c).1 hc).1
    omega
  · intro i hi
    simp only [WinData.ofPoints_fst] at hi
    rw [dv_getD_labJU hS.nodup hi]
    exact nodup_jUnionData _ _ _ _
  · intro π hπ i hi
    simp only [WinData.ofPoints_fst] at hi
    rw [hden] at hπ
    obtain ⟨g, rfl⟩ := hπ
    have hin := hS.win_lt i hi
    have hiN : i < N := hS.owin.lt i hi
    rw [pAt_rebaseHom_lt hn hstr hw hbs hGb g hin]
    ext c
    simp only [List.mem_toFinset, List.mem_map]
    rw [dv_labJU_equivar hS hJv hK g.2 hi hiN c]
    constructor
    · rintro ⟨c', hc', rfl⟩
      refine ⟨c', hc', ?_⟩
      have hc'l := ((dv_mem_labJU hS hJv hi c').1 hc').1
      rw [pAt_rebaseHom_ge hn hstr hw hbs hGb g (by rw [hk]; exact hc'l)]
    · rintro ⟨c', hc', rfl⟩
      have hc'l := ((dv_mem_labJU hS hJv hi c').1 hc').1
      refine ⟨c', hc', ?_⟩
      rw [pAt_rebaseHom_ge hn hstr hw hbs hGb g (by rw [hk]; exact hc'l)]
  · obtain ⟨i, hi, j, hj, hne⟩ := dv_ncBD_iff.1 hcU
    refine ⟨i, by simpa using hi, j, by simpa using hj, fun he => hne ?_⟩
    ext x
    simp only [SoJProg.mem_setOf]
    rw [← List.mem_toFinset, he, List.mem_toFinset]

end CJRebase

/-! ### Coloured Johnson structures: the fallback -/

section CJFallback

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b}
  {DV : ℕ → GensData → D.denote → Prop}
  {n N : ℕ} {gsG gs : GensData} {w : WinData} {L : LabelData} {d : D.denote} {O : List ℕ}

/-- **The number of union cells**, the data version of `card_jUnion_le`: at a point `u₀`, the
union labels have at most `|L u₀| · s` cells (`s = jd.2.2.1`, the parameter of the Johnson
data). -/
theorem jfallback_cells_le {m : ℕ} {jd : Align.JData} (hJv : Align.JValid m jd) (Lu : List ℕ) :
    (jUnionData jd.2.1.length (markArr m jd.1) jd.2.2.2 Lu).length ≤ Lu.length * jd.2.2.1 := by
  refine length_jUnionData_le _ _ _ _ fun j _ hj => ?_
  have hjV : j ∈ jd.1 := ((getB_markArr _ _ _).1 hj).2
  exact le_of_eq (hJv.f_len j hjV)

/-- **The Johnson fallback** on the orbit `O`, when the labels, but neither the labels outside
`V₀` nor the Johnson union, are not constant on `O`. In the group `G₄ = ⟨gs₄⟩` re-based onto
the cells, the program `jfallbackProg` computes the pointwise stabilizer `R` of the positions
of the union cells at the first point of `O`; the outcome is `johnFallback`, with `u` the
number of these cells. -/
theorem dv_jfallback (hO : MeetsContractOn DV stabOps X.O)
    (hPre : ∀ op x, stabOps op → GroupPre DV op x → X.Pre op x)
    (hS : DSetting DV n N gsG w L gs d O) {jd : Align.JData} (hJv : Align.JValid (N - n) jd)
    {V : Finset (Fin (N - n))} {t : ℕ} (hJ : IsJohnson V t (Align.jdec (N - n) jd))
    (hK : ∀ g : ↥(GensData.denote N gs),
      baseHom (GensData.denote N gs) n hS.base_inv g • Align.jdec (N - n) jd =
        Align.jdec (N - n) jd)
    (hc : ncBD n N L O = true)
    (hcA : ncBD n N (labDiffD (markArr (N - n) jd.1) L O) O = false)
    (hcU : ncBD n (n + jd.2.1.length)
      (labJUD jd.2.1.length (markArr (N - n) jd.1) jd.2.2.2 L O) O = false)
    {gs₄ : GensData} {d₄ : D.denote}
    (hval : GroupValid DV (n + (cellPosD n jd.2.1).length) gs₄ d₄)
    (hden : GensData.denote (n + (cellPosD n jd.2.1).length) gs₄ =
      (rebaseHom hS.hint.le (isInvariant_strSet hS.base_inv) (dv_cellPos_valid hJv hS.hint.le)
        (dv_cellPos_blocks hJv) (dv_cellPos_perm hS.base_inv hJv hK)).range)
    {s' : ℕ} {G₀ : Subgroup (Perm (Fin (n + (cellPosD n jd.2.1).length)))}
    (B : BackendBounds X DV (n + (cellPosD n jd.2.1).length) s' G₀) (hs' : gs₄.length ≤ s')
    (hG₀ : GensData.denote (n + (cellPosD n jd.2.1).length) gs₄ ≤ G₀) :
    RunsWithin X body
        (Main.jfallbackProg n (n + (cellPosD n jd.2.1).length, gs₄, d₄)
          ((labJUD jd.2.1.length (markArr (N - n) jd.1) jd.2.2.2 L O).getD (O.headD 0) []))
        (jfallbackModel X.O n (n + (cellPosD n jd.2.1).length, gs₄, d₄)
          ((labJUD jd.2.1.length (markArr (N - n) jd.1) jd.2.2.2 L O).getD (O.headD 0) []))
        (jfallbackCost (n + (cellPosD n jd.2.1).length)
          ((labJUD jd.2.1.length (markArr (N - n) jd.1) jd.2.2.2 L O).getD
            (O.headD 0) []).length B.Btr B.Bstab) ∧
      DOutcome DV n N w L gs d O
        (outD 5 (n + (cellPosD n jd.2.1).length, gs₄, d₄)
          (jfallbackModel X.O n (n + (cellPosD n jd.2.1).length, gs₄, d₄)
            ((labJUD jd.2.1.length (markArr (N - n) jd.1) jd.2.2.2 L O).getD
              (O.headD 0) [])).1
          (jfallbackModel X.O n (n + (cellPosD n jd.2.1).length, gs₄, d₄)
            ((labJUD jd.2.1.length (markArr (N - n) jd.1) jd.2.2.2 L O).getD
              (O.headD 0) [])).2
          (jfallbackModel X.O n (n + (cellPosD n jd.2.1).length, gs₄, d₄)
            ((labJUD jd.2.1.length (markArr (N - n) jd.1) jd.2.2.2 L O).getD
              (O.headD 0) [])).1
          (WinData.ofPoints (n + (cellPosD n jd.2.1).length) O) #[]) := by
  have hn := hS.hint.le
  have hbase := hS.base_inv
  have hstr := isInvariant_strSet hbase
  have hw := dv_cellPos_valid (n := n) hJv hn
  have hbs := dv_cellPos_blocks (N := N) (n := n) hJv
  have hGb := dv_cellPos_perm hbase hJv hK
  have hk : (cellPosD n jd.2.1).length = jd.2.1.length := dv_length_cellPos _ _
  have hnc := dv_nc_le hJv
  set N₄ := n + (cellPosD n jd.2.1).length with hN₄
  set LU := labJUD jd.2.1.length (markArr (N - n) jd.1) jd.2.2.2 L O with hLU
  set u₀ := O.headD 0 with hu₀def
  have hu₀ : u₀ ∈ O := by
    obtain ⟨a, rest, h⟩ := List.exists_cons_of_ne_nil hS.ne
    rw [hu₀def, h]
    exact List.mem_cons_self
  have hu₀N : u₀ < N := hS.owin.lt u₀ hu₀
  set cl := LU.getD u₀ [] with hcl
  have hclnd : cl.Nodup := by
    rw [hcl, hLU, dv_getD_labJU hS.nodup hu₀]
    exact nodup_jUnionData _ _ _ _
  have hcllt : ∀ c ∈ cl, c < jd.2.1.length := fun c hc => ((dv_mem_labJU hS hJv hu₀ c).1 hc).1
  -- the union labels are constant on `O`, as sets of cells below `|Λ|`
  have hconst : ∀ v ∈ O, ∀ c < jd.2.1.length, c ∈ LU.getD v [] ↔ c ∈ cl := by
    intro v hv c hc
    have h := congrArg (fun T => (⟨c, by omega⟩ : Fin (n + jd.2.1.length - n)) ∈ T)
      (DSetting.const hcU v hv u₀ hu₀)
    simpa only [SoJProg.mem_setOf, eq_iff_iff] using h
  -- `G₄` permutes the positions of the union cells
  have hHS : ∀ g ∈ GensData.denote N₄ gs₄, ∀ u : Fin N₄, u.val ∈ cl.map (n + ·) →
      (g u).val ∈ cl.map (n + ·) := by
    rw [hden]
    rintro _ ⟨g, rfl⟩ u hu
    obtain ⟨c, hc, hcu⟩ := List.mem_map.1 hu
    have hcl' := hcllt c hc
    rw [rebaseHom_ge hn hstr hw hbs hGb g (show n ≤ u.val by omega)]
    refine List.mem_map.2 ⟨_, ?_, rfl⟩
    have hgc := (dv_labJU_equivar hS hJv hK g.2 hu₀ hu₀N _).2 ⟨c, hc, rfl⟩
    have hgu₀ : (g.1 ⟨u₀, hu₀N⟩).val ∈ O := hS.oinv g.1 g.2 ⟨u₀, hu₀N⟩ hu₀
    rw [show u.val - n = c by omega]
    refine (hconst _ hgu₀ _ ?_).1 hgc
    exact ((dv_mem_labJU hS hJv hgu₀ _).1 hgc).1
  have hinv4 : IsInvariant (GensData.denote N₄ gs₄) (baseSet n N₄) := by
    rw [hden]; exact (rebase_invariant hn hstr hw hbs hGb).1
  have hO3 : MeetsContractOn DV stabOps X.O := hO
  obtain ⟨hrun, hN5, hv5, hden5, hrv5, hcov5, hcard5⟩ := RunsWithin.jfallbackProg (body := body)
    hO3 hPre hval hinv4 hclnd (fun c hc => by have := hcllt c hc; omega) hHS B hs' hG₀
  refine ⟨hrun, ?_⟩
  set M5 := jfallbackModel X.O n (N₄, gs₄, d₄) cl with hM5
  have e1 : M5.1 = (N₄, M5.1.2.1, M5.1.2.2) := Prod.ext hN5 rfl
  obtain ⟨hwv, hinv', -, hfa', hiso'⟩ := dv_rebase_facts hn hbase hw hbs hGb hS.kfaith hden
    hS.win_lt hS.nodup hS.oinv
  have hRP : GensData.denote N₄ M5.1.2.1 ≤ GensData.denote N₄ gs₄ := by
    rw [hden5]; exact pointwiseStab_le _ _
  unfold outD
  rw [e1]
  refine DOutcome.johnFallback (u := cl.length) (by omega) hval hfa' hinv' hiso' hv5 hRP hrv5
    hcov5 hcard5 ?_ (fun g hg => hinv' g (hRP hg)) ?_
  · have hcllen : cl.length ≤ jd.2.1.length := by
      rw [hcl, hLU, dv_getD_labJU hS.nodup hu₀]
      unfold jUnionData
      exact (List.length_filter_le _ _).trans (by simp)
    omega
  · -- the orbits of `R` in `O` have at most `|O|/2` points
    intro O' hO'nd hO' horb
    set Ofin := winFinset N (WinData.ofPoints N O) with hOfin
    have hOinv : Invariant ↥(GensData.denote N gs) Ofin := by
      intro g u hu
      rw [mem_winFinset] at hu ⊢
      exact hS.oinv g.1 g.2 u hu
    have hT : Transitive ↥(GensData.denote N gs) Ofin := by
      intro u hu v hv
      rw [mem_winFinset] at hu hv
      obtain ⟨g, hg, e⟩ := hS.otrans u hu v hv
      exact ⟨⟨g, hg⟩, e⟩
    have hh : IsHint (baseHom (GensData.denote N gs) n hbase) Ofin (labOf n N L) :=
      (hS.hintK hc).isHint hS.kvalid.1 hS.owin hS.oinv
    have hA := dv_labDiff_const hS hcA
    have hU := dv_labJU_const hS hJv hcU
    have hu₀' : (⟨u₀, hu₀N⟩ : Fin N) ∈ Ofin := mem_winFinset.2 hu₀
    -- the elements of `K` whose re-basing lies in `R`
    set Kc : Subgroup ↥(GensData.denote N gs) :=
      (GensData.denote N₄ M5.1.2.1).comap (rebaseHom hn hstr hw hbs hGb) with hKc
    have hfix : ∀ g ∈ Kc, ∀ a ∈ jUnion (Align.jdec (N - n) jd) (labOf n N L ⟨u₀, hu₀N⟩),
        baseHom (GensData.denote N gs) n hbase g • a = a := by
      intro g hg a ha
      rw [mr_labOf_eq_setOf] at ha
      obtain ⟨c, hc, rfl⟩ := dv_jUnion_cell hJv ha
      have hcu : c ∈ cl := (dv_mem_labJU hS hJv hu₀ c).2 ⟨hc, ha⟩
      have hgR : rebaseHom hn hstr hw hbs hGb g ∈ GensData.denote N₄ M5.1.2.1 := hg
      rw [hden5] at hgR
      have hfx := (mem_pointwiseStab.1 hgR).2 ⟨n + c, by omega⟩
        (show n + c ∈ cl.map (n + ·) from List.mem_map.2 ⟨c, hcu, rfl⟩)
      have hv := congrArg Fin.val hfx
      rw [rebaseHom_ge hn hstr hw hbs hGb g (show n ≤ n + c by omega)] at hv
      simp only [Nat.add_sub_cancel_left] at hv
      obtain ⟨-, hbme⟩ := dv_blockMap_cell hbase hJv hn hK g.2 hc
      have hbm : blockMap N (cellPosD n jd.2.1) g.1 c = c := by omega
      rw [hbm] at hbme
      exact hbme.symm
    -- the part as a set of positions of degree `N`
    set O'f : Finset (Fin N) := SoJProg.setOf N O' with hO'f
    have hO'sub : O'f ⊆ Ofin := by
      intro v hv
      rw [hO'f, SoJProg.mem_setOf] at hv
      exact mem_winFinset.2 (hO' _ hv)
    have hO'orb : ∀ v ∈ O'f, ∀ v' ∈ O'f, ∃ g ∈ Kc, g • v = v' := by
      intro v hv v' hv'
      rw [hO'f, SoJProg.mem_setOf] at hv hv'
      obtain ⟨hvN, hv'N, r, hr, hrv⟩ := horb _ hv _ hv'
      obtain ⟨g, hg⟩ : r ∈ (rebaseHom hn hstr hw hbs hGb).range := by
        rw [← hden]; exact hRP hr
      refine ⟨g, show rebaseHom hn hstr hw hbs hGb g ∈ GensData.denote N₄ M5.1.2.1 by
        rw [hg]; exact hr, ?_⟩
      have hvn : v.val < n := hS.win_lt _ (hO' _ hv)
      apply Fin.ext
      have h1 := congrArg Fin.val hrv
      rw [← hg, rebaseHom_lt hn hstr hw hbs hGb g (show v.val < n from hvn)] at h1
      exact h1
    have := jfallback_half hJ hK hOinv hT hh hA hU hu₀' Kc hfix hO'sub hO'orb
    rwa [show O'f.card = O'.length from SoJProg.card_setOf hO'nd fun i hi =>
        hS.owin.lt i (hO' i hi),
      show Ofin.card = O.length from SoJProg.card_setOf hS.nodup fun i hi =>
        hS.owin.lt i hi] at this

end CJFallback

/-! ### Coloured Johnson structures: programs, models, costs -/

section CJProgs

variable {D : Ty} {rec : Ty × Ty} {var : Ty → Type}

/-- `cellPosD` as a program. -/
def cellPosProg {S : Signature} (n : var .nat) (cs : var (.list (.list .nat))) :
    Prog S rec var (.list (.list .nat)) :=
  mapList cs fun c => mapList c fun x => .op2 .add n x

/-- **The Johnson step**, when the labels outside `V₀` are constant on `O`. The group `G4` is
re-based onto the cells (`rebaseProg`, cell `c` at the position `n + c`). If the Johnson union
labels are not constant on `O`, they are re-based onto the cells (tag `4`; tag `6` if there are
more than `3m/4` cells); otherwise the Johnson fallback in `G4` at the first point of `O`
(tag `5`). -/
def johnStepProg (n N : var .nat) (K : var (Ty.group D)) (O : var (.list .nat))
    (L : var (.array (.list .nat))) (w : var Ty.win) (v0 : var (.array .bool))
    (cs : var (.list (.list .nat))) (fA : var (.array (.list .nat))) :
    Prog (groupSig D) rec var (deriveTy D) :=
  .bind (.op2 .sub N n) fun m =>
  .bind (.op1 .length cs) fun nc =>
  .bind (mapLabelsProg L O fun li => jUnionProg nc v0 fA li) fun LU =>
  .bind (.op2 .add n nc) fun nnc =>
  .bind (ncBProg n nnc LU O) fun cU =>
  .bind (cellPosProg n cs) fun cps => .bind (.op1 .snd K) fun kd =>
  .bind (.op1 .fst kd) fun gs => .bind (rebaseProg n N gs cps) fun G4 =>
  .bind (.op1 .fst G4) fun N4 => .bind (mkWindow N4 O) fun w4 =>
  .bind (.op0 .nil) fun nil =>
  .ite cU
    (.bind (leQProg nc m) fun b =>
      .ite b (outProg 4 G4 G4 nil G4 w4 LU) (outProg 6 K K nil K w L))
    (.bind (.caseList O (.op0 (.natLit 0)) fun u _ => .ret u) fun u₀ =>
      .bind (.op2 .arrayGet LU u₀) fun cl =>
      .bind (jfallbackProg n G4 cl) fun res =>
      .bind (.op1 .fst res) fun R => .bind (.op1 .snd res) fun reps =>
      .bind (.op0 .nil) fun e0 => .bind (.op1 .arrayOfList e0) fun em =>
      outProg 5 G4 R reps R w4 em)

/-- **A coloured Johnson structure** `e`: no hint when the labels are constant on `O`; M1 and
the block step on the labels outside `V₀` when those are not constant on `O`; otherwise the
Johnson step. -/
def deriveCJProg (n N : var .nat) (K : var (Ty.group D)) (O : var (.list .nat))
    (L : var (.array (.list .nat))) (e : var cjTy) : Prog (groupSig D) rec var (deriveTy D) :=
  .bind (ncBProg n N L O) fun c => .bind (mkWindow N O) fun w =>
  .ite c
    (.bind (.op1 .fst e) fun jd => .bind (.op1 .fst jd) fun V0 => .bind (.op1 .snd jd) fun r1 =>
      .bind (.op1 .fst r1) fun cs => .bind (.op1 .snd r1) fun r2 =>
      .bind (.op1 .snd r2) fun fA =>
      .bind (.op2 .sub N n) fun m => .bind (markProg m V0) fun v0 =>
      .bind (mapLabelsProg L O fun li =>
          filterList li fun j => .bind (.op2 .arrayGet v0 j) fun b => .op1 .not b) fun LA =>
      .bind (ncBProg n N LA O) fun cA =>
      .ite cA (m1ContProg n N K w LA) (johnStepProg n N K O L w v0 cs fA))
    (noHintProg K w)

end CJProgs

section CJModels

variable {D : Ty}

/-- The value of `johnStepProg`. -/
def johnStepD (Or : Oracle (groupSig D)) (n N : ℕ) (K : GroupData D.denote) (O : List ℕ)
    (L : LabelData) (jd : Align.JData) : DOut D :=
  cond (ncBD n (n + jd.2.1.length) (labJUD jd.2.1.length (markArr (N - n) jd.1) jd.2.2.2 L O) O)
    (cond (leQD jd.2.1.length (N - n))
      (outD 4 (rebaseModel Or n N (cellPosD n jd.2.1) K.2.1)
        (rebaseModel Or n N (cellPosD n jd.2.1) K.2.1) []
        (rebaseModel Or n N (cellPosD n jd.2.1) K.2.1)
        (WinData.ofPoints (rebaseModel Or n N (cellPosD n jd.2.1) K.2.1).1 O)
        (labJUD jd.2.1.length (markArr (N - n) jd.1) jd.2.2.2 L O))
      (outD 6 K K [] K (WinData.ofPoints N O) L))
    (outD 5 (rebaseModel Or n N (cellPosD n jd.2.1) K.2.1)
      (jfallbackModel Or n (rebaseModel Or n N (cellPosD n jd.2.1) K.2.1)
        ((labJUD jd.2.1.length (markArr (N - n) jd.1) jd.2.2.2 L O).getD (O.headD 0) [])).1
      (jfallbackModel Or n (rebaseModel Or n N (cellPosD n jd.2.1) K.2.1)
        ((labJUD jd.2.1.length (markArr (N - n) jd.1) jd.2.2.2 L O).getD (O.headD 0) [])).2
      (jfallbackModel Or n (rebaseModel Or n N (cellPosD n jd.2.1) K.2.1)
        ((labJUD jd.2.1.length (markArr (N - n) jd.1) jd.2.2.2 L O).getD (O.headD 0) [])).1
      (WinData.ofPoints (rebaseModel Or n N (cellPosD n jd.2.1) K.2.1).1 O) #[])

/-- The value of `deriveCJProg`. -/
def deriveCJModel (Or : Oracle (groupSig D)) (n N : ℕ) (K : GroupData D.denote) (O : List ℕ)
    (L : LabelData) (e : CJData) : DOut D :=
  cond (ncBD n N L O)
    (cond (ncBD n N (labDiffD (markArr (N - n) e.1.1) L O) O)
      (m1ContD Or n N (m1Model Or n N K (WinData.ofPoints N O)
        (labDiffD (markArr (N - n) e.1.1) L O)))
      (johnStepD Or n N K O L e.1))
    (noHintD K (WinData.ofPoints N O))

/-- The cost of `johnStepProg`: `p` points, a label array of size `Ls`, `s` generators, at
most `uB` union cells at a point, the fallback's charges `Bt`, `Bs` (at the degree of the group
re-based onto the cells) and the re-basing charge `Bgen₄`. -/
def johnStepCost (n N p Ls s uB Bt Bs Bgen₄ : ℕ) : ℕ :=
  (N - n) + (p * (jUnionCost (N - n) (N - n) (N - n) + 6) + Ls + 3) + ncBCost n N p (N - n) +
    ((N - n) * (4 * (N - n) + 5) + rebaseCost n N (N - n) (N - n) s Bgen₄ + 2 * N + 5 * p) +
    jfallbackCost N uB Bt Bs + 60

/-- The cost of `deriveCJProg`. -/
def deriveCJCost
    (n N p Ls s Borb Bgen s₁ sS Lt sH Bgen₂ Bge Bst Btr Bgt Bgen₃ Bgen₄ uB Bt Bs : ℕ) : ℕ :=
  2 * ncBCost n N p (N - n) + (2 * N + 5 * p + 7) + markCost (N - n) (N - n) +
    (p * ((N - n) * 6 + 9) + Ls + 3) +
    m1ContCost n N p s Borb Bgen s₁ sS Lt sH Bgen₂ Bge Bst Btr Bgt Bgen₃ +
    johnStepCost n N p Ls s uB Bt Bs Bgen₄ + 30

theorem ncBCost_mono {n N N' p Lb Lb' : ℕ} (hN : N ≤ N') (hL : Lb ≤ Lb') :
    ncBCost n N p Lb ≤ ncBCost n N' p Lb' := by
  unfold ncBCost baseWinCost ncCost ncPairCost interOCost SoJTree.setEqCost
  gcongr

theorem jUnionCost_mono {nc nc' t t' s s' : ℕ} (h1 : nc ≤ nc') (h2 : t ≤ t') (h3 : s ≤ s') :
    jUnionCost nc t s ≤ jUnionCost nc' t' s' := by
  unfold jUnionCost
  gcongr

theorem rebaseCost_mono {n N m m' k k' s s' B : ℕ} (hm : m ≤ m') (hk : k ≤ k')
    (hs : s ≤ s') :
    rebaseCost n N m k s B ≤ rebaseCost n N m' k' s' B := by
  unfold rebaseCost
  gcongr

theorem jfallbackCost_mono {N N' u u' Bt Bs : ℕ} (hN : N ≤ N') (hu : u ≤ u') :
    jfallbackCost N u Bt Bs ≤ jfallbackCost N' u' Bt Bs := by
  unfold jfallbackCost CertProg.kerACost
  have := Nat.factorial_le hu
  gcongr

end CJModels

/-! ### Coloured Johnson structures: the specs -/

section CJSpec

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b}
  {DV : ℕ → GensData → D.denote → Prop}
  {n N : ℕ} {gsG gs : GensData} {w : WinData} {L : LabelData} {d : D.denote} {O : List ℕ}

theorem RunsWithin.cellPosProg (n : ℕ) (cs : List (List ℕ)) {Lc : ℕ}
    (h : ∀ c ∈ cs, c.length ≤ Lc) :
    RunsWithin X body (Main.cellPosProg n cs) (cellPosD n cs) (cs.length * (4 * Lc + 5) + 2) := by
  have hm := RunsWithin.mapList_le (X := X) (body := body) (a' := .list .nat) (b' := .list .nat)
    (xs := cs) (c := 4 * Lc + 2) (F := fun c => c.map (n + ·))
    (f := fun c => mapList c fun x => Prog.op2 Prim.add n x) fun c hc =>
      (RunsWithin.mapList_le (c := 1) (F := (n + ·)) fun x _ => RunsWithin.prim _ _).mono
        (by have := h c hc; omega)
  refine hm.mono ?_
  have : cs.length * (4 * Lc + 2 + 3) = cs.length * (4 * Lc + 5) := by ring
  omega

/-- **The Johnson parameter's binomial bound**: a Johnson embedding in a type of `k` points
has `C(|Λ|, s) ≤ k` (its points are the `s`-subsets of the cells). -/
theorem dv_johnson_choose_le {α : Type*} [Fintype α] [DecidableEq α] {V : Finset α} {t : ℕ}
    {J : JEmb α} (hJ : IsJohnson V t J) : J.Λ.card.choose J.s ≤ Fintype.card α := by
  rw [← Finset.card_powersetCard]
  calc (J.Λ.powersetCard J.s).card ≤ (J.V0.image J.f).card := by
        refine Finset.card_le_card fun T hT => ?_
        obtain ⟨v, hv, rfl⟩ := hJ.surj T hT
        exact Finset.mem_image_of_mem _ hv
    _ ≤ J.V0.card := Finset.card_image_le
    _ ≤ Fintype.card α := Finset.card_le_univ _

/-- The decoded cells of valid Johnson data are its `nc` cells. -/
theorem dv_jdec_card {m : ℕ} {jd : Align.JData} (hJv : Align.JValid m jd) :
    (Align.jdec m jd).Λ.card = jd.2.1.length := by
  have h := congrArg Multiset.card (Align.famOf_val_card hJv)
  rw [Align.jdec_Λ]
  simpa using h

/-- **Valid Johnson data on `m` points** with `nc` cells and parameter `s`: `C(nc, s) ≤ m`. -/
theorem dv_cj_choose_le {m t : ℕ} {V : Finset (Fin m)} {jd : Align.JData}
    (hJv : Align.JValid m jd) (hJ : IsJohnson V t (Align.jdec m jd)) :
    jd.2.1.length.choose jd.2.2.1 ≤ m := by
  have h := dv_johnson_choose_le hJ
  rwa [dv_jdec_card hJv, Align.jdec_s, Fintype.card_fin] at h

/-- **The Johnson step.** When the labels, but not those outside `V₀`, are not constant on
`O`: the Johnson union re-based onto the cells (`johnUnion`), the Johnson fallback in the group
re-based onto the cells (`johnFallback`, at most `u!` cosets for `u ≤ uB` union cells), or
`stuck` when there are more than `3m/4` cells. `BackendBounds` is needed at the degree of the
group re-based onto the cells, for that group. -/
theorem RunsWithin.johnStepProg (hO : MeetsContractOn DV deriveOps X.O)
    (hPre : ∀ op x, deriveOps op → GroupPre DV op x → X.Pre op x)
    (hS : DSetting DV n N gsG w L gs d O) {jd : Align.JData} (hJv : Align.JValid (N - n) jd)
    {V : Finset (Fin (N - n))} {t : ℕ} (hJ : IsJohnson V t (Align.jdec (N - n) jd))
    (hK : ∀ g : ↥(GensData.denote N gs),
      baseHom (GensData.denote N gs) n hS.base_inv g • Align.jdec (N - n) jd =
        Align.jdec (N - n) jd)
    (hc : ncBD n N L O = true)
    (hcA : ncBD n N (labDiffD (markArr (N - n) jd.1) L O) O = false)
    {uB Bgen₄ : ℕ}
    (hB4 : X.B.call GroupOp.generate (n + (cellPosD n jd.2.1).length,
      rebaseGens n N (cellPosD n jd.2.1) gs) (rebaseModel X.O n N (cellPosD n jd.2.1) gs) ≤
        Bgen₄)
    (hu : ((labJUD jd.2.1.length (markArr (N - n) jd.1) jd.2.2.2 L O).getD (O.headD 0)
      []).length ≤ uB)
    {s' : ℕ} {G₀ : Subgroup (Perm (Fin (n + (cellPosD n jd.2.1).length)))}
    (B : BackendBounds X DV (n + (cellPosD n jd.2.1).length) s' G₀)
    (hs' : (rebaseModel X.O n N (cellPosD n jd.2.1) gs).2.1.length ≤ s')
    (hG₀ : GensData.denote (n + (cellPosD n jd.2.1).length)
      (rebaseModel X.O n N (cellPosD n jd.2.1) gs).2.1 ≤ G₀) :
    RunsWithin X body
        (Main.johnStepProg n N (N, gs, d) O L (WinData.ofPoints N O) (markArr (N - n) jd.1)
          jd.2.1 jd.2.2.2)
        (johnStepD X.O n N (N, gs, d) O L jd)
        (johnStepCost n N O.length L.size gs.length uB B.Btr B.Bstab Bgen₄) ∧
      DOutcome DV n N w L gs d O (johnStepD X.O n N (N, gs, d) O L jd) := by
  have hn := hS.hint.le
  have hbase := hS.base_inv
  have hnc := dv_nc_le hJv
  have hk : (cellPosD n jd.2.1).length = jd.2.1.length := dv_length_cellPos _ _
  have hO' : MeetsContractOn DV rebaseOps X.O := fun op x h => hO op x (by
    rw [show op = .generate from h]; simp [deriveOps])
  have hPre' : ∀ op x, rebaseOps op → GroupPre DV op x → X.Pre op x := fun op x h =>
    hPre op x (by rw [show op = .generate from h]; simp [deriveOps])
  have hw := dv_cellPos_valid (n := n) hJv hn
  have hbs := dv_cellPos_blocks (N := N) (n := n) hJv
  have hGb := dv_cellPos_perm hbase hJv hK
  obtain ⟨hrun4, hdeg4, hval4, hden4⟩ := RunsWithin.rebaseProg (body := body) hO' hPre' hn hbase
    hw hbs hGb hS.kvalid.1 hB4
  have e4 : rebaseModel X.O n N (cellPosD n jd.2.1) gs = (n + (cellPosD n jd.2.1).length,
      (rebaseModel X.O n N (cellPosD n jd.2.1) gs).2.1,
      (rebaseModel X.O n N (cellPosD n jd.2.1) gs).2.2) := Prod.ext hdeg4 rfl
  have hrc := rebaseCost_mono (n := n) (N := N) (s := gs.length) (B := Bgen₄)
    (show (cellPosD n jd.2.1).flatten.length ≤ N - n by
      rw [dv_flatten_cellPos, List.length_map]
      exact mf_length_le_of_nodup (dv_cells_flatten_nodup hJv) fun a ha => by
        obtain ⟨c, hc, hac⟩ := List.mem_flatten.1 ha
        exact hJv.cell_lt c hc a hac)
    (show (cellPosD n jd.2.1).length ≤ N - n by rw [hk]; exact hnc) le_rfl
  rw [e4] at hrun4
  have hcp := RunsWithin.cellPosProg (X := X) (body := body) n jd.2.1 (Lc := N - n)
    fun c hc => mf_length_le_of_nodup (hJv.cell_nodup c hc) (hJv.cell_lt c hc)
  have hcpc : jd.2.1.length * (4 * (N - n) + 5) ≤ (N - n) * (4 * (N - n) + 5) :=
    Nat.mul_le_mul_right _ hnc
  have hrLU : RunsWithin X body
      (mapLabelsProg L O fun li => jUnionProg jd.2.1.length (markArr (N - n) jd.1) jd.2.2.2 li)
      (labJUD jd.2.1.length (markArr (N - n) jd.1) jd.2.2.2 L O)
      (O.length * (jUnionCost jd.2.1.length (N - n) jd.2.1.length + 6) + L.size + 3) := by
    refine RunsWithin.mapLabelsProg
      (F := jUnionData jd.2.1.length (markArr (N - n) jd.1) jd.2.2.2) fun i hi => ?_
    refine (RunsWithin.jUnionProg _ _ jd.2.2.2 (L.getD i [])
      (s := jd.2.1.length) fun j _ => dv_fl_len hJv j).mono ?_
    exact jUnionCost_mono le_rfl (hS.lab_len i hi) le_rfl
  have hLUlen : ∀ i ∈ O, ((labJUD jd.2.1.length (markArr (N - n) jd.1) jd.2.2.2 L O).getD i
      []).length ≤ jd.2.1.length := by
    intro i hi
    rw [dv_getD_labJU hS.nodup hi]
    refine mf_length_le_of_nodup (nodup_jUnionData _ _ _ _) fun c hc => ?_
    exact ((mem_jUnionData _ _ _ _ c).1 hc).1
  have hncU := RunsWithin.ncBProg (X := X) (body := body) n (n + jd.2.1.length)
    (labJUD jd.2.1.length (markArr (N - n) jd.1) jd.2.2.2 L O) O hLUlen
  have hncUc : ncBCost n (n + jd.2.1.length) O.length jd.2.1.length ≤
      ncBCost n N O.length (N - n) :=
    ncBCost_mono (by omega) hnc
  have hLUc : O.length * (jUnionCost jd.2.1.length (N - n) jd.2.1.length + 6) ≤
      O.length * (jUnionCost (N - n) (N - n) (N - n) + 6) := by
    have := jUnionCost_mono (nc := jd.2.1.length) (nc' := N - n) (t := N - n) (t' := N - n)
      (s := jd.2.1.length) (s' := N - n) hnc le_rfl hnc
    gcongr
  have hmk := RunsWithin.mkWindow (X := X) (body := body) (n + (cellPosD n jd.2.1).length) O
  cases hcU : ncBD n (n + jd.2.1.length)
      (labJUD jd.2.1.length (markArr (N - n) jd.1) jd.2.2.2 L O) O
  · -- the fallback
    have hO3 : MeetsContractOn DV stabOps X.O := fun op x h => hO op x (deriveOps_of_stab h)
    have hPre3 : ∀ op x, stabOps op → GroupPre DV op x → X.Pre op x :=
      fun op x h => hPre op x (deriveOps_of_stab h)
    obtain ⟨hrunF, houtF⟩ := dv_jfallback (body := body) (w := w) hO3 hPre3 hS hJv hJ hK hc
      hcA hcU hval4 hden4 B hs' hG₀
    have hm : johnStepD X.O n N (N, gs, d) O L jd = outD 5
        (rebaseModel X.O n N (cellPosD n jd.2.1) gs)
        (jfallbackModel X.O n (rebaseModel X.O n N (cellPosD n jd.2.1) gs)
          ((labJUD jd.2.1.length (markArr (N - n) jd.1) jd.2.2.2 L O).getD (O.headD 0) [])).1
        (jfallbackModel X.O n (rebaseModel X.O n N (cellPosD n jd.2.1) gs)
          ((labJUD jd.2.1.length (markArr (N - n) jd.1) jd.2.2.2 L O).getD (O.headD 0) [])).2
        (jfallbackModel X.O n (rebaseModel X.O n N (cellPosD n jd.2.1) gs)
          ((labJUD jd.2.1.length (markArr (N - n) jd.1) jd.2.2.2 L O).getD (O.headD 0) [])).1
        (WinData.ofPoints (rebaseModel X.O n N (cellPosD n jd.2.1) gs).1 O) #[] := by
      simp only [johnStepD, hcU, Bool.cond_false]
    rw [hm, e4]
    refine ⟨?_, houtF⟩
    rw [hcU] at hncU
    have hhead : RunsWithin X body
        (Prog.caseList (a := .nat) O (.op0 (.natLit 0)) fun u _ => .ret u) (O.headD 0) 2 := by
      cases O with
      | nil => exact (RunsWithin.caseList_nil (RunsWithin.prim _ _)).mono (by simp [Prim.cost])
      | cons u rest => exact (RunsWithin.caseList_cons (RunsWithin.ret _)).mono (by omega)
    have hFc := jfallbackCost_mono (Bt := B.Btr) (Bs := B.Bstab)
      (show n + (cellPosD n jd.2.1).length ≤ N by rw [hk]; omega) hu
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      simp only [Prim.eval]
      run_step hrLU
      run_step (RunsWithin.prim _ _)
      simp only [Prim.eval]
      run_step hncU
      run_step hcp
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      simp only [Prim.eval]
      run_step hrun4
      run_step (RunsWithin.prim _ _)
      simp only [Prim.eval]
      run_step hmk
      run_step (RunsWithin.prim _ _)
      apply RunsWithin.ite_false
      run_step hhead
      run_step (RunsWithin.prim _ _)
      simp only [Prim.eval]
      run_step hrunF
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      exact RunsWithin.outProg _ _ _ _ _ _ _
    case hc =>
      simp only [Prim.cost, johnStepCost, Args.head_cons, Prim.eval, List.length_nil]
      generalize jfallbackCost (n + (cellPosD n jd.2.1).length)
        ((labJUD jd.2.1.length (markArr (N - n) jd.1) jd.2.2.2 L O).getD (O.headD 0) []).length
        B.Btr B.Bstab = F₁ at hFc ⊢
      generalize jfallbackCost N uB B.Btr B.Bstab = F₂ at hFc ⊢
      clear hrunF houtF hrun4 hmk hhead e4 hu hcU hcA hc hrLU hncU hcp hS hK hJ hJv hden4 hval4
        hB4 hs' hG₀ hO hPre hO' hPre' hO3 hPre3 hw hbs hGb hbase hm
      omega
  · rw [hcU] at hncU
    have hleq := RunsWithin.leQProg (X := X) (body := body) jd.2.1.length (N - n)
    cases hq : leQD jd.2.1.length (N - n)
    · -- too many cells: stuck
      have hm : johnStepD X.O n N (N, gs, d) O L jd = outD 6 (N, gs, d) (N, gs, d) []
          (N, gs, d) (WinData.ofPoints N O) L := by
        simp only [johnStepD, hcU, hq, Bool.cond_true, Bool.cond_false]
      rw [hm]
      refine ⟨?_, .stuck _ rfl⟩
      rw [hq] at hleq
      apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        simp only [Prim.eval]
        run_step hrLU
        run_step (RunsWithin.prim _ _)
        simp only [Prim.eval]
        run_step hncU
        run_step hcp
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        simp only [Prim.eval]
        run_step hrun4
        run_step (RunsWithin.prim _ _)
        simp only [Prim.eval]
        run_step hmk
        run_step (RunsWithin.prim _ _)
        apply RunsWithin.ite_true
        run_step hleq
        exact RunsWithin.ite_false (RunsWithin.outProg _ _ _ _ _ _ _)
      case hc =>
        simp only [Prim.cost, johnStepCost, Args.head_cons]
        clear hrun4 hmk e4 hu hcU hcA hc hrLU hncU hcp hS hK hJ hJv hden4 hval4 hB4 hs' hG₀
          hO hPre hO' hPre' hw hbs hGb hbase hm hleq hq
        omega
    · -- the Johnson union, re-based onto the cells
      have hch4 := dv_cells_child (X := X) hO' hS hJv hK hcU
      have hm : johnStepD X.O n N (N, gs, d) O L jd =
          outD 4 (rebaseModel X.O n N (cellPosD n jd.2.1) gs)
            (rebaseModel X.O n N (cellPosD n jd.2.1) gs) []
            (rebaseModel X.O n N (cellPosD n jd.2.1) gs)
            (WinData.ofPoints (rebaseModel X.O n N (cellPosD n jd.2.1) gs).1 O)
            (labJUD jd.2.1.length (markArr (N - n) jd.1) jd.2.2.2 L O) := by
        simp only [johnStepD, hcU, hq, Bool.cond_true]
      rw [hm, e4]
      refine ⟨?_, DOutcome.johnUnion hch4 rfl ?_ ?_⟩
      · rw [hq] at hleq
        apply RunsWithin.mono
        case h =>
          run_step (RunsWithin.prim _ _)
          run_step (RunsWithin.prim _ _)
          simp only [Prim.eval]
          run_step hrLU
          run_step (RunsWithin.prim _ _)
          simp only [Prim.eval]
          run_step hncU
          run_step hcp
          run_step (RunsWithin.prim _ _)
          run_step (RunsWithin.prim _ _)
          simp only [Prim.eval]
          run_step hrun4
          run_step (RunsWithin.prim _ _)
          simp only [Prim.eval]
          run_step hmk
          run_step (RunsWithin.prim _ _)
          apply RunsWithin.ite_true
          run_step hleq
          exact RunsWithin.ite_true (RunsWithin.outProg _ _ _ _ _ _ _)
        case hc =>
          simp only [Prim.cost, johnStepCost, Args.head_cons]
          clear hrun4 hmk e4 hu hcU hcA hc hrLU hncU hcp hS hK hJ hJv hden4 hval4 hB4 hs' hG₀
            hO hPre hO' hPre' hw hbs hGb hbase hm hleq hq hch4
          omega
      · have := leQD_iff.1 hq
        omega
      · have h2 : 2 ≤ jd.2.2.1 := hJ.two_le
        have e : n + (cellPosD n jd.2.1).length - n = jd.2.1.length := by omega
        refine ⟨jd.2.2.1, ?_, ?_, h2, ?_⟩
        · exact labLen_labJUD_le hS.nodup (by omega)
            fun j hj => le_of_eq (hJv.f_len j ((getB_markArr _ _ _).1 hj).2)
        · rw [e]
          exact dv_cj_choose_le hJv hJ
        · rw [e, ← dv_jdec_card hJv]
          exact hJ.le_half

end CJSpec

/-! ### Coloured Johnson structures: the program -/

section CJMain

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b}
  {DV : ℕ → GensData → D.denote → Prop}
  {n N : ℕ} {gsG gs : GensData} {w : WinData} {L : LabelData} {d : D.denote} {O : List ℕ}

/-- **A coloured Johnson structure.** For `K` preserving the coloured Johnson structure `e`
(valid data, a Johnson embedding): no hint (`noHint`); M1 and the block step on the labels
outside `V₀` (`inter`, `blockLab`, `blockStab`, `stuck`); the Johnson union re-based onto the
cells (`johnUnion`); the Johnson fallback (`johnFallback`); or `stuck` with more than `3m/4`
cells. `deriveCJ_ne_stuck` excludes `stuck`. -/
theorem RunsWithin.deriveCJProg (hO : MeetsContractOn DV deriveOps X.O)
    (hPre : ∀ op x, deriveOps op → GroupPre DV op x → X.Pre op x)
    (hS : DSetting DV n N gsG w L gs d O) {e : CJData} (hJv : Align.JValid (N - n) e.1)
    {V : Finset (Fin (N - n))} {t : ℕ} (hJ : IsJohnson V t (Align.jdec (N - n) e.1))
    (hK : ∀ g : ↥(GensData.denote N gs),
      baseHom (GensData.denote N gs) n hS.base_inv g • cjdec (N - n) e = cjdec (N - n) e)
    {Borb Bgen s₁ Bgen₂ Bge Bst Btr Bgt sS Lt sH Bgen₃ Bgen₄ uB : ℕ}
    (hB : M1Charges X n N gs d (WinData.ofPoints N O) (labDiffD (markArr (N - n) e.1.1) L O)
      Borb Bgen)
    (hB' : BlkCharges X n (m1Model X.O n N (N, gs, d) (WinData.ofPoints N O)
        (labDiffD (markArr (N - n) e.1.1) L O)).1.1
      (m1Model X.O n N (N, gs, d) (WinData.ofPoints N O)
        (labDiffD (markArr (N - n) e.1.1) L O)).1.2.1
      s₁ Bgen₂ Bge Bst Btr Bgt sS Lt sH Bgen₃)
    (hB4 : X.B.call GroupOp.generate (n + (cellPosD n e.1.2.1).length,
      rebaseGens n N (cellPosD n e.1.2.1) gs) (rebaseModel X.O n N (cellPosD n e.1.2.1) gs) ≤
        Bgen₄)
    (hu : ((labJUD e.1.2.1.length (markArr (N - n) e.1.1) e.1.2.2.2 L O).getD (O.headD 0)
      []).length ≤ uB)
    {s' : ℕ} {G₀ : Subgroup (Perm (Fin (n + (cellPosD n e.1.2.1).length)))}
    (B : BackendBounds X DV (n + (cellPosD n e.1.2.1).length) s' G₀)
    (hs' : (rebaseModel X.O n N (cellPosD n e.1.2.1) gs).2.1.length ≤ s')
    (hG₀ : GensData.denote (n + (cellPosD n e.1.2.1).length)
      (rebaseModel X.O n N (cellPosD n e.1.2.1) gs).2.1 ≤ G₀) :
    RunsWithin X body (Main.deriveCJProg n N (N, gs, d) O L e)
        (deriveCJModel X.O n N (N, gs, d) O L e)
        (deriveCJCost n N O.length L.size gs.length Borb Bgen s₁ sS Lt sH Bgen₂ Bge Bst Btr Bgt
          Bgen₃ Bgen₄ uB B.Btr B.Bstab) ∧
      DOutcome DV n N w L gs d O (deriveCJModel X.O n N (N, gs, d) O L e) := by
  have hKJ : ∀ g : ↥(GensData.denote N gs),
      baseHom (GensData.denote N gs) n hS.base_inv g • Align.jdec (N - n) e.1 =
        Align.jdec (N - n) e.1 := fun g => ((cj_smul_eq_iff' _ _ _).1 (hK g)).1
  have hnc := RunsWithin.ncBProg (X := X) (body := body) n N L O hS.lab_len
  have hmk := RunsWithin.mkWindow (X := X) (body := body) N O
  cases hc : ncBD n N L O
  · have hm : deriveCJModel X.O n N (N, gs, d) O L e =
        noHintD (N, gs, d) (WinData.ofPoints N O) := by
      simp [deriveCJModel, hc]
    rw [hm]
    refine ⟨?_, .noHint (DSetting.const hc) (hS.half hc)⟩
    rw [hc] at hnc
    apply RunsWithin.mono
    case h =>
      run_step hnc
      run_step hmk
      exact RunsWithin.ite_false (RunsWithin.noHintProg _ _)
    case hc => simp only [deriveCJCost]; omega
  rw [hc] at hnc
  have hV0 : e.1.1.length ≤ N - n := mf_length_le_of_nodup hJv.v0_nodup hJv.v0_lt
  have hmark := RunsWithin.markProg (X := X) (body := body) (N - n) e.1.1
  have hmarkc : markCost (N - n) e.1.1.length ≤ markCost (N - n) (N - n) := by
    unfold markCost
    omega
  have hLA : RunsWithin X body
      (mapLabelsProg L O fun li => Toolkit.filterList li fun j =>
        Prog.bind (Prog.op2 Prim.arrayGet (markArr (N - n) e.1.1) j) fun b => Prog.op1 Prim.not b)
      (labDiffD (markArr (N - n) e.1.1) L O) (O.length * ((N - n) * 6 + 9) + L.size + 3) := by
    refine (RunsWithin.mapLabelsProg (c := (N - n) * 6 + 3)
      (F := fun l => l.filter fun j => !getB (markArr (N - n) e.1.1) j) fun i hi => ?_).mono
      (le_of_eq (by ring))
    refine (RunsWithin.filterList (c := 2) fun j _ => ?_).mono ?_
    · exact RunsWithin.bind_le (RunsWithin.prim _ _) (RunsWithin.prim _ _) (by simp [Prim.cost])
    · have := hS.lab_len i hi
      have : (L.getD i []).length * (2 + 4) ≤ (N - n) * 6 := Nat.mul_le_mul this le_rfl
      omega
  have hLAlen : ∀ i ∈ O, ((labDiffD (markArr (N - n) e.1.1) L O).getD i []).length ≤ N - n := by
    intro i hi
    rw [dv_getD_labDiff hS.nodup hi]
    exact (List.length_filter_le _ _).trans (hS.lab_len i hi)
  have hncA := RunsWithin.ncBProg (X := X) (body := body) n N
    (labDiffD (markArr (N - n) e.1.1) L O) O hLAlen
  cases hcA : ncBD n N (labDiffD (markArr (N - n) e.1.1) L O) O
  · obtain ⟨hrun, hout⟩ := RunsWithin.johnStepProg (body := body) (w := w) hO hPre hS hJv hJ hKJ
      hc hcA hB4 hu B hs' hG₀
    have hm : deriveCJModel X.O n N (N, gs, d) O L e = johnStepD X.O n N (N, gs, d) O L e.1 := by
      simp [deriveCJModel, hc, hcA]
    rw [hm]
    refine ⟨?_, hout⟩
    rw [hcA] at hncA
    apply RunsWithin.mono
    case h =>
      run_step hnc
      run_step hmk
      apply RunsWithin.ite_true
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      simp only [Prim.eval]
      run_step hmark
      run_step hLA
      run_step hncA
      exact RunsWithin.ite_false hrun
    case hc =>
      simp only [Prim.cost, deriveCJCost]
      omega
  · obtain ⟨hrun, hout⟩ := RunsWithin.m1ContProg (body := body) (w := w) (L := L) hO hPre
      hS.kvalid hS.owin hS.oinv hS.kfaith hS.otrans (dv_labDiff_hint hS hKJ hcA) hS.ne
      (labLen_labDiffD_le hS.nodup _ L) hB hB'
    have hm : deriveCJModel X.O n N (N, gs, d) O L e = m1ContD X.O n N (m1Model X.O n N (N, gs, d)
        (WinData.ofPoints N O) (labDiffD (markArr (N - n) e.1.1) L O)) := by
      simp [deriveCJModel, hc, hcA]
    rw [hm]
    refine ⟨?_, hout⟩
    rw [hcA] at hncA
    apply RunsWithin.mono
    case h =>
      run_step hnc
      run_step hmk
      apply RunsWithin.ite_true
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      simp only [Prim.eval]
      run_step hmark
      run_step hLA
      run_step hncA
      exact RunsWithin.ite_true hrun
    case hc =>
      simp only [Prim.cost, deriveCJCost]
      omega

end CJMain

/-! ### The dispatch on the structure -/

section Dispatch

variable {D : Ty} {rec : Ty × Ty} {var : Ty → Type}

/-- The structure on the base: a tag (`2` for a coloured Johnson structure, any other tag for no
structure or a colored partition, which the program does not read) and coloured Johnson
data. -/
abbrev stTy : Ty := .prod .nat cjTy

/-- **The derived hint.** For the reduced group `K`, a `K`-orbit `O` of the window, the labels
`L` of the parent hint, and the structure `st` that `K` preserves. -/
def deriveProg (n N : var .nat) (K : var (Ty.group D)) (O : var (.list .nat))
    (L : var (.array (.list .nat))) (st : var stTy) : Prog (groupSig D) rec var (deriveTy D) :=
  .bind (.op1 .fst st) fun tag => .bind (.op1 .snd st) fun e =>
  .bind (.op0 (.natLit 2)) fun two => .bind (.op2 .natEq tag two) fun isJ =>
  .ite isJ (deriveCJProg n N K O L e) (deriveFreeProg n N K O L)

end Dispatch

section DispatchSpec

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b}
  {DV : ℕ → GensData → D.denote → Prop}
  {n N : ℕ} {gsG gs : GensData} {w : WinData} {L : LabelData} {d : D.denote} {O : List ℕ}

/-- The value of `deriveProg`. -/
def deriveModel (Or : Oracle (groupSig D)) (n N : ℕ) (K : GroupData D.denote) (O : List ℕ)
    (L : LabelData) (st : ℕ × CJData) : DOut D :=
  cond (st.1 == 2) (deriveCJModel Or n N K O L st.2) (deriveFreeModel Or n N K O L)

/-- **`deriveProg` without a coloured Johnson structure** (tag `≠ 2`): `RunsWithin.deriveFreeProg`
plus the dispatch. -/
theorem RunsWithin.deriveProg_free (hO : MeetsContractOn DV deriveOps X.O)
    (hPre : ∀ op x, deriveOps op → GroupPre DV op x → X.Pre op x)
    (hS : DSetting DV n N gsG w L gs d O) {st : ℕ × CJData} (hst : st.1 ≠ 2)
    {Borb Bgen s₁ Bgen₂ Bge Bst Btr Bgt sS Lt sH Bgen₃ : ℕ}
    (hB : M1Charges X n N gs d (WinData.ofPoints N O) L Borb Bgen)
    (hB' : BlkCharges X n (m1Model X.O n N (N, gs, d) (WinData.ofPoints N O) L).1.1
      (m1Model X.O n N (N, gs, d) (WinData.ofPoints N O) L).1.2.1
      s₁ Bgen₂ Bge Bst Btr Bgt sS Lt sH Bgen₃) :
    RunsWithin X body (Main.deriveProg n N (N, gs, d) O L st)
        (deriveModel X.O n N (N, gs, d) O L st)
        (deriveFreeCost n N O.length gs.length Borb Bgen s₁ sS Lt sH Bgen₂ Bge Bst Btr Bgt
          Bgen₃ + 5) ∧
      DOutcome DV n N w L gs d O (deriveModel X.O n N (N, gs, d) O L st) := by
  obtain ⟨hrun, hout⟩ := RunsWithin.deriveFreeProg (body := body) hO hPre hS hB hB'
  have he : (st.1 == 2) = false := by simpa using hst
  have hm : deriveModel X.O n N (N, gs, d) O L st = deriveFreeModel X.O n N (N, gs, d) O L := by
    simp only [deriveModel, he, Bool.cond_false]
  rw [hm]
  refine ⟨?_, hout⟩
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    simp only [Prim.eval, he]
    exact RunsWithin.ite_false hrun
  case hc => simp only [Prim.cost]; omega

/-- **`deriveProg` with a coloured Johnson structure** (tag `2`): `RunsWithin.deriveCJProg` plus
the dispatch. -/
theorem RunsWithin.deriveProg_cj (hO : MeetsContractOn DV deriveOps X.O)
    (hPre : ∀ op x, deriveOps op → GroupPre DV op x → X.Pre op x)
    (hS : DSetting DV n N gsG w L gs d O) {st : ℕ × CJData} (hst : st.1 = 2)
    (hJv : Align.JValid (N - n) st.2.1) {V : Finset (Fin (N - n))} {t : ℕ}
    (hJ : IsJohnson V t (Align.jdec (N - n) st.2.1))
    (hK : ∀ g : ↥(GensData.denote N gs),
      baseHom (GensData.denote N gs) n hS.base_inv g • cjdec (N - n) st.2 = cjdec (N - n) st.2)
    {Borb Bgen s₁ Bgen₂ Bge Bst Btr Bgt sS Lt sH Bgen₃ Bgen₄ uB : ℕ}
    (hB : M1Charges X n N gs d (WinData.ofPoints N O) (labDiffD (markArr (N - n) st.2.1.1) L O)
      Borb Bgen)
    (hB' : BlkCharges X n (m1Model X.O n N (N, gs, d) (WinData.ofPoints N O)
        (labDiffD (markArr (N - n) st.2.1.1) L O)).1.1
      (m1Model X.O n N (N, gs, d) (WinData.ofPoints N O)
        (labDiffD (markArr (N - n) st.2.1.1) L O)).1.2.1
      s₁ Bgen₂ Bge Bst Btr Bgt sS Lt sH Bgen₃)
    (hB4 : X.B.call GroupOp.generate (n + (cellPosD n st.2.1.2.1).length,
      rebaseGens n N (cellPosD n st.2.1.2.1) gs)
      (rebaseModel X.O n N (cellPosD n st.2.1.2.1) gs) ≤ Bgen₄)
    (hu : ((labJUD st.2.1.2.1.length (markArr (N - n) st.2.1.1) st.2.1.2.2.2 L O).getD
      (O.headD 0) []).length ≤ uB)
    {s' : ℕ} {G₀ : Subgroup (Perm (Fin (n + (cellPosD n st.2.1.2.1).length)))}
    (B : BackendBounds X DV (n + (cellPosD n st.2.1.2.1).length) s' G₀)
    (hs' : (rebaseModel X.O n N (cellPosD n st.2.1.2.1) gs).2.1.length ≤ s')
    (hG₀ : GensData.denote (n + (cellPosD n st.2.1.2.1).length)
      (rebaseModel X.O n N (cellPosD n st.2.1.2.1) gs).2.1 ≤ G₀) :
    RunsWithin X body (Main.deriveProg n N (N, gs, d) O L st)
        (deriveModel X.O n N (N, gs, d) O L st)
        (deriveCJCost n N O.length L.size gs.length Borb Bgen s₁ sS Lt sH Bgen₂ Bge Bst Btr Bgt
          Bgen₃ Bgen₄ uB B.Btr B.Bstab + 5) ∧
      DOutcome DV n N w L gs d O (deriveModel X.O n N (N, gs, d) O L st) := by
  obtain ⟨hrun, hout⟩ := RunsWithin.deriveCJProg (body := body) hO hPre hS hJv hJ hK hB hB' hB4
    hu B hs' hG₀
  have he : (st.1 == 2) = true := by simpa using hst
  have hm : deriveModel X.O n N (N, gs, d) O L st = deriveCJModel X.O n N (N, gs, d) O L st.2 := by
    simp only [deriveModel, he, Bool.cond_true]
  rw [hm]
  refine ⟨?_, hout⟩
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    simp only [Prim.eval, he]
    exact RunsWithin.ite_true hrun
  case hc => simp only [Prim.cost]; omega

end DispatchSpec

/-! ### Progress: a colored partition excludes `stuck` -/

section PartProgress

variable {D : Ty} {DV : ℕ → GensData → D.denote → Prop}

/-- **The base action of the M1 child is not primitive** when the group preserves a colored
`t`-partition with `4t ≤ 3m` and the chosen orbit has more than `3m/4` points: by
`colPart_orbit`, the blocks of the partition cut the orbit into a nontrivial invariant
partition, and its pull-back to the new base is a nontrivial block. -/
theorem dv_not_prim {N n : ℕ} {G : Subgroup (Perm (Fin N))} (hn : n ≤ N)
    (hbase : IsInvariant G (baseSet n N)) {Ob : List ℕ} (hnd : Ob.Nodup)
    (hb : ∀ x ∈ Ob, n ≤ x ∧ x < N) (horb : ∀ i ∈ Ob, ∀ j, j ∈ Ob ↔ SameOrbit G i j)
    (hwO : (WinData.ofPoints N Ob).Valid N) (hGb : PermutesBlocks G (singD Ob))
    {hs : GensData}
    (hden : GensData.denote (n + (singD Ob).length) hs =
      (rebaseHom hn (isInvariant_strSet hbase) hwO mf_sing_isBlockList hGb).range)
    (hinv1 : IsInvariant (GensData.denote (n + (singD Ob).length) hs)
      (baseSet n (n + (singD Ob).length)))
    {p : CPart (Fin (N - n))} {t : ℕ} (hp : IsColPart Finset.univ t p)
    (hpK : ∀ g : ↥G, baseHom G n hbase g • p = p) (ht : 4 * t ≤ 3 * (N - n))
    (hm : 2 ≤ N - n) (hbig : 3 * (N - n) < 4 * Ob.length) :
    ¬ MulAction.IsPreprimitive
      (baseHom (GensData.denote (n + (singD Ob).length) hs) n hinv1).range
      (Fin (n + (singD Ob).length - n)) := by
  intro hprim
  have hk : (singD Ob).length = Ob.length := length_singD Ob
  have hstr := isInvariant_strSet hbase
  generalize GensData.denote (n + (singD Ob).length) hs = G1 at hden hinv1 hprim
  subst hden
  -- the base points of the orbit
  have hlt : ∀ (z : Fin (n + (singD Ob).length - n)), z.val < Ob.length := fun z => by
    have := z.2; omega
  have hgetD : ∀ {s : ℕ} (hs : s < Ob.length), Ob.getD s 0 = Ob[s] := fun hs => by
    simp [List.getD_eq_getElem?_getD, hs]
  let e : Fin (n + (singD Ob).length - n) → Fin (N - n) := fun z =>
    ⟨Ob.getD z.val 0 - n, by
      rw [hgetD (hlt z)]
      have := hb _ (List.getElem_mem (hlt z))
      omega⟩
  have he : ∀ z, (e z).val = Ob[z.val]'(hlt z) - n := fun z => by
    simp only [e]
    rw [hgetD (hlt z)]
  have heinj : Function.Injective e := by
    intro z z' h
    have h1 := congrArg Fin.val h
    rw [he, he] at h1
    have := hb _ (List.getElem_mem (hlt z))
    have := hb _ (List.getElem_mem (hlt z'))
    apply Fin.ext
    exact (hnd.getElem_inj_iff).1 (by omega)
  -- the elements of the new group and their base action
  set G1 := (rebaseHom hn hstr hwO mf_sing_isBlockList hGb).range with hG1
  have hmemR : ∀ g : ↥G, rebaseHom hn hstr hwO mf_sing_isBlockList hGb g ∈ G1 :=
    fun g => ⟨g, rfl⟩
  have he' : ∀ z, (e z).val = Ob.getD z.val 0 - n := fun z => rfl
  have hequi : ∀ (g : ↥G) (z : Fin (n + (singD Ob).length - n)),
      e (baseHom G1 n hinv1 ⟨_, hmemR g⟩ z) = baseHom G n hbase g (e z) := by
    intro g z
    apply Fin.ext
    have hz := hlt z
    obtain ⟨hbm, hbmeq⟩ := mf_blockMap_sing hwO hGb g.2 hz
    have hv := dv_baseHom_val hinv1 (hmemR g) z
    rw [pAt_rebaseHom_ge hn hstr hwO mf_sing_isBlockList hGb g (lt_of_lt_of_eq hz hk.symm)] at hv
    rw [he', hv, dv_baseHom_val hbase g.2 (e z), he', hgetD hbm, hgetD hz]
    have hOz := hb _ (List.getElem_mem hz)
    rw [show n + (Ob[z.val] - n) = Ob[z.val] by omega, pAt_of_lt _ hOz.2, ← hbmeq]
  have hall : ∀ σ ∈ (baseHom G1 n hinv1).range, ∃ g : ↥G, ∀ z, e (σ z) =
      baseHom G n hbase g (e z) := by
    rintro σ ⟨π, rfl⟩
    obtain ⟨g, hg⟩ := π.2
    refine ⟨g, fun z => ?_⟩
    have hπ : π = ⟨_, hmemR g⟩ := Subtype.ext hg.symm
    rw [hπ]
    exact hequi g z
  -- the relation "in the same block of the partition"
  let R : Fin (n + (singD Ob).length - n) → Fin (n + (singD Ob).length - n) → Prop :=
    fun a z => e z ∈ p.blk (e a)
  have hrefl : ∀ a, R a a := fun a => hp.mem_blk _ (Finset.mem_univ _)
  have hbe : ∀ a z, R a z → p.blk (e z) = p.blk (e a) := fun a z h =>
    hp.blk_eq _ (Finset.mem_univ _) _ h
  have hRinv : ∀ σ ∈ (baseHom G1 n hinv1).range, ∀ a z, R (σ a) (σ z) ↔ R a z := by
    intro σ hσ a z
    obtain ⟨g, hg⟩ := hall σ hσ
    show e (σ z) ∈ p.blk (e (σ a)) ↔ e z ∈ p.blk (e a)
    rw [hg, hg, (dm_cpart_fix (hpK g) (e a)).2]
    exact Finset.smul_mem_smul_finset_iff _
  have h0 : 0 < n + (singD Ob).length - n := by omega
  set a₀ : Fin (n + (singD Ob).length - n) := ⟨0, h0⟩
  have hblock : MulAction.IsBlock (baseHom G1 n hinv1).range {z | R a₀ z} := by
    have hsmul : ∀ σ : ↥(baseHom G1 n hinv1).range, σ • {z | R a₀ z} = {z | R (σ • a₀) z} := by
      intro σ
      ext z
      rw [Set.mem_smul_set_iff_inv_smul_mem]
      have h1 := hRinv σ.1 σ.2 a₀ (σ⁻¹ • z)
      have h2 : σ.1 (σ⁻¹ • z) = z := by
        change (σ * σ⁻¹) • z = z
        rw [mul_inv_cancel, one_smul]
      rw [h2] at h1
      exact h1.symm
    intro σ₁ σ₂ hne
    rw [hsmul, hsmul] at hne ⊢
    refine Set.disjoint_left.mpr fun z hz₁ hz₂ => hne ?_
    have e1 := hbe _ _ hz₁
    have e2 := hbe _ _ hz₂
    ext x
    show e x ∈ p.blk (e (σ₁ • a₀)) ↔ e x ∈ p.blk (e (σ₂ • a₀))
    rw [← e1, ← e2]
  -- the orbit as a set of base points, and `colPart_orbit`
  set Obf : Finset (Fin (N - n)) := Finset.univ.filter fun γ => n + γ.val ∈ Ob with hObf
  have hmemObf : ∀ γ, γ ∈ Obf ↔ ∃ z, e z = γ := by
    intro γ
    simp only [hObf, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      obtain ⟨s, hs, hsγ⟩ := List.getElem_of_mem h
      refine ⟨⟨s, by omega⟩, Fin.ext ?_⟩
      rw [he]
      simp only [hsγ]
      omega
    · rintro ⟨z, rfl⟩
      rw [he]
      have := hb _ (List.getElem_mem (hlt z))
      rw [show n + (Ob[z.val]'(hlt z) - n) = Ob[z.val]'(hlt z) by omega]
      exact List.getElem_mem _
  have hcardObf : Obf.card = Ob.length := by
    have : Obf = Finset.univ.image e := by
      ext γ
      rw [hmemObf]
      simp
    rw [this, Finset.card_image_of_injective _ heinj, Finset.card_univ, Fintype.card_fin]
    omega
  have hP : ∀ σ ∈ (baseHom G n hbase).range, ∀ γ ∈ (Finset.univ : Finset (Fin (N - n))),
      p.col (σ γ) = p.col γ ∧ p.blk (σ γ) = σ • p.blk γ := by
    rintro σ ⟨g, rfl⟩ γ -
    exact dm_cpart_fix (hpK g) γ
  have hOinvP : ∀ σ ∈ (baseHom G n hbase).range, ∀ γ ∈ Obf, σ γ ∈ Obf := by
    rintro σ ⟨g, rfl⟩ γ hγ
    simp only [hObf, Finset.mem_filter, Finset.mem_univ, true_and] at hγ ⊢
    have hp' := dv_pAt_base hbase g.2 γ
    rw [pAt_of_lt _ (by have := γ.2; omega)] at hp'
    rw [← hp']
    exact (horb _ hγ _).2 ⟨by have := γ.2; omega, (g.1 _).2, g.1, g.2, rfl⟩
  have hOtrP : ∀ γ ∈ Obf, ∀ δ ∈ Obf, ∃ σ ∈ (baseHom G n hbase).range, σ γ = δ := by
    intro γ hγ δ hδ
    simp only [hObf, Finset.mem_filter, Finset.mem_univ, true_and] at hγ hδ
    obtain ⟨hγN, hδN, g, hg, e'⟩ := (horb _ hγ _).1 hδ
    refine ⟨_, ⟨⟨g, hg⟩, rfl⟩, Fin.ext ?_⟩
    have hp' := dv_pAt_base hbase hg γ
    rw [pAt_of_lt _ (by have := γ.2; omega), e'] at hp'
    simp only at hp'
    omega
  rcases colPart_orbit hp hP (Finset.subset_univ _) hOinvP hOtrP (by omega) with h1 | h2 | h3
  · omega
  · rw [Finset.card_univ, Fintype.card_fin] at h2
    omega
  obtain ⟨h2b, hbsz, -⟩ := h3
  have hpart : p.blk (e a₀) ∩ Obf ∈ Obf.image fun γ => p.blk γ ∩ Obf :=
    Finset.mem_image.2 ⟨e a₀, (hmemObf _).2 ⟨a₀, rfl⟩, rfl⟩
  rcases MulAction.IsPreprimitive.isTrivialBlock_of_isBlock hblock with hsub | huniv
  · -- the class of `a₀` has at least two points
    have h2 := hbsz _ hpart
    obtain ⟨γ₁, hγ₁, γ₂, hγ₂, hne⟩ :=
      Finset.one_lt_card.1 (by omega : 1 < (p.blk (e a₀) ∩ Obf).card)
    obtain ⟨z₁, rfl⟩ := (hmemObf _).1 (Finset.mem_inter.1 hγ₁).2
    obtain ⟨z₂, rfl⟩ := (hmemObf _).1 (Finset.mem_inter.1 hγ₂).2
    exact hne (congrArg e (hsub (Finset.mem_inter.1 hγ₁).1 (Finset.mem_inter.1 hγ₂).1))
  · -- the class of `a₀` is everything: a single part
    have hsubO : ∀ γ ∈ Obf, γ ∈ p.blk (e a₀) := by
      intro γ hγ
      obtain ⟨z, rfl⟩ := (hmemObf _).1 hγ
      have : z ∈ {z | R a₀ z} := by rw [huniv]; exact Set.mem_univ z
      exact this
    have hone : (Obf.image fun γ => p.blk γ ∩ Obf).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro B hB C hC
      obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.1 hB
      obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.1 hC
      rw [hp.blk_eq _ (Finset.mem_univ _) γ (hsubO γ hγ),
        hp.blk_eq _ (Finset.mem_univ _) δ (hsubO δ hδ)]
    omega

/-- **Progress for a colored partition**: if `K` preserves a colored `t`-partition `p` of the
base with `4t ≤ 3m` and `m ≥ 2` (for partition data `(col, blk)`, `p = cpartOf m col blk`),
`deriveFreeProg` is never `stuck`. The M1 child either has at most `3m/4` base points, or its
base action is not primitive (`dv_not_prim`), so its maximal blocks are proper. -/
theorem derivePart_ne_stuck {X : Ctx (groupSig D)} (hO : MeetsContractOn DV deriveOps X.O)
    {n N : ℕ} {gsG gs : GensData} {w : WinData} {L : LabelData} {d : D.denote} {O : List ℕ}
    (hS : DSetting DV n N gsG w L gs d O) {p : CPart (Fin (N - n))} {t : ℕ}
    (hp : IsColPart Finset.univ t p)
    (hpK : ∀ g : ↥(GensData.denote N gs), baseHom (GensData.denote N gs) n hS.base_inv g • p = p)
    (ht : 4 * t ≤ 3 * (N - n)) (hm : 2 ≤ N - n) :
    (deriveFreeModel X.O n N (N, gs, d) O L).1 ≠ 6 := by
  unfold deriveFreeModel
  cases hc : ncBD n N L O
  · simp [noHintD, outD]
  simp only [Bool.cond_true]
  have hL := hS.hintK hc
  have hO1 : MeetsContractOn DV m1Ops X.O := fun op x h => hO op x (deriveOps_of_m1 h)
  have hO' : MeetsContractOn DV rebaseOps X.O := fun op x h => hO op x (by
    rw [show op = .generate from h]; simp [deriveOps])
  obtain ⟨hnd, hb, horb, -⟩ := dv_m1O hO1 hS.kvalid hL
  have htr1 := dv_m1_trans hO1 hS.kvalid hL
  set Ob := m1O X.O n N (N, gs, d) (WinData.ofPoints N O) L with hObdef
  have hwO : (WinData.ofPoints N Ob).Valid N :=
    WinData.valid_ofPoints hnd fun x hx => (hb x hx).2
  have hGb : PermutesBlocks (GensData.denote N gs) (singD Ob) := mf_sing_permutes horb
  obtain ⟨hdeg, hval, hden⟩ := dv_rebase_den (X := X) (DV := DV) hO' hS.hint.le hS.base_inv hwO
    mf_sing_isBlockList hGb hS.kvalid.1
  have hm1 : m1Model X.O n N (N, gs, d) (WinData.ofPoints N O) L =
      (rebaseModel X.O n N (singD Ob) gs, (WinData.ofPoints (n + (singD Ob).length) O,
        labM1D n Ob L (WinData.ofPoints N O).2)) := rfl
  rw [hm1]
  rw [hm1] at htr1
  unfold m1ContD
  cases hq : leQD ((rebaseModel X.O n N (singD Ob) gs).1 - n) (N - n)
  swap
  · simp [outD]
  simp only [Bool.cond_false]
  unfold blocksD
  cases hok : blkOKD ((rebaseModel X.O n N (singD Ob) gs).1 - n)
      (mbD n (rebaseModel X.O n N (singD Ob) gs).1 (rebaseModel X.O n N (singD Ob) gs).2.1)
  swap
  · simp only [Bool.cond_true]
    cases neqD n (rebaseModel X.O n N (singD Ob) gs).1
      (mbD n (rebaseModel X.O n N (singD Ob) gs).1 (rebaseModel X.O n N (singD Ob) gs).2.1)
      (labM1D n Ob L (WinData.ofPoints N O).2) (WinData.ofPoints (n + (singD Ob).length) O).1
    · simp [m2bOutD, outD]
    · simp [m2aOutD, outD]
  exfalso
  have hk : (singD Ob).length = Ob.length := length_singD Ob
  rw [hdeg] at hq hok htr1
  have hq' := hq
  rw [← Bool.not_eq_true, leQD_iff] at hq'
  simp only [Nat.add_sub_cancel_left] at hq' hok
  rw [hk] at hq'
  have hinv1 : IsInvariant (GensData.denote (n + (singD Ob).length)
      (rebaseModel X.O n N (singD Ob) gs).2.1) (baseSet n (n + (singD Ob).length)) := by
    rw [hden]
    exact (rebase_invariant hS.hint.le (isInvariant_strSet hS.base_inv) hwO mf_sing_isBlockList
      hGb).1
  have h2 : 2 ≤ n + (singD Ob).length - n := by omega
  have hh : ((mbD n (n + (singD Ob).length) (rebaseModel X.O n N (singD Ob) gs).2.1).headD
      []).length < 2 := by
    rw [← Bool.not_eq_true, blkOKD_iff] at hok
    simp only [Nat.add_sub_cancel_left] at h2
    omega
  exact dv_not_prim hS.hint.le hS.base_inv hnd hb horb hwO hGb hden hinv1 hp hpK ht hm (by omega)
    (dv_blocks_prim hval.1 hinv1 htr1 h2 hh)

end PartProgress

/-! ### Progress: a coloured Johnson structure excludes `stuck` -/

section CJProgress

variable {D : Ty} {DV : ℕ → GensData → D.denote → Prop}

/-- The orbit M1 chooses has labels that are not constant on the window. -/
theorem dv_m1O_nc {X : Ctx (groupSig D)} (hO : MeetsContractOn DV m1Ops X.O) {n N : ℕ}
    {gs : GensData} {d : D.denote} {w : WinData} {L : LabelData} (hGv : GroupValid DV N gs d)
    (hL : HintValid n N gs w L) : ncD n (N - n) L w.1 (m1O X.O n N (N, gs, d) w L) = true := by
  have hpre : GroupPre DV .orbits ((N, gs, d), baseWin n N) :=
    ⟨hGv, baseWin_valid n N, by rw [baseWin_denote]; exact hL.base_inv⟩
  have hos : IsOrbitPartition (GensData.denote N gs) (baseWin n N)
      (X.O.run GroupOp.orbits ((N, gs, d), baseWin n N)) := hO .orbits _ (Or.inl rfl) hpre
  exact (mf_pickD_spec (mf_exists_ncD hL hos.1)).2

/-- **The colour classes bound M1 on the labels outside `V₀`**: the chosen orbit meets a label
outside `V₀`, so (with `V₀` and the colours invariant) it lies in one colour class outside
`V₀`, of at most `m/2` points. -/
theorem dv_m1_colour {X : Ctx (groupSig D)} (hO : MeetsContractOn DV m1Ops X.O) {n N : ℕ}
    {gsG gs : GensData} {w : WinData} {L : LabelData} {d : D.denote} {O : List ℕ}
    (hS : DSetting DV n N gsG w L gs d O) {e : CJData}
    (hK : ∀ g : ↥(GensData.denote N gs),
      baseHom (GensData.denote N gs) n hS.base_inv g • cjdec (N - n) e = cjdec (N - n) e)
    (hq : ∀ c, 2 * (Finset.univ.filter fun γ =>
      γ ∉ (Align.jdec (N - n) e.1).V0 ∧ cjcol (N - n) e γ = c).card ≤ N - n)
    (hLA : HintValid n N gs (WinData.ofPoints N O) (labDiffD (markArr (N - n) e.1.1) L O)) :
    2 * (m1O X.O n N (N, gs, d) (WinData.ofPoints N O)
      (labDiffD (markArr (N - n) e.1.1) L O)).length ≤ N - n := by
  have hKJ : ∀ g : ↥(GensData.denote N gs),
      baseHom (GensData.denote N gs) n hS.base_inv g • Align.jdec (N - n) e.1 =
        Align.jdec (N - n) e.1 := fun g => ((cj_smul_eq_iff' _ _ _).1 (hK g)).1
  have hKc : ∀ (g : ↥(GensData.denote N gs)) (x : Fin (N - n)),
      cjcol (N - n) e (baseHom (GensData.denote N gs) n hS.base_inv g x) = cjcol (N - n) e x :=
    fun g x => ((cj_smul_eq_iff' _ _ _).1 (hK g)).2 x
  obtain ⟨hnd, hb, horb, -⟩ := dv_m1O hO hS.kvalid hLA
  have hnc := dv_m1O_nc hO hS.kvalid hLA
  set LA := labDiffD (markArr (N - n) e.1.1) L O with hLAdef
  set Ob := m1O X.O n N (N, gs, d) (WinData.ofPoints N O) LA with hObdef
  -- a point of the orbit in a label outside `V₀`
  obtain ⟨i, hi, j, hj, hne⟩ : ∃ i ∈ O, ∃ j ∈ O, SoJTree.setEqD (N - n)
      (interO n Ob (LA.getD i [])) (interO n Ob (LA.getD j [])) = false := by
    simp only [ncD, List.any_eq_true, Bool.not_eq_true', WinData.ofPoints_fst] at hnc
    exact hnc
  have hne' : SoJProg.setOf (N - n) (interO n Ob (LA.getD i [])) ≠
      SoJProg.setOf (N - n) (interO n Ob (LA.getD j [])) := by
    intro h
    rw [← SoJTree.setEqD_iff, hne] at h
    exact Bool.false_ne_true h
  obtain ⟨γ, hγ⟩ : ∃ γ : Fin (N - n), ¬ (γ ∈ SoJProg.setOf (N - n) (interO n Ob (LA.getD i [])) ↔
      γ ∈ SoJProg.setOf (N - n) (interO n Ob (LA.getD j []))) := by
    by_contra hcon
    push Not at hcon
    exact hne' (Finset.ext hcon)
  obtain ⟨k, hk, hγk, hγOb⟩ : ∃ k ∈ O, γ.val ∈ LA.getD k [] ∧ n + γ.val ∈ Ob := by
    simp only [SoJProg.mem_setOf, mem_interO] at hγ
    by_cases h1 : γ.val ∈ LA.getD i [] ∧ n + γ.val ∈ Ob
    · exact ⟨i, hi, h1⟩
    · exact ⟨j, hj, by tauto⟩
  have hγV : γ ∉ (Align.jdec (N - n) e.1).V0 := by
    rw [hLAdef, dv_getD_labDiff hS.nodup hk, List.mem_filter] at hγk
    intro hV
    have : getB (markArr (N - n) e.1.1) γ.val = true :=
      (getB_markArr _ _ _).2 ⟨γ.2, SoJProg.mem_setOf.1 hV⟩
    rw [this] at hγk
    simp at hγk
  -- the orbit lies in the colour class of `γ` outside `V₀`
  set C := Finset.univ.filter fun δ : Fin (N - n) =>
    δ ∉ (Align.jdec (N - n) e.1).V0 ∧ cjcol (N - n) e δ = cjcol (N - n) e γ with hC
  have hsub : Ob.toFinset ⊆ C.image fun δ => n + δ.val := by
    intro y hy
    rw [List.mem_toFinset] at hy
    obtain ⟨hγN, hyN, g, hg, he⟩ := (horb _ hγOb y).1 hy
    set σ := baseHom (GensData.denote N gs) n hS.base_inv ⟨g, hg⟩
    have hv := dv_baseHom_val hS.base_inv hg γ
    rw [pAt_of_lt _ (by have := γ.2; omega), he] at hv
    have hyn := (hb y hy).1
    refine Finset.mem_image.2 ⟨σ γ, ?_, ?_⟩
    · simp only [hC, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨fun hσ => hγV ?_, hKc _ γ⟩
      have hV := jemb_V0 (ψ := baseHom (GensData.denote N gs) n hS.base_inv) hKJ ⟨g, hg⟩
      rw [← hV] at hσ
      exact (Finset.smul_mem_smul_finset_iff σ).1 hσ
    · rw [hv]
      simp only
      omega
  have hcard : Ob.length ≤ C.card := by
    rw [← List.toFinset_card_of_nodup hnd]
    exact (Finset.card_le_card hsub).trans Finset.card_image_le
  have h3 : 2 * C.card ≤ N - n := hq (cjcol (N - n) e γ)
  omega

/-- **Progress for a coloured Johnson structure**: if `K` preserves the coloured Johnson
structure `e` (a Johnson embedding, `m ≥ 5`), whose colour classes outside `V₀` have at most
`m/2` points each, `deriveCJProg` is never `stuck`: M1 on the labels outside `V₀` stays inside
one colour class (`dv_m1_colour`), and there are at most `3m/4` cells (`dm_cells_bound`). -/
theorem deriveCJ_ne_stuck {X : Ctx (groupSig D)} (hO : MeetsContractOn DV deriveOps X.O)
    {n N : ℕ} {gsG gs : GensData} {w : WinData} {L : LabelData} {d : D.denote} {O : List ℕ}
    (hS : DSetting DV n N gsG w L gs d O) {e : CJData} (hJv : Align.JValid (N - n) e.1)
    {t : ℕ} (hJ : IsJohnson Finset.univ t (Align.jdec (N - n) e.1))
    (hK : ∀ g : ↥(GensData.denote N gs),
      baseHom (GensData.denote N gs) n hS.base_inv g • cjdec (N - n) e = cjdec (N - n) e)
    (hq : ∀ c, 2 * (Finset.univ.filter fun γ =>
      γ ∉ (Align.jdec (N - n) e.1).V0 ∧ cjcol (N - n) e γ = c).card ≤ N - n)
    (hm : 5 ≤ N - n) :
    (deriveCJModel X.O n N (N, gs, d) O L e).1 ≠ 6 := by
  have hKJ : ∀ g : ↥(GensData.denote N gs),
      baseHom (GensData.denote N gs) n hS.base_inv g • Align.jdec (N - n) e.1 =
        Align.jdec (N - n) e.1 := fun g => ((cj_smul_eq_iff' _ _ _).1 (hK g)).1
  have hO1 : MeetsContractOn DV m1Ops X.O := fun op x h => hO op x (deriveOps_of_m1 h)
  have hO' : MeetsContractOn DV rebaseOps X.O := fun op x h => hO op x (by
    rw [show op = .generate from h]; simp [deriveOps])
  unfold deriveCJModel
  cases hc : ncBD n N L O
  · simp [noHintD, outD]
  simp only [Bool.cond_true]
  cases hcA : ncBD n N (labDiffD (markArr (N - n) e.1.1) L O) O
  · simp only [Bool.cond_false]
    unfold johnStepD
    cases hcU : ncBD n (n + e.1.2.1.length)
        (labJUD e.1.2.1.length (markArr (N - n) e.1.1) e.1.2.2.2 L O) O
    · simp [outD]
    · have hcard : (Align.jdec (N - n) e.1).Λ.card = e.1.2.1.length := by
        have := congrArg Multiset.card (Align.famOf_val_card hJv)
        simp only [Multiset.card_map, Multiset.coe_card, List.length_map] at this
        exact this
      have h4 : leQD e.1.2.1.length (N - n) = true := by
        rw [leQD_iff]
        have := dm_cells_bound hJ (by simpa using hm)
        rw [Fintype.card_fin, hcard] at this
        exact this
      simp [h4, outD]
  · simp only [Bool.cond_true]
    have hLA := dv_labDiff_hint hS hKJ hcA
    have h2 := dv_m1_colour hO1 hS hK hq hLA
    obtain ⟨hnd, hb, horb, -⟩ := dv_m1O hO1 hS.kvalid hLA
    have hwO : (WinData.ofPoints N (m1O X.O n N (N, gs, d) (WinData.ofPoints N O)
        (labDiffD (markArr (N - n) e.1.1) L O))).Valid N :=
      WinData.valid_ofPoints hnd fun x hx => (hb x hx).2
    obtain ⟨hdeg, -, -⟩ := dv_rebase_den (X := X) (DV := DV) hO' hS.hint.le hS.base_inv hwO
      mf_sing_isBlockList (mf_sing_permutes horb) hS.kvalid.1
    rw [length_singD] at hdeg
    unfold m1ContD
    have h4 : leQD ((m1Model X.O n N (N, gs, d) (WinData.ofPoints N O)
        (labDiffD (markArr (N - n) e.1.1) L O)).1.1 - n) (N - n) = true := by
      rw [leQD_iff]
      change 4 * ((rebaseModel X.O n N _ gs).1 - n) ≤ _
      rw [hdeg]
      omega
    simp [h4, outD]

end CJProgress

/-! ### Well-formedness -/

section Wf

variable {D : Ty} {S : Signature} {rec : Ty × Ty} {var₁ var₂ : Ty → Type} {r : Bool}
  {Γ : WfCtx var₁ var₂}

theorem wf_outProg (tag : ℕ) {P₁ R₁ G₁ : var₁ (Ty.group D)} {P₂ R₂ G₂ : var₂ (Ty.group D)}
    {e₁ : var₁ (.list Ty.perm)} {e₂ : var₂ (.list Ty.perm)} {w₁ : var₁ Ty.win} {w₂ : var₂ Ty.win}
    {L₁ : var₁ (.array (.list .nat))} {L₂ : var₂ (.array (.list .nat))}
    (hP : ⟨Ty.group D, P₁, P₂⟩ ∈ Γ) (hR : ⟨Ty.group D, R₁, R₂⟩ ∈ Γ)
    (he : ⟨.list Ty.perm, e₁, e₂⟩ ∈ Γ) (hG : ⟨Ty.group D, G₁, G₂⟩ ∈ Γ)
    (hw : ⟨Ty.win, w₁, w₂⟩ ∈ Γ) (hL : ⟨.array (.list .nat), L₁, L₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (outProg tag P₁ R₁ e₁ G₁ w₁ L₁)
      (outProg tag P₂ R₂ e₂ G₂ w₂ L₂) := by
  unfold outProg
  prog_wf

theorem wf_leQProg {k₁ m₁ : var₁ .nat} {k₂ m₂ : var₂ .nat} (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ)
    (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (leQProg k₁ m₁) (leQProg k₂ m₂) := by
  unfold leQProg
  prog_wf

theorem wf_ncBProg {n₁ N₁ : var₁ .nat} {n₂ N₂ : var₂ .nat} {L₁ : var₁ (.array (.list .nat))}
    {L₂ : var₂ (.array (.list .nat))} {O₁ : var₁ (.list .nat)} {O₂ : var₂ (.list .nat)}
    (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (hN : ⟨.nat, N₁, N₂⟩ ∈ Γ) (hL : ⟨.array (.list .nat), L₁, L₂⟩ ∈ Γ)
    (hO : ⟨.list .nat, O₁, O₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (ncBProg n₁ N₁ L₁ O₁) (ncBProg n₂ N₂ L₂ O₂) := by
  unfold ncBProg
  refine .bind (wf_baseWinProg hn hN) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp [hN]) (.cons (by simp [hn]) .nil))) fun _ _ => ?_
  exact wf_ncProg (by simp [hn]) (List.Mem.head _) (by simp [hL]) (by simp [hO]) (by simp)

theorem wf_noHintProg {K₁ : var₁ (Ty.group D)} {K₂ : var₂ (Ty.group D)} {w₁ : var₁ Ty.win}
    {w₂ : var₂ Ty.win} (hK : ⟨Ty.group D, K₁, K₂⟩ ∈ Γ) (hw : ⟨Ty.win, w₁, w₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (noHintProg K₁ w₁) (noHintProg K₂ w₂) := by
  unfold noHintProg outProg
  prog_wf

theorem wf_blkOKProg {k₁ : var₁ .nat} {k₂ : var₂ .nat} {b₁ : var₁ (.list (.list .nat))}
    {b₂ : var₂ (.list (.list .nat))} (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ)
    (hb : ⟨.list (.list .nat), b₁, b₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (blkOKProg k₁ b₁) (blkOKProg k₂ b₂) := by
  unfold blkOKProg
  prog_wf

theorem wf_neqProg {n₁ N₁ : var₁ .nat} {n₂ N₂ : var₂ .nat} {b₁ : var₁ (.list (.list .nat))}
    {b₂ : var₂ (.list (.list .nat))} {L₁ : var₁ (.array (.list .nat))}
    {L₂ : var₂ (.array (.list .nat))} {p₁ : var₁ (.list .nat)} {p₂ : var₂ (.list .nat)}
    (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (hN : ⟨.nat, N₁, N₂⟩ ∈ Γ) (hb : ⟨.list (.list .nat), b₁, b₂⟩ ∈ Γ)
    (hL : ⟨.array (.list .nat), L₁, L₂⟩ ∈ Γ) (hp : ⟨.list .nat, p₁, p₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (neqProg n₁ N₁ b₁ L₁ p₁) (neqProg n₂ N₂ b₂ L₂ p₂) := by
  unfold neqProg
  refine .bind (by unfold blockIdxProg mapList; prog_wf) fun _ _ => ?_
  refine .bind (wf_m2aIdxProg (by simp [hn]) (by simp [hN]) (List.Mem.head _)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp [hb]) .nil)) fun _ _ => ?_
  refine wf_anyList (by simp [hp]) fun Γ' hΓ u₁ u₂ hu => ?_
  refine .bind (.prim _ (.cons (hΓ (by simp [hL])) (.cons hu .nil))) fun _ _ => ?_
  refine .bind (wf_equidistProg (List.mem_cons_of_mem _ (hΓ (List.Mem.head _)))
    (List.mem_cons_of_mem _ (hΓ (by simp))) (List.Mem.head _)) fun _ _ => ?_
  exact .prim _ (.cons (List.Mem.head _) .nil)

theorem wf_m2aOutProg {r₁ : var₁ (.prod (Ty.group D) (.prod Ty.win (.array (.list .nat))))}
    {r₂ : var₂ (.prod (Ty.group D) (.prod Ty.win (.array (.list .nat))))}
    (hr : ⟨_, r₁, r₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (m2aOutProg r₁) (m2aOutProg r₂) := by
  unfold m2aOutProg outProg
  prog_wf

theorem wf_m2bOutProg {G₁ : var₁ (Ty.group D)} {G₂ : var₂ (Ty.group D)} {p₁ : var₁ (.list .nat)}
    {p₂ : var₂ (.list .nat)}
    {r₁ : var₁ (.prod (.prod (Ty.group D) (.list Ty.perm))
      (.prod (Ty.group D) (.array (.list .nat))))}
    {r₂ : var₂ (.prod (.prod (Ty.group D) (.list Ty.perm))
      (.prod (Ty.group D) (.array (.list .nat))))}
    (hG : ⟨Ty.group D, G₁, G₂⟩ ∈ Γ) (hp : ⟨.list .nat, p₁, p₂⟩ ∈ Γ) (hr : ⟨_, r₁, r₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (m2bOutProg G₁ p₁ r₁) (m2bOutProg G₂ p₂ r₂) := by
  unfold m2bOutProg outProg mkWindow mapList
  prog_wf

theorem wf_blocksProg {n₁ : var₁ .nat} {n₂ : var₂ .nat} {G₁ : var₁ (Ty.group D)}
    {G₂ : var₂ (Ty.group D)} {w₁ : var₁ Ty.win} {w₂ : var₂ Ty.win}
    {L₁ : var₁ (.array (.list .nat))} {L₂ : var₂ (.array (.list .nat))}
    (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (hG : ⟨Ty.group D, G₁, G₂⟩ ∈ Γ) (hw : ⟨Ty.win, w₁, w₂⟩ ∈ Γ)
    (hL : ⟨.array (.list .nat), L₁, L₂⟩ ∈ Γ) :
    Prog.Wf (rec := rec) r Γ (blocksProg n₁ G₁ w₁ L₁) (blocksProg n₂ G₂ w₂ L₂) := by
  unfold blocksProg
  refine .bind (.prim _ (.cons hG .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp [hG]) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp [hw]) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) (.cons (by simp [hn]) .nil))) fun _ _ => ?_
  refine .bind (wf_baseBlocksProg (by simp [hn]) (by simp [hG])) fun _ _ => ?_
  refine .bind (wf_blkOKProg (by simp) (List.Mem.head _)) fun _ _ => ?_
  refine .bind (.prim _ .nil) fun _ _ => ?_
  refine .ite (by simp) ?_ (wf_outProg 6 (by simp [hG]) (by simp [hG]) (List.Mem.head _)
    (by simp [hG]) (by simp [hw]) (by simp [hL]))
  refine .bind (wf_neqProg (by simp [hn]) (by simp) (by simp) (by simp [hL]) (by simp))
    fun _ _ => ?_
  refine .ite (List.Mem.head _) ?_ ?_
  · refine .bind (wf_m2aProg (by simp [hn]) (by simp) (by simp) (by simp [hw]) (by simp [hL])
      (by simp)) fun _ _ => ?_
    exact wf_m2aOutProg (List.Mem.head _)
  · refine .bind (.prim _ .nil) fun _ _ => ?_
    refine .bind (wf_m2bProg (by simp [hn]) (by simp) (by simp) (by simp) (List.Mem.head _)
      (by simp [hL]) (by simp)) fun _ _ => ?_
    exact wf_m2bOutProg (by simp [hG]) (by simp) (List.Mem.head _)

theorem wf_m1ContProg {n₁ N₁ : var₁ .nat} {n₂ N₂ : var₂ .nat} {K₁ : var₁ (Ty.group D)}
    {K₂ : var₂ (Ty.group D)} {w₁ : var₁ Ty.win} {w₂ : var₂ Ty.win}
    {L₁ : var₁ (.array (.list .nat))} {L₂ : var₂ (.array (.list .nat))}
    (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (hN : ⟨.nat, N₁, N₂⟩ ∈ Γ) (hK : ⟨Ty.group D, K₁, K₂⟩ ∈ Γ)
    (hw : ⟨Ty.win, w₁, w₂⟩ ∈ Γ) (hL : ⟨.array (.list .nat), L₁, L₂⟩ ∈ Γ) :
    Prog.Wf (rec := rec) r Γ (m1ContProg n₁ N₁ K₁ w₁ L₁) (m1ContProg n₂ N₂ K₂ w₂ L₂) := by
  unfold m1ContProg
  refine .bind (wf_m1Prog hn hN hK hw hL) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) (.cons (by simp [hn]) .nil))) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp [hN]) (.cons (by simp [hn]) .nil))) fun _ _ => ?_
  refine .bind (wf_leQProg (by simp) (List.Mem.head _)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (.prim _ .nil) fun _ _ => ?_
  exact .ite (by simp) (wf_outProg 1 (by simp) (by simp) (List.Mem.head _) (by simp) (by simp)
    (by simp)) (wf_blocksProg (by simp [hn]) (by simp) (by simp) (by simp))

theorem wf_deriveFreeProg {n₁ N₁ : var₁ .nat} {n₂ N₂ : var₂ .nat} {K₁ : var₁ (Ty.group D)}
    {K₂ : var₂ (Ty.group D)} {O₁ : var₁ (.list .nat)} {O₂ : var₂ (.list .nat)}
    {L₁ : var₁ (.array (.list .nat))} {L₂ : var₂ (.array (.list .nat))}
    (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (hN : ⟨.nat, N₁, N₂⟩ ∈ Γ) (hK : ⟨Ty.group D, K₁, K₂⟩ ∈ Γ)
    (hO : ⟨.list .nat, O₁, O₂⟩ ∈ Γ) (hL : ⟨.array (.list .nat), L₁, L₂⟩ ∈ Γ) :
    Prog.Wf (rec := rec) r Γ (deriveFreeProg n₁ N₁ K₁ O₁ L₁) (deriveFreeProg n₂ N₂ K₂ O₂ L₂) := by
  unfold deriveFreeProg
  refine .bind (wf_ncBProg hn hN hL hO) fun _ _ => ?_
  refine .bind (wf_mkWindow (by simp [hN]) (by simp [hO])) fun _ _ => ?_
  exact .ite (by simp) (wf_m1ContProg (by simp [hn]) (by simp [hN]) (by simp [hK])
    (List.Mem.head _) (by simp [hL])) (wf_noHintProg (by simp [hK]) (List.Mem.head _))

theorem wf_cellPosProg {n₁ : var₁ .nat} {n₂ : var₂ .nat} {c₁ : var₁ (.list (.list .nat))}
    {c₂ : var₂ (.list (.list .nat))} (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ)
    (hc : ⟨.list (.list .nat), c₁, c₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (cellPosProg n₁ c₁) (cellPosProg n₂ c₂) := by
  unfold cellPosProg mapList
  prog_wf

theorem wf_johnStepProg {n₁ N₁ : var₁ .nat} {n₂ N₂ : var₂ .nat} {K₁ : var₁ (Ty.group D)}
    {K₂ : var₂ (Ty.group D)} {O₁ : var₁ (.list .nat)} {O₂ : var₂ (.list .nat)}
    {L₁ : var₁ (.array (.list .nat))} {L₂ : var₂ (.array (.list .nat))} {w₁ : var₁ Ty.win}
    {w₂ : var₂ Ty.win} {v₁ : var₁ (.array .bool)} {v₂ : var₂ (.array .bool)}
    {c₁ : var₁ (.list (.list .nat))} {c₂ : var₂ (.list (.list .nat))}
    {f₁ : var₁ (.array (.list .nat))} {f₂ : var₂ (.array (.list .nat))}
    (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (hN : ⟨.nat, N₁, N₂⟩ ∈ Γ) (hK : ⟨Ty.group D, K₁, K₂⟩ ∈ Γ)
    (hO : ⟨.list .nat, O₁, O₂⟩ ∈ Γ) (hL : ⟨.array (.list .nat), L₁, L₂⟩ ∈ Γ)
    (hw : ⟨Ty.win, w₁, w₂⟩ ∈ Γ) (hv : ⟨.array .bool, v₁, v₂⟩ ∈ Γ)
    (hc : ⟨.list (.list .nat), c₁, c₂⟩ ∈ Γ) (hf : ⟨.array (.list .nat), f₁, f₂⟩ ∈ Γ) :
    Prog.Wf (rec := rec) r Γ (johnStepProg n₁ N₁ K₁ O₁ L₁ w₁ v₁ c₁ f₁)
      (johnStepProg n₂ N₂ K₂ O₂ L₂ w₂ v₂ c₂ f₂) := by
  unfold johnStepProg
  refine .bind (.prim _ (.cons hN (.cons hn .nil))) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp [hc]) .nil)) fun _ _ => ?_
  refine .bind (wf_mapLabelsProg (by simp [hL]) (by simp [hO]) fun Γ' hΓ x₁ x₂ hx =>
    wf_jUnionProg (hΓ (List.Mem.head _)) (hΓ (by simp [hv])) (hΓ (by simp [hf])) hx)
    fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp [hn]) (.cons (by simp) .nil))) fun _ _ => ?_
  refine .bind (wf_ncBProg (by simp [hn]) (List.Mem.head _) (by simp) (by simp [hO]))
    fun _ _ => ?_
  refine .bind (wf_cellPosProg (by simp [hn]) (by simp [hc])) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp [hK]) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (wf_rebaseProg (by simp [hn]) (by simp [hN]) (List.Mem.head _) (by simp))
    fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (wf_mkWindow (List.Mem.head _) (by simp [hO])) fun _ _ => ?_
  refine .bind (.prim _ .nil) fun _ _ => ?_
  refine .ite (by simp) ?_ ?_
  · refine .bind (wf_leQProg (by simp) (by simp)) fun _ _ => ?_
    exact .ite (List.Mem.head _)
      (wf_outProg 4 (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))
      (wf_outProg 6 (by simp [hK]) (by simp [hK]) (by simp) (by simp [hK]) (by simp [hw])
        (by simp [hL]))
  · refine .bind (.caseList (by simp [hO]) (.prim _ .nil) fun _ _ _ _ => .ret (List.Mem.head _))
      fun _ _ => ?_
    refine .bind (.prim _ (.cons (by simp) (.cons (List.Mem.head _) .nil))) fun _ _ => ?_
    refine .bind (wf_jfallbackProg (by simp [hn]) (by simp) (List.Mem.head _)) fun _ _ => ?_
    refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
    refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
    refine .bind (.prim _ .nil) fun _ _ => ?_
    refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
    exact wf_outProg 5 (by simp) (by simp) (by simp) (by simp) (by simp) (List.Mem.head _)

theorem wf_deriveCJProg {n₁ N₁ : var₁ .nat} {n₂ N₂ : var₂ .nat} {K₁ : var₁ (Ty.group D)}
    {K₂ : var₂ (Ty.group D)} {O₁ : var₁ (.list .nat)} {O₂ : var₂ (.list .nat)}
    {L₁ : var₁ (.array (.list .nat))} {L₂ : var₂ (.array (.list .nat))} {e₁ : var₁ cjTy}
    {e₂ : var₂ cjTy} (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (hN : ⟨.nat, N₁, N₂⟩ ∈ Γ)
    (hK : ⟨Ty.group D, K₁, K₂⟩ ∈ Γ) (hO : ⟨.list .nat, O₁, O₂⟩ ∈ Γ)
    (hL : ⟨.array (.list .nat), L₁, L₂⟩ ∈ Γ) (he : ⟨cjTy, e₁, e₂⟩ ∈ Γ) :
    Prog.Wf (rec := rec) r Γ (deriveCJProg n₁ N₁ K₁ O₁ L₁ e₁) (deriveCJProg n₂ N₂ K₂ O₂ L₂ e₂) := by
  unfold deriveCJProg
  refine .bind (wf_ncBProg hn hN hL hO) fun _ _ => ?_
  refine .bind (wf_mkWindow (by simp [hN]) (by simp [hO])) fun _ _ => ?_
  refine .ite (by simp) ?_ (wf_noHintProg (by simp [hK]) (List.Mem.head _))
  refine .bind (.prim _ (.cons (by simp [he]) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp [hN]) (.cons (by simp [hn]) .nil))) fun _ _ => ?_
  refine .bind (wf_markProg (List.Mem.head _) (by simp)) fun _ _ => ?_
  refine .bind (wf_mapLabelsProg (by simp [hL]) (by simp [hO]) fun Γ' hΓ x₁ x₂ hx =>
    Toolkit.wf_filterList hx fun Γ'' hΓ' j₁ j₂ hj =>
      .bind (.prim _ (.cons (hΓ' (hΓ (List.Mem.head _))) (.cons hj .nil))) fun _ _ =>
        .prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (wf_ncBProg (by simp [hn]) (by simp [hN]) (List.Mem.head _) (by simp [hO]))
    fun _ _ => ?_
  exact .ite (List.Mem.head _) (wf_m1ContProg (by simp [hn]) (by simp [hN]) (by simp [hK])
    (by simp) (by simp)) (wf_johnStepProg (by simp [hn]) (by simp [hN]) (by simp [hK])
      (by simp [hO]) (by simp [hL]) (by simp) (by simp) (by simp) (by simp))

theorem wf_deriveProg {n₁ N₁ : var₁ .nat} {n₂ N₂ : var₂ .nat} {K₁ : var₁ (Ty.group D)}
    {K₂ : var₂ (Ty.group D)} {O₁ : var₁ (.list .nat)} {O₂ : var₂ (.list .nat)}
    {L₁ : var₁ (.array (.list .nat))} {L₂ : var₂ (.array (.list .nat))} {s₁ : var₁ stTy}
    {s₂ : var₂ stTy} (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (hN : ⟨.nat, N₁, N₂⟩ ∈ Γ)
    (hK : ⟨Ty.group D, K₁, K₂⟩ ∈ Γ) (hO : ⟨.list .nat, O₁, O₂⟩ ∈ Γ)
    (hL : ⟨.array (.list .nat), L₁, L₂⟩ ∈ Γ) (hs : ⟨stTy, s₁, s₂⟩ ∈ Γ) :
    Prog.Wf (rec := rec) r Γ (deriveProg n₁ N₁ K₁ O₁ L₁ s₁) (deriveProg n₂ N₂ K₂ O₂ L₂ s₂) := by
  unfold deriveProg
  refine .bind (.prim _ (.cons hs .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp [hs]) .nil)) fun _ _ => ?_
  refine .bind (.prim _ .nil) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) (.cons (List.Mem.head _) .nil))) fun _ _ => ?_
  exact .ite (List.Mem.head _) (wf_deriveCJProg (by simp [hn]) (by simp [hN]) (by simp [hK])
    (by simp [hO]) (by simp [hL]) (by simp)) (wf_deriveFreeProg (by simp [hn]) (by simp [hN])
      (by simp [hK]) (by simp [hO]) (by simp [hL]))

end Wf

end GraphIso.Main
