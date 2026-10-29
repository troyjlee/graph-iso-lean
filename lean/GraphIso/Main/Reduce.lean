module

public import GraphIso.CertProg.Kernel
public import GraphIso.Toolkit.BlockStab
public import GraphIso.Toolkit.Extend
public import GraphIso.Toolkit.Labels
public import GraphIso.SoJProg.JohnsonData

/-!
# The coarsening reductions of the main recursion

Stage 14j-1, item 3 (`PLAN-14.md` §14.1). Two reductions that coarsen a hint and branch over
the cosets of a subgroup:

* **M2b** (`m2bProg`). The base action is transitive with a block system `Ψ`, and the label
  of some point of the window meets every block in the same number of points. The group is
  reduced to the setwise stabilizer `H` of a block `B₀` (stage 14b's `blockStabProg`: at most
  `|Ψ|` coset representatives forming an `IsLeftCover`). `H` is re-based onto the points of
  `B₀` (singleton blocks, `rebaseProg`), and the labels are intersected with `B₀` and
  renumbered (`interLab`); `RunsWithin.m2bProg` gives the run, the cover and the re-based
  group. On every nonempty `H`-invariant part of the window the new labels are valid hint
  data (`m2b_hintValid`, by stage 14a's `hint_blockStab`), and with at least two blocks the
  new base has at most half of the old one (`m2b_card`).
* **The Johnson fallback** (`jfallbackProg`). The base action preserves a Johnson structure
  `J`, and on an orbit `O` of the window both `lab ∖ V₀` and the Johnson union are constant.
  The group, re-based onto the cells (cell `c` at the position `n + c`), is reduced to the
  pointwise stabilizer of the positions of the cells `U₀` of the union at a point of `O`
  (`pointStabsProg`); its elements fix each cell of the union as a set. Since the group
  permutes these positions, there are at most `|U₀|!` coset representatives
  (`RunsWithin.mr_pointStabsFact`, at a cost polynomial times `|U₀|!`), and `|U₀|` is at most
  the label size times `s` (`length_jUnionData_le`, the data version of `card_jUnion_le`). By
  stage 14a's `fix_of_jUnion_const`, every element of the result fixes every label of `O`, so
  each of its orbits in `O` has constant labels and at most `|O|/2` points (`jfallback_half`).
-/

@[expose] public section

namespace GraphIso.Main

open Equiv MulAction Pointwise Cost GraphIso GraphIso.Programs GraphIso.Toolkit
  GraphIso.Recursion GraphIso.SplitJohnson GraphIso.Solver

/-! ### The pointwise stabilizer of a permuted list, with factorial bounds -/

section PointStabs

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}

/-- **The pointwise stabilizer of a list of base positions permuted by the group**, with at
most `|ps|!` coset representatives and a cost polynomial times `|ps|!` (stage 14e's
`cp_ps_run`, for any group permuting the list). -/
theorem RunsWithin.mr_pointStabsFact (hO : MeetsContractOn DV stabOps X.O)
    (hPre : ∀ op x, stabOps op → GroupPre DV op x → X.Pre op x) {n N : ℕ} {gs : GensData}
    {d : D.denote} (hGv : GroupValid DV N gs d)
    (hG : IsInvariant (GensData.denote N gs) (baseSet n N)) {ps : List ℕ} (hnd : ps.Nodup)
    (hps : ∀ u ∈ ps, n ≤ u ∧ u < N)
    (hHS : ∀ g ∈ GensData.denote N gs, ∀ u : Fin N, u.val ∈ ps → (g u).val ∈ ps)
    {s : ℕ} {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N s G₀) (hs : gs.length ≤ s)
    (hG₀ : GensData.denote N gs ≤ G₀) :
    RunsWithin X body (Toolkit.pointStabsProg (N, gs, d) ps) (pointStabsModel X.O (N, gs, d) ps)
        (CertProg.kerACost N ps.length B.Btr B.Bstab) ∧
      (pointStabsModel X.O (N, gs, d) ps).1.1 = N ∧
      GroupValid DV N (pointStabsModel X.O (N, gs, d) ps).1.2.1
        (pointStabsModel X.O (N, gs, d) ps).1.2.2 ∧
      GensData.denote N (pointStabsModel X.O (N, gs, d) ps).1.2.1 =
        pointwiseStab (GensData.denote N gs) {v : Fin N | v.val ∈ ps} ∧
      (∀ r ∈ (pointStabsModel X.O (N, gs, d) ps).2, PermData.Valid N r) ∧
      IsLeftCover (GensData.denote N gs)
        (GensData.denote N (pointStabsModel X.O (N, gs, d) ps).1.2.1)
        (fun i : Fin (pointStabsModel X.O (N, gs, d) ps).2.length =>
          PermData.denote N ((pointStabsModel X.O (N, gs, d) ps).2.get i)) ∧
      (pointStabsModel X.O (N, gs, d) ps).2.length ≤ ps.length.factorial := by
  obtain ⟨-, hN, hv, hden, hrv, hcov, -⟩ := RunsWithin.pointStabsProg (X := X) (body := body)
    hO hPre hGv hG hps B hs hG₀
  refine ⟨?_, hN, hv, hden, hrv, hcov, ?_⟩
  · have hfold := CertProg.cp_ps_run (X := X) (body := body) hO hPre B hnd hHS ps
      [] ((N, gs, d), [PermData.one N]) (by simpa using hnd)
      (by simpa using fun u hu => ⟨hu, (hps u hu).2⟩) rfl hGv hs le_rfl hG₀ (by simp)
      (by simp [PermData.valid_one]) (by simp)
    apply RunsWithin.mono
    case h =>
      unfold Toolkit.pointStabsProg
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.permOne N)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      exact hfold
    case hc =>
      simp only [Prim.cost, CertProg.kerACost]
      omega
  · exact CertProg.pointStabs_reps_le_factorial (X := X) hO hGv hnd (fun u hu => (hps u hu).2)
      hHS

end PointStabs


/-! ### The Johnson fallback: model -/

section JFallbackModel

variable {M Ω Γ : Type*} [Group M] [MulAction M Ω] [DecidableEq Γ] {ψ : M →* Perm Γ}
  {lab : Ω → Finset Γ}

/-- **The Johnson fallback halves the window.** If both `lab ∖ V₀` and the Johnson union are
constant on the orbit `O` of a hinted instance, every subgroup fixing each cell of the union at
`u₀ ∈ O` (as a set) has orbits of at most `|O|/2` points in `O`: its elements fix every label
of `O` (`fix_of_jUnion_const`), so its orbits have constant labels (`card_le_of_const`). -/
theorem jfallback_half {V : Finset Γ} {t : ℕ} {J : JEmb Γ} (hJ : IsJohnson V t J)
    (hinv : ∀ g : M, ψ g • J = J) {O : Finset Ω} (hOinv : Invariant M O) (hT : Transitive M O)
    (hh : IsHint ψ O lab) (hA : ¬ NonConst O fun u => lab u \ J.V0)
    (hU : ¬ NonConst O fun u => jUnion J (lab u)) {u₀ : Ω} (hu₀ : u₀ ∈ O) (K : Subgroup M)
    (hK : ∀ g ∈ K, ∀ a ∈ jUnion J (lab u₀), ψ g • a = a) {O' : Finset Ω} (hO' : O' ⊆ O)
    (hO'orb : ∀ v ∈ O', ∀ v' ∈ O', ∃ g ∈ K, g • v = v') : 2 * O'.card ≤ O.card := by
  refine card_le_of_const hOinv hT hh hO' ?_
  rintro ⟨v, hv, v', hv', hne⟩
  obtain ⟨g, hg, rfl⟩ := hO'orb v hv v' hv'
  have hlab := fix_of_jUnion_const hJ hinv hOinv hh.equivar hA hU hu₀ (hK g hg)
  exact hne (lab_smul_of_fix hh.equivar hlab (hO' hv)).symm

end JFallbackModel


/-! ### The Johnson fallback: data -/

section JFallbackData

/-- **The number of union cells on data** (the data version of `card_jUnion_le`): at most the
label size times the bound `s` on the cell lists of the points marked in `v0`. -/
theorem length_jUnionData_le (nc : ℕ) (v0 : Array Bool) (fA : Array (List ℕ)) (Lu : List ℕ)
    {s : ℕ} (hs : ∀ j ∈ Lu, getB v0 j = true → (fA.getD j []).length ≤ s) :
    (jUnionData nc v0 fA Lu).length ≤ Lu.length * s := by
  have hsub : (jUnionData nc v0 fA Lu).toFinset ⊆
      ((Lu.filter (getB v0)).flatMap fun j => fA.getD j []).toFinset := by
    intro c hc
    obtain ⟨-, j, hj, hv, hcj⟩ := (mem_jUnionData nc v0 fA Lu c).1 (List.mem_toFinset.1 hc)
    exact List.mem_toFinset.2 (List.mem_flatMap.2 ⟨j, List.mem_filter.2 ⟨hj, hv⟩, hcj⟩)
  have h1 := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup (nodup_jUnionData _ _ _ _)] at h1
  have h2 := List.toFinset_card_le ((Lu.filter (getB v0)).flatMap fun j => fA.getD j [])
  have h3 : ((Lu.filter (getB v0)).flatMap fun j => fA.getD j []).length ≤
      (Lu.filter (getB v0)).length * s := by
    rw [List.length_flatMap]
    calc ((Lu.filter (getB v0)).map fun j => (fA.getD j []).length).sum
        ≤ ((Lu.filter (getB v0)).map fun _ => s).sum :=
          List.sum_le_sum fun j hj => by
            obtain ⟨hjL, hjv⟩ := List.mem_filter.1 hj
            exact hs j hjL hjv
      _ = (Lu.filter (getB v0)).length * s := by simp
  have h4 := Nat.mul_le_mul_right s (List.length_filter_le (getB v0) Lu)
  omega

end JFallbackData


/-! ### The Johnson fallback: programs -/

section JFallbackProgs

variable {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- Shift base indices to positions. -/
def shiftProg (n : var .nat) (l : var (.list .nat)) : Prog S rec var (.list .nat) :=
  mapList l fun j => .op2 .add n j

end JFallbackProgs

section JFallbackProg

variable {D : Ty} {rec : Ty × Ty} {var : Ty → Type}

/-- **The Johnson fallback**, in a group `G` re-based onto the cells (cell `c` at the position
`n + c`): the pointwise stabilizer of the positions of the union cells `cl`, with its coset
representatives. -/
def jfallbackProg (n : var .nat) (G : var (Ty.group D)) (cl : var (.list .nat)) :
    Prog (groupSig D) rec var (.prod (Ty.group D) (.list Ty.perm)) :=
  .bind (shiftProg n cl) fun ps => Toolkit.pointStabsProg G ps

end JFallbackProg

section JFallbackSpecs

variable {S : Signature} {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

theorem RunsWithin.shiftProg (n : ℕ) (l : List ℕ) :
    RunsWithin X body (Main.shiftProg n l) (l.map (n + ·)) (4 * l.length + 2) := by
  refine (RunsWithin.mapList_le (c := 1) fun j _ => RunsWithin.prim_le rfl ?_).mono ?_
  · simp [Prim.cost]
  · omega

end JFallbackSpecs

section JFallbackSpec

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}

/-- The value of `jfallbackProg`: the pointwise stabilizer of the positions of the cells `cl`
and its coset representatives. -/
def jfallbackModel (O : Oracle (groupSig D)) (n : ℕ) (G : GroupData D.denote) (cl : List ℕ) :
    GroupData D.denote × List PermData :=
  pointStabsModel O G (cl.map (n + ·))

/-- The cost of `jfallbackProg` on `u` union cells at degree `N`: the shift and the pointwise
stabilizer (polynomial times `u!`). -/
def jfallbackCost (N u Bt Bs : ℕ) : ℕ := 4 * u + 2 + CertProg.kerACost N u Bt Bs

/-- **The Johnson fallback.** For a group `G = ⟨gs⟩` re-based onto the cells (base `[n, N)`)
that permutes the positions of the union cells `cl`, the program returns the pointwise
stabilizer of these positions: a valid group, at most `|cl|!` coset representatives forming an
`IsLeftCover`, at a cost polynomial times `|cl|!`. -/
theorem RunsWithin.jfallbackProg (hO : MeetsContractOn DV stabOps X.O)
    (hPre : ∀ op x, stabOps op → GroupPre DV op x → X.Pre op x) {n N : ℕ} {gs : GensData}
    {d : D.denote} (hGv : GroupValid DV N gs d)
    (hG : IsInvariant (GensData.denote N gs) (baseSet n N)) {cl : List ℕ} (hnd : cl.Nodup)
    (hcl : ∀ c ∈ cl, c < N - n)
    (hHS : ∀ g ∈ GensData.denote N gs, ∀ u : Fin N,
      u.val ∈ cl.map (n + ·) → (g u).val ∈ cl.map (n + ·))
    {s' : ℕ} {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N s' G₀)
    (hs' : gs.length ≤ s') (hG₀ : GensData.denote N gs ≤ G₀) :
    RunsWithin X body (Main.jfallbackProg n (N, gs, d) cl) (jfallbackModel X.O n (N, gs, d) cl)
        (jfallbackCost N cl.length B.Btr B.Bstab) ∧
      (jfallbackModel X.O n (N, gs, d) cl).1.1 = N ∧
      GroupValid DV N (jfallbackModel X.O n (N, gs, d) cl).1.2.1
        (jfallbackModel X.O n (N, gs, d) cl).1.2.2 ∧
      GensData.denote N (jfallbackModel X.O n (N, gs, d) cl).1.2.1 =
        pointwiseStab (GensData.denote N gs) {v : Fin N | v.val ∈ cl.map (n + ·)} ∧
      (∀ r ∈ (jfallbackModel X.O n (N, gs, d) cl).2, PermData.Valid N r) ∧
      IsLeftCover (GensData.denote N gs)
        (GensData.denote N (jfallbackModel X.O n (N, gs, d) cl).1.2.1)
        (fun i : Fin (jfallbackModel X.O n (N, gs, d) cl).2.length =>
          PermData.denote N ((jfallbackModel X.O n (N, gs, d) cl).2.get i)) ∧
      (jfallbackModel X.O n (N, gs, d) cl).2.length ≤ cl.length.factorial := by
  have hnd' : (cl.map (n + ·)).Nodup := hnd.map fun a b h => by simpa using h
  have hps : ∀ u ∈ cl.map (n + ·), n ≤ u ∧ u < N := by
    intro u hu
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hu
    have := hcl c hc
    omega
  obtain ⟨hrun, hN, hv, hden, hrv, hcov, hcard⟩ := RunsWithin.mr_pointStabsFact (X := X)
    (body := body) hO hPre hGv hG hnd' hps hHS B hs' hG₀
  rw [List.length_map] at hrun hcard
  refine ⟨?_, hN, hv, hden, hrv, hcov, hcard⟩
  apply RunsWithin.mono
  case h =>
    unfold Main.jfallbackProg
    run_step (RunsWithin.shiftProg (X := X) (body := body) n cl)
    exact hrun
  case hc =>
    simp only [jfallbackCost]
    omega

end JFallbackSpec


/-! ### The Johnson fallback: labels as sets -/

section JFallbackBridge

variable {n N : ℕ} {L : LabelData}

theorem mr_labOf_eq_setOf (u : Fin N) :
    labOf n N L u = SoJProg.setOf (N - n) (L.getD u.val []) := by
  ext j
  rw [mem_labOf, SoJProg.mem_setOf]

theorem mr_val_basePos (j : Fin (N - n)) : (basePos (n := n) j : Fin N).val = n + j.val := rfl

end JFallbackBridge


/-! ### M2b: the block stabilizer, re-based onto the block -/

section M2bProg

variable {D : Ty} {rec : Ty × Ty} {var : Ty → Type}

/-- **M2b.** The setwise stabilizer `H` of block `t` of `bs` (with coset representatives), `H`
re-based onto the points of the block (singleton blocks), and the labels of the window `w`
intersected with the block and renumbered. The result is `((H, reps), (H', L'))`. -/
def m2bProg (n N : var .nat) (gs : var Ty.gens) (bs : var (.list (.list .nat))) (t : var .nat)
    (L : var (.array (.list .nat))) (w : var (.list .nat)) :
    Prog (groupSig D) rec var
      (.prod (.prod (Ty.group D) (.list Ty.perm)) (.prod (Ty.group D) (.array (.list .nat)))) :=
  .bind (Toolkit.blockStabProg N gs bs t) fun Hr =>
  .bind (.op1 .fst Hr) fun H => .bind (.op1 .snd H) fun hd => .bind (.op1 .fst hd) fun hgs =>
  .bind (.op1 .arrayOfList bs) fun bsA => .bind (.op2 .arrayGet bsA t) fun B₀ =>
  .bind (mapList B₀ fun p => .bind (.op0 .nil) fun nil => .op2 .cons p nil) fun sbs =>
  .bind (Toolkit.rebaseProg n N hgs sbs) fun H' =>
  .bind (mapList B₀ fun p => .op2 .sub p n) fun pts =>
  .bind (.op2 .sub N n) fun m =>
  .bind (markProg m pts) fun mask =>
  .bind (Programs.posProg m pts) fun pos =>
  .bind (mapLabelsProg L w fun li => interLabProg pos mask li) fun L' =>
  .bind (.op2 .pair H' L') fun hl => .op2 .pair Hr hl

end M2bProg

section M2bSpec

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}

/-- The block's points as base indices. -/
def m2bPts (n : ℕ) (bs : List (List ℕ)) (t : ℕ) : List ℕ := (bs.toArray.getD t []).map (· - n)

/-- The new labels: intersected with the block and renumbered. -/
def m2bLabels (n N : ℕ) (bs : List (List ℕ)) (t : ℕ) (L : LabelData) (w : List ℕ) : LabelData :=
  mapLabels L w (interLab (WinData.pos (N - n) (WinData.ofPoints (N - n) (m2bPts n bs t)))
    (markArr (N - n) (m2bPts n bs t)))

/-- The value of `m2bProg`. -/
def m2bModel (O : Oracle (groupSig D)) (n N : ℕ) (gs : GensData) (bs : List (List ℕ)) (t : ℕ)
    (L : LabelData) (w : List ℕ) :
    (GroupData D.denote × List PermData) × (GroupData D.denote × LabelData) :=
  (blockStabModel O N bs gs t,
    (rebaseModel O n N ((bs.toArray.getD t []).map fun p => [p])
      (blockStabModel O N bs gs t).1.2.1,
      m2bLabels n N bs t L w))

/-- The cost of `m2bProg`. The arguments are the block stabilizer's (`blockStabCost`), `k` the
block's size, `sH` the number of generators of the stabilizer, `Bgen` the re-basing charge,
`wl` the window's length, `T` a bound on the label lengths and `Ls` the size of the label
array. -/
def m2bCost (N n mb kb s sS Lt Bge Bst Btr Bgt k sH Bgen wl T Ls : ℕ) : ℕ :=
  blockStabCost N mb kb s sS Lt Bge Bst Btr Bgt + rebaseCost n N k k sH Bgen + 9 * k + kb +
    markCost (N - n) k + (2 * (N - n) + 9 * k + 8) + (wl * (interCost T + 6) + Ls + 3) + 30

theorem mr_getD_toArray' {α : Type*} (l : List (List α)) (c : ℕ) :
    l.toArray.getD c [] = l.getD c [] := by
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getD_eq_getElem?_getD]

/-- A block of a block list of a valid window is duplicate-free and listed in the window. -/
theorem mr_block_nodup {N : ℕ} {w : WinData} (hw : w.Valid N) {bs : List (List ℕ)}
    (hbs : IsBlockList w bs) {t : ℕ} (ht : t < bs.length) :
    (bs.getD t []).Nodup ∧ ∀ p ∈ bs.getD t [], p ∈ w.1 := by
  have hnd : bs.flatten.Nodup := hbs.1.nodup_iff.2 hw.nodup
  rw [List.getD_eq_getElem _ _ ht]
  refine ⟨(List.nodup_flatten.1 hnd).1 _ (List.getElem_mem ht), fun p hp => ?_⟩
  exact hbs.1.mem_iff.1 (List.mem_flatten.2 ⟨_, List.getElem_mem ht, hp⟩)

/-- A group mapping a list of points into itself permutes its singleton blocks. -/
theorem mr_permutes_singletons {N : ℕ} {H : Subgroup (Perm (Fin N))} {B : List ℕ}
    (h : ∀ g ∈ H, ∀ u : Fin N, u.val ∈ B → (g u).val ∈ B) :
    PermutesBlocks H (B.map fun p => [p]) := by
  intro g hg b hb
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hb
  by_cases hpN : p < N
  · refine ⟨[(g ⟨p, hpN⟩).val], List.mem_map.2 ⟨_, h g hg ⟨p, hpN⟩ hp, rfl⟩, fun u hu => ?_⟩
    rw [List.mem_singleton] at hu ⊢
    rw [show u = ⟨p, hpN⟩ from Fin.ext hu]
  · refine ⟨[p], List.mem_map.2 ⟨p, hp, rfl⟩, fun u hu => ?_⟩
    rw [List.mem_singleton] at hu
    exact absurd (hu ▸ u.2) hpN

theorem mr_flatten_singletons (B : List ℕ) : (B.map fun p => [p]).flatten = B := by
  induction B with
  | nil => rfl
  | cons p B ih => simp [ih]

theorem mr_isBlockList_singletons {N : ℕ} {B : List ℕ} :
    IsBlockList (WinData.ofPoints N B) (B.map fun p => [p]) := by
  refine ⟨?_, fun b hb => ?_⟩
  · rw [mr_flatten_singletons]
    exact List.Perm.refl _
  · obtain ⟨p, -, rfl⟩ := List.mem_map.1 hb
    simp

/-- The block stabilizer maps the block's positions into themselves. -/
theorem mr_blockStab_maps {n N : ℕ} {G : Subgroup (Perm (Fin N))} (hG : IsInvariant G (baseSet n N))
    {B : List ℕ} (hBn : ∀ p ∈ B, n ≤ p) :
    ∀ g ∈ (Recursion.blockStab (baseHom G n hG) (baseBlockSet n N B)).map G.subtype,
      ∀ u : Fin N, u.val ∈ B → (g u).val ∈ B := by
  intro g hg u hu
  obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.1 hg
  have hun : n ≤ u.val := hBn _ hu
  set γ : Fin (N - n) := ⟨u.val - n, by omega⟩
  have hγ : γ ∈ baseBlockSet n N B := by
    rw [mem_baseBlockSet]
    simpa [γ, Nat.add_sub_cancel' hun] using hu
  have hu' : u = basePos γ := Fin.ext (by simp [basePos, γ]; omega)
  have hh' : baseHom G n hG h • baseBlockSet n N B = baseBlockSet n N B := hh
  have hmem : baseHom G n hG h γ ∈ baseBlockSet n N B := by
    rw [← hh']
    exact Finset.smul_mem_smul_finset hγ
  rw [mem_baseBlockSet] at hmem
  show (h.1 u).val ∈ B
  rw [hu', ← baseHom_apply]
  exact hmem

end M2bSpec


section M2bRun

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}

/-- **M2b, the run.** The program returns `m2bModel`: the block stabilizer with its cover (as
`RunsWithin.blockStabProg`), and its re-basing onto the points of the block, generated by the
image of `rebaseHom` for the singleton blocks. -/
theorem RunsWithin.m2bProg (hO : MeetsContractOn DV blockStabOps X.O)
    (hPre : ∀ op x, blockStabOps op → GroupPre DV op x → X.Pre op x) {n N : ℕ} (hn : n ≤ N)
    {wb : WinData} {bs : List (List ℕ)} {gs : GensData} {t : ℕ}
    (hG : IsInvariant (GensData.denote N gs) (baseSet n N)) (hwb : wb.Valid N)
    (hwbn : ∀ i ∈ wb.1, n ≤ i) (hbs : IsBlockList wb bs)
    (hGb : PermutesBlocks (GensData.denote N gs) bs) (hgs : GensData.AllValid N gs)
    (ht : t < bs.length) {Bge Bst Btr Bgt : ℕ}
    (hBge : X.B.call GroupOp.generate (N + bs.length, extendGens N bs gs)
      (extGroup X.O N bs gs) ≤ Bge)
    (hBst : X.B.call GroupOp.stabilizer (extGroup X.O N bs gs, N + t)
      (bsStab X.O N bs gs t) ≤ Bst)
    (hBtr : X.B.call GroupOp.orbitTransversal (extGroup X.O N bs gs, N + t)
      (bsTrans X.O N bs gs t) ≤ Btr)
    (hBgt : X.B.call GroupOp.generate (N, (bsStab X.O N bs gs t).2.1.map (PermData.truncTo N))
      (blockStabModel X.O N bs gs t).1 ≤ Bgt) {Bgen : ℕ}
    (hBgen : X.B.call GroupOp.generate
      (n + ((bs.toArray.getD t []).map fun p => [p]).length,
        rebaseGens n N ((bs.toArray.getD t []).map fun p => [p])
          (blockStabModel X.O N bs gs t).1.2.1)
      (rebaseModel X.O n N ((bs.toArray.getD t []).map fun p => [p])
        (blockStabModel X.O N bs gs t).1.2.1) ≤ Bgen)
    (L : LabelData) (w : List ℕ) {T : ℕ} (hT : ∀ i ∈ w, (L.getD i []).length ≤ T) :
    RunsWithin X body (Main.m2bProg n N gs bs t L w) (m2bModel X.O n N gs bs t L w)
        (m2bCost N n bs.flatten.length bs.length gs.length
          (bsStab X.O N bs gs t).2.1.length (bsTrans X.O N bs gs t).length Bge Bst Btr Bgt
          (bs.toArray.getD t []).length (blockStabModel X.O N bs gs t).1.2.1.length Bgen
          w.length T L.size) ∧
      (blockStabModel X.O N bs gs t).1.1 = N ∧
      GroupValid DV N (blockStabModel X.O N bs gs t).1.2.1
        (blockStabModel X.O N bs gs t).1.2.2 ∧
      GensData.denote N (blockStabModel X.O N bs gs t).1.2.1 =
        (Recursion.blockStab (baseHom (GensData.denote N gs) n hG)
          (baseBlockSet n N bs[t])).map (GensData.denote N gs).subtype ∧
      (∀ r ∈ (blockStabModel X.O N bs gs t).2, PermData.Valid N r) ∧
      IsLeftCover (GensData.denote N gs)
        (GensData.denote N (blockStabModel X.O N bs gs t).1.2.1)
        (fun i : Fin (blockStabModel X.O N bs gs t).2.length =>
          PermData.denote N ((blockStabModel X.O N bs gs t).2.get i)) ∧
      (blockStabModel X.O N bs gs t).2.length ≤ bs.length ∧
      (m2bModel X.O n N gs bs t L w).2.1.1 = n + (bs.toArray.getD t []).length ∧
      GroupValid DV (n + (bs.toArray.getD t []).length) (m2bModel X.O n N gs bs t L w).2.1.2.1
        (m2bModel X.O n N gs bs t L w).2.1.2.2 ∧
      ∃ (hHb : IsInvariant (GensData.denote N (blockStabModel X.O N bs gs t).1.2.1)
          (baseSet n N))
        (hGb' : PermutesBlocks (GensData.denote N (blockStabModel X.O N bs gs t).1.2.1)
          ((bs.toArray.getD t []).map fun p => [p]))
        (hw' : (WinData.ofPoints N (bs.toArray.getD t [])).Valid N),
        GensData.denote (n + ((bs.toArray.getD t []).map fun p => [p]).length)
            (m2bModel X.O n N gs bs t L w).2.1.2.1 =
          (rebaseHom hn (isInvariant_strSet hHb) hw' mr_isBlockList_singletons hGb').range := by
  obtain ⟨hrunH, hHN, hHv, hHden, hrv, hcov, hrl⟩ := RunsWithin.blockStabProg (X := X)
    (body := body) hO hPre hG hwb hwbn hbs hGb hgs ht hBge hBst hBtr hBgt
  have hB0e : bs.toArray.getD t [] = bs[t] := by
    rw [mr_getD_toArray', List.getD_eq_getElem _ _ ht]
  have hB0 := mr_block_nodup hwb hbs ht
  rw [List.getD_eq_getElem _ _ ht, ← hB0e] at hB0
  have hBn : ∀ p ∈ bs.toArray.getD t [], n ≤ p := fun p hp => hwbn p (hB0.2 p hp)
  have hBN : ∀ p ∈ bs.toArray.getD t [], p < N := fun p hp => hwb.lt p (hB0.2 p hp)
  have hHG : GensData.denote N (blockStabModel X.O N bs gs t).1.2.1 ≤ GensData.denote N gs := by
    rw [hHden]
    exact Subgroup.map_subtype_le _
  have hHb : IsInvariant (GensData.denote N (blockStabModel X.O N bs gs t).1.2.1)
      (baseSet n N) := fun g hg => hG g (hHG hg)
  have hmaps := mr_blockStab_maps hG hBn
  rw [hB0e] at hmaps
  have hGb' : PermutesBlocks (GensData.denote N (blockStabModel X.O N bs gs t).1.2.1)
      ((bs.toArray.getD t []).map fun p => [p]) := by
    refine mr_permutes_singletons fun g hg u hu => ?_
    rw [hB0e] at hu ⊢
    exact hmaps g (hHden ▸ hg) u hu
  have hw' := WinData.valid_ofPoints hB0.1 hBN
  have hO' : MeetsContractOn DV rebaseOps X.O := fun op x h => hO op x (Or.inl h)
  have hPre' : ∀ op x, rebaseOps op → GroupPre DV op x → X.Pre op x :=
    fun op x h => hPre op x (Or.inl h)
  obtain ⟨hrunR, hRN, hRv, hRden⟩ := RunsWithin.rebaseProg (X := X) (body := body) hO' hPre' hn
    hHb hw' mr_isBlockList_singletons hGb' hHv.1 hBgen
  rw [mr_flatten_singletons, List.length_map] at hrunR
  set B := bs.toArray.getD t [] with hB
  have hptl : (m2bPts n bs t).length = B.length := List.length_map _
  have hmask := RunsWithin.markProg (X := X) (body := body) (N - n) (m2bPts n bs t)
  have hpos := RunsWithin.posProg (X := X) (body := body) (N - n)
    (WinData.ofPoints (N - n) (m2bPts n bs t))
  have hlab := RunsWithin.mapLabelsProg (X := X) (body := body) (L := L) (w := w)
    (f := fun li => Toolkit.interLabProg
      (WinData.pos (N - n) (WinData.ofPoints (N - n) (m2bPts n bs t)))
      (markArr (N - n) (m2bPts n bs t)) li) (c := interCost T) fun i hi =>
    (RunsWithin.interLabProg _ _ _).mono (by have := hT i hi; simp only [interCost]; omega)
  rw [List.length_map] at hRN hRv
  refine ⟨?_, hHN, hHv, hHden, hrv, hcov, hrl, hRN, hRv, hHb, hGb', hw', hRden⟩
  apply RunsWithin.mono
  case h =>
    run_step hrunH
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.mapList_le (c := 2) fun p _ =>
      RunsWithin.bind_le (RunsWithin.prim _ _) (RunsWithin.prim _ _) (by simp [Prim.cost]))
    run_step hrunR
    run_step (RunsWithin.mapList_le (c := 1) fun p _ => RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step hmask
    run_step hpos
    run_step hlab
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    have e1 : (Prim.arrayGet (a := .list .nat)).eval
        (.cons (Prim.arrayOfList.eval (.cons bs .nil)) (.cons t .nil)) = B := rfl
    have e2 : (WinData.ofPoints (N - n) (m2bPts n bs t)).1.length = B.length := hptl
    simp only [Prim.cost, Args.head, m2bCost, e1, e2, hptl]
    omega

end M2bRun


/-! ### M2b: the new hint and the new base size -/

section M2bHint

variable {n N : ℕ}

/-- `π` on a natural number: `π i` below the degree, the identity above. -/
def mr_pAt {M : ℕ} (π : Perm (Fin M)) (i : ℕ) : ℕ := if h : i < M then (π ⟨i, h⟩).val else i

theorem mr_pAt_of_lt {M : ℕ} (π : Perm (Fin M)) {i : ℕ} (h : i < M) :
    mr_pAt π i = (π ⟨i, h⟩).val := by
  simp [mr_pAt, h]

theorem mr_get_eq_pAt {M : ℕ} {g : PermData} (hg : g.Valid M) {i : ℕ} (hi : i < M) :
    get g.1 i = mr_pAt (PermData.denote M g) i := by
  rw [mr_pAt_of_lt _ hi, PermData.val_denote_apply hg]

/-- Hint data is valid for a generating list once the labels are equivariant for every element
of the generated group. -/
theorem mr_hintValid_of_forall {M : ℕ} {hs : GensData} {w : WinData} {L : LabelData}
    (hle : n ≤ M) (hhs : GensData.AllValid M hs)
    (hbase : IsInvariant (GensData.denote M hs) (baseSet n M))
    (hwin : ∀ i ∈ w.1, i < n) (hlt : ∀ i ∈ w.1, ∀ j ∈ L.getD i [], j < M - n)
    (hnd : ∀ i ∈ w.1, (L.getD i []).Nodup)
    (heq : ∀ π ∈ GensData.denote M hs, ∀ i ∈ w.1, (L.getD (mr_pAt π i) []).toFinset =
      ((L.getD i []).map fun j => mr_pAt π (n + j) - n).toFinset)
    (hnc : ∃ i ∈ w.1, ∃ j ∈ w.1, (L.getD i []).toFinset ≠ (L.getD j []).toFinset) :
    HintValid n M hs w L := by
  refine ⟨hle, hbase, hwin, hlt, hnd, fun g hg i hi => ?_, hnc⟩
  have hgv := hhs g hg
  have hmem : PermData.denote M g ∈ GensData.denote M hs :=
    Subgroup.subset_closure ⟨g, hg, rfl⟩
  have hiM : i < M := by have := hwin i hi; omega
  rw [mr_get_eq_pAt hgv hiM, heq _ hmem i hi]
  congr 1
  refine List.map_congr_left fun j hj => ?_
  have hj' := hlt i hi j hj
  rw [mr_get_eq_pAt hgv (by omega)]

/-- The labels' equivariance on data, for every element of the group. -/
theorem mr_lab_mem_iff {gs : GensData} {w : WinData} {L : LabelData} (hL : HintValid n N gs w L)
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

/-- A group permuting singleton blocks maps their points into themselves. -/
theorem mr_maps_of_singletons {B : List ℕ} {H : Subgroup (Perm (Fin N))}
    (hGb : PermutesBlocks H (B.map fun p => [p])) {h : Perm (Fin N)} (hh : h ∈ H) {u : Fin N}
    (hu : u.val ∈ B) : (h u).val ∈ B := by
  obtain ⟨b', hb', himg⟩ := hGb h hh [u.val] (List.mem_map.2 ⟨_, hu, rfl⟩)
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hb'
  have := himg u (List.mem_singleton_self _)
  rw [List.mem_singleton] at this
  rw [this]
  exact hq

/-- On singleton blocks the block map follows the points. -/
theorem mr_blockMap_single {B : List ℕ} {H : Subgroup (Perm (Fin N))}
    (hw : (WinData.ofPoints N B).Valid N) (hGb : PermutesBlocks H (B.map fun p => [p]))
    {h : Perm (Fin N)} (hh : h ∈ H) {y : ℕ} (hy : y < B.length) :
    ∃ hy' : blockMap N (B.map fun p => [p]) h y < B.length, ∃ hyN : B[y] < N,
      (h ⟨B[y], hyN⟩).val = B[blockMap N (B.map fun p => [p]) h y] := by
  have hy1 : y < (B.map fun p => [p]).length := by simpa using hy
  obtain ⟨ht', himg⟩ := blockMap_spec hw mr_isBlockList_singletons hGb hh hy1
  have hyN : B[y] < N := hw.lt _ (by simp)
  have := himg ⟨B[y], hyN⟩ (by simp)
  simp only [List.getElem_map, List.mem_singleton] at this
  exact ⟨by simpa using ht', hyN, this⟩

/-- The rebased action on singleton blocks, on the new base. -/
theorem mr_pAt_rebase_ge {B : List ℕ} {H : Subgroup (Perm (Fin N))} (hn : n ≤ N)
    (hHs : IsInvariant H (strSet n N)) (hw : (WinData.ofPoints N B).Valid N)
    (hGb : PermutesBlocks H (B.map fun p => [p])) (h : ↥H) {y : ℕ} (hy : y < B.length) :
    mr_pAt (rebaseHom hn hHs hw mr_isBlockList_singletons hGb h) (n + y) - n =
      blockMap N (B.map fun p => [p]) h.1 y := by
  rw [mr_pAt_of_lt _ (by simp; omega), rebaseHom_ge hn hHs hw mr_isBlockList_singletons hGb h
    (x := ⟨n + y, by simp; omega⟩) (show n ≤ n + y by omega)]
  simp

/-- The block's points as base indices form a valid window of the base. -/
theorem mr_pts_valid {B : List ℕ} (hnd : B.Nodup) (hB : ∀ p ∈ B, n ≤ p ∧ p < N) :
    (WinData.ofPoints (N - n) (B.map (· - n))).Valid (N - n) := by
  refine WinData.valid_ofPoints ?_ ?_
  · refine hnd.map_on fun p hp q hq e => ?_
    have := hB p hp
    have := hB q hq
    omega
  · intro j hj
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hj
    have := hB p hp
    omega

theorem mr_pts_pos {B : List ℕ} (hnd : B.Nodup) (hB : ∀ p ∈ B, n ≤ p ∧ p < N) :
    ∀ i (h : i < (B.map (· - n)).length),
      get (WinData.pos (N - n) (WinData.ofPoints (N - n) (B.map (· - n)))) (B.map (· - n))[i] =
        i := by
  intro i hi
  have := WinData.get_pos (mr_pts_valid hnd hB) (j := i) (by simpa using hi)
  rwa [WinData.ofPoints_fst, List.getD_eq_getElem _ _ hi] at this

theorem mr_pts_mask {B : List ℕ} (hB : ∀ p ∈ B, n ≤ p ∧ p < N) :
    ∀ j, getB (markArr (N - n) (B.map (· - n))) j = true ↔ j ∈ B.map (· - n) := by
  intro j
  rw [getB_markArr]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 h
  have := hB p hp
  omega

theorem mr_getD_m2bLabels {w : WinData} (hw : w.Valid N) {bs : List (List ℕ)} {t : ℕ}
    {L : LabelData} {i : ℕ} (hi : i ∈ w.1) :
    (m2bLabels n N bs t L w.1).getD i [] =
      interLab (WinData.pos (N - n) (WinData.ofPoints (N - n) (m2bPts n bs t)))
        (markArr (N - n) (m2bPts n bs t)) (L.getD i []) := by
  rw [m2bLabels, getD_mapLabels hw.nodup]
  split_ifs with h
  · rfl
  · have hs : ¬ i < L.size := fun hl => h ⟨hi, hl⟩
    have e : L.getD i [] = [] := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (Nat.le_of_not_lt hs)]
      rfl
    rw [e]
    rfl


/-- **M2b, the new hint.** Let the labels `L` be valid hint data on the window `w` for
`G = ⟨gs⟩`, with `G` transitive on `w` and on the base, `bs` a block system of the base action,
and the label of some `u₀ ∈ w` meeting every block in the same number of points. Let
`H = blockStab` of block `t` (as `RunsWithin.m2bProg` computes it) and `hs` generate its
re-basing onto the block's points (`hden`, as in `RunsWithin.m2bProg`). Then on every
nonempty `H`-invariant part `wO` of the window, the new labels (`L` intersected with the
block, renumbered) are valid hint data for `hs` at degree `n + |B₀|`. -/
theorem m2b_hintValid {gs : GensData} {w : WinData} {L : LabelData}
    (hL : HintValid n N gs w L) (hgs : GensData.AllValid N gs) (hw : w.Valid N)
    (hinv : IsInvariant (GensData.denote N gs) (w.denote N))
    (hT : Transitive ↥(GensData.denote N gs) (winFinset N w))
    (htr : ∀ γ δ : Fin (N - n), ∃ g, baseHom (GensData.denote N gs) n hL.base_inv g γ = δ)
    {bs : List (List ℕ)} (hbs : IsBlockList (WinData.ofPoints N (basePts n N)) bs)
    (hΨ : IsBlockSys (baseHom (GensData.denote N gs) n hL.base_inv) (blockFam n N bs))
    {u₀ : Fin N} (hu₀ : u₀.val ∈ w.1) (heq : Equidist (blockFam n N bs) (labOf n N L u₀))
    {t : ℕ} (ht : t < bs.length) {H : Subgroup (Perm (Fin N))}
    (hH : H = (Recursion.blockStab (baseHom (GensData.denote N gs) n hL.base_inv)
      (baseBlockSet n N bs[t])).map (GensData.denote N gs).subtype)
    (hHb : IsInvariant H (baseSet n N))
    (hGb : PermutesBlocks H ((bs.toArray.getD t []).map fun p => [p]))
    (hw' : (WinData.ofPoints N (bs.toArray.getD t [])).Valid N) {hs : GensData}
    (hhs : GensData.AllValid (n + (bs.toArray.getD t []).length) hs)
    (hden : GensData.denote (n + ((bs.toArray.getD t []).map fun p => [p]).length) hs =
      (rebaseHom hL.le (isInvariant_strSet hHb) hw' mr_isBlockList_singletons hGb).range)
    {wO : WinData} (hwO : ∀ i ∈ wO.1, i ∈ w.1) (hwO0 : wO.1 ≠ [])
    (hOinv : IsInvariant H (wO.denote N)) :
    HintValid n (n + (bs.toArray.getD t []).length) hs wO (m2bLabels n N bs t L w.1) := by
  have hB0e : bs.toArray.getD t [] = bs[t] := by
    rw [mr_getD_toArray', List.getD_eq_getElem _ _ ht]
  have hHG : H ≤ GensData.denote N gs := by
    rw [hH]
    exact Subgroup.map_subtype_le _
  have hlab : ∀ i ∈ w.1, (m2bLabels n N bs t L w.1).getD i [] =
      interLab (WinData.pos (N - n) (WinData.ofPoints (N - n) (m2bPts n bs t)))
        (markArr (N - n) (m2bPts n bs t)) (L.getD i []) := fun i hi => mr_getD_m2bLabels hw hi
  set B := bs.toArray.getD t [] with hBdef
  have hBnd : B.Nodup := hB0e ▸ block_nodup hbs (List.getElem_mem ht)
  have hBr : ∀ p ∈ B, n ≤ p ∧ p < N := fun p hp =>
    block_sub_base hbs (List.getElem_mem ht) (hB0e ▸ hp)
  have hpos : ∀ i (h : i < (m2bPts n bs t).length),
      get (WinData.pos (N - n) (WinData.ofPoints (N - n) (m2bPts n bs t))) (m2bPts n bs t)[i] =
        i := mr_pts_pos hBnd hBr
  have hmask : ∀ j, getB (markArr (N - n) (m2bPts n bs t)) j = true ↔ j ∈ m2bPts n bs t :=
    mr_pts_mask hBr
  have hPl : (m2bPts n bs t).length = B.length := List.length_map _
  have hk : (B.map fun p => [p]).length = B.length := List.length_map _
  have hPget : ∀ x (hx : x < (m2bPts n bs t).length), (m2bPts n bs t)[x] = B[x]'(hPl ▸ hx) - n :=
    fun x hx => List.getElem_map _
  suffices h : HintValid n (n + (B.map fun p => [p]).length) hs wO (m2bLabels n N bs t L w.1) by
    rwa [hk] at h
  refine mr_hintValid_of_forall (by omega) (by rw [hk]; exact hhs) ?_
    (fun i hi => hL.win_lt i (hwO i hi)) ?_ ?_ ?_ ?_
  · rw [hden]
    exact (rebase_invariant hL.le (isInvariant_strSet hHb) hw' mr_isBlockList_singletons hGb).1
  · intro i hi j hj
    rw [hlab i (hwO i hi)] at hj
    have := lt_of_mem_interLab hpos hmask hj
    omega
  · intro i hi
    rw [hlab i (hwO i hi)]
    exact nodup_interLab hpos hmask (hL.lab_nodup i (hwO i hi))
  · intro π hπ i hi
    rw [hden] at hπ
    obtain ⟨h, rfl⟩ := hπ
    have hiw := hwO i hi
    have hin : i < n := hL.win_lt i hiw
    have hhG : h.1 ∈ GensData.denote N gs := hHG h.2
    rw [mr_pAt_of_lt _ (show i < n + (B.map fun p => [p]).length by omega),
      rebaseHom_lt hL.le (isInvariant_strSet hHb) hw' mr_isBlockList_singletons hGb h
        (x := ⟨i, by omega⟩) hin]
    have hgi : (h.1 ⟨i, hw.lt i hiw⟩).val ∈ w.1 := hinv h.1 hhG ⟨i, hw.lt i hiw⟩ hiw
    rw [hlab _ hgi, hlab i hiw]
    ext x
    simp only [List.mem_toFinset, List.mem_map]
    rw [mem_interLab hpos hmask]
    constructor
    · rintro ⟨hx, hmem⟩
      have hxB : x < B.length := hPl ▸ hx
      rw [mr_lab_mem_iff hL hgs hw hinv hhG hiw] at hmem
      obtain ⟨j', hj', hlt, hgj⟩ := hmem
      rw [hPget x hx] at hgj
      have hBx := hBr _ (List.getElem_mem hxB)
      have hgjB : (h.1 ⟨n + j', hlt⟩).val ∈ B := by
        rw [hgj, show n + (B[x] - n) = B[x] by omega]
        exact List.getElem_mem hxB
      have hjB : n + j' ∈ B := by
        have := mr_maps_of_singletons hGb (H.inv_mem h.2) (u := h.1 ⟨n + j', hlt⟩) hgjB
        rwa [← Perm.mul_apply, inv_mul_cancel, Perm.one_apply] at this
      obtain ⟨y, hyB, hyv⟩ := List.getElem_of_mem hjB
      obtain ⟨hy', hyN, himg⟩ := mr_blockMap_single hw' hGb h.2 hyB
      refine ⟨y, (mem_interLab hpos hmask _ y).2 ⟨hPl ▸ hyB, ?_⟩, ?_⟩
      · rw [hPget y (hPl ▸ hyB), hyv, show n + j' - n = j' by omega]
        exact hj'
      · rw [mr_pAt_rebase_ge hL.le (isInvariant_strSet hHb) hw' hGb h hyB]
        apply (hBnd.getElem_inj_iff (hi := hy') (hj := hxB)).1
        rw [← himg]
        have e : (⟨B[y], hyN⟩ : Fin N) = ⟨n + j', hlt⟩ := Fin.ext hyv
        rw [e, hgj]
        omega
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨hyP, hPy⟩ := (mem_interLab hpos hmask _ y).1 hy
      have hyB : y < B.length := hPl ▸ hyP
      rw [mr_pAt_rebase_ge hL.le (isInvariant_strSet hHb) hw' hGb h hyB]
      obtain ⟨hy', hyN, himg⟩ := mr_blockMap_single hw' hGb h.2 hyB
      refine ⟨hPl ▸ hy', ?_⟩
      rw [mr_lab_mem_iff hL hgs hw hinv hhG hiw]
      have hBy := hBr _ (List.getElem_mem hyB)
      have hBy' := hBr _ (List.getElem_mem hy')
      have hlt : n + (m2bPts n bs t)[y] < N := by rw [hPget y hyP]; omega
      refine ⟨(m2bPts n bs t)[y], hPy, hlt, ?_⟩
      have e : (⟨n + (m2bPts n bs t)[y], hlt⟩ : Fin N) = ⟨B[y], hyN⟩ :=
        Fin.ext (by simp only; rw [hPget y hyP]; omega)
      rw [e, himg, hPget _ (hPl ▸ hy')]
      omega
  · have hh := hL.isHint hgs hw hinv
    have hB₀ : baseBlockSet n N bs[t] ∈ blockFam n N bs :=
      List.mem_toFinset.2 (List.mem_map.2 ⟨_, List.getElem_mem ht, rfl⟩)
    obtain ⟨i₀, hi₀⟩ := List.exists_mem_of_ne_nil _ hwO0
    have hO : winFinset N wO ⊆ winFinset N w := fun u hu =>
      mem_winFinset.2 (hwO _ (mem_winFinset.1 hu))
    have hOne : (winFinset N wO).Nonempty :=
      ⟨⟨i₀, hw.lt i₀ (hwO i₀ hi₀)⟩, mem_winFinset.2 hi₀⟩
    have hOinv' : Invariant ↥(Recursion.blockStab (baseHom (GensData.denote N gs) n hL.base_inv)
        (baseBlockSet n N bs[t])) (winFinset N wO) := by
      intro g u hu
      rw [mem_winFinset] at hu ⊢
      have hgH : ((g : ↥(GensData.denote N gs)) : Perm (Fin N)) ∈ H := by
        rw [hH]
        exact Subgroup.mem_map.2 ⟨g.1, g.2, rfl⟩
      exact hOinv _ hgH u hu
    obtain ⟨u, hu, v, hv, hne⟩ :=
      (hint_blockStab hΨ htr hT hh (mem_winFinset.2 hu₀) heq hB₀ hO hOne hOinv').nonconst
    have huw := mem_winFinset.1 (hO hu)
    have hvw := mem_winFinset.1 (hO hv)
    refine ⟨u.val, mem_winFinset.1 hu, v.val, mem_winFinset.1 hv, fun he => hne ?_⟩
    have key : ∀ z ∈ w.1, ∀ x (hx : x < B.length),
        (B[x] - n ∈ L.getD z [] ↔ x ∈ (m2bLabels n N bs t L w.1).getD z []) := by
      intro z hz x hx
      rw [hlab z hz, mem_interLab hpos hmask]
      constructor
      · intro h
        exact ⟨hPl ▸ hx, by rw [hPget]; exact h⟩
      · rintro ⟨hx', h⟩
        rwa [hPget] at h
    have key2 : ∀ x (hx : x < B.length),
        (B[x] - n ∈ L.getD u.val [] ↔ B[x] - n ∈ L.getD v.val []) := by
      intro x hx
      rw [key _ huw x hx, key _ hvw x hx, ← List.mem_toFinset, he, List.mem_toFinset]
    rw [subLab_eq_iff]
    ext γ
    simp only [Finset.mem_inter, mem_labOf, mem_baseBlockSet]
    rw [← hB0e]
    refine and_congr_left fun hγ => ?_
    obtain ⟨x, hx, hxv⟩ := List.getElem_of_mem hγ
    have e : γ.val = B[x] - n := by omega
    rw [e]
    exact key2 x hx

/-- **M2b, the new base size**: a block of a block system with at least two blocks, of a
transitive base action, has at most half the base points. -/
theorem m2b_card {G : Subgroup (Perm (Fin N))} {hG : IsInvariant G (baseSet n N)}
    {bs : List (List ℕ)} (hbs : IsBlockList (WinData.ofPoints N (basePts n N)) bs)
    (hΨ : IsBlockSys (baseHom G n hG) (blockFam n N bs))
    (htr : ∀ γ δ : Fin (N - n), ∃ g, baseHom G n hG g γ = δ) (h2 : 2 ≤ (blockFam n N bs).card)
    {t : ℕ} (ht : t < bs.length) :
    2 * (bs.toArray.getD t []).length ≤ N - n := by
  have hB0e : bs.toArray.getD t [] = bs[t] := by
    rw [mr_getD_toArray', List.getD_eq_getElem _ _ ht]
  have hB₀ : baseBlockSet n N bs[t] ∈ blockFam n N bs :=
    List.mem_toFinset.2 (List.mem_map.2 ⟨_, List.getElem_mem ht, rfl⟩)
  obtain ⟨C, hC, hne⟩ :=
    Finset.exists_mem_ne (s := blockFam n N bs) (by omega) (baseBlockSet n N bs[t])
  obtain ⟨γ, hγ⟩ := hΨ.nonempty _ hB₀
  obtain ⟨δ, hδ⟩ := hΨ.nonempty _ hC
  obtain ⟨g, -, hgB⟩ := hΨ.exists_smul_eq htr hB₀ hC hγ hδ
  have hcard : C.card = (baseBlockSet n N bs[t]).card := by
    rw [← hgB, Finset.card_smul_finset]
  have hdisj := hΨ.disj _ hB₀ C hC hne.symm
  have hu := Finset.card_union_of_disjoint hdisj
  have hle := Finset.card_le_univ (baseBlockSet n N bs[t] ∪ C)
  rw [Fintype.card_fin] at hle
  rw [hB0e, ← card_baseBlockSet hbs (List.getElem_mem ht)]
  omega

end M2bHint


/-! ### Well-formedness -/

section Wf

variable {D : Ty} {S : Signature} {rec : Ty × Ty} {var₁ var₂ : Ty → Type} {r : Bool}
  {Γ : WfCtx var₁ var₂}

theorem wf_shiftProg {n₁ : var₁ .nat} {n₂ : var₂ .nat} {l₁ : var₁ (.list .nat)}
    {l₂ : var₂ (.list .nat)} (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (hl : ⟨.list .nat, l₁, l₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (shiftProg n₁ l₁) (shiftProg n₂ l₂) := by
  unfold shiftProg mapList
  prog_wf

theorem wf_jfallbackProg {n₁ : var₁ .nat} {n₂ : var₂ .nat} {G₁ : var₁ (Ty.group D)}
    {G₂ : var₂ (Ty.group D)} {l₁ : var₁ (.list .nat)} {l₂ : var₂ (.list .nat)}
    (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (hG : ⟨Ty.group D, G₁, G₂⟩ ∈ Γ) (hl : ⟨.list .nat, l₁, l₂⟩ ∈ Γ) :
    Prog.Wf (rec := rec) r Γ (jfallbackProg n₁ G₁ l₁) (jfallbackProg n₂ G₂ l₂) := by
  unfold jfallbackProg
  refine .bind (wf_shiftProg hn hl) fun p₁ p₂ => ?_
  exact Toolkit.wf_pointStabsProg (by simp [hG]) (List.Mem.head _)

theorem wf_m2bProg {n₁ N₁ t₁ : var₁ .nat} {n₂ N₂ t₂ : var₂ .nat} {g₁ : var₁ Ty.gens}
    {g₂ : var₂ Ty.gens} {b₁ : var₁ (.list (.list .nat))} {b₂ : var₂ (.list (.list .nat))}
    {L₁ : var₁ (.array (.list .nat))} {L₂ : var₂ (.array (.list .nat))}
    {w₁ : var₁ (.list .nat)} {w₂ : var₂ (.list .nat)} (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ)
    (hN : ⟨.nat, N₁, N₂⟩ ∈ Γ) (hg : ⟨Ty.gens, g₁, g₂⟩ ∈ Γ)
    (hb : ⟨.list (.list .nat), b₁, b₂⟩ ∈ Γ) (ht : ⟨.nat, t₁, t₂⟩ ∈ Γ)
    (hL : ⟨.array (.list .nat), L₁, L₂⟩ ∈ Γ) (hw : ⟨.list .nat, w₁, w₂⟩ ∈ Γ) :
    Prog.Wf (rec := rec) r Γ (m2bProg (D := D) n₁ N₁ g₁ b₁ t₁ L₁ w₁)
      (m2bProg (D := D) n₂ N₂ g₂ b₂ t₂ L₂ w₂) := by
  unfold m2bProg
  refine .bind (wf_blockStabProg hN hg hb ht) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp [hb]) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) (.cons (by simp [ht]) .nil))) fun _ _ => ?_
  refine .bind (by unfold mapList; prog_wf) fun _ _ => ?_
  refine .bind (wf_rebaseProg (by simp [hn]) (by simp [hN]) (by simp) (List.Mem.head _))
    fun _ _ => ?_
  refine .bind (by unfold mapList; prog_wf) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp [hN]) (.cons (by simp [hn]) .nil))) fun _ _ => ?_
  refine .bind (wf_markProg (List.Mem.head _) (by simp)) fun _ _ => ?_
  refine .bind (by unfold Programs.posProg mapList; prog_wf) fun _ _ => ?_
  refine .bind (wf_mapLabelsProg (by simp [hL]) (by simp [hw]) fun _ hΓ _ _ hv =>
    wf_interLabProg (hΓ (List.Mem.head _)) (hΓ (by simp)) hv) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) (.cons (List.Mem.head _) .nil))) fun _ _ => ?_
  exact .prim _ (.cons (by simp) (.cons (List.Mem.head _) .nil))

end Wf


/-- **M2b's labels**: intersections with the block. -/
theorem labLen_m2bLabels_le {w : List ℕ} (hw : w.Nodup) (n N : ℕ) (bs : List (List ℕ)) (t : ℕ)
    (L : LabelData) : labLen (m2bLabels n N bs t L w) ≤ labLen L :=
  labLen_mapLabels_short hw fun l => length_interLab_le _ _ l

end GraphIso.Main
