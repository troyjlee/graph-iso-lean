module

public import GraphIso.Case2b.Link
public import GraphIso.SoJTree.LeafBound
public import GraphIso.Certificates.Cases

/-!
# The structure of M4

Stage 14j-3, item 4 (`PLAN-14.md` §14.3). A group `H = (N, gs, d)` keeps the window `[n', N)`
invariant (the base positions after individualization) and acts on it transitively and not
doubly transitively, through `baseHom H n'` on `Fin (N − n')`. Write `k = msK n' N`, the length
of the window's list (`msK_eq`: `k = N − n'`). `m4StructProg n' H` computes a structure on the
window and its stabilizer:

1. the orbital configuration `C` of the action (`orbitalProg n'`): a homogeneous classical
   coherent configuration that is not a clique (`ms_config`, `ms_config'`, from
   `orbital_config` and `ms_coherent2`);
2. the leaves of `C` (stage 14h's `leavesOfProg`): the components partition of the least
   disconnected colour if a colour graph is disconnected (a colored `⌊k/2⌋`-partition,
   `isColPart_comp`), otherwise the trimmed leaves of `soj (colOf k C) ((k + 3) / 2)` (the
   configuration is then uniprimitive, `ms_uniprimitive`, and `split_or_johnson` applies);
3. the first leaf `o` and its stabilizer `K` in `H` with coset representatives (stage 14d's
   `leafStabProg` on the window `[n', N)`, by orbit–stabilizer).

The restriction of `H` to the window, indexed by `Fin k`, is `msPsi` (`restrictHom` along
`WinData.reindex`). It agrees with `baseHom` on values (`msPsi_val`), the configuration's colours
are its orbitals (`ms_orbital`), and it preserves the configuration (`ms_relab`).

* `ms_leaves`: the leaves are nonempty and each is valid (`M4Out`, with `t = (k + 3) / 2`: a
  colored `t`-partition, or a trimmed Johnson structure on more than `t` points with cells
  disjoint from its points), has stage 14h's data shape `LkJ` when it is a Johnson leaf, is
  small, and has an orbit of at most `msCount k = 2^(129 (⌈log₂ k⌉ + 2)²)` elements under any
  group preserving the configuration (one element, the leaf being fixed, in the disconnected
  case). A trimmed leaf's orbit is at most the untrimmed one's (`ms_card_orbit_trim`), which
  `card_orbit_le_count` bounds by the count of `soj`.
* `RunsWithin.m4StructProg`: the run, at the explicit cost `m4StructCost` (the `soj` tree has
  size at most `sojZ k`, `ms_sojSz_le`), with the charges of `orbitalProg` from
  `BackendBounds` and those of the leaf stabilizer as the hypotheses `M4Charges` on the
  specific inputs.
* `m4Struct_spec`: `K` is valid of degree `N` and denotes exactly the preimage under `msPsi` of
  the stabilizer of the decoded leaf (so `K ≤ H` and `K` preserves the structure); the
  representatives are valid, form an `IsLeftCover` of `H` by `K`, and number at most
  `msCount k` (at most `1`, with `K = H`, in the disconnected case); the leaf is the first leaf
  (`msLeaf`), valid, of the data shape `LkJ` when Johnson, and small.
* The Johnson leaves are not shown `JValid` here: their indices are only known to be below `k`
  after stage 14h's extension (`lk_ext`, then `lk_jshape` and `jvalid_of_isJohnson`), which the
  step applies when it extends the structure from the window to the whole base.
* The hypotheses: `H` valid and base-invariant at `n' < N`, transitive on the window
  (`baseHom` form, as `orbitalModel_spec`), not doubly transitive
  (`¬ IsMultiplyPretransitive (baseHom …).range (Fin (N − n')) 2`), and `4 ≤ N − n'` (for
  `split_or_johnson`'s `t < k`).
* `wf_m4StructProg`: well-formedness.
-/

@[expose] public section

namespace GraphIso.Main

open Equiv MulAction Cost GraphIso GraphIso.Toolkit GraphIso.Programs GraphIso.SoJTree
  GraphIso.SoJProg GraphIso.SplitJohnson GraphIso.Case2b

/-! ### The program -/

section Programs

variable {D : Ty} {rec : Ty × Ty} {var : Ty → Type}

/-- **The structure of M4 and its stabilizer**: the orbital configuration of `H` on `[n', N)`,
its first leaf (components or `soj`), and the leaf's stabilizer with coset representatives. -/
def m4StructProg (n' : var .nat) (H : var (Ty.group D)) :
    Prog (groupSig D) rec var (.prod (Ty.group D) (.prod (.list Ty.perm) outTy)) :=
  .bind (.op1 .fst H) fun N => .bind (.op2 .sub N n') fun m =>
  .bind (rangeFromProg n' m) fun ps => .bind (.op1 .length ps) fun k =>
  .bind (Toolkit.orbitalProg n' H) fun C =>
  .bind (Case2b.leavesOfProg k C) fun ls =>
  .caseList ls
    (.bind (.op0 .nil) fun nil => .bind SoJTree.noneProg fun o =>
      .bind (.op2 .pair nil o) fun ro => .op2 .pair H ro)
    (fun o _ =>
      .bind (posProg N ps) fun pos =>
      .bind (.op1 .snd H) fun gd => .bind (.op1 .fst gd) fun gs =>
      .bind (SoJTree.leafStabProg N k pos ps gs o) fun kr =>
      .bind (.op1 .fst kr) fun K => .bind (.op1 .snd kr) fun reps =>
      .bind (.op2 .pair reps o) fun ro => .op2 .pair K ro)

end Programs

/-! ### The model -/

section Model

variable {D : Ty}

/-- The number `k` of points of the window `[n', N)`, as the length of its list. -/
abbrev msK (n' N : ℕ) : ℕ := (baseWin n' N).1.length

theorem msK_eq (n' N : ℕ) : msK n' N = N - n' := length_basePts n' N

/-- The leaves of the orbital configuration of `H` on `[n', N)`. -/
def msLeaves (O : Oracle (groupSig D)) (n' : ℕ) (H : GroupData D.denote) : List OutD :=
  leavesOfD (msK n' H.1) (orbitalModel O n' H)

/-- The first leaf (`noneD` if there is none). -/
def msLeaf (O : Oracle (groupSig D)) (n' : ℕ) (H : GroupData D.denote) : OutD :=
  (msLeaves O n' H).headD noneD

/-- The size of the orbit of a leaf under the generators restricted to `[n', N)`. -/
def msR (n' N : ℕ) (gs : GensData) (o : OutD) : ℕ :=
  leafR (msK n' N) (WinData.pos N (baseWin n' N)) (baseWin n' N).1 gs o

/-- The index maps of the generators on the orbit of a leaf. -/
def msImgs (n' N : ℕ) (gs : GensData) (o : OutD) : List (List ℕ) :=
  leafImgs (msK n' N) (WinData.pos N (baseWin n' N)) (baseWin n' N).1 gs o

/-- The stabilizer of a leaf and its coset representatives, as computed. -/
def msStab (O : Oracle (groupSig D)) (n' N : ℕ) (gs : GensData) (o : OutD) :
    GroupData D.denote × List PermData :=
  leafStabModel O N (msK n' N) (WinData.pos N (baseWin n' N)) (baseWin n' N).1 gs o

/-- **The value of `m4StructProg`**: the stabilizer `K`, the representatives, the leaf. -/
def m4StructModel (O : Oracle (groupSig D)) (n' : ℕ) (H : GroupData D.denote) :
    GroupData D.denote × (List PermData × OutD) :=
  match msLeaves O n' H with
  | [] => (H, ([], noneD))
  | o :: _ => ((msStab O n' H.1 H.2.1 o).1, ((msStab O n' H.1 H.2.1 o).2, o))

/-- The bound on the number of coset representatives: the count bound of `split_or_johnson`. -/
def msCount (k : ℕ) : ℕ := 2 ^ (129 * (Nat.clog 2 k + 2) ^ 2)

/-- **The cost of `m4StructProg`**: degree `N`, `k = N − n'` window points, `s` generators, the
charges of `orbitalProg`, and the bounds `sS`, `L` and charges of the leaf stabilizer. -/
def m4StructCost (N k s Btr Bstab Borb sS L Bge Bst Btr' Bgt : ℕ) : ℕ :=
  orbitalCost N k Btr Bstab Borb + leavesOfCost k (sojZ k) + (2 * N + 9 * k + 8) +
    (5 * k + 3) + (1000 * (N + k + s + msCount k + outB k ((k + 3) / 2) + 2) ^ 8 +
      sS * (11 * N + 13) + L * (11 * N + 14) + Bge + Bst + Btr' + Bgt) + k + 40

/-- The operations `m4StructProg` calls. -/
def m4StructOps (op : GroupOp) : Prop :=
  op = .orbitTransversal ∨ op = .stabilizer ∨ op = .orbits ∨ op = .generate

/-- **The charges of the leaf stabilizer** on the specific inputs (`RunsWithin.leafStabProg`),
with bounds `sS` on the stabilizer's generators and `L` on the transversal. -/
structure M4Charges (X : Ctx (groupSig D)) (n' N : ℕ) (gs : GensData) (o : OutD)
    (sS L Bge Bst Btr Bgt : ℕ) : Prop where
  ge : X.B.call GroupOp.generate (N + msR n' N gs o, os_extGens N (msR n' N gs o) gs
      (msImgs n' N gs o)) (osGroup X.O N (msR n' N gs o) gs (msImgs n' N gs o)) ≤ Bge
  st : X.B.call GroupOp.stabilizer (osGroup X.O N (msR n' N gs o) gs (msImgs n' N gs o), N)
      (osStab X.O N (msR n' N gs o) gs (msImgs n' N gs o)) ≤ Bst
  tr : X.B.call GroupOp.orbitTransversal
      (osGroup X.O N (msR n' N gs o) gs (msImgs n' N gs o), N)
      (osTrans X.O N (msR n' N gs o) gs (msImgs n' N gs o)) ≤ Btr
  gt : X.B.call GroupOp.generate (N, (osStab X.O N (msR n' N gs o) gs
      (msImgs n' N gs o)).2.1.map (PermData.truncTo N))
      (orbitStabModel X.O N (msR n' N gs o) gs (msImgs n' N gs o)).1 ≤ Bgt
  sS : (osStab X.O N (msR n' N gs o) gs (msImgs n' N gs o)).2.1.length ≤ sS
  L : (osTrans X.O N (msR n' N gs o) gs (msImgs n' N gs o)).length ≤ L

end Model

/-! ### The window and its restriction -/

section Bridge

variable {N n' : ℕ} {G : Subgroup (Perm (Fin N))}

theorem ms_win_valid (n' N : ℕ) : (baseWin n' N).Valid N :=
  WinData.valid_ofPoints (basePts_nodup n' N) fun _ hi => (mem_basePts.1 hi).2

theorem ms_win_inv (hinv : IsInvariant G (baseSet n' N)) :
    IsInvariant G ((baseWin n' N).denote N) := by
  unfold baseWin
  rw [denote_basePts]
  exact hinv

/-- **The restriction of `G` to the window `[n', N)`**, indexed by `Fin k` in list order. -/
def msPsi (G : Subgroup (Perm (Fin N))) (n' : ℕ) (hinv : IsInvariant G (baseSet n' N)) :
    ↥G →* Perm (Fin (msK n' N)) :=
  restrictHom (ms_win_inv hinv) (WinData.reindex (ms_win_valid n' N))

theorem ms_lt {j : ℕ} (hj : j < msK n' N) : j < N - n' := by
  rwa [msK_eq] at hj

theorem ms_getD_basePts {j : ℕ} (hj : j < N - n') : (basePts n' N).getD j 0 = n' + j := by
  simp [basePts, List.getD_eq_getElem?_getD, hj]

theorem ms_reindex_val (i : Fin (msK n' N)) :
    (((WinData.reindex (ms_win_valid n' N) i : _) : Fin N) : ℕ) = n' + i.val := by
  rw [WinData.reindex_val]
  exact ms_getD_basePts (ms_lt i.2)

/-- **The restriction agrees with the base action** on values. -/
theorem msPsi_val (hinv : IsInvariant G (baseSet n' N)) (g : ↥G) (j : Fin (msK n' N)) :
    ((msPsi G n' hinv g j : Fin _) : ℕ) = (baseHom G n' hinv g ⟨j.val, ms_lt j.2⟩ : ℕ) := by
  have h1 := congrArg Fin.val (restrictHom_apply (ms_win_inv hinv)
    (WinData.reindex (ms_win_valid n' N)) g j)
  have h2 := congrArg Fin.val (baseHom_apply (hG := hinv) g ⟨j.val, ms_lt j.2⟩)
  have hpos : (WinData.reindex (ms_win_valid n' N) j : Fin N) = basePos ⟨j.val, ms_lt j.2⟩ := by
    apply Fin.ext
    rw [ms_reindex_val]
    rfl
  rw [hpos, ms_reindex_val] at h1
  have h1' : n' + ((msPsi G n' hinv g j : Fin _) : ℕ) =
      ((g : Perm (Fin N)) (basePos ⟨j.val, ms_lt j.2⟩) : ℕ) := h1
  have h2' : n' + (baseHom G n' hinv g ⟨j.val, ms_lt j.2⟩ : ℕ) =
      ((g : Perm (Fin N)) (basePos ⟨j.val, ms_lt j.2⟩) : ℕ) := h2
  omega

end Bridge

/-! ### The orbital configuration -/

section Config

variable {Φ : Type} [Fintype Φ] [DecidableEq Φ]

omit [DecidableEq Φ] in
/-- **Orbital colourings are coherent.** -/
theorem ms_coherent2 {P : Type*} [Group P] [MulAction P Φ] (c : Φ → Φ → ℕ)
    (hc : ∀ u v u' v', c u v = c u' v' ↔ ∃ g : P, g • u = u' ∧ g • v = v') :
    Coherent.IsCoherent2 c := by
  have hg : ∀ (g : P) (u v : Φ), c (g • u) (g • v) = c u v :=
    fun g u v => ((hc u v _ _).mpr ⟨g, rfl, rfl⟩).symm
  refine ⟨fun x y x' y' hxy => ?_, fun x y x' y' hxy r s => ?_⟩
  · obtain ⟨g, hx, hy⟩ := (hc x y x' y').mp hxy
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← hx, ← hy, smul_left_cancel_iff]
    · exact (hc _ _ _ _).mpr ⟨g, hy, hx⟩
    · exact (hc _ _ _ _).mpr ⟨g, hx, hx⟩
    · exact (hc _ _ _ _).mpr ⟨g, hy, hy⟩
  · obtain ⟨g, hx, hy⟩ := (hc x y x' y').mp hxy
    refine Finset.card_nbij' (fun z => g • z) (fun z => g⁻¹ • z) (fun z hz => ?_)
      (fun z hz => ?_) (fun z _ => inv_smul_smul g z) (fun z _ => smul_inv_smul g z)
    · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hz ⊢
      rw [← hx, ← hy, hg, hg]
      exact hz
    · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hz ⊢
      rw [← hg g, ← hg g _ y, smul_inv_smul, hx, hy]
      exact hz

/-- **No disconnected colour: uniprimitive.** A homogeneous configuration that is not a clique
and has no disconnected colour graph is uniprimitive (as in `wlRel_split_or_uniprimitive`). -/
theorem ms_uniprimitive {c : Φ → Φ → ℕ} (hhom : Coherent.IsHomog Finset.univ c)
    (hncl : ¬ Coherent.IsClique c Finset.univ)
    (hd : ¬ (disconn Finset.univ c).Nonempty) : Coherent.IsUniprimitive Finset.univ c := by
  refine ⟨⟨hhom, fun r hr x _ y _ => ?_⟩, hncl⟩
  have hx : Coherent.comp Finset.univ c r x = Finset.univ := by
    by_contra hne
    exact hd ⟨r, Finset.mem_filter.2 ⟨hr, x, Finset.mem_univ _, hne⟩⟩
  have hy : y ∈ Coherent.comp Finset.univ c r x := by
    rw [hx]
    exact Finset.mem_univ _
  exact (Coherent.mem_comp.1 hy).2

theorem ms_isColPart_mono {α : Type*} [DecidableEq α] {V : Finset α} {t t' : ℕ}
    {p : CPart α} (h : IsColPart V t p) (ht : t ≤ t') : IsColPart V t' p :=
  { h with card_le := fun v hv => (h.card_le v hv).trans ht }

variable {D : Ty} {X : Ctx (groupSig D)} {DV : ℕ → GensData → D.denote → Prop}
  {N n' : ℕ} {gs : GensData} {d : D.denote}

/-- **The configuration on `Fin (N − n')`**: homogeneous, coherent, not a clique, for a
transitive, not doubly transitive base action. -/
theorem ms_config (hO : MeetsContractOn DV orbitalOps X.O) (hG : GroupValid DV N gs d)
    (hinv : IsInvariant (GensData.denote N gs) (baseSet n' N)) (hn : n' < N)
    (htr : ∀ γ δ : Fin (N - n'), ∃ g : ↥(GensData.denote N gs),
      baseHom (GensData.denote N gs) n' hinv g γ = δ)
    (h2 : ¬ IsMultiplyPretransitive (baseHom (GensData.denote N gs) n' hinv).range
      (Fin (N - n')) 2) :
    Coherent.IsCoherent2 (colOf (N - n') (orbitalModel X.O n' (N, gs, d))) ∧
      Coherent.IsCoh2On Finset.univ (colOf (N - n') (orbitalModel X.O n' (N, gs, d))) ∧
      Coherent.IsHomog Finset.univ (colOf (N - n') (orbitalModel X.O n' (N, gs, d))) ∧
      ¬ Coherent.IsClique (colOf (N - n') (orbitalModel X.O n' (N, gs, d))) Finset.univ := by
  have hc := orbitalModel_spec hO hG hinv hn htr
  have : IsPretransitive (baseHom (GensData.denote N gs) n' hinv).range (Fin (N - n')) :=
    ⟨fun x y => by
      obtain ⟨g, hg⟩ := htr x y
      exact ⟨⟨_, g, rfl⟩, hg⟩⟩
  obtain ⟨h1, h2', h3⟩ := Certificates.orbital_config h2
    (colOf (N - n') (orbitalModel X.O n' (N, gs, d))) hc
  exact ⟨ms_coherent2 _ hc, h1, h2', h3⟩

end Config

/-! ### The colours are the orbitals of the restriction -/

section Orbital

variable {D : Ty} {X : Ctx (groupSig D)} {DV : ℕ → GensData → D.denote → Prop}
  {N n' : ℕ} {gs : GensData} {d : D.denote}

/-- **The configuration's colours are the orbitals of `msPsi`.** -/
theorem ms_orbital (hO : MeetsContractOn DV orbitalOps X.O) (hG : GroupValid DV N gs d)
    (hinv : IsInvariant (GensData.denote N gs) (baseSet n' N)) (hn : n' < N)
    (htr : ∀ γ δ : Fin (N - n'), ∃ g : ↥(GensData.denote N gs),
      baseHom (GensData.denote N gs) n' hinv g γ = δ)
    (u v u' v' : Fin (msK n' N)) :
    colOf (msK n' N) (orbitalModel X.O n' (N, gs, d)) u v =
        colOf (msK n' N) (orbitalModel X.O n' (N, gs, d)) u' v' ↔
      ∃ g : ↥(GensData.denote N gs), msPsi _ n' hinv g u = u' ∧ msPsi _ n' hinv g v = v' := by
  have hk := msK_eq n' N
  have hs := orbitalModel_spec (X := X) hO hG hinv hn htr ⟨u.val, ms_lt u.2⟩
    ⟨v.val, ms_lt v.2⟩ ⟨u'.val, ms_lt u'.2⟩ ⟨v'.val, ms_lt v'.2⟩
  have e1 : u.val * msK n' N = u.val * (N - n') := congrArg (u.val * ·) hk
  have e2 : u'.val * msK n' N = u'.val * (N - n') := congrArg (u'.val * ·) hk
  simp only [colOf]
  rw [e1, e2, hs]
  constructor
  · rintro ⟨⟨σ, g, rfl⟩, h1, h2⟩
    refine ⟨g, Fin.ext ?_, Fin.ext ?_⟩
    · rw [msPsi_val]
      exact congrArg Fin.val h1
    · rw [msPsi_val]
      exact congrArg Fin.val h2
  · rintro ⟨g, h1, h2⟩
    refine ⟨⟨_, g, rfl⟩, Fin.ext ?_, Fin.ext ?_⟩
    · have := congrArg Fin.val h1
      rw [msPsi_val] at this
      exact this
    · have := congrArg Fin.val h2
      rw [msPsi_val] at this
      exact this

/-- **The restriction preserves the configuration.** -/
theorem ms_relab (hO : MeetsContractOn DV orbitalOps X.O) (hG : GroupValid DV N gs d)
    (hinv : IsInvariant (GensData.denote N gs) (baseSet n' N)) (hn : n' < N)
    (htr : ∀ γ δ : Fin (N - n'), ∃ g : ↥(GensData.denote N gs),
      baseHom (GensData.denote N gs) n' hinv g γ = δ) :
    ∀ σ ∈ (msPsi (GensData.denote N gs) n' hinv).range,
      relab2 σ (colOf (msK n' N) (orbitalModel X.O n' (N, gs, d))) =
        colOf (msK n' N) (orbitalModel X.O n' (N, gs, d)) := by
  rintro σ ⟨g, rfl⟩
  funext x y
  show colOf _ _ ((msPsi _ n' hinv g)⁻¹ • x) ((msPsi _ n' hinv g)⁻¹ • y) = colOf _ _ x y
  refine (ms_orbital hO hG hinv hn htr _ _ x y).2 ⟨g, ?_, ?_⟩
  · simp [Perm.smul_def]
  · simp [Perm.smul_def]

/-- **The configuration on the window**: coherent, homogeneous, not a clique. -/
theorem ms_config' (hO : MeetsContractOn DV orbitalOps X.O) (hG : GroupValid DV N gs d)
    (hinv : IsInvariant (GensData.denote N gs) (baseSet n' N)) (hn : n' < N)
    (htr : ∀ γ δ : Fin (N - n'), ∃ g : ↥(GensData.denote N gs),
      baseHom (GensData.denote N gs) n' hinv g γ = δ)
    (h2 : ¬ IsMultiplyPretransitive (baseHom (GensData.denote N gs) n' hinv).range
      (Fin (N - n')) 2) :
    Coherent.IsCoherent2 (colOf (msK n' N) (orbitalModel X.O n' (N, gs, d))) ∧
      Coherent.IsCoh2On Finset.univ (colOf (msK n' N) (orbitalModel X.O n' (N, gs, d))) ∧
      Coherent.IsHomog Finset.univ (colOf (msK n' N) (orbitalModel X.O n' (N, gs, d))) ∧
      ¬ Coherent.IsClique (colOf (msK n' N) (orbitalModel X.O n' (N, gs, d)))
        Finset.univ := by
  rw [msK_eq]
  exact ms_config hO hG hinv hn htr h2

end Orbital

/-! ### The leaves -/

section Leaves

/-- **A valid leaf of M4**, with `t = (k + 3) / 2`: a colored `t`-partition of the window, or
a trimmed Johnson structure on more than `t` points whose cells avoid its points. -/
def M4Out (k : ℕ) (o : OutD) : Prop :=
  (∃ p, decodeOut k o = some (.inl p) ∧ IsColPart Finset.univ ((k + 3) / 2) p) ∨
    ∃ J, decodeOut k o = some (.inr J) ∧ IsJohnson Finset.univ ((k + 3) / 2) J ∧
      (∀ v, v ∉ J.V0 → J.f v = ∅) ∧ ∀ A ∈ J.Λ, Disjoint A J.V0

/-- Trimming does not enlarge orbits. -/
theorem ms_card_orbit_trim {k : ℕ} (P : Subgroup (Perm (Fin k)))
    (x : Option (Out (Fin k))) :
    Nat.card (orbit P (Align.trimOut x)) ≤ Nat.card (orbit P x) := by
  have h : orbit P (Align.trimOut x) = Align.trimOut '' orbit P x := by
    ext y
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g • x, mem_orbit _ _, by
        show Align.trimOut ((g : Perm (Fin k)) • x) = (g : Perm (Fin k)) • Align.trimOut x
        exact Align.trimOut_smul _ _⟩
    · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
      exact ⟨g, by
        show (g : Perm (Fin k)) • Align.trimOut x = Align.trimOut ((g : Perm (Fin k)) • x)
        exact (Align.trimOut_smul _ _).symm⟩
  rw [h]
  exact Nat.card_image_le (Set.finite_range _)

variable {k : ℕ} {C : Array ℕ}

/-- **The components partition is fixed** by every permutation preserving the colouring. -/
theorem ms_comp_fixed {σ : Perm (Fin k)} (hσ : relab2 σ (colOf k C) = colOf k C) (r : ℕ) :
    σ • (⟨fun _ => 0, Coherent.comp Finset.univ (colOf k C) r⟩ : CPart (Fin k)) =
      ⟨fun _ => 0, Coherent.comp Finset.univ (colOf k C) r⟩ := by
  show CPart.mk _ _ = CPart.mk _ _
  congr 1
  funext v
  have h := comp_smul' σ Finset.univ (colOf k C) r v
  rw [Finset.smul_finset_univ, hσ] at h
  exact h.symm

/-- **The leaves of a configuration** (`leavesOfD`): under coherence, homogeneity, no clique and
`4 ≤ k`, the list is nonempty and every leaf is valid (`M4Out`), has the data shape of a
Johnson leaf, and has an orbit under any group `P` preserving the colouring of at most
`msCount k` elements (one element in the disconnected case). -/
theorem ms_leaves (hcoh : Coherent.IsCoherent2 (colOf k C))
    (hcoh' : Coherent.IsCoh2On Finset.univ (colOf k C))
    (hhom : Coherent.IsHomog Finset.univ (colOf k C))
    (hncl : ¬ Coherent.IsClique (colOf k C) Finset.univ) (hk4 : 4 ≤ k)
    (P : Subgroup (Perm (Fin k))) (hP : ∀ σ ∈ P, relab2 σ (colOf k C) = colOf k C) :
    leavesOfD k C ≠ [] ∧ ∀ o ∈ leavesOfD k C, M4Out k o ∧ (o.1 = 2 → LkJ k o) ∧
      outSize o ≤ outB k ((k + 3) / 2) ∧ Nat.card (orbit P (decodeOut k o)) ≤ msCount k ∧
      ((disconn Finset.univ (colOf k C)).Nonempty → Nat.card (orbit P (decodeOut k o)) ≤ 1 ∧
        ∀ σ ∈ P, σ • decodeOut k o = decodeOut k o) := by
  have hcard : (Finset.univ : Finset (Fin k)).card = k := by simp
  have hE : 1 ≤ msCount k := Nat.one_le_two_pow
  by_cases hd : (disconn Finset.univ (colOf k C)).Nonempty
  · -- the components partition
    have hdec := leavesOfD_decode_comp k C hd
    set r := (disconn Finset.univ (colOf k C)).min' hd
    have hpart := isColPart_comp hcoh' hhom ((disconn Finset.univ (colOf k C)).min'_mem hd)
    rw [hcard] at hpart
    have hfix : ∀ σ ∈ P, σ • (some (.inl ⟨fun _ => 0, Coherent.comp Finset.univ (colOf k C) r⟩) :
        Option (Out (Fin k))) = some (.inl ⟨fun _ => 0, Coherent.comp Finset.univ (colOf k C) r⟩) :=
      fun σ hσ => by
        show some (Sum.inl (σ • _)) = _
        rw [ms_comp_fixed (hP σ hσ)]
    refine ⟨fun h => by rw [h] at hdec; simp at hdec, fun o ho => ?_⟩
    have hdo : decodeOut k o = some (.inl ⟨fun _ => 0,
        Coherent.comp Finset.univ (colOf k C) r⟩) := by
      have := List.mem_map_of_mem (f := decodeOut k) ho
      rw [hdec, List.mem_singleton] at this
      exact this
    have horb : Nat.card (orbit P (decodeOut k o)) ≤ 1 := by
      have hsub : orbit P (decodeOut k o) ⊆ {decodeOut k o} := by
        rintro _ ⟨g, rfl⟩
        rw [Set.mem_singleton_iff, hdo]
        exact hfix _ g.2
      refine (Nat.card_mono (Set.finite_singleton _) hsub).trans ?_
      simp
    refine ⟨Or.inl ⟨_, hdo, ms_isColPart_mono hpart (by omega)⟩, lk_leaves_shape C o ho,
      outSize_leavesOfD k C o ho, horb.trans hE, fun _ => ⟨horb, fun σ hσ => ?_⟩⟩
    rw [hdo]
    exact hfix σ hσ
  · -- the trimmed leaves of `soj`
    have hnil : disconn Finset.univ (colOf k C) = ∅ := Finset.not_nonempty_iff_eq_empty.1 hd
    have hdec := leavesOfD_decode_soj k C hnil
    have hu := ms_uniprimitive hhom hncl hd
    obtain ⟨hlive, hcount, hval⟩ := split_or_johnson (Γ := Fin k) (t := (k + 3) / 2) hcoh hu
      (by simp only [Fintype.card_fin]; omega) (by simp only [Fintype.card_fin]; omega)
    simp only [Fintype.card_fin] at hcount
    have hpos := (CTree.meas_size_live hlive).2
    refine ⟨fun h => ?_, fun o ho => ?_⟩
    · rw [h] at hdec
      have h0 := congrArg Multiset.card hdec
      simp only [List.map_nil, Multiset.coe_nil, Multiset.card_zero, Multiset.card_map,
        CTree.card_leafMs] at h0
      omega
    have hmem : decodeOut k o ∈ ((soj (colOf k C) ((k + 3) / 2)).leafMs.map Align.trimOut) := by
      rw [← hdec]
      exact Multiset.mem_coe.2 (List.mem_map_of_mem ho)
    obtain ⟨x, hx, hxo⟩ := Multiset.mem_map.1 hmem
    have hreach := CTree.mem_leafMs.1 hx
    have hvx := CTree.allLeaves_iff_reach.1 hval x hreach
    have horb : Nat.card (orbit P (decodeOut k o)) ≤ msCount k := by
      rw [← hxo]
      exact (ms_card_orbit_trim P x).trans ((card_orbit_le_count hP hreach).trans hcount)
    refine ⟨?_, lk_leaves_shape C o ho, outSize_leavesOfD k C o ho, horb, fun h => absurd h hd⟩
    rcases x with _ | p | J
    · exact absurd hvx id
    · exact Or.inl ⟨p, hxo.symm, hvx⟩
    · refine Or.inr ⟨Align.trimJ J, hxo.symm, Align.isJohnson_trimJ hvx, fun v hv => ?_,
        fun A hA => ?_⟩
      · show (if v ∈ J.V0 then J.f v else ∅) = ∅
        exact ite_eq_right_iff.2 fun h => absurd h hv
      · exact Align.soj_johnson_disjoint _ _ hreach A hA

end Leaves

/-! ### The run -/

section Run

theorem ms_leavesOfCost_mono (m : ℕ) {sz sz' : ℕ} (h : sz ≤ sz') :
    leavesOfCost m sz ≤ leavesOfCost m sz' := by
  unfold leavesOfCost sojBranchCost
  have h1 := Nat.mul_le_mul_left ((m + 3) / 2 + 2) h
  have h2 := Nat.mul_le_mul_left (stepK m ((m + 3) / 2) ((m + 3) / 2) + 11) h1
  have h3 := Nat.mul_le_mul_right (trimCost m (outB m ((m + 3) / 2)) + 3) h
  omega

/-- **The `soj` tree that `leavesOfProg` builds is small** for a homogeneous coherent
configuration that is not a clique. -/
theorem ms_sojSz_le {k : ℕ} {C : Array ℕ} (hcoh : Coherent.IsCoherent2 (colOf k C))
    (hhom : Coherent.IsHomog Finset.univ (colOf k C))
    (hncl : ¬ Coherent.IsClique (colOf k C) Finset.univ) (hk4 : 4 ≤ k) :
    sojSz k C ≤ sojZ k := by
  unfold sojSz
  split
  · rename_i hnil
    have hd : ¬ (disconn Finset.univ (colOf k C)).Nonempty := by
      rw [disconn_wlCol, hnil]
      simp
    obtain ⟨hlive, hcount, -⟩ := split_or_johnson (Γ := Fin k) (t := (k + 3) / 2) hcoh
      (ms_uniprimitive hhom hncl hd) (by simp only [Fintype.card_fin]; omega)
      (by simp only [Fintype.card_fin]; omega)
    simp only [Fintype.card_fin] at hcount
    have hh := height_soj_le (colOf k C) ((k + 3) / 2)
    rw [Fintype.card_fin] at hh
    refine (CTree.size_le_of_live hlive).trans ?_
    unfold sojZ
    exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 (by omega)) hcount
  · exact Nat.zero_le _

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}
  {N n' : ℕ} {gs : GensData} {d : D.denote}

theorem ms_orbitalOps {op : GroupOp} (h : orbitalOps op) : m4StructOps op := by
  rcases h with h | h | h <;> simp [m4StructOps, h]

theorem ms_orbitStabOps {op : GroupOp} (h : orbitStabOps op) : m4StructOps op := by
  rcases h with h | h | h <;> simp [m4StructOps, h]

/-- The facts of the leaves of `H`'s configuration, for the restriction `msPsi`. -/
theorem ms_leaves_of (hO : MeetsContractOn DV m4StructOps X.O) (hG : GroupValid DV N gs d)
    (hinv : IsInvariant (GensData.denote N gs) (baseSet n' N)) (hn : n' < N)
    (htr : ∀ γ δ : Fin (N - n'), ∃ g : ↥(GensData.denote N gs),
      baseHom (GensData.denote N gs) n' hinv g γ = δ)
    (h2 : ¬ IsMultiplyPretransitive (baseHom (GensData.denote N gs) n' hinv).range
      (Fin (N - n')) 2) (hk4 : 4 ≤ N - n') :
    msLeaves X.O n' (N, gs, d) ≠ [] ∧ ∀ o ∈ msLeaves X.O n' (N, gs, d),
      M4Out (msK n' N) o ∧ (o.1 = 2 → LkJ (msK n' N) o) ∧
      outSize o ≤ outB (msK n' N) ((msK n' N + 3) / 2) ∧
      Nat.card (orbit (msPsi (GensData.denote N gs) n' hinv).range
        (decodeOut (msK n' N) o)) ≤ msCount (msK n' N) ∧
      ((disconn Finset.univ (colOf (msK n' N) (orbitalModel X.O n' (N, gs, d)))).Nonempty →
        Nat.card (orbit (msPsi (GensData.denote N gs) n' hinv).range
          (decodeOut (msK n' N) o)) ≤ 1 ∧
        ∀ σ ∈ (msPsi (GensData.denote N gs) n' hinv).range,
          σ • decodeOut (msK n' N) o = decodeOut (msK n' N) o) := by
  have hO' : MeetsContractOn DV orbitalOps X.O := fun op x h => hO op x (ms_orbitalOps h)
  obtain ⟨hcoh, hcoh', hhom, hncl⟩ := ms_config' hO' hG hinv hn htr h2
  exact ms_leaves hcoh hcoh' hhom hncl (by rw [msK_eq]; exact hk4) _
    (ms_relab hO' hG hinv hn htr)

/-- **The run of `m4StructProg`**, within `m4StructCost`. -/
theorem RunsWithin.m4StructProg (hO : MeetsContractOn DV m4StructOps X.O)
    (hPre : ∀ op x, m4StructOps op → GroupPre DV op x → X.Pre op x)
    {s : ℕ} {G₀ : Subgroup (Perm (Fin N))} (B : Solver.BackendBounds X DV N s G₀)
    (hG : GroupValid DV N gs d) (hs : gs.length ≤ s) (hG₀ : GensData.denote N gs ≤ G₀)
    (hinv : IsInvariant (GensData.denote N gs) (baseSet n' N)) (hn : n' < N)
    (htr : ∀ γ δ : Fin (N - n'), ∃ g : ↥(GensData.denote N gs),
      baseHom (GensData.denote N gs) n' hinv g γ = δ)
    (h2 : ¬ IsMultiplyPretransitive (baseHom (GensData.denote N gs) n' hinv).range
      (Fin (N - n')) 2) (hk4 : 4 ≤ N - n') {sS L Bge Bst Btr Bgt : ℕ}
    (hB : M4Charges X n' N gs (msLeaf X.O n' (N, gs, d)) sS L Bge Bst Btr Bgt) :
    RunsWithin X body (Main.m4StructProg n' (N, gs, d)) (m4StructModel X.O n' (N, gs, d))
      (m4StructCost N (N - n') gs.length B.Btr B.Bstab B.Borb sS L Bge Bst Btr Bgt) := by
  have hO' : MeetsContractOn DV orbitalOps X.O := fun op x h => hO op x (ms_orbitalOps h)
  have hOs : MeetsContractOn DV orbitStabOps X.O := fun op x h => hO op x (ms_orbitStabOps h)
  have hk := msK_eq n' N
  obtain ⟨hne, hall⟩ := ms_leaves_of hO hG hinv hn htr h2 hk4
  obtain ⟨hcoh, -, hhom, hncl⟩ := ms_config' hO' hG hinv hn htr h2
  have hsz := ms_sojSz_le hcoh hhom hncl (by rw [hk]; exact hk4)
  rcases hL : msLeaves X.O n' (N, gs, d) with _ | ⟨o, rest⟩
  · exact absurd hL hne
  have ho : o ∈ msLeaves X.O n' (N, gs, d) := by rw [hL]; exact List.mem_cons_self
  obtain ⟨-, -, hS, horb, -⟩ := hall o ho
  have hleaf : msLeaf X.O n' (N, gs, d) = o := by simp [msLeaf, hL]
  rw [hleaf] at hB
  have hr : msR n' N gs o ≤ msCount (msK n' N) := by
    unfold msR
    rw [leafOrbit_length_eq hG.1 (ms_win_valid n' N) (ms_win_inv hinv) o]
    exact horb
  have hval : m4StructModel X.O n' (N, gs, d) =
      ((msStab X.O n' N gs o).1, ((msStab X.O n' N gs o).2, o)) := by
    simp [m4StructModel, hL]
  rw [hval]
  have hls := RunsWithin.leafStabProg_of_outSize (X := X) (body := body) hOs
    (fun op x h hp => hPre op x (ms_orbitStabOps h) hp) hG.1 (ms_win_valid n' N)
    (ms_win_inv hinv) hS rfl rfl hB.ge hB.st hB.tr hB.gt
  have hLeaves : leavesOfD (msK n' N) (orbitalModel X.O n' (N, gs, d)) = o :: rest := hL
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.rangeFromProg n' (N - n'))
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.orbitalProg hO' (fun op x h hp => hPre op x (ms_orbitalOps h) hp) B hG
      hs hG₀ hinv hn)
    run_step (RunsWithin.leavesOfProg (msK n' N) (orbitalModel X.O n' (N, gs, d)))
    run_with Coherent.RunsWithin.caseList_eq_cons hLeaves _
    run_step (RunsWithin.posProg N (baseWin n' N))
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step hls
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim _ _
  case hc =>
    have hc1 := ms_leavesOfCost_mono (msK n' N) hsz
    have hpow : (N + msK n' N + gs.length + msR n' N gs o + outB (msK n' N)
        ((msK n' N + 3) / 2) + 2) ^ 8 ≤ (N + msK n' N + gs.length + msCount (msK n' N) +
          outB (msK n' N) ((msK n' N + 3) / 2) + 2) ^ 8 :=
      Nat.pow_le_pow_left (by omega) 8
    have h1 := Nat.mul_le_mul_right (11 * N + 13) hB.sS
    have h2' := Nat.mul_le_mul_right (11 * N + 14) hB.L
    simp only [Prim.cost, Args.head, List.length_map, List.length_range]
    unfold m4StructCost
    rw [← hk]
    simp only [msR, msImgs, msK] at hpow h1 h2' hc1 ⊢
    omega

end Run

/-! ### What the program computes -/

section Spec

variable {D : Ty} {X : Ctx (groupSig D)} {DV : ℕ → GensData → D.denote → Prop}
  {N n' : ℕ} {gs : GensData} {d : D.denote}

/-- **The structure of M4 and its stabilizer.** Under the hypotheses of
`RunsWithin.m4StructProg`, write `(K, reps, o) = m4StructModel` and `k = msK n' N = N − n'`:

* `K` has degree `N`, is valid, and denotes exactly the elements of `H` whose restriction
  `msPsi` to the window fixes the decoded leaf (so `K ≤ H` and `K` preserves the structure);
* the representatives are valid, form an `IsLeftCover` of `H` by `K`, and number at most
  `msCount k = 2^(129 (⌈log₂ k⌉ + 2)²)`; if a colour graph of the configuration is
  disconnected, at most `1`, and `K = H`;
* the leaf is valid (`M4Out k o`, with `t = (k + 3) / 2`), has the data shape `LkJ` when it is a
  Johnson leaf, is small, and is the first leaf of the configuration. -/
theorem m4Struct_spec (hO : MeetsContractOn DV m4StructOps X.O)
    (hPre : ∀ op x, m4StructOps op → GroupPre DV op x → X.Pre op x)
    (hG : GroupValid DV N gs d) (hinv : IsInvariant (GensData.denote N gs) (baseSet n' N))
    (hn : n' < N)
    (htr : ∀ γ δ : Fin (N - n'), ∃ g : ↥(GensData.denote N gs),
      baseHom (GensData.denote N gs) n' hinv g γ = δ)
    (h2 : ¬ IsMultiplyPretransitive (baseHom (GensData.denote N gs) n' hinv).range
      (Fin (N - n')) 2) (hk4 : 4 ≤ N - n') {sS L Bge Bst Btr Bgt : ℕ}
    (hB : M4Charges X n' N gs (msLeaf X.O n' (N, gs, d)) sS L Bge Bst Btr Bgt) :
    (m4StructModel X.O n' (N, gs, d)).1.1 = N ∧
      GroupValid DV N (m4StructModel X.O n' (N, gs, d)).1.2.1
        (m4StructModel X.O n' (N, gs, d)).1.2.2 ∧
      GensData.denote N (m4StructModel X.O n' (N, gs, d)).1.2.1 =
        ((MulAction.stabilizer (Perm (Fin (msK n' N)))
          (decodeOut (msK n' N) (m4StructModel X.O n' (N, gs, d)).2.2)).comap
            (msPsi (GensData.denote N gs) n' hinv)).map (GensData.denote N gs).subtype ∧
      (∀ x ∈ (m4StructModel X.O n' (N, gs, d)).2.1, PermData.Valid N x) ∧
      IsLeftCover (GensData.denote N gs)
        (GensData.denote N (m4StructModel X.O n' (N, gs, d)).1.2.1)
        (fun i : Fin (m4StructModel X.O n' (N, gs, d)).2.1.length =>
          PermData.denote N ((m4StructModel X.O n' (N, gs, d)).2.1.get i)) ∧
      (m4StructModel X.O n' (N, gs, d)).2.1.length ≤ msCount (msK n' N) ∧
      ((disconn Finset.univ (colOf (msK n' N) (orbitalModel X.O n' (N, gs, d)))).Nonempty →
        (m4StructModel X.O n' (N, gs, d)).2.1.length ≤ 1 ∧
          GensData.denote N (m4StructModel X.O n' (N, gs, d)).1.2.1 =
            GensData.denote N gs) ∧
      M4Out (msK n' N) (m4StructModel X.O n' (N, gs, d)).2.2 ∧
      ((m4StructModel X.O n' (N, gs, d)).2.2.1 = 2 →
        LkJ (msK n' N) (m4StructModel X.O n' (N, gs, d)).2.2) ∧
      outSize (m4StructModel X.O n' (N, gs, d)).2.2 ≤ outB (msK n' N) ((msK n' N + 3) / 2) ∧
      (m4StructModel X.O n' (N, gs, d)).2.2 = msLeaf X.O n' (N, gs, d) := by
  have hOs : MeetsContractOn DV orbitStabOps X.O := fun op x h => hO op x (ms_orbitStabOps h)
  obtain ⟨hne, hall⟩ := ms_leaves_of hO hG hinv hn htr h2 hk4
  rcases hL : msLeaves X.O n' (N, gs, d) with _ | ⟨o, rest⟩
  · exact absurd hL hne
  have ho : o ∈ msLeaves X.O n' (N, gs, d) := by rw [hL]; exact List.mem_cons_self
  obtain ⟨hM, hJ, hS, horb, hdis⟩ := hall o ho
  have hleaf : msLeaf X.O n' (N, gs, d) = o := by simp [msLeaf, hL]
  rw [hleaf] at hB
  have hval : m4StructModel X.O n' (N, gs, d) =
      ((msStab X.O n' N gs o).1, ((msStab X.O n' N gs o).2, o)) := by
    simp [m4StructModel, hL]
  rw [hval, hleaf]
  obtain ⟨-, hN, hv, hden, hrv, hcov, hlen⟩ := RunsWithin.leafStabProg (a := .unit) (b := .unit)
    (body := fun x => Prog.ret x) hOs (fun op x h hp => hPre op x (ms_orbitStabOps h) hp) hG.1
    (ms_win_valid n' N) (ms_win_inv hinv) o rfl rfl hB.ge hB.st hB.tr hB.gt
  have hr : leafR (baseWin n' N).1.length (WinData.pos N (baseWin n' N)) (baseWin n' N).1 gs o =
      Nat.card (orbit (msPsi (GensData.denote N gs) n' hinv).range
        (decodeOut (msK n' N) o)) :=
    leafOrbit_length_eq hG.1 (ms_win_valid n' N) (ms_win_inv hinv) o
  refine ⟨hN, hv, hden, hrv, hcov, ?_, fun hd => ?_, hM, hJ, hS, rfl⟩
  · exact hlen.trans (hr.trans_le horb)
  · obtain ⟨h1, hfix⟩ := hdis hd
    refine ⟨hlen.trans (hr.trans_le h1), ?_⟩
    have htop : (MulAction.stabilizer (Perm (Fin (msK n' N))) (decodeOut (msK n' N) o)).comap
        (msPsi (GensData.denote N gs) n' hinv) = ⊤ := by
      ext g
      simp only [Subgroup.mem_comap, MulAction.mem_stabilizer_iff, Subgroup.mem_top, iff_true]
      exact hfix _ ⟨g, rfl⟩
    show GensData.denote N (msStab X.O n' N gs o).1.2.1 = _
    rw [show (msStab X.O n' N gs o).1.2.1 = (leafStabModel X.O N (msK n' N)
      (WinData.pos N (baseWin n' N)) (baseWin n' N).1 gs o).1.2.1 from rfl, hden]
    change Subgroup.map _ ((MulAction.stabilizer (Perm (Fin (msK n' N)))
      (decodeOut (msK n' N) o)).comap (msPsi (GensData.denote N gs) n' hinv)) = _
    rw [htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

end Spec

/-! ### Well-formedness -/

section Wf

variable {D : Ty} {rec : Ty × Ty} {var₁ var₂ : Ty → Type} {r : Bool} {Γ : WfCtx var₁ var₂}

theorem ms_wf_rangeFromProg {a₁ k₁ : var₁ .nat} {a₂ k₂ : var₂ .nat}
    (ha : ⟨.nat, a₁, a₂⟩ ∈ Γ) (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ) :
    Prog.Wf (S := groupSig D) (rec := rec) r Γ (rangeFromProg a₁ k₁) (rangeFromProg a₂ k₂) := by
  unfold rangeFromProg mapList
  prog_wf

theorem ms_wf_posProg {n₁ : var₁ .nat} {n₂ : var₂ .nat} {l₁ : var₁ (.list .nat)}
    {l₂ : var₂ (.list .nat)} (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (hl : ⟨.list .nat, l₁, l₂⟩ ∈ Γ) :
    Prog.Wf (S := groupSig D) (rec := rec) r Γ (posProg n₁ l₁) (posProg n₂ l₂) := by
  unfold posProg mapList
  prog_wf

theorem wf_m4StructProg {n₁ : var₁ .nat} {n₂ : var₂ .nat} {H₁ : var₁ (Ty.group D)}
    {H₂ : var₂ (Ty.group D)} (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (hH : ⟨Ty.group D, H₁, H₂⟩ ∈ Γ) :
    Prog.Wf (S := groupSig D) (rec := rec) r Γ (m4StructProg n₁ H₁) (m4StructProg n₂ H₂) := by
  unfold m4StructProg
  refine .bind (.prim _ (.cons hH .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) (.cons (by simp [hn]) .nil))) fun _ _ =>
    .bind (ms_wf_rangeFromProg (by simp [hn]) (by simp)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (wf_orbitalProg (by simp [hn]) (by simp [hH])) fun _ _ =>
    .bind (wf_leavesOfProg (by simp) (by simp)) fun _ _ =>
    .caseList (by simp) ?_ fun _ _ _ _ => ?_
  · exact .bind (.prim _ .nil) fun _ _ => .bind wf_noneProg fun _ _ =>
      .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ =>
      .prim _ (.cons (by simp [hH]) (.cons (by simp) .nil))
  · exact .bind (ms_wf_posProg (by simp) (by simp)) fun _ _ =>
      .bind (.prim _ (.cons (by simp [hH]) .nil)) fun _ _ =>
      .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
      .bind (wf_leafStabProg (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))
        fun _ _ =>
      .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
      .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
      .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ =>
      .prim _ (.cons (by simp) (.cons (by simp) .nil))

end Wf

end GraphIso.Main
