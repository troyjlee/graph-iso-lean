module

public import GraphIso.Recursion.Coarsen
public import GraphIso.Recursion.Progress
public import Mathlib.Tactic.Linarith
public import GraphIso.Case2b.Tree

/-!
# The structure-derived hint

Stage 14j-1, item 4 (`PLAN-14.md` §14.1), at the level of the model of stage 14a. A macro-step
that reduces the group (M4, M5) keeps the original hint `(Γ, ψ, lab)` of a transitive instance
on the window `W`; the reduced group `K ≤ M` preserves a structure on the base. Before
recursing on a `K`-orbit `O` of the window, the step coarsens the hint, so that the child meets
the condition of `pot_step` (a hint on a base of at most `3m/4` points, `m = |Γ|`, or no hint on
at most `|W|/2` points). `Derived ψ W O lab K` lists what the child gets:

* `noHint`: the labels are constant on `O`, so `2 |O| ≤ |W|` (`card_le_of_const`, which uses
  that `M` is transitive on `W`, the invariant of hinted instances).
* `inter`: a `ψ(K)`-invariant set `Γ'` of at most `3m/4` points on which the labels are not
  constant: `lab ∩ Γ'` is a hint for `K` on `O` (`inter_isHint`, from `hint_inter`).
* `blocks`: a base orbit `Γ'` of `ψ(K)` (so `|Γ'| ≤ m`) with a `ψ(K)`-invariant block system
  `Ψ` of at least two blocks of at least two points each, on which the labels `lab ∩ Γ'` are not
  constant. Then:
  - if some label is not equidistributed over `Ψ`, the block labels are a hint on `Ψ`, a base
    of `|Ψ| ≤ |Γ'|/2 ≤ m/2` points (`blocks_label_isHint`, M2a);
  - otherwise, after the reduction to the stabilizer of a block `B₀` (branching factor `|Ψ|`),
    `lab ∩ B₀` is a hint on every orbit, a base of `|B₀| ≤ |Γ'|/2 ≤ m/2` points
    (`blocks_stab_isHint`, M2b).
* `johnUnion`: the Johnson union is a hint on the cells `Λ`, `4 |Λ| ≤ 3m`
  (`johnUnion_isHint`, from `hint_jUnion`).
* `johnFallback`: the labels outside `V₀` and the Johnson union are constant on `O`; after the
  reduction to the pointwise stabilizer of the cells of the union (the Johnson fallback), the
  labels are constant on every orbit, so each has at most `|W|/2` points (`johnFallback_half`,
  from `fix_of_jUnion_const`).

So every outcome meets `pot_step`'s condition: `4 m' ≤ 3 m` with a hint (`inter`, `johnUnion`;
`2 m' ≤ m` for `blocks`), or no hint with `2 |O| ≤ |W|` (`noHint`, `johnFallback` after its
reduction). The two reductions inside the outcomes (M2b with factor `|Ψ| ≤ m/2`, the Johnson
fallback) add their factors to the macro-step's.

The three structures:

* `derived_colPart`: `K` preserves a colored `t`-partition of `Γ` with `4t ≤ 3m` (and `m ≥ 2`);
  the outcome is `noHint`, `inter` or `blocks` (`colPart_orbit`);
* `derived_johnson`: `K` preserves a Johnson structure `IsJohnson univ t J` with `m ≤ 4t` (and
  `m ≥ 5`); the outcome is `noHint`, `inter` (on `Γ ∖ V₀`), `johnUnion` or `johnFallback`;
* `derived_cjohnson`: `K` preserves the pair of a Johnson structure and a coarse partition `q`
  of `Γ` whose classes outside `V₀` have at most `m/2` points (`PLAN-14.md` §14.1 item 5: the
  structure Cases 2b and 3 align); no bound between `m` and `t` is needed, and `inter` is on a
  class outside `V₀`, of at most `m/2` points;
* for partitions extended to `Γ` as in stages 14h and 14i, `4t ≤ 3m` holds when the leaf
  blocks and the rest have at most `3m/4` points each (`isColPart_ext_bound`, from stage 14h's
  `extPart_valid`, and `derived_extPart`);
* `derived_set`: `K` preserves a set `Φ` with `m < 2|Φ|`; the outcome is `noHint`, `inter` (on
  `Γ ∖ Φ`), or the labels are not constant on `O` only inside `Φ`. The last case gives no
  progress: alignment of the large orbit alone does not coarsen the hint, and Cases 2a and 2b
  must continue (the pullback, or the structure of Case 2b).
-/

@[expose] public section

namespace GraphIso.Main

open Equiv MulAction Pointwise GraphIso.Recursion GraphIso.SplitJohnson

variable {M Ω Γ : Type*} [Group M] [MulAction M Ω] [Fintype Γ] [DecidableEq Γ]
  {ψ : M →* Perm Γ} {W O : Finset Ω} {lab : Ω → Finset Γ}

/-- The base action of a subgroup. -/
abbrev psiK (ψ : M →* Perm Γ) (K : Subgroup M) : ↥K →* Perm Γ := ψ.comp K.subtype

/-- **What a child orbit `O` of the reduced group `K` gets** (see the module docstring). -/
inductive Derived (ψ : M →* Perm Γ) (W O : Finset Ω) (lab : Ω → Finset Γ) (K : Subgroup M) :
    Prop
  /-- Constant labels: no hint, at most half of the window. -/
  | noHint (hc : ¬ NonConst O lab) (hhalf : 2 * O.card ≤ W.card)
  /-- An invariant set of at most `3m/4` points on which the labels are not constant. -/
  | inter (Γ' : Finset Γ) (hinv : ∀ g : K, ∀ γ ∈ Γ', psiK ψ K g γ ∈ Γ')
      (hn : NonConst O fun u => lab u ∩ Γ') (hcard : 4 * Γ'.card ≤ 3 * Fintype.card Γ)
  /-- A base orbit with a block system of at least two blocks of at least two points. -/
  | blocks (Γ' : Finset Γ) (hinv : ∀ g : K, ∀ γ ∈ Γ', psiK ψ K g γ ∈ Γ')
      (hn : NonConst O fun u => lab u ∩ Γ')
      (htr : ∀ γ δ : ↥Γ', ∃ g : K, restrictHom (psiK ψ K) Γ' hinv g γ = δ)
      (Ψ : Finset (Finset ↥Γ')) (hΨ : IsBlockSys (restrictHom (psiK ψ K) Γ' hinv) Ψ)
      (h2 : ∀ B ∈ Ψ, 2 ≤ B.card) (hΨ2 : 2 ≤ Ψ.card)
      (hcard : 2 * Ψ.card ≤ Γ'.card) (hblk : ∀ B ∈ Ψ, 2 * B.card ≤ Γ'.card)
  /-- The Johnson union is not constant: a hint on the cells, at most `3m/4` of them. -/
  | johnUnion (J : JEmb Γ) (t : ℕ) (hJ : IsJohnson Finset.univ t J)
      (hinv : ∀ g : K, psiK ψ K g • J = J) (hn : NonConst O fun u => jUnion J (lab u))
      (hcard : 4 * J.Λ.card ≤ 3 * Fintype.card Γ)
  /-- The Johnson fallback: the labels outside `V₀` and the union are constant on `O`. -/
  | johnFallback (J : JEmb Γ) (t : ℕ) (hJ : IsJohnson Finset.univ t J)
      (hinv : ∀ g : K, psiK ψ K g • J = J) (hn : NonConst O lab)
      (hA : ¬ NonConst O fun u => lab u \ J.V0) (hU : ¬ NonConst O fun u => jUnion J (lab u))

/-! ### Helpers -/

omit [Fintype Γ] in
theorem dm_equivar (hh : Equivar ψ W lab) (K : Subgroup M) (hO : O ⊆ W) :
    Equivar (psiK ψ K) O lab :=
  fun g u hu => hh g u (hO hu)

omit [Fintype Γ] in
theorem dm_card_subLab {S B : Finset Γ} (hB : B ⊆ S) : (subLab S B).card = B.card := by
  rw [subLab, Finset.card_subtype, Finset.filter_true_of_mem fun x hx => hB hx]

omit [Fintype Γ] in
theorem dm_subLab_inj {S A B : Finset Γ} (hA : A ⊆ S) (hB : B ⊆ S)
    (h : subLab S A = subLab S B) : A = B := by
  have := subLab_eq_iff.1 h
  rwa [Finset.inter_eq_left.2 hA, Finset.inter_eq_left.2 hB] at this

omit [Fintype Γ] in
theorem dm_mem_subLab {S B : Finset Γ} {x : ↥S} : x ∈ subLab S B ↔ (x : Γ) ∈ B :=
  mem_subLab

/-! ### The hints of the outcomes -/

omit [Fintype Γ] in
/-- **`inter`**: the labels inside `Γ'` are a hint for `K` on `O`. -/
theorem inter_isHint (hh : Equivar ψ W lab) (K : Subgroup M) (hO : O ⊆ W) {Γ' : Finset Γ}
    (hinv : ∀ g : K, ∀ γ ∈ Γ', psiK ψ K g γ ∈ Γ') (hn : NonConst O fun u => lab u ∩ Γ') :
    IsHint (restrictHom (psiK ψ K) Γ' hinv) O fun u => subLab Γ' (lab u) :=
  hint_inter hinv (dm_equivar hh K hO) hn

omit [Fintype Γ] in
/-- **`blocks`, M2a**: if some label is not equidistributed over the blocks, the block labels
are a hint on the blocks. -/
theorem blocks_label_isHint (hh : Equivar ψ W lab) (K : Subgroup M) (hO : O ⊆ W)
    (hOinv : Invariant (↥K) O) {Γ' : Finset Γ} (hinv : ∀ g : K, ∀ γ ∈ Γ', psiK ψ K g γ ∈ Γ')
    (hn : NonConst O fun u => lab u ∩ Γ')
    (htr : ∀ γ δ : ↥Γ', ∃ g : K, restrictHom (psiK ψ K) Γ' hinv g γ = δ)
    {Ψ : Finset (Finset ↥Γ')} (hΨ : IsBlockSys (restrictHom (psiK ψ K) Γ' hinv) Ψ) {u₀ : Ω}
    (hu₀ : u₀ ∈ O) (hne : ¬ Equidist Ψ (subLab Γ' (lab u₀))) :
    IsHint (restrictHom (setAct (restrictHom (psiK ψ K) Γ' hinv)) Ψ hΨ.inv) O
      fun u => subLab Ψ (blockLabel Ψ (subLab Γ' (lab u))) :=
  hint_blockLabel hΨ htr hOinv (inter_isHint hh K hO hinv hn) hu₀ hne

omit [Fintype Γ] in
/-- **`blocks`, M2b**: if the labels are equidistributed over the blocks, then on every orbit
of the stabilizer of a block `B₀` the labels inside `B₀` are a hint on `B₀`. -/
theorem blocks_stab_isHint (hh : Equivar ψ W lab) (K : Subgroup M) (hO : O ⊆ W)
    (hOtr : Transitive (↥K) O) {Γ' : Finset Γ} (hinv : ∀ g : K, ∀ γ ∈ Γ', psiK ψ K g γ ∈ Γ')
    (hn : NonConst O fun u => lab u ∩ Γ')
    (htr : ∀ γ δ : ↥Γ', ∃ g : K, restrictHom (psiK ψ K) Γ' hinv g γ = δ)
    {Ψ : Finset (Finset ↥Γ')} (hΨ : IsBlockSys (restrictHom (psiK ψ K) Γ' hinv) Ψ) {u₀ : Ω}
    (hu₀ : u₀ ∈ O) (heq : Equidist Ψ (subLab Γ' (lab u₀))) {B₀ : Finset ↥Γ'} (hB₀ : B₀ ∈ Ψ)
    {O' : Finset Ω} (hO' : O' ⊆ O) (hO'ne : O'.Nonempty)
    (hO'inv : Invariant (↥(blockStab (restrictHom (psiK ψ K) Γ' hinv) B₀)) O') :
    IsHint (restrictHom ((restrictHom (psiK ψ K) Γ' hinv).comp
        (blockStab (restrictHom (psiK ψ K) Γ' hinv) B₀).subtype) B₀ (blockStab_inv B₀)) O'
      fun u => subLab B₀ (subLab Γ' (lab u)) :=
  hint_blockStab hΨ htr hOtr (inter_isHint hh K hO hinv hn) hu₀ heq hB₀ hO' hO'ne hO'inv

/-- **`johnUnion`**: the Johnson union is a hint on the cells. -/
theorem johnUnion_isHint (hh : Equivar ψ W lab) (K : Subgroup M) (hO : O ⊆ W) {J : JEmb Γ}
    {t : ℕ} (hJ : IsJohnson Finset.univ t J) (hinv : ∀ g : K, psiK ψ K g • J = J)
    (hn : NonConst O fun u => jUnion J (lab u)) :
    IsHint (restrictHom (setAct (psiK ψ K)) J.Λ (cells_inv hinv)) O
      fun u => subLab J.Λ (jUnion J (lab u)) :=
  hint_jUnion hJ hinv (dm_equivar hh K hO) hn

/-- **`johnFallback`**: an element of `K` fixing every cell of the union at `u₀` keeps every
point of `O` in its fibre. -/
theorem johnFallback_fix (hh : Equivar ψ W lab) (K : Subgroup M) (hO : O ⊆ W)
    (hOinv : Invariant (↥K) O) {J : JEmb Γ} {t : ℕ} (hJ : IsJohnson Finset.univ t J)
    (hinv : ∀ g : K, psiK ψ K g • J = J) (hA : ¬ NonConst O fun u => lab u \ J.V0)
    (hU : ¬ NonConst O fun u => jUnion J (lab u)) {u₀ : Ω} (hu₀ : u₀ ∈ O) {g : K}
    (hg : ∀ a ∈ jUnion J (lab u₀), psiK ψ K g • a = a) :
    ∀ u ∈ O, lab ((g : M) • u) = lab u := by
  have hfix := fix_of_jUnion_const hJ hinv hOinv (dm_equivar hh K hO) hA hU hu₀ hg
  intro u hu
  exact lab_smul_of_fix (dm_equivar hh K hO) hfix hu

/-- **`johnFallback`, after the reduction**: a part of `O` connected by elements fixing every
cell of the union has at most half of the window. -/
theorem johnFallback_half (hW : Invariant M W) (hT : Transitive M W) (hh : IsHint ψ W lab)
    (K : Subgroup M) (hO : O ⊆ W) (hOinv : Invariant (↥K) O) {J : JEmb Γ} {t : ℕ}
    (hJ : IsJohnson Finset.univ t J) (hinv : ∀ g : K, psiK ψ K g • J = J)
    (hA : ¬ NonConst O fun u => lab u \ J.V0) (hU : ¬ NonConst O fun u => jUnion J (lab u))
    {u₀ : Ω} (hu₀ : u₀ ∈ O) {O' : Finset Ω} (hO' : O' ⊆ O)
    (hconn : ∀ u ∈ O', ∀ v ∈ O', ∃ g : K, (∀ a ∈ jUnion J (lab u₀), psiK ψ K g • a = a) ∧
      (g : M) • u = v) :
    2 * O'.card ≤ W.card := by
  refine card_le_of_const hW hT hh (hO'.trans hO) ?_
  rintro ⟨u, hu, v, hv, huv⟩
  obtain ⟨g, hg, rfl⟩ := hconn u hu v hv
  exact huv (johnFallback_fix hh.equivar K hO hOinv hJ hinv hA hU hu₀ hg u (hO' hu)).symm

/-! ### The three structures -/

omit [Fintype Γ] [DecidableEq Γ] in
/-- The orbit of `γ₀` under `ψ(K)`, given as a finite set. -/
theorem dm_orbit_inv (K : Subgroup M) {Ob : Finset Γ} {γ₀ : Γ}
    (hmem : ∀ δ, δ ∈ Ob ↔ ∃ g : K, psiK ψ K g γ₀ = δ) :
    ∀ g : K, ∀ γ ∈ Ob, psiK ψ K g γ ∈ Ob := by
  intro g γ hγ
  obtain ⟨g', rfl⟩ := (hmem γ).1 hγ
  exact (hmem _).2 ⟨g * g', by rw [map_mul, Perm.mul_apply]⟩

omit [Fintype Γ] [DecidableEq Γ] in
theorem dm_orbit_tr (K : Subgroup M) {Ob : Finset Γ} {γ₀ : Γ}
    (hmem : ∀ δ, δ ∈ Ob ↔ ∃ g : K, psiK ψ K g γ₀ = δ) :
    ∀ γ ∈ Ob, ∀ δ ∈ Ob, ∃ g : K, psiK ψ K g γ = δ := by
  intro γ hγ δ hδ
  obtain ⟨g₁, rfl⟩ := (hmem γ).1 hγ
  obtain ⟨g₂, rfl⟩ := (hmem δ).1 hδ
  exact ⟨g₂ * g₁⁻¹, by rw [map_mul, Perm.mul_apply, map_inv, Perm.inv_def,
    Equiv.symm_apply_apply]⟩

omit [Fintype Γ] in
/-- A permutation preserving a colored partition moves colours and blocks along. -/
theorem dm_cpart_fix {p : CPart Γ} {σ : Perm Γ} (h : σ • p = p) (γ : Γ) :
    p.col (σ γ) = p.col γ ∧ p.blk (σ γ) = σ • p.blk γ := by
  constructor
  · have := congrArg (fun q : CPart Γ => q.col (σ γ)) h
    simp only [CPart.smul_col, Perm.smul_def, Perm.inv_def, Equiv.symm_apply_apply] at this
    exact this.symm
  · have := congrArg (fun q : CPart Γ => q.blk (σ γ)) h
    simp only [CPart.smul_blk, Perm.smul_def, Perm.inv_def, Equiv.symm_apply_apply] at this
    exact this.symm

/-- **A colored partition** with `4t ≤ 3m`: the outcome is `noHint`, `inter` or `blocks`. -/
theorem derived_colPart (hW : Invariant M W) (hT : Transitive M W) (hh : IsHint ψ W lab)
    (K : Subgroup M) (hO : O ⊆ W) {p : CPart Γ} {t : ℕ} (hp : IsColPart Finset.univ t p)
    (hpK : ∀ g : K, psiK ψ K g • p = p) (ht : 4 * t ≤ 3 * Fintype.card Γ)
    (hm : 2 ≤ Fintype.card Γ) : Derived ψ W O lab K := by
  classical
  by_cases hn : NonConst O lab
  swap
  · exact .noHint hn (card_le_of_const hW hT hh hO hn)
  obtain ⟨γ₀, -, hn₀⟩ := exists_nonConst_inter (O := O) (lab := lab) Finset.univ
    (fun γ₀ => Finset.univ.filter fun δ => ∃ g : K, psiK ψ K g γ₀ = δ)
    (fun γ => ⟨γ, Finset.mem_univ _, Finset.mem_filter.2 ⟨Finset.mem_univ _, 1, by simp⟩⟩) hn
  set Ob := Finset.univ.filter fun δ => ∃ g : K, psiK ψ K g γ₀ = δ with hOb
  have hmem : ∀ δ, δ ∈ Ob ↔ ∃ g : K, psiK ψ K g γ₀ = δ := fun δ => by simp [hOb]
  have hinv := dm_orbit_inv K hmem
  have htrOb := dm_orbit_tr K hmem
  have hcardOb : Ob.card ≤ Fintype.card Γ := Finset.card_le_univ _
  rcases Nat.lt_or_ge Ob.card 2 with hlt | hge
  · exact .inter Ob hinv hn₀ (by omega)
  have hP : ∀ σ ∈ (psiK ψ K).range, ∀ γ ∈ (Finset.univ : Finset Γ),
      p.col (σ γ) = p.col γ ∧ p.blk (σ γ) = σ • p.blk γ := by
    rintro σ ⟨g, rfl⟩ γ -
    exact dm_cpart_fix (hpK g) γ
  have hOinvP : ∀ σ ∈ (psiK ψ K).range, ∀ γ ∈ Ob, σ γ ∈ Ob := by
    rintro σ ⟨g, rfl⟩ γ hγ
    exact hinv g γ hγ
  have hOtrP : ∀ γ ∈ Ob, ∀ δ ∈ Ob, ∃ σ ∈ (psiK ψ K).range, σ γ = δ := by
    intro γ hγ δ hδ
    obtain ⟨g, hg⟩ := htrOb γ hγ δ hδ
    exact ⟨_, ⟨g, rfl⟩, hg⟩
  rcases colPart_orbit hp hP (Finset.subset_univ _) hOinvP hOtrP hge with h1 | h2 | h3
  · exact .inter Ob hinv hn₀ (by omega)
  · exact .inter Ob hinv hn₀ (by rw [Finset.card_univ] at h2; omega)
  obtain ⟨h2b, hbsz, hbinv⟩ := h3
  -- the blocks, inside `Ob`, and as subsets of the subtype
  set Ψ₀ := Ob.image fun γ => p.blk γ ∩ Ob with hΨ₀
  have hsub : ∀ B ∈ Ψ₀, B ⊆ Ob := by
    intro B hB
    obtain ⟨γ, -, rfl⟩ := Finset.mem_image.1 hB
    exact Finset.inter_subset_right
  have hdisj₀ : ∀ B ∈ Ψ₀, ∀ C ∈ Ψ₀, B ≠ C → Disjoint B C := by
    intro B hB C hC hBC
    obtain ⟨γ, -, rfl⟩ := Finset.mem_image.1 hB
    obtain ⟨δ, -, rfl⟩ := Finset.mem_image.1 hC
    rw [Finset.disjoint_left]
    intro x hxB hxC
    apply hBC
    have e1 := hp.blk_eq γ (Finset.mem_univ _) x (Finset.mem_inter.1 hxB).1
    have e2 := hp.blk_eq δ (Finset.mem_univ _) x (Finset.mem_inter.1 hxC).1
    rw [← e1, ← e2]
  set Ψ := Ψ₀.image (subLab Ob) with hΨ
  have hinj : Set.InjOn (subLab Ob) Ψ₀ := fun A hA B hB h =>
    dm_subLab_inj (hsub A hA) (hsub B hB) h
  have hΨcard : Ψ.card = Ψ₀.card := Finset.card_image_of_injOn hinj
  have hcardB : ∀ B ∈ Ψ, ∃ B₀ ∈ Ψ₀, B = subLab Ob B₀ ∧ B.card = B₀.card := by
    intro B hB
    obtain ⟨B₀, hB₀, rfl⟩ := Finset.mem_image.1 hB
    exact ⟨B₀, hB₀, rfl, dm_card_subLab (hsub B₀ hB₀)⟩
  have htr : ∀ γ δ : ↥Ob, ∃ g : K, restrictHom (psiK ψ K) Ob hinv g γ = δ := by
    intro γ δ
    obtain ⟨g, hg⟩ := htrOb γ γ.2 δ δ.2
    exact ⟨g, Subtype.ext (by rw [restrictHom_apply]; exact hg)⟩
  have hΨsys : IsBlockSys (restrictHom (psiK ψ K) Ob hinv) Ψ := by
    refine ⟨fun B hB => ?_, fun B hB C hC hBC => ?_, fun x => ?_, fun g B hB => ?_⟩
    · obtain ⟨B₀, hB₀, rfl, hc⟩ := hcardB B hB
      rw [← Finset.card_pos, hc]
      have := hbsz B₀ hB₀
      omega
    · obtain ⟨B₀, hB₀, rfl, -⟩ := hcardB B hB
      obtain ⟨C₀, hC₀, rfl, -⟩ := hcardB C hC
      have hd := hdisj₀ B₀ hB₀ C₀ hC₀ fun h => hBC (by rw [h])
      rw [Finset.disjoint_left]
      intro x hx hx'
      exact Finset.disjoint_left.1 hd (dm_mem_subLab.1 hx) (dm_mem_subLab.1 hx')
    · refine ⟨subLab Ob (p.blk x ∩ Ob), Finset.mem_image.2 ⟨_, Finset.mem_image.2
        ⟨x, x.2, rfl⟩, rfl⟩, dm_mem_subLab.2 (Finset.mem_inter.2 ⟨hp.mem_blk _
          (Finset.mem_univ _), x.2⟩)⟩
    · obtain ⟨B₀, hB₀, rfl, -⟩ := hcardB B hB
      rw [setAct_apply, ← subLab_smul]
      exact Finset.mem_image.2 ⟨_, hbinv _ ⟨g, rfl⟩ B₀ hB₀, rfl⟩
  have h2 : ∀ B ∈ Ψ, 2 ≤ B.card := by
    intro B hB
    obtain ⟨B₀, hB₀, -, hc⟩ := hcardB B hB
    rw [hc]
    exact hbsz B₀ hB₀
  have hΨ2 : 2 ≤ Ψ.card := by rw [hΨcard]; exact h2b
  have hcard : 2 * Ψ.card ≤ Ob.card := by
    have := card_blockSys_le hΨsys h2
    rwa [Fintype.card_coe] at this
  have hblk : ∀ B ∈ Ψ, 2 * B.card ≤ Ob.card := by
    intro B hB
    obtain ⟨C, hC, hCB⟩ := Finset.exists_mem_ne (by omega : 1 < Ψ.card) B
    obtain ⟨γ, hγ⟩ := hΨsys.nonempty B hB
    obtain ⟨δ, hδ⟩ := hΨsys.nonempty C hC
    obtain ⟨g, -, hgB⟩ := hΨsys.exists_smul_eq htr hB hC hγ hδ
    have hBC : B.card = C.card := by rw [← hgB, Finset.card_smul_finset]
    have hd := hΨsys.disj B hB C hC hCB.symm
    have hu := Finset.card_le_univ (B ∪ C)
    rw [Finset.card_union_of_disjoint hd, Fintype.card_coe] at hu
    omega
  exact .blocks Ob hinv hn₀ htr Ψ hΨsys h2 hΨ2 hcard hblk

omit [DecidableEq Γ] in
/-- The cells of a Johnson structure on `m ≥ 5` points: `4 |Λ| ≤ 3m` (from `card_cells`). -/
theorem dm_cells_bound {J : JEmb Γ} {t : ℕ} (hJ : IsJohnson Finset.univ t J)
    (hm : 5 ≤ Fintype.card Γ) : 4 * J.Λ.card ≤ 3 * Fintype.card Γ := by
  have hV0 : J.V0.card ≤ Fintype.card Γ := Finset.card_le_univ _
  have hc := card_cells hJ
  by_contra hlt
  push Not at hlt
  obtain ⟨L, hL⟩ : ∃ L, J.Λ.card = L + 1 := ⟨J.Λ.card - 1, by omega⟩
  rw [hL, Nat.add_sub_cancel] at hc
  rw [hL] at hlt
  nlinarith

/-- **A Johnson structure** with `m ≤ 4t`: the outcome is `noHint`, `inter` (on `Γ ∖ V₀`),
`johnUnion` or `johnFallback`. -/
theorem derived_johnson (hW : Invariant M W) (hT : Transitive M W) (hh : IsHint ψ W lab)
    (K : Subgroup M) (hO : O ⊆ W) {J : JEmb Γ} {t : ℕ} (hJ : IsJohnson Finset.univ t J)
    (hinv : ∀ g : K, psiK ψ K g • J = J) (hJt : Fintype.card Γ ≤ 4 * t)
    (hm : 5 ≤ Fintype.card Γ) : Derived ψ W O lab K := by
  classical
  by_cases hn : NonConst O lab
  swap
  · exact .noHint hn (card_le_of_const hW hT hh hO hn)
  have hV0 : J.V0.card ≤ Fintype.card Γ := Finset.card_le_univ _
  have hgt := hJ.card_gt
  by_cases hA : NonConst O fun u => lab u \ J.V0
  · refine .inter (Finset.univ \ J.V0) ?_ ?_ ?_
    · intro g γ hγ
      have hV := jemb_V0 hinv g⁻¹
      rw [Finset.mem_sdiff] at hγ ⊢
      refine ⟨Finset.mem_univ _, fun hgγ => hγ.2 ?_⟩
      have : psiK ψ K g⁻¹ (psiK ψ K g γ) ∈ psiK ψ K g⁻¹ • J.V0 :=
        Finset.smul_mem_smul_finset hgγ
      rwa [hV, map_inv, Perm.inv_def, Equiv.symm_apply_apply] at this
    · have he : ∀ u, lab u ∩ (Finset.univ \ J.V0) = lab u \ J.V0 := fun u => by
        ext x
        simp
      simpa only [he] using hA
    · rw [Finset.card_univ_sdiff]
      omega
  by_cases hU : NonConst O fun u => jUnion J (lab u)
  · exact .johnUnion J t hJ hinv hU (dm_cells_bound hJ hm)
  · exact .johnFallback J t hJ hinv hn hA hU

/-- **A Johnson structure aligned with a coarse partition** (`PLAN-14.md` §14.1 item 5): the
structure of Cases 2b and 3 is the pair of the Johnson structure and a canonical partition of
`Γ` (`{S, Φ ∖ S, Γ ∖ Φ}` in Case 2b, `{S, C, (Γ ∖ S) ∖ C}` in Case 3), given by colours `q`
preserved by `ψ(K)`, whose classes outside `V₀` have at most `m/2` points each. Then the
outcome is `noHint`, `inter` on such a class (`2|Γ'| ≤ m`), `johnUnion` or `johnFallback`; no
bound between `m` and `t` is needed. -/
theorem derived_cjohnson (hW : Invariant M W) (hT : Transitive M W) (hh : IsHint ψ W lab)
    (K : Subgroup M) (hO : O ⊆ W) {J : JEmb Γ} {t : ℕ} (hJ : IsJohnson Finset.univ t J)
    (hinv : ∀ g : K, psiK ψ K g • J = J) {q : Γ → ℕ}
    (hqK : ∀ g : K, ∀ γ, q (psiK ψ K g γ) = q γ)
    (hq : ∀ c, 2 * (Finset.univ.filter fun γ => γ ∉ J.V0 ∧ q γ = c).card ≤ Fintype.card Γ)
    (hm : 5 ≤ Fintype.card Γ) : Derived ψ W O lab K := by
  classical
  by_cases hn : NonConst O lab
  swap
  · exact .noHint hn (card_le_of_const hW hT hh hO hn)
  by_cases hA : NonConst O fun u => lab u \ J.V0
  · obtain ⟨i, -, hi⟩ := exists_nonConst_inter (O := O) (lab := fun u => lab u \ J.V0)
      (Finset.univ.image fun γ => if γ ∈ J.V0 then (none : Option ℕ) else some (q γ))
      (fun i => i.elim J.V0 fun c => Finset.univ.filter fun γ => γ ∉ J.V0 ∧ q γ = c)
      (fun γ => ⟨if γ ∈ J.V0 then none else some (q γ),
        Finset.mem_image_of_mem _ (Finset.mem_univ _), by
          by_cases hγ : γ ∈ J.V0 <;> simp [hγ]⟩) hA
    cases i with
    | none =>
      exfalso
      obtain ⟨u, -, v, -, huv⟩ := hi
      apply huv
      simp only [Option.elim]
      rw [Finset.sdiff_inter_self, Finset.sdiff_inter_self]
    | some c =>
      refine .inter (Finset.univ.filter fun γ => γ ∉ J.V0 ∧ q γ = c) ?_ ?_ ?_
      · intro g γ hγ
        have hV := jemb_V0 hinv g⁻¹
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hγ ⊢
        refine ⟨fun hgγ => hγ.1 ?_, by rw [hqK g γ]; exact hγ.2⟩
        have : psiK ψ K g⁻¹ (psiK ψ K g γ) ∈ psiK ψ K g⁻¹ • J.V0 :=
          Finset.smul_mem_smul_finset hgγ
        rwa [hV, map_inv, Perm.inv_def, Equiv.symm_apply_apply] at this
      · have he : ∀ u, (lab u \ J.V0) ∩
            (Finset.univ.filter fun γ => γ ∉ J.V0 ∧ q γ = c) =
            lab u ∩ (Finset.univ.filter fun γ => γ ∉ J.V0 ∧ q γ = c) := fun u => by
          ext x
          simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ,
            true_and]
          tauto
        simpa only [Option.elim, he] using hi
      · have := hq c
        omega
  by_cases hU : NonConst O fun u => jUnion J (lab u)
  · exact .johnUnion J t hJ hinv hU (dm_cells_bound hJ hm)
  · exact .johnFallback J t hJ hinv hn hA hU

/-- **The extended partitions of stages 14h and 14i**: a colored `t₀`-partition of `Fin m₀`
extended along `e : Fin m₀ ↪ Γ` (the rest one block) is a colored `max(t₀, r)`-partition of `Γ`,
`r` the size of the rest (stage 14h's `extPart_valid`). -/
theorem isColPart_ext_bound {m₀ : ℕ} (e : Fin m₀ ↪ Γ) {t₀ : ℕ} {p : CPart (Fin m₀)}
    (hp : IsColPart Finset.univ t₀ p) :
    IsColPart Finset.univ (max t₀ (Finset.univ \ Finset.univ.map e).card)
      (GraphIso.Case2b.extPart e p) :=
  GraphIso.Case2b.extPart_valid e hp

/-- **`derived_colPart` for the extended partitions**: it applies when the leaf blocks and the
rest have at most `3m/4` points each. -/
theorem derived_extPart (hW : Invariant M W) (hT : Transitive M W) (hh : IsHint ψ W lab)
    (K : Subgroup M) (hO : O ⊆ W) {m₀ : ℕ} (e : Fin m₀ ↪ Γ) {t₀ : ℕ} {p₀ : CPart (Fin m₀)}
    (hp : IsColPart Finset.univ t₀ p₀)
    (hpK : ∀ g : K, psiK ψ K g • GraphIso.Case2b.extPart e p₀ = GraphIso.Case2b.extPart e p₀)
    (ht₀ : 4 * t₀ ≤ 3 * Fintype.card Γ)
    (hr : 4 * (Finset.univ \ Finset.univ.map e).card ≤ 3 * Fintype.card Γ)
    (hm : 2 ≤ Fintype.card Γ) : Derived ψ W O lab K := by
  refine derived_colPart hW hT hh K hO (isColPart_ext_bound e hp) hpK ?_ hm
  rcases Nat.le_total t₀ (Finset.univ \ Finset.univ.map e).card with h | h
  · rw [max_eq_right h]
    exact hr
  · rw [max_eq_left h]
    exact ht₀

/-- **A large invariant set** `Φ` (`m < 2|Φ|`): the outcome is `noHint`, `inter` (on `Γ ∖ Φ`),
or the labels are not constant on `O` only inside `Φ`, which gives no progress. -/
theorem derived_set (hW : Invariant M W) (hT : Transitive M W) (hh : IsHint ψ W lab)
    (K : Subgroup M) (hO : O ⊆ W) {Φ : Finset Γ} (hΦK : ∀ g : K, psiK ψ K g • Φ = Φ)
    (hΦ : Fintype.card Γ < 2 * Φ.card) :
    Derived ψ W O lab K ∨
      (NonConst O (fun u => lab u ∩ Φ) ∧ ¬ NonConst O fun u => lab u \ Φ) := by
  classical
  by_cases hn : NonConst O lab
  swap
  · exact .inl (.noHint hn (card_le_of_const hW hT hh hO hn))
  have hΦc : Φ.card ≤ Fintype.card Γ := Finset.card_le_univ _
  by_cases hA : NonConst O fun u => lab u \ Φ
  · refine .inl (.inter (Finset.univ \ Φ) ?_ ?_ ?_)
    · intro g γ hγ
      have hV := hΦK g⁻¹
      rw [Finset.mem_sdiff] at hγ ⊢
      refine ⟨Finset.mem_univ _, fun hgγ => hγ.2 ?_⟩
      have : psiK ψ K g⁻¹ (psiK ψ K g γ) ∈ psiK ψ K g⁻¹ • Φ := Finset.smul_mem_smul_finset hgγ
      rwa [hV, map_inv, Perm.inv_def, Equiv.symm_apply_apply] at this
    · have he : ∀ u, lab u ∩ (Finset.univ \ Φ) = lab u \ Φ := fun u => by
        ext x
        simp
      simpa only [he] using hA
    · rw [Finset.card_univ_sdiff]
      omega
  · refine .inr ⟨?_, hA⟩
    obtain ⟨u, hu, v, hv, huv⟩ := hn
    refine ⟨u, hu, v, hv, fun h => huv ?_⟩
    have h' : lab u \ Φ = lab v \ Φ := by
      by_contra hne
      exact hA ⟨u, hu, v, hv, hne⟩
    ext x
    by_cases hx : x ∈ Φ
    · have := congrArg (x ∈ ·) h
      simpa [hx] using this
    · have := congrArg (x ∈ ·) h'
      simpa [hx] using this

end GraphIso.Main
