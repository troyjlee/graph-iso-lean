module

public import GraphIso.Certificates.Aggregate
public import GraphIso.Certificates.Relabel

/-!
# The paired beard

Stage 14e, item 1 (`PLAN-14.md` §9), at the level of milestone 13's model
(`GraphIso/Certificates/`). Babai compares local certificates by running the beard on
`(x, A)` and `(x', A')` in lockstep. After `i` steps the candidates form the coset
`pairCoset φ A A' x x' i`: the elements of `G` that map `A` to `A'` through `φ`, every window
`W_j` (`j ≤ i`) of `x` at `A` onto the window `W'_j` of `x'` at `A'`, and `x` to `x'` on `W_i`.

* `pairCoset_self`: for `x' = x` and `A' = A` it is the beard's group `H_i` (`beardG`).
* `pairCoset_eq_smul`: it is a left coset of `H_i` when it is not empty.
* `beardG_conj`: an element of it conjugates `H_i` to the group of `x'` at `A'`, so the lockstep
  needs only one beard: the affected points of `x'` are the images of those of `x`.
* `pairCoset_succ`: each step keeps the elements mapping `x` to `x'` on the next window, a
  string-isomorphism coset on the newly affected points.
* `certIso_iff`: milestone 13's equivalence of certificates holds exactly when the final coset
  contains an element mapping the tuple `T` to `T'`.
-/

@[expose] public section

namespace GraphIso.Certificates

open Equiv MulAction Pointwise

variable {Ω Γ : Type} [Fintype Ω] [DecidableEq Ω] [Fintype Γ] [DecidableEq Γ]
variable {G : Subgroup (Perm Ω)} (φ : G →* Perm Γ) {L : Type*}

/-- The beard's group after `i` steps, as a subgroup of `G`. -/
def beardG (A : Finset Γ) (x : Ω → L) (i : ℕ) : Subgroup G :=
  (beard φ A x i).2.map (stabA φ A).subtype

/-- **The paired beard's coset after `i` steps.** -/
def pairCoset (A A' : Finset Γ) (x x' : Ω → L) (i : ℕ) : Set G :=
  {g | φ g • A = A' ∧ (∀ j ≤ i, g • (beard φ A x j).1 = (beard φ A' x' j).1) ∧
    ∀ u ∈ (beard φ A x i).1, x' (g • u) = x u}

/-! ### Helpers -/

omit [Fintype Ω] [DecidableEq Ω] in
theorem pb_autW_congr {M : Type*} [Group M] [MulAction M Ω] (H : Subgroup M) (W : Set Ω)
    {x₁ x₂ : Ω → L} (h : ∀ u ∈ W, x₁ u = x₂ u) : autW H W x₁ = autW H W x₂ := by
  ext g
  rw [mem_autW, mem_autW]
  refine and_congr Iff.rfl ⟨fun ⟨hW, hx⟩ => ⟨hW, fun u hu => ?_⟩,
    fun ⟨hW, hx⟩ => ⟨hW, fun u hu => ?_⟩⟩
  · have hgu : g • u ∈ W := by rw [← hW]; exact Set.smul_mem_smul_set hu
    rw [← h _ hgu, ← h _ hu]
    exact hx u hu
  · have hgu : g • u ∈ W := by rw [← hW]; exact Set.smul_mem_smul_set hu
    rw [h _ hgu, h _ hu]
    exact hx u hu

omit [Fintype Ω] [DecidableEq Ω] [Fintype Γ] in
/-- **Locality**: the beard up to step `i` reads the string only on its `i`-th window. -/
theorem pb_beard_congr (A : Finset Γ) {x₁ x₂ : Ω → L} {i : ℕ}
    (h : ∀ u ∈ (beard φ A x₁ i).1, x₁ u = x₂ u) :
    ∀ j ≤ i, beard φ A x₁ j = beard φ A x₂ j := by
  intro j hj
  induction j with
  | zero => rfl
  | succ j ih =>
    have ih := ih (by omega)
    rw [beard_succ, beard_succ, ih]
    refine Prod.ext rfl ?_
    show autW (beard φ A x₂ j).2 _ x₁ = autW (beard φ A x₂ j).2 _ x₂
    refine pb_autW_congr _ _ fun u hu => h u ?_
    have hu' : u ∈ (beard φ A x₁ (j + 1)).1 := by
      rw [beard_succ, ih]
      exact hu
    exact beardW_mono φ A x₁ hj hu'

omit [Fintype Ω] [DecidableEq Ω] [Fintype Γ] in
/-- The beard's group after `i` steps: the elements of `G_A` preserving every window up to
step `i` and the string on the `i`-th. -/
theorem pb_mem_beard (A : Finset Γ) (x : Ω → L) (i : ℕ) (h : stabA φ A) :
    h ∈ (beard φ A x i).2 ↔ (∀ j ≤ i, h • (beard φ A x j).1 = (beard φ A x j).1) ∧
      ∀ u ∈ (beard φ A x i).1, x (h • u) = x u := by
  induction i with
  | zero =>
    constructor
    · intro _
      refine ⟨fun j hj => ?_, fun u hu => ((Set.mem_empty_iff_false u).1 hu).elim⟩
      obtain rfl : j = 0 := by omega
      show h • (∅ : Set Ω) = ∅
      exact Set.smul_set_empty
    · intro _
      exact Subgroup.mem_top h
  | succ i ih =>
    rw [beardH_succ, mem_autW, ih]
    constructor
    · rintro ⟨⟨hW, -⟩, hW', hx'⟩
      refine ⟨fun j hj => ?_, hx'⟩
      rcases Nat.lt_or_ge j (i + 1) with hlt | hge
      · exact hW j (by omega)
      · obtain rfl : j = i + 1 := by omega
        exact hW'
    · rintro ⟨hW, hx⟩
      exact ⟨⟨fun j hj => hW j (by omega),
        fun u hu => hx u (beardW_mono φ A x (Nat.le_succ i) hu)⟩, hW (i + 1) le_rfl, hx⟩

omit [Fintype Ω] [DecidableEq Ω] [Fintype Γ] in
theorem pb_mem_beardG {A : Finset Γ} {x : Ω → L} {i : ℕ} {g : G} :
    g ∈ beardG φ A x i ↔ φ g • A = A ∧
      (∀ j ≤ i, g • (beard φ A x j).1 = (beard φ A x j).1) ∧
        ∀ u ∈ (beard φ A x i).1, x (g • u) = x u := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h.2, (pb_mem_beard φ A x i h).1 hh⟩
  · rintro ⟨hA, hrest⟩
    exact ⟨⟨g, hA⟩, (pb_mem_beard φ A x i ⟨g, hA⟩).2 hrest, rfl⟩

omit [Fintype Ω] [DecidableEq Ω] [Fintype Γ] in
/-- If `g` maps `x` to `x'` on the `i`-th window, the beard of `x'` at `φ g • A` up to step `i`
is that of the relabelled string `smulStr g x`. -/
theorem pb_beard_smulStr {A : Finset Γ} {x x' : Ω → L} {i : ℕ} {g : G}
    (hx : ∀ u ∈ (beard φ A x i).1, x' (g • u) = x u) :
    ∀ j ≤ i, beard φ (φ g • A) (smulStr g x) j = beard φ (φ g • A) x' j := by
  refine pb_beard_congr φ (φ g • A) fun v hv => ?_
  rw [beard_conjStab] at hv
  obtain ⟨u, hu, rfl⟩ := Set.mem_smul_set.1 hv
  simp only [smulStr, inv_smul_smul]
  exact (hx u hu).symm

omit [Fintype Ω] [DecidableEq Ω] [Fintype Γ] in
theorem pairCoset_self (A : Finset Γ) (x : Ω → L) (i : ℕ) :
    pairCoset φ A A x x i = (beardG φ A x i : Set G) := by
  ext g
  show _ ↔ g ∈ beardG φ A x i
  exact (pb_mem_beardG φ).symm

omit [Fintype Ω] [DecidableEq Ω] [Fintype Γ] in
theorem pairCoset_eq_smul {A A' : Finset Γ} {x x' : Ω → L} {i : ℕ} {σ : G}
    (hσ : σ ∈ pairCoset φ A A' x x' i) :
    pairCoset φ A A' x x' i = σ • (beardG φ A x i : Set G) := by
  obtain ⟨hA, hW, hx⟩ := hσ
  ext g
  rw [Set.mem_smul_set]
  constructor
  · rintro ⟨hgA, hgW, hgx⟩
    have hWi : (σ⁻¹ * g) • (beard φ A x i).1 = (beard φ A x i).1 := by
      rw [mul_smul, hgW i le_rfl, ← hW i le_rfl, inv_smul_smul]
    refine ⟨σ⁻¹ * g, (pb_mem_beardG φ).2 ⟨?_, fun j hj => ?_, fun u hu => ?_⟩, ?_⟩
    · rw [map_mul, mul_smul, hgA, map_inv, inv_smul_eq_iff, hA]
    · rw [mul_smul, hgW j hj, ← hW j hj, inv_smul_smul]
    · have hv : (σ⁻¹ * g) • u ∈ (beard φ A x i).1 := by
        rw [← hWi]
        exact Set.smul_mem_smul_set hu
      rw [← hx _ hv, ← mul_smul, mul_inv_cancel_left]
      exact hgx u hu
    · rw [smul_eq_mul, mul_inv_cancel_left]
  · rintro ⟨h, hh, rfl⟩
    obtain ⟨hhA, hhW, hhx⟩ := (pb_mem_beardG φ).1 (SetLike.mem_coe.1 hh)
    refine ⟨?_, fun j hj => ?_, fun u hu => ?_⟩
    · rw [smul_eq_mul, map_mul, mul_smul, hhA, hA]
    · rw [smul_eq_mul, mul_smul, hhW j hj, hW j hj]
    · have hv : h • u ∈ (beard φ A x i).1 := by
        rw [← hhW i le_rfl]
        exact Set.smul_mem_smul_set hu
      rw [smul_eq_mul, mul_smul, hx _ hv, hhx u hu]

omit [Fintype Ω] [DecidableEq Ω] [Fintype Γ] in
/-- **The lockstep needs one beard**: an element of the paired coset conjugates the beard's
group of `x` at `A` onto that of `x'` at `A'`. -/
theorem beardG_conj {A A' : Finset Γ} {x x' : Ω → L} {i : ℕ} {σ : G}
    (hσ : σ ∈ pairCoset φ A A' x x' i) :
    beardG φ A' x' i = (beardG φ A x i).map (MulAut.conj σ).toMonoidHom := by
  obtain ⟨hA, -, hx⟩ := hσ
  subst hA
  have h : beard φ (φ σ • A) x' i =
      (σ • (beard φ A x i).1, (beard φ A x i).2.map (conjStab φ σ A).toMonoidHom) := by
    rw [← pb_beard_smulStr φ hx i le_rfl, beard_conjStab]
  unfold beardG
  rw [h]
  exact map_conjStab_subtype φ σ A _

omit [Fintype Ω] [DecidableEq Ω] [Fintype Γ] in
/-- The windows correspond too: an element of the paired coset maps every window of `x` at `A`
up to step `i + 1` onto that of `x'` at `A'`. -/
theorem beardW_succ_conj {A A' : Finset Γ} {x x' : Ω → L} {i : ℕ} {σ : G}
    (hσ : σ ∈ pairCoset φ A A' x x' i) :
    σ • (beard φ A x (i + 1)).1 = (beard φ A' x' (i + 1)).1 := by
  obtain ⟨hA, -, hx⟩ := hσ
  subst hA
  have h := pb_beard_smulStr φ hx i le_rfl
  have h1 : (beard φ (φ σ • A) x' (i + 1)).1 =
      (beard φ (φ σ • A) (smulStr σ x) (i + 1)).1 := by
    rw [beard_succ, beard_succ, h]
    rfl
  rw [h1, beard_conjStab]

omit [Fintype Ω] [DecidableEq Ω] [Fintype Γ] in
/-- **One step of the paired beard** keeps the elements mapping `x` to `x'` on the next window.
-/
theorem pairCoset_succ (A A' : Finset Γ) (x x' : Ω → L) (i : ℕ) :
    pairCoset φ A A' x x' (i + 1) =
      {g | g ∈ pairCoset φ A A' x x' i ∧ ∀ u ∈ (beard φ A x (i + 1)).1, x' (g • u) = x u} := by
  ext g
  constructor
  · rintro ⟨hA, hW, hx⟩
    exact ⟨⟨hA, fun j hj => hW j (by omega),
      fun u hu => hx u (beardW_mono φ A x (Nat.le_succ i) hu)⟩, hx⟩
  · rintro ⟨hg, hx⟩
    refine ⟨hg.1, fun j hj => ?_, hx⟩
    rcases Nat.lt_or_ge j (i + 1) with hlt | hge
    · exact hg.2.1 j (by omega)
    · obtain rfl : j = i + 1 := by omega
      exact beardW_succ_conj φ hg

omit [DecidableEq Ω] [Fintype Γ] in
/-- **Certificates are compared by the paired beard.** -/
theorem certIso_iff (x x' : Ω → L) {k : ℕ} (T T' : Fin k → Γ) :
    CertIso φ x x' T T' ↔
      ∃ g ∈ pairCoset φ (Finset.univ.image T) (Finset.univ.image T') x x' (Fintype.card Ω),
        ∀ i, φ g (T i) = T' i := by
  constructor
  · rintro ⟨g, hT, -, hx⟩
    have hx' : ∀ u ∈ (beard φ (Finset.univ.image T) x (Fintype.card Ω)).1,
        x' (g • u) = x u := hx
    have hA : φ g • Finset.univ.image T = Finset.univ.image T' := by
      rw [Finset.smul_finset_def, Finset.image_image]
      congr 1
      funext i
      exact hT i
    refine ⟨g, ⟨hA, fun j hj => ?_, hx'⟩, hT⟩
    rw [← hA, ← pb_beard_smulStr φ hx' j hj, beard_conjStab]
  · rintro ⟨g, ⟨-, hW, hx⟩, hT⟩
    exact ⟨g, hT, hW _ le_rfl, hx⟩

end GraphIso.Certificates
