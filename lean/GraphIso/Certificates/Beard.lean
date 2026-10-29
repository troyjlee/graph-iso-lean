module

public import GraphIso.Certificates.Basic

/-!
# The beard: Babai's procedure LocalCertificates

Babai §10.1 (lines 01–05 of LocalCertificates; Helfgott §6.1.1). Starting from the empty window
and `H₀ = G_A`, as long as `ψ_A(H_i)` is a giant the window grows by the affected points
("growing the beard") and the group shrinks to the elements respecting `x` on the new window:
`W_{i+1} = W_i ∪ Aff(H_i)`, `H_{i+1} = Aut^{W_{i+1}}_{H_i}(x)`. Once `ψ_A(H_i)` is not a giant the
window stops growing.

* `beard φ A x n`: the pair `(W_n, H_n)`; `beardW`, `beardH`: the values after `|Ω|` steps.
* `beard_stable`: the iteration is constant from step `|Ω|` on.
* `beardH_le_autW`, `autW_univ_le_beard`: `W_n` is `H_n`-invariant and `H_n` respects `x` on
  it, and every automorphism of `x` in `G_A` lies in every `H_n` (the invariant behind
  Claim 10.1.7). `smul_beardW_succ`: `W_{n+1}` is `H_n`-invariant, since `H` permutes the points
  it affects (`smul_mem_aff`).
* `beardH_eq_autW`: the final group is `Aut_{G_A}(x^{W(A)})`.
* `aff_subset_beardW`: if `ψ_A(H(A))` is a giant, every affected point lies in `W(A)`.
-/

@[expose] public section

namespace GraphIso.Certificates

open Equiv MulAction Pointwise

variable {Ω Γ : Type} [Fintype Ω] [DecidableEq Ω] [Fintype Γ] [DecidableEq Γ]
variable {G : Subgroup (Perm Ω)} (φ : G →* Perm Γ) {L : Type*}

/-! ### Window groups -/

section autW

variable {M : Type*} [Group M] [MulAction M Ω] {H : Subgroup M} {W : Set Ω} {x : Ω → L}

omit [Fintype Ω] [DecidableEq Ω] in
theorem mem_autW {h : M} : h ∈ autW H W x ↔ h ∈ H ∧ h • W = W ∧ ∀ i ∈ W, x (h • i) = x i :=
  Iff.rfl

omit [Fintype Ω] [DecidableEq Ω] in
theorem autW_le : autW H W x ≤ H := fun _ hh => (mem_autW.1 hh).1

omit [Fintype Ω] [DecidableEq Ω] in
theorem autW_mono {H' : Subgroup M} (hH : H ≤ H') : autW H W x ≤ autW H' W x :=
  fun _ hh => mem_autW.2 ⟨hH (mem_autW.1 hh).1, (mem_autW.1 hh).2⟩

omit [Fintype Ω] [DecidableEq Ω] in
/-- A group already respecting `x` on `W` is its own window group. -/
theorem autW_eq_self (hH : H ≤ autW ⊤ W x) : autW H W x = H :=
  le_antisymm autW_le fun _ hh => mem_autW.2 ⟨hh, (mem_autW.1 (hH hh)).2⟩

omit [Fintype Ω] [DecidableEq Ω] [Fintype Γ] [DecidableEq Γ] in
/-- A set closed under a subgroup is mapped onto itself by each of its elements. -/
theorem smul_set_eq_of_forall (hW : ∀ h ∈ H, ∀ i ∈ W, h • i ∈ W) {h : M} (hh : h ∈ H) :
    h • W = W := by
  apply Set.Subset.antisymm
  · intro j hj
    obtain ⟨i, hi, rfl⟩ := Set.mem_smul_set.1 hj
    exact hW h hh i hi
  · intro i hi
    exact Set.mem_smul_set.2 ⟨h⁻¹ • i, hW _ (H.inv_mem hh) i hi, smul_inv_smul h i⟩

end autW

/-! ### Affected points are permuted by the group -/

omit [Fintype Ω] [DecidableEq Ω] [Fintype Γ] in
/-- If `j` is not affected by `H`, neither is `h • j` for `h ∈ H`: the stabilizers are conjugate
in `H`, and `Alt(A)` is normal in `Sym(A)`. -/
theorem le_map_stabilizer_smul {A : Finset Γ} {H : Subgroup (stabA φ A)} {h : stabA φ A}
    (hh : h ∈ H) {j : Ω}
    (hj : alternatingGroup A ≤ (H ⊓ stabilizer (stabA φ A) j).map (psiA φ A)) :
    alternatingGroup A ≤ (H ⊓ stabilizer (stabA φ A) (h • j)).map (psiA φ A) := by
  intro σ hσ
  have hτ : psiA φ A h⁻¹ * σ * (psiA φ A h⁻¹)⁻¹ ∈ alternatingGroup A :=
    (alternatingGroup.normal).conj_mem σ hσ _
  obtain ⟨k, hk, hkσ⟩ := Subgroup.mem_map.1 (hj hτ)
  rw [Subgroup.mem_inf, mem_stabilizer_iff] at hk
  refine Subgroup.mem_map.2 ⟨h * k * h⁻¹, Subgroup.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
  · exact H.mul_mem (H.mul_mem hh hk.1) (H.inv_mem hh)
  · rw [mem_stabilizer_iff, mul_smul, mul_smul, inv_smul_smul, hk.2]
  · rw [map_mul, map_mul, hkσ, map_inv]
    group

omit [Fintype Ω] [DecidableEq Ω] [Fintype Γ] in
/-- The affected points of `H` are permuted by `H`. -/
theorem smul_mem_aff {A : Finset Γ} {H : Subgroup (stabA φ A)} {h : stabA φ A} (hh : h ∈ H)
    {i : Ω} (hi : i ∈ aff φ A H) : h • i ∈ aff φ A H := by
  intro hc
  apply hi
  have := le_map_stabilizer_smul φ (H.inv_mem hh) hc
  rwa [inv_smul_smul] at this

omit [Fintype Ω] [DecidableEq Ω] [Fintype Γ] in
/-- The points added to the window in one step are permuted by the current group. -/
theorem smul_newPoints {A : Finset Γ} {H : Subgroup (stabA φ A)} {h : stabA φ A} (hh : h ∈ H) :
    h • {i | IsGiantOn φ A H ∧ i ∈ aff φ A H} = {i | IsGiantOn φ A H ∧ i ∈ aff φ A H} :=
  smul_set_eq_of_forall (H := H) (W := {i | IsGiantOn φ A H ∧ i ∈ aff φ A H})
    (fun _ hh' _ hi => ⟨hi.1, smul_mem_aff φ hh' hi.2⟩) hh

/-- One step of the beard. -/
def beardStep (A : Finset Γ) (x : Ω → L) (p : Set Ω × Subgroup (stabA φ A)) :
    Set Ω × Subgroup (stabA φ A) :=
  let W := p.1 ∪ {i | IsGiantOn φ A p.2 ∧ i ∈ aff φ A p.2}
  (W, autW p.2 W x)

/-- The window and the group after `n` steps. -/
def beard (A : Finset Γ) (x : Ω → L) (n : ℕ) : Set Ω × Subgroup (stabA φ A) :=
  (beardStep φ A x)^[n] (∅, ⊤)

/-- The final window `W(A)`. -/
def beardW (A : Finset Γ) (x : Ω → L) : Set Ω := (beard φ A x (Fintype.card Ω)).1

/-- The final group `H(A)`. -/
def beardH (A : Finset Γ) (x : Ω → L) : Subgroup (stabA φ A) :=
  (beard φ A x (Fintype.card Ω)).2

section beard

variable (A : Finset Γ) (x : Ω → L)

omit [Fintype Ω] [DecidableEq Ω] [Fintype Γ] in
theorem beard_succ (n : ℕ) : beard φ A x (n + 1) = beardStep φ A x (beard φ A x n) :=
  Function.iterate_succ_apply' _ _ _

omit [Fintype Ω] [DecidableEq Ω] [Fintype Γ] in
theorem beardW_succ (n : ℕ) : (beard φ A x (n + 1)).1 = (beard φ A x n).1 ∪
    {i | IsGiantOn φ A (beard φ A x n).2 ∧ i ∈ aff φ A (beard φ A x n).2} := by
  rw [beard_succ]; rfl

omit [Fintype Ω] [DecidableEq Ω] [Fintype Γ] in
theorem beardH_succ (n : ℕ) :
    (beard φ A x (n + 1)).2 = autW (beard φ A x n).2 (beard φ A x (n + 1)).1 x := by
  rw [beard_succ]; rfl

omit [Fintype Ω] [DecidableEq Ω] [Fintype Γ] in
/-- The window grows. -/
theorem beardW_mono : Monotone fun n => (beard φ A x n).1 :=
  monotone_nat_of_le_succ fun n => by
    show (beard φ A x n).1 ⊆ (beard φ A x (n + 1)).1
    rw [beardW_succ]
    exact Set.subset_union_left

end beard

omit [Fintype Ω] [DecidableEq Ω] [Fintype Γ] in
/-- The window is invariant under the group, which respects `x` on it. -/
theorem beardH_le_autW (A : Finset Γ) (x : Ω → L) (n : ℕ) :
    (beard φ A x n).2 ≤ autW ⊤ (beard φ A x n).1 x := by
  cases n with
  | zero => exact fun _ _ => mem_autW.2 ⟨Subgroup.mem_top _, Set.smul_set_empty, fun _ h => h.elim⟩
  | succ n => rw [beardH_succ]; exact autW_mono le_top

omit [Fintype Ω] [DecidableEq Ω] [Fintype Γ] in
/-- The next window is invariant under the current group. -/
theorem smul_beardW_succ (A : Finset Γ) (x : Ω → L) {n : ℕ} {h : stabA φ A}
    (hh : h ∈ (beard φ A x n).2) : h • (beard φ A x (n + 1)).1 = (beard φ A x (n + 1)).1 := by
  rw [beardW_succ, Set.smul_set_union, (mem_autW.1 (beardH_le_autW φ A x n hh)).2.1,
    smul_newPoints φ hh]

omit [Fintype Ω] [DecidableEq Ω] [Fintype Γ] in
/-- If the window does not grow at step `n`, the beard is constant from step `n` on. -/
theorem beard_add_of_fst (A : Finset Γ) (x : Ω → L) {n : ℕ}
    (hW : (beard φ A x (n + 1)).1 = (beard φ A x n).1) (m : ℕ) :
    beard φ A x (n + m) = beard φ A x n := by
  have hf : beard φ A x (n + 1) = beard φ A x n := by
    refine Prod.ext hW ?_
    rw [beardH_succ, hW]
    exact autW_eq_self (beardH_le_autW φ A x n)
  induction m with
  | zero => rfl
  | succ m ih => rw [← add_assoc, beard_succ, ih, ← beard_succ, hf]

omit [DecidableEq Ω] [Fintype Γ] in
/-- The window cannot grow at step `|Ω|`: it would have grown at every earlier step. -/
theorem beardW_card_succ (A : Finset Γ) (x : Ω → L) :
    (beard φ A x (Fintype.card Ω + 1)).1 = (beard φ A x (Fintype.card Ω)).1 := by
  set N := Fintype.card Ω
  by_contra hne
  have hgrow : ∀ n ≤ N, (beard φ A x n).1 ⊂ (beard φ A x (n + 1)).1 := by
    intro n hn
    refine (beardW_mono φ A x (Nat.le_succ n)).ssubset_of_ne fun h => hne ?_
    have h1 := beard_add_of_fst φ A x h.symm (N + 1 - n)
    have h2 := beard_add_of_fst φ A x h.symm (N - n)
    rw [show n + (N + 1 - n) = N + 1 by omega] at h1
    rw [show n + (N - n) = N by omega] at h2
    rw [h1, h2]
  have hcard : ∀ n ≤ N + 1, n ≤ (beard φ A x n).1.ncard := by
    intro n hn
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih => exact (ih (by omega)).trans_lt (Set.ncard_lt_ncard (hgrow n (by omega)))
  have := (hcard (N + 1) le_rfl).trans (Set.ncard_le_ncard (Set.subset_univ _))
  rw [Set.ncard_univ, Nat.card_eq_fintype_card] at this
  omega

omit [DecidableEq Ω] [Fintype Γ] in
/-- **The beard stabilizes** after `|Ω|` steps. -/
theorem beard_stable (A : Finset Γ) (x : Ω → L) (j : ℕ) :
    beard φ A x (Fintype.card Ω + j) = beard φ A x (Fintype.card Ω) :=
  beard_add_of_fst φ A x (beardW_card_succ φ A x) j

omit [Fintype Ω] [DecidableEq Ω] [Fintype Γ] in
/-- **Automorphisms of `x` survive** (the invariant of Claim 10.1.7). -/
theorem autW_univ_le_beard (A : Finset Γ) (x : Ω → L) (n : ℕ) :
    autW (⊤ : Subgroup (stabA φ A)) Set.univ x ≤ (beard φ A x n).2 := by
  intro g hg
  induction n with
  | zero => exact Subgroup.mem_top g
  | succ n ih =>
    rw [beardH_succ]
    exact mem_autW.2 ⟨ih, smul_beardW_succ φ A x ih,
      fun i _ => (mem_autW.1 hg).2.2 i (Set.mem_univ i)⟩

omit [DecidableEq Ω] [Fintype Γ] in
/-- **The final group is the window group** `Aut_{G_A}(x^{W(A)})`. -/
theorem beardH_eq_autW (A : Finset Γ) (x : Ω → L) :
    beardH φ A x = autW ⊤ (beardW φ A x) x := by
  refine le_antisymm (beardH_le_autW φ A x _) fun g hg => ?_
  have key : ∀ n ≤ Fintype.card Ω, g ∈ (beard φ A x n).2 := by
    intro n hn
    induction n with
    | zero => exact Subgroup.mem_top g
    | succ n ih =>
      have ih := ih (by omega)
      rw [beardH_succ]
      exact mem_autW.2 ⟨ih, smul_beardW_succ φ A x ih,
        fun i hi => (mem_autW.1 hg).2.2 i (beardW_mono φ A x hn hi)⟩
  exact key _ le_rfl

omit [DecidableEq Ω] [Fintype Γ] in
/-- If the final group is a giant on `A`, every point it affects lies in the final window. -/
theorem aff_subset_beardW (A : Finset Γ) (x : Ω → L) (h : IsGiantOn φ A (beardH φ A x)) :
    aff φ A (beardH φ A x) ⊆ beardW φ A x := by
  intro i hi
  have h1 := beardW_card_succ φ A x
  rw [beardW_succ] at h1
  rw [beardW, ← h1]
  exact Set.mem_union_right _ ⟨h, hi⟩

end GraphIso.Certificates
