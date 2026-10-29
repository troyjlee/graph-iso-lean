module

public import GraphIso.Certificates.Beard

/-!
# Local certificates

Babai, Thm. 10.1.3 with Claims 10.1.6 and 10.1.7 (Helfgott §6.1.1), against the CFSG-free
interface `AltQuotientIso K` of milestone 12 (`Thresholds`).

* **Certificate of fullness** (`cert_full`): if `ψ_A(H(A))` is a giant, then
  `K(A) = H(A)_(Ω \ W(A))` consists of automorphisms of `x` and `Alt(A) ≤ ψ_A(K(A))` — by the
  Unaffected Stabilizer Theorem, since no point outside `W(A)` is affected.
* **Certificate of non-fullness** (`cert_not_full`): otherwise `M(A) = ψ_A(H(A))` does not
  contain `Alt(A)` and contains `ψ_A(Aut_{G_A}(x))`.
* `isFull_iff`: so `A` is full exactly when `ψ_A(H(A))` is a giant.
* `kernel_orbit` (Babai's complexity argument, Cor. 8.3.7): while `ψ_A(H_n)` is a giant, the
  kernel `N` of `ψ_A` on `H_n` splits each affected orbit `u^{H_n}` into orbits of at most
  `|u^{H_n}|/k` points — the windows on which "Recompute `H(W)`" calls string isomorphism.
-/

@[expose] public section

namespace GraphIso.Certificates

open Equiv MulAction Pointwise GraphIso.AltQuot

namespace Local

variable {Ω Λ : Type} {G : Subgroup (Perm Ω)} {S : Subgroup G}

/-- **A subgroup as a permutation group.** For `H ≤ S ≤ G ≤ Sym(Ω)` and a representation `ψ` of
`S`, the permutations of `Ω` induced by `H` form a group `P` with a representation `ρ`
(`ψ` on `H`) such that images of stabilizers and pointwise stabilizers, orbits, and orbits of
the kernel are those of `H`. -/
theorem exists_permGroup (H : Subgroup S) (ψ : S →* Perm Λ) :
    ∃ (P : Subgroup (Perm Ω)) (ρ : P →* Perm Λ),
      ρ.range = H.map ψ ∧
      (∀ i : Ω, (stabilizer P i).map ρ = (H ⊓ stabilizer S i).map ψ) ∧
      (∀ D : Set Ω, (fixingSubgroup P D).map ρ = (H ⊓ fixingSubgroup S D).map ψ) ∧
      (∀ i : Ω, orbit P i = orbit H i) ∧
      (∀ i : Ω, orbit ρ.ker i = orbit ↥(H ⊓ ψ.ker) i) := by
  let ι : S →* Perm Ω := G.subtype.comp S.subtype
  have hι : Function.Injective ι := Subtype.val_injective.comp Subtype.val_injective
  let e := H.equivMapOfInjective ι hι
  let ρ : H.map ι →* Perm Λ := (ψ.comp H.subtype).comp e.symm.toMonoidHom
  have hρ : ∀ h : H, ρ (e h) = ψ h := fun h => by simp [ρ]
  have hmap : ∀ (Q : Subgroup (H.map ι)) (R : Subgroup S),
      (∀ h : H, e h ∈ Q ↔ (h : S) ∈ R) → Q.map ρ = (H ⊓ R).map ψ := by
    intro Q R hQR
    ext y
    constructor
    · rintro ⟨p, hp, rfl⟩
      obtain ⟨h, rfl⟩ := e.surjective p
      exact ⟨h, ⟨h.2, (hQR h).1 hp⟩, (hρ h).symm⟩
    · rintro ⟨s, ⟨hsH, hsR⟩, rfl⟩
      exact ⟨e ⟨s, hsH⟩, (hQR ⟨s, hsH⟩).2 hsR, hρ ⟨s, hsH⟩⟩
  refine ⟨H.map ι, ρ, ?_, fun i => hmap _ _ fun h => Iff.rfl,
    fun D => hmap _ _ fun h => Iff.rfl, fun i => ?_, fun i => ?_⟩
  · rw [MonoidHom.range_eq_map, hmap ⊤ ⊤ fun h => Iff.rfl, inf_top_eq]
  · ext j
    simp only [mem_orbit_iff]
    constructor
    · rintro ⟨p, rfl⟩
      obtain ⟨h, rfl⟩ := e.surjective p
      exact ⟨h, rfl⟩
    · rintro ⟨h, rfl⟩
      exact ⟨e h, rfl⟩
  · ext j
    simp only [mem_orbit_iff]
    constructor
    · rintro ⟨⟨p, hp⟩, rfl⟩
      obtain ⟨h, rfl⟩ := e.surjective p
      refine ⟨⟨h, h.2, MonoidHom.mem_ker.2 ?_⟩, rfl⟩
      rw [← hρ]
      exact MonoidHom.mem_ker.1 hp
    · rintro ⟨⟨s, hsH, hsK⟩, rfl⟩
      refine ⟨⟨e ⟨s, hsH⟩, ?_⟩, rfl⟩
      rw [MonoidHom.mem_ker, hρ]
      exact hsK

end Local

variable {Ω Γ : Type} [Fintype Ω] [DecidableEq Ω] [Fintype Γ] [DecidableEq Γ]
variable {G : Subgroup (Perm Ω)} (φ : G →* Perm Γ) {L : Type*}

/-- The thresholds of milestone 12 for test sets of size `k` in degree `n`. -/
structure Thresholds (K : ℕ → ℕ) (n k : ℕ) : Prop where
  iso : AltQuotientIso K
  mono : Monotone K
  five : 5 ≤ k
  le : K n ≤ k
  lt : n < k.factorial / 2

/-- The certificate of fullness `K(A) = H(A)_(Ω \ W(A))`. -/
def certK (A : Finset Γ) (x : Ω → L) : Subgroup (stabA φ A) :=
  beardH φ A x ⊓ fixingSubgroup (stabA φ A) (beardW φ A x)ᶜ

/-- The certificate of non-fullness `M(A) = ψ_A(H(A))`. -/
def certM (A : Finset Γ) (x : Ω → L) : Subgroup (Perm A) := (beardH φ A x).map (psiA φ A)

namespace Local

omit [DecidableEq Ω] [Fintype Γ] in
/-- `K(A)` consists of automorphisms of `x`: it respects `x` on `W(A)` and fixes the rest. -/
theorem certK_le_autW {A : Finset Γ} (x : Ω → L) :
    certK φ A x ≤ autW ⊤ Set.univ x := by
  rintro s ⟨hsH, hsF⟩
  obtain ⟨-, -, hx⟩ := beardH_le_autW φ A x (Fintype.card Ω) hsH
  refine ⟨trivial, Set.smul_set_univ, fun i _ => ?_⟩
  by_cases hi : i ∈ beardW φ A x
  · exact hx i hi
  · rw [(mem_fixingSubgroup_iff _).1 hsF i hi]

omit [DecidableEq Ω] in
/-- The orbits of a group of permutations of `Ω` have at most `|Ω|` points. -/
theorem card_orbit_le (P : Subgroup (Perm Ω)) (i : Ω) :
    Nat.card (orbit P i) ≤ Fintype.card Ω :=
  (Finite.card_subtype_le _).trans Nat.card_eq_fintype_card.le

end Local

open Local

omit [DecidableEq Ω] [Fintype Γ] in
/-- **The certificate of fullness** (Babai, Claim 10.1.6). -/
theorem cert_full {K : ℕ → ℕ} {A : Finset Γ} (x : Ω → L)
    (hT : Thresholds K (Fintype.card Ω) A.card) (h : IsGiantOn φ A (beardH φ A x)) :
    (certK φ A x).map (stabA φ A).subtype ≤ autG x ∧
      alternatingGroup A ≤ (certK φ A x).map (psiA φ A) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨s, hs, rfl⟩
    obtain ⟨-, -, hx⟩ := certK_le_autW φ x hs
    exact ⟨trivial, Set.smul_set_univ, fun i _ => hx i trivial⟩
  obtain ⟨P, ρ, hrange, hstab, hfix, -, -⟩ := exists_permGroup (beardH φ A x) (psiA φ A)
  have hρ : IsGiant ρ := by
    rw [IsGiant, hrange]
    exact h
  have hA := Fintype.card_coe A
  have key := unaffected_stabilizer hT.iso hT.mono P ρ hρ (hA ▸ hT.five) (card_orbit_le P)
    (hA ▸ hT.le) (hA ▸ hT.lt)
  rw [hfix] at key
  refine key.trans (Subgroup.map_mono (inf_le_inf_left _ (fixingSubgroup_antitone _ _ ?_)))
  intro i hi hai
  apply hi
  apply aff_subset_beardW φ A x h
  show ¬ _ ≤ _
  rw [← hstab]
  exact hai

omit [DecidableEq Ω] [Fintype Γ] in
/-- **The certificate of non-fullness** (Babai, Claim 10.1.7). -/
theorem cert_not_full {A : Finset Γ} (x : Ω → L) (h : ¬ IsGiantOn φ A (beardH φ A x)) :
    ¬ alternatingGroup A ≤ certM φ A x ∧
      (autW (⊤ : Subgroup (stabA φ A)) Set.univ x).map (psiA φ A) ≤ certM φ A x :=
  ⟨h, Subgroup.map_mono (autW_univ_le_beard φ A x _)⟩

omit [DecidableEq Ω] [Fintype Γ] in
/-- **The certificates decide fullness** (Babai, Thm. 10.1.3). -/
theorem isFull_iff {K : ℕ → ℕ} {A : Finset Γ} (x : Ω → L)
    (hT : Thresholds K (Fintype.card Ω) A.card) :
    IsFull φ A x ↔ IsGiantOn φ A (beardH φ A x) :=
  ⟨fun hF => hF.trans (Subgroup.map_mono (autW_univ_le_beard φ A x _)),
    fun h => (cert_full φ x hT h).2.trans (Subgroup.map_mono (certK_le_autW φ x))⟩

omit [DecidableEq Ω] [Fintype Γ] in
/-- **The kernel on the new window** (Babai's complexity argument, Cor. 8.3.7). -/
theorem kernel_orbit {A : Finset Γ} (x : Ω → L) (h5 : 5 ≤ A.card) (n : ℕ)
    (h : IsGiantOn φ A (beard φ A x n).2) {u : Ω} (hu : u ∈ aff φ A (beard φ A x n).2) :
    A.card * Nat.card (orbit ↥((beard φ A x n).2 ⊓ (psiA φ A).ker) u) ≤
      Nat.card (orbit (beard φ A x n).2 u) := by
  obtain ⟨P, ρ, hrange, hstab, -, horb, hker⟩ := exists_permGroup (beard φ A x n).2 (psiA φ A)
  have hρ : IsGiant ρ := by
    rw [IsGiant, hrange]
    exact h
  have hu' : IsAffected ρ u := by
    rw [IsAffected, hstab]
    exact hu
  have key := affected_orbit ρ hρ (by rwa [Fintype.card_coe]) hu'
  rwa [Fintype.card_coe, hker, horb] at key

end GraphIso.Certificates
