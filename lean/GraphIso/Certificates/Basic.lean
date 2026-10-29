module

public import GraphIso.AltQuot.Unaffected
public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic

/-!
# Local certificates: the setting

Babai §10.1 (Helfgott §6.1). `G : Subgroup (Perm Ω)` acts on a finite type `Ω`, `φ : G →* Perm Γ`
is a representation (a giant one in the applications), and `x : Ω → L` is a string; `G` acts
on strings by `(σ • x) i = x (σ⁻¹ • i)` (`smulStr`).

* `stabA φ A`: the setwise stabilizer `G_A` of a test set `A ⊆ Γ` under `φ`;
  `psiA φ A : G_A →* Sym(A)` restricts `φ` to `A` (Babai's `ψ_A`).
* `autW H W x`: the elements of `H` that map the window `W ⊆ Ω` onto itself and preserve `x`
  on it — Babai's `Aut_H(x^W)`, `x^W` being `x` truncated outside `W`. `autG x` is `Aut_G(x)`.
* `aff φ A H`: the points `i` affected by `H ≤ G_A`, i.e. `Alt(A) ≰ ψ_A(H_i)` (Def. 10.1.4);
  `IsGiantOn φ A H`: `Alt(A) ≤ ψ_A(H)`.
* `IsFull φ A x`: `A` is full (Def. 10.1.2): `Alt(A) ≤ ψ_A(Aut_{G_A}(x))`.
-/

@[expose] public section

namespace GraphIso.Certificates

open Equiv MulAction Pointwise

variable {Ω Γ : Type} [Fintype Ω] [DecidableEq Ω] [Fintype Γ] [DecidableEq Γ]
variable {G : Subgroup (Perm Ω)} (φ : G →* Perm Γ)

/-- The setwise stabilizer `G_A` of `A ⊆ Γ` under `φ`. -/
def stabA (A : Finset Γ) : Subgroup G := (stabilizer (Perm Γ) A).comap φ

omit [Fintype Ω] [DecidableEq Ω] [Fintype Γ] in
theorem mem_stabA {A : Finset Γ} {g : G} : g ∈ stabA φ A ↔ φ g • A = A := Iff.rfl

/-- The restriction `ψ_A : G_A → Sym(A)`. -/
def psiA (A : Finset Γ) : stabA φ A →* Perm A where
  toFun g := (φ g).subtypePerm (p := fun a => a ∈ A) (fun a => by
    have key (f : Perm Γ) (hf : f • A = A) : f • a ∈ A ↔ a ∈ A := by
      conv_lhs => rw [← hf]
      exact Finset.smul_mem_smul_finset_iff f
    exact key _ g.2)
  map_one' := by ext; simp
  map_mul' g h := by ext; simp; rfl

/-- `Aut_H(x^W)`: the elements of `H` mapping `W` onto itself and preserving `x` on `W`. -/
def autW {M : Type*} [Group M] [MulAction M Ω] {L : Type*} (H : Subgroup M) (W : Set Ω)
    (x : Ω → L) : Subgroup M where
  carrier := {h | h ∈ H ∧ h • W = W ∧ ∀ i ∈ W, x (h • i) = x i}
  one_mem' := ⟨H.one_mem, one_smul _ _, fun i _ => by rw [one_smul]⟩
  mul_mem' := by
    rintro a b ⟨ha, haW, hax⟩ ⟨hb, hbW, hbx⟩
    refine ⟨H.mul_mem ha hb, by rw [mul_smul, hbW, haW], fun i hi => ?_⟩
    have hbi : b • i ∈ W := hbW ▸ Set.smul_mem_smul_set hi
    rw [mul_smul, hax _ hbi, hbx i hi]
  inv_mem' := by
    rintro a ⟨ha, haW, hax⟩
    have haW' : a⁻¹ • W = W := by rw [inv_smul_eq_iff, haW]
    refine ⟨H.inv_mem ha, haW', fun i hi => ?_⟩
    have hai : a⁻¹ • i ∈ W := haW' ▸ Set.smul_mem_smul_set hi
    rw [← hax _ hai, smul_inv_smul]

/-- `Aut_G(x)`. -/
def autG {L : Type*} (x : Ω → L) : Subgroup G := autW ⊤ Set.univ x

/-- The points affected by `H ≤ G_A` (Babai, Def. 10.1.4). -/
def aff (A : Finset Γ) (H : Subgroup (stabA φ A)) : Set Ω :=
  {i | ¬ alternatingGroup A ≤ (H ⊓ stabilizer (stabA φ A) i).map (psiA φ A)}

/-- `ψ_A` restricted to `H` is a giant representation. -/
def IsGiantOn (A : Finset Γ) (H : Subgroup (stabA φ A)) : Prop :=
  alternatingGroup A ≤ H.map (psiA φ A)

/-- `A` is **full** with respect to `x` (Babai, Def. 10.1.2): the automorphisms of `x` in `G_A`
induce a giant on `A`. -/
def IsFull {L : Type*} (A : Finset Γ) (x : Ω → L) : Prop :=
  alternatingGroup A ≤ (autW (⊤ : Subgroup (stabA φ A)) Set.univ x).map (psiA φ A)

/-- The action of `G` on strings. -/
def smulStr {L : Type*} (σ : G) (x : Ω → L) : Ω → L := fun i => x (σ⁻¹ • i)

end GraphIso.Certificates
