module

public import GraphIso.Semantics.StringIso
public import GraphIso.SplitJohnson.CTree
public import Mathlib.GroupTheory.Index

/-!
# Canonical structures and coset decompositions

The decompositions of `iso` that the macro-steps use (`PLAN-14.md` §2.2–2.3, §5 item 5).
`G : Subgroup (Perm Ω)` acts on a window `W`, and `ψ : G →* Perm Γ` is a representation.

* A map `X` from strings to `Perm Γ`-sets is **canonical** (`Canonical G W ψ X`) if it depends
  only on the window and is equivariant: `X (relabel g x) = ψ g • X x`.
* `iso_transporter`: every isomorphism carries `X x` to `X y`.
* `iso_eq_align`: if `σ ∈ G` carries `X x` to `X y`, the isomorphisms are those in the coset
  `σ • G₁`, where `G₁ = ψ⁻¹(Stab(X x))` (Babai's procedure Align).
* Choice trees: if `T` is canonical (`T (relabel g x) = (T x).act (ψ g)`), every isomorphism
  maps a reachable leaf for `x` to a reachable leaf for `y` (`iso_reach`).
* For a tree fixed by `ψ(G)` (built from `G` alone, such as Split-or-Johnson on an orbital
  configuration), the stabilizer of a reachable leaf has index at most the tree's count
  (`index_stab_le_count`).
-/

@[expose] public section

namespace GraphIso.Recursion

open Equiv MulAction Pointwise GraphIso.SplitJohnson

variable {Ω α Γ S : Type*} [MulAction (Perm Γ) S]

/-- A canonical structure: it depends only on the window and moves with the group. -/
structure Canonical (G : Subgroup (Perm Ω)) (W : Set Ω) (ψ : G →* Perm Γ)
    (X : (Ω → α) → S) : Prop where
  local_ : ∀ x x' : Ω → α, (∀ u ∈ W, x u = x' u) → X x = X x'
  equivar : ∀ (g : G) (x : Ω → α), X (relabel (g : Perm Ω) x) = ψ g • X x

variable {G : Subgroup (Perm Ω)} {W : Set Ω} {ψ : G →* Perm Γ} {x y : Ω → α}

omit [MulAction (Perm Γ) S] in
/-- An isomorphism relabels `x` into a string agreeing with `y` on the window. -/
theorem relabel_eq_on_of_mem_iso (hW : IsInvariant G W) {g : Perm Ω}
    (hg : g ∈ iso W 1 G x y) : ∀ u ∈ W, relabel g x u = y u := by
  obtain ⟨hgG, hm⟩ := mem_iso_one.1 hg
  intro u hu
  have hu' : g⁻¹ u ∈ W := hW g⁻¹ (G.inv_mem hgG) u hu
  simpa using hm (g⁻¹ u) hu'

/-- **Isomorphisms transport canonical structures.** -/
theorem iso_transporter (hW : IsInvariant G W) {X : (Ω → α) → S} (hX : Canonical G W ψ X)
    {g : Perm Ω} (hg : g ∈ iso W 1 G x y) : ψ ⟨g, (mem_iso_one.1 hg).1⟩ • X x = X y := by
  rw [← hX.equivar]
  exact hX.local_ _ _ (relabel_eq_on_of_mem_iso hW hg)

/-- The preimage, as a subgroup of `Perm Ω`, of the stabilizer of `s`. -/
def stabPre (ψ : G →* Perm Γ) (s : S) : Subgroup (Perm Ω) :=
  ((stabilizer (Perm Γ) s).comap ψ).map G.subtype

theorem stabPre_le (s : S) : stabPre ψ s ≤ G := Subgroup.map_subtype_le _

/-- **Alignment** (Babai's procedure Align): if `σ ∈ G` carries `X x` to `X y`, the
isomorphisms are the solutions in the coset `σ • ψ⁻¹(Stab(X x))`. -/
theorem iso_eq_align (hW : IsInvariant G W) {X : (Ω → α) → S} (hX : Canonical G W ψ X)
    {σ : Perm Ω} (hσ : σ ∈ G) (hσX : ψ ⟨σ, hσ⟩ • X x = X y) :
    iso W 1 G x y = iso W σ (stabPre ψ (X x)) x y := by
  ext g
  rw [mem_iso_one, mem_iso]
  constructor
  · rintro ⟨hgG, hm⟩
    refine ⟨⟨⟨σ, hσ⟩⁻¹ * ⟨g, hgG⟩, ?_, rfl⟩, hm⟩
    have ht := iso_transporter hW hX (mem_iso_one.2 ⟨hgG, hm⟩)
    show ψ (⟨σ, hσ⟩⁻¹ * ⟨g, hgG⟩) • X x = X x
    rw [map_mul, map_inv, mul_smul, ht, ← hσX, inv_smul_smul]
  · rintro ⟨hh, hm⟩
    refine ⟨?_, hm⟩
    have h1 : σ⁻¹ * g ∈ G := stabPre_le _ hh
    simpa using G.mul_mem hσ h1

/-- **Choice trees**: every isomorphism carries a reachable leaf for `x` to a reachable leaf
for `y`. -/
theorem iso_reach {C O : Type*} [MulAction (Perm Γ) C] [MulAction (Perm Γ) O] [DecidableEq C]
    (hW : IsInvariant G W) (T : (Ω → α) → CTree C O)
    (hloc : ∀ x x' : Ω → α, (∀ u ∈ W, x u = x' u) → T x = T x')
    (heq : ∀ (g : G) (x : Ω → α), T (relabel (g : Perm Ω) x) = (T x).act (ψ g))
    {o : O} (ho : (T x).Reach o) {g : Perm Ω} (hg : g ∈ iso W 1 G x y) :
    (T y).Reach (ψ ⟨g, (mem_iso_one.1 hg).1⟩ • o) := by
  have hT : T y = (T x).act (ψ ⟨g, (mem_iso_one.1 hg).1⟩) := by
    rw [← heq]
    exact (hloc _ _ (relabel_eq_on_of_mem_iso hW hg)).symm
  rw [hT]
  exact (CTree.reach_act _).2 ho

/-- **Leaf stabilizers**: for a tree fixed by `ψ(G)`, the stabilizer of a reachable leaf has
index at most the count. -/
theorem index_stab_le_count {C O : Type*} [MulAction (Perm Γ) C] [MulAction (Perm Γ) O]
    [DecidableEq C] [DecidableEq O] (t : CTree C O) (ht : ∀ g : G, t.act (ψ g) = t) {o : O}
    (ho : t.Reach o) : ((stabilizer (Perm Γ) o).comap ψ).index ≤ t.count := by
  let _ : MulAction G O := MulAction.compHom O ψ
  have hst : (stabilizer (Perm Γ) o).comap ψ = stabilizer G o := by
    ext g
    rfl
  rw [hst, MulAction.index_stabilizer]
  have hsub : orbit G o ⊆ (t.leaves : Set O) := by
    rintro _ ⟨g, rfl⟩
    rw [Finset.mem_coe, CTree.mem_leaves]
    have := (CTree.reach_act (ψ g) (t := t)).2 ho
    rwa [ht g] at this
  calc (orbit G o).ncard ≤ (t.leaves : Set O).ncard := Set.ncard_le_ncard hsub
    _ = t.leaves.card := Set.ncard_coe_finset _
    _ ≤ t.count := CTree.card_leaves_le t

end GraphIso.Recursion
