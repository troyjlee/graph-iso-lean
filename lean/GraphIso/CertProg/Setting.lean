module

public import GraphIso.Toolkit.Extend
public import GraphIso.Toolkit.Reduce
public import GraphIso.Certificates.Aggregate

/-!
# The setting of the local certificates on data

Stage 14e (`PLAN-14.md` §9). The programs see a group `G` of degree `N` whose string positions
`[0, n)` form the window `Ω` and whose base positions `[n, N)` form `Γ = Fin (N - n)`. When `G`
preserves the base and is faithful on the string positions (`CertSetting`), it is isomorphic to
its restriction `strGroup` to `[0, n)` (through `strR`, `strR_bijective`), and the base action
becomes a representation of `strGroup`: milestone 13's `φ`, with `Ω = Fin n`.

The inverse of `strR` is not computable, so `φ` is not defined: the statements take any `φ`
with `IsPhi φ` (`φ (strR g)` is the base action of `g`), and `exists_phi` provides one.

* `toStab φ A H`: a subgroup `H` of `Perm (Fin N)` (what the programs compute) seen inside
  milestone 13's `G_A = stabA φ A`: the elements of `G_A` coming from `H` (`mem_toStab`).
* `toStab_eq_top`: a group containing every element of `G` that stabilizes `A` gives all of
  `G_A`.
* `toStab_pointStab`: the stabilizer of a string position; `toStab_pointwiseStab`: the
  pointwise stabilizer of the positions of `A` gives the kernel of `ψ_A`.
-/

@[expose] public section

namespace GraphIso.CertProg

open Equiv MulAction Pointwise GraphIso GraphIso.Toolkit GraphIso.Certificates

/-- The hypotheses of the certificate setting: the base `[n, N)` is invariant and `G` is
faithful on the string positions `[0, n)`. -/
structure CertSetting {N : ℕ} (G : Subgroup (Perm (Fin N))) (n : ℕ) : Prop where
  le : n ≤ N
  base : IsInvariant G (baseSet n N)
  faithful : ∀ g ∈ G, (∀ j : Fin N, j.val < n → g j = j) → g = 1

variable {N n : ℕ} {G : Subgroup (Perm (Fin N))}

namespace CertSetting

theorem str (hC : CertSetting G n) : IsInvariant G (strSet n N) := isInvariant_strSet hC.base

/-- The restriction to the string positions. -/
def strH (hC : CertSetting G n) : ↥G →* Perm (Fin n) := strHom G n hC.le hC.str

theorem strH_injective (hC : CertSetting G n) : Function.Injective hC.strH := by
  rw [injective_iff_map_eq_one]
  intro g hg
  apply Subtype.ext
  apply hC.faithful g.1 g.2
  intro j hj
  have := congrArg (fun π : Perm (Fin n) => (π ⟨j.val, hj⟩).val) hg
  simp only [Perm.one_apply] at this
  exact Fin.ext this

end CertSetting

variable (hC : CertSetting G n)

/-- The group `G` restricted to the string positions. -/
def strGroup : Subgroup (Perm (Fin n)) := hC.strH.range

/-- The restriction onto `strGroup`. -/
def strR : ↥G →* strGroup hC := hC.strH.rangeRestrict

theorem strR_injective : Function.Injective (strR hC) :=
  MonoidHom.rangeRestrict_injective_iff.2 hC.strH_injective

theorem strR_surjective : Function.Surjective (strR hC) := MonoidHom.rangeRestrict_surjective _

theorem strR_apply_val (g : G) (j : Fin n) :
    (((strR hC g : Perm (Fin n)) j : Fin n) : ℕ) = (g.1 ⟨j.val, by have := hC.le; omega⟩).val :=
  rfl

/-- `φ` is the base action transported to the restricted group. -/
def IsPhi (φ : strGroup hC →* Perm (Fin (N - n))) : Prop :=
  ∀ g : G, φ (strR hC g) = baseHom G n hC.base g

/-- **The base action as a representation of the restricted group** (milestone 13's `φ`). -/
theorem exists_phi : ∃ φ : strGroup hC →* Perm (Fin (N - n)), IsPhi hC φ := by
  let e : ↥G ≃* strGroup hC := MulEquiv.ofBijective (strR hC)
    ⟨strR_injective hC, strR_surjective hC⟩
  refine ⟨(baseHom G n hC.base).comp e.symm.toMonoidHom, fun g => ?_⟩
  simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply]
  congr 1
  exact e.symm_apply_apply g

variable {hC} {φ : strGroup hC →* Perm (Fin (N - n))}

/-- **A subgroup of `Perm (Fin N)` inside `G_A`**: the elements of `G_A` coming from an element of
`G` in `H`. -/
def toStab (φ : strGroup hC →* Perm (Fin (N - n))) (A : Finset (Fin (N - n)))
    (H : Subgroup (Perm (Fin N))) : Subgroup (stabA φ A) :=
  ((H.subgroupOf G).map (strR hC)).comap (stabA φ A).subtype

theorem mem_toStab {A : Finset (Fin (N - n))} {H : Subgroup (Perm (Fin N))}
    {s : stabA φ A} : s ∈ toStab φ A H ↔ ∀ g : G, strR hC g = s.1 → (g : Perm (Fin N)) ∈ H := by
  simp only [toStab, Subgroup.mem_comap, Subgroup.coe_subtype, Subgroup.mem_map,
    Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨g, hg, hgs⟩ g' hg'
    rw [← strR_injective hC (hgs.trans hg'.symm)]
    exact hg
  · intro h
    obtain ⟨g, hg⟩ := strR_surjective hC s.1
    exact ⟨g, h g hg, hg⟩

theorem mem_toStab_strR {A : Finset (Fin (N - n))} {H : Subgroup (Perm (Fin N))} (g : G)
    (hg : strR hC g ∈ stabA φ A) :
    (⟨strR hC g, hg⟩ : stabA φ A) ∈ toStab φ A H ↔ (g : Perm (Fin N)) ∈ H := by
  rw [mem_toStab]
  exact ⟨fun h => h g rfl, fun h g' hg' => by rwa [strR_injective hC hg']⟩

theorem toStab_mono {A : Finset (Fin (N - n))} {H K : Subgroup (Perm (Fin N))} (h : H ≤ K) :
    toStab φ A H ≤ toStab φ A K :=
  fun _ hs => mem_toStab.2 fun g hg => h (mem_toStab.1 hs g hg)

/-- The base action of `g ∈ G` stabilizes `A` exactly when its restriction lies in `G_A`. -/
theorem mem_stabA_strR (hφ : IsPhi hC φ) {A : Finset (Fin (N - n))} (g : G) :
    strR hC g ∈ stabA φ A ↔ baseHom G n hC.base g • A = A := by
  rw [mem_stabA, hφ]

/-- If `H` contains every element of `G` that stabilizes `A` under the base action, it gives all
of `G_A`. -/
theorem toStab_eq_top (hφ : IsPhi hC φ) {A : Finset (Fin (N - n))} {H : Subgroup (Perm (Fin N))}
    (hH : ∀ g : G, baseHom G n hC.base g • A = A → (g : Perm (Fin N)) ∈ H) :
    toStab φ A H = ⊤ := by
  rw [eq_top_iff]
  intro s _
  rw [mem_toStab]
  intro g hg
  apply hH
  rw [← mem_stabA_strR hφ, hg]
  exact s.2

/-- **The stabilizer of a string position.** -/
theorem toStab_pointStab {A : Finset (Fin (N - n))} {H : Subgroup (Perm (Fin N))} (i : Fin N)
    (hi : i.val < n) :
    toStab φ A (pointStab H i) =
      toStab φ A H ⊓ stabilizer (stabA φ A) (⟨i.val, hi⟩ : Fin n) := by
  ext s
  obtain ⟨g, hg⟩ := strR_surjective hC s.1
  have hs : s = ⟨strR hC g, hg ▸ s.2⟩ := Subtype.ext hg.symm
  rw [Subgroup.mem_inf, hs, mem_toStab_strR, mem_toStab_strR, mem_pointStab, mem_stabilizer_iff]
  refine and_congr Iff.rfl ?_
  have e := strR_apply_val hC g ⟨i.val, hi⟩
  have hi' : (⟨i.val, by have := hC.le; omega⟩ : Fin N) = i := Fin.ext rfl
  rw [hi'] at e
  constructor
  · intro h
    apply Fin.ext
    show (((strR hC g : Perm (Fin n)) ⟨i.val, hi⟩ : Fin n) : ℕ) = i.val
    rw [e, h]
  · intro h
    apply Fin.ext
    have h' : (strR hC g : Perm (Fin n)) ⟨i.val, hi⟩ = ⟨i.val, hi⟩ := h
    rw [← e, h']

/-- The positions of a set of base points. -/
def basePosSet (A : Finset (Fin (N - n))) : Set (Fin N) := {v | ∃ a ∈ A, v = basePos a}

/-- **The pointwise stabilizer of the positions of `A`** gives the kernel of `ψ_A`. -/
theorem toStab_pointwiseStab (hφ : IsPhi hC φ) {A : Finset (Fin (N - n))}
    {H : Subgroup (Perm (Fin N))} :
    toStab φ A (pointwiseStab H (basePosSet A)) = toStab φ A H ⊓ (psiA φ A).ker := by
  ext s
  obtain ⟨g, hg⟩ := strR_surjective hC s.1
  have hs : s = ⟨strR hC g, hg ▸ s.2⟩ := Subtype.ext hg.symm
  rw [Subgroup.mem_inf, hs, mem_toStab_strR, mem_toStab_strR, MonoidHom.mem_ker]
  simp only [pointwiseStab, Subgroup.mem_mk]
  refine and_congr Iff.rfl ?_
  constructor
  · intro h
    ext a
    have ha := h (basePos a.1) ⟨a.1, a.2, rfl⟩
    have hb := baseHom_apply (hG := hC.base) g a.1
    rw [ha] at hb
    have hb' : baseHom G n hC.base g a.1 = a.1 := by
      apply Fin.ext
      have := congrArg Fin.val hb
      simp only [basePos] at this
      omega
    simp only [Perm.coe_one, id_eq]
    show ((psiA φ A _ a : Fin (N - n)) : ℕ) = a.1.val
    rw [psiA_apply_coe]
    show ((φ (strR hC g) a.1 : Fin (N - n)) : ℕ) = a.1.val
    rw [hφ, hb']
  · intro h v ⟨a, ha, hv⟩
    subst hv
    have hpa : psiA φ A ⟨strR hC g, hg ▸ s.2⟩ ⟨a, ha⟩ = ⟨a, ha⟩ := by rw [h]; rfl
    have hpa' := congrArg Subtype.val hpa
    rw [psiA_apply_coe] at hpa'
    have hpa'' : baseHom G n hC.base g a = a := by
      rw [← hφ]
      exact hpa'
    rw [← baseHom_apply (hG := hC.base) g a, hpa'']

end GraphIso.CertProg
