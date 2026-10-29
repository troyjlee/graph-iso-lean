module

public import GraphIso.AltQuot.Affected

/-!
# The Unaffected Stabilizer Theorem and the Affected Orbit Lemma

Babai §8.3 (Helfgott §4.1, Prop. 4.4), against the CFSG-free interface `AltQuotientIso K`.
* `unaffected_stabilizer` (**the Unaffected Stabilizer Theorem**, Babai Thm. 8.3.5; Helfgott,
  Prop. 4.4 (a)): for a giant representation `φ : G → Sym(Λ)` and `D` the unaffected points,
  `Alt(Λ) ≤ φ(G_(D))`, the image of the pointwise stabilizer of `D`. The proof reduces to the
  epimorphism onto `Alt(Λ)` obtained on `φ⁻¹(Alt(Λ))`, whose unaffected points include those
  of `φ`. For an epimorphism onto `Alt(Λ)` (`unaffected_stabilizer_alt`), `D` is `G`-invariant
  (`smul_mem_unaffected`), so `φ(G_(D))` is normal in the simple `Alt(Λ)`; if it were trivial,
  `φ` would factor through the restriction of `G` to `D`, and `exists_affected` would give an
  affected point in `D`.
* `card_orbit_ker_mul_index` (Prop. 8.3.6): for `φ : G → H` onto and `y` in the orbit of `x`,
  `|y^{ker φ}| · [H : φ(G_x)] = |x^G|`. With `N = ker φ` normal, `[H : φ(G_x)] = [G : G_x ⊔ N]`
  and `[G_x ⊔ N : G_x] = [N : N_x] = |x^N|` (`relIndex_sup_of_normal`); the orbits of `N` along
  `x^G` all have the size of `x^N` (`card_orbit_smul_of_normal`).
* `affected_orbit` (**the Affected Orbit Lemma**, Cor. 8.3.7; Helfgott, Prop. 4.4 (b)): for a
  giant `φ`, `k ≥ 5` and `x` affected, `k · |x^{ker φ}| ≤ |x^G|`.
-/

@[expose] public section

namespace GraphIso.AltQuot

open Equiv MulAction

variable {Ω Λ : Type} [Fintype Ω] [DecidableEq Ω] [Fintype Λ] [DecidableEq Λ]

/-! ### Orbits of the kernel -/

/-- The second isomorphism theorem for relative indices: `[H ⊔ N : H] = [N : H ⊓ N]` for `N`
normal. -/
theorem relIndex_sup_of_normal {G : Type*} [Group G] [Finite G] (H N : Subgroup G) [N.Normal] :
    H.relIndex (H ⊔ N) = H.relIndex N := by
  have e1 := Subgroup.relIndex_mul_relIndex (H ⊓ N) H (H ⊔ N) inf_le_left le_sup_left
  have e2 := Subgroup.relIndex_mul_relIndex (H ⊓ N) N (H ⊔ N) inf_le_right le_sup_right
  rw [Subgroup.inf_relIndex_left] at e1
  rw [Subgroup.inf_relIndex_right, Subgroup.relIndex_sup_right] at e2
  have hne : N.relIndex H ≠ 0 := Subgroup.index_ne_zero_of_finite
  have := e1.trans e2.symm
  rw [mul_comm (H.relIndex N)] at this
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne) this

omit [Fintype Ω] [DecidableEq Ω] in
/-- A normal subgroup has orbits of equal size along an orbit of the group. -/
theorem card_orbit_smul_of_normal {G : Subgroup (Perm Ω)} (N : Subgroup G) [N.Normal] (g : G)
    (x : Ω) : Nat.card (orbit N (g • x)) = Nat.card (orbit N x) := by
  have hset : orbit N (g • x) = (fun z => g • z) '' orbit N x := by
    ext z
    simp only [Set.mem_image, mem_orbit_iff]
    constructor
    · rintro ⟨n, rfl⟩
      refine ⟨(⟨g⁻¹ * n * g, ?_⟩ : N) • x, ⟨⟨g⁻¹ * n * g, ?_⟩, rfl⟩, ?_⟩
      · simpa using (inferInstance : N.Normal).conj_mem n n.2 g⁻¹
      · simpa using (inferInstance : N.Normal).conj_mem n n.2 g⁻¹
      · simp [Subgroup.smul_def, mul_smul]
    · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
      refine ⟨⟨g * n * g⁻¹, (inferInstance : N.Normal).conj_mem n n.2 g⟩, ?_⟩
      simp [Subgroup.smul_def, mul_smul]
  rw [hset, Nat.card_image_of_injective (MulAction.injective g)]

omit [DecidableEq Ω] in
/-- **The orbits of the kernel** (Babai, Prop. 8.3.6). -/
theorem card_orbit_ker_mul_index {G : Subgroup (Perm Ω)} {H : Type*} [Group H] (φ : G →* H)
    (hφ : Function.Surjective φ) (x y : Ω) (hy : y ∈ orbit G x) :
    Nat.card (orbit φ.ker y) * ((stabilizer G x).map φ).index = Nat.card (orbit G x) := by
  obtain ⟨g, rfl⟩ := hy
  rw [card_orbit_smul_of_normal]
  set S := stabilizer G x
  have hmap : (S.map φ).index = (S ⊔ φ.ker).index := by
    rw [Subgroup.index_map, φ.range_eq_top_of_surjective hφ, Subgroup.index_top, mul_one]
  have hN : Nat.card (orbit φ.ker x) = S.relIndex φ.ker := by
    rw [Nat.card_coe_set_eq, ← index_stabilizer]
    rfl
  have hG : Nat.card (orbit G x) = S.index := by
    rw [Nat.card_coe_set_eq, ← index_stabilizer]
  rw [hN, hmap, hG, ← relIndex_sup_of_normal]
  exact Subgroup.relIndex_mul_index le_sup_left

omit [DecidableEq Ω] in
/-- **The Affected Orbit Lemma** (Babai, Cor. 8.3.7; Helfgott, Prop. 4.4 (b)): the kernel of a
giant representation splits an affected orbit into orbits of at most `1/k` of its size. -/
theorem affected_orbit {G : Subgroup (Perm Ω)} (φ : G →* Perm Λ) (hφ : IsGiant φ)
    (h5 : 5 ≤ Fintype.card Λ) {x : Ω} (hx : IsAffected φ x) :
    Fintype.card Λ * Nat.card (orbit φ.ker x) ≤ Nat.card (orbit G x) := by
  have h := card_orbit_ker_mul_index φ.rangeRestrict φ.rangeRestrict_surjective x x
    (mem_orbit_self x)
  rw [MonoidHom.ker_rangeRestrict] at h
  set L := (stabilizer G x).map φ
  have hmapR : (stabilizer G x).map φ.rangeRestrict = L.subgroupOf φ.range := by
    ext r
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, L]
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨g, hg, rfl⟩
    · rintro ⟨g, hg, hgr⟩
      exact ⟨g, hg, Subtype.ext hgr⟩
  have hidx : Fintype.card Λ ≤ ((stabilizer G x).map φ.rangeRestrict).index := by
    rw [hmapR]
    refine le_trans ?_ (Subgroup.relIndex_le_of_le_right hφ Subgroup.index_ne_zero_of_finite)
    refine card_le_index_of_ne_top h5 ?_
    rw [Ne, Subgroup.subgroupOf_eq_top]
    exact hx
  rw [← h, mul_comm]
  exact Nat.mul_le_mul_left _ hidx

/-! ### The Unaffected Stabilizer Theorem -/

omit [Fintype Ω] [DecidableEq Ω] in
/-- The unaffected points of an epimorphism onto `Alt(Λ)` form a `G`-invariant set. -/
theorem smul_mem_unaffected {G : Subgroup (Perm Ω)} (φ : G →* alternatingGroup Λ) (g : G)
    {x : Ω} (hx : (stabilizer G x).map φ = ⊤) : (stabilizer G (g • x)).map φ = ⊤ := by
  rw [eq_top_iff] at hx ⊢
  intro b _
  obtain ⟨h, hh, hhb⟩ := Subgroup.mem_map.1 (hx (Subgroup.mem_top (φ g⁻¹ * b * φ g)))
  refine Subgroup.mem_map.2 ⟨g * h * g⁻¹, ?_, ?_⟩
  · rw [mem_stabilizer_iff] at hh ⊢
    rw [mul_smul, mul_smul, inv_smul_smul, hh]
  · rw [map_mul, map_mul, hhb, map_inv]
    group

omit [DecidableEq Ω] in
/-- **The Unaffected Stabilizer Theorem for epimorphisms onto `Alt(Λ)`.** -/
theorem unaffected_stabilizer_alt {K : ℕ → ℕ} (hL : AltQuotientIso K) (hK : Monotone K)
    (G : Subgroup (Perm Ω)) (φ : G →* alternatingGroup Λ) (hφ : Function.Surjective φ)
    (h5 : 5 ≤ Fintype.card Λ) {N : ℕ} (hN : ∀ x : Ω, Nat.card (orbit G x) ≤ N)
    (hk : K N ≤ Fintype.card Λ) (hn : N < (Fintype.card Λ).factorial / 2) :
    (fixingSubgroup G ({x | (stabilizer G x).map φ = ⊤} : Set Ω)).map φ = ⊤ := by
  classical
  set D : Set Ω := {x | (stabilizer G x).map φ = ⊤} with hD
  have hinv : ∀ (g : G) (x : Ω), x ∈ D → g • x ∈ D := fun g x hx => smul_mem_unaffected φ g hx
  have hFn : (fixingSubgroup G D).Normal := ⟨fun f hf g => by
    rw [mem_fixingSubgroup_iff] at hf ⊢
    intro y hy
    rw [mul_smul, mul_smul, hf (g⁻¹ • y) (hinv g⁻¹ y hy), smul_inv_smul]⟩
  have h5' : 5 ≤ Nat.card Λ := by rwa [Nat.card_eq_fintype_card]
  have : ((fixingSubgroup G D).map φ).Normal := hFn.map φ hφ
  rcases alternatingGroup.normal_subgroup_eq_bot_or_eq_top h5'
      (N := (fixingSubgroup G D).map φ) with hbot | htop
  swap
  · exact htop
  exfalso
  have hFker : fixingSubgroup G D ≤ φ.ker := (Subgroup.map_eq_bot_iff _).1 hbot
  -- the restriction of `G` to `D`
  let S : SubMulAction G Ω := ⟨D, fun g x hx => hinv g x hx⟩
  let ρ := MulAction.toPermHom G S
  have hρ : ∀ (g : G) (y : S), (ρ g y : Ω) = g • (y : Ω) := fun g y => rfl
  have hker : ρ.ker ≤ φ.ker := fun g hg => hFker (by
    rw [mem_fixingSubgroup_iff]
    intro y hy
    have := congrArg (fun p : Perm S => (p ⟨y, hy⟩ : Ω)) (MonoidHom.mem_ker.1 hg)
    simpa [hρ] using this)
  let e := QuotientGroup.quotientKerEquivRange ρ
  let ψ : ρ.range →* alternatingGroup Λ :=
    (QuotientGroup.lift ρ.ker φ hker).comp e.symm.toMonoidHom
  have hψ : ∀ g, ψ (ρ.rangeRestrict g) = φ g := by
    intro g
    have : e.symm (ρ.rangeRestrict g) = (g : G ⧸ ρ.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show QuotientGroup.lift ρ.ker φ hker (e.symm (ρ.rangeRestrict g)) = φ g
    rw [this]
    rfl
  have hψs : Function.Surjective ψ := fun b => by
    obtain ⟨g, rfl⟩ := hφ b
    exact ⟨ρ.rangeRestrict g, hψ g⟩
  have horb : ∀ y : S, Nat.card (orbit ρ.range y) ≤ N := by
    intro y
    refine le_trans ?_ (hN y)
    refine Nat.card_le_card_of_injective
      (fun z => ⟨(z.1 : Ω), ?_⟩) ?_
    · obtain ⟨p, hp⟩ := z.2
      obtain ⟨g, hg⟩ := p.2
      refine ⟨g, ?_⟩
      show g • (y : Ω) = ((z : S) : Ω)
      rw [← hp]
      show g • (y : Ω) = (((p : Perm S) y : S) : Ω)
      rw [← hg]
      rfl
    · intro a b hab
      simp only [Subtype.mk.injEq] at hab
      exact Subtype.ext (Subtype.ext hab)
  obtain ⟨y, hy⟩ := exists_affected hL hK ρ.range ψ hψs h5 horb hk hn
  apply hy
  rw [eq_top_iff]
  intro b _
  have hyD : (stabilizer G (y : Ω)).map φ = ⊤ := y.2
  obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.1 (hyD ▸ Subgroup.mem_top b)
  refine Subgroup.mem_map.2 ⟨ρ.rangeRestrict h, ?_, hψ h⟩
  rw [mem_stabilizer_iff]
  apply Subtype.ext
  rw [Subgroup.smul_def, Perm.smul_def]
  exact (hρ h y).trans (mem_stabilizer_iff.1 hh)

omit [DecidableEq Ω] in
/-- **The Unaffected Stabilizer Theorem** (Babai, Thm. 8.3.5; Helfgott, Prop. 4.4 (a)): the
pointwise stabilizer of the unaffected points still maps onto a group containing `Alt(Λ)`. -/
theorem unaffected_stabilizer {K : ℕ → ℕ} (hL : AltQuotientIso K) (hK : Monotone K)
    (G : Subgroup (Perm Ω)) (φ : G →* Perm Λ) (hφ : IsGiant φ) (h5 : 5 ≤ Fintype.card Λ)
    {N : ℕ} (hN : ∀ x : Ω, Nat.card (orbit G x) ≤ N) (hk : K N ≤ Fintype.card Λ)
    (hn : N < (Fintype.card Λ).factorial / 2) :
    alternatingGroup Λ ≤ (fixingSubgroup G ({x | ¬ IsAffected φ x} : Set Ω)).map φ := by
  classical
  -- `G₁ = φ⁻¹(Alt(Λ))`, as a permutation group, and `φ₁ : G₁ → Alt(Λ)` onto
  let G₁ : Subgroup (Perm Ω) := ((alternatingGroup Λ).comap φ).map G.subtype
  have hle : G₁ ≤ G := Subgroup.map_subtype_le _
  have hincl : ∀ (g : G) (h : (g : Perm Ω) ∈ G₁), Subgroup.inclusion hle ⟨g, h⟩ = g :=
    fun g h => rfl
  have hmem : ∀ σ : G₁, φ (Subgroup.inclusion hle σ) ∈ alternatingGroup Λ := by
    rintro ⟨σ, hσ⟩
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hσ
    exact hg
  let φ₁ : G₁ →* alternatingGroup Λ :=
    (φ.comp (Subgroup.inclusion hle)).codRestrict (alternatingGroup Λ) hmem
  have hφ₁ : ∀ σ : G₁, (φ₁ σ : Perm Λ) = φ (Subgroup.inclusion hle σ) := fun σ => rfl
  have hφ₁s : Function.Surjective φ₁ := by
    rintro ⟨a, ha⟩
    obtain ⟨g, hg⟩ := MonoidHom.mem_range.1 (hφ ha)
    have hgA : g ∈ (alternatingGroup Λ).comap φ := by
      show φ g ∈ alternatingGroup Λ
      rw [hg]
      exact ha
    refine ⟨⟨g, Subgroup.mem_map.2 ⟨g, hgA, rfl⟩⟩, Subtype.ext ?_⟩
    rw [hφ₁, hincl, hg]
  have hN₁ : ∀ x : Ω, Nat.card (orbit G₁ x) ≤ N := by
    intro x
    refine le_trans ?_ (hN x)
    have hsub : orbit G₁ x ⊆ orbit G x := by
      rintro _ ⟨σ, rfl⟩
      exact ⟨Subgroup.inclusion hle σ, rfl⟩
    exact Nat.card_le_card_of_injective (Set.inclusion hsub) (Set.inclusion_injective hsub)
  have key := unaffected_stabilizer_alt hL hK G₁ φ₁ hφ₁s h5 hN₁ hk hn
  -- the unaffected points of `φ` are unaffected for `φ₁`
  have hD : ∀ y : Ω, ¬ IsAffected φ y → (stabilizer G₁ y).map φ₁ = ⊤ := by
    intro y hy
    rw [IsAffected, not_not] at hy
    rw [eq_top_iff]
    rintro ⟨b, hb⟩ _
    obtain ⟨g, hg, hgb⟩ := Subgroup.mem_map.1 (hy hb)
    have hgA : g ∈ (alternatingGroup Λ).comap φ := by
      show φ g ∈ alternatingGroup Λ
      rw [hgb]
      exact hb
    refine Subgroup.mem_map.2 ⟨⟨g, Subgroup.mem_map.2 ⟨g, hgA, rfl⟩⟩, ?_, Subtype.ext ?_⟩
    · rw [mem_stabilizer_iff] at hg ⊢
      exact hg
    · rw [hφ₁, hincl, hgb]
  intro a ha
  have hmemtop : (⟨a, ha⟩ : alternatingGroup Λ) ∈
      (fixingSubgroup G₁ ({x | (stabilizer G₁ x).map φ₁ = ⊤} : Set Ω)).map φ₁ :=
    by rw [key]; exact Subgroup.mem_top _
  obtain ⟨σ, hσ, hσa⟩ := Subgroup.mem_map.1 hmemtop
  refine Subgroup.mem_map.2 ⟨Subgroup.inclusion hle σ, ?_, ?_⟩
  · rw [mem_fixingSubgroup_iff] at hσ ⊢
    intro y hy
    exact hσ y (hD y hy)
  · rw [← hφ₁, hσa]

end GraphIso.AltQuot
