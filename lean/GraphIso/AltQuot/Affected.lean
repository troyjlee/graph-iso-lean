module

public import GraphIso.AltQuot.Interfaces
public import GraphIso.AltQuot.Alternating
public import GraphIso.AltQuot.Subdirect
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Alternating quotients versus stabilizers

Babai §8.3 (Helfgott §4.1), proved against the CFSG-free interface `AltQuotientIso K`.
Throughout, `G : Subgroup (Perm Ω)` is a permutation group on a finite type `Ω` and `k = |Λ|`.

* `stabilizer_map_ne_top` (Babai, Lemma 8.3.1; Helfgott, Lemma 4.3 (a)): for `G` transitive and
  an epimorphism `φ : G → Alt(Λ)`, with `5 ≤ k`, `K |Ω| ≤ k`, `|Ω| < k!/2` and `K` monotone,
  `φ(G_x) ≠ Alt(Λ)` for every `x`.
* `exists_affected` (Lemma 8.3.3; Lemma 4.3 (b)): for `G` arbitrary with orbits of at most `N`
  points, `K N ≤ k` and `N < k!/2`, some `x` has `φ(G_x) ≠ Alt(Λ)`.
* A homomorphism `φ : G → Sym(Λ)` is a **giant representation** if `Alt(Λ) ≤ φ(G)`
  (`IsGiant`); `x` is **affected** if `Alt(Λ) ≰ φ(G_x)` (`IsAffected`, Babai Def. 8.3.4).
  Their consequences are in `AltQuot/Unaffected.lean`.

Both lemmas come from `stab_map_ne_top_aux`, Lemma 8.3.1 for an abstract transitive action
whose kernel lies in `ker φ`, by induction on the order of the group. With `M ≥ G_x` a maximal
subgroup, `G` acts primitively on `G ⧸ M` with kernel `A`; as `φ(A)` is normal in the simple
`Alt(Λ)`, either `A ≤ ker φ` — then `φ` factors through the primitive image, `AltQuotientIso`
makes it injective, and `G = G_x ker φ ≤ M` — or `φ(A) = Alt(Λ)`. In the second case Babai's
Lemma 8.1.1 (`exists_le_ker_of_simple_of_le`, for kernels meeting inside `ker φ`) puts the
kernel of `A` on some `A`-orbit inside `ker φ`, hence (by conjugation in `G`) the kernel on the
orbit of `x`; induction on `A` there and the normality of `φ(A_x)` in `φ(G_x) = Alt(Λ)` give
`φ(A_x) = 1`, so `k!/2 ≤ [A : A_x] ≤ |Ω|`, a contradiction.
-/

@[expose] public section

namespace GraphIso.AltQuot

open Equiv MulAction

variable {Ω Λ : Type} [Fintype Ω] [DecidableEq Ω] [Fintype Λ] [DecidableEq Λ]

/-- `φ` is a **giant representation**: its image contains `Alt(Λ)`. -/
def IsGiant {G : Subgroup (Perm Ω)} (φ : G →* Perm Λ) : Prop := alternatingGroup Λ ≤ φ.range

/-- `x` is **affected** by `φ` (Babai, Def. 8.3.4): `φ(G_x)` does not contain `Alt(Λ)`. -/
def IsAffected {G : Subgroup (Perm Ω)} (φ : G →* Perm Λ) (x : Ω) : Prop :=
  ¬ alternatingGroup Λ ≤ (stabilizer G x).map φ

section Aux

omit [Fintype Ω] [DecidableEq Ω]

omit [DecidableEq Λ] in
theorem five_le_nat_card (h5 : 5 ≤ Fintype.card Λ) : 5 ≤ Nat.card Λ := by
  rwa [Nat.card_eq_fintype_card]

/-- `Alt(Λ)` is nonabelian for `|Λ| ≥ 5`. -/
theorem alternatingGroup_nonabelian (h5 : 5 ≤ Fintype.card Λ) :
    ∃ a b : alternatingGroup Λ, a * b ≠ b * a := by
  by_contra hc
  push Not at hc
  have := alternatingGroup.isSimpleGroup (five_le_nat_card h5)
  have h := alternatingGroup_commutator h5
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer.2
    (fun a _ => Subgroup.mem_centralizer_iff.2 fun b _ => hc b a)] at h
  obtain ⟨a, ha⟩ := exists_ne (1 : alternatingGroup Λ)
  exact ha (by rw [← Subgroup.mem_bot, h]; trivial)

/-- **Simple quotient of a subdirect product**, with the intersection of the `M i` only inside
the kernel: pass to the quotient by the intersection and apply `exists_le_ker_of_simple`. -/
theorem exists_le_ker_of_simple_of_le {G S : Type*} [Group G] [Group S] [IsSimpleGroup S]
    (hS : ∃ a b : S, a * b ≠ b * a) {ι : Type*} [Finite ι] (M : ι → Subgroup G)
    (hM : ∀ i, (M i).Normal) (φ : G →* S) (hinf : ⨅ i, M i ≤ φ.ker)
    (hφ : Function.Surjective φ) : ∃ i, M i ≤ φ.ker := by
  set A := ⨅ i, M i with hA
  have : A.Normal := Subgroup.normal_iInf_normal hM
  let ψ : G ⧸ A →* S := QuotientGroup.lift A φ hinf
  have hψ : Function.Surjective ψ := by
    intro s
    obtain ⟨g, rfl⟩ := hφ s
    exact ⟨g, rfl⟩
  let M' : ι → Subgroup (G ⧸ A) := fun i => (M i).map (QuotientGroup.mk' A)
  have hM' : ∀ i, (M' i).Normal := fun i => (hM i).map _ (QuotientGroup.mk'_surjective A)
  have hinf' : ⨅ i, M' i = ⊥ := by
    rw [eq_bot_iff]
    intro q hq
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective A q
    rw [Subgroup.mem_iInf] at hq
    have hg : g ∈ A := by
      rw [hA, Subgroup.mem_iInf]
      intro i
      obtain ⟨m, hm, e⟩ := Subgroup.mem_map.1 (hq i)
      have : m⁻¹ * g ∈ A := QuotientGroup.eq.1 e
      have hmi : m⁻¹ * g ∈ M i := (iInf_le M i) this
      simpa using (M i).mul_mem hm hmi
    rw [Subgroup.mem_bot]
    exact (QuotientGroup.eq_one_iff g).2 hg
  obtain ⟨i, hi⟩ := exists_le_ker_of_simple hS M' hM' hinf' ψ hψ
  refine ⟨i, fun m hm => ?_⟩
  have := hi (Subgroup.mem_map_of_mem (QuotientGroup.mk' A) hm)
  simpa [ψ, MonoidHom.mem_ker] using this

/-- The intermediate quotient `G ⧸ M` by a maximal subgroup `M ≥ G_x` is at most as large as
the orbit. -/
theorem index_le_of_le {G : Type} [Group G] [Finite G] {H M : Subgroup G} (h : H ≤ M) :
    M.index ≤ H.index :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)) (Subgroup.index_dvd_of_le h)

/-- **Babai's Lemma 8.3.1 for an abstract transitive action** whose kernel lies in `ker φ`, by
induction on the order of the group. -/
theorem stab_map_ne_top_aux {K : ℕ → ℕ} (hL : AltQuotientIso K) (hK : Monotone K)
    (h5 : 5 ≤ Fintype.card Λ) :
    ∀ (n : ℕ) (G : Type) [Group G] [Finite G] (X : Type) [Finite X] [MulAction G X]
      [IsPretransitive G X] (φ : G →* alternatingGroup Λ), Nat.card G ≤ n →
      Function.Surjective φ → (∀ g : G, (∀ y : X, g • y = y) → φ g = 1) →
      K (Nat.card X) ≤ Fintype.card Λ → Nat.card X < (Fintype.card Λ).factorial / 2 →
      ∀ x : X, (stabilizer G x).map φ ≠ ⊤ := by
  have hS := alternatingGroup.isSimpleGroup (five_le_nat_card h5)
  have hnt : Nontrivial Λ := by
    rw [← Finite.one_lt_card_iff_nontrivial, Nat.card_eq_fintype_card]
    omega
  intro n
  induction n with
  | zero =>
    intro G _ _ X _ _ _ φ hG
    have := Nat.card_pos (α := G)
    omega
  | succ n ih =>
    intro G _ _ X _ _ _ φ hG hφ hfac hk hn x hx
    classical
    set H := stabilizer G x with hHdef
    -- `G = G_x ker φ`
    have hHN : ∀ g : G, ∃ h ∈ H, φ h = φ g := by
      intro g
      have : φ g ∈ H.map φ := by rw [hx]; trivial
      exact Subgroup.mem_map.1 this
    by_cases hHtop : H = ⊤
    · -- `G` fixes `x`, hence every point: `φ` would be trivial
      have hfix : ∀ g : G, g • x = x := fun g => by
        have : g ∈ H := by rw [hHtop]; trivial
        exact this
      have htriv : ∀ g : G, ∀ y : X, g • y = y := by
        intro g y
        obtain ⟨g', rfl⟩ := exists_smul_eq G x y
        rw [hfix g', hfix g]
      obtain ⟨a, ha⟩ := exists_ne (1 : alternatingGroup Λ)
      obtain ⟨g, rfl⟩ := hφ a
      exact ha (hfac g (htriv g))
    -- a maximal subgroup `M ≥ G_x` and the primitive action on `G ⧸ M`
    obtain ⟨M, hMc, hHM⟩ := (eq_top_or_exists_le_coatom H).resolve_left hHtop
    have hYnt : Nontrivial (G ⧸ M) := by
      rw [← Finite.one_lt_card_iff_nontrivial, ← Subgroup.index]
      exact Subgroup.one_lt_index_of_ne_top hMc.1
    have hYprim : IsPreprimitive G (G ⧸ M) :=
      (isCoatom_stabilizer_iff_preprimitive G ((1 : G) : G ⧸ M)).1
        (by rwa [MulAction.stabilizer_quotient])
    set A := (MulAction.toPermHom G (G ⧸ M)).ker with hAdef
    have hAnorm : A.Normal := MonoidHom.normal_ker _
    have hmemA : ∀ a : G, a ∈ A ↔ ∀ q : G ⧸ M, a • q = q := by
      intro a
      rw [hAdef, MonoidHom.mem_ker, Equiv.Perm.ext_iff]
      rfl
    have hAM : A ≤ M := by
      intro a ha
      have := (hmemA a).1 ha ((1 : G) : G ⧸ M)
      rw [← MulAction.stabilizer_quotient M]
      exact this
    have hcardY : Nat.card (G ⧸ M) ≤ Nat.card X := by
      rw [← Subgroup.index, ← index_stabilizer_of_transitive G x]
      exact index_le_of_le hHM
    have hAn : (A.map φ).Normal := Subgroup.Normal.map hAnorm φ hφ
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (A.map φ) with hbot | htop
    · -- `A ≤ ker φ`: `φ` factors through the primitive image, which `hL` makes injective
      have hAN : A ≤ φ.ker := by
        intro a ha
        have : φ a ∈ A.map φ := Subgroup.mem_map_of_mem φ ha
        rw [hbot, Subgroup.mem_bot] at this
        exact this
      set ρ := (MulAction.toPermHom G (G ⧸ M)).rangeRestrict
      have hρ : Function.Surjective ρ := MonoidHom.rangeRestrict_surjective _
      have hρker : ρ.ker = A := MonoidHom.ker_rangeRestrict _
      let ψ : (MulAction.toPermHom G (G ⧸ M)).range →* alternatingGroup Λ :=
        ρ.liftOfRightInverse (Function.surjInv hρ) (Function.rightInverse_surjInv hρ)
          ⟨φ, hρker ▸ hAN⟩
      have hψρ : ∀ g, ψ (ρ g) = φ g := fun g =>
        MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ g
      have hψ : Function.Surjective ψ := by
        intro a
        obtain ⟨g, rfl⟩ := hφ a
        exact ⟨ρ g, hψρ g⟩
      have hPprim : IsPreprimitive (MulAction.toPermHom G (G ⧸ M)).range (G ⧸ M) := by
        let f : (G ⧸ M) →ₑ[ρ] (G ⧸ M) := ⟨id, fun _ _ => rfl⟩
        exact IsPreprimitive.of_surjective (f := f) Function.surjective_id
      have : Fintype (G ⧸ M) := Fintype.ofFinite _
      have hinj := hL (G ⧸ M) (MulAction.toPermHom G (G ⧸ M)).range hPprim Λ ψ hψ
        (by rw [← Nat.card_eq_fintype_card]; exact (hK hcardY).trans hk)
      have hNA : φ.ker ≤ A := by
        intro g hg
        rw [← hρker, MonoidHom.mem_ker]
        apply hinj
        rw [hψρ, map_one]
        exact hg
      apply hMc.1
      rw [eq_top_iff]
      intro g _
      obtain ⟨h, hh, e⟩ := hHN g
      have h1 : h⁻¹ * g ∈ φ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, e, inv_mul_cancel]
      have h2 : h⁻¹ * g ∈ M := hAM (hNA h1)
      simpa using M.mul_mem (hHM hh) h2
    · -- `φ(A) = Alt(Λ)`: go down to an orbit of `A`
      have hAφ : Function.Surjective (φ.comp A.subtype) := by
        intro a
        have : a ∈ A.map φ := by rw [htop]; trivial
        obtain ⟨g, hg, e⟩ := Subgroup.mem_map.1 this
        exact ⟨⟨g, hg⟩, e⟩
      -- the kernels of `A` on its orbits
      let Mo : X → Subgroup A := fun y => (MulAction.toPermHom A (orbit A y)).ker
      have hMo : ∀ y, (Mo y).Normal := fun y => MonoidHom.normal_ker _
      have hmemMo : ∀ (a : A) (y : X), a ∈ Mo y ↔ ∀ z ∈ orbit A y, (a : G) • z = z := by
        intro a y
        constructor
        · intro ha z hz
          exact congrArg Subtype.val (Equiv.Perm.ext_iff.1 ((MonoidHom.mem_ker).1 ha) ⟨z, hz⟩)
        · intro h
          rw [MonoidHom.mem_ker, Equiv.Perm.ext_iff]
          intro w
          exact Subtype.ext (h w.1 w.2)
      have hinf : ⨅ y, Mo y ≤ (φ.comp A.subtype).ker := by
        intro a ha
        rw [Subgroup.mem_iInf] at ha
        rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
        apply hfac
        intro z
        exact (hmemMo a z).1 (ha z) z (mem_orbit_self z)
      obtain ⟨y, hy⟩ :=
        exists_le_ker_of_simple_of_le (alternatingGroup_nonabelian h5) Mo hMo _ hinf hAφ
      -- the kernel on the orbit of `x` is conjugate to the one on the orbit of `y`
      obtain ⟨g, hgy⟩ := exists_smul_eq G y x
      have hMx : ∀ a : A, (∀ z ∈ orbit A x, (a : G) • z = z) → φ a = 1 := by
        intro a ha
        have hb : g⁻¹ * (a : G) * g ∈ A := by
          have := hAnorm.conj_mem (a : G) a.2 g⁻¹
          simpa using this
        have hbM : (⟨g⁻¹ * a * g, hb⟩ : A) ∈ Mo y := by
          rw [hmemMo]
          intro z hz
          obtain ⟨c, rfl⟩ := hz
          have hc' : g * (c : G) * g⁻¹ ∈ A := hAnorm.conj_mem _ c.2 g
          have hkey : (g * (c : G) * g⁻¹) • x = g • ((c : G) • y) := by
            rw [← hgy, ← mul_smul, ← mul_smul, mul_assoc (g * (c : G)), inv_mul_cancel,
              mul_one, mul_smul]
          have hfix : (a : G) • ((g * (c : G) * g⁻¹) • x) = (g * (c : G) * g⁻¹) • x :=
            ha _ ⟨⟨_, hc'⟩, rfl⟩
          show (g⁻¹ * (a : G) * g) • ((c : G) • y) = (c : G) • y
          rw [mul_smul, mul_smul, ← hkey, hfix, hkey, ← mul_smul, inv_mul_cancel, one_smul]
        have := hy hbM
        rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at this
        change φ (g⁻¹ * (a : G) * g) = 1 at this
        rw [map_mul, map_mul, map_inv] at this
        have e : φ a = φ g * ((φ g)⁻¹ * φ a * φ g) * (φ g)⁻¹ := by group
        rw [e, this, mul_one, mul_inv_cancel]
      -- induction on `A` acting on the orbit of `x`
      have hAlt : A < ⊤ := lt_of_le_of_lt hAM (lt_top_iff_ne_top.2 hMc.1)
      have hcardA : Nat.card A ≤ n := by
        have := Subgroup.card_lt_of_lt hAlt
        rw [Subgroup.card_top] at this
        omega
      have hOle : Nat.card (orbit A x) ≤ Nat.card X := Finite.card_subtype_le _
      have hrec := ih A (orbit A x) (φ.comp A.subtype) hcardA hAφ
        (fun a ha => hMx a fun z hz => congrArg Subtype.val (ha ⟨z, hz⟩))
        ((hK hOle).trans hk) (lt_of_le_of_lt hOle hn) ⟨x, mem_orbit_self x⟩
      have hstab : stabilizer A (⟨x, mem_orbit_self x⟩ : orbit A x) = stabilizer A x := by
        ext a
        simp only [mem_stabilizer_iff]
        exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
      rw [hstab] at hrec
      -- `φ(A_x)` is normal in `φ(G_x) = Alt(Λ)`, hence trivial
      have hAxn : ((stabilizer A x).map (φ.comp A.subtype)).Normal := by
        constructor
        intro s hs t
        obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hs
        have : t ∈ H.map φ := by rw [hx]; trivial
        obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.1 this
        have hh' : h • x = x := hh
        refine Subgroup.mem_map.2 ⟨⟨h * a * h⁻¹, hAnorm.conj_mem _ a.2 h⟩, ?_, ?_⟩
        · rw [mem_stabilizer_iff]
          have ha' : (a : G) • x = x := ha
          show (h * (a : G) * h⁻¹) • x = x
          have hinv : h⁻¹ • x = x := by rw [inv_smul_eq_iff, hh']
          rw [mul_smul, mul_smul, hinv, ha', hh']
        · simp [map_mul]
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
          ((stabilizer A x).map (φ.comp A.subtype)) with hb | ht
      · have hle : stabilizer A x ≤ (φ.comp A.subtype).ker := by
          intro a ha
          have : (φ.comp A.subtype) a ∈ (stabilizer A x).map (φ.comp A.subtype) :=
            Subgroup.mem_map_of_mem _ ha
          rw [hb, Subgroup.mem_bot] at this
          exact this
        have h1 := index_le_of_le hle
        have h2 : (φ.comp A.subtype).ker.index = (Fintype.card Λ).factorial / 2 := by
          rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hAφ, Subgroup.card_top,
            nat_card_alternatingGroup, Nat.card_eq_fintype_card]
        have h3 : (stabilizer A x).index ≤ Nat.card X := by
          rw [index_stabilizer, ← Nat.card_coe_set_eq]
          exact hOle
        omega
      · exact hrec ht

end Aux

omit [DecidableEq Ω] in
/-- **Transitive groups** (Babai, Lemma 8.3.1; Helfgott, Lemma 4.3 (a)). -/
theorem stabilizer_map_ne_top {K : ℕ → ℕ} (hL : AltQuotientIso K) (hK : Monotone K)
    (G : Subgroup (Perm Ω)) [IsPretransitive G Ω] (φ : G →* alternatingGroup Λ)
    (hφ : Function.Surjective φ) (h5 : 5 ≤ Fintype.card Λ)
    (hk : K (Fintype.card Ω) ≤ Fintype.card Λ)
    (hn : Fintype.card Ω < (Fintype.card Λ).factorial / 2) (x : Ω) :
    (stabilizer G x).map φ ≠ ⊤ := by
  refine stab_map_ne_top_aux hL hK h5 (Nat.card G) G Ω φ le_rfl hφ (fun g hg => ?_)
    (by rwa [Nat.card_eq_fintype_card]) (by rwa [Nat.card_eq_fintype_card]) x
  have : g = 1 := Subtype.ext (Equiv.ext hg)
  rw [this, map_one]

omit [DecidableEq Ω] in
/-- **Some point is affected** (Babai, Lemma 8.3.3; Helfgott, Lemma 4.3 (b)). -/
theorem exists_affected {K : ℕ → ℕ} (hL : AltQuotientIso K) (hK : Monotone K)
    (G : Subgroup (Perm Ω)) (φ : G →* alternatingGroup Λ) (hφ : Function.Surjective φ)
    (h5 : 5 ≤ Fintype.card Λ) {N : ℕ} (hN : ∀ x : Ω, Nat.card (orbit G x) ≤ N)
    (hk : K N ≤ Fintype.card Λ) (hn : N < (Fintype.card Λ).factorial / 2) :
    ∃ x : Ω, (stabilizer G x).map φ ≠ ⊤ := by
  have hS := alternatingGroup.isSimpleGroup (five_le_nat_card h5)
  -- the kernels of `G` on its orbits meet trivially; one of them lies in `ker φ`
  let Mo : Ω → Subgroup G := fun y => (MulAction.toPermHom G (orbit G y)).ker
  have hMo : ∀ y, (Mo y).Normal := fun y => MonoidHom.normal_ker _
  have hmemMo : ∀ (g : G) (y : Ω), g ∈ Mo y ↔ ∀ z ∈ orbit G y, g • z = z := by
    intro g y
    constructor
    · intro hg z hz
      exact congrArg Subtype.val (Equiv.Perm.ext_iff.1 ((MonoidHom.mem_ker).1 hg) ⟨z, hz⟩)
    · intro h
      rw [MonoidHom.mem_ker, Equiv.Perm.ext_iff]
      intro w
      exact Subtype.ext (h w.1 w.2)
  have hinf : ⨅ y, Mo y ≤ φ.ker := by
    intro g hg
    rw [Subgroup.mem_iInf] at hg
    have : g = 1 :=
      Subtype.ext (Equiv.ext fun z => (hmemMo g z).1 (hg z) z (mem_orbit_self z))
    rw [this, MonoidHom.mem_ker, map_one]
  obtain ⟨y, hy⟩ :=
    exists_le_ker_of_simple_of_le (alternatingGroup_nonabelian h5) Mo hMo φ hinf hφ
  -- `φ` factors through the restriction to the orbit of `y`: Lemma 8.3.1 there
  refine ⟨y, ?_⟩
  have hOle := hN y
  have hrec := stab_map_ne_top_aux hL hK h5 (Nat.card G) G (orbit G y) φ le_rfl hφ
    (fun g hg => hy ((hmemMo g y).2 fun z hz => congrArg Subtype.val (hg ⟨z, hz⟩)))
    ((hK hOle).trans hk) (lt_of_le_of_lt hOle hn) ⟨y, mem_orbit_self y⟩
  have hstab : stabilizer G (⟨y, mem_orbit_self y⟩ : orbit G y) = stabilizer G y := by
    ext g
    simp only [mem_stabilizer_iff]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  rwa [hstab] at hrec

end GraphIso.AltQuot
