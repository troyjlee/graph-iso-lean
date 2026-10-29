module

public import GraphIso.Groups.SolvableLinear
public import Mathlib.GroupTheory.GroupAction.Primitive
public import Mathlib.Algebra.Module.ZMod

/-!
# Primitive solvable groups

* `exists_abelian_normal`: a nontrivial solvable group has a nontrivial abelian normal subgroup
  (the last nontrivial term of its derived series).
* `exists_elementary_abelian_normal`: it even has one of prime exponent; more generally, every
  nontrivial abelian normal subgroup contains one (`exists_elementary_of_abelian`).
* `isPretransitive_of_ne_bot`: in a quasiprimitive group, nontrivial normal subgroups are
  transitive.
* `card_le_of_isQuasiPreprimitive_of_abelian`: the affine reduction below, for any
  quasiprimitive group with a nontrivial abelian normal subgroup: a bound `k^e` for the point
  stabilizers as linear groups gives `|G| ≤ k^{e + 1}`. Milestone 8 uses it for groups with
  bounded sections.
* `card_le_of_isQuasiPreprimitive_of_isSolvable`: a quasiprimitive solvable permutation group
  of degree `k ≥ 2` whose order has `s + 1` prime divisors has order at most `k^{12 s + 1}`;
  `card_le_of_isPreprimitive_of_isSolvable` for primitive groups.

For the bound: a nontrivial elementary abelian normal subgroup `V` of exponent `p` is transitive
(`IsQuasiPreprimitive`) and abelian, hence regular, so `|V| = k`. The stabilizer `G_α` of a
point acts faithfully on `V` by conjugation, and has no nontrivial normal `p`-subgroup `Q`: the
fixed points of `Q` on `V` form a nontrivial subgroup normal in `G = V G_α`, hence transitive,
hence all of `V`. Then `card_le_of_isSolvable_linear` bounds `|G_α|`, and `|G| = k |G_α|`.
-/

@[expose] public section

namespace GraphIso.Groups

open Equiv MulAction

/-- A nontrivial solvable group has a nontrivial abelian normal subgroup. -/
theorem exists_abelian_normal {G : Type*} [Group G] [Group.IsSolvable G] [Nontrivial G] :
    ∃ A : Subgroup G, A.Normal ∧ A ≠ ⊥ ∧ ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
  obtain ⟨m, hm, h1⟩ := exists_derivedSeries_last (G := G)
  refine ⟨derivedSeries G m, derivedSeries_normal G m, hm, ?_⟩
  rw [derivedSeries_succ] at h1
  intro x hx y hy
  exact ((Subgroup.mem_centralizer_iff.1
    (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h1 hx)) y hy).symm

/-- A nontrivial abelian normal subgroup of a finite group contains a nontrivial normal subgroup
of prime exponent. -/
theorem exists_elementary_of_abelian {G : Type*} [Group G] [Finite G] {A : Subgroup G}
    (hAn : A.Normal) (hA : A ≠ ⊥) (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) :
    ∃ p : ℕ, p.Prime ∧ ∃ V : Subgroup G, V ≤ A ∧ V.Normal ∧ V ≠ ⊥ ∧
      (∀ x ∈ V, ∀ y ∈ V, x * y = y * x) ∧ ∀ x ∈ V, x ^ p = 1 := by
  have : Nontrivial A := (Subgroup.nontrivial_iff_ne_bot A).2 hA
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (Finite.one_lt_card_iff_nontrivial.2 this).ne'
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' p hpd
  let V : Subgroup G :=
    { carrier := {x | x ∈ A ∧ x ^ p = 1}
      mul_mem' := fun {x y} hx hy => ⟨A.mul_mem hx.1 hy.1, by
        rw [Commute.mul_pow (hcomm x hx.1 y hy.1), hx.2, hy.2, one_mul]⟩
      one_mem' := ⟨A.one_mem, one_pow _⟩
      inv_mem' := fun {x} hx => ⟨A.inv_mem hx.1, by rw [inv_pow, hx.2, inv_one]⟩ }
  refine ⟨p, hp, V, fun x hx => hx.1, ⟨fun x hx g => ⟨hAn.conj_mem x hx.1 g, ?_⟩⟩, ?_,
    fun x hx y hy => hcomm x hx.1 y hy.1, fun x hx => hx.2⟩
  · rw [conj_pow, hx.2, mul_one, mul_inv_cancel]
  · intro h
    have hmem : (a : G) ∈ V := ⟨a.2, by
      rw [← Subgroup.coe_pow, ← ha, pow_orderOf_eq_one, Subgroup.coe_one]⟩
    rw [h, Subgroup.mem_bot] at hmem
    have : a = 1 := Subtype.ext hmem
    rw [this, orderOf_one] at ha
    exact hp.one_lt.ne ha

/-- A nontrivial finite solvable group has a nontrivial abelian normal subgroup of prime
exponent. -/
theorem exists_elementary_abelian_normal {G : Type*} [Group G] [Finite G] [Group.IsSolvable G]
    [Nontrivial G] :
    ∃ p : ℕ, p.Prime ∧ ∃ V : Subgroup G, V.Normal ∧ V ≠ ⊥ ∧
      (∀ x ∈ V, ∀ y ∈ V, x * y = y * x) ∧ ∀ x ∈ V, x ^ p = 1 := by
  obtain ⟨A, hAn, hA, hcomm⟩ := exists_abelian_normal (G := G)
  obtain ⟨p, hp, V, -, hV⟩ := exists_elementary_of_abelian hAn hA hcomm
  exact ⟨p, hp, V, hV⟩

/-- A transitive subgroup of `Sym(k)`, `k ≥ 2`, is nontrivial. -/
theorem nontrivial_of_isPretransitive {k : ℕ} (G : Subgroup (Perm (Fin k))) (hk : 2 ≤ k)
    [IsPretransitive G (Fin k)] : Nontrivial G := by
  obtain ⟨g, hg⟩ := exists_smul_eq G (⟨0, by omega⟩ : Fin k) ⟨1, by omega⟩
  refine ⟨⟨g, 1, fun h => ?_⟩⟩
  rw [h, one_smul] at hg
  exact absurd (congrArg Fin.val hg) (by simp)

/-- In a quasiprimitive subgroup of `Sym(k)`, every nontrivial normal subgroup is transitive. -/
theorem isPretransitive_of_ne_bot {k : ℕ} (G : Subgroup (Perm (Fin k)))
    [hq : IsQuasiPreprimitive G (Fin k)] (N : Subgroup G) (hN : N.Normal) (hNb : N ≠ ⊥) :
    IsPretransitive N (Fin k) := by
  refine hq.isPretransitive_of_normal ?_
  intro h
  apply hNb
  rw [eq_bot_iff]
  intro g hg
  have : g = 1 := Subtype.ext (Equiv.ext fun x => by
    have hx : x ∈ fixedPoints N (Fin k) := h ▸ Set.mem_univ x
    exact hx ⟨g, hg⟩)
  rw [this]
  exact Subgroup.one_mem _

/-- **The affine reduction**: let `G ≤ Sym(k)`, `k ≥ 2`, be quasiprimitive with a nontrivial
abelian normal subgroup. Then `G` has a regular normal subgroup `V`, elementary abelian of
prime exponent `p` dividing `|G|`, so `|V| = k`; a point stabilizer `S` acts faithfully on `V` by
conjugation, as a group of `ZMod p`-linear maps with no nontrivial normal `p`-subgroup; and
`|G| = k |S|`. So a bound `|S| ≤ k^e` for such linear groups gives `|G| ≤ k^{e + 1}`. -/
theorem card_le_of_isQuasiPreprimitive_of_abelian {k e : ℕ} (G : Subgroup (Perm (Fin k)))
    (hk : 2 ≤ k) [hq : IsQuasiPreprimitive G (Fin k)] {A : Subgroup G} (hAn : A.Normal)
    (hA : A ≠ ⊥) (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hlin : ∀ (p : ℕ) [Fact p.Prime] (V : Type) [AddCommGroup V] [Module (ZMod p) V]
      [Finite V] (S : Subgroup G) (ρ : S →* LinearMap.GeneralLinearGroup (ZMod p) V),
      Function.Injective ρ → (∀ Q : Subgroup S, Q.Normal → IsPGroup p Q → Q = ⊥) →
      p ∣ Nat.card G → Nat.card V = k → Nat.card S ≤ k ^ e) :
    Nat.card G ≤ k ^ (e + 1) := by
  classical
  have hfaith : ∀ g : G, (∀ x : Fin k, g • x = x) → g = 1 := fun g h =>
    Subtype.ext (Equiv.ext fun x => h x)
  set α : Fin k := ⟨0, by omega⟩
  -- every nontrivial normal subgroup is transitive
  have htrans := isPretransitive_of_ne_bot G
  -- the elementary abelian normal subgroup `V`, transitive and regular
  obtain ⟨p, hp, V, -, hVn, hV, hcomm, hexp⟩ := exists_elementary_of_abelian hAn hA hAc
  have : Fact p.Prime := ⟨hp⟩
  have hVt : IsPretransitive V (Fin k) := htrans V hVn hV
  have hreg : ∀ v : V, v • α = α → v = 1 := by
    intro v hv
    refine Subtype.ext (hfaith v fun x => ?_)
    obtain ⟨u, rfl⟩ := exists_smul_eq V α x
    change (v : G) • (u : G) • α = (u : G) • α
    rw [smul_smul, hcomm v v.2 u u.2, ← smul_smul]
    exact congrArg ((u : G) • ·) hv
  have hbij : Function.Bijective (fun v : V => v • α) := by
    refine ⟨fun u w h => ?_, fun x => exists_smul_eq V α x⟩
    have : (w⁻¹ * u) • α = α := by
      rw [mul_smul]
      exact inv_smul_eq_iff.2 h
    exact (inv_mul_eq_one.1 (hreg _ this)).symm
  have hVcard : Nat.card V = k := (Nat.card_eq_of_bijective _ hbij).trans (Nat.card_fin k)
  -- the stabilizer `S` of `α` and `|G| = k |S|`
  set S := stabilizer G α
  have hGS : Nat.card G = Nat.card S * k := by
    rw [← Subgroup.card_mul_index S, index_stabilizer_of_transitive G α, Nat.card_fin]
  -- elements of `S` commuting with `V` are trivial
  have hcent : ∀ s : G, s ∈ S → (∀ v ∈ V, s * v * s⁻¹ = v) → s = 1 := by
    intro s hs hsv
    refine hfaith s fun x => ?_
    obtain ⟨u, rfl⟩ := exists_smul_eq V α x
    change s • (u : G) • α = (u : G) • α
    have hus : s * u = u * s := by
      have := hsv u u.2
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this
    rw [smul_smul, hus, ← smul_smul, show s • α = α from hs]
  -- `V` as a `ZMod p`-space, and the faithful conjugation action of `S` on it
  let _ : CommGroup V :=
    { (inferInstance : Group V) with mul_comm := fun a b => Subtype.ext (hcomm a a.2 b b.2) }
  let _ : Module (ZMod p) (Additive V) := AddCommGroup.zmodModule fun x => by
    rw [← ofMul_toMul x, ← ofMul_pow]
    rw [show x.toMul ^ p = 1 from Subtype.ext (hexp _ x.toMul.2), ofMul_one]
  obtain ⟨toGL, htoGL, -⟩ := exists_mulAut_toGL p V
  have : V.Normal := hVn
  let ρ : S →* LinearMap.GeneralLinearGroup (ZMod p) (Additive V) :=
    toGL.comp ((MulAut.conjNormal (H := V)).comp S.subtype)
  have hconj : ∀ s : G, MulAut.conjNormal (H := V) s = 1 → ∀ v ∈ V, s * v * s⁻¹ = v := by
    intro s h v hv
    rw [← Subgroup.mem_centralizer_iff.1 (mem_centralizer_of_conjNormal_eq_one h) v hv]
    group
  have hρ : Function.Injective ρ := by
    refine (injective_iff_map_eq_one ρ).2 fun s hs => ?_
    have h1 : MulAut.conjNormal (H := V) (s : G) = 1 := htoGL (by rw [map_one]; exact hs)
    exact Subtype.ext (hcent s s.2 (hconj s h1))
  -- `S` has no nontrivial normal `p`-subgroup
  have hVp : IsPGroup p V := fun v => ⟨1, Subtype.ext (by simpa using hexp _ v.2)⟩
  have hVnt : Nontrivial V := (Subgroup.nontrivial_iff_ne_bot V).2 hV
  have hpV : p ∣ Nat.card V :=
    hVp.card_eq_or_dvd.resolve_left fun h => hV (Subgroup.card_eq_one.1 h)
  have hpS : ∀ Q : Subgroup S, Q.Normal → IsPGroup p Q → Q = ⊥ := by
    intro Q hQn hQ
    let φQ : Q →* MulAut V := (MulAut.conjNormal (H := V)).comp (S.subtype.comp Q.subtype)
    let _ : MulAction Q V := MulAction.compHom V φQ
    obtain ⟨u, hu, hne⟩ := hQ.exists_fixed_point_of_prime_dvd_card_of_fixed_point V hpV
      (a := 1) (fun q => map_one (φQ q))
    have hufix : ∀ q : Q, ((q : S) : G) * u * ((q : S) : G)⁻¹ = u := fun q =>
      congrArg Subtype.val (hu q)
    -- the fixed points of `Q` in `V`, as a subgroup of `G`
    let U : Subgroup G :=
      { carrier := {x | x ∈ V ∧ ∀ q : Q, ((q : S) : G) * x * ((q : S) : G)⁻¹ = x}
        mul_mem' := fun {x y} hx hy => ⟨V.mul_mem hx.1 hy.1, fun q => by
          rw [show ((q : S) : G) * (x * y) * ((q : S) : G)⁻¹ =
            (((q : S) : G) * x * ((q : S) : G)⁻¹) * (((q : S) : G) * y * ((q : S) : G)⁻¹)
            by group, hx.2 q, hy.2 q]⟩
        one_mem' := ⟨V.one_mem, fun q => by group⟩
        inv_mem' := fun {x} hx => ⟨V.inv_mem hx.1, fun q => by
          rw [show ((q : S) : G) * x⁻¹ * ((q : S) : G)⁻¹ =
            (((q : S) : G) * x * ((q : S) : G)⁻¹)⁻¹ by group, hx.2 q]⟩ }
    have hUn : U.Normal := by
      refine ⟨fun x hx g => ⟨hVn.conj_mem x hx.1 g, fun q => ?_⟩⟩
      obtain ⟨w, hw⟩ := exists_smul_eq V α (g • α)
      have hs : (w : G)⁻¹ * g ∈ S := by
        change ((w : G)⁻¹ * g) • α = α
        rw [mul_smul, inv_smul_eq_iff]
        exact hw.symm
      set s : G := (w : G)⁻¹ * g
      have hg : g = w * s := by simp [s]
      have hy : s * x * s⁻¹ ∈ V := hVn.conj_mem x hx.1 s
      have hgy : g * x * g⁻¹ = s * x * s⁻¹ := by
        rw [hg, show (w : G) * s * x * ((w : G) * s)⁻¹ =
          (w : G) * (s * x * s⁻¹) * (w : G)⁻¹ by group, hcomm _ w.2 _ hy,
          mul_inv_cancel_right]
      have hq' : (⟨s, hs⟩ : S)⁻¹ * (q : S) * (⟨s, hs⟩ : S) ∈ Q := by
        have := hQn.conj_mem (q : S) q.2 (⟨s, hs⟩ : S)⁻¹
        rwa [inv_inv] at this
      have hfix := hx.2 ⟨_, hq'⟩
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hfix
      rw [hgy]
      calc ((q : S) : G) * (s * x * s⁻¹) * ((q : S) : G)⁻¹
          = s * (s⁻¹ * ((q : S) : G) * s * x * (s⁻¹ * ((q : S) : G) * s)⁻¹) * s⁻¹ := by
            group
        _ = s * x * s⁻¹ := by rw [hfix]
    have hUb : U ≠ ⊥ := by
      intro h
      have hmem : (u : G) ∈ U := ⟨u.2, hufix⟩
      rw [h, Subgroup.mem_bot] at hmem
      exact hne (Subtype.ext hmem.symm)
    -- `U` is transitive, so `U = V`
    have hUt : IsPretransitive U (Fin k) := htrans U hUn hUb
    have hkU : k ≤ Nat.card U := (Nat.card_fin k).symm.trans_le
      (Nat.card_le_card_of_surjective (fun x : U => x • α) fun x => exists_smul_eq U α x)
    have hUV : U = V := Subgroup.eq_of_le_of_card_ge (fun x hx => hx.1) (hVcard.trans_le hkU)
    rw [eq_bot_iff]
    intro q hq
    have h1 := hcent (q : G) (q : S).2 fun v hv => by
      have hvU : v ∈ U := hUV ▸ hv
      exact hvU.2 ⟨q, hq⟩
    rw [Subgroup.mem_bot]
    exact Subtype.ext h1
  -- the bound for `S`
  have hS := hlin p (Additive V) S ρ hρ hpS (hpV.trans (Subgroup.card_subgroup_dvd_card V)) hVcard
  calc Nat.card G = Nat.card S * k := hGS
    _ ≤ k ^ e * k := Nat.mul_le_mul_right _ hS
    _ = k ^ (e + 1) := (pow_succ _ _).symm

/-- **Quasiprimitive solvable groups have polynomial order**: every nontrivial normal subgroup
transitive is all the argument uses. -/
theorem card_le_of_isQuasiPreprimitive_of_isSolvable {k : ℕ} (G : Subgroup (Perm (Fin k)))
    [Group.IsSolvable G] (hk : 2 ≤ k) [hq : IsQuasiPreprimitive G (Fin k)] :
    Nat.card G ≤ k ^ (12 * ((Nat.card G).primeFactors.card - 1) + 1) := by
  have : Nontrivial G := nontrivial_of_isPretransitive G hk
  obtain ⟨A, hAn, hA, hcomm⟩ := exists_abelian_normal (G := G)
  refine card_le_of_isQuasiPreprimitive_of_abelian G hk hAn hA hcomm
    fun p _ V _ _ _ S ρ hρ hpS hpG hVk => ?_
  -- the bound for `S`, and the count of primes
  have hS := card_le_of_isSolvable_linear ρ hρ hpS
  have hpf : ((Nat.card S).primeFactors.erase p).card ≤ (Nat.card G).primeFactors.card - 1 := by
    have h1 : (Nat.card S).primeFactors ⊆ (Nat.card G).primeFactors :=
      Nat.primeFactors_mono (Subgroup.card_subgroup_dvd_card S) Nat.card_pos.ne'
    have h2 : p ∈ (Nat.card G).primeFactors :=
      Nat.mem_primeFactors.2 ⟨Fact.out, hpG, Nat.card_pos.ne'⟩
    calc ((Nat.card S).primeFactors.erase p).card
        ≤ ((Nat.card G).primeFactors.erase p).card :=
          Finset.card_le_card (Finset.erase_subset_erase p h1)
      _ = (Nat.card G).primeFactors.card - 1 := Finset.card_erase_of_mem h2
  rw [hVk] at hS
  exact hS.trans (Nat.pow_le_pow_right (by omega) (by omega))

/-- **Primitive solvable groups have polynomial order**: a primitive solvable subgroup of
`Sym(k)`, `k ≥ 2`, whose order has `s + 1` prime divisors has order at most `k^{12 s + 1}`. -/
theorem card_le_of_isPreprimitive_of_isSolvable {k : ℕ} (G : Subgroup (Perm (Fin k)))
    [Group.IsSolvable G] (hk : 2 ≤ k) [IsPreprimitive G (Fin k)] :
    Nat.card G ≤ k ^ (12 * ((Nat.card G).primeFactors.card - 1) + 1) :=
  have : IsQuasiPreprimitive G (Fin k) := IsPreprimitive.isQuasiPreprimitive
  card_le_of_isQuasiPreprimitive_of_isSolvable G hk

end GraphIso.Groups
