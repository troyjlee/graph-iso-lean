module

public import GraphIso.Groups.LinearPGroup
public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.Abelianization.Finite
public import Mathlib.Algebra.Module.ZMod

/-!
# Coprime action on solvable groups

* `card_le_of_coprime`: a `p`-group of automorphisms of a finite solvable group `N` with
  `p ∤ |N|` has order at most `|N|³`.

The proof is by strong induction on `|N|`. For a prime `r` dividing the order of the
abelianization, let `E` be the abelianization modulo `r`-th powers, a nonzero `ZMod r`-space,
and `M` the kernel of `N → E`, a characteristic subgroup. An automorphism of order a power of
`p` acting trivially on `M` and on `E` is trivial (`map_one_of_isPGroup` applied to
`g ↦ x⁻¹ g(x)`), so `P` embeds in the product of its images in `Aut(M)` and in `GL(E)`, of
orders at most `|M|³` (induction) and `|E|³` (`card_le_of_isPGroup'`).
-/

@[expose] public section

namespace GraphIso.Groups

universe u

open LinearMap

/-- A homomorphism from a `p`-group to a finite group of order prime to `p` is trivial. -/
theorem map_one_of_isPGroup {p : ℕ} [Fact p.Prime] {G K : Type*} [Group G] [Group K] [Finite K]
    (hG : IsPGroup p G) (hK : ¬ p ∣ Nat.card K) (f : G →* K) (g : G) : f g = 1 := by
  have hr : IsPGroup p f.range := hG.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  obtain ⟨k, hk⟩ := hr.exists_card_eq
  have hdvd : Nat.card f.range ∣ Nat.card K := Subgroup.card_subgroup_dvd_card _
  have hk0 : k = 0 := by
    by_contra h
    exact hK ((dvd_pow_self p h).trans (hk ▸ hdvd))
  rw [hk0, pow_zero, Subgroup.card_eq_one] at hk
  have : f g ∈ f.range := ⟨g, rfl⟩
  rw [hk] at this
  exact this

/-- The automorphisms of an elementary abelian group act linearly on its additive form, by an
injective homomorphism into `GL`. -/
theorem exists_mulAut_toGL (r : ℕ) (E : Type*) [CommGroup E] [Module (ZMod r) (Additive E)] :
    ∃ f : MulAut E →* GeneralLinearGroup (ZMod r) (Additive E), Function.Injective f ∧
      ∀ e x, (f e : Additive E →ₗ[ZMod r] Additive E) x = Additive.ofMul (e x.toMul) := by
  refine ⟨{ toFun := fun e =>
              ⟨(MulEquiv.toAdditive e : Additive E →+ Additive E).toZModLinearMap r,
               (MulEquiv.toAdditive e.symm : Additive E →+ Additive E).toZModLinearMap r,
               LinearMap.ext fun x => by simp, LinearMap.ext fun x => by simp⟩
            map_one' := ?_
            map_mul' := fun e f => ?_ }, ?_, fun e x => rfl⟩
  · apply Units.ext
    apply LinearMap.ext
    intro x
    rfl
  · apply Units.ext
    apply LinearMap.ext
    intro x
    rfl
  · intro e f h
    refine MulEquiv.ext fun x => ?_
    have := LinearMap.congr_fun (congrArg Units.val h) (Additive.ofMul x)
    exact Additive.ofMul.injective this

/-- **Coprime automorphism groups of solvable groups are small**: `|P| ≤ |N|³`. -/
theorem card_le_of_coprime {p : ℕ} [Fact p.Prime] {N : Type u} [Group N] [Finite N]
    [Group.IsSolvable N] (hN : ¬ p ∣ Nat.card N) (P : Subgroup (MulAut N))
    (hP : IsPGroup p P) : Nat.card P ≤ Nat.card N ^ 3 := by
  induction hn : Nat.card N using Nat.strong_induction_on generalizing N with
  | _ n ih =>
  rw [← hn]
  rcases subsingleton_or_nontrivial N with hs | hs
  · have : Subsingleton (MulAut N) := ⟨fun e f => MulEquiv.ext fun x => Subsingleton.elim _ _⟩
    have h1 : Nat.card P ≤ 1 := Finite.card_le_one_iff_subsingleton.2 inferInstance
    have h2 : 1 ≤ Nat.card N ^ 3 := Nat.one_le_pow _ _ Nat.card_pos
    omega
  have hofs : Function.Surjective (Abelianization.of : N →* Abelianization N) :=
    fun x => Quot.inductionOn x fun a => ⟨a, (Abelianization.mk_eq_of a).symm⟩
  -- the elementary abelian quotient `E` of the abelianization
  have hAb : Nontrivial (Abelianization N) := by
    rw [Abelianization, QuotientGroup.nontrivial_iff]
    exact (Group.IsSolvable.commutator_lt_top_of_nontrivial N).ne
  obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd
    (Finite.one_lt_card_iff_nontrivial.2 hAb).ne'
  have : Fact r.Prime := ⟨hr⟩
  have hrN : r ∣ Nat.card N := hrd.trans (Subgroup.card_quotient_dvd_card (commutator N))
  have hrp : r ≠ p := fun h => hN (h ▸ hrN)
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' r hrd
  set R : Subgroup (Abelianization N) := (powMonoidHom r).range
  have hRtop : R ≠ ⊤ := by
    intro h
    have hsurj : Function.Surjective (powMonoidHom r : Abelianization N →* _) := by
      intro y
      have : y ∈ R := h ▸ Subgroup.mem_top y
      exact this
    have hinj := Finite.injective_iff_surjective.2 hsurj
    have : a = 1 := hinj (by simp [pow_orderOf_eq_one, ← ha])
    rw [this, orderOf_one] at ha
    exact hr.one_lt.ne ha
  have : Nontrivial (Abelianization N ⧸ R) := QuotientGroup.nontrivial_iff.2 hRtop
  have hRmap : ∀ φ : Abelianization N ≃* Abelianization N, R.map (φ : _ →* _) = R := by
    intro φ
    ext x
    constructor
    · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
      exact ⟨φ z, by simp⟩
    · rintro ⟨z, rfl⟩
      exact ⟨φ.symm z ^ r, ⟨φ.symm z, rfl⟩, by simp⟩
  -- the map `π : N → E` and its kernel `M`
  set E := Abelianization N ⧸ R
  set π : N →* E := (QuotientGroup.mk' R).comp Abelianization.of
  have hπs : Function.Surjective π := (QuotientGroup.mk'_surjective R).comp hofs
  set M : Subgroup N := π.ker with hM
  -- automorphisms of `N` descend to `E`
  let bar : MulAut N → MulAut E := fun e =>
    QuotientGroup.congr R R e.abelianizationCongr (hRmap _)
  have hbar : ∀ (e : MulAut N) (x : N), bar e (π x) = π (e x) := fun e x => rfl
  have hMchar : M.Characteristic := by
    refine Subgroup.characteristic_iff_le_comap.2 fun φ x hx => ?_
    rw [Subgroup.mem_comap, hM, MonoidHom.mem_ker] at *
    change π (φ x) = 1
    rw [← hbar, hx, map_one]
  let barE : MulAut N →* MulAut E :=
    { toFun := bar
      map_one' := MulEquiv.ext fun q => by
        obtain ⟨x, rfl⟩ := hπs q
        rw [hbar]
        rfl
      map_mul' := fun e f => MulEquiv.ext fun q => by
        obtain ⟨x, rfl⟩ := hπs q
        rw [hbar]
        rfl }
  -- `E` as a `ZMod r`-space, and the action of automorphisms on it
  have hexp : ∀ q : E, q ^ r = 1 := by
    intro q
    obtain ⟨x, rfl⟩ := hπs q
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).2 ⟨Abelianization.of x, by simp⟩
  let _ : Module (ZMod r) (Additive E) := AddCommGroup.zmodModule fun x => by
    rw [← ofMul_toMul x, ← ofMul_pow, hexp, ofMul_one]
  obtain ⟨toGL, htoGL, -⟩ := exists_mulAut_toGL r E
  let resE : MulAut N →* GeneralLinearGroup (ZMod r) (Additive E) := toGL.comp barE
  have hE1 : ∀ γ : MulAut N, resE γ = 1 → ∀ x, π (γ x) = π x := by
    intro γ h x
    have h' : barE γ = 1 := htoGL (by rw [map_one]; exact h)
    rw [← hbar]
    exact congrArg (fun f : MulAut E => f (π x)) h'
  have hM1 : ∀ γ : MulAut N, MulAut.characteristic M γ = 1 → ∀ m ∈ M, γ m = m := by
    intro γ h m hm
    exact congrArg (fun f : MulAut M => (f ⟨m, hm⟩ : N)) h
  -- an element of `P` acting trivially on `M` and on `E` is trivial
  have hMp : ¬ p ∣ Nat.card M := fun h => hN (h.trans (Subgroup.card_subgroup_dvd_card M))
  have hker : ∀ γ ∈ P, MulAut.characteristic M γ = 1 → resE γ = 1 → γ = 1 := by
    intro γ hγ h1 h2
    set P₀ : Subgroup (MulAut N) := P ⊓ (MulAut.characteristic M).ker ⊓ resE.ker
    have hP₀ : IsPGroup p P₀ := hP.to_le (inf_le_left.trans inf_le_left)
    refine MulEquiv.ext fun x => ?_
    let φ : P₀ →* M :=
      { toFun := fun g => ⟨x⁻¹ * (g : MulAut N) x, by
          rw [hM, MonoidHom.mem_ker, map_mul, map_inv, hE1 g (MonoidHom.mem_ker.1 g.2.2) x,
            inv_mul_cancel]⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun g h => Subtype.ext (by
          have hh : x⁻¹ * (h : MulAut N) x ∈ M := by
            rw [hM, MonoidHom.mem_ker, map_mul, map_inv,
              hE1 h (MonoidHom.mem_ker.1 h.2.2) x, inv_mul_cancel]
          change x⁻¹ * (g : MulAut N) ((h : MulAut N) x) =
            x⁻¹ * (g : MulAut N) x * (x⁻¹ * (h : MulAut N) x)
          conv_lhs => rw [show (h : MulAut N) x = x * (x⁻¹ * (h : MulAut N) x) by group]
          rw [map_mul, hM1 g (MonoidHom.mem_ker.1 g.2.1.2) _ hh]
          group) }
    have h0 := congrArg Subtype.val (map_one_of_isPGroup hP₀ hMp φ ⟨γ, ⟨hγ, h1⟩, h2⟩)
    exact (inv_mul_eq_one.1 h0).symm
  -- `P` embeds in the product of its images
  have hinj : Function.Injective (fun α : P =>
      ((⟨MulAut.characteristic M α, Subgroup.mem_map_of_mem _ α.2⟩ :
          P.map (MulAut.characteristic M)),
        (⟨resE α, Subgroup.mem_map_of_mem resE α.2⟩ : P.map resE))) := by
    intro α β h
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
    have := hker ((α : MulAut N)⁻¹ * β) (P.mul_mem (P.inv_mem α.2) β.2)
      (by rw [map_mul, map_inv, h.1, inv_mul_cancel])
      (by rw [map_mul, map_inv, h.2, inv_mul_cancel])
    exact Subtype.ext (inv_mul_eq_one.1 this)
  have : Finite (MulAut N) :=
    Finite.of_injective (fun e : MulAut N => (e : N → N)) fun e f h => MulEquiv.ext (congrFun h)
  have hfin : ∀ {K : Type u} [Group K] (f : MulAut N →* K), Finite (P.map f) := fun f =>
    Finite.of_surjective (fun α : P => (⟨f α, Subgroup.mem_map_of_mem _ α.2⟩ : P.map f))
      (by rintro ⟨_, ⟨α, hα, rfl⟩⟩; exact ⟨⟨α, hα⟩, rfl⟩)
  have := hfin (MulAut.characteristic M)
  have := hfin resE
  have hcard := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_prod] at hcard
  -- the orders
  have hNME : Nat.card N = Nat.card M * Nat.card E := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup M, mul_comm]
    congr 1
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπs).toEquiv
  have hE2 : 1 < Nat.card E := Finite.one_lt_card
  have hM0 : 0 < Nat.card M := Nat.card_pos
  have hlt : Nat.card M < Nat.card N := by
    rw [hNME]
    exact lt_mul_of_one_lt_right hM0 hE2
  have hMb := ih (Nat.card M) (hn ▸ hlt) (N := M) hMp (P.map (MulAut.characteristic M))
    (hP.map _) rfl
  have hEb := card_le_of_isPGroup' (p := r) (r := p) hrp (P.map resE) (hP.map _)
  calc Nat.card P ≤ _ := hcard
    _ ≤ Nat.card M ^ 3 * Nat.card (Additive E) ^ 3 := Nat.mul_le_mul hMb hEb
    _ = Nat.card N ^ 3 := by rw [hNME, mul_pow]; rfl

end GraphIso.Groups
