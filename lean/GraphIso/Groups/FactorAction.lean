module

public import GraphIso.Groups.SolvableLinear
public import GraphIso.Groups.Sections
public import GraphIso.Groups.MinimalNormal

/-!
# The action on a set of factors

`card_le_of_factors`: let `F` be a finite set of subgroups of order at most `k` of a finite group
`X` with bounded sections, permuted by conjugation by a subgroup `Y`, and `N` their supremum.
Then `|Y| ≤ |C_Y(N)| (k! 2^k)^{|F|}`.

* The image of `Y` in `Sym(F)` has every Sylow `r`-subgroup of order at most `2^{|F| - 1}`
  (`card_le_two_pow_of_isPGroup_perm`), and at most `k` primes divide its order; so it has order
  at most `2^{k |F|}`.
* The kernel acts on each factor `A` by conjugation, through `Sym(A)` of order `|A|! ≤ k!`, and
  the kernel of that action centralizes every factor, hence `N`.
-/

@[expose] public section

namespace GraphIso.Groups

variable {X : Type*} [Group X]

/-- **The action on the factors.** -/
theorem card_le_of_factors [Finite X] {k : ℕ} (hk : BoundedSections k X) {Y N : Subgroup X}
    (F : Finset (Subgroup X)) (hFk : ∀ A ∈ F, Nat.card A ≤ k)
    (hFN : (⨆ A : F, (A : Subgroup X)) = N) (hcjF : ∀ g ∈ Y, ∀ A ∈ F, cj g A ∈ F) :
    Nat.card Y ≤ Nat.card (Y ⊓ Subgroup.centralizer (N : Set X) : Subgroup X) *
      (k.factorial * 2 ^ k) ^ F.card := by
  classical
  -- the action on the factors
  let φ : Y →* Equiv.Perm F :=
    { toFun := fun y =>
        { toFun := fun A => ⟨cj (y : X) A, hcjF y y.2 A A.2⟩
          invFun := fun A => ⟨cj (y : X)⁻¹ A, hcjF _ (Y.inv_mem y.2) A A.2⟩
          left_inv := fun A => Subtype.ext (by
            change cj (y : X)⁻¹ (cj (y : X) A) = A
            rw [cj_mul, inv_mul_cancel, cj_one])
          right_inv := fun A => Subtype.ext (by
            change cj (y : X) (cj (y : X)⁻¹ A) = A
            rw [cj_mul, mul_inv_cancel, cj_one]) }
      map_one' := Equiv.ext fun A => Subtype.ext (cj_one (A : Subgroup X))
      map_mul' := fun x y => Equiv.ext fun A => Subtype.ext (cj_mul (x : X) y A).symm }
  have hFc : Nat.card F = F.card := by simp
  -- the image
  have hrange : Nat.card φ.range ≤ 2 ^ (k * F.card) := by
    have hbs : BoundedSections k φ.range :=
      (hk.subgroup Y).of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
    have hpf := hbs.card_primeFactors_le
    calc Nat.card φ.range ≤ ∏ r ∈ (Nat.card φ.range).primeFactors, 2 ^ (Nat.card F - 1) := by
          refine card_le_prod_of_sylow _ fun r hr S => ?_
          have : Fact r.Prime := ⟨Nat.prime_of_mem_primeFactors hr⟩
          rw [← Subgroup.card_map_of_injective (K := (S : Subgroup φ.range))
            φ.range.subtype_injective]
          exact card_le_two_pow_of_isPGroup_perm _ (S.isPGroup'.map _)
      _ = 2 ^ ((Nat.card F - 1) * (Nat.card φ.range).primeFactors.card) := by
          rw [Finset.prod_const, ← pow_mul]
      _ ≤ 2 ^ (k * F.card) := by
          refine Nat.pow_le_pow_right (by norm_num) ?_
          rw [hFc, mul_comm k]
          exact Nat.mul_le_mul (Nat.sub_le _ _) hpf
  -- the kernel acts on each factor
  have hker : ∀ g ∈ φ.ker, ∀ A : F, cj ((g : Y) : X) A = A := fun g hg A => by
    have := congrArg (fun σ : Equiv.Perm F => (σ A : Subgroup X)) (MonoidHom.mem_ker.1 hg)
    exact this
  let e : φ.ker →* X := Y.subtype.comp φ.ker.subtype
  have he : Function.Injective e := Y.subtype_injective.comp φ.ker.subtype_injective
  have hmemA : ∀ (g : φ.ker) (A : F) (a : X), a ∈ (A : Subgroup X) →
      e g * a * (e g)⁻¹ ∈ (A : Subgroup X) := fun g A a ha => by
    have h := hker g g.2 A
    rw [← h, mem_cj]
    simpa [e, mul_assoc] using ha
  let ψ : φ.ker →* (∀ A : F, Equiv.Perm (A : Subgroup X)) :=
    { toFun := fun g A =>
        { toFun := fun a => ⟨e g * a * (e g)⁻¹, hmemA g A a a.2⟩
          invFun := fun a => ⟨e g⁻¹ * a * (e g⁻¹)⁻¹, hmemA g⁻¹ A a a.2⟩
          left_inv := fun a => Subtype.ext (by simp [mul_assoc])
          right_inv := fun a => Subtype.ext (by simp [mul_assoc]) }
      map_one' := by
        ext A a
        simp
      map_mul' := fun g h => by
        ext A a
        simp [mul_assoc] }
  -- its kernel centralizes `N`
  have hcen : ∀ g ∈ ψ.ker, e g ∈ Subgroup.centralizer (N : Set X) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [SetLike.mem_coe, ← hFN] at hx
    refine Subgroup.iSup_induction (fun A : F => (A : Subgroup X)) hx
      (C := fun x => x * e g = e g * x) (fun A a ha => ?_) (by simp)
      (fun x y hx hy => by rw [mul_assoc, hy, ← mul_assoc, hx, mul_assoc])
    have := congrArg (fun σ : ∀ A : F, Equiv.Perm (A : Subgroup X) =>
      ((σ A ⟨a, ha⟩ : (A : Subgroup X)) : X)) (MonoidHom.mem_ker.1 hg)
    simp only [ψ, MonoidHom.coe_mk, OneHom.coe_mk, Equiv.coe_fn_mk, Pi.one_apply,
      Equiv.Perm.coe_one, id_eq] at this
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  have hkerψ : Nat.card ψ.ker ≤
      Nat.card (Y ⊓ Subgroup.centralizer (N : Set X) : Subgroup X) := by
    refine Nat.card_le_card_of_injective
      (fun g => ⟨e g, ⟨((g : φ.ker) : Y).2, hcen g g.2⟩⟩) fun g h hgh => ?_
    have h1 : e g = e h :=
      congrArg (fun z : (Y ⊓ Subgroup.centralizer (N : Set X) : Subgroup X) => (z : X)) hgh
    exact Subtype.ext (he h1)
  have hrangeψ : Nat.card ψ.range ≤ k.factorial ^ F.card := by
    calc Nat.card ψ.range ≤ Nat.card (∀ A : F, Equiv.Perm (A : Subgroup X)) :=
          Subgroup.card_le_card_group _
      _ = ∏ A : F, (Nat.card (A : Subgroup X)).factorial := by
          rw [Nat.card_pi]
          simp only [Nat.card_perm]
      _ ≤ k.factorial ^ (Finset.univ : Finset F).card :=
          Finset.prod_le_pow_card _ _ _ fun A _ => Nat.factorial_le (hFk A A.2)
      _ = k.factorial ^ F.card := by simp
  calc Nat.card Y = Nat.card φ.ker * Nat.card φ.range := card_eq_card_ker_mul_card_range φ
    _ = Nat.card ψ.ker * Nat.card ψ.range * Nat.card φ.range := by
        rw [card_eq_card_ker_mul_card_range ψ]
    _ ≤ Nat.card (Y ⊓ Subgroup.centralizer (N : Set X) : Subgroup X) * k.factorial ^ F.card *
        2 ^ (k * F.card) := Nat.mul_le_mul (Nat.mul_le_mul hkerψ hrangeψ) hrange
    _ = Nat.card (Y ⊓ Subgroup.centralizer (N : Set X) : Subgroup X) *
        (k.factorial * 2 ^ k) ^ F.card := by
        rw [mul_pow, pow_mul, mul_assoc]

end GraphIso.Groups
