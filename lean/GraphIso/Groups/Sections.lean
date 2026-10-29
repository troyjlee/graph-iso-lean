module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Algebra.Group.Pi.Lemmas
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.PGroup

/-!
# Groups with bounded simple sections

`BoundedSections k G`: every simple section of `G` (a simple quotient `H/M` of a subgroup
`H ≤ G`) has order at most `k`. Every composition factor is a simple section, and every simple
section is a section of a composition factor (Jordan–Hölder), so this says that every
composition factor of `G` has order at most `k`.

* `BoundedSections.card_le`: the same for any surjection from a subgroup onto a simple group.
* Closure: under injective maps (`of_injective`, subgroups `subgroup`), surjective maps
  (`of_surjective`), extensions (`of_ker`: a map whose kernel and target have bounded
  sections) and finite products (`pi`).
* `le_of_prime_dvd_card`: every prime dividing `|G|` is at most `k`; so `|G|` has at most `k`
  prime divisors (`card_primeFactors_le`).
* `boundedSections_card`: a finite group has sections of order at most `|G|`; a finite
  `p`-group has sections of order `p` (`boundedSections_of_isPGroup`).
* `mono`: a bound may be raised.
-/

@[expose] public section

namespace GraphIso.Groups

/-- **Bounded simple sections**: every simple quotient of a subgroup has order at most `k`. -/
def BoundedSections (k : ℕ) (G : Type*) [Group G] : Prop :=
  ∀ (H : Subgroup G) (M : Subgroup H) [M.Normal], IsSimpleGroup (H ⧸ M) → Nat.card (H ⧸ M) ≤ k

variable {k : ℕ} {G : Type*} [Group G]

theorem BoundedSections.mono {k' : ℕ} (h : BoundedSections k G) (hk : k ≤ k') :
    BoundedSections k' G :=
  fun H M _ hs => (h H M hs).trans hk

/-- A simple group that is the image of a subgroup has order at most `k`. -/
theorem BoundedSections.card_le (h : BoundedSections k G) (H : Subgroup G) {S : Type*} [Group S]
    [IsSimpleGroup S] (f : H →* S) (hf : Function.Surjective f) : Nat.card S ≤ k := by
  have e : H ⧸ f.ker ≃* S := QuotientGroup.quotientKerEquivOfSurjective f hf
  have : IsSimpleGroup (H ⧸ f.ker) := e.isSimpleGroup
  rw [← Nat.card_congr e.toEquiv]
  exact h H f.ker this

/-- Sections of a group are sections of any group it embeds in. -/
theorem BoundedSections.of_injective {G' : Type*} [Group G'] (h : BoundedSections k G)
    (f : G' →* G) (hf : Function.Injective f) : BoundedSections k G' := by
  intro H M _ hs
  let e : H ≃* H.map f := H.equivMapOfInjective f hf
  exact h.card_le (H.map f) ((QuotientGroup.mk' M).comp e.symm.toMonoidHom)
    ((QuotientGroup.mk'_surjective M).comp e.symm.surjective)

theorem BoundedSections.subgroup (h : BoundedSections k G) (K : Subgroup G) :
    BoundedSections k K :=
  h.of_injective K.subtype K.subtype_injective

/-- Sections of a quotient are sections of the group. -/
theorem BoundedSections.of_surjective {G' : Type*} [Group G'] (h : BoundedSections k G)
    (f : G →* G') (hf : Function.Surjective f) : BoundedSections k G' := by
  intro H M _ hs
  let g : H.comap f →* H :=
    { toFun := fun x => ⟨f x.1, x.2⟩
      map_one' := Subtype.ext (map_one f)
      map_mul' := fun x y => Subtype.ext (map_mul f x.1 y.1) }
  have hg : Function.Surjective g := fun y => by
    obtain ⟨x, hx⟩ := hf y
    exact ⟨⟨x, show f x ∈ H by rw [hx]; exact y.2⟩, Subtype.ext hx⟩
  exact h.card_le (H.comap f) ((QuotientGroup.mk' M).comp g)
    ((QuotientGroup.mk'_surjective M).comp hg)

/-- **Extensions**: if the kernel and the target of `f` have bounded sections, so does the
source. -/
theorem BoundedSections.of_ker {G' : Type*} [Group G'] (f : G →* G')
    (hK : BoundedSections k f.ker) (hG' : BoundedSections k G') : BoundedSections k G := by
  intro H M _ hs
  let g : H →* H ⧸ M := QuotientGroup.mk' M
  have hg : Function.Surjective g := QuotientGroup.mk'_surjective M
  -- the part of the kernel in `H`
  let K : Subgroup H := f.ker.subgroupOf H
  have hKn : K.Normal := by
    refine ⟨fun x hx y => ?_⟩
    simp only [K, Subgroup.mem_subgroupOf, MonoidHom.mem_ker] at hx ⊢
    simp [hx]
  have hgK : (K.map g).Normal := Subgroup.Normal.map hKn g hg
  rcases hgK.eq_bot_or_eq_top with hb | ht
  · -- `g` kills the kernel: a section of `G'`
    let φ : H →* G' := f.comp H.subtype
    have hle : φ.ker ≤ g.ker := by
      intro x hx
      have hxK : x ∈ K := by
        simp only [K, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
        exact hx
      have : g x ∈ K.map g := Subgroup.mem_map_of_mem g hxK
      rw [hb, Subgroup.mem_bot] at this
      exact this
    let g' : φ.range →* H ⧸ M :=
      (QuotientGroup.lift φ.ker g hle).comp
        (QuotientGroup.quotientKerEquivRange φ).symm.toMonoidHom
    have hg' : Function.Surjective g' := by
      intro z
      obtain ⟨x, rfl⟩ := hg z
      refine ⟨(QuotientGroup.quotientKerEquivRange φ) (x : H ⧸ φ.ker), ?_⟩
      simp [g']
    exact hG'.card_le φ.range g' hg'
  · -- `g` is onto from the kernel: a section of `f.ker`
    let L : Subgroup f.ker := H.subgroupOf f.ker
    let e : L →* H :=
      { toFun := fun x => ⟨((x : f.ker) : G), x.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have he : Function.Surjective (g.comp e) := by
      intro z
      have hz : z ∈ K.map g := by rw [ht]; exact Subgroup.mem_top z
      obtain ⟨x, hx, rfl⟩ := hz
      have hx' : (x : G) ∈ f.ker := by simpa [K, Subgroup.mem_subgroupOf] using hx
      refine ⟨⟨⟨x, hx'⟩, ?_⟩, rfl⟩
      simp [L, Subgroup.mem_subgroupOf]
    exact hK.card_le L (g.comp e) he

/-- A group with at most one element has no simple section. -/
theorem boundedSections_of_subsingleton [Subsingleton G] (k : ℕ) : BoundedSections k G := by
  intro H M _ hs
  obtain ⟨x, hx⟩ := exists_ne (1 : H ⧸ M)
  induction x using QuotientGroup.induction_on with
  | H h =>
    refine absurd ?_ hx
    rw [Subsingleton.elim h 1]
    rfl

/-- **Finite products.** -/
theorem BoundedSections.pi {ι : Type*} [Finite ι] {G : ι → Type*} [∀ i, Group (G i)]
    (h : ∀ i, BoundedSections k (G i)) : BoundedSections k (∀ i, G i) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  -- the elements supported on `s`
  let P : Finset ι → Subgroup (∀ i, G i) := fun s =>
    { carrier := {x | ∀ i, i ∉ s → x i = 1}
      mul_mem' := fun {x y} hx hy i hi => by simp [hx i hi, hy i hi]
      one_mem' := fun i _ => rfl
      inv_mem' := fun {x} hx i hi => by simp [hx i hi] }
  have key : ∀ s, BoundedSections k (P s) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have : Subsingleton (P ∅) := ⟨fun x y => Subtype.ext (funext fun i => by
        rw [x.2 i (Finset.notMem_empty i), y.2 i (Finset.notMem_empty i)])⟩
      exact boundedSections_of_subsingleton k
    | insert a s ha ih =>
      let f : P (insert a s) →* G a := (Pi.evalMonoidHom G a).comp (P (insert a s)).subtype
      refine BoundedSections.of_ker f ?_ (h a)
      refine ih.of_injective
        { toFun := fun x => ⟨((x : P (insert a s)) : ∀ i, G i), fun i hi => ?_⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl } ?_
      · by_cases hia : i = a
        · subst hia
          exact x.2
        · exact (x : P (insert a s)).2 i (by simp [hia, hi])
      · intro x y hxy
        have := congrArg (fun z : P s => (z : ∀ i, G i)) hxy
        exact Subtype.ext (Subtype.ext this)
  refine (key Finset.univ).of_injective
    { toFun := fun x => ⟨x, fun i hi => absurd (Finset.mem_univ i) hi⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl } ?_
  intro x y hxy
  exact congrArg (fun z : P Finset.univ => (z : ∀ i, G i)) hxy

/-- A finite group has sections of order at most its own. -/
theorem boundedSections_card [Finite G] : BoundedSections (Nat.card G) G := by
  intro H M _ _
  calc Nat.card (H ⧸ M) ≤ Nat.card H := Nat.card_le_card_of_surjective _
        (QuotientGroup.mk'_surjective M)
    _ ≤ Nat.card G := Subgroup.card_le_card_group H

/-- **A finite `p`-group has simple sections of order `p`**: a simple `p`-group is its own
centre, so it is commutative, and the subgroup generated by an element of order `p` is
normal. -/
theorem boundedSections_of_isPGroup {p : ℕ} [Fact p.Prime] [Finite G] (h : IsPGroup p G) :
    BoundedSections p G := by
  intro H M _ hs
  have hS : IsPGroup p (H ⧸ M) := (h.to_subgroup H).to_quotient M
  have hc : Subgroup.center (H ⧸ M) = ⊤ := by
    have := hS.center_nontrivial
    refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal _).resolve_left ?_
    exact (Subgroup.nontrivial_iff_ne_bot _).1 this
  have hcomm : ∀ a b : H ⧸ M, a * b = b * a := fun a b =>
    (Subgroup.mem_center_iff.1 (hc ▸ Subgroup.mem_top a) b).symm
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hS
  have hm0 : m ≠ 0 := by
    rintro rfl
    have := Finite.one_lt_card_iff_nontrivial.2 (inferInstance : Nontrivial (H ⧸ M))
    rw [hm, pow_zero] at this
    omega
  have hdvd : p ∣ Nat.card (H ⧸ M) := hm ▸ dvd_pow_self p hm0
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hn : (Subgroup.zpowers x).Normal :=
    ⟨fun n hn g => by rw [hcomm g n, mul_inv_cancel_right]; exact hn⟩
  have hb : Subgroup.zpowers x ≠ ⊥ := by
    intro hb
    have : x = 1 := by
      rw [← Subgroup.mem_bot, ← hb]
      exact Subgroup.mem_zpowers x
    rw [this, orderOf_one] at hx
    exact (Fact.out : p.Prime).one_lt.ne hx
  have ht := (IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers x)).resolve_left hb
  rw [← Subgroup.card_top (G := H ⧸ M), ← ht, Nat.card_zpowers, hx]

/-- **Primes dividing the order are at most `k`.** -/
theorem BoundedSections.le_of_prime_dvd_card [Finite G] (h : BoundedSections k G) {p : ℕ}
    (hp : p.Prime) (hdvd : p ∣ Nat.card G) : p ≤ k := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  let H := Subgroup.zpowers x
  have hH : Nat.card H = p := by rw [Nat.card_zpowers, hx]
  have : IsSimpleGroup H := isSimpleGroup_of_prime_card hH
  rw [← hH]
  exact h.card_le H (MonoidHom.id H) Function.surjective_id

theorem BoundedSections.card_primeFactors_le [Finite G] (h : BoundedSections k G) :
    (Nat.card G).primeFactors.card ≤ k := by
  have hsub : (Nat.card G).primeFactors ⊆ Finset.Icc 2 k := by
    intro p hp
    obtain ⟨hpp, hdvd, -⟩ := Nat.mem_primeFactors.1 hp
    exact Finset.mem_Icc.2 ⟨hpp.two_le, h.le_of_prime_dvd_card hpp hdvd⟩
  refine (Finset.card_le_card hsub).trans ?_
  simp

theorem factorial_le_two_pow_sq (k : ℕ) : k.factorial ≤ 2 ^ (k ^ 2) :=
  calc k.factorial ≤ k ^ k := Nat.factorial_le_pow k
    _ ≤ (2 ^ k) ^ k := Nat.pow_le_pow_left (Nat.lt_two_pow_self).le k
    _ = 2 ^ (k ^ 2) := by rw [← pow_mul, sq]

end GraphIso.Groups
