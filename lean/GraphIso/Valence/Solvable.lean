module

public import GraphIso.Graph.Perms
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Layer groups of graphs of maximum degree at most five

For a layered graph of maximum degree `Δ ≤ 5` rooted at two edges (`LayeredD Δ`, `Roots4`),
every layer group `A_r` is **solvable**, and **its order has at most the two prime divisors
`2` and `3`**. Both facts are proved from the construction; Burnside's `pᵃqᵇ` theorem is not
used.

* `resHom r : A_{r+1} →* A_r`: restriction to level `≤ r` (`resPerm`). Its kernel consists of
  the elements fixing level `≤ r` pointwise.
* `twinHom r`: the kernel embeds (`twinHom_injective`) in the product over the points `x` of
  the permutations of the twins of `x` (`Tw r x`: `x` itself, or a point of level `r + 1` with
  the same neighbourhood). A point of level `r + 1` has at most `Δ − 1 ≤ 4` twins
  (`card_tw_le_pred`, `card_tw_le`), so every factor is solvable (`Equiv.Perm.isSolvable`)
  and every element of the kernel satisfies `k¹² = 1` (`ker_pow_twelve`).
* `isSolvable_autR`: by induction on `r`; `A₀` is a `2`-group. A finite product of solvable
  groups is solvable (`isSolvable_pi`).
* `exists_pow_eq_one`: every element of `A_r` has order dividing `2^i 3^j`.
  By Cauchy's theorem, the prime divisors of `|A_r|` are among `2` and `3`
  (`card_primeFactors_autR_le`).
-/

@[expose] public section

namespace GraphIso.Graph.Valence

open Equiv Sims

/-! ### Groups -/

/-- **A finite product of solvable groups is solvable.** -/
theorem isSolvable_pi {ι : Type*} [Finite ι] {H : ι → Type*} [∀ i, Group (H i)]
    (h : ∀ i, Group.IsSolvable (H i)) : Group.IsSolvable (∀ i, H i) := by
  classical
  cases nonempty_fintype ι
  choose n hn using fun i => (h i).solvable
  refine ⟨⟨Finset.univ.sup n, eq_bot_iff.2 fun x hx => ?_⟩⟩
  rw [Subgroup.mem_bot]
  funext i
  have h₁ : Pi.evalMonoidHom H i x ∈ derivedSeries (H i) (Finset.univ.sup n) :=
    map_derivedSeries_le_derivedSeries (Pi.evalMonoidHom H i) _ (Subgroup.mem_map_of_mem _ hx)
  have h₂ := derivedSeries_antitone (G := H i) (Finset.le_sup (Finset.mem_univ i)) h₁
  rw [hn i, Subgroup.mem_bot] at h₂
  exact h₂

/-- **A permutation of at most four points satisfies `σ¹² = 1`.** -/
theorem pow_twelve_eq_one {α : Type*} [Fintype α] [DecidableEq α] (h : Fintype.card α ≤ 4)
    (σ : Perm α) : σ ^ 12 = 1 := by
  refine orderOf_dvd_iff_pow_eq_one.1 ?_
  rw [← Perm.lcm_cycleType]
  refine Multiset.lcm_dvd.2 fun k hk => ?_
  have h₂ := Perm.two_le_of_mem_cycleType hk
  have h₄ := (Perm.le_card_support_of_mem_cycleType hk).trans
    ((Finset.card_le_univ σ.support).trans h)
  interval_cases k <;> decide

/-! ### Restriction -/

section Res

variable {Δ N : ℕ} {G : GraphData} {roots : List ℕ} {lev : Array ℕ}
  (hZ : LayeredD Δ N G roots lev)

/-- **Restriction** from `A_{r+1}` to `A_r`. -/
def resHom (r : ℕ) : AutR N G lev (r + 1) →* AutR N G lev r where
  toFun g := ⟨resPerm g.2, (resPerm_mem hZ g.2).1⟩
  map_one' := Subtype.ext (perm_eq_of_act fun v _ => by
    rw [act_resPerm]
    simp [resFun])
  map_mul' g h := Subtype.ext (perm_eq_of_act fun v hv => by
    simp only [Subgroup.coe_mul]
    rw [act_mul, act_resPerm, act_resPerm, act_resPerm]
    unfold resFun
    by_cases hl : get lev v ≤ r
    · have : get lev (act (h : Perm (Fin N)) v) ≤ r := by rw [h.2.2.1 v hv]; exact hl
      simp only [hl, this, ↓reduceIte, act_mul]
    · simp only [hl, ↓reduceIte])

theorem act_resHom {r : ℕ} (g : AutR N G lev (r + 1)) {v : ℕ} (hv : get lev v ≤ r) :
    act ((resHom hZ r g : AutR N G lev r) : Perm (Fin N)) v = act (g : Perm (Fin N)) v := by
  show act (resPerm g.2) v = _
  rw [act_resPerm]
  simp [resFun, hv]

/-- The kernel of the restriction: the elements fixing level `≤ r` pointwise. -/
theorem fix_of_mem_ker {r : ℕ} {k : AutR N G lev (r + 1)} (hk : k ∈ (resHom hZ r).ker) :
    ∀ v < N, get lev v ≤ r → act (k : Perm (Fin N)) v = v := by
  intro v _ hv
  have := act_resHom hZ k hv
  rw [MonoidHom.mem_ker.1 hk] at this
  rw [← this]
  exact act_one v

/-- An element of the kernel fixes every point not of level `r + 1`. -/
theorem fix_of_mem_ker' {r : ℕ} {k : AutR N G lev (r + 1)} (hk : k ∈ (resHom hZ r).ker) {v : ℕ}
    (hv : v < N) (hl : get lev v ≠ r + 1) : act (k : Perm (Fin N)) v = v := by
  rcases Nat.lt_or_ge (r + 1) (get lev v) with h | h
  · exact k.2.1 v hv h
  · exact fix_of_mem_ker hZ hk v hv (by omega)

/-! ### Twins -/

variable (G lev) in
/-- The twins of `x` in level `r + 1`: `x` itself, or a point of level `r + 1` with the same
neighbourhood. -/
def Tw (r : ℕ) (x y : Fin N) : Prop :=
  x = y ∨ (get lev x = r + 1 ∧ get lev y = r + 1 ∧ nb G lev r x = nb G lev r y)

theorem tw_iff {r : ℕ} {k : AutR N G lev (r + 1)} (hk : k ∈ (resHom hZ r).ker) (x y : Fin N) :
    Tw G lev r x ((k : Perm (Fin N)) y) ↔ Tw G lev r x y := by
  have hky : act (k : Perm (Fin N)) y.val = ((k : Perm (Fin N)) y).val := act_of_lt _ y.2
  have hfix := fix_of_mem_ker hZ hk
  by_cases hy : get lev y = r + 1
  · have hl : get lev ((k : Perm (Fin N)) y) = r + 1 := by rw [← hky, k.2.2.1 y y.2, hy]
    have hn : nb G lev r ((k : Perm (Fin N)) y) = nb G lev r y := by
      rw [← hky]
      exact nb_act_of_fix hZ k.2 hfix y.2 hy
    unfold Tw
    rw [hl, hn]
    constructor
    · rintro (e | h)
      · right
        refine ⟨by rw [e]; exact hl, hy, by rw [e, hn]⟩
      · exact Or.inr ⟨h.1, hy, h.2.2⟩
    · rintro (rfl | h)
      · exact Or.inr ⟨hy, rfl, rfl⟩
      · exact Or.inr ⟨h.1, rfl, h.2.2⟩
  · have e : (k : Perm (Fin N)) y = y :=
      Fin.ext (by rw [← hky]; exact fix_of_mem_ker' hZ hk y.2 hy)
    rw [e]

include hZ in
/-- **A point has at most `Δ − 1` twins**, itself included. -/
theorem card_tw_le_pred {r : ℕ} (x : Fin N) [Fintype {y : Fin N // Tw G lev r x y}] :
    Fintype.card {y : Fin N // Tw G lev r x y} ≤ Δ - 1 := by
  classical
  rw [Fintype.card_subtype]
  by_cases hx : get lev x = r + 1
  · have hT := (subL_nb hZ x.2 hx).1
    have hc := cnt_le hZ (r := r) hT
    refine (Finset.card_le_card_of_injOn (fun y : Fin N => y.val)
      (t := (cls G lev N r (nb G lev r x)).toFinset) ?_ ?_).trans ?_
    · intro y hy
      have hy' : Tw G lev r x y := by simpa using hy
      simp only [Finset.mem_coe, List.mem_toFinset]
      rcases hy' with rfl | ⟨-, hly, hn⟩
      · exact mem_cls_self x.2 hx
      · exact mem_cls.2 ⟨y.2, hly, hn.symm⟩
    · intro y _ z _ h
      exact Fin.ext h
    · rw [List.toFinset_card_of_nodup (nodup_cls _ _)]
      unfold cnt at hc
      omega
  · have := hZ.two_le
    refine (Finset.card_le_card (t := {x}) fun y hy => ?_).trans (by simp; omega)
    have hy' : Tw G lev r x y := by simpa using hy
    rcases hy' with rfl | ⟨h, -⟩
    · simp
    · exact absurd h hx

variable (hΔ : Δ ≤ 5)
include hΔ

include hZ in
theorem card_tw_le {r : ℕ} (x : Fin N) [Fintype {y : Fin N // Tw G lev r x y}] :
    Fintype.card {y : Fin N // Tw G lev r x y} ≤ 4 :=
  (card_tw_le_pred hZ x).trans (by omega)

omit hΔ in
variable (G lev) in
/-- The kernel of the restriction, on the twins of each point. -/
def twinHom (r : ℕ) : (resHom hZ r).ker →* ∀ x : Fin N, Perm {y : Fin N // Tw G lev r x y} where
  toFun k x := ((k : AutR N G lev (r + 1)) : Perm (Fin N)).subtypePerm (tw_iff hZ k.2 x)
  map_one' := rfl
  map_mul' _ _ := rfl

omit hΔ in
theorem twinHom_injective (r : ℕ) : Function.Injective (twinHom G lev hZ r) := by
  intro k k' h
  refine Subtype.ext (Subtype.ext (Equiv.ext fun x => ?_))
  exact congrArg (fun f => (f x ⟨x, Or.inl rfl⟩ : {y : Fin N // Tw G lev r x y}).val) h

/-- **The kernel of the restriction is solvable.** -/
theorem isSolvable_ker (r : ℕ) : Group.IsSolvable (resHom hZ r).ker := by
  classical
  have : Group.IsSolvable (∀ x : Fin N, Perm {y : Fin N // Tw G lev r x y}) :=
    isSolvable_pi fun x => Perm.isSolvable (by
      rw [Nat.card_eq_fintype_card]
      exact card_tw_le hZ hΔ x)
  exact Group.isSolvable_of_isSolvable_injective (twinHom_injective hZ r)

/-- **Every element of the kernel satisfies `k¹² = 1`.** -/
theorem ker_pow_twelve {r : ℕ} (k : (resHom hZ r).ker) : k ^ 12 = 1 := by
  classical
  apply twinHom_injective hZ r
  rw [map_pow, map_one]
  funext x
  exact pow_twelve_eq_one (card_tw_le hZ hΔ x) _

end Res

/-! ### All layer groups -/

section Layers

variable {Δ N : ℕ} {G : GraphData} {roots : List ℕ} {lev : Array ℕ} {a b c d : ℕ}
  (hZ : LayeredD Δ N G roots lev) (hR : Roots4 N G lev a b c d) (hΔ : Δ ≤ 5)
include hZ hR hΔ

/-- **Every layer group is solvable.** -/
theorem isSolvable_autR : ∀ r, Group.IsSolvable (AutR N G lev r)
  | 0 => by
    have h2 : IsPGroup 2 (AutR N G lev 0) := fun x =>
      ⟨2, Subtype.ext (by rw [Subgroup.coe_pow]; exact autR0_pow_four hR hZ.valid x.2)⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := h2.isNilpotent
    infer_instance
  | r + 1 => by
    have := isSolvable_autR r
    have := isSolvable_ker hZ hΔ r
    exact Group.isSolvable_of_ker_le_range (resHom hZ r).ker.subtype (resHom hZ r)
      (by rw [Subgroup.range_subtype])

/-- **Every element of a layer group has order dividing `2^i 3^j`.** -/
theorem exists_pow_eq_one : ∀ r (g : AutR N G lev r), ∃ i j : ℕ, g ^ (2 ^ i * 3 ^ j) = 1
  | 0, g => ⟨2, 0, Subtype.ext (by
      rw [Subgroup.coe_pow]
      simpa using autR0_pow_four hR hZ.valid g.2)⟩
  | r + 1, g => by
    obtain ⟨i, j, h⟩ := exists_pow_eq_one r (resHom hZ r g)
    have hq : g ^ (2 ^ i * 3 ^ j) ∈ (resHom hZ r).ker := by
      rw [MonoidHom.mem_ker, map_pow, h]
    have h12 := congrArg Subtype.val (ker_pow_twelve hZ hΔ ⟨_, hq⟩)
    simp only [SubmonoidClass.mk_pow, OneMemClass.coe_one] at h12
    refine ⟨i + 2, j + 1, ?_⟩
    rw [← pow_mul] at h12
    rw [← h12]
    congr 1
    ring

/-- **The order of a layer group has at most the two prime divisors `2` and `3`.** -/
theorem card_primeFactors_autR_le (r : ℕ) :
    (Nat.card (AutR N G lev r)).primeFactors.card ≤ 2 := by
  have hsub : (Nat.card (AutR N G lev r)).primeFactors ⊆ {2, 3} := by
    intro p hp
    obtain ⟨hpp, hdvd, -⟩ := Nat.mem_primeFactors.1 hp
    have : Fact p.Prime := ⟨hpp⟩
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hdvd
    obtain ⟨i, j, h⟩ := exists_pow_eq_one hZ hR hΔ r g
    have hdvd' : p ∣ 2 ^ i * 3 ^ j := hg ▸ orderOf_dvd_of_pow_eq_one h
    rcases (Nat.Prime.dvd_mul hpp).1 hdvd' with h₂ | h₃
    · have := (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1 (hpp.dvd_of_dvd_pow h₂)
      simp [this]
    · have := (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_three).1 (hpp.dvd_of_dvd_pow h₃)
      simp [this]
  exact (Finset.card_le_card hsub).trans (by decide)

end Layers

end GraphIso.Graph.Valence
