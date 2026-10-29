module

public import GraphIso.Pyber.OddOrder
public import GraphIso.Pyber.Wielandt
public import GraphIso.Pyber.MinNormal
public import GraphIso.Pyber.Imprimitive

/-!
# Pyber's Theorem 7: point stabilizers have few abelian composition factors

Stage 15c. For a finite group `G : Type` and a core-free `H ≤ G` of index `n`,
`|compA H| ≤ 2 λ(n)² + 1` (`ncard_compA_le_of_coreFree`). For a transitive group `G` of degree `n`,
`|compA G_x| ≤ 2 λ(n)² + 1` and `|compA G| ≤ 2 λ(n)² + λ(n) + 1`.

By strong induction on `n`, with `F(m) = 2 λ(m)² + 1`:
* `H = ⊤`: `G` is trivial.
* `H` maximal, `|G|` odd: `|compA H| ≤ ω(|G|) ≤ λ(n)(λ(n)+1)/2` (stage 15b).
* `H` maximal, `|G|` even: an involution gives a self-paired orbital of `(x, y)` on `G ⧸ H`, with
  `x` the base coset. Wielandt's corollary gives `compA H ⊆ compA P ∪ compA P_y`, with `P` the
  image of `G_x` on the suborbit `Δ`, `d = |Δ| < n`, and `P_y` core-free in `P` of index `d`:
  - `P` primitive, abelian minimal normal subgroup: `|P| ≤ d^(λ(d)+1)`, so
    `|compA H| ≤ ω(|P|) ≤ λ(d)² + 2 λ(d)`;
  - `P` primitive, nonabelian minimal normal subgroup: `compA P ⊆ compA P_y`, and the induction
    at `d` applies;
  - `P` imprimitive: Lemma 8 for `P_y` in `P`, and Proposition 3 for `P_y ≤ P`.
* `H` neither `⊤` nor maximal: Lemma 8.
-/

@[expose] public section

namespace GraphIso.Pyber

open Subgroup MulAction

/-! ### Arithmetic -/

/-- `T(L) ≤ 2 L² + 1`. -/
theorem tri_le_F (L : ℕ) : L * (L + 1) / 2 ≤ 2 * L ^ 2 + 1 := by
  have := two_mul_tri L
  nlinarith

/-- `F` is monotone in `λ`. -/
theorem F_mono {a c : ℕ} (h : a ≤ c) : 2 * a ^ 2 + 1 ≤ 2 * c ^ 2 + 1 := by
  have := Nat.pow_le_pow_left h 2
  omega

/-- The imprimitive step: `F(a) + F(c) + c ≤ F(L)` when `1 ≤ a`, `1 ≤ c`, `a + c ≤ L`. -/
theorem F_add_le {a c L : ℕ} (ha : 1 ≤ a) (hc : 1 ≤ c) (h : a + c ≤ L) :
    (2 * a ^ 2 + 1) + (2 * c ^ 2 + 1) + c ≤ 2 * L ^ 2 + 1 := by
  have h1 : (a + c) ^ 2 ≤ L ^ 2 := Nat.pow_le_pow_left h 2
  nlinarith

/-- The primitive step with an imprimitive `P`: `F(a) + F(c) + c + s ≤ F(L)` when `1 ≤ a`,
`1 ≤ c`, `a + c ≤ s ≤ L`. -/
theorem F_add_add_le {a c s L : ℕ} (ha : 1 ≤ a) (hc : 1 ≤ c) (hs : a + c ≤ s) (h : s ≤ L) :
    (2 * a ^ 2 + 1) + (2 * c ^ 2 + 1) + c + s ≤ 2 * L ^ 2 + 1 := by
  have h1 : s ^ 2 ≤ L ^ 2 := Nat.pow_le_pow_left h 2
  have h2 : (a + c) * (a + c) ≤ s * s := Nat.mul_le_mul hs hs
  nlinarith

/-- `λ(m^k) + 1 ≤ k (λ(m) + 1)` for `k ≥ 1`. -/
theorem log_pow_lt (m k : ℕ) (hk : k ≠ 0) : Nat.log 2 (m ^ k) + 1 ≤ k * (Nat.log 2 m + 1) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [zero_pow hk, Nat.log_zero_right]
    omega
  · apply Nat.succ_le_of_lt
    apply Nat.log_lt_of_lt_pow (pow_ne_zero _ hm.ne')
    rw [pow_mul']
    exact Nat.pow_lt_pow_left (Nat.lt_pow_succ_log_self Nat.one_lt_two m) hk

/-- The primitive step with an abelian minimal normal subgroup:
`λ(d^(λ(d)+1)) ≤ F(L)` when `λ(d) ≤ L`. -/
theorem log_pow_le_F {d L : ℕ} (h : Nat.log 2 d ≤ L) :
    Nat.log 2 (d ^ (Nat.log 2 d + 1)) ≤ 2 * L ^ 2 + 1 := by
  have h1 := log_pow_lt d (Nat.log 2 d + 1) (Nat.succ_ne_zero _)
  have h2 : Nat.log 2 d * Nat.log 2 d ≤ L * L := Nat.mul_le_mul h h
  nlinarith

/-! ### The induction -/

/-- `|Δ(x)| < |Ω|`: a suborbit misses `x`. -/
theorem ncard_suborbit_lt {G' Ω' : Type*} [Group G'] [MulAction G' Ω'] [Finite Ω'] {x y : Ω'}
    (hxy : x ≠ y) : Nat.card (orbit (stabilizer G' x) y) < Nat.card Ω' := by
  have hsub : orbit (stabilizer G' x) y ⊆ ({x} : Set Ω')ᶜ := by
    rintro b hb rfl
    exact diag_notMem_orbit hxy (mem_orbit_stabilizer_iff.mp hb)
  have h1 := Set.ncard_le_ncard hsub
  have h2 := Set.ncard_add_ncard_compl ({x} : Set Ω')
  rw [Set.ncard_singleton] at h2
  rw [Nat.card_coe_set_eq]
  omega

theorem ncard_compA_le_of_coreFree_aux (n : ℕ) :
    ∀ (G : Type) [Group G] [Finite G] (H : Subgroup G), H.normalCore = ⊥ → H.index = n →
      (compA H).ncard ≤ 2 * Nat.log 2 n ^ 2 + 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G _ _ H hc hn
  by_cases htop : H = ⊤
  · -- `G` is trivial
    subst htop
    rw [normalCore_eq_self] at hc
    rw [compA_eq_of_mulEquiv (MulEquiv.subgroupCongr hc),
      compA_eq_empty_of_subsingleton (G := ↥(⊥ : Subgroup G)), Set.ncard_empty]
    exact Nat.zero_le _
  by_cases hmax : IsCoatom H
  swap
  · -- Lemma 8
    obtain ⟨t, b, ht, hb, htb, hle⟩ :=
      exists_ncard_compA_le (fun m => 2 * Nat.log 2 m ^ 2 + 1) ih hc hn htop hmax
    have ha : 1 ≤ Nat.log 2 t := Nat.le_log_of_pow_le Nat.one_lt_two (by omega)
    have hb' : 1 ≤ Nat.log 2 b := Nat.le_log_of_pow_le Nat.one_lt_two (by omega)
    have hs : Nat.log 2 t + Nat.log 2 b ≤ Nat.log 2 n := htb ▸ log_add_log_le (by omega) (by omega)
    exact hle.trans (F_add_le ha hb' hs)
  by_cases hodd : Odd (Nat.card G)
  · -- odd order
    have h1 := card_primeFactors_le_of_odd hc hodd
    rw [hn] at h1
    have h2 : (compA H).ncard ≤ (Nat.card G).primeFactors.card :=
      ncard_compA_le_card_primeFactors.trans
        (Finset.card_le_card (Nat.primeFactors_mono (card_subgroup_dvd_card H) Nat.card_pos.ne'))
    exact h2.trans (h1.trans (tri_le_F _))
  -- even order: an involution gives a self-paired orbital
  have h2 : 2 ∣ Nat.card G := (Nat.not_odd_iff_even.mp hodd).two_dvd
  have := Fact.mk Nat.prime_two
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hgg : g * g = 1 := by rw [← sq, ← hg, pow_orderOf_eq_one]
  have hg1 : g ≠ 1 := fun h => by rw [h, orderOf_one] at hg; omega
  have hfaith := faithful_quotient hc
  obtain ⟨x', hx'⟩ : ∃ x' : G ⧸ H, g • x' ≠ x' := by
    by_contra hall
    push Not at hall
    exact hg1 (hfaith g hall)
  have := isPreprimitive_quotient hmax
  set x : G ⧸ H := ((1 : G) : G ⧸ H)
  obtain ⟨k, hk⟩ := exists_smul_eq G x' x
  set y := k • g • x'
  have hxy : x ≠ y := by
    intro h
    rw [← hk] at h
    exact hx' (smul_left_cancel k h).symm
  have hsp : (y, x) ∈ orbit G (x, y) := by
    have h1 := smul_mem_orbit_pair (swap_mem_orbit_of_mul_self hgg x') k
    rw [hk] at h1
    have h3 : orbit G (x, y) = orbit G (x', g • x') :=
      orbit_eq_iff.mpr ⟨k, by show k • (x', g • x') = (x, y); rw [Prod.smul_mk, hk]⟩
    rw [h3]
    exact h1
  -- Wielandt's corollary
  have hW := compA_stabilizer_subset hfaith hxy hsp
  rw [compA_eq_of_mulEquiv (MulEquiv.subgroupCongr (stabilizer_quotient H).symm)]
  change (compA (stabilizer G x)).ncard ≤ _
  set Δ := orbit (stabilizer G x) y
  set P := (toPermHom (stabilizer G x) Δ).range
  set y' : Δ := ⟨y, mem_orbit_self y⟩
  have : IsPretransitive P Δ := isPretransitive_range
  have hPc := normalCore_stabilizer_eq_bot (faithful_perm P) y'
  have hPi : (stabilizer P y').index = Nat.card Δ := index_stabilizer_of_transitive P y'
  have hdn : Nat.card Δ < n := by
    rw [← hn]
    exact ncard_suborbit_lt hxy
  have hL : Nat.log 2 (Nat.card Δ) ≤ Nat.log 2 n := Nat.log_mono_right hdn.le
  have hPy := ih _ hdn P (stabilizer P y') hPc hPi
  rcases subsingleton_or_nontrivial P with hP | hP
  · -- `P` is trivial
    rw [compA_eq_empty_of_subsingleton (G := P),
      compA_eq_empty_of_subsingleton (G := stabilizer P y'), Set.empty_union] at hW
    rw [Set.subset_empty_iff.mp hW, Set.ncard_empty]
    exact Nat.zero_le _
  by_cases hprim : IsPreprimitive P Δ
  · rcases card_le_or_compA_subset (faithful_perm P) y' with hcard | hsub
    · -- an abelian minimal normal subgroup
      have hs : compA P ∪ compA (stabilizer P y') ⊆ ↑(Nat.card P).primeFactors := by
        refine Set.union_subset compA_subset_primeFactors (compA_subset_primeFactors.trans ?_)
        exact_mod_cast Nat.primeFactors_mono (card_subgroup_dvd_card _) Nat.card_pos.ne'
      calc (compA (stabilizer G x)).ncard ≤ (Nat.card P).primeFactors.card :=
            (Set.ncard_le_ncard (hW.trans hs) (Finset.finite_toSet _)).trans
              (Set.ncard_coe_finset _).le
        _ ≤ Nat.log 2 (Nat.card P) := card_primeFactors_le_log _
        _ ≤ Nat.log 2 (Nat.card Δ ^ (Nat.log 2 (Nat.card Δ) + 1)) := Nat.log_mono_right hcard
        _ ≤ 2 * Nat.log 2 n ^ 2 + 1 := log_pow_le_F hL
    · -- a nonabelian minimal normal subgroup
      have h1 : compA (stabilizer G x) ⊆ compA (stabilizer P y') :=
        hW.trans (Set.union_subset hsub subset_rfl)
      exact (Set.ncard_le_ncard h1 compA_finite).trans (hPy.trans (F_mono hL))
  · -- `P` imprimitive
    have hΔ : Nontrivial Δ := by
      by_contra hnt
      rw [not_nontrivial_iff_subsingleton] at hnt
      exact hprim IsPreprimitive.of_subsingleton
    have hmaxP : ¬IsCoatom (stabilizer P y') := by
      rw [isCoatom_stabilizer_iff_preprimitive]
      exact hprim
    have htopP : stabilizer P y' ≠ ⊤ := by
      intro h
      obtain ⟨b, hb⟩ := exists_ne y'
      obtain ⟨σ, hσ⟩ := exists_smul_eq P y' b
      have hσ' : σ • y' = y' := (h ▸ mem_top σ : σ ∈ stabilizer P y')
      exact hb (hσ.symm.trans hσ')
    obtain ⟨t, b, ht, hb, htb, hle⟩ := exists_ncard_compA_le (fun m => 2 * Nat.log 2 m ^ 2 + 1)
      (fun m hm => ih m (hm.trans hdn)) hPc hPi htopP hmaxP
    -- Proposition 3 for `P_y ≤ P`
    have h3 := compA_sdiff_subset (stabilizer P y')
    rw [hPi] at h3
    have hs : compA P ∪ compA (stabilizer P y') ⊆
        compA (stabilizer P y') ∪ ↑(Nat.card Δ).primeFactors := by
      refine Set.union_subset (fun p hp => ?_) Set.subset_union_left
      by_cases hpy : p ∈ compA (stabilizer P y')
      · exact Or.inl hpy
      · exact Or.inr (h3 ⟨hp, hpy⟩)
    have h4 := (Set.ncard_le_ncard (hW.trans hs) (compA_finite.union (Finset.finite_toSet _))).trans
      (Set.ncard_union_le _ _)
    rw [Set.ncard_coe_finset] at h4
    have h5 := card_primeFactors_le_log (Nat.card Δ)
    have ha : 1 ≤ Nat.log 2 t := Nat.le_log_of_pow_le Nat.one_lt_two (by omega)
    have hb' : 1 ≤ Nat.log 2 b := Nat.le_log_of_pow_le Nat.one_lt_two (by omega)
    have hs' : Nat.log 2 t + Nat.log 2 b ≤ Nat.log 2 (Nat.card Δ) :=
      htb ▸ log_add_log_le (by omega) (by omega)
    have h6 := F_add_add_le ha hb' hs' hL
    omega

/-- **Pyber's Theorem 7**, abstract form: for a finite group `G : Type` and a core-free subgroup
`H` of index `n`, `|compA H| ≤ 2 λ(n)² + 1`. -/
theorem ncard_compA_le_of_coreFree {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hc : H.normalCore = ⊥) :
    (compA H).ncard ≤ 2 * Nat.log 2 H.index ^ 2 + 1 :=
  ncard_compA_le_of_coreFree_aux _ G H hc rfl

/-- **Theorem 7, concretely:** for a faithful transitive action of a finite group of degree `n`,
a point stabilizer has `|compA G_x| ≤ 2 λ(n)² + 1`. -/
theorem ncard_compA_stabilizer_le {G Ω : Type} [Group G] [Finite G] [MulAction G Ω]
    [IsPretransitive G Ω] (hf : Faithful G Ω) (x : Ω) :
    (compA (stabilizer G x)).ncard ≤ 2 * Nat.log 2 (Nat.card Ω) ^ 2 + 1 := by
  have h := ncard_compA_le_of_coreFree (normalCore_stabilizer_eq_bot hf x)
  rwa [index_stabilizer_of_transitive] at h

/-- **The corollary for transitive groups:** for a faithful transitive action of a finite group
of degree `n ≥ 1`, `|compA G| ≤ 2 λ(n)² + λ(n) + 1` (Proposition 3 for `G_x ≤ G`). -/
theorem ncard_compA_le_of_transitive {G Ω : Type} [Group G] [Finite G] [MulAction G Ω]
    [IsPretransitive G Ω] [Nonempty Ω] (hf : Faithful G Ω) :
    (compA G).ncard ≤ 2 * Nat.log 2 (Nat.card Ω) ^ 2 + Nat.log 2 (Nat.card Ω) + 1 := by
  obtain ⟨x⟩ := ‹Nonempty Ω›
  have h1 := compA_sdiff_subset (stabilizer G x)
  rw [index_stabilizer_of_transitive] at h1
  have hs : compA G ⊆ compA (stabilizer G x) ∪ ↑(Nat.card Ω).primeFactors := by
    intro p hp
    by_cases hpx : p ∈ compA (stabilizer G x)
    · exact Or.inl hpx
    · exact Or.inr (h1 ⟨hp, hpx⟩)
  have h2 := (Set.ncard_le_ncard hs (compA_finite.union (Finset.finite_toSet _))).trans
    (Set.ncard_union_le _ _)
  rw [Set.ncard_coe_finset] at h2
  have h3 := ncard_compA_stabilizer_le hf x
  have h4 := card_primeFactors_le_log (Nat.card Ω)
  omega

end GraphIso.Pyber
