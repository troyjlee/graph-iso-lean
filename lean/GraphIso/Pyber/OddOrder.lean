module

public import GraphIso.Pyber.Orbital
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-!
# The odd-order bound

Stage 15b (`PLAN-15.md` §4, item 6): the claim in Pyber's Lemma 2. If `G` is a finite group of
odd order and `H ≤ G` is core-free of index `n`, then
`ω(|G|) ≤ λ(n) (λ(n) + 1) / 2`, where `ω(m) = |m.primeFactors|` and `λ = Nat.log 2`
(`card_primeFactors_le_of_odd`). The concrete form (`card_primeFactors_le_of_odd_action`) is
for a faithful transitive action of degree `n`.

The proof is by strong induction on `n`:
* `H = ⊤`: then `G` is trivial.
* `H` maximal: `G` acts primitively and faithfully on `Ω = G ⧸ H`. Take `y ≠ x` and the
  suborbit `Δ = Δ(x)`, of size `d` with `2 d + 1 ≤ n` (odd order). By Jordan's lemma every prime
  of `|G_x|` divides `|P|`, where `P ≤ Perm Δ` is transitive of degree `d` and odd order. So
  `ω(|G|) ≤ ω(n) + ω(|P|) ≤ λ(n) + λ(d)(λ(d) + 1)/2`, and `λ(d) + 1 ≤ λ(n)`.
* otherwise take `H < M < G` and `K = M.normalCore`. In `G ⧸ K` the image of `M` is core-free
  of index `t = [G : M]`; in `K ⧸ J` (`J` the core of `H ∩ K` in `K`) the image of `H ∩ K` is
  core-free of index `b' = [K : H ∩ K] ≤ b = [M : H]`. Every prime of `|K|` divides
  `|K ⧸ J|`, so `ω(|G|) ≤ ω(|G ⧸ K|) + ω(|K ⧸ J|)`, and `t b = n` with `t, b ≥ 2`.

The arithmetic is in `tri_add_le`, `tri_mono`, `add_tri_le`, `log_add_log_le` and
`log_add_one_le`. As in milestone 12, the groups are in `Type`.
-/

@[expose] public section

namespace GraphIso.Pyber

open Subgroup MulAction

/-! ### Arithmetic -/

theorem two_mul_tri (L : ℕ) : 2 * (L * (L + 1) / 2) = L * (L + 1) :=
  Nat.mul_div_cancel' (Nat.even_mul_succ_self L).two_dvd

/-- `T(a) + T(c) ≤ T(a + c)` for `T(L) = L(L+1)/2`. -/
theorem tri_add_le (a c : ℕ) : a * (a + 1) / 2 + c * (c + 1) / 2 ≤ (a + c) * (a + c + 1) / 2 := by
  have ha := two_mul_tri a
  have hc := two_mul_tri c
  have hac := two_mul_tri (a + c)
  have he : (a + c) * (a + c + 1) = a * (a + 1) + c * (c + 1) + 2 * (a * c) := by ring
  omega

/-- `T` is monotone. -/
theorem tri_mono {a c : ℕ} (h : a ≤ c) : a * (a + 1) / 2 ≤ c * (c + 1) / 2 :=
  Nat.div_le_div_right (Nat.mul_le_mul h (Nat.add_le_add_right h 1))

/-- `L + T(a) ≤ T(L)` when `a + 1 ≤ L`. -/
theorem add_tri_le {a L : ℕ} (h : a + 1 ≤ L) : L + a * (a + 1) / 2 ≤ L * (L + 1) / 2 := by
  obtain ⟨L, rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
  have h1 := tri_mono (show a ≤ L by omega)
  have hL := two_mul_tri L
  have hL1 := two_mul_tri (L + 1)
  have he : (L + 1) * (L + 1 + 1) = L * (L + 1) + 2 * (L + 1) := by ring
  omega

/-- `λ(t) + λ(b) ≤ λ(t b)`. -/
theorem log_add_log_le {t b : ℕ} (ht : t ≠ 0) (hb : b ≠ 0) :
    Nat.log 2 t + Nat.log 2 b ≤ Nat.log 2 (t * b) := by
  apply Nat.le_log_of_pow_le Nat.one_lt_two
  rw [pow_add]
  exact Nat.mul_le_mul (Nat.pow_log_le_self 2 ht) (Nat.pow_log_le_self 2 hb)

/-- `λ(d) + 1 ≤ λ(n)` when `1 ≤ d` and `2 d < n`. -/
theorem log_add_one_le {d n : ℕ} (hd : d ≠ 0) (h : 2 * d < n) :
    Nat.log 2 d + 1 ≤ Nat.log 2 n := by
  apply Nat.le_log_of_pow_le Nat.one_lt_two
  rw [pow_succ]
  have := Nat.pow_log_le_self 2 hd
  omega

/-! ### The induction -/

/-- `ω(a b) ≤ ω(a) + ω(b)`. -/
theorem card_primeFactors_mul_le {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (a * b).primeFactors.card ≤ a.primeFactors.card + b.primeFactors.card := by
  rw [Nat.primeFactors_mul ha hb]
  exact Finset.card_union_le _ _

theorem card_primeFactors_le_of_odd_aux (n : ℕ) :
    ∀ (G : Type) [Group G] [Finite G] (H : Subgroup G), H.normalCore = ⊥ → H.index = n →
      Odd (Nat.card G) →
      (Nat.card G).primeFactors.card ≤ Nat.log 2 n * (Nat.log 2 n + 1) / 2 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G _ _ H hc hn hodd
  by_cases htop : H = ⊤
  · -- `G` is trivial
    subst htop
    rw [normalCore_eq_self] at hc
    have h1 : Nat.card G = 1 := by
      rw [← card_top (G := G), hc, card_bot]
    rw [h1, Nat.primeFactors_one, Finset.card_empty]
    exact Nat.zero_le _
  by_cases hmax : IsCoatom H
  · -- the primitive case
    have := nontrivial_quotient htop
    have := isPreprimitive_quotient hmax
    set x : G ⧸ H := ((1 : G) : G ⧸ H)
    obtain ⟨y, hy⟩ := exists_ne x
    have hxy : x ≠ y := hy.symm
    set Δ := orbit (stabilizer G x) y
    set P := (toPermHom (stabilizer G x) Δ).range
    have hfaith := faithful_quotient hc
    have hidx : (stabilizer G x).index = n := by
      rw [index_stabilizer_of_transitive, ← hn]
      rfl
    have hcard : Nat.card G = n * Nat.card (stabilizer G x) := by
      rw [← card_mul_index (stabilizer G x), hidx, mul_comm]
    have hn0 : n ≠ 0 := by
      rw [← hn]
      exact index_ne_zero_of_finite
    -- the subgroup `P` of `Perm Δ`
    have : IsPretransitive P Δ := isPretransitive_range
    set y' : Δ := ⟨y, mem_orbit_self y⟩
    have hPc := normalCore_stabilizer_eq_bot (faithful_perm P) y'
    have hPi : (stabilizer P y').index = Nat.card Δ := index_stabilizer_of_transitive P y'
    have hPodd : Odd (Nat.card P) :=
      hodd.of_dvd_nat ((card_range_dvd _).trans (card_subgroup_dvd_card _))
    have hd : 2 * Nat.card Δ + 1 ≤ n := by
      rw [Nat.card_coe_set_eq, ← hn]
      exact two_mul_ncard_suborbit_add_one_le hodd hxy
    have : Nonempty Δ := ⟨y'⟩
    have hd0 : Nat.card Δ ≠ 0 := Nat.card_pos.ne'
    have hP := ih _ (by omega) P (stabilizer P y') hPc hPi hPodd
    -- Jordan's lemma
    have hsub : (Nat.card G).primeFactors ⊆ n.primeFactors ∪ (Nat.card P).primeFactors := by
      intro p hp
      rw [Nat.mem_primeFactors, hcard] at hp
      obtain ⟨hpp, hdvd, -⟩ := hp
      rw [Finset.mem_union, Nat.mem_primeFactors, Nat.mem_primeFactors]
      rcases (Nat.Prime.dvd_mul hpp).mp hdvd with h | h
      · exact Or.inl ⟨hpp, h, hn0⟩
      · exact Or.inr ⟨hpp, prime_dvd_card_range hfaith hxy hpp h, Nat.card_pos.ne'⟩
    calc (Nat.card G).primeFactors.card
        ≤ n.primeFactors.card + (Nat.card P).primeFactors.card :=
          (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      _ ≤ Nat.log 2 n + Nat.log 2 (Nat.card Δ) * (Nat.log 2 (Nat.card Δ) + 1) / 2 :=
          Nat.add_le_add (card_primeFactors_le_log n) hP
      _ ≤ Nat.log 2 n * (Nat.log 2 n + 1) / 2 := add_tri_le (log_add_one_le hd0 (by omega))
  · -- the imprimitive case
    obtain ⟨M, hHM, hM⟩ : ∃ M, H < M ∧ M ≠ ⊤ := by
      by_contra hall
      push Not at hall
      exact hmax ⟨htop, hall⟩
    set K := M.normalCore
    set t := M.index
    set b := H.relIndex M
    have hbt : b * t = n := by rw [← hn]; exact relIndex_mul_index hHM.le
    have hb2 : 2 ≤ b := by
      have h0 : b ≠ 0 := relIndex_ne_zero_of_finite H M
      have h1 : b ≠ 1 := fun h => hHM.not_ge (relIndex_eq_one.mp h)
      omega
    have ht2 : 2 ≤ t := by
      have h0 : t ≠ 0 := index_ne_zero_of_finite
      have h1 : t ≠ 1 := fun h => hM (index_eq_one.mp h)
      omega
    -- the quotient by the core of `M`
    have hQ1 := ih t (by nlinarith) (G ⧸ K) (M.map (QuotientGroup.mk' K)) (normalCore_map_mk M)
      (index_map_mk M) (hodd.of_dvd_nat (card_quotient_dvd_card K))
    -- the normal subgroup `K`
    set L := H.subgroupOf K
    have hb' : L.index ≤ b := relIndex_le_of_le_right M.normalCore_le
      (relIndex_ne_zero_of_finite H M)
    have hQ2 := ih L.index (by nlinarith) (K ⧸ L.normalCore) (L.map (QuotientGroup.mk' _))
      (normalCore_map_mk L) (index_map_mk L)
      (hodd.of_dvd_nat ((card_quotient_dvd_card _).trans (card_subgroup_dvd_card K)))
    have hK : (Nat.card K).primeFactors.card ≤ (Nat.card (K ⧸ L.normalCore)).primeFactors.card :=
      Finset.card_le_card (primeFactors_card_subset hc)
    calc (Nat.card G).primeFactors.card
        ≤ (Nat.card (G ⧸ K)).primeFactors.card + (Nat.card K).primeFactors.card := by
          rw [card_eq_card_quotient_mul_card_subgroup K]
          exact card_primeFactors_mul_le Nat.card_pos.ne' Nat.card_pos.ne'
      _ ≤ Nat.log 2 t * (Nat.log 2 t + 1) / 2 + Nat.log 2 b * (Nat.log 2 b + 1) / 2 :=
          Nat.add_le_add hQ1 (hK.trans (hQ2.trans (tri_mono (Nat.log_mono_right hb'))))
      _ ≤ (Nat.log 2 t + Nat.log 2 b) * (Nat.log 2 t + Nat.log 2 b + 1) / 2 := tri_add_le _ _
      _ ≤ Nat.log 2 n * (Nat.log 2 n + 1) / 2 := by
          apply tri_mono
          rw [← hbt, mul_comm b t]
          exact log_add_log_le (by omega) (by omega)

/-- **The odd-order bound** (the claim in Pyber's Lemma 2). If `G : Type` is finite of odd order
and `H` is core-free, then `ω(|G|) ≤ λ(n) (λ(n) + 1) / 2` with `n = [G : H]`. -/
theorem card_primeFactors_le_of_odd {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hc : H.normalCore = ⊥) (hodd : Odd (Nat.card G)) :
    (Nat.card G).primeFactors.card ≤ Nat.log 2 H.index * (Nat.log 2 H.index + 1) / 2 :=
  card_primeFactors_le_of_odd_aux _ G H hc rfl hodd

/-- **The odd-order bound, concretely:** for a faithful transitive action of a finite group of
odd order on `Ω`, `ω(|G|) ≤ λ(|Ω|) (λ(|Ω|) + 1) / 2`. -/
theorem card_primeFactors_le_of_odd_action {G Ω : Type} [Group G] [Finite G] [MulAction G Ω]
    [IsPretransitive G Ω] (hf : Faithful G Ω) (hodd : Odd (Nat.card G)) :
    (Nat.card G).primeFactors.card ≤ Nat.log 2 (Nat.card Ω) * (Nat.log 2 (Nat.card Ω) + 1) / 2 := by
  rcases isEmpty_or_nonempty Ω with hΩ | ⟨⟨x⟩⟩
  · have : Subsingleton G := ⟨fun a b => by
      rw [hf a fun c => isEmptyElim c, hf b fun c => isEmptyElim c]⟩
    rw [Nat.card_unique, Nat.primeFactors_one, Finset.card_empty]
    exact Nat.zero_le _
  · have h := card_primeFactors_le_of_odd (normalCore_stabilizer_eq_bot hf x) hodd
    rwa [index_stabilizer_of_transitive] at h

end GraphIso.Pyber
