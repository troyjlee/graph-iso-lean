module

public import GraphIso.Groups.PrimitiveSolvable
public import GraphIso.Groups.BoundedLinear
public import GraphIso.Groups.Subdirect

/-!
# The Babai–Cameron–Pálfy theorem

`card_le_of_isPreprimitive_of_boundedSections`: a primitive subgroup `G` of `Sym(n)`, `n ≥ 2`,
all of whose simple sections have order at most `k`, has order at most
`n^{3 k³ + 3 k² + 12 k + 1}`. Only quasiprimitivity is used
(`card_le_of_isQuasiPreprimitive_of_boundedSections`). Take a minimal normal subgroup `N`.

* **`N` abelian** (`card_le_of_isQuasiPreprimitive_of_abelian`): a point stabilizer is a linear
  group with no normal `p`-subgroup on a space of order `n`, of order at most
  `n^{3 k³ + 3 k² + 12 k}` (`card_le_of_boundedSections_linear`).
* **`N` nonabelian** (`card_le_of_isQuasiPreprimitive_of_nonabelian`): `N` is the product of `j`
  simple factors of order at most `k`, all of the same order (`exists_simple_factors`).
  - `N` is transitive and its centralizer `C` meets a point stabilizer trivially, so `|C| ≤ n`.
  - `|G| ≤ |C| (k! 2^k)^j` (`card_le_of_factors`).
  - The point stabilizer `N_α` contains no factor `T` (`T` is normal in `N`, so it would fix
    every point), so `2^j |N_α|² ≤ |N|² = n² |N_α|²` (`two_pow_mul_card_sq_le`).
  - So `|G| ≤ n (2^j)^{k² + k} ≤ n^{2 k² + 2 k + 1}`, as `k! ≤ 2^{k²}`.
-/

@[expose] public section

namespace GraphIso.Groups

open Equiv MulAction

/-- **Quasiprimitive groups with a nonabelian minimal normal subgroup.** -/
theorem card_le_of_isQuasiPreprimitive_of_nonabelian {n k : ℕ} (G : Subgroup (Perm (Fin n)))
    (hk : BoundedSections k G) (hn : 2 ≤ n) [hq : IsQuasiPreprimitive G (Fin n)]
    {N : Subgroup G} (hN : IsMinNormal ⊤ N) (hna : ∃ x ∈ N, ∃ y ∈ N, x * y ≠ y * x) :
    Nat.card G ≤ n ^ (2 * k ^ 2 + 2 * k + 1) := by
  classical
  have hfaith : ∀ g : G, (∀ x : Fin n, g • x = x) → g = 1 := fun g h =>
    Subtype.ext (Equiv.ext fun x => h x)
  set α : Fin n := ⟨0, by omega⟩
  have hNn : N.Normal := nnormal_top_iff.1 hN.1
  have hNt : IsPretransitive N (Fin n) := isPretransitive_of_ne_bot G N hNn hN.2.1
  obtain ⟨F, hFn, hFs, hFna, hFcomm, hFind, hFN, hcjF, htr⟩ := exists_simple_factors hN hna
  have hFk : ∀ A ∈ F, Nat.card A ≤ k := fun A hA => by
    have := hFs A hA
    exact hk.card_le A (MonoidHom.id A) Function.surjective_id
  -- the centralizer `C` of `N` acts semiregularly, so `|C| ≤ n`
  set C := (⊤ : Subgroup G) ⊓ Subgroup.centralizer (N : Set G)
  have hC : Nat.card C ≤ n := by
    have hinj : Function.Injective (fun c : C => (c : G) • α) := by
      intro c d hcd
      have hcd' : (c : G) • α = (d : G) • α := hcd
      have hfix : ((d : G)⁻¹ * c) • α = α := by
        rw [mul_smul]
        exact inv_smul_eq_iff.2 hcd'
      have hcen : (d : G)⁻¹ * c ∈ Subgroup.centralizer (N : Set G) :=
        (C.mul_mem (C.inv_mem d.2) c.2).2
      have h1 : (d : G)⁻¹ * c = 1 := hfaith _ fun x => by
        obtain ⟨m, rfl⟩ := exists_smul_eq N α x
        change ((d : G)⁻¹ * c) • (m : G) • α = (m : G) • α
        rw [smul_smul, ← Subgroup.mem_centralizer_iff.1 hcen m m.2, ← smul_smul, hfix]
      exact Subtype.ext (inv_mul_eq_one.1 h1).symm
    simpa using Nat.card_le_card_of_injective _ hinj
  -- `N` as a product of its factors
  have hcomm' : Pairwise fun A B : F => ∀ x y : G, x ∈ (A : Subgroup G) →
      y ∈ (B : Subgroup G) → Commute x y := fun A B hAB x y hx hy =>
    hFcomm A A.2 B B.2 (fun h => hAB (Subtype.ext h)) x hx y hy
  let φ := Subgroup.noncommPiCoprod hcomm'
  have hinj : Function.Injective φ := Subgroup.injective_noncommPiCoprod_of_iSupIndep hFind
  have hrange : φ.range = N := by rw [Subgroup.noncommPiCoprod_range, hFN]
  -- the factors have equal orders
  obtain ⟨A₀, hA₀⟩ : F.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    apply hN.2.1
    rw [← hFN]
    exact le_bot_iff.1 (iSup_le fun A => absurd A.2 (Finset.notMem_empty _))
  have hm : ∀ A : F, Nat.card (A : Subgroup G) = Nat.card A₀ := fun A => by
    obtain ⟨g, -, hg⟩ := htr A₀ hA₀ A A.2
    rw [← hg, card_cj]
  -- the point stabilizer in `N`, pulled back to the product
  let Hα : Subgroup G := (stabilizer N α).map N.subtype
  let H' : Subgroup (∀ A : F, (A : Subgroup G)) := Hα.comap φ
  have hH'card : Nat.card H' = Nat.card (stabilizer N α) := by
    have hmap : H'.map φ = Hα := by
      rw [Subgroup.map_comap_eq, hrange]
      exact inf_eq_right.2 (Subgroup.map_subtype_le _)
    rw [← Subgroup.card_map_of_injective hinj, hmap,
      Subgroup.card_map_of_injective N.subtype_injective]
  -- it contains no factor: a factor in it would fix every point
  have hnf : ∀ A : F, ¬ HasFactor H' A := by
    intro A hA
    have hfixA : ∀ a ∈ (A : Subgroup G), a • α = α := fun a ha => by
      have hmem : φ (Pi.mulSingle A ⟨a, ha⟩) ∈ Hα := hA ⟨a, ha⟩
      rw [Subgroup.noncommPiCoprod_mulSingle] at hmem
      obtain ⟨s, hs, hsa⟩ := hmem
      have has : a = N.subtype s := hsa.symm
      rw [has]
      exact hs
    have hA1 : ∀ a ∈ (A : Subgroup G), a = 1 := fun a ha => hfaith a fun x => by
      obtain ⟨m', rfl⟩ := exists_smul_eq N α x
      change a • (m' : G) • α = (m' : G) • α
      have hconj : (m' : G)⁻¹ * a * m' ∈ (A : Subgroup G) := by
        have := (hFn A A.2).2 (m' : G)⁻¹ (N.inv_mem m'.2) a ha
        simpa using this
      calc a • (m' : G) • α = (m' : G) • (((m' : G)⁻¹ * a * m') • α) := by
            simp [smul_smul, mul_assoc]
        _ = (m' : G) • α := by rw [hfixA _ hconj]
    have := (hFs A A.2).toNontrivial
    obtain ⟨b, hb⟩ := exists_ne (1 : (A : Subgroup G))
    exact hb (Subtype.ext (hA1 b b.2))
  -- so `2^j ≤ n²`
  have hsub := two_pow_mul_card_sq_le (T := fun A : F => ((A : Subgroup G) : Type _)) hm
    (fun A => hFs A A.2) (fun A => by
      obtain ⟨x, hx, y, hy, hxy⟩ := hFna A A.2
      exact ⟨⟨x, hx⟩, ⟨y, hy⟩, fun h => hxy (congrArg Subtype.val h)⟩) H' hnf
  rw [Fintype.card_coe] at hsub
  have hNcard : Nat.card N = Nat.card A₀ ^ F.card := by
    rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_pi,
      Finset.prod_congr rfl fun A _ => hm A, Finset.prod_const, Finset.card_univ,
      Fintype.card_coe]
  have hNstab : Nat.card N = Nat.card (stabilizer N α) * n := by
    rw [← Subgroup.card_mul_index (stabilizer N α), index_stabilizer_of_transitive N α,
      Nat.card_fin]
  have h2j : 2 ^ F.card ≤ n ^ 2 := by
    have hpos : 0 < Nat.card H' ^ 2 := pow_pos Nat.card_pos 2
    have : 2 ^ F.card * Nat.card H' ^ 2 ≤ n ^ 2 * Nat.card H' ^ 2 :=
      calc 2 ^ F.card * Nat.card H' ^ 2 ≤ Nat.card A₀ ^ (2 * F.card) := hsub
        _ = (Nat.card A₀ ^ F.card) ^ 2 := by rw [← pow_mul, mul_comm]
        _ = (Nat.card H' * n) ^ 2 := by rw [← hNcard, hNstab, hH'card]
        _ = n ^ 2 * Nat.card H' ^ 2 := by ring
    exact Nat.le_of_mul_le_mul_right this hpos
  -- the action on the factors
  have hGC := card_le_of_factors hk F hFk hFN hcjF
  rw [Subgroup.card_top] at hGC
  have hfac : k.factorial * 2 ^ k ≤ 2 ^ (k ^ 2 + k) := by
    rw [pow_add]
    exact Nat.mul_le_mul_right _ (factorial_le_two_pow_sq k)
  calc Nat.card G ≤ Nat.card C * (k.factorial * 2 ^ k) ^ F.card := hGC
    _ ≤ n * (2 ^ (k ^ 2 + k)) ^ F.card := Nat.mul_le_mul hC (Nat.pow_le_pow_left hfac _)
    _ = n * (2 ^ F.card) ^ (k ^ 2 + k) := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm (k ^ 2 + k)]
    _ ≤ n * (n ^ 2) ^ (k ^ 2 + k) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h2j _)
    _ = n ^ (2 * k ^ 2 + 2 * k + 1) := by
        rw [← pow_mul, ← pow_succ']
        congr 1
        ring

/-- **Quasiprimitive groups with bounded sections have polynomial order.** -/
theorem card_le_of_isQuasiPreprimitive_of_boundedSections {n k : ℕ}
    (G : Subgroup (Perm (Fin n))) (hk : BoundedSections k G) (hn : 2 ≤ n)
    [IsQuasiPreprimitive G (Fin n)] :
    Nat.card G ≤ n ^ (3 * k ^ 3 + 3 * k ^ 2 + 12 * k + 1) := by
  have : Nontrivial G := nontrivial_of_isPretransitive G hn
  obtain ⟨N, hN⟩ := exists_isMinNormal (Y := (⊤ : Subgroup G)) top_ne_bot
  by_cases hna : ∃ x ∈ N, ∃ y ∈ N, x * y ≠ y * x
  · refine (card_le_of_isQuasiPreprimitive_of_nonabelian G hk hn hN hna).trans
      (Nat.pow_le_pow_right (by omega) ?_)
    nlinarith [Nat.zero_le (k ^ 3), Nat.zero_le (k ^ 2), Nat.zero_le k]
  · push Not at hna
    exact card_le_of_isQuasiPreprimitive_of_abelian G hn (nnormal_top_iff.1 hN.1) hN.2.1 hna
      fun p _ V _ _ _ S ρ hρ hpS _ hVk => by
        have := card_le_of_boundedSections_linear (hk.subgroup S) ρ hρ hpS
        rwa [hVk] at this

/-- **The Babai–Cameron–Pálfy theorem**: a primitive subgroup of `Sym(n)`, `n ≥ 2`, all of
whose simple sections have order at most `k`, has order at most `n^{3 k³ + 3 k² + 12 k + 1}`. -/
theorem card_le_of_isPreprimitive_of_boundedSections {n k : ℕ} (G : Subgroup (Perm (Fin n)))
    (hk : BoundedSections k G) (hn : 2 ≤ n) [IsPreprimitive G (Fin n)] :
    Nat.card G ≤ n ^ (3 * k ^ 3 + 3 * k ^ 2 + 12 * k + 1) :=
  have : IsQuasiPreprimitive G (Fin n) := IsPreprimitive.isQuasiPreprimitive
  card_le_of_isQuasiPreprimitive_of_boundedSections G hk hn

end GraphIso.Groups
