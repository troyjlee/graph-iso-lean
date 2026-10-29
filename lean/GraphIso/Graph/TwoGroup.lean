module

public import GraphIso.Graph.Twins
public import Mathlib.GroupTheory.PGroup

/-!
# The layer groups are `2`-groups

The roots are two edges `{a, b}` and `{c, d}` (`Roots4`): the points of level `0` are exactly
`a, b, c, d`, and the only edges among them are `a b` and `c d`. Each root has its partner
(`partner`).

* `A₀` preserves partners. `edgeParity g`, whether `g` keeps `a` in `{a, b}`, is multiplicative
  like a homomorphism to `ℤ/2` (`edgeParity_mul`). An element keeping `{a, b}` squares to `1`,
  so every element of `A₀` satisfies `g⁴ = 1`.
* `isPGroup_autR`: every `A_r` is a `2`-group. Restricting `g ∈ A_{r+1}` to level `≤ r` gives
  an element of `A_r`, so some `g^(2^k)` fixes level `≤ r` pointwise, and such elements are
  involutions (`kernel_apply_apply`).
-/

@[expose] public section

namespace GraphIso.Graph

open Equiv Sims

variable {Δ N : ℕ} {G : GraphData} {roots : List ℕ} {lev : Array ℕ}

/-- The roots: two edges `{a, b}` and `{c, d}`, the only edges among the points of level `0`. -/
structure Roots4 (N : ℕ) (G : GraphData) (lev : Array ℕ) (a b c d : ℕ) : Prop where
  lt_a : a < N
  lt_b : b < N
  lt_c : c < N
  lt_d : d < N
  zero_iff : ∀ v < N, get lev v = 0 ↔ (v = a ∨ v = b ∨ v = c ∨ v = d)
  ab : Adj G a b
  cd : Adj G c d
  only : ∀ u v, get lev u = 0 → get lev v = 0 → Adj G u v →
    (u = a ∧ v = b) ∨ (u = b ∧ v = a) ∨ (u = c ∧ v = d) ∨ (u = d ∧ v = c)
  hab : a ≠ b
  hac : a ≠ c
  had : a ≠ d
  hbc : b ≠ c
  hbd : b ≠ d
  hcd : c ≠ d

/-- The partner of a root. -/
def partner (a b c d v : ℕ) : ℕ := if v = a then b else if v = b then a else if v = c then d else c

section Roots

variable {a b c d : ℕ} (hR : Roots4 N G lev a b c d)
include hR

omit hR in
theorem partner_a : partner a b c d a = b := by simp [partner]
theorem partner_b : partner a b c d b = a := by simp [partner, hR.hab.symm]
theorem partner_c : partner a b c d c = d := by simp [partner, hR.hac.symm, hR.hbc.symm]
theorem partner_d : partner a b c d d = c := by
  simp [partner, hR.had.symm, hR.hbd.symm, hR.hcd.symm]

/-- The roots, as a disjunction. -/
theorem root_cases {v : ℕ} (hv : v < N) (h0 : get lev v = 0) :
    v = a ∨ v = b ∨ v = c ∨ v = d := (hR.zero_iff v hv).1 h0

theorem lev_a : get lev a = 0 := (hR.zero_iff a hR.lt_a).2 (Or.inl rfl)
theorem lev_b : get lev b = 0 := (hR.zero_iff b hR.lt_b).2 (Or.inr (Or.inl rfl))
theorem lev_c : get lev c = 0 := (hR.zero_iff c hR.lt_c).2 (Or.inr (Or.inr (Or.inl rfl)))
theorem lev_d : get lev d = 0 := (hR.zero_iff d hR.lt_d).2 (Or.inr (Or.inr (Or.inr rfl)))

/-- Roots are adjacent exactly to their partners, among roots. -/
theorem adj_root_iff (hG : G.ValidD Δ N) {u v : ℕ} (hu : u < N) (hlu : get lev u = 0)
    (hlv : get lev v = 0) : Adj G u v ↔ v = partner a b c d u := by
  constructor
  · intro h
    rcases hR.only u v hlu hlv h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact (partner_a).symm
    · exact (partner_b hR).symm
    · exact (partner_c hR).symm
    · exact (partner_d hR).symm
  · rintro rfl
    rcases root_cases hR hu hlu with rfl | rfl | rfl | rfl
    · rw [partner_a]; exact hR.ab
    · rw [partner_b hR]; exact hG.symm _ _ hR.ab
    · rw [partner_c hR]; exact hR.cd
    · rw [partner_d hR]; exact hG.symm _ _ hR.cd

theorem partner_lt {v : ℕ} (hv : v < N) (h0 : get lev v = 0) : partner a b c d v < N := by
  rcases root_cases hR hv h0 with rfl | rfl | rfl | rfl
  · rw [partner_a]; exact hR.lt_b
  · rw [partner_b hR]; exact hR.lt_a
  · rw [partner_c hR]; exact hR.lt_d
  · rw [partner_d hR]; exact hR.lt_c

theorem lev_partner {v : ℕ} (hv : v < N) (h0 : get lev v = 0) :
    get lev (partner a b c d v) = 0 := by
  rcases root_cases hR hv h0 with rfl | rfl | rfl | rfl
  · rw [partner_a]; exact lev_b hR
  · rw [partner_b hR]; exact lev_a hR
  · rw [partner_c hR]; exact lev_d hR
  · rw [partner_d hR]; exact lev_c hR

omit hR in
/-- Mapping roots to roots and preserving adjacency among them. -/
def RootAut (N : ℕ) (G : GraphData) (lev : Array ℕ) (g : Perm (Fin N)) : Prop :=
  (∀ v < N, get lev v = 0 → get lev (act g v) = 0) ∧
    ∀ u v, u < N → v < N → get lev u = 0 → get lev v = 0 →
      (Adj G (act g u) (act g v) ↔ Adj G u v)

omit hR in
/-- Every layer group preserves the roots. -/
theorem rootAut_of_autR {r : ℕ} {g : Perm (Fin N)} (hg : g ∈ AutR N G lev r) :
    RootAut N G lev g := by
  refine ⟨fun v hv h => by rw [hg.2.1 v hv, h], fun u v hu hv hlu hlv => ?_⟩
  have e : ∀ x y, get lev x = 0 → get lev y = 0 → (EdgeR G lev r x y ↔ Adj G x y) :=
    fun x y hx hy => ⟨fun h => h.1, fun h => ⟨h, by omega, by omega, Or.inr (Or.inr ⟨hx, hy⟩)⟩⟩
  rw [← e _ _ (by rw [hg.2.1 u hu, hlu]) (by rw [hg.2.1 v hv, hlv]), ← e u v hlu hlv]
  exact hg.2.2 u v hu hv

/-- **Root-preserving permutations preserve partners.** -/
theorem act_partner (hG : G.ValidD Δ N) {g : Perm (Fin N)} (hg : RootAut N G lev g) {v : ℕ}
    (hv : v < N) (h0 : get lev v = 0) :
    act g (partner a b c d v) = partner a b c d (act g v) := by
  have hp := partner_lt hR hv h0
  have hlp := lev_partner hR hv h0
  have hadj : Adj G v (partner a b c d v) := (adj_root_iff hR hG hv h0 hlp).2 rfl
  have he' := (hg.2 v _ hv hp h0 hlp).2 hadj
  have hgv : get lev (act g v) = 0 := hg.1 v hv h0
  have hgp : get lev (act g (partner a b c d v)) = 0 := hg.1 _ hp hlp
  exact (adj_root_iff hR hG (act_lt g hv) hgv hgp).1 he'

end Roots

/-! ### The edge parity -/

section Parity

variable {a b c d : ℕ} (hR : Roots4 N G lev a b c d) (hG : G.ValidD Δ N)
include hR hG

/-- `g` keeps `a` in the edge `{a, b}`. -/
def EPar (a b : ℕ) (g : Perm (Fin N)) : Prop := act g a = a ∨ act g a = b

omit hR hG in
theorem act_root {g : Perm (Fin N)} (hg : RootAut N G lev g) {v : ℕ} (hv : v < N)
    (h0 : get lev v = 0) : act g v < N ∧ get lev (act g v) = 0 :=
  ⟨act_lt g hv, hg.1 v hv h0⟩

omit hG in
theorem partner_mem_ab {y : ℕ} (hy : y < N) (h0 : get lev y = 0) :
    (partner a b c d y = a ∨ partner a b c d y = b) ↔ (y = a ∨ y = b) := by
  have := hR.hab; have := hR.hac; have := hR.had; have := hR.hbc; have := hR.hbd; have := hR.hcd
  rcases root_cases hR hy h0 with rfl | rfl | rfl | rfl
  · rw [partner_a]; tauto
  · rw [partner_b hR]; tauto
  · rw [partner_c hR]; constructor <;> intro h <;> rcases h with h | h <;> omega
  · rw [partner_d hR]; constructor <;> intro h <;> rcases h with h | h <;> omega

theorem act_b_mem {g : Perm (Fin N)} (hg : RootAut N G lev g) :
    (act g b = a ∨ act g b = b) ↔ EPar a b g := by
  have hpb : act g b = partner a b c d (act g a) := by
    rw [← act_partner hR hG hg hR.lt_a (lev_a hR), partner_a]
  obtain ⟨hgaN, hga0⟩ := act_root hg hR.lt_a (lev_a hR)
  rw [hpb, partner_mem_ab hR hgaN hga0]
  rfl

theorem act_cd_mem {g : Perm (Fin N)} (hg : RootAut N G lev g) {x : ℕ} (hx : x = c ∨ x = d) :
    (act g x = a ∨ act g x = b) ↔ ¬ EPar a b g := by
  have hxN : x < N := by rcases hx with rfl | rfl; exacts [hR.lt_c, hR.lt_d]
  have hx0 : get lev x = 0 := by rcases hx with rfl | rfl; exacts [lev_c hR, lev_d hR]
  obtain ⟨hgxN, hgx0⟩ := act_root hg hxN hx0
  have hxa : x ≠ a := by rcases hx with rfl | rfl; exacts [hR.hac.symm, hR.had.symm]
  have hxb : x ≠ b := by rcases hx with rfl | rfl; exacts [hR.hbc.symm, hR.hbd.symm]
  have hne_a : act g x ≠ act g a := fun e => hxa (act_injective g e)
  have hne_b : act g x ≠ act g b := fun e => hxb (act_injective g e)
  have hab' : act g a ≠ act g b := fun e => hR.hab (act_injective g e)
  have hb := act_b_mem hR hG hg
  unfold EPar at hb ⊢
  have := hR.hab; have := hR.hac; have := hR.had; have := hR.hbc; have := hR.hbd; have := hR.hcd
  constructor
  · rintro h (hE | hE)
    · have hb' := hb.2 (Or.inl hE)
      rcases h with h | h <;> rcases hb' with h' | h' <;> omega
    · have hb' := hb.2 (Or.inr hE)
      rcases h with h | h <;> rcases hb' with h' | h' <;> omega
  · intro hE
    obtain ⟨hgaN, hga0⟩ := act_root hg hR.lt_a (lev_a hR)
    obtain ⟨hgbN, hgb0⟩ := act_root hg hR.lt_b (lev_b hR)
    have hga : act g a = c ∨ act g a = d := by
      rcases root_cases hR hgaN hga0 with h | h | h | h
      · exact absurd (Or.inl h) hE
      · exact absurd (Or.inr h) hE
      · exact Or.inl h
      · exact Or.inr h
    have hgb : act g b = c ∨ act g b = d := by
      rcases root_cases hR hgbN hgb0 with h | h | h | h
      · exact absurd (hb.1 (Or.inl h)) hE
      · exact absurd (hb.1 (Or.inr h)) hE
      · exact Or.inl h
      · exact Or.inr h
    rcases root_cases hR hgxN hgx0 with h | h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exfalso; rcases hga with h₁ | h₁ <;> rcases hgb with h₂ | h₂ <;> omega
    · exfalso; rcases hga with h₁ | h₁ <;> rcases hgb with h₂ | h₂ <;> omega

/-- **The edge parity is multiplicative.** -/
theorem edgeParity_mul {g h : Perm (Fin N)} (hg : RootAut N G lev g)
    (hh : RootAut N G lev h) : EPar a b (g * h) ↔ (EPar a b g ↔ EPar a b h) := by
  have hgb := act_b_mem hR hG hg
  have hgc := act_cd_mem hR hG hg (x := c) (Or.inl rfl)
  have hgd := act_cd_mem hR hG hg (x := d) (Or.inr rfl)
  unfold EPar at hgb hgc hgd ⊢
  rw [act_mul]
  obtain ⟨hhaN, hha0⟩ := act_root hh hR.lt_a (lev_a hR)
  have := hR.hab; have := hR.hac; have := hR.had; have := hR.hbc; have := hR.hbd
  rcases root_cases hR hhaN hha0 with e | e | e | e <;> rw [e]
  · exact ⟨fun h' => ⟨fun _ => Or.inl rfl, fun _ => h'⟩, fun h' => h'.2 (Or.inl rfl)⟩
  · rw [hgb]
    exact ⟨fun h' => ⟨fun _ => Or.inr rfl, fun _ => h'⟩, fun h' => h'.2 (Or.inr rfl)⟩
  · have hn : ¬ (c = a ∨ c = b) := by omega
    rw [hgc]
    simp only [hn, iff_false]
  · have hn : ¬ (d = a ∨ d = b) := by omega
    rw [hgd]
    simp only [hn, iff_false]

omit hR hG in
/-- A map sending a pair into itself injectively squares to the identity on it. -/
theorem two_cycle {f : ℕ → ℕ} {x y : ℕ} (hx : f x = x ∨ f x = y) (hy : f y = x ∨ f y = y)
    (hne : f x ≠ f y) : f (f x) = x ∧ f (f y) = y := by
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact absurd (hx.trans hy.symm) hne
  · exact ⟨by rw [hx, hx], by rw [hy, hy]⟩
  · exact ⟨by rw [hx, hy], by rw [hy, hx]⟩
  · exact absurd (hx.trans hy.symm) hne

/-- An element of `A₀` keeping the edge `{a, b}` is an involution. -/
theorem kernel0_apply_apply {k : Perm (Fin N)} (hk : k ∈ AutR N G lev 0) (hE : EPar a b k)
    {v : ℕ} (hv : v < N) : act k (act k v) = v := by
  by_cases h0 : get lev v = 0
  · have hb := (act_b_mem hR hG (rootAut_of_autR hk)).2 hE
    have hc := (act_cd_mem hR hG (rootAut_of_autR hk) (x := c) (Or.inl rfl)).not.2 (not_not.2 hE)
    have hd := (act_cd_mem hR hG (rootAut_of_autR hk) (x := d) (Or.inr rfl)).not.2 (not_not.2 hE)
    unfold EPar at hE
    have hab' : act k a ≠ act k b := fun e => hR.hab (act_injective k e)
    have hcd' : act k c ≠ act k d := fun e => hR.hcd (act_injective k e)
    obtain ⟨hcN, hc0⟩ := act_root (rootAut_of_autR hk) hR.lt_c (lev_c hR)
    obtain ⟨hdN, hd0⟩ := act_root (rootAut_of_autR hk) hR.lt_d (lev_d hR)
    have hc' : act k c = c ∨ act k c = d := by
      rcases root_cases hR hcN hc0 with e | e | e | e
      · exact absurd (Or.inl e) hc
      · exact absurd (Or.inr e) hc
      · exact Or.inl e
      · exact Or.inr e
    have hd' : act k d = c ∨ act k d = d := by
      rcases root_cases hR hdN hd0 with e | e | e | e
      · exact absurd (Or.inl e) hd
      · exact absurd (Or.inr e) hd
      · exact Or.inl e
      · exact Or.inr e
    have h₁ := two_cycle hE hb hab'
    have h₂ := two_cycle hc' hd' hcd'
    rcases root_cases hR hv h0 with e | e | e | e <;> rw [e]
    exacts [h₁.1, h₁.2, h₂.1, h₂.2]
  · have hfix := hk.1 v hv (by omega)
    rw [hfix, hfix]

/-- **Every element of `A₀` satisfies `g⁴ = 1`.** -/
theorem autR0_pow_four {g : Perm (Fin N)} (hg : g ∈ AutR N G lev 0) : g ^ 4 = 1 := by
  have hE : EPar a b (g * g) := by
    rw [edgeParity_mul hR hG (rootAut_of_autR hg) (rootAut_of_autR hg)]
  have hgg := mul_mem hg hg
  have e : g ^ 4 = (g * g) * (g * g) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  rw [e]
  apply Perm.ext
  intro x
  apply Fin.ext
  have := kernel0_apply_apply hR hG hgg hE x.2
  rw [act_of_lt _ x.2, act_of_lt _ (Fin.isLt _)] at this
  simpa [Perm.mul_apply] using this

end Parity

/-! ### All layer groups -/

theorem act_pow_res {r : ℕ} {g : Perm (Fin N)} (hg : g ∈ AutR N G lev (r + 1)) :
    ∀ (m : ℕ) (v : ℕ), get lev v ≤ r → act (g ^ m) v = act (resPerm hg ^ m) v
  | 0, v, _ => by simp
  | m + 1, v, hv => by
    have hgv : act g v = act (resPerm hg) v := by
      rw [act_resPerm]
      simp [resFun, hv]
    have hlv : get lev (act g v) ≤ r := by
      by_cases hvN : v < N
      · rw [hg.2.1 v hvN]; exact hv
      · rw [act_of_ge _ (by omega)]; exact hv
    rw [pow_succ, pow_succ, act_mul, act_mul, act_pow_res hg m _ hlv, hgv]

/-- **Every layer group is a `2`-group.** -/
theorem isPGroup_autR {a b c d : ℕ} (hZ : Layered N G roots lev)
    (hR : Roots4 N G lev a b c d) : ∀ r, IsPGroup 2 (AutR N G lev r)
  | 0 => fun x => ⟨2, Subtype.ext (by
      rw [Subgroup.coe_pow]
      exact autR0_pow_four hR hZ.valid x.2)⟩
  | r + 1 => fun x => by
    obtain ⟨k, hk⟩ := isPGroup_autR hZ hR r ⟨resPerm x.2, (resPerm_mem hZ x.2).1⟩
    have hk' : resPerm x.2 ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      rwa [Subgroup.coe_pow] at this
    set q := (x : Perm (Fin N)) ^ 2 ^ k with hq
    have hqA : q ∈ AutR N G lev (r + 1) := pow_mem x.2 _
    have hlow : ∀ v < N, get lev v ≤ r → act q v = v := by
      intro v _ hv
      rw [hq, act_pow_res x.2 _ v hv, hk', act_one]
    have hqq : q * q = 1 := Perm.ext fun y => by
      rw [Perm.mul_apply, kernel_apply_apply hZ le_rfl hqA hlow y]
      rfl
    refine ⟨k + 1, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, pow_succ, pow_mul, pow_two, ← hq, hqq]
    rfl

/-! ### The initial group -/

theorem act_swap_eq (x y : Fin N) (v : ℕ) :
    act (swap x y) v = if v = x.val then y.val else if v = y.val then x.val else v := by
  by_cases hv : v < N
  · rw [act_of_lt _ hv, swap_apply_def]
    by_cases h₁ : v = x.val
    · subst h₁; simp
    · by_cases h₂ : v = y.val
      · subst h₂
        have : (⟨y.val, hv⟩ : Fin N) ≠ x := fun e => h₁ (congrArg Fin.val e)
        simp [this, h₁]
      · have e₁ : (⟨v, hv⟩ : Fin N) ≠ x := fun e => h₁ (congrArg Fin.val e)
        have e₂ : (⟨v, hv⟩ : Fin N) ≠ y := fun e => h₂ (congrArg Fin.val e)
        simp [e₁, e₂, h₁, h₂]
  · rw [act_of_ge _ (by omega)]
    have h₁ : v ≠ x.val := by have := x.2; omega
    have h₂ : v ≠ y.val := by have := y.2; omega
    simp [h₁, h₂]

section Initial

variable {a b c d : ℕ} (hR : Roots4 N G lev a b c d) (hG : G.ValidD Δ N)
include hR hG

/-- A permutation fixing the points of positive level, mapping roots to roots and commuting
with partners lies in `A₀`. -/
theorem mem_autR0 {g : Perm (Fin N)} (hfix : ∀ v < N, 0 < get lev v → act g v = v)
    (hroot : ∀ v < N, get lev v = 0 → get lev (act g v) = 0)
    (hpart : ∀ v < N, get lev v = 0 → act g (partner a b c d v) = partner a b c d (act g v)) :
    g ∈ AutR N G lev 0 := by
  have hlev : ∀ v < N, get lev (act g v) = get lev v := fun v hv => by
    by_cases h : get lev v = 0
    · rw [hroot v hv h, h]
    · rw [hfix v hv (by omega)]
  refine ⟨fun v hv h => hfix v hv h, hlev, fun u v hu hv => ?_⟩
  have e : ∀ x y, x < N → y < N → (EdgeR G lev 0 x y ↔
      (get lev x = 0 ∧ get lev y = 0 ∧ y = partner a b c d x)) := by
    intro x y hx hy
    unfold EdgeR
    constructor
    · rintro ⟨hadj, h₁, h₂, -⟩
      exact ⟨by omega, by omega, (adj_root_iff hR hG hx (by omega) (by omega)).1 hadj⟩
    · rintro ⟨h₁, h₂, h₃⟩
      exact ⟨(adj_root_iff hR hG hx h₁ h₂).2 h₃, by omega, by omega, Or.inr (Or.inr ⟨h₁, h₂⟩)⟩
  rw [e _ _ (act_lt g hu) (act_lt g hv), e u v hu hv, hlev u hu, hlev v hv]
  constructor
  · rintro ⟨h₁, h₂, h₃⟩
    refine ⟨h₁, h₂, act_injective g ?_⟩
    rw [h₃, hpart u hu h₁]
  · rintro ⟨h₁, h₂, h₃⟩
    exact ⟨h₁, h₂, by rw [h₃, hpart u hu h₁]⟩

end Initial

section Gens

variable {a b c d : ℕ} (hR : Roots4 N G lev a b c d) (hG : G.ValidD Δ N)

/-- The generators of `A₀`: the two edge swaps and the exchange of the edges. -/
def gens0 : Set (Perm (Fin N)) :=
  {swap ⟨a, hR.lt_a⟩ ⟨b, hR.lt_b⟩, swap ⟨c, hR.lt_c⟩ ⟨d, hR.lt_d⟩,
    swap ⟨a, hR.lt_a⟩ ⟨c, hR.lt_c⟩ * swap ⟨b, hR.lt_b⟩ ⟨d, hR.lt_d⟩}

include hR in
theorem not_root {v : ℕ} (hv : v < N) (h : 0 < get lev v) : v ≠ a ∧ v ≠ b ∧ v ≠ c ∧ v ≠ d := by
  have := (hR.zero_iff v hv).not.1 (by omega)
  tauto

include hR hG in
theorem gens0_mem : gens0 hR ⊆ AutR N G lev 0 := by
  have hab := hR.hab; have hac := hR.hac; have had := hR.had
  have hbc := hR.hbc; have hbd := hR.hbd; have hcd := hR.hcd
  have hba := hab.symm; have hca := hac.symm; have hda := had.symm
  have hcb := hbc.symm; have hdb := hbd.symm; have hdc := hcd.symm
  have la := lev_a hR; have lb := lev_b hR; have lc := lev_c hR; have ld := lev_d hR
  rintro g (rfl | rfl | rfl)
  · refine mem_autR0 hR hG (fun v hv h => ?_) (fun v hv h => ?_) (fun v hv h => ?_)
    · obtain ⟨h₁, h₂, -, -⟩ := not_root hR hv h
      simp [act_swap_eq, h₁, h₂]
    · rcases root_cases hR hv h with rfl | rfl | rfl | rfl <;>
        simp [act_swap_eq, *]
    · rcases root_cases hR hv h with rfl | rfl | rfl | rfl <;>
        simp [act_swap_eq, partner, *]
  · refine mem_autR0 hR hG (fun v hv h => ?_) (fun v hv h => ?_) (fun v hv h => ?_)
    · obtain ⟨-, -, h₁, h₂⟩ := not_root hR hv h
      simp [act_swap_eq, h₁, h₂]
    · rcases root_cases hR hv h with rfl | rfl | rfl | rfl <;>
        simp [act_swap_eq, *]
    · rcases root_cases hR hv h with rfl | rfl | rfl | rfl <;>
        simp [act_swap_eq, partner, *]
  · refine mem_autR0 hR hG (fun v hv h => ?_) (fun v hv h => ?_) (fun v hv h => ?_)
    · obtain ⟨h₁, h₂, h₃, h₄⟩ := not_root hR hv h
      simp [act_mul, act_swap_eq, h₁, h₂, h₃, h₄]
    · rcases root_cases hR hv h with rfl | rfl | rfl | rfl <;>
        simp [act_mul, act_swap_eq, *]
    · rcases root_cases hR hv h with rfl | rfl | rfl | rfl <;>
        simp [act_mul, act_swap_eq, partner, *]

include hR hG in
theorem eq_one_of_fix {g : Perm (Fin N)} (hg : g ∈ AutR N G lev 0) (ha : act g a = a)
    (hc : act g c = c) : g = 1 := by
  have hb : act g b = b := by
    have := act_partner hR hG (rootAut_of_autR hg) hR.lt_a (lev_a hR)
    rwa [partner_a, ha, partner_a] at this
  have hd : act g d = d := by
    have := act_partner hR hG (rootAut_of_autR hg) hR.lt_c (lev_c hR)
    rwa [partner_c hR, hc, partner_c hR] at this
  apply Perm.ext
  intro x
  have key : act g x.val = x.val := by
    by_cases h0 : get lev x = 0
    · rcases root_cases hR x.2 h0 with e | e | e | e <;> rw [e] <;> assumption
    · exact hg.1 x x.2 (by omega)
  rw [act_of_lt g x.2] at key
  exact Fin.ext key

include hR hG in
/-- **The generators of `A₀`.** -/
theorem closure_gens0 : Subgroup.closure (gens0 hR) = AutR N G lev 0 := by
  have hgm := gens0_mem hR hG
  apply le_antisymm ((Subgroup.closure_le _).2 hgm)
  set σab := swap (⟨a, hR.lt_a⟩ : Fin N) ⟨b, hR.lt_b⟩ with hσab
  set σcd := swap (⟨c, hR.lt_c⟩ : Fin N) ⟨d, hR.lt_d⟩ with hσcd
  set τ := swap (⟨a, hR.lt_a⟩ : Fin N) ⟨c, hR.lt_c⟩ * swap ⟨b, hR.lt_b⟩ ⟨d, hR.lt_d⟩ with hτ
  have m₁ : σab ∈ gens0 hR := Or.inl rfl
  have m₂ : σcd ∈ gens0 hR := Or.inr (Or.inl rfl)
  have m₃ : τ ∈ gens0 hR := Or.inr (Or.inr rfl)
  have hσab' : σab ∈ Subgroup.closure (gens0 hR) := Subgroup.subset_closure m₁
  have hσcd' : σcd ∈ Subgroup.closure (gens0 hR) := Subgroup.subset_closure m₂
  have hτ' : τ ∈ Subgroup.closure (gens0 hR) := Subgroup.subset_closure m₃
  have hσabA : σab ∈ AutR N G lev 0 := hgm m₁
  have hσcdA : σcd ∈ AutR N G lev 0 := hgm m₂
  have hτA : τ ∈ AutR N G lev 0 := hgm m₃
  have hab := hR.hab; have hac := hR.hac; have had := hR.had
  have hbc := hR.hbc; have hbd := hR.hbd; have hcd := hR.hcd
  -- fixing `a`
  have step₁ : ∀ g ∈ AutR N G lev 0, act g a = a → g ∈ Subgroup.closure (gens0 hR) := by
    intro g hg ha
    have hb : act g b = b := by
      have := act_partner hR hG (rootAut_of_autR hg) hR.lt_a (lev_a hR)
      rwa [partner_a, ha, partner_a] at this
    obtain ⟨hcN, hc0⟩ := act_root (rootAut_of_autR hg) hR.lt_c (lev_c hR)
    rcases root_cases hR hcN hc0 with e | e | e | e
    · exact absurd (act_injective g (e.trans ha.symm)) hac.symm
    · exact absurd (act_injective g (e.trans hb.symm)) hbc.symm
    · rw [eq_one_of_fix hR hG hg ha e]
      exact one_mem _
    · have h1 : σcd * g = 1 := eq_one_of_fix hR hG (mul_mem hσcdA hg)
        (by rw [act_mul, ha, hσcd, act_swap_eq]; simp [hac, had])
        (by rw [act_mul, e, hσcd, act_swap_eq]; simp [hcd.symm])
      have : g = σcd⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [this]
      exact inv_mem hσcd'
  -- keeping the edge `{a, b}`
  have step₂ : ∀ g ∈ AutR N G lev 0, EPar a b g → g ∈ Subgroup.closure (gens0 hR) := by
    intro g hg hE
    rcases hE with ha | ha
    · exact step₁ g hg ha
    · have := step₁ (σab * g) (mul_mem hσabA hg)
        (by rw [act_mul, ha, hσab, act_swap_eq]; simp [hab.symm])
      have e : g = σab * (σab * g) := by rw [← mul_assoc, hσab, swap_mul_self, one_mul]
      rw [e]
      exact mul_mem hσab' this
  intro g hg
  by_cases hE : EPar a b g
  · exact step₂ g hg hE
  · have hτE : ¬ EPar a b τ := by
      unfold EPar
      rw [hτ, act_mul, act_swap_eq, act_swap_eq]
      simp [hab, had, hac.symm, hbc.symm]
    have h' : EPar a b (τ * g) := by
      rw [edgeParity_mul hR hG (rootAut_of_autR hτA) (rootAut_of_autR hg)]
      tauto
    have := step₂ (τ * g) (mul_mem hτA hg) h'
    have e : g = τ⁻¹ * (τ * g) := by rw [← mul_assoc, inv_mul_cancel, one_mul]
    rw [e]
    exact mul_mem (inv_mem hτ') this

end Gens

end GraphIso.Graph
