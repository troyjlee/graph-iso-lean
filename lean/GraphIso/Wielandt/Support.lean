module

public import GraphIso.Wielandt.Commutator
public import Mathlib.GroupTheory.GroupAction.Jordan
public import Mathlib.Tactic.Linarith

/-!
# Small supports in `3`-transitive groups

Stage 16a. Let `G ≤ Sym(Ω)` be `3`-transitive, `|Ω| = n`, and `x ∈ G`, `x ≠ 1`, with support `S`
of size `s`, `6 s ≤ n`.

* **Averaging** (`exists_mem_card_inter_le`): fix `a ∈ S`, `a' = x a` and `b ∉ S`. Over the
  elements `h ∈ G` with `h a = a` and `h a' = b`, each `h w` (`w ≠ a, a'`) is equidistributed on
  `Ω \ {a, b}` (by `3`-transitivity), so some such `h` has
  `(n − 2) |S ∩ h⁻¹(S)| ≤ (n − 2) + (s − 1)(s − 2)`.
* **The reduction** (`exists_isThreeCycle_mem`): for `y = h x h⁻¹`, the commutator `⁅x, y⁆ ∈ G` is
  not `1` (at `a`: `x y a = b ≠ y x a`) and moves at most `3 |S ∩ h(S)|` points. Either the
  overlap is the single point `a`, and `⁅x, y⁆` is a `3`-cycle, or `⁅x, y⁆` has support smaller
  than `s` and we recurse. Hence `G` contains a `3`-cycle, and so `Alt(Ω) ≤ G` (Jordan,
  `alternatingGroup_le_of_support_le`).
-/

@[expose] public section

namespace GraphIso.Wielandt

open Equiv Equiv.Perm Finset MulAction
open scoped commutatorElement

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem ite_eq_of_pos {p : Prop} [Decidable p] {β : Sort*} {a b : β} (h : p) :
    (if p then a else b) = a := by simp [h]

theorem ite_eq_of_neg {p : Prop} [Decidable p] {β : Sort*} {a b : β} (h : ¬p) :
    (if p then a else b) = b := by simp [h]

/-- Three distinct points, as an embedding of `Fin 3`. -/
def emb3 (a b c : α) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : Fin 3 ↪ α :=
  ⟨![a, b, c], by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]⟩

omit [Fintype α] [DecidableEq α] in
/-- **`3`-transitivity on points.** -/
theorem exists_mem_map3 (G : Subgroup (Perm α)) [IsMultiplyPretransitive G α 3]
    {a b c a' b' c' : α} (h1 : a ≠ b) (h2 : a ≠ c) (h3 : b ≠ c) (h1' : a' ≠ b') (h2' : a' ≠ c')
    (h3' : b' ≠ c') : ∃ g ∈ G, g a = a' ∧ g b = b' ∧ g c = c' := by
  obtain ⟨g, hg⟩ := exists_smul_eq G (emb3 a b c h1 h2 h3) (emb3 a' b' c' h1' h2' h3')
  have e : ∀ i, (g : Perm α) (![a, b, c] i) = ![a', b', c'] i := fun i => by
    have := congrArg (fun f : Fin 3 ↪ α => f i) hg
    exact this
  exact ⟨g, g.2, by simpa using e 0, by simpa using e 1, by simpa using e 2⟩

omit [Fintype α] in
/-- `|S ∩ h(S)| = |{w ∈ S | h w ∈ S}|`. -/
theorem card_inter_map_eq (S : Finset α) (h : Perm α) :
    #(S ∩ S.map h.toEmbedding) = #(S.filter fun w => h w ∈ S) := by
  symm
  rw [← card_map h.toEmbedding]
  congr 1
  ext v
  simp only [mem_inter, mem_map, mem_filter, Equiv.toEmbedding_apply]
  constructor
  · rintro ⟨w, ⟨hw, hhw⟩, rfl⟩
    exact ⟨hhw, w, hw, rfl⟩
  · rintro ⟨hv, w, hw, rfl⟩
    exact ⟨w, ⟨hw, hv⟩, rfl⟩

/-- **The averaging lemma.** For `a, a' ∈ S` distinct and `b ∉ S`, some `h ∈ G` with `h a = a`
and `h a' = b` has `(n − 2) |{w ∈ S | h w ∈ S}| ≤ (n − 2) + (|S| − 1)(|S| − 2)`. -/
theorem exists_mem_card_inter_le (G : Subgroup (Perm α)) [IsMultiplyPretransitive G α 3]
    {S : Finset α} {a a' b : α} (ha : a ∈ S) (ha' : a' ∈ S) (hb : b ∉ S) (haa : a ≠ a') :
    ∃ h ∈ G, h a = a ∧ h a' = b ∧
      (Fintype.card α - 2) * #(S.filter fun w => h w ∈ S) ≤
        (Fintype.card α - 2) + (#S - 1) * (#S - 2) := by
  classical
  set n := Fintype.card α with hn
  have hab : a ≠ b := fun h => hb (h ▸ ha)
  have ha'b : a' ≠ b := fun h => hb (h ▸ ha')
  set C := (univ : Finset (Perm α)).filter (fun h => h ∈ G ∧ h a = a ∧ h a' = b) with hC
  have hmemC : ∀ h, h ∈ C ↔ h ∈ G ∧ h a = a ∧ h a' = b := fun h => by simp [hC]
  -- the fibers of `h ↦ h w` over `Ω \ {a, b}` have equal sizes
  have hfib : ∀ w, w ≠ a → w ≠ a' → ∀ v, v ≠ a → v ≠ b →
      (n - 2) * #(C.filter fun h => h w = v) = #C := by
    intro w hwa hwa' v hva hvb
    have hle : ∀ v₁ v₂, v₁ ≠ a → v₁ ≠ b → v₂ ≠ a → v₂ ≠ b →
        #(C.filter fun h => h w = v₁) ≤ #(C.filter fun h => h w = v₂) := by
      intro v₁ v₂ h1a h1b h2a h2b
      obtain ⟨g, hgG, hga, hgb, hgv⟩ :=
        exists_mem_map3 G hab (Ne.symm h1a) (Ne.symm h1b) hab (Ne.symm h2a) (Ne.symm h2b)
      refine card_le_card_of_injOn (fun h => g * h) ?_ ?_
      · intro h hh
        simp only [mem_coe, mem_filter, hmemC] at hh ⊢
        obtain ⟨⟨hG, h1, h2⟩, h3⟩ := hh
        exact ⟨⟨G.mul_mem hgG hG, by simp [h1, hga], by simp [h2, hgb]⟩, by simp [h3, hgv]⟩
      · intro h₁ _ h₂ _ h
        exact mul_left_cancel h
    set t := (univ.erase a).erase b with ht
    have hmt : ∀ h ∈ C, h w ∈ t := by
      intro h hh
      rw [hmemC] at hh
      simp only [ht, mem_erase, mem_univ, and_true]
      refine ⟨fun e => hwa' (h.injective (e.trans hh.2.2.symm)), fun e => hwa ?_⟩
      exact h.injective (e.trans hh.2.1.symm)
    have hsum := card_eq_sum_card_fiberwise hmt
    have hconst : ∀ v' ∈ t, #(C.filter fun h => h w = v') = #(C.filter fun h => h w = v) := by
      intro v' hv'
      simp only [ht, mem_erase, mem_univ, and_true] at hv'
      exact le_antisymm (hle v' v hv'.2 hv'.1 hva hvb) (hle v v' hva hvb hv'.2 hv'.1)
    rw [sum_congr rfl hconst, sum_const, smul_eq_mul] at hsum
    have hct : #t = n - 2 := by
      rw [ht, card_erase_of_mem (by simp [Ne.symm hab]), card_erase_of_mem (mem_univ _),
        card_univ]
      omega
    rw [hsum, hct]
  -- the double count
  have hcount : ∀ w ∈ S, (n - 2) * #(C.filter fun h => h w ∈ S) =
      if w = a then (n - 2) * #C else if w = a' then 0 else (#S - 1) * #C := by
    intro w hw
    split_ifs with h1 h2
    · subst h1
      rw [filter_true_of_mem]
      intro h hh
      rw [((hmemC h).mp hh).2.1]
      exact ha
    · subst h2
      rw [filter_false_of_mem fun h hh => ?_, card_empty, mul_zero]
      rw [(hmemC h).mp hh |>.2.2]
      exact hb
    · have hmS : ∀ h ∈ C.filter (fun h => h w ∈ S), h w ∈ S.erase a := by
        intro h hh
        rw [mem_filter, hmemC] at hh
        refine mem_erase.mpr ⟨fun e => h1 (h.injective (e.trans hh.1.2.1.symm)), hh.2⟩
      rw [card_eq_sum_card_fiberwise hmS, mul_sum]
      have : ∀ v ∈ S.erase a, (n - 2) * #((C.filter fun h => h w ∈ S).filter fun h => h w = v)
          = #C := by
        intro v hv
        rw [mem_erase] at hv
        rw [filter_filter, ← hfib w h1 h2 v hv.1 (fun e => hb (e ▸ hv.2))]
        congr 2
        ext h
        simp only [mem_filter]
        constructor
        · rintro ⟨hh, -, e⟩
          exact ⟨hh, e⟩
        · rintro ⟨hh, e⟩
          exact ⟨hh, e ▸ hv.2, e⟩
      rw [sum_congr rfl this, sum_const, smul_eq_mul, card_erase_of_mem ha]
  have htot : (n - 2) * ∑ h ∈ C, #(S.filter fun w => h w ∈ S) =
      (n - 2) * #C + (#S - 2) * ((#S - 1) * #C) := by
    have e1 : ∑ h ∈ C, #(S.filter fun w => h w ∈ S) =
        ∑ w ∈ S, #(C.filter fun h => h w ∈ S) := by
      simp only [card_filter]
      exact sum_comm
    rw [e1, mul_sum, sum_congr rfl hcount]
    rw [← add_sum_erase S _ ha, ite_eq_of_pos rfl]
    have ha'e : a' ∈ S.erase a := mem_erase.mpr ⟨Ne.symm haa, ha'⟩
    rw [← add_sum_erase (S.erase a) _ ha'e, ite_eq_of_neg (Ne.symm haa), ite_eq_of_pos rfl,
      zero_add]
    have : ∀ w ∈ (S.erase a).erase a',
        (if w = a then (n - 2) * #C else if w = a' then 0 else (#S - 1) * #C) =
          (#S - 1) * #C := by
      intro w hw
      simp only [mem_erase] at hw
      rw [ite_eq_of_neg hw.2.1, ite_eq_of_neg hw.1]
    rw [sum_congr rfl this, sum_const, smul_eq_mul, card_erase_of_mem ha'e,
      card_erase_of_mem ha]
    congr 2
  -- `C` is nonempty, by `2`-transitivity
  have h3 : 3 ≤ Nat.card α := by
    rw [Nat.card_eq_fintype_card]
    have : ({a, a', b} : Finset α) ⊆ univ := subset_univ _
    have hc := card_le_card this
    rw [card_univ, card_insert_of_notMem (by simp [haa, hab]),
      card_insert_of_notMem (by simp [ha'b]), card_singleton] at hc
    exact hc
  obtain ⟨c, hc⟩ : ∃ c, c ≠ a ∧ c ≠ a' := by
    by_contra hcon
    push Not at hcon
    have hsub : (univ : Finset α) ⊆ {a, a'} := fun c _ => by
      by_cases hca : c = a
      · simp [hca]
      · simp [hcon c hca]
    have := card_le_card hsub
    rw [card_univ, card_insert_of_notMem (by simp [haa]), card_singleton] at this
    rw [Nat.card_eq_fintype_card] at h3
    omega
  obtain ⟨c', hc'⟩ : ∃ c', c' ≠ a ∧ c' ≠ b := by
    by_contra hcon
    push Not at hcon
    have hsub : (univ : Finset α) ⊆ {a, b} := fun c _ => by
      by_cases hca : c = a
      · simp [hca]
      · simp [hcon c hca]
    have := card_le_card hsub
    rw [card_univ, card_insert_of_notMem (by simp [hab]), card_singleton] at this
    rw [Nat.card_eq_fintype_card] at h3
    omega
  obtain ⟨g₀, hg₀G, hg₀a, hg₀a', -⟩ :=
    exists_mem_map3 G haa (Ne.symm hc.1) (Ne.symm hc.2) hab (Ne.symm hc'.1) (Ne.symm hc'.2)
  have hCne : C.Nonempty := ⟨g₀, (hmemC g₀).mpr ⟨hg₀G, hg₀a, hg₀a'⟩⟩
  -- some `h ∈ C` is at most the average
  by_contra hcon
  push Not at hcon
  have hlt : ∀ h ∈ C, (n - 2) + (#S - 1) * (#S - 2) <
      (n - 2) * #(S.filter fun w => h w ∈ S) := fun h hh => by
    rw [hmemC] at hh
    exact hcon h hh.1 hh.2.1 hh.2.2
  have hsumlt := sum_lt_sum_of_nonempty hCne hlt
  rw [sum_const, smul_eq_mul, ← mul_sum, htot] at hsumlt
  have e : #C * ((n - 2) + (#S - 1) * (#S - 2)) = (n - 2) * #C + (#S - 2) * ((#S - 1) * #C) := by
    ring
  omega

/-- The arithmetic of the reduction. -/
theorem three_mul_lt (n s k : ℕ) (hs : 2 ≤ s) (h6 : 6 * s ≤ n) (hk : 2 ≤ k)
    (h : (n - 2) * k ≤ (n - 2) + (s - 1) * (s - 2)) : 3 * k < s := by
  obtain ⟨u, rfl⟩ : ∃ u, s = u + 2 := ⟨s - 2, by omega⟩
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 2 := ⟨n - 2, by omega⟩
  simp only [Nat.add_sub_cancel, show u + 2 - 1 = u + 1 by omega] at h
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hN : 6 * u + 10 ≤ N := by omega
  have h' : N * j ≤ (u + 1) * u := by nlinarith
  by_contra hc
  push Not at hc
  have hj : u ≤ 3 * j + 1 := by omega
  have h1 : N ≤ (u + 1) * u := by nlinarith
  nlinarith

/-- **Small supports give `3`-cycles:** a `3`-transitive `G ≤ Sym(Ω)` containing `x ≠ 1` with
`6 |supp x| ≤ |Ω|` contains a `3`-cycle. -/
theorem exists_isThreeCycle_mem (G : Subgroup (Perm α)) [IsMultiplyPretransitive G α 3] :
    ∀ s, ∀ x ∈ G, x ≠ 1 → #x.support = s → 6 * s ≤ Fintype.card α →
      ∃ g ∈ G, g.IsThreeCycle := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
  intro x hxG hx1 hs h6
  set S := x.support with hS
  have hs2 : 2 ≤ s := hs ▸ two_le_card_support_of_ne_one hx1
  obtain ⟨a, ha⟩ : S.Nonempty := card_pos.mp (by omega)
  set a' := x a with ha'def
  have ha' : a' ∈ S := apply_mem_support.mpr ha
  have haa : a ≠ a' := fun e => (mem_support.mp ha) e.symm
  obtain ⟨b, hb⟩ : ∃ b, b ∉ S := by
    by_contra hcon
    push Not at hcon
    have : (univ : Finset α) ⊆ S := fun b _ => hcon b
    have := card_le_card this
    rw [card_univ] at this
    omega
  obtain ⟨h, hG, hha, hha', hle⟩ := exists_mem_card_inter_le G ha ha' hb haa
  set y := h * x * h⁻¹ with hy
  have hyG : y ∈ G := G.mul_mem (G.mul_mem hG hxG) (G.inv_mem hG)
  have hsy : y.support = S.map h.toEmbedding := support_conj
  have hya : y a = b := by
    have : h⁻¹ a = a := by rw [Perm.inv_eq_iff_eq, hha]
    simp [hy, Perm.mul_apply, this, ← ha'def, hha']
  have hxb : x b = b := notMem_support.mp hb
  have hne : ⁅x, y⁆ ≠ 1 := by
    rw [Ne, commutatorElement_eq_one_iff_mul_comm]
    intro e
    have := congrArg (fun σ : Perm α => σ a) e
    simp only [Perm.mul_apply, hya, hxb] at this
    exact haa (y.injective (this.symm.trans hya.symm)).symm |>.elim
  have hcG : ⁅x, y⁆ ∈ G := by
    rw [commutatorElement_def]
    exact G.mul_mem (G.mul_mem (G.mul_mem hxG hyG) (G.inv_mem hxG)) (G.inv_mem hyG)
  set k := #(x.support ∩ y.support) with hk
  have hk' : k = #(S.filter fun w => h w ∈ S) := by rw [hk, hsy, card_inter_map_eq]
  have hk1 : 1 ≤ k := by
    rw [hk]
    refine card_pos.mpr ⟨a, mem_inter.mpr ⟨ha, mem_support.mpr ?_⟩⟩
    rw [hya]
    exact fun e => hb (e ▸ ha)
  rcases (show k = 1 ∨ 2 ≤ k by omega) with h1 | h2
  · exact ⟨_, hcG, isThreeCycle_commutatorElement (hk ▸ h1) hne⟩
  · have h3 : 3 * k < s := by
      rw [hk'] at h2 ⊢
      rw [hs] at hle
      exact three_mul_lt _ _ _ hs2 h6 h2 hle
    have hc := card_support_commutatorElement_le x y
    exact ih _ (by omega) _ hcG hne rfl (by omega)

/-- **Jordan via small supports:** a `3`-transitive `G ≤ Sym(Ω)` containing `x ≠ 1` with
`6 |supp x| ≤ |Ω|` contains `Alt(Ω)`. -/
theorem alternatingGroup_le_of_support_le (G : Subgroup (Perm α))
    [IsMultiplyPretransitive G α 3] {x : Perm α} (hx : x ∈ G) (h1 : x ≠ 1)
    (h6 : 6 * #x.support ≤ Fintype.card α) : alternatingGroup α ≤ G := by
  obtain ⟨g, hgG, hg⟩ := exists_isThreeCycle_mem G _ x hx h1 rfl h6
  have h3 : 3 ≤ Nat.card α := by
    rw [Nat.card_eq_fintype_card]
    have := hg.card_support
    have := card_le_univ g.support
    omega
  have : IsMultiplyPretransitive G α 2 := isMultiplyPretransitive_of_le (by norm_num) h3
  exact alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem
    (isPreprimitive_of_is_two_pretransitive this) hg hgG

end GraphIso.Wielandt
