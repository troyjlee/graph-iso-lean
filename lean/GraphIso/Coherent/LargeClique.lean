module

public import GraphIso.Coherent.Basic
public import GraphIso.Coherent.Fisher

/-!
# The large clique lemma

**The large clique lemma** (Helfgott, Lemma 5.2): in a classical coherent configuration, a
vertex colour class `C` with `2 |C| > |V|` on which all pairs of distinct points have one colour
consists of pairwise twins (`isTwin2_of_large_clique`). Helfgott states `|C| ≥ |V|/2`; his
proof uses the strict inequality.

* **Every outside point sees `C` in one colour** (`eq_of_large_clique`). Suppose `x ∉ C` has
  `c x u ≠ c x v` with `u, v ∈ C`; call `c x u` azure. The sets `A_b = {y ∈ C | c b y = azure}`,
  for `b` in the colour class `B` of `x`, form a block design on `C`: by coherence
  (`IsCoherent2.card_filter_pred`) every point of `C` lies in the same number `r` of blocks
  (the number of `z` with `c z y = azure`, which forces `c z z = c x x`), and every pair of
  distinct points in the same number `λ` (using the transposed colour `c u x` and that `C` is a
  clique). The block `A_x` contains `u` but not `v`, so `λ < r`. Fisher's inequality gives
  `|C| ≤ |B|`, but `B` and `C` are disjoint and `2 |C| > |V|`.
* **Twins.** The transposition `(u v)` then preserves every colour: pairs inside `C` by the
  clique and the common diagonal colour, pairs with an outside point by the first step and the
  configuration axioms (`c w u` determines `c u w`).
-/

@[expose] public section

namespace GraphIso.Coherent

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- Counting the elements of a subtype with a property. -/
theorem card_filter_subtype {q : V → Prop} [DecidablePred q] (p : V → Prop) [DecidablePred p] :
    (univ.filter fun b : {w // q w} => p b.1).card = (univ.filter fun w => q w ∧ p w).card := by
  rw [← card_map (Function.Embedding.subtype q)]
  congr 1
  ext w
  simp [and_comm]

/-- **Every point outside a large clique class sees the class in one colour.** -/
theorem eq_of_large_clique {c : V → V → ℕ} (hc : IsCoherent2 c) {κ : ℕ}
    (hC : Fintype.card V < 2 * (univ.filter fun x => c x x = κ).card)
    (hcl : IsClique c (univ.filter fun x => c x x = κ)) {x u v : V} (hx : c x x ≠ κ)
    (hu : c u u = κ) (hv : c v v = κ) : c x u = c x v := by
  by_contra hne
  have huv : u ≠ v := fun h => hne (by rw [h])
  set az := c x u with haz
  -- the transposed colour
  have htr : ∀ y z, c z y = az ↔ c y z = c u x := fun y z =>
    ⟨fun h => (hc.config h).2.1, fun h => (hc.config h).2.1⟩
  -- a point `z` with `c z y = azure` has the colour of `x`
  have hdiag : ∀ y z, c z y = az → c z z = c x x := fun y z h => (hc.config h).2.2.1
  -- the design: points `C`, blocks the class of `x`
  let A : {b // c b b = c x x} → Finset {w // c w w = κ} :=
    fun b => univ.filter fun y => c b.1 y.1 = az
  set R := (univ.filter fun z => c z u = az).card
  set L := (univ.filter fun z => c z u = az ∧ c z v = az).card
  have hr : ∀ y : {w // c w w = κ}, (univ.filter fun b => y ∈ A b).card = R := by
    intro y
    have e1 : (univ.filter fun b : {b // c b b = c x x} => y ∈ A b).card =
        (univ.filter fun z => c z y.1 = az).card := by
      simp only [A, mem_filter, mem_univ, true_and]
      rw [card_filter_subtype (q := fun b => c b b = c x x) (fun z => c z y.1 = az)]
      congr 1
      ext z
      simp only [mem_filter, mem_univ, true_and]
      exact ⟨fun h => h.2, fun h => ⟨hdiag _ _ h, h⟩⟩
    rw [e1]
    have := hc.card_filter_pred (x := y.1) (y := y.1) (x' := u) (y' := u) (by rw [y.2, hu])
      (fun _ b => b = az)
    simpa using this
  have hl : ∀ y y' : {w // c w w = κ}, y ≠ y' →
      (univ.filter fun b => y ∈ A b ∧ y' ∈ A b).card = L := by
    intro y y' hyy
    have hne' : y.1 ≠ y'.1 := fun h => hyy (Subtype.ext h)
    have e1 : (univ.filter fun b : {b // c b b = c x x} => y ∈ A b ∧ y' ∈ A b).card =
        (univ.filter fun z => c y.1 z = c u x ∧ c z y'.1 = az).card := by
      simp only [A, mem_filter, mem_univ, true_and]
      rw [card_filter_subtype (q := fun b => c b b = c x x)
        (fun z => c z y.1 = az ∧ c z y'.1 = az)]
      congr 1
      ext z
      simp only [mem_filter, mem_univ, true_and]
      rw [← htr]
      exact ⟨fun h => h.2, fun h => ⟨hdiag _ _ h.1, h⟩⟩
    have e2 : L = (univ.filter fun z => c u z = c u x ∧ c z v = az).card := by
      simp only [L]
      congr 1
      ext z
      simp only [mem_filter, mem_univ, true_and]
      rw [← htr]
    rw [e1, e2]
    have hcol : c y.1 y'.1 = c u v :=
      hcl _ (by simpa using y.2) _ (by simpa using y'.2) _ (by simpa using hu) _
        (by simpa using hv) hne' huv
    exact hc.card_filter_pred hcol (fun a b => a = c u x ∧ b = az)
  have hlr : L < R := by
    refine card_lt_card ⟨fun z hz => ?_, fun hsub => ?_⟩
    · simp only [mem_filter, mem_univ, true_and] at hz ⊢
      exact hz.1
    · have hxm : x ∈ univ.filter fun z => c z u = az := by simp [haz]
      have := (mem_filter.1 (hsub hxm)).2.2
      exact hne this.symm
  have hfish := fisher_inequality A hr hl hlr
  rw [Fintype.card_subtype, Fintype.card_subtype] at hfish
  have hdisj : Disjoint (univ.filter fun w => c w w = κ) (univ.filter fun w => c w w = c x x) := by
    rw [disjoint_filter]
    intro w _ h1 h2
    exact hx (h2 ▸ h1)
  have hun := card_union_of_disjoint hdisj
  have hle := card_le_univ ((univ.filter fun w => c w w = κ) ∪
    (univ.filter fun w => c w w = c x x))
  omega

/-- **The large clique lemma** (Helfgott, Lemma 5.2): in a classical coherent configuration, a
vertex colour class `C` with `2 |C| > |V|` on which all pairs of distinct points have one colour
consists of pairwise twins. -/
theorem isTwin2_of_large_clique {c : V → V → ℕ} (hc : IsCoherent2 c) {κ : ℕ}
    (hC : Fintype.card V < 2 * (univ.filter fun x => c x x = κ).card)
    (hcl : IsClique c (univ.filter fun x => c x x = κ)) {u v : V} (hu : c u u = κ)
    (hv : c v v = κ) : IsTwin2 c u v := by
  intro a b
  by_cases huv : u = v
  · subst huv
    simp
  have hmem : ∀ {w}, c w w = κ → w ∈ univ.filter fun x => c x x = κ := fun h => by simpa using h
  have F1 : c u u = c v v := by rw [hu, hv]
  have F2 : c u v = c v u := hcl _ (hmem hu) _ (hmem hv) _ (hmem hv) _ (hmem hu) huv (Ne.symm huv)
  have F3 : ∀ w, w ≠ u → w ≠ v → c w u = c w v := by
    intro w hwu hwv
    by_cases hw : c w w = κ
    · exact hcl _ (hmem hw) _ (hmem hu) _ (hmem hw) _ (hmem hv) hwu hwv
    · exact eq_of_large_clique hc hC hcl hw hu hv
  have F4 : ∀ w, w ≠ u → w ≠ v → c u w = c v w := fun w hwu hwv =>
    (hc.config (F3 w hwu hwv)).2.1
  by_cases hau : a = u
  · subst hau
    rw [Equiv.swap_apply_left]
    by_cases hbu : b = a
    · subst hbu
      rw [Equiv.swap_apply_left]
      exact F1.symm
    by_cases hbv : b = v
    · subst hbv
      rw [Equiv.swap_apply_right]
      exact F2.symm
    rw [Equiv.swap_apply_of_ne_of_ne hbu hbv]
    exact (F4 b hbu hbv).symm
  by_cases hav : a = v
  · subst hav
    rw [Equiv.swap_apply_right]
    by_cases hbu : b = u
    · subst hbu
      rw [Equiv.swap_apply_left]
      exact F2
    by_cases hbv : b = a
    · subst hbv
      rw [Equiv.swap_apply_right]
      exact F1
    rw [Equiv.swap_apply_of_ne_of_ne hbu hbv]
    exact F4 b hbu hbv
  rw [Equiv.swap_apply_of_ne_of_ne hau hav]
  by_cases hbu : b = u
  · subst hbu
    rw [Equiv.swap_apply_left]
    exact (F3 a hau hav).symm
  by_cases hbv : b = v
  · subst hbv
    rw [Equiv.swap_apply_right]
    exact F3 a hau hav
  rw [Equiv.swap_apply_of_ne_of_ne hbu hbv]

end GraphIso.Coherent
