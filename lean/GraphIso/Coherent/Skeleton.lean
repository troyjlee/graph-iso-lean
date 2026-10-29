module

public import GraphIso.Coherent.Basic

/-!
# Individualized skeletons

For a `k`-ary structure `c` and a list `x` of points, `skel1 c x` and `skel2 c x` are the 1- and
2-skeletons of the structure individualized at `x` (Helfgott's `X_x^{(1)}` and `X_x^{(2)}`).

* `skel2 c x u u = skel1 c x u` (`skel2_self`) and `skel1 c (x ++ [z]) u = skel2 c x z u`
  (`skel1_append`).
* **`isCoherent2_skel2`** (Helfgott, Exercises 2.11 and 2.13): if `c` is a coherent
  configuration and `x` has at most `k − 2` points, the individualized 2-skeleton is a classical
  coherent configuration. A tuple agreeing with `x` on the first positions, composed with the
  map of positions `selPos`, is a tuple `(x, a, b, …, b)` (`comp_selPos`), so the configuration
  axioms of `c` give those of the 2-skeleton; its intersection numbers are counts of predicates
  on the colour vectors of `c` (`IsCoherent.card_filter_pred`).
* **`isCoherent2_restrict`** (Exercise 2.12): the restriction of a classical coherent
  configuration to a vertex colour class is again one.
* Individualizing is canonical (`skel1_relabel`, `skel2_relabel`).
-/

@[expose] public section

namespace GraphIso.Coherent

open Finset Function

variable {V : Type*} [Fintype V] {k : ℕ}

/-- The map of positions fixing the positions below `L` and sending position `L` to `p` and the
positions above `L` to `q`. -/
def selPos (L : ℕ) (p q : Fin k) : Fin k → Fin k :=
  fun i => if i.val < L then i else if i.val = L then p else q

omit [Fintype V] in
/-- A tuple agreeing with `x` on the first positions, composed with `selPos`, is the tuple
`(x, w p, w q, …, w q)`. -/
theorem comp_selPos {x : List V} {w : Fin k → V}
    (hw : ∀ (i : Fin k) (h : i.val < x.length), w i = x[i.val]) (p q : Fin k) :
    w ∘ selPos x.length p q = pad2 k x (w p) (w q) := by
  funext i
  simp only [comp_apply, selPos, pad2]
  by_cases h : i.val < x.length
  · simp only [h, ↓reduceIte, ↓reduceDIte]
    exact hw i h
  · by_cases h' : i.val = x.length <;> simp [h, h']

omit [Fintype V] in
theorem pad2_lt (x : List V) (u v : V) (i : Fin k) (h : i.val < x.length) :
    pad2 k x u v i = x[i.val] := by
  simp [pad2, h]

omit [Fintype V] in
/-- The vertex colour of the individualized 2-skeleton is the individualized 1-skeleton. -/
theorem skel2_self (c : (Fin k → V) → ℕ) (x : List V) (u : V) :
    skel2 c x u u = skel1 c x u := by
  unfold skel2 skel1
  congr 1
  funext i
  simp only [pad1, pad2]
  split_ifs <;> rfl

omit [Fintype V] in
/-- Individualizing one more point: `c (x, z, u, …, u)`. -/
theorem skel1_append (c : (Fin k → V) → ℕ) {x : List V} (hx : x.length + 2 ≤ k) (z u : V) :
    skel1 c (x ++ [z]) u = skel2 c x z u := by
  have _ := hx
  unfold skel1 skel2
  congr 1
  funext i
  simp only [pad1, pad2, List.length_append, List.length_singleton]
  by_cases h : i.val < x.length
  · have h1 : i.val < x.length + 1 := by omega
    simp [h, h1, List.getElem_append_left h]
  · by_cases h' : i.val = x.length
    · simp [h']
    · have h1 : ¬ i.val < x.length + 1 := by omega
      simp [h, h', h1]

/-- **The individualized 2-skeleton of a `k`-ary coherent configuration is a classical coherent
configuration** (Helfgott, Exercises 2.11 and 2.13). -/
theorem isCoherent2_skel2 {c : (Fin k → V) → ℕ} (hc : IsCoherent c) {x : List V}
    (hx : x.length + 2 ≤ k) : IsCoherent2 (skel2 c x) := by
  classical
  let pL : Fin k := ⟨x.length, by omega⟩
  let pL1 : Fin k := ⟨x.length + 1, by omega⟩
  have h0 : ∀ u v, pad2 k x u v pL = u := fun u v => by simp [pad2, pL]
  have h1 : ∀ u v, pad2 k x u v pL1 = v := fun u v => by simp [pad2, pL1]
  have hsel : ∀ u v p q, pad2 k x u v ∘ selPos x.length p q =
      pad2 k x (pad2 k x u v p) (pad2 k x u v q) := fun u v p q =>
    comp_selPos (pad2_lt x u v) p q
  refine ⟨fun u v u' v' h => ?_, fun u v u' v' h r s => ?_⟩
  · unfold skel2 at h ⊢
    refine ⟨?_, ?_, ?_, ?_⟩
    · have := hc.config.eq_iff h pL pL1
      simpa only [h0, h1] using this
    · have := hc.config.comp h (selPos x.length pL1 pL)
      simpa only [hsel, h0, h1] using this
    · have := hc.config.comp h (selPos x.length pL pL)
      simpa only [hsel, h0] using this
    · have := hc.config.comp h (selPos x.length pL1 pL1)
      simpa only [hsel, h1] using this
  · -- the two colours of the count, as colours of tuples obtained from `pad2 k x a d`
    have hupd0 : ∀ a d z, pad2 k x z d = update (pad2 k x a d) pL z := fun a d z => by
      funext i
      by_cases hi : i = pL
      · subst hi
        rw [update_self, h0]
      · rw [update_of_ne hi]
        have hi' : i.val ≠ x.length := fun e => hi (Fin.ext e)
        simp [pad2, hi']
    have hupd1 : ∀ a d z, pad2 k x a z = update (pad2 k x a d) pL1 z ∘ selPos x.length pL pL1 :=
      fun a d z => by
        have hne : pL ≠ pL1 := fun e => by simpa [pL, pL1] using congrArg Fin.val e
        rw [comp_selPos (fun i hi => ?_) pL pL1, update_of_ne hne, update_self, h0]
        have hi' : i ≠ pL1 := fun e => by
          have := congrArg Fin.val e
          simp [pL1] at this
          omega
        rw [update_of_ne hi', pad2_lt x a d i hi]
    let P : (Fin k → ℕ) → Prop := fun w =>
      (∃ t, c t = w pL1 ∧ c (t ∘ selPos x.length pL pL1) = r) ∧ w pL = s
    have key : ∀ a d z, (skel2 c x a z = r ∧ skel2 c x z d = s) ↔
        P (cvec c (pad2 k x a d) z) := fun a d z => by
      simp only [skel2, P, cvec]
      rw [hupd0 a d z, hupd1 a d z]
      constructor
      · rintro ⟨h1', h2'⟩
        exact ⟨⟨_, rfl, h1'⟩, h2'⟩
      · rintro ⟨⟨t, ht, ht'⟩, h2'⟩
        refine ⟨?_, h2'⟩
        rw [← hc.config.comp ht]
        exact ht'
    rw [filter_congr (fun z _ => key u v z), filter_congr (fun z _ => key u' v' z)]
    exact hc.card_filter_pred h P

/-- **The restriction of a classical coherent configuration to a vertex colour class is a
classical coherent configuration** (Helfgott, Exercise 2.12). -/
theorem isCoherent2_restrict {c : V → V → ℕ} (hc : IsCoherent2 c) (κ : ℕ) :
    IsCoherent2 (fun u v : {w // c w w = κ} => c u v) := by
  classical
  refine ⟨fun x y x' y' h => ?_, fun x y x' y' h r s => ?_⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hc.config h
    exact ⟨by rw [Subtype.ext_iff, Subtype.ext_iff]; exact h1, h2, h3, h4⟩
  · -- a count over the class is a count over `V` with the extra condition `c z z = κ`, which
    -- the colour `c a z` determines
    have hsub : ∀ a b : {w // c w w = κ},
        (univ.filter fun z : {w // c w w = κ} => c a z = r ∧ c z b = s).card =
          (univ.filter fun z : V => c a z = r ∧ c z b = s ∧ c z z = κ).card := by
      intro a b
      refine card_bij (fun z _ => z.1) ?_ ?_ ?_
      · intro z hz
        simp only [mem_filter, mem_univ, true_and] at hz ⊢
        exact ⟨hz.1, hz.2, z.2⟩
      · intro z₁ _ z₂ _ e
        exact Subtype.ext e
      · intro z hz
        simp only [mem_filter, mem_univ, true_and] at hz
        exact ⟨⟨z, hz.2.2⟩, by simp [hz.1, hz.2.1], rfl⟩
    let Q : ℕ → ℕ → Prop := fun a b =>
      a = r ∧ b = s ∧ ∃ x₀ z₀, c x₀ z₀ = a ∧ c z₀ z₀ = κ
    have key : ∀ a b z : V, (c a z = r ∧ c z b = s ∧ c z z = κ) ↔ Q (c a z) (c z b) := by
      intro a b z
      simp only [Q]
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨h1, h2, a, z, rfl, h3⟩
      · rintro ⟨h1, h2, x₀, z₀, e, h3⟩
        exact ⟨h1, h2, by rw [← (hc.config e).2.2.2, h3]⟩
    rw [hsub, hsub, filter_congr (fun z _ => key x y z), filter_congr (fun z _ => key x' y' z)]
    exact hc.card_filter_pred h Q

omit [Fintype V] in
/-- Individualizing is canonical: relabelling the structure and the individualized points by
`π` leaves the individualized vertex colouring unchanged. -/
theorem skel1_relabel [DecidableEq V] (c : (Fin k → V) → ℕ) (π : Equiv.Perm V) (x : List V)
    (u : V) : skel1 (fun y => c (⇑π.symm ∘ y)) (x.map π) (π u) = skel1 c x u := by
  show c (⇑π.symm ∘ pad1 k (x.map π) (π u)) = c (pad1 k x u)
  congr 1
  funext i
  simp only [comp_apply, pad1, List.length_map]
  by_cases h : i.val < x.length <;> simp [h]

omit [Fintype V] in
/-- Individualizing is canonical for the 2-skeleton. -/
theorem skel2_relabel [DecidableEq V] (c : (Fin k → V) → ℕ) (π : Equiv.Perm V) (x : List V)
    (u v : V) : skel2 (fun y => c (⇑π.symm ∘ y)) (x.map π) (π u) (π v) = skel2 c x u v := by
  show c (⇑π.symm ∘ pad2 k (x.map π) (π u) (π v)) = c (pad2 k x u v)
  congr 1
  funext i
  simp only [comp_apply, pad2, List.length_map]
  by_cases h : i.val < x.length
  · simp [h]
  · by_cases h' : i.val = x.length <;> simp [h, h']

end GraphIso.Coherent
