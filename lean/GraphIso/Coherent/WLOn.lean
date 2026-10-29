module

public import GraphIso.Coherent.WL

/-!
# Weisfeiler–Leman on any finite type

`wlOn k c` is the `k`-ary Weisfeiler–Leman refinement `wl` (milestone 10) of a structure
`c : (Fin k → V) → ℕ` on an arbitrary finite type `V`. It is `wl` transported along an
enumeration `e : V ≃ Fin |V|`. By `wl_relabel` the result does not depend on `e`
(`wl_along_indep`), so the definition goes through `Fintype.truncEquivFin` and `Trunc.lift` and
is computable (`wlOn_eq` evaluates it at any enumeration, `wlOn_eq'` at any `V ≃ Fin n`).

Its properties follow from milestone 10: it is a coherent configuration refining `c`
(`wlOn_isCoherent`, `wlOn_refines`) with the same twins (`isTwin_wlOn_iff`), and it is natural
under every equivalence `V ≃ W` (`wlOn_natural`), so it is canonical. The transport lemmas
`IsCoherent.comp_equiv` and `isTwin_comp_equiv_iff` pull coherence and twins back along an
equivalence.
-/

@[expose] public section

namespace GraphIso.Coherent

open Finset Function

section Transport

variable {k : ℕ} {V U : Type*}

/-- `wl` along an enumeration does not depend on the enumeration. -/
theorem wl_along_indep (c : (Fin k → V) → ℕ) {n : ℕ} (e e' : V ≃ Fin n) :
    (fun x => (wl k n (fun y => c (⇑e.symm ∘ y))).1 (⇑e ∘ x)) =
      fun x => (wl k n (fun y => c (⇑e'.symm ∘ y))).1 (⇑e' ∘ x) := by
  funext x
  have h1 : (fun y => c (⇑e'.symm ∘ y)) =
      fun y => (fun y => c (⇑e.symm ∘ y)) (⇑(e.symm.trans e')⁻¹ ∘ y) := by
    funext y
    congr 1
    funext i
    simp [Equiv.Perm.inv_def]
  rw [h1, wl_relabel (fun y => c (⇑e.symm ∘ y)) (e.symm.trans e')]
  refine congrArg _ ?_
  funext i
  simp [Equiv.Perm.inv_def]

theorem card_filter_comp_equiv [Fintype V] [Fintype U] (e : V ≃ U) (p : U → Prop)
    [DecidablePred p] : (univ.filter fun z : V => p (e z)).card = (univ.filter p).card := by
  have h : (univ.filter p) = (univ.filter fun z : V => p (e z)).map e.toEmbedding := by
    ext u
    simp only [mem_filter, mem_univ, true_and, mem_map, Equiv.coe_toEmbedding]
    exact ⟨fun hu => ⟨e.symm u, by simpa using hu, by simp⟩, fun ⟨z, hz, hzu⟩ => hzu ▸ hz⟩
  rw [h, card_map]

/-- Coherence pulls back along an equivalence. -/
theorem IsCoherent.comp_equiv [Fintype V] [Fintype U] {c : (Fin k → U) → ℕ}
    (hc : IsCoherent c) (e : V ≃ U) : IsCoherent fun x : Fin k → V => c (⇑e ∘ x) := by
  refine ⟨fun x y h => ⟨fun i j => ?_, fun τ => ?_⟩, fun x y h r => ?_⟩
  · have := (hc.1 _ _ h).1 i j
    simp only [comp_apply, e.injective.eq_iff] at this
    exact this
  · exact (hc.1 _ _ h).2 τ
  · have key : ∀ (w : Fin k → V) (z : V) (j : Fin k),
        c (⇑e ∘ update w j z) = c (update (⇑e ∘ w) j (e z)) := fun w z j => by
      rw [comp_update]
    simp only [key]
    rw [card_filter_comp_equiv e (fun u => ∀ j, c (update (⇑e ∘ x) j u) = r j),
      card_filter_comp_equiv e (fun u => ∀ j, c (update (⇑e ∘ y) j u) = r j)]
    exact hc.2 _ _ h r

theorem equiv_swap_apply [DecidableEq V] [DecidableEq U] (e : V ≃ U) (u v z : V) :
    e (Equiv.swap u v z) = Equiv.swap (e u) (e v) (e z) := by
  simp only [Equiv.swap_apply_def, e.injective.eq_iff]
  split_ifs <;> rfl

/-- Twins pull back along an equivalence. -/
theorem isTwin_comp_equiv_iff [DecidableEq V] [DecidableEq U] (c : (Fin k → U) → ℕ)
    (e : V ≃ U) (u v : V) :
    IsTwin (fun x : Fin k → V => c (⇑e ∘ x)) u v ↔ IsTwin c (e u) (e v) := by
  have key : ∀ x : Fin k → V,
      ⇑e ∘ (⇑(Equiv.swap u v) ∘ x) = ⇑(Equiv.swap (e u) (e v)) ∘ (⇑e ∘ x) := fun x => by
    funext i
    exact equiv_swap_apply e u v (x i)
  unfold IsTwin
  simp only [key]
  constructor
  · intro h y
    have := h (⇑e.symm ∘ y)
    have hy : ⇑e ∘ (⇑e.symm ∘ y) = y := by
      funext i
      simp
    rwa [hy] at this
  · intro h x
    exact h _

end Transport

variable {V : Type*} [Fintype V] [DecidableEq V] (k : ℕ)

/-- **Weisfeiler–Leman on a finite type**: `wl` along any enumeration of `V`. -/
def wlOn (c : (Fin k → V) → ℕ) : (Fin k → V) → ℕ :=
  Trunc.lift (fun e : V ≃ Fin (Fintype.card V) =>
      fun x => (wl k (Fintype.card V) (fun y => c (⇑e.symm ∘ y))).1 (⇑e ∘ x))
    (fun e e' => wl_along_indep c e e') (Fintype.truncEquivFin V)

variable {k}

/-- `wlOn` evaluated at an enumeration. -/
theorem wlOn_eq (c : (Fin k → V) → ℕ) (e : V ≃ Fin (Fintype.card V)) :
    wlOn k c = fun x => (wl k (Fintype.card V) (fun y => c (⇑e.symm ∘ y))).1 (⇑e ∘ x) := by
  unfold wlOn
  rw [show Fintype.truncEquivFin V = Trunc.mk e from Trunc.eq _ _]
  rfl

/-- `wlOn` evaluated at any equivalence with some `Fin n`. -/
theorem wlOn_eq' (c : (Fin k → V) → ℕ) {n : ℕ} (e : V ≃ Fin n) :
    wlOn k c = fun x => (wl k n (fun y => c (⇑e.symm ∘ y))).1 (⇑e ∘ x) := by
  have h : Fintype.card V = n := by simpa using Fintype.card_congr e
  subst h
  exact wlOn_eq c e

omit [Fintype V] [DecidableEq V] in
theorem symm_comp_comp {W : Type*} (e : V ≃ W) (x : Fin k → V) : ⇑e.symm ∘ (⇑e ∘ x) = x := by
  funext i
  simp

/-- **`wlOn` is a coherent configuration.** -/
theorem wlOn_isCoherent (c : (Fin k → V) → ℕ) : IsCoherent (wlOn k c) := by
  let e := Fintype.equivFin V
  rw [wlOn_eq c e]
  exact (wl_isCoherent _).comp_equiv e

/-- **`wlOn` refines its input.** -/
theorem wlOn_refines (c : (Fin k → V) → ℕ) {x y : Fin k → V} (h : wlOn k c x = wlOn k c y) :
    c x = c y := by
  let e := Fintype.equivFin V
  rw [wlOn_eq c e] at h
  have := wl_refines _ h
  simpa only [symm_comp_comp] using this

/-- **`wlOn` has the twins of its input.** -/
theorem isTwin_wlOn_iff (c : (Fin k → V) → ℕ) (u v : V) :
    IsTwin (wlOn k c) u v ↔ IsTwin c u v := by
  let e := Fintype.equivFin V
  rw [wlOn_eq c e, isTwin_comp_equiv_iff, isTwin_wl_iff, isTwin_comp_equiv_iff c e.symm]
  simp only [Equiv.symm_apply_apply]

/-- **Canonicity: `wlOn` is natural under equivalences.** Pulling a structure back along
`e : V ≃ W` pulls its refinement back, colour names included. -/
theorem wlOn_natural {W : Type*} [Fintype W] [DecidableEq W] (e : V ≃ W)
    (c : (Fin k → W) → ℕ) :
    wlOn k (fun x => c (⇑e ∘ x)) = fun x => wlOn k c (⇑e ∘ x) := by
  let f := Fintype.equivFin W
  rw [wlOn_eq' _ (e.trans f), wlOn_eq c f]
  funext x
  have h1 : (fun y => (fun x => c (⇑e ∘ x)) (⇑(e.trans f).symm ∘ y)) =
      fun y => c (⇑f.symm ∘ y) := by
    funext y
    show c (⇑e ∘ (⇑(e.trans f).symm ∘ y)) = c (⇑f.symm ∘ y)
    congr 1
    funext i
    simp
  rw [h1]
  rfl

end GraphIso.Coherent
