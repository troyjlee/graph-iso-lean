module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Logic.Equiv.Defs

/-!
# Configurations and coherent configurations

Points are a finite type `V`; a `k`-ary partition structure is a colouring
`c : (Fin k → V) → ℕ` of the `k`-tuples (Helfgott, *Graph isomorphisms in quasi-polynomial
time*, §§2.3–2.4).

* `IsConfig c` (Def. 2.5): the colour of a tuple determines which of its entries are equal, and
  the colour of `x ∘ τ` for every map of positions `τ : Fin k → Fin k`.
* `IsCoherent c` (Def. 2.8): a configuration in which, for every vector of colours `r`, the
  number of points `z` with `c (update x j z) = r j` for all `j` depends only on `c x`.
* `IsCoherent2 c` (`c : V → V → ℕ`): classical coherent configurations, stated directly, with
  the intersection numbers `#{z | c x z = r ∧ c z y = s}`.
* `IsTwin c u v`, `IsTwin2 c u v`: the transposition `(u v)` preserves `c`. `IsClique c C`: all
  pairs of distinct points of `C` have one colour.
* `skel1 c x u = c (x, u, u, …, u)` and `skel2 c x u v = c (x, u, v, …, v)` (`x` a list of
  points): the 1- and 2-skeletons of the structure individualized at `x` (Helfgott's `X_x`).

Counting with arbitrary predicates on the colour vector depends only on the colour
(`IsCoherent.card_filter_pred`, `IsCoherent2.card_filter_pred`).
-/

@[expose] public section

namespace GraphIso.Coherent

open Finset Function

variable {V : Type*} [Fintype V] {k : ℕ}

/-- **A `k`-ary configuration** (Helfgott, Def. 2.5): the colour of a tuple determines which of
its entries are equal, and the colour of `x ∘ τ` for every map of positions `τ`. -/
def IsConfig (c : (Fin k → V) → ℕ) : Prop :=
  ∀ x y, c x = c y → (∀ i j, x i = x j ↔ y i = y j) ∧ ∀ τ : Fin k → Fin k, c (x ∘ τ) = c (y ∘ τ)

/-- **A `k`-ary coherent configuration** (Def. 2.8): a configuration in which the number of
points `z` with `c (update x j z) = r j` for all positions `j` depends only on the colour of
`x`, for every vector of colours `r`. -/
def IsCoherent (c : (Fin k → V) → ℕ) : Prop :=
  IsConfig c ∧ ∀ x y, c x = c y → ∀ r : Fin k → ℕ,
    (univ.filter fun z => ∀ j, c (update x j z) = r j).card =
      (univ.filter fun z => ∀ j, c (update y j z) = r j).card

/-- `u` and `v` are **twins**: the transposition `(u v)` preserves `c`. -/
def IsTwin [DecidableEq V] (c : (Fin k → V) → ℕ) (u v : V) : Prop :=
  ∀ x : Fin k → V, c (⇑(Equiv.swap u v) ∘ x) = c x

/-- **A classical coherent configuration** (`k = 2`): the colour of `(x, y)` determines whether
`x = y` and the colours of `(y, x)`, `(x, x)`, `(y, y)`, and the intersection numbers
`#{z | c x z = r ∧ c z y = s}` depend only on the colour of `(x, y)`. -/
def IsCoherent2 (c : V → V → ℕ) : Prop :=
  (∀ x y x' y', c x y = c x' y' →
    (x = y ↔ x' = y') ∧ c y x = c y' x' ∧ c x x = c x' x' ∧ c y y = c y' y') ∧
  ∀ x y x' y', c x y = c x' y' → ∀ r s,
    (univ.filter fun z => c x z = r ∧ c z y = s).card =
      (univ.filter fun z => c x' z = r ∧ c z y' = s).card

/-- `u` and `v` are twins of a classical structure. -/
def IsTwin2 [DecidableEq V] (c : V → V → ℕ) (u v : V) : Prop :=
  ∀ x y, c (Equiv.swap u v x) (Equiv.swap u v y) = c x y

/-- All pairs of distinct points of `C` have the same colour. -/
def IsClique (c : V → V → ℕ) (C : Finset V) : Prop :=
  ∀ u ∈ C, ∀ v ∈ C, ∀ u' ∈ C, ∀ v' ∈ C, u ≠ v → u' ≠ v' → c u v = c u' v'

/-! ### Individualization -/

variable (k) in
/-- The tuple `(x, u, u, …, u)`. -/
def pad1 (x : List V) (u : V) : Fin k → V :=
  fun i => if h : i.val < x.length then x[i.val] else u

variable (k) in
/-- The tuple `(x, u, v, …, v)`. -/
def pad2 (x : List V) (u v : V) : Fin k → V :=
  fun i => if h : i.val < x.length then x[i.val] else if i.val = x.length then u else v

/-- The vertex colouring of the structure individualized at `x`: `u ↦ c (x, u, …, u)`. -/
def skel1 (c : (Fin k → V) → ℕ) (x : List V) (u : V) : ℕ := c (pad1 k x u)

/-- The classical structure individualized at `x`: `(u, v) ↦ c (x, u, v, …, v)`. -/
def skel2 (c : (Fin k → V) → ℕ) (x : List V) (u v : V) : ℕ := c (pad2 k x u v)

/-- The class of `u` in the individualized vertex colouring. -/
def cls1 (c : (Fin k → V) → ℕ) (x : List V) (u : V) : Finset V :=
  univ.filter fun w => skel1 c x w = skel1 c x u

/-! ### Basic facts -/

omit [Fintype V] in
theorem IsConfig.comp {c : (Fin k → V) → ℕ} (hc : IsConfig c) {x y : Fin k → V}
    (h : c x = c y) (τ : Fin k → Fin k) : c (x ∘ τ) = c (y ∘ τ) :=
  (hc x y h).2 τ

omit [Fintype V] in
theorem IsConfig.eq_iff {c : (Fin k → V) → ℕ} (hc : IsConfig c) {x y : Fin k → V}
    (h : c x = c y) (i j : Fin k) : x i = x j ↔ y i = y j :=
  (hc x y h).1 i j

omit [Fintype V] in
/-- The colour of `x ∘ τ` is a function of the colour of `x`: membership of a colour is the
same for `x` and `y` of equal colour. -/
theorem IsConfig.comp_eq_iff {c : (Fin k → V) → ℕ} (hc : IsConfig c) {x y : Fin k → V}
    (h : c x = c y) (τ : Fin k → Fin k) (r : ℕ) : c (x ∘ τ) = r ↔ c (y ∘ τ) = r := by
  rw [hc.comp h τ]

/-- The colour vector of `x` at `z`: the colours of `x` with position `j` replaced by `z`. -/
def cvec (c : (Fin k → V) → ℕ) (x : Fin k → V) (z : V) : Fin k → ℕ :=
  fun j => c (update x j z)

theorem IsCoherent.config {c : (Fin k → V) → ℕ} (hc : IsCoherent c) : IsConfig c := hc.1

theorem IsCoherent.card_cvec_eq {c : (Fin k → V) → ℕ} (hc : IsCoherent c) {x y : Fin k → V}
    (h : c x = c y) (r : Fin k → ℕ) :
    (univ.filter fun z => cvec c x z = r).card = (univ.filter fun z => cvec c y z = r).card := by
  have e : ∀ w : Fin k → V, (univ.filter fun z => cvec c w z = r) =
      univ.filter fun z => ∀ j, c (update w j z) = r j := fun w => by
    ext z
    simp only [mem_filter, mem_univ, true_and, cvec, funext_iff]
  rw [e x, e y]
  exact hc.2 x y h r

/-- **Counting with a predicate on the colour vector**: in a coherent configuration, the
number of points `z` whose colour vector satisfies `P` depends only on the colour of `x`. -/
theorem IsCoherent.card_filter_pred {c : (Fin k → V) → ℕ} (hc : IsCoherent c)
    {x y : Fin k → V} (h : c x = c y) (P : (Fin k → ℕ) → Prop) [DecidablePred P] :
    (univ.filter fun z => P (cvec c x z)).card = (univ.filter fun z => P (cvec c y z)).card := by
  classical
  set R : Finset (Fin k → ℕ) := (univ.image (cvec c x)).filter P
  have key : ∀ w : Fin k → V, c w = c x →
      (univ.filter fun z => P (cvec c w z)).card =
        ∑ r ∈ R, (univ.filter fun z => cvec c w z = r).card := by
    intro w hw
    rw [card_eq_sum_card_fiberwise (f := cvec c w) (t := R)]
    · refine sum_congr rfl fun r hr => ?_
      congr 1
      ext z
      simp only [mem_filter, mem_univ, true_and]
      constructor
      · exact fun h' => h'.2
      · rintro rfl
        exact ⟨(mem_filter.1 hr).2, rfl⟩
    · intro z hz
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hz
      refine mem_filter.2 ⟨?_, hz⟩
      -- the vector `cvec c w z` occurs for `x`, as the fibres have equal size
      have hpos : 0 < (univ.filter fun z' => cvec c w z' = cvec c w z).card :=
        card_pos.2 ⟨z, by simp⟩
      rw [hc.card_cvec_eq hw] at hpos
      obtain ⟨z', hz'⟩ := card_pos.1 hpos
      simp only [mem_filter, mem_univ, true_and] at hz'
      exact mem_image.2 ⟨z', mem_univ _, hz'⟩
  rw [key x rfl, key y h.symm]
  exact sum_congr rfl fun r _ => hc.card_cvec_eq h r

theorem IsCoherent2.config {c : V → V → ℕ} (hc : IsCoherent2 c) {x y x' y' : V}
    (h : c x y = c x' y') :
    (x = y ↔ x' = y') ∧ c y x = c y' x' ∧ c x x = c x' x' ∧ c y y = c y' y' :=
  hc.1 x y x' y' h

/-- **Counting with a predicate on the two colours**: in a classical coherent configuration,
the number of points `z` with `P (c x z) (c z y)` depends only on the colour of `(x, y)`. -/
theorem IsCoherent2.card_filter_pred {c : V → V → ℕ} (hc : IsCoherent2 c) {x y x' y' : V}
    (h : c x y = c x' y') (P : ℕ → ℕ → Prop) [∀ a, DecidablePred (P a)] :
    (univ.filter fun z => P (c x z) (c z y)).card =
      (univ.filter fun z => P (c x' z) (c z y')).card := by
  classical
  set f : V → V → V → ℕ × ℕ := fun a b z => (c a z, c z b)
  set R : Finset (ℕ × ℕ) :=
    ((univ.image (f x y)) ∪ (univ.image (f x' y'))).filter fun q => P q.1 q.2
  have hfib : ∀ q : ℕ × ℕ, (univ.filter fun z => f x y z = q).card =
      (univ.filter fun z => f x' y' z = q).card := by
    intro q
    have e : ∀ a b, (univ.filter fun z => f a b z = q) =
        univ.filter fun z => c a z = q.1 ∧ c z b = q.2 := fun a b => by
      ext z
      simp only [f, mem_filter, mem_univ, true_and, Prod.ext_iff]
    rw [e, e]
    exact hc.2 x y x' y' h q.1 q.2
  have key : ∀ a b, (a = x ∧ b = y) ∨ (a = x' ∧ b = y') →
      (univ.filter fun z => P (c a z) (c z b)).card =
        ∑ q ∈ R, (univ.filter fun z => f a b z = q).card := by
    intro a b hab
    rw [card_eq_sum_card_fiberwise (f := f a b) (t := R)]
    · refine sum_congr rfl fun q hq => ?_
      congr 1
      ext z
      simp only [mem_filter, mem_univ, true_and]
      constructor
      · exact fun h' => h'.2
      · intro hz
        refine ⟨?_, hz⟩
        have := (mem_filter.1 hq).2
        rw [← hz] at this
        exact this
    · intro z hz
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hz
      refine mem_filter.2 ⟨?_, hz⟩
      rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact mem_union_left _ (mem_image_of_mem _ (mem_univ z))
      · exact mem_union_right _ (mem_image_of_mem _ (mem_univ z))
  rw [key x y (Or.inl ⟨rfl, rfl⟩), key x' y' (Or.inr ⟨rfl, rfl⟩)]
  exact sum_congr rfl fun q _ => hfib q

end GraphIso.Coherent
