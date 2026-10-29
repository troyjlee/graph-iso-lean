module

public import Mathlib.Algebra.Group.Action.Option
public import Mathlib.Algebra.Group.Action.Pointwise.Finset
public import Mathlib.Algebra.Group.Action.Sum
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Algebra.Group.Action.End

/-!
# The outputs of Split-or-Johnson

Points are a type `α` with decidable equality; permutations `σ : Equiv.Perm α` act on points,
on *cells* `Finset α` (pointwise) and on everything built from them.

* **Colored partitions** (Babai, Def. 5.1.1). `CPart α` is a colouring `col` with a block map
  `blk`: `blk v` is the block containing `v`, so blocks are named by their elements, which is
  canonical. `IsColPart V t p` says that `p` is an admissible colored equipartition of `V`
  whose blocks have at most `t` points (a colored `t`-partition; Helfgott's colored
  `α`-partition with `t = α|V|`). *Equipartition:* the blocks partition `V`, every colour class
  is a union of blocks, and blocks of one colour have one size. *Admissible:* a block with one
  point is a whole colour class.
* **Johnson embeddings.** `JEmb α` is a set `V0`, a set `Λ` of cells, a size `s` and a map `f`;
  `IsJohnson V t J` says that `V0 ⊆ V` has more than `t` points and that `f` is a bijection from
  `V0` onto the `s`-subsets of `Λ`, where `Λ` consists of nonempty, pairwise disjoint cells and
  `2 ≤ s ≤ |Λ|/2`. The embedded scheme is `J(|Λ|, s)`: `c(v, w) = |f v \ f w|` (Helfgott §2.7,
  with `2s ≤ r` as in §5.3.3).
* **Choices** are lists over `α ⊕ Finset α`: points, cells, or tuples of cells.
-/

@[expose] public section

namespace GraphIso.SplitJohnson

open Finset Pointwise

variable {α : Type*}

/-- A colouring with a block map. -/
structure CPart (α : Type*) where
  col : α → ℕ
  blk : α → Finset α

/-- An embedded Johnson scheme: a bijection `f` from `V0` onto the `s`-subsets of `Λ`. -/
structure JEmb (α : Type*) where
  V0 : Finset α
  Λ : Finset (Finset α)
  s : ℕ
  f : α → Finset (Finset α)

/-- The two outcomes of Split-or-Johnson. -/
abbrev Out (α : Type*) := CPart α ⊕ JEmb α

/-- Choices: lists of points and cells. -/
def Choice (α : Type*) := List (α ⊕ Finset α)

instance [DecidableEq α] : DecidableEq (Choice α) :=
  inferInstanceAs (DecidableEq (List (α ⊕ Finset α)))

variable [DecidableEq α]

/-- **A colored `t`-partition of `V`** (Babai, Def. 5.1.1): an admissible colored equipartition
of `V` whose blocks have at most `t` points. -/
structure IsColPart (V : Finset α) (t : ℕ) (p : CPart α) : Prop where
  mem_blk : ∀ v ∈ V, v ∈ p.blk v
  blk_sub : ∀ v ∈ V, p.blk v ⊆ V
  blk_eq : ∀ v ∈ V, ∀ w ∈ p.blk v, p.blk w = p.blk v
  col_eq : ∀ v ∈ V, ∀ w ∈ p.blk v, p.col w = p.col v
  card_eq : ∀ v ∈ V, ∀ w ∈ V, p.col v = p.col w → (p.blk v).card = (p.blk w).card
  admissible : ∀ v ∈ V, (p.blk v).card = 1 → ∀ w ∈ V, p.col w = p.col v → w = v
  card_le : ∀ v ∈ V, (p.blk v).card ≤ t

/-- **A Johnson scheme embedded in `V` on more than `t` points.** -/
structure IsJohnson (V : Finset α) (t : ℕ) (J : JEmb α) : Prop where
  sub : J.V0 ⊆ V
  card_gt : t < J.V0.card
  two_le : 2 ≤ J.s
  le_half : 2 * J.s ≤ J.Λ.card
  cells_ne : ∀ a ∈ J.Λ, a.Nonempty
  cells_disj : ∀ a ∈ J.Λ, ∀ b ∈ J.Λ, a ≠ b → Disjoint a b
  maps_to : ∀ v ∈ J.V0, J.f v ∈ J.Λ.powersetCard J.s
  inj : ∀ v ∈ J.V0, ∀ w ∈ J.V0, J.f v = J.f w → v = w
  surj : ∀ T ∈ J.Λ.powersetCard J.s, ∃ v ∈ J.V0, J.f v = T

/-- A valid leaf: a colored `t`-partition of `V` or a Johnson embedding in `V` on more than `t`
points. -/
def ValidOut (V : Finset α) (t : ℕ) : Option (Out α) → Prop
  | some (Sum.inl p) => IsColPart V t p
  | some (Sum.inr J) => IsJohnson V t J
  | none => False

/-! ### Actions of `Sym(α)` -/

instance : MulAction (Equiv.Perm α) (CPart α) where
  smul σ p := ⟨fun v => p.col (σ⁻¹ • v), fun v => σ • p.blk (σ⁻¹ • v)⟩
  one_smul p := by
    show CPart.mk _ _ = p
    simp only [inv_one, one_smul]
  mul_smul σ τ p := by
    show CPart.mk _ _ = CPart.mk _ _
    simp only [mul_inv_rev, mul_smul]
    rfl

instance : MulAction (Equiv.Perm α) (JEmb α) where
  smul σ J := ⟨σ • J.V0, σ • J.Λ, J.s, fun v => σ • J.f (σ⁻¹ • v)⟩
  one_smul J := by
    show JEmb.mk _ _ _ _ = J
    simp only [inv_one, one_smul]
  mul_smul σ τ J := by
    show JEmb.mk _ _ _ _ = JEmb.mk _ _ _ _
    simp only [mul_inv_rev, mul_smul]
    rfl

instance : MulAction (Equiv.Perm α) (Choice α) where
  smul σ x := List.map (fun a => σ • a) (show List (α ⊕ Finset α) from x)
  one_smul x := by
    show List.map _ x = x
    simp only [one_smul, List.map_id_fun']
    rfl
  mul_smul σ τ x := by
    let l : List (α ⊕ Finset α) := x
    show List.map _ l = List.map _ (List.map _ l)
    rw [List.map_map]
    exact List.map_congr_left fun a _ => mul_smul σ τ a

theorem CPart.smul_col (σ : Equiv.Perm α) (p : CPart α) (v : α) :
    (σ • p).col v = p.col (σ⁻¹ • v) := rfl

theorem CPart.smul_blk (σ : Equiv.Perm α) (p : CPart α) (v : α) :
    (σ • p).blk v = σ • p.blk (σ⁻¹ • v) := rfl

theorem JEmb.smul_V0 (σ : Equiv.Perm α) (J : JEmb α) : (σ • J).V0 = σ • J.V0 := rfl

theorem JEmb.smul_Λ (σ : Equiv.Perm α) (J : JEmb α) : (σ • J).Λ = σ • J.Λ := rfl

theorem JEmb.smul_s (σ : Equiv.Perm α) (J : JEmb α) : (σ • J).s = J.s := rfl

theorem JEmb.smul_f (σ : Equiv.Perm α) (J : JEmb α) (v : α) :
    (σ • J).f v = σ • J.f (σ⁻¹ • v) := rfl

end GraphIso.SplitJohnson
