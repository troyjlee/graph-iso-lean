module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Group.Action.Pointwise.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Choice trees: canonicity relative to arbitrary choices

Babai's algorithm makes arbitrary choices, such as individualizing a point, and is canonical
only relative to them (Babai, *Graph isomorphism in quasipolynomial time*, Def. 4.0.4,
"reduction at multiplicative cost"). A **choice tree** records the choices.

* `CTree.node S k` chooses an element `c` of a finite set `S` and continues with `k c`.
* `CTree.leaf o` returns `o`.

Only the choices in the node sets are followed: `Reach o t` says that `o` is a reachable leaf,
`AllLeaves P t` that every reachable leaf satisfies `P`, and `Live t` that every reachable node
set is nonempty. `count t`, the number of root-to-leaf paths, is the multiplicative cost.

A group `G` acting on the choices and on the outputs acts on trees (`CTree.act`). A procedure
`F` is **canonical** when `F (g • X) = (F X).act g` for every `g`. Then `g` maps the reachable
leaves of `F X` onto those of `F (g • X)` (`reach_act`), so isomorphisms of the inputs carry
leaves to leaves. To test `X` against `Y`, one fixes one leaf of `F X` and compares it with the
leaves of `F Y`, at most `count (F Y)` comparisons.
-/

@[expose] public section

namespace GraphIso.SplitJohnson

open Finset

/-- **Choice trees**: a leaf returns an output; a node chooses an element of a finite set and
continues. -/
inductive CTree (C O : Type*) where
  | leaf : O → CTree C O
  | node : Finset C → (C → CTree C O) → CTree C O

namespace CTree

variable {C C' O O' O'' : Type*}

/-- The number of root-to-leaf paths: the multiplicative cost. -/
def count : CTree C O → ℕ
  | leaf _ => 1
  | node S k => ∑ c ∈ S, (k c).count

/-- Every reachable leaf satisfies `P`. -/
def AllLeaves (P : O → Prop) : CTree C O → Prop
  | leaf o => P o
  | node S k => ∀ c ∈ S, (k c).AllLeaves P

/-- Every reachable node set is nonempty. -/
def Live : CTree C O → Prop
  | leaf _ => True
  | node S k => S.Nonempty ∧ ∀ c ∈ S, (k c).Live

/-- `o` is a reachable leaf. -/
def Reach (o : O) : CTree C O → Prop
  | leaf o' => o' = o
  | node S k => ∃ c ∈ S, (k c).Reach o

/-- The reachable leaves. -/
def leaves [DecidableEq O] : CTree C O → Finset O
  | leaf o => {o}
  | node S k => S.biUnion fun c => (k c).leaves

/-- Continue every leaf `o` with `f o`. -/
def bind : CTree C O → (O → CTree C O') → CTree C O'
  | leaf o, f => f o
  | node S k, f => node S fun c => (k c).bind f

/-- Change the type of choices along `f` (with a retraction `r`) and of outputs along `h`. -/
def trans [DecidableEq C'] (f : C → C') (r : C' → C) (h : O → O') : CTree C O → CTree C' O'
  | leaf o => leaf (h o)
  | node S k => node (S.image f) fun c' => (k (r c')).trans f r h

section Basic

theorem allLeaves_iff_reach {P : O → Prop} {t : CTree C O} :
    t.AllLeaves P ↔ ∀ o, t.Reach o → P o := by
  induction t with
  | leaf o => simp [AllLeaves, Reach]
  | node S k ih =>
    simp only [AllLeaves, Reach, ih]
    constructor
    · rintro h o ⟨c, hc, ho⟩
      exact h c hc o ho
    · intro h c hc o ho
      exact h o ⟨c, hc, ho⟩

theorem AllLeaves.mono {P Q : O → Prop} (hPQ : ∀ o, P o → Q o) {t : CTree C O}
    (h : t.AllLeaves P) : t.AllLeaves Q := by
  rw [allLeaves_iff_reach] at h ⊢
  exact fun o ho => hPQ o (h o ho)

theorem Live.exists_reach {t : CTree C O} (h : t.Live) : ∃ o, t.Reach o := by
  induction t with
  | leaf o => exact ⟨o, rfl⟩
  | node S k ih =>
    obtain ⟨c, hc⟩ := h.1
    obtain ⟨o, ho⟩ := ih c (h.2 c hc)
    exact ⟨o, c, hc, ho⟩

theorem mem_leaves [DecidableEq O] {t : CTree C O} {o : O} : o ∈ t.leaves ↔ t.Reach o := by
  induction t with
  | leaf o' => simp [leaves, Reach, eq_comm]
  | node S k ih => simp [leaves, Reach, ih]

theorem card_leaves_le [DecidableEq O] (t : CTree C O) : t.leaves.card ≤ t.count := by
  induction t with
  | leaf o => simp [leaves, count]
  | node S k ih =>
    simp only [leaves, count]
    exact (card_biUnion_le).trans (sum_le_sum fun c _ => ih c)

end Basic

section Bind

theorem allLeaves_bind {P : O' → Prop} {t : CTree C O} {f : O → CTree C O'}
    (h : t.AllLeaves fun o => (f o).AllLeaves P) : (t.bind f).AllLeaves P := by
  induction t with
  | leaf o => exact h
  | node S k ih => exact fun c hc => ih c (h c hc)

theorem live_bind {t : CTree C O} {f : O → CTree C O'} (ht : t.Live)
    (h : t.AllLeaves fun o => (f o).Live) : (t.bind f).Live := by
  induction t with
  | leaf o => exact h
  | node S k ih => exact ⟨ht.1, fun c hc => ih c (ht.2 c hc) (h c hc)⟩

theorem count_bind_le {t : CTree C O} {f : O → CTree C O'} {B : ℕ}
    (h : t.AllLeaves fun o => (f o).count ≤ B) : (t.bind f).count ≤ t.count * B := by
  induction t with
  | leaf o =>
    show (f o).count ≤ 1 * B
    rw [one_mul]
    exact h
  | node S k ih =>
    simp only [bind, count, sum_mul]
    exact sum_le_sum fun c hc => ih c (h c hc)

theorem bind_assoc (t : CTree C O) (f : O → CTree C O') (g : O' → CTree C O'') :
    (t.bind f).bind g = t.bind fun o => (f o).bind g := by
  induction t with
  | leaf o => rfl
  | node S k ih => simp only [bind, ih]

end Bind

section Trans

variable [DecidableEq C']

theorem allLeaves_trans {f : C → C'} {r : C' → C} {h : O → O'} (hr : ∀ c, r (f c) = c)
    {P : O' → Prop} {t : CTree C O} (ht : t.AllLeaves fun o => P (h o)) :
    (t.trans f r h).AllLeaves P := by
  induction t with
  | leaf o => exact ht
  | node S k ih =>
    intro c' hc'
    obtain ⟨c, hc, rfl⟩ := mem_image.1 hc'
    show (trans f r h (k (r (f c)))).AllLeaves P
    rw [hr]
    exact ih c (ht c hc)

theorem live_trans {f : C → C'} {r : C' → C} {h : O → O'} (hr : ∀ c, r (f c) = c)
    {t : CTree C O} (ht : t.Live) : (t.trans f r h).Live := by
  induction t with
  | leaf o => trivial
  | node S k ih =>
    refine ⟨ht.1.image f, fun c' hc' => ?_⟩
    obtain ⟨c, hc, rfl⟩ := mem_image.1 hc'
    show (trans f r h (k (r (f c)))).Live
    rw [hr]
    exact ih c (ht.2 c hc)

theorem count_trans {f : C → C'} {r : C' → C} {h : O → O'} (hr : ∀ c, r (f c) = c)
    (t : CTree C O) : (t.trans f r h).count = t.count := by
  have hf : Function.Injective f := fun a b e => by rw [← hr a, e, hr]
  induction t with
  | leaf o => rfl
  | node S k ih =>
    simp only [trans, count]
    rw [sum_image fun a _ b _ e => hf e]
    exact sum_congr rfl fun c _ => by rw [hr, ih]

end Trans

section Act

variable {G : Type*} [Group G] [MulAction G C] [MulAction G O] [DecidableEq C]

open Pointwise

/-- The action of `g` on a tree: choices and outputs are moved by `g`. -/
def act (g : G) : CTree C O → CTree C O
  | leaf o => leaf (g • o)
  | node S k => node (g • S) fun c => (k (g⁻¹ • c)).act g

theorem reach_act (g : G) {t : CTree C O} {o : O} : (t.act g).Reach (g • o) ↔ t.Reach o := by
  induction t with
  | leaf o' => simp [act, Reach]
  | node S k ih =>
    simp only [act, Reach]
    constructor
    · rintro ⟨c, hc, ho⟩
      obtain ⟨c₀, hc₀, rfl⟩ := mem_smul_finset.1 hc
      rw [inv_smul_smul] at ho
      exact ⟨c₀, hc₀, (ih c₀).1 ho⟩
    · rintro ⟨c, hc, ho⟩
      exact ⟨g • c, smul_mem_smul_finset hc, by rw [inv_smul_smul]; exact (ih c).2 ho⟩

theorem allLeaves_act (g : G) {P : O → Prop} {t : CTree C O} :
    (t.act g).AllLeaves P ↔ t.AllLeaves fun o => P (g • o) := by
  rw [allLeaves_iff_reach, allLeaves_iff_reach]
  constructor
  · intro h o ho
    exact h _ ((reach_act g).2 ho)
  · intro h o ho
    have := h (g⁻¹ • o) ((reach_act g).1 (by rwa [smul_inv_smul]))
    rwa [smul_inv_smul] at this

theorem live_act (g : G) {t : CTree C O} : (t.act g).Live ↔ t.Live := by
  induction t with
  | leaf o => simp [act, Live]
  | node S k ih =>
    simp only [act, Live, smul_finset_nonempty]
    constructor
    · rintro ⟨hS, h⟩
      refine ⟨hS, fun c hc => (ih c).1 ?_⟩
      have := h (g • c) (smul_mem_smul_finset hc)
      rwa [inv_smul_smul] at this
    · rintro ⟨hS, h⟩
      refine ⟨hS, fun c hc => (ih _).2 (h _ ?_)⟩
      obtain ⟨c₀, hc₀, rfl⟩ := mem_smul_finset.1 hc
      rwa [inv_smul_smul]

theorem count_act (g : G) (t : CTree C O) : (t.act g).count = t.count := by
  induction t with
  | leaf o => rfl
  | node S k ih =>
    simp only [act, count]
    rw [smul_finset_def, sum_image fun a _ b _ e => smul_left_cancel g e]
    exact sum_congr rfl fun c _ => by rw [inv_smul_smul, ih]

/-- Binding with a canonical continuation commutes with the action. -/
theorem act_bind [MulAction G O'] (g : G) (t : CTree C O) {f : O → CTree C O'}
    (hf : ∀ o, f (g • o) = (f o).act g) : (t.bind f).act g = (t.act g).bind f := by
  induction t with
  | leaf o => exact (hf o).symm
  | node S k ih => simp only [bind, act, ih]

/-- Changing the types of choices and outputs commutes with the actions when the maps do. -/
theorem act_trans {G' : Type*} [Group G'] [MulAction G' C'] [MulAction G' O'] [DecidableEq C']
    (g : G) (g' : G') {f : C → C'} {r : C' → C} {h : O → O'} (hf : ∀ c, f (g • c) = g' • f c)
    (hr : ∀ c', r (g'⁻¹ • c') = g⁻¹ • r c') (hh : ∀ o, h (g • o) = g' • h o)
    (t : CTree C O) : (t.act g).trans f r h = (t.trans f r h).act g' := by
  induction t with
  | leaf o => simp only [act, trans, hh]
  | node S k ih =>
    simp only [act, trans]
    congr 1
    · ext c'
      simp only [mem_image, mem_smul_finset]
      constructor
      · rintro ⟨c, ⟨c₀, hc₀, rfl⟩, rfl⟩
        exact ⟨f c₀, ⟨c₀, hc₀, rfl⟩, (hf c₀).symm⟩
      · rintro ⟨c₁, ⟨c₀, hc₀, rfl⟩, rfl⟩
        exact ⟨g • c₀, ⟨c₀, hc₀, rfl⟩, hf c₀⟩
    · funext c'
      rw [← ih, hr]

end Act

end CTree

end GraphIso.SplitJohnson
