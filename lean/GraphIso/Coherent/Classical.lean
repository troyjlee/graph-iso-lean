module

public import GraphIso.Coherent.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Prod
public import Mathlib.Logic.Relation

/-!
# Classical coherent configurations on a finite set

Split-or-Johnson manipulates classical coherent configurations on finite subsets of a type `R`
(Helfgott, §§2.4, 2.6 and 5.2). A colouring `c : R → R → ℕ` is a **classical coherent
configuration on `S : Finset R`** (`IsCoh2On S c`) if its restriction to the subtype `↥S` is
one in the sense of `IsCoherent2` (Def. 2.8).

* `IsHomog S c`: all points of `S` have one vertex colour.
* `offCols S c`: the colours of pairs of distinct points.
* `Adj S c r`: undirected adjacency in colour `r` within `S`; `comp S c r x` is the connected
  component of `x` (computed by `|S|` rounds of closure, `mem_comp`).
* `IsPrimitive S c` (Def. 2.14): homogeneous, with every off-diagonal colour graph connected;
  `IsUniprimitive S c`: primitive and not a clique.

Facts:
* restriction to a union of vertex colour classes is coherent (Exercise 2.12);
* out- and in-degrees in a colour depend only on the vertex colour (Exercise 2.17);
* a colour class of more than half the points is symmetric;
* a homogeneous configuration that is not a clique has no clique on more than half of its
  points (Exercise 2.15, `not_isClique_of_large`);
* the number of walks with a prescribed colour sequence between two points depends only on the
  colour of the pair (Exercise 2.16 (a), `walkCount_eq`); so does reachability in a colour graph,
  and the components of a colour graph all have the same size, at least two points
  (Exercise 2.16 (b));
* contracting the components of a colour graph gives a semiregular bipartite graph
  (Exercise 2.18);
* the colour of a pair determines whether its points are twins with respect to a vertex colour
  class (Exercise 5.6);
* in a uniprimitive configuration, two points joined by a colour `r` have a common
  neighbour in the complement of `r` (Exercise B.7).
-/

@[expose] public section

namespace GraphIso.Coherent

open Finset

variable {R : Type*} [DecidableEq R]

/-- **A classical coherent configuration on `S`.** -/
def IsCoh2On (S : Finset R) (c : R → R → ℕ) : Prop := IsCoherent2 fun x y : S => c x y

/-- All points of `S` have one vertex colour. -/
def IsHomog (S : Finset R) (c : R → R → ℕ) : Prop := ∀ x ∈ S, ∀ y ∈ S, c x x = c y y

/-- The colours of pairs of distinct points of `S`. -/
def offCols (S : Finset R) (c : R → R → ℕ) : Finset ℕ :=
  ((S ×ˢ S).filter fun p => p.1 ≠ p.2).image fun p => c p.1 p.2

/-- Undirected adjacency in colour `r` within `S`. -/
def Adj (S : Finset R) (c : R → R → ℕ) (r : ℕ) (x y : R) : Prop :=
  x ∈ S ∧ y ∈ S ∧ (c x y = r ∨ c y x = r)

/-- One round of closure under `r`-adjacency within `S`. -/
def compStep (S : Finset R) (c : R → R → ℕ) (r : ℕ) (T : Finset R) : Finset R :=
  T ∪ S.filter fun y => ∃ x ∈ T, c x y = r ∨ c y x = r

/-- The connected component of `x` in the `r`-graph on `S` (empty if `x ∉ S`). -/
def comp (S : Finset R) (c : R → R → ℕ) (r : ℕ) (x : R) : Finset R :=
  (compStep S c r)^[S.card] (if x ∈ S then {x} else ∅)

/-- **Primitive** (Helfgott, Def. 2.14): homogeneous, and every off-diagonal colour graph is
connected. -/
def IsPrimitive (S : Finset R) (c : R → R → ℕ) : Prop :=
  IsHomog S c ∧
    ∀ r ∈ offCols S c, ∀ x ∈ S, ∀ y ∈ S, Relation.ReflTransGen (Adj S c r) x y

/-- **Uniprimitive**: primitive and not a clique. -/
def IsUniprimitive (S : Finset R) (c : R → R → ℕ) : Prop := IsPrimitive S c ∧ ¬ IsClique c S

/-! ### The components of a colour graph -/

section Comp

variable {S : Finset R} {c : R → R → ℕ} {r : ℕ}

theorem subset_compStep (T : Finset R) : T ⊆ compStep S c r T := subset_union_left

theorem compStep_subset {T : Finset R} (hT : T ⊆ S) : compStep S c r T ⊆ S :=
  union_subset hT (filter_subset _ _)

omit [DecidableEq R] in
theorem adj_symm {x y : R} (h : Adj S c r x y) : Adj S c r y x :=
  ⟨h.2.1, h.1, h.2.2.symm⟩

omit [DecidableEq R] in
theorem reflTransGen_adj_symm {x y : R} (h : Relation.ReflTransGen (Adj S c r) x y) :
    Relation.ReflTransGen (Adj S c r) y x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hab ih => exact Relation.ReflTransGen.head (adj_symm hab) ih

/-- The starting set of the closure. -/
def compStart (S : Finset R) (x : R) : Finset R := if x ∈ S then {x} else ∅

theorem compStart_subset (x : R) : compStart S x ⊆ S := by
  unfold compStart
  split_ifs with h
  · exact singleton_subset_iff.2 h
  · exact empty_subset _

theorem iterate_compStep_subset (x : R) (n : ℕ) : (compStep S c r)^[n] (compStart S x) ⊆ S := by
  induction n with
  | zero => exact compStart_subset x
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact compStep_subset ih

/-- Every point of the closure is reachable from `x`. -/
theorem reach_of_mem_iterate (x : R) (n : ℕ) :
    ∀ y ∈ (compStep S c r)^[n] (compStart S x), x ∈ S ∧ Relation.ReflTransGen (Adj S c r) x y := by
  induction n with
  | zero =>
    intro y hy
    simp only [Function.iterate_zero, id, compStart] at hy
    split_ifs at hy with hx
    · rw [mem_singleton] at hy
      subst hy
      exact ⟨hx, Relation.ReflTransGen.refl⟩
    · simp at hy
  | succ n ih =>
    intro y hy
    rw [Function.iterate_succ_apply'] at hy
    rcases mem_union.1 hy with hy | hy
    · exact ih y hy
    · obtain ⟨hyS, z, hz, hzy⟩ := mem_filter.1 hy
      obtain ⟨hx, hxz⟩ := ih z hz
      exact ⟨hx, hxz.tail ⟨iterate_compStep_subset x n hz, hyS, hzy⟩⟩

/-- The closure stabilizes within `|S|` rounds. -/
theorem exists_fixed (x : R) :
    ∃ m ≤ S.card, compStep S c r ((compStep S c r)^[m] (compStart S x)) =
      (compStep S c r)^[m] (compStart S x) := by
  by_contra hne
  push Not at hne
  have key : ∀ n ≤ S.card + 1, n ≤ ((compStep S c r)^[n] (compStart S x)).card := by
    intro n
    induction n with
    | zero => intro _; exact Nat.zero_le _
    | succ n ih =>
      intro hn
      have h1 := ih (by omega)
      have hss : (compStep S c r)^[n] (compStart S x) ⊂
          (compStep S c r)^[n + 1] (compStart S x) := by
        rw [Function.iterate_succ_apply']
        exact ssubset_of_subset_of_ne (subset_compStep _) (hne n (by omega)).symm
      have := card_lt_card hss
      omega
  have h1 := key (S.card + 1) le_rfl
  have h2 := card_le_card (iterate_compStep_subset (S := S) (c := c) (r := r) x (S.card + 1))
  omega

theorem comp_fixed (x : R) : compStep S c r (comp S c r x) = comp S c r x := by
  obtain ⟨m, hm, hfix⟩ := exists_fixed (S := S) (c := c) (r := r) x
  have e : comp S c r x = (compStep S c r)^[S.card - m] ((compStep S c r)^[m] (compStart S x)) := by
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hm]
    rfl
  rw [e, Function.iterate_fixed hfix]
  exact hfix

theorem compStart_subset_iterate (x : R) (n : ℕ) :
    compStart S x ⊆ (compStep S c r)^[n] (compStart S x) := by
  induction n with
  | zero => exact Subset.refl _
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact ih.trans (subset_compStep _)

end Comp

/-! ### Basic facts -/

theorem mem_comp {S : Finset R} {c : R → R → ℕ} {r : ℕ} {x y : R} :
    y ∈ comp S c r x ↔ x ∈ S ∧ Relation.ReflTransGen (Adj S c r) x y := by
  constructor
  · exact reach_of_mem_iterate x S.card y
  · rintro ⟨hx, hxy⟩
    have hx' : x ∈ comp S c r x := by
      apply compStart_subset_iterate x S.card
      simp [compStart, hx]
    induction hxy with
    | refl => exact hx'
    | tail _ hab ih =>
      rw [← comp_fixed x]
      exact mem_union_right _ (mem_filter.2 ⟨hab.2.1, _, ih, hab.2.2⟩)

theorem comp_subset (S : Finset R) (c : R → R → ℕ) (r : ℕ) (x : R) : comp S c r x ⊆ S :=
  iterate_compStep_subset x S.card

theorem self_mem_comp {S : Finset R} {c : R → R → ℕ} {r : ℕ} {x : R} (hx : x ∈ S) :
    x ∈ comp S c r x :=
  mem_comp.2 ⟨hx, Relation.ReflTransGen.refl⟩

theorem comp_eq_of_mem {S : Finset R} {c : R → R → ℕ} {r : ℕ} {x y : R}
    (hy : y ∈ comp S c r x) : comp S c r y = comp S c r x := by
  obtain ⟨hx, hxy⟩ := mem_comp.1 hy
  have hyS := comp_subset S c r x hy
  ext z
  rw [mem_comp, mem_comp]
  constructor
  · rintro ⟨-, hyz⟩
    exact ⟨hx, hxy.trans hyz⟩
  · rintro ⟨-, hxz⟩
    exact ⟨hyS, (reflTransGen_adj_symm hxy).trans hxz⟩

omit [DecidableEq R] in
/-- Counting over the subtype `↥S` is counting over `S`. -/
theorem card_univ_filter_val (S : Finset R) (Q : R → Prop) [DecidablePred Q] :
    ((univ : Finset S).filter fun z => Q z.1).card = (S.filter Q).card := by
  refine card_bij (fun z _ => z.1) ?_ ?_ ?_
  · intro z hz
    simp only [mem_filter, mem_univ, true_and] at hz ⊢
    exact ⟨z.2, hz⟩
  · intro a _ b _ e
    exact Subtype.ext e
  · intro w hw
    rw [mem_filter] at hw
    exact ⟨⟨w, hw.1⟩, by simp [hw.2], rfl⟩

omit [DecidableEq R] in
theorem IsCoh2On.config {S : Finset R} {c : R → R → ℕ} (hc : IsCoh2On S c) {x y x' y' : R}
    (hx : x ∈ S) (hy : y ∈ S) (hx' : x' ∈ S) (hy' : y' ∈ S) (h : c x y = c x' y') :
    (x = y ↔ x' = y') ∧ c y x = c y' x' ∧ c x x = c x' x' ∧ c y y = c y' y' := by
  have := hc.1 ⟨x, hx⟩ ⟨y, hy⟩ ⟨x', hx'⟩ ⟨y', hy'⟩ h
  refine ⟨?_, this.2.1, this.2.2.1, this.2.2.2⟩
  have h1 := this.1
  simp only [Subtype.mk.injEq] at h1
  exact h1

omit [DecidableEq R] in
/-- Counting with an arbitrary predicate on the two colours depends only on the colour of the
pair. -/
theorem IsCoh2On.card_filter_pred {S : Finset R} {c : R → R → ℕ} (hc : IsCoh2On S c)
    {x y x' y' : R} (hx : x ∈ S) (hy : y ∈ S) (hx' : x' ∈ S) (hy' : y' ∈ S)
    (h : c x y = c x' y') (P : ℕ → ℕ → Prop) [DecidableRel P] :
    (S.filter fun z => P (c x z) (c z y)).card = (S.filter fun z => P (c x' z) (c z y')).card := by
  rw [← card_univ_filter_val S (fun z => P (c x z) (c z y)),
    ← card_univ_filter_val S (fun z => P (c x' z) (c z y'))]
  exact IsCoherent2.card_filter_pred hc (x := ⟨x, hx⟩) (y := ⟨y, hy⟩) (x' := ⟨x', hx'⟩)
    (y' := ⟨y', hy'⟩) h P

omit [DecidableEq R] in
/-- **Restriction to a union of vertex colour classes** (Exercise 2.12). -/
theorem IsCoh2On.subset {S T : Finset R} {c : R → R → ℕ} (hc : IsCoh2On S c) (hTS : T ⊆ S)
    (hT : ∀ x ∈ T, ∀ y ∈ S, c x x = c y y → y ∈ T) : IsCoh2On T c := by
  classical
  refine ⟨fun a b a' b' h => ?_, fun a b a' b' h r s => ?_⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hc.config (hTS a.2) (hTS b.2) (hTS a'.2) (hTS b'.2) h
    refine ⟨?_, h2, h3, h4⟩
    rw [Subtype.ext_iff, Subtype.ext_iff]
    exact h1
  · have key : ∀ p q : T, (univ.filter fun z : T => c p z = r ∧ c z q = s).card =
        (S.filter fun z => (c p z = r ∧ c z q = s) ∧ ∃ u ∈ S, ∃ w ∈ T, c u w = c p z).card := by
      intro p q
      rw [card_univ_filter_val T (fun z => c p z = r ∧ c z q = s)]
      congr 1
      ext z
      simp only [mem_filter]
      constructor
      · rintro ⟨hz, h'⟩
        exact ⟨hTS hz, h', p, hTS p.2, z, hz, rfl⟩
      · rintro ⟨hz, h', u, hu, w, hw, e⟩
        refine ⟨hT w hw z hz ?_, h'⟩
        exact (hc.config hu (hTS hw) (hTS p.2) hz e).2.2.2
    exact (key a b).trans ((hc.card_filter_pred (hTS a.2) (hTS b.2) (hTS a'.2) (hTS b'.2) h
      (fun α β => (α = r ∧ β = s) ∧ ∃ u ∈ S, ∃ w ∈ T, c u w = α)).trans (key a' b').symm)

omit [DecidableEq R] in
/-- **Out-degrees** in a colour depend only on the vertex colour (Exercise 2.17). -/
theorem IsCoh2On.outdeg {S : Finset R} {c : R → R → ℕ} (hc : IsCoh2On S c) {x x' : R}
    (hx : x ∈ S) (hx' : x' ∈ S) (h : c x x = c x' x') (g : ℕ) :
    (S.filter fun z => c x z = g).card = (S.filter fun z => c x' z = g).card :=
  hc.card_filter_pred hx hx hx' hx' h (fun a _ => a = g)

omit [DecidableEq R] in
/-- **In-degrees** in a colour depend only on the vertex colour. -/
theorem IsCoh2On.indeg {S : Finset R} {c : R → R → ℕ} (hc : IsCoh2On S c) {y y' : R}
    (hy : y ∈ S) (hy' : y' ∈ S) (h : c y y = c y' y') (g : ℕ) :
    (S.filter fun z => c z y = g).card = (S.filter fun z => c z y' = g).card :=
  hc.card_filter_pred hy hy hy' hy' h (fun _ b => b = g)

omit [DecidableEq R] in
/-- **In-degrees equal out-degrees** in a homogeneous configuration (double counting). -/
theorem IsCoh2On.card_in_eq_out {S : Finset R} {c : R → R → ℕ} (hc : IsCoh2On S c)
    (hh : IsHomog S c) {p q : R} (hp : p ∈ S) (hq : q ∈ S) (g : ℕ) :
    (S.filter fun z => c z p = g).card = (S.filter fun z => c q z = g).card := by
  have h1 : ∑ u ∈ S, (S.filter fun z => c u z = g).card =
      ∑ v ∈ S, (S.filter fun z => c z v = g).card := by
    simp only [card_filter]
    exact sum_comm
  rw [sum_congr rfl fun u hu => hc.outdeg hu hq (hh u hu q hq) g,
    sum_congr rfl fun v hv => hc.indeg hv hp (hh v hv p hp) g, sum_const, sum_const,
    smul_eq_mul, smul_eq_mul] at h1
  exact (Nat.eq_of_mul_eq_mul_left (card_pos.2 ⟨p, hp⟩) h1).symm

/-- **A colour of more than half the out-neighbourhood is symmetric.** -/
theorem IsCoh2On.symm_of_large {S : Finset R} {c : R → R → ℕ} (hc : IsCoh2On S c)
    (hh : IsHomog S c) {x : R} (hx : x ∈ S) {a : ℕ}
    (ha : S.card < 2 * (S.filter fun z => c x z = a).card) {y z : R} (hy : y ∈ S)
    (hz : z ∈ S) (hyz : c y z = a) : c z y = a := by
  by_contra hne
  have e1 : (S.filter fun w => c x w = c z y) = S.filter fun w => c w x = a := by
    ext w
    simp only [mem_filter]
    constructor
    · rintro ⟨hw, h'⟩
      exact ⟨hw, by rw [← hyz]; exact (hc.config hx hw hz hy h').2.1⟩
    · rintro ⟨hw, h'⟩
      refine ⟨hw, ?_⟩
      rw [← hyz] at h'
      exact (hc.config hw hx hy hz h').2.1
  have e2 := hc.card_in_eq_out hh hx hx a
  have hdisj : Disjoint (S.filter fun w => c x w = a) (S.filter fun w => c x w = c z y) := by
    rw [disjoint_filter]
    intro w _ h1 h2
    exact hne (h2.symm.trans h1)
  have h3 := card_union_of_disjoint hdisj
  have h4 := card_le_card (union_subset (filter_subset (fun w => c x w = a) S)
    (filter_subset (fun w => c x w = c z y) S))
  rw [e1] at h3 h4
  omega

/-- **No large clique** (Exercise 2.15) in a homogeneous configuration that is not a
clique. Homogeneity is needed: the orbital configuration of `Sym({0, 1, 2})` on `{0, 1, 2, 3}`
is not a clique but is one on `{0, 1, 2}`. -/
theorem IsCoh2On.not_isClique_of_large {S B : Finset R} {c : R → R → ℕ}
    (hc : IsCoh2On S c) (hh : IsHomog S c) (hS : ¬ IsClique c S) (hB : B ⊆ S)
    (hcard : S.card < 2 * B.card) : ¬ IsClique c B := by
  intro hcl
  -- an off-diagonal pair of `S` whose colour is not the colour of `B`
  obtain ⟨p, hp, q, hq, hpq, hcol⟩ : ∃ p ∈ S, ∃ q ∈ S, p ≠ q ∧
      ∀ u ∈ B, ∀ v ∈ B, u ≠ v → c p q ≠ c u v := by
    by_contra hno
    push Not at hno
    apply hS
    intro u hu v hv u' hu' v' hv' huv hu'v'
    obtain ⟨b₁, hb₁, b₂, hb₂, hb, e₁⟩ := hno u hu v hv huv
    obtain ⟨b₃, hb₃, b₄, hb₄, hb', e₂⟩ := hno u' hu' v' hv' hu'v'
    rw [e₁, e₂]
    exact hcl b₁ hb₁ b₂ hb₂ b₃ hb₃ b₄ hb₄ hb hb'
  set black := c p q
  have hd : ∀ u ∈ S, (S.filter fun z => c u z = black).card =
      (S.filter fun z => c p z = black).card := fun u hu => hc.outdeg hu hp (hh u hu p hp) _
  have hi : ∀ v ∈ S, (S.filter fun z => c z v = black).card =
      (S.filter fun z => c p z = black).card := fun v hv => hc.card_in_eq_out hh hv hp _
  -- black edges from `B` leave `B`
  have hout : ∀ b ∈ B,
      (S.filter fun z => c b z = black) ⊆ (S \ B).filter fun z => c b z = black := by
    intro b hb z hz
    rw [mem_filter] at hz
    refine mem_filter.2 ⟨mem_sdiff.2 ⟨hz.1, fun hzB => ?_⟩, hz.2⟩
    have hbz : b ≠ z := fun e => hpq ((hc.config hp hq (hB hb) hz.1 hz.2.symm).1.2 e)
    exact hcol b hb z hzB hbz hz.2.symm
  have hcount : ∑ b ∈ B, ((S \ B).filter fun z => c b z = black).card =
      ∑ z ∈ S \ B, (B.filter fun b => c b z = black).card := by
    simp only [card_filter]
    exact sum_comm
  have hle1 : B.card * (S.filter fun z => c p z = black).card ≤
      ∑ b ∈ B, ((S \ B).filter fun z => c b z = black).card := by
    rw [← smul_eq_mul, ← sum_const]
    exact sum_le_sum fun b hb => by rw [← hd b (hB hb)]; exact card_le_card (hout b hb)
  have hle2 : ∑ z ∈ S \ B, (B.filter fun b => c b z = black).card ≤
      (S \ B).card * (S.filter fun z => c p z = black).card := by
    rw [← smul_eq_mul, ← sum_const]
    refine sum_le_sum fun z hz => ?_
    rw [← hi z (mem_sdiff.1 hz).1]
    exact card_le_card (filter_subset_filter _ hB)
  have hpos : 0 < (S.filter fun z => c p z = black).card := card_pos.2 ⟨q, mem_filter.2 ⟨hq, rfl⟩⟩
  have h3 : B.card ≤ (S \ B).card :=
    Nat.le_of_mul_le_mul_right (hle1.trans (hcount ▸ hle2)) hpos
  rw [card_sdiff_of_subset hB] at h3
  omega

omit [DecidableEq R] in
/-- **Transport of a point along a pair**: if `c x y = c x' y'`, every `w` has a counterpart
`w'` with the same colours to the pair. -/
theorem IsCoh2On.transport {S : Finset R} {c : R → R → ℕ} (hc : IsCoh2On S c) {x y x' y' w : R}
    (hx : x ∈ S) (hy : y ∈ S) (hx' : x' ∈ S) (hy' : y' ∈ S) (h : c x y = c x' y')
    (hw : w ∈ S) : ∃ w' ∈ S, c x' w' = c x w ∧ c w' y' = c w y := by
  have e : (S.filter fun z => c x z = c x w ∧ c z y = c w y).card =
      (S.filter fun z => c x' z = c x w ∧ c z y' = c w y).card :=
    hc.card_filter_pred hx hy hx' hy' h (fun a b => a = c x w ∧ b = c w y)
  have hpos : 0 < (S.filter fun z => c x z = c x w ∧ c z y = c w y).card :=
    card_pos.2 ⟨w, mem_filter.2 ⟨hw, rfl, rfl⟩⟩
  rw [e] at hpos
  obtain ⟨w', hw'⟩ := card_pos.1 hpos
  rw [mem_filter] at hw'
  exact ⟨w', hw'.1, hw'.2⟩

omit [DecidableEq R] in
/-- Reachability transports along pairs of the same colour. -/
theorem IsCoh2On.reach_of_eq {S : Finset R} {c : R → R → ℕ} (hc : IsCoh2On S c) (r : ℕ)
    {x y : R} (hxy : Relation.ReflTransGen (Adj S c r) x y) (hx : x ∈ S) (hy : y ∈ S)
    {x' y' : R} (hx' : x' ∈ S) (hy' : y' ∈ S) (h : c x y = c x' y') :
    Relation.ReflTransGen (Adj S c r) x' y' := by
  induction hxy using Relation.ReflTransGen.head_induction_on generalizing x' with
  | refl =>
    have := (hc.config hy hy hx' hy' h).1.1 rfl
    rw [this]
  | head hxw _ ih =>
    rename_i a w
    obtain ⟨w', hw', h1, h2⟩ := hc.transport hx hy hx' hy' h hxw.2.1
    refine Relation.ReflTransGen.head ⟨hx', hw', ?_⟩ (ih hxw.2.1 hw' h2.symm)
    rcases hxw.2.2 with e | e
    · left
      rw [h1, e]
    · right
      rw [← (hc.config hx hxw.2.1 hx' hw' h1.symm).2.1]
      exact e

omit [DecidableEq R] in
/-- **Reachability depends only on the colour of the pair** (from Exercise 2.16 (a)). -/
theorem IsCoh2On.reach_iff {S : Finset R} {c : R → R → ℕ} (hc : IsCoh2On S c) (r : ℕ)
    {x y x' y' : R} (hx : x ∈ S) (hy : y ∈ S) (hx' : x' ∈ S) (hy' : y' ∈ S)
    (h : c x y = c x' y') :
    Relation.ReflTransGen (Adj S c r) x y ↔ Relation.ReflTransGen (Adj S c r) x' y' :=
  ⟨fun h' => hc.reach_of_eq r h' hx hy hx' hy' h,
    fun h' => hc.reach_of_eq r h' hx' hy' hx hy h.symm⟩

omit [DecidableEq R] in
/-- A sum over `z ∈ S` of a function of `c x z` and of a colour-determined function `H z y`
depends only on the colour of `(x, y)`. -/
theorem IsCoh2On.sum_colour_eq {S : Finset R} {c : R → R → ℕ} (hc : IsCoh2On S c)
    {H : R → R → ℕ}
    (hH : ∀ z ∈ S, ∀ y ∈ S, ∀ z' ∈ S, ∀ y' ∈ S, c z y = c z' y' → H z y = H z' y') (r : ℕ)
    {x y x' y' : R} (hx : x ∈ S) (hy : y ∈ S) (hx' : x' ∈ S) (hy' : y' ∈ S)
    (h : c x y = c x' y') :
    ∑ z ∈ S, (if c x z = r then H z y else 0) = ∑ z ∈ S, (if c x' z = r then H z y' else 0) := by
  classical
  set h₁ : R → ℕ := fun z => if c x z = r then H z y else 0 with hh₁
  set h₂ : R → ℕ := fun z => if c x' z = r then H z y' else 0 with hh₂
  set T := S.image h₁ ∪ S.image h₂
  have m₁ : ∀ z ∈ S, h₁ z ∈ T := fun z hz => mem_union_left _ (mem_image_of_mem _ hz)
  have m₂ : ∀ z ∈ S, h₂ z ∈ T := fun z hz => mem_union_right _ (mem_image_of_mem _ hz)
  have fib : ∀ (g : R → ℕ), (∀ z ∈ S, g z ∈ T) →
      ∑ z ∈ S, g z = ∑ v ∈ T, (S.filter fun z => g z = v).card * v := by
    intro g hg
    calc ∑ z ∈ S, g z = ∑ v ∈ T, ∑ z ∈ S with g z = v, v :=
          (sum_fiberwise_of_maps_to' hg (fun v => v)).symm
      _ = _ := sum_congr rfl fun v _ => by rw [sum_const, smul_eq_mul]
  -- the fibres of `h₁` are sets defined by a predicate on the two colours
  let P : ℕ → ℕ → ℕ → Prop := fun v a b =>
    (a = r ∧ ∃ z₀ ∈ S, ∃ y₀ ∈ S, c z₀ y₀ = b ∧ H z₀ y₀ = v) ∨ (a ≠ r ∧ v = 0)
  have key : ∀ (u w : R), u ∈ S → w ∈ S → ∀ v, ∀ z ∈ S,
      ((if c u z = r then H z w else 0) = v ↔ P v (c u z) (c z w)) := by
    intro u w _ hw v z hz
    by_cases hr : c u z = r
    · simp only [hr, ↓reduceIte, true_and, ne_eq, not_true_eq_false, false_and, or_false, P]
      constructor
      · rintro rfl
        exact ⟨z, hz, w, hw, rfl, rfl⟩
      · rintro ⟨z₀, hz₀, y₀, hy₀, e, rfl⟩
        exact hH z hz w hw z₀ hz₀ y₀ hy₀ e.symm
    · simp only [hr, ↓reduceIte, false_and, ne_eq, not_false_eq_true, true_and, false_or, P]
      exact eq_comm
  rw [fib h₁ m₁, fib h₂ m₂]
  refine sum_congr rfl fun v _ => ?_
  congr 1
  rw [filter_congr fun z hz => key x y hx hy v z hz,
    filter_congr fun z hz => key x' y' hx' hy' v z hz]
  exact hc.card_filter_pred hx hy hx' hy' h (P v)

/-- The number of walks `x = x₀, x₁, …, x_k = y` in `S` with `c xᵢ₋₁ xᵢ = rᵢ` for the colour
sequence `rs = [r₁, …, r_k]` (`k ≥ 1`; the empty sequence counts nothing). -/
def walkCount (S : Finset R) (c : R → R → ℕ) : List ℕ → R → R → ℕ
  | [], _, _ => 0
  | [r], x, y => if c x y = r then 1 else 0
  | r :: r' :: rs, x, y => ∑ z ∈ S, if c x z = r then walkCount S c (r' :: rs) z y else 0

omit [DecidableEq R] in
/-- **Walk counts depend only on the colour of the pair** (Exercise 2.16 (a)): the number of
walks with a prescribed colour sequence from `x` to `y` is determined by `c x y`. -/
theorem IsCoh2On.walkCount_eq {S : Finset R} {c : R → R → ℕ} (hc : IsCoh2On S c)
    (rs : List ℕ) {x y x' y' : R} (hx : x ∈ S) (hy : y ∈ S) (hx' : x' ∈ S) (hy' : y' ∈ S)
    (h : c x y = c x' y') : walkCount S c rs x y = walkCount S c rs x' y' := by
  induction rs generalizing x y x' y' with
  | nil => rfl
  | cons r rs ih =>
    cases rs with
    | nil => simp only [walkCount, h]
    | cons r' rs =>
      simp only [walkCount]
      exact hc.sum_colour_eq (fun z hz w hw z' hz' w' hw' e => ih hz hw hz' hw' e) r
        hx hy hx' hy' h

/-- **The components of a colour graph have equal sizes** (Exercise 2.16 (b)). -/
theorem IsCoh2On.card_comp_eq {S : Finset R} {c : R → R → ℕ} (hc : IsCoh2On S c)
    (hh : IsHomog S c) (r : ℕ) {x y : R} (hx : x ∈ S) (hy : y ∈ S) :
    (comp S c r x).card = (comp S c r y).card := by
  classical
  let P : ℕ → ℕ → Prop := fun a _ =>
    ∃ p ∈ S, ∃ q ∈ S, c p q = a ∧ Relation.ReflTransGen (Adj S c r) p q
  have key : ∀ u ∈ S, comp S c r u = S.filter fun z => P (c u z) (c z u) := by
    intro u hu
    ext z
    rw [mem_comp, mem_filter]
    constructor
    · rintro ⟨-, huz⟩
      have hz : z ∈ S := comp_subset S c r u (mem_comp.2 ⟨hu, huz⟩)
      exact ⟨hz, u, hu, z, hz, rfl, huz⟩
    · rintro ⟨hz, p, hp, q, hq, e, hpq⟩
      exact ⟨hu, hc.reach_of_eq r hpq hp hq hu hz e⟩
  rw [key x hx, key y hy]
  exact hc.card_filter_pred hx hx hy hy (hh x hx y hy) P

/-- The component of an off-diagonal colour has at least two points. -/
theorem IsCoh2On.two_le_card_comp {S : Finset R} {c : R → R → ℕ} (hc : IsCoh2On S c)
    (hh : IsHomog S c) {r : ℕ} (hr : r ∈ offCols S c) {x : R} (hx : x ∈ S) :
    2 ≤ (comp S c r x).card := by
  obtain ⟨⟨p, q⟩, hpq, rfl⟩ := mem_image.1 hr
  simp only [mem_filter, mem_product] at hpq
  have hdeg := hc.outdeg hpq.1.1 hx (hh p hpq.1.1 x hx) (c p q)
  have hpos : 0 < (S.filter fun z => c x z = c p q).card := by
    rw [← hdeg]
    exact card_pos.2 ⟨q, mem_filter.2 ⟨hpq.1.2, rfl⟩⟩
  obtain ⟨w, hw⟩ := card_pos.1 hpos
  rw [mem_filter] at hw
  have hxw : x ≠ w := fun e => hpq.2 ((hc.config hx hw.1 hpq.1.1 hpq.1.2 hw.2).1.1 e)
  have h1 : x ∈ comp S c (c p q) x := self_mem_comp hx
  have h2 : w ∈ comp S c (c p q) x :=
    mem_comp.2 ⟨hx, Relation.ReflTransGen.single ⟨hx, hw.1, Or.inl hw.2⟩⟩
  exact one_lt_card.2 ⟨x, h1, w, h2, hxw⟩

/-- A component of a disconnected colour graph has at most half of the points. -/
theorem IsCoh2On.two_mul_card_comp_le {S : Finset R} {c : R → R → ℕ} (hc : IsCoh2On S c)
    (hh : IsHomog S c) (r : ℕ) {x : R} (hx : x ∈ S) (hne : comp S c r x ≠ S) :
    2 * (comp S c r x).card ≤ S.card := by
  obtain ⟨y, hyS, hy⟩ : ∃ y ∈ S, y ∉ comp S c r x := by
    by_contra h
    push Not at h
    exact hne (Subset.antisymm (comp_subset S c r x) h)
  have hdisj : Disjoint (comp S c r x) (comp S c r y) := by
    rw [disjoint_left]
    intro z hzx hzy
    apply hy
    have e : comp S c r y = comp S c r x := (comp_eq_of_mem hzy).symm.trans (comp_eq_of_mem hzx)
    rw [← e]
    exact self_mem_comp hyS
  have h1 := card_union_of_disjoint hdisj
  have h2 := card_le_card (union_subset (comp_subset S c r x) (comp_subset S c r y))
  rw [hc.card_comp_eq hh r hyS hx] at h1
  omega

omit [DecidableEq R] in
theorem eq_iff_card_inter [DecidableEq R] {A B : Finset R} :
    A = B ↔ (A ∩ B).card = A.card ∧ (A ∩ B).card = B.card := by
  constructor
  · rintro rfl
    simp
  · rintro ⟨h1, h2⟩
    have e1 : A ∩ B = A := eq_of_subset_of_card_le inter_subset_left h1.symm.le
    have e2 : A ∩ B = B := eq_of_subset_of_card_le inter_subset_right h2.symm.le
    rw [← e1, e2]

/-- **Twins with respect to a vertex colour class are determined by the colour of the pair**
(Exercise 5.6), for a single colour `g`. -/
theorem IsCoh2On.twin_iff {S : Finset R} {c : R → R → ℕ} (hc : IsCoh2On S c) (κ g : ℕ)
    {x x' z z' : R} (hx : x ∈ S) (hx' : x' ∈ S) (hz : z ∈ S) (hz' : z' ∈ S)
    (h : c x x' = c z z') :
    (∀ y ∈ S, c y y = κ → (c x y = g ↔ c x' y = g)) ↔
      (∀ y ∈ S, c y y = κ → (c z y = g ↔ c z' y = g)) := by
  classical
  let K : ℕ → Prop := fun a => ∃ p ∈ S, ∃ q ∈ S, c p q = a ∧ c q q = κ
  let G : ℕ → Prop := fun b => ∃ p ∈ S, ∃ q ∈ S, c q p = b ∧ c p q = g
  have hK : ∀ u ∈ S, ∀ y ∈ S, (c y y = κ ↔ K (c u y)) := by
    intro u hu y hy
    constructor
    · intro e
      exact ⟨u, hu, y, hy, rfl, e⟩
    · rintro ⟨p, hp, q, hq, e, hqk⟩
      rw [← (hc.config hp hq hu hy e).2.2.2]
      exact hqk
  have hG : ∀ u ∈ S, ∀ y ∈ S, (c u y = g ↔ G (c y u)) := by
    intro u hu y hy
    constructor
    · intro e
      exact ⟨u, hu, y, hy, rfl, e⟩
    · rintro ⟨p, hp, q, hq, e, hpq⟩
      rw [← (hc.config hq hp hy hu e).2.1]
      exact hpq
  let N : R → Finset R := fun u => S.filter fun y => c y y = κ ∧ c u y = g
  have htw : ∀ u u', (∀ y ∈ S, c y y = κ → (c u y = g ↔ c u' y = g)) ↔ N u = N u' := by
    intro u u'
    constructor
    · intro H
      ext y
      simp only [N, mem_filter]
      constructor
      · rintro ⟨hy, hk, hg⟩
        exact ⟨hy, hk, (H y hy hk).1 hg⟩
      · rintro ⟨hy, hk, hg⟩
        exact ⟨hy, hk, (H y hy hk).2 hg⟩
    · intro H y hy hk
      rw [Finset.ext_iff] at H
      have := H y
      simp only [N, mem_filter] at this
      constructor
      · intro hg
        exact (this.1 ⟨hy, hk, hg⟩).2.2
      · intro hg
        exact (this.2 ⟨hy, hk, hg⟩).2.2
  have hinter : ∀ u ∈ S, ∀ u' ∈ S,
      N u ∩ N u' = S.filter fun y => K (c u y) ∧ c u y = g ∧ G (c y u') := by
    intro u hu u' hu'
    ext y
    simp only [N, mem_inter, mem_filter]
    constructor
    · rintro ⟨⟨hy, hk, hg⟩, -, -, hg'⟩
      exact ⟨hy, (hK u hu y hy).1 hk, hg, (hG u' hu' y hy).1 hg'⟩
    · rintro ⟨hy, hk, hg, hg'⟩
      have hk' := (hK u hu y hy).2 hk
      exact ⟨⟨hy, hk', hg⟩, hy, hk', (hG u' hu' y hy).2 hg'⟩
  have hN : ∀ u ∈ S, N u = S.filter fun y => K (c u y) ∧ c u y = g := by
    intro u hu
    ext y
    simp only [N, mem_filter]
    constructor
    · rintro ⟨hy, hk, hg⟩
      exact ⟨hy, (hK u hu y hy).1 hk, hg⟩
    · rintro ⟨hy, hk, hg⟩
      exact ⟨hy, (hK u hu y hy).2 hk, hg⟩
  have hcfg := hc.config hx hx' hz hz' h
  have hI : (N x ∩ N x').card = (N z ∩ N z').card := by
    rw [hinter x hx x' hx', hinter z hz z' hz']
    exact hc.card_filter_pred hx hx' hz hz' h (fun a b => K a ∧ a = g ∧ G b)
  have hNx : (N x).card = (N z).card := by
    rw [hN x hx, hN z hz]
    exact hc.card_filter_pred hx hx hz hz hcfg.2.2.1 (fun a _ => K a ∧ a = g)
  have hNx' : (N x').card = (N z').card := by
    rw [hN x' hx', hN z' hz']
    exact hc.card_filter_pred hx' hx' hz' hz' hcfg.2.2.2 (fun a _ => K a ∧ a = g)
  rw [htw, htw, eq_iff_card_inter, eq_iff_card_inter, hI, hNx, hNx']

/-- Twins with respect to all colours into a vertex colour class are determined by the colour
of the pair (Exercise 5.6). -/
theorem IsCoh2On.twinAll_iff {S : Finset R} {c : R → R → ℕ} (hc : IsCoh2On S c) (κ : ℕ)
    {x x' z z' : R} (hx : x ∈ S) (hx' : x' ∈ S) (hz : z ∈ S) (hz' : z' ∈ S)
    (h : c x x' = c z z') :
    (∀ y ∈ S, c y y = κ → c x y = c x' y) ↔ (∀ y ∈ S, c y y = κ → c z y = c z' y) := by
  have key : ∀ u u', (∀ y ∈ S, c y y = κ → c u y = c u' y) ↔
      ∀ g, ∀ y ∈ S, c y y = κ → (c u y = g ↔ c u' y = g) := by
    intro u u'
    constructor
    · intro H g y hy hk
      rw [H y hy hk]
    · intro H y hy hk
      exact (H (c u' y) y hy hk).2 rfl
  rw [key, key]
  exact forall_congr' fun g => hc.twin_iff κ g hx hx' hz hz' h

/-- A green edge into a component of a colour graph on a vertex colour class transports along
pairs of the same colour. -/
theorem IsCoh2On.exists_comp_of_eq {S : Finset R} {c : R → R → ℕ} (hc : IsCoh2On S c)
    (κ₂ red green : ℕ) {x y x' y' : R} (hx : x ∈ S) (hy : y ∈ S) (hx' : x' ∈ S)
    (hy' : y' ∈ S) (h : c x y = c x' y')
    (hD : ∃ z ∈ comp (S.filter fun w => c w w = κ₂) c red y, c x z = green) :
    ∃ z ∈ comp (S.filter fun w => c w w = κ₂) c red y', c x' z = green := by
  set C₂ := S.filter fun w => c w w = κ₂ with hC₂def
  have hC₂ : IsCoh2On C₂ c := hc.subset (filter_subset _ _) fun a ha b hb e =>
    mem_filter.2 ⟨hb, e ▸ (mem_filter.1 ha).2⟩
  obtain ⟨z, hz, hxz⟩ := hD
  obtain ⟨hyC, hyz⟩ := mem_comp.1 hz
  have hzC := comp_subset C₂ c red y hz
  have hzS := (mem_filter.1 hzC).1
  obtain ⟨z', hz', h1, h2⟩ := hc.transport hx hy hx' hy' h hzS
  have hy'C : y' ∈ C₂ := by
    refine mem_filter.2 ⟨hy', ?_⟩
    rw [← (hc.config hx hy hx' hy' h).2.2.2]
    exact (mem_filter.1 hyC).2
  have hz'C : z' ∈ C₂ := by
    refine mem_filter.2 ⟨hz', ?_⟩
    rw [(hc.config hz' hy' hzS hy h2).2.2.1]
    exact (mem_filter.1 hzC).2
  have e : c y z = c y' z' := (hc.config hzS hy hz' hy' h2.symm).2.1
  refine ⟨z', mem_comp.2 ⟨hy'C, hC₂.reach_of_eq red hyz hyC hzC hy'C hz'C e⟩, ?_⟩
  rw [h1, hxz]

/-- **The contraction of a colour graph is semiregular** (Exercise 2.18), on the side of the
blocks: let `C₂ = {y ∈ S | c y y = κ₂}` and `red` a colour. The number of `x ∈ S` of vertex
colour `κ₁` with a `green` edge into the `red`-component of `y ∈ C₂` does not depend on `y`. -/
theorem IsCoh2On.contract_deg_blocks {S : Finset R} {c : R → R → ℕ} (hc : IsCoh2On S c)
    (κ₁ κ₂ red green : ℕ) {y y' : R} (hy : y ∈ S) (hy' : y' ∈ S) (hyk : c y y = κ₂)
    (hy'k : c y' y' = κ₂) :
    (S.filter fun x => c x x = κ₁ ∧
        ∃ z ∈ comp (S.filter fun w => c w w = κ₂) c red y, c x z = green).card =
      (S.filter fun x => c x x = κ₁ ∧
        ∃ z ∈ comp (S.filter fun w => c w w = κ₂) c red y', c x z = green).card := by
  classical
  let K₁ : ℕ → Prop := fun b => ∃ p ∈ S, ∃ q ∈ S, c p q = b ∧ c p p = κ₁
  let Dc : ℕ → Prop := fun b => ∃ p ∈ S, ∃ q ∈ S, c p q = b ∧
    ∃ z ∈ comp (S.filter fun w => c w w = κ₂) c red q, c p z = green
  have key : ∀ u ∈ S, (S.filter fun x => c x x = κ₁ ∧
      ∃ z ∈ comp (S.filter fun w => c w w = κ₂) c red u, c x z = green) =
        S.filter fun x => K₁ (c x u) ∧ Dc (c x u) := by
    intro u hu
    refine filter_congr fun x hx => ?_
    constructor
    · rintro ⟨hk, hD⟩
      exact ⟨⟨x, hx, u, hu, rfl, hk⟩, x, hx, u, hu, rfl, hD⟩
    · rintro ⟨⟨p, hp, q, hq, e, hk⟩, ⟨p', hp', q', hq', e', hD⟩⟩
      refine ⟨?_, hc.exists_comp_of_eq κ₂ red green hp' hq' hx hu e' hD⟩
      rw [← (hc.config hp hq hx hu e).2.2.1]
      exact hk
  rw [key y hy, key y' hy']
  exact hc.card_filter_pred hy hy hy' hy' (hyk.trans hy'k.symm) (fun _ b => K₁ b ∧ Dc b)

/-- **The contraction of a colour graph is semiregular** (Exercise 2.18), on the side of the
points: the number of `red`-components of `C₂` that a point `x` of vertex colour `κ₁` reaches
by a `green` edge does not depend on `x`. -/
theorem IsCoh2On.contract_deg_points {S : Finset R} {c : R → R → ℕ} (hc : IsCoh2On S c)
    (κ₂ red green : ℕ) {x x' : R} (hx : x ∈ S) (hx' : x' ∈ S) (h : c x x = c x' x') :
    (((S.filter fun w => c w w = κ₂).image (comp (S.filter fun w => c w w = κ₂) c red)).filter
        fun B => ∃ z ∈ B, c x z = green).card =
      (((S.filter fun w => c w w = κ₂).image (comp (S.filter fun w => c w w = κ₂) c red)).filter
        fun B => ∃ z ∈ B, c x' z = green).card := by
  classical
  set C₂ := S.filter fun w => c w w = κ₂ with hC₂def
  have hC₂ : IsCoh2On C₂ c := hc.subset (filter_subset _ _) fun a ha b hb e =>
    mem_filter.2 ⟨hb, e ▸ (mem_filter.1 ha).2⟩
  set Bl := C₂.image (comp C₂ c red) with hBl
  let reached : R → Finset (Finset R) := fun u => Bl.filter fun B => ∃ z ∈ B, c u z = green
  -- the green neighbours in `C₂` are partitioned by the blocks they meet
  have hsplit : ∀ u, (C₂.filter fun z => c u z = green).card =
      ∑ B ∈ reached u, (B.filter fun z => c u z = green).card := by
    intro u
    have e : C₂.filter (fun z => c u z = green) =
        (reached u).biUnion fun B => B.filter fun z => c u z = green := by
      ext z
      simp only [mem_filter, mem_biUnion, reached, hBl, mem_image]
      constructor
      · rintro ⟨hz, hg⟩
        exact ⟨comp C₂ c red z, ⟨⟨z, hz, rfl⟩, z, self_mem_comp hz, hg⟩, self_mem_comp hz, hg⟩
      · rintro ⟨B, ⟨⟨y, hy, rfl⟩, -⟩, hzB, hg⟩
        exact ⟨comp_subset C₂ c red y hzB, hg⟩
    rw [e, card_biUnion]
    intro B₁ hB₁ B₂ hB₂ hne
    rw [mem_coe] at hB₁ hB₂
    simp only [reached, mem_filter, hBl, mem_image] at hB₁ hB₂
    obtain ⟨⟨y₁, -, rfl⟩, -⟩ := hB₁
    obtain ⟨⟨y₂, -, rfl⟩, -⟩ := hB₂
    rw [Function.onFun, disjoint_left]
    intro z hz₁ hz₂
    apply hne
    have h₁ := mem_filter.1 hz₁
    have h₂ := mem_filter.1 hz₂
    rw [← comp_eq_of_mem h₁.1, comp_eq_of_mem h₂.1]
  -- the number of green neighbours in `C₂` depends only on the vertex colour
  have hn : (C₂.filter fun z => c x z = green).card = (C₂.filter fun z => c x' z = green).card := by
    let K₂ : ℕ → Prop := fun a => ∃ p ∈ S, ∃ q ∈ S, c p q = a ∧ c q q = κ₂
    have key : ∀ u ∈ S, C₂.filter (fun z => c u z = green) =
        S.filter fun z => K₂ (c u z) ∧ c u z = green := by
      intro u hu
      rw [hC₂def, filter_filter]
      refine filter_congr fun z hz => ?_
      constructor
      · rintro ⟨hk, hg⟩
        exact ⟨⟨u, hu, z, hz, rfl, hk⟩, hg⟩
      · rintro ⟨⟨p, hp, q, hq, e, hk⟩, hg⟩
        refine ⟨?_, hg⟩
        rw [← (hc.config hp hq hu hz e).2.2.2]
        exact hk
    rw [key x hx, key x' hx']
    exact hc.card_filter_pred hx hx hx' hx' h (fun a _ => K₂ a ∧ a = green)
  -- a block reached by a green edge contains a number of green neighbours that depends only on
  -- the colour green
  let RP : ℕ → Prop := fun b => ∃ p ∈ C₂, ∃ q ∈ C₂, c p q = b ∧
    Relation.ReflTransGen (Adj C₂ c red) p q
  have hblock : ∀ u ∈ S, ∀ y ∈ C₂, c u y = green →
      (comp C₂ c red y).filter (fun z => c u z = green) =
        S.filter fun z => c u z = green ∧ RP (c z y) := by
    intro u hu y hy hg
    ext z
    simp only [mem_filter]
    constructor
    · rintro ⟨hz, hgz⟩
      have hzC := comp_subset C₂ c red y hz
      exact ⟨(mem_filter.1 hzC).1, hgz, z, hzC, y, hy, rfl,
        reflTransGen_adj_symm (mem_comp.1 hz).2⟩
    · rintro ⟨hzS, hgz, p, hp, q, hq, e, hpq⟩
      have hzC : z ∈ C₂ := by
        refine mem_filter.2 ⟨hzS, ?_⟩
        rw [(hc.config hzS (mem_filter.1 hy).1 (mem_filter.1 hp).1 (mem_filter.1 hq).1
          e.symm).2.2.1]
        exact (mem_filter.1 hp).2
      exact ⟨mem_comp.2 ⟨hy, reflTransGen_adj_symm (hC₂.reach_of_eq red hpq hp hq hzC hy e)⟩,
        hgz⟩
  have hq : ∀ u ∈ S, ∀ y ∈ C₂, ∀ u' ∈ S, ∀ y' ∈ C₂, c u y = green → c u' y' = green →
      ((comp C₂ c red y).filter fun z => c u z = green).card =
        ((comp C₂ c red y').filter fun z => c u' z = green).card := by
    intro u hu y hy u' hu' y' hy' hg hg'
    rw [hblock u hu y hy hg, hblock u' hu' y' hy' hg']
    exact hc.card_filter_pred hu (mem_filter.1 hy).1 hu' (mem_filter.1 hy').1 (hg.trans hg'.symm)
      (fun a b => a = green ∧ RP b)
  by_cases h0 : (C₂.filter fun z => c x z = green).card = 0
  · -- no green neighbours: no block is reached
    have hr0 : ∀ u, (C₂.filter fun z => c u z = green).card = 0 → (reached u).card = 0 := by
      intro u hu
      rw [card_eq_zero, eq_empty_iff_forall_notMem]
      intro B hB
      simp only [reached, mem_filter, hBl, mem_image] at hB
      obtain ⟨⟨y, -, rfl⟩, z, hz, hg⟩ := hB
      rw [card_eq_zero, eq_empty_iff_forall_notMem] at hu
      exact hu z (mem_filter.2 ⟨comp_subset C₂ c red y hz, hg⟩)
    show (reached x).card = (reached x').card
    rw [hr0 x h0, hr0 x' (hn ▸ h0)]
  · obtain ⟨y₀, hy₀⟩ := card_pos.1 (Nat.pos_of_ne_zero h0)
    rw [mem_filter] at hy₀
    set Q := ((comp C₂ c red y₀).filter fun z => c x z = green).card with hQ
    have hQpos : 0 < Q := card_pos.2 ⟨y₀, mem_filter.2 ⟨self_mem_comp hy₀.1, hy₀.2⟩⟩
    have hcount : ∀ u ∈ S, (C₂.filter fun z => c u z = green).card = (reached u).card * Q := by
      intro u hu
      rw [hsplit u, ← smul_eq_mul, ← sum_const]
      refine sum_congr rfl fun B hB => ?_
      simp only [reached, mem_filter, hBl, mem_image] at hB
      obtain ⟨⟨y, -, rfl⟩, z, hz, hg⟩ := hB
      rw [← comp_eq_of_mem hz]
      have hzC := comp_subset C₂ c red y hz
      exact hq u hu z hzC x hx y₀ hy₀.1 hg hy₀.2
    have e1 := hcount x hx
    have e2 := hcount x' hx'
    show (reached x).card = (reached x').card
    rw [hn] at e1
    exact Nat.eq_of_mul_eq_mul_right hQpos (e1.symm.trans e2)

/-- **A common neighbour in the complement** (Exercise B.7): in a uniprimitive configuration,
two distinct points joined by the colour `r` have a common neighbour `y` with
`c x y ≠ r` and `c y z ≠ r`. -/
theorem IsUniprimitive.exists_common {S : Finset R} {c : R → R → ℕ} (hc : IsCoh2On S c)
    (hu : IsUniprimitive S c) {x z : R} (hx : x ∈ S) (hz : z ∈ S) (hxz : x ≠ z) :
    ∃ y ∈ S, c x y ≠ c x z ∧ c y z ≠ c x z := by
  by_contra hcon
  push Not at hcon
  set r := c x z with hr
  obtain ⟨⟨hh, hprim⟩, hncl⟩ := hu
  -- every `r`-pair has no common neighbour in the complement
  have hall : ∀ p ∈ S, ∀ q ∈ S, c p q = r → ∀ y ∈ S, c p y = r ∨ c y q = r := by
    intro p hp q hq hpq
    have e : (S.filter fun y => c x y ≠ r ∧ c y z ≠ r).card =
        (S.filter fun y => c p y ≠ r ∧ c y q ≠ r).card :=
      hc.card_filter_pred hx hz hp hq hpq.symm (fun a b => a ≠ r ∧ b ≠ r)
    have h0 : (S.filter fun y => c x y ≠ r ∧ c y z ≠ r) = ∅ := by
      rw [filter_eq_empty_iff]
      rintro y hy ⟨h1, h2⟩
      exact h2 (hcon y hy h1)
    rw [h0, card_empty, eq_comm, card_eq_zero, filter_eq_empty_iff] at e
    intro y hy
    by_contra hn
    push Not at hn
    exact e hy hn
  -- points outside the `r`-neighbourhood of `x` have the same `r`-neighbourhood
  have hN : ∀ y ∈ S, c x y ≠ r →
      (S.filter fun w => c y w = r) = S.filter fun w => c x w = r := by
    intro y hy hyr
    symm
    apply eq_of_subset_of_card_le
    · intro w hw
      rw [mem_filter] at hw ⊢
      refine ⟨hw.1, ?_⟩
      rcases hall x hx w hw.1 hw.2 y hy with h | h
      · exact absurd h hyr
      · exact h
    · rw [hc.outdeg hy hx (hh y hy x hx) r]
  -- the complement of the `r`-neighbourhood is closed under the other colours
  have hclosed : ∀ q, q ≠ r → q ≠ c z x → ∀ u v, Adj S c q u v → c x u ≠ r → c x v ≠ r := by
    rintro q hq1 hq2 u v ⟨hu, hv, hadj⟩ hur hvr
    have huv : c u v = r := by
      have hv' : v ∈ S.filter fun w => c x w = r := mem_filter.2 ⟨hv, hvr⟩
      rw [← hN u hu hur] at hv'
      exact (mem_filter.1 hv').2
    rcases hadj with e | e
    · exact hq1 (e.symm.trans huv)
    · exact hq2 (e.symm.trans (hc.config hu hv hx hz huv).2.1)
  have hxx : c x x ≠ r := fun e => hxz ((hc.config hx hx hx hz e).1.1 rfl)
  have hU : ∀ q ∈ offCols S c, q = r ∨ q = c z x := by
    intro q hq
    by_contra hn
    push Not at hn
    have key : ∀ y, Relation.ReflTransGen (Adj S c q) x y → c x y ≠ r := by
      intro y hy
      induction hy with
      | refl => exact hxx
      | tail _ hab ih => exact hclosed q hn.1 hn.2 _ _ hab ih
    exact key z (hprim q hq x hx z hz) rfl
  by_cases hrr : c z x = r
  · -- all off-diagonal colours are `r`: a clique
    apply hncl
    have hoff : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → c u v = r := by
      intro u hu v hv huv
      have h1 : c u v ∈ offCols S c :=
        mem_image.2 ⟨(u, v), mem_filter.2 ⟨mem_product.2 ⟨hu, hv⟩, huv⟩, rfl⟩
      rcases hU _ h1 with e | e
      · exact e
      · rw [e, hrr]
    intro u hu v hv u' hu' v' hv' huv hu'v'
    rw [hoff u hu v hv huv, hoff u' hu' v' hv' hu'v']
  · -- `r` is not symmetric: count
    have hsub1 : (S.filter fun y => c x y ≠ r) ⊆ S.filter fun y => c y z = r := by
      intro y hy
      rw [mem_filter] at hy ⊢
      exact ⟨hy.1, hcon y hy.1 hy.2⟩
    have hsub2 : insert x (S.filter fun y => c x y = c z x) ⊆ S.filter fun y => c x y ≠ r := by
      intro y hy
      rw [mem_insert] at hy
      rw [mem_filter]
      rcases hy with rfl | hy
      · exact ⟨hx, hxx⟩
      · rw [mem_filter] at hy
        exact ⟨hy.1, by rw [hy.2]; exact hrr⟩
    have hxnot : x ∉ S.filter fun y => c x y = c z x := by
      intro h
      rw [mem_filter] at h
      exact hxz ((hc.config hx hx hz hx h.2).1.1 rfl).symm
    have e1 : (S.filter fun y => c x y = c z x) = S.filter fun y => c y x = r := by
      ext y
      simp only [mem_filter]
      constructor
      · rintro ⟨hy, h⟩
        exact ⟨hy, (hc.config hx hy hz hx h).2.1⟩
      · rintro ⟨hy, h⟩
        exact ⟨hy, (hc.config hy hx hx hz h).2.1⟩
    have e2 := hc.card_in_eq_out hh hx hx r
    have e3 := hc.card_in_eq_out hh hz hx r
    have := card_le_card (hsub2.trans hsub1)
    rw [card_insert_of_notMem hxnot, e1, e2, e3] at this
    omega

end GraphIso.Coherent
