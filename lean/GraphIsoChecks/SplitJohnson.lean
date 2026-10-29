module

public import GraphIso.SplitJohnson.Main
meta import GraphIso.SplitJohnson.Main
import all Init.Data.Array.Basic
import all Init.Data.List.Sort.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Mathlib.Data.List.Sort

/-!
# Milestone 11 checks: Split-or-Johnson

Interpreter runs of the model procedures (each `#eval` throws on a failure). Colored partitions
are checked by deciding `IsColPart` field by field; Johnson embeddings and ideal points by
Boolean checks (`johnsonB`, `idealB`) that test the cell conditions arithmetically.

* **Theorem 5.3** (`soj`) on two uniprimitive configurations, given as strongly regular graphs
  (colours: diagonal, adjacent, non-adjacent):
  - the Petersen graph with `t = 6`: no colour class of `c x ·` has more than `6` points, so
    every leaf is the colouring by `c x ·` (`10` leaves);
  - the Clebsch graph (the folded `5`-cube, `srg(16, 5, 0, 2)`) with `t = 9`: the
    non-neighbours of `x` form the class of more than `t` points, and Bipartite
    Split-or-Johnson on `(non-neighbours, neighbours; adjacency)` recognizes the Johnson scheme
    `J(5, 2)` (each non-neighbour is adjacent to exactly two neighbours, and every pair occurs),
    so there are 16 leaves, all Johnson embeddings.

  Each leaf is checked to be valid (a colored `t`-partition of `Γ` or a Johnson embedding),
  the count is compared with the number of leaves, and canonicity is checked: for a relabelling
  `σ`, the leaves of `sojAt` at `σ x` on the relabelled input are the `σ`-images of the leaves
  at `x`.
* **Proposition 5.8** (`cohSoj`) on two orbital (hence coherent) configurations, checked by brute
  force to be coherent and to satisfy the hypotheses; every leaf is checked valid and the count
  at most `|C₂|`:
  - `Sym(5)` on the ordered pairs (`C₁`, 20 points) and the 2-subsets (`C₂`, 10 points) of
    `{0, …, 4}`: `X[C₁]` is imprimitive, and the leaf is the partition into the components of its
    least disconnected colour;
  - `Sym(7)` on the 3-subsets (`C₁`, 35 points) and the 2-subsets (`C₂`, 21 points) of
    `{0, …, 6}`: both restrictions are primitive, so the procedure chooses `y ∈ C₂` (21 leaves,
    each a bipartite graph `(L_violet(y), L_blue(y); violet)`).
* **Proposition 5.7** (`bsoj`) on incidence graphs of `k`-subsets against points, with the
  hypotheses of `bipartite_split_or_johnson` checked: the 3-subsets of a 7-set (`t = 19`) give
  one Johnson leaf `J(7, 3)`; the 2-subsets of a 6-set with one removed (`t = 8`) are not a
  Johnson scheme, and the base case gives `6! = 720` colourings by neighbourhoods. Every leaf is
  checked valid.

The deeper branches of Proposition 5.7 (the `d`-ary structure, the Design Lemma's choice,
Coherent Split-or-Johnson inside the recursion) are exercised only by the proofs: at sizes that
can be run, the base case `v² ≤ 27 ⌈log₂ 2t⌉³` applies whenever the Johnson test fails, and the
`d`-ary Weisfeiler–Leman step is a polynomial of degree about `6d`.
-/

@[expose] public section

namespace GraphIsoChecks.SplitJohnson

open GraphIso.SplitJohnson GraphIso.Coherent Finset

variable {α : Type} [DecidableEq α]

instance (V : Finset α) (t : ℕ) (p : CPart α) : Decidable (IsColPart V t p) :=
  decidable_of_iff ((∀ v ∈ V, v ∈ p.blk v) ∧ (∀ v ∈ V, p.blk v ⊆ V) ∧
      (∀ v ∈ V, ∀ w ∈ p.blk v, p.blk w = p.blk v) ∧ (∀ v ∈ V, ∀ w ∈ p.blk v, p.col w = p.col v) ∧
      (∀ v ∈ V, ∀ w ∈ V, p.col v = p.col w → (p.blk v).card = (p.blk w).card) ∧
      (∀ v ∈ V, (p.blk v).card = 1 → ∀ w ∈ V, p.col w = p.col v → w = v) ∧
      ∀ v ∈ V, (p.blk v).card ≤ t)
    ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩,
      fun h => ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7⟩⟩

/-- The cells of `Λ` are nonempty and pairwise disjoint, as arithmetic: no empty cell, and the
union has as many points as the cells together. (Quantifying over a `Finset` of `Finset`s with
`decide` is very slow in compiled code on this toolchain, so the checks avoid it.) -/
def cellsB (Λ : Finset (Finset α)) : Bool :=
  decide ((Λ.filter fun a => a.card = 0).card = 0) &&
    decide ((Λ.biUnion id).card = ∑ a ∈ Λ, a.card)

/-- A Johnson embedding, as a Boolean: `V₀ ⊆ V`, `t < |V₀|`, `2 ≤ s`, `2s ≤ |Λ|`, the cells are
nonempty and pairwise disjoint, `f` maps `V₀` into the `s`-subsets of `Λ`, injectively, and its
image has `C(|Λ|, s)` elements (so it is all of them). -/
def johnsonB (V : Finset α) (t : ℕ) (J : JEmb α) : Bool :=
  decide (J.V0 ⊆ V ∧ t < J.V0.card ∧ 2 ≤ J.s ∧ 2 * J.s ≤ J.Λ.card) && cellsB J.Λ &&
    decide (∀ v ∈ J.V0, (J.f v ∪ J.Λ).card = J.Λ.card ∧ (J.f v).card = J.s) &&
    decide ((J.V0.image J.f).card = J.V0.card) &&
    decide ((J.V0.image J.f).card = J.Λ.card.choose J.s)

/-- Validity of a leaf, as a Boolean. -/
def validB (V : Finset α) (t : ℕ) : Option (Out α) → Bool
  | some (Sum.inl p) => decide (IsColPart V t p)
  | some (Sum.inr J) => johnsonB V t J
  | none => false

/-- Every reachable leaf satisfies `P`, as a Boolean. -/
def allB {C O : Type} (P : O → Bool) : CTree C O → Bool
  | .leaf o => P o
  | .node S k => decide (∀ c ∈ S, allB P (k c) = true)

theorem allB_iff {C O : Type} {P : O → Bool} {t : CTree C O} :
    allB P t = true ↔ t.AllLeaves fun o => P o = true := by
  induction t with
  | leaf o => rfl
  | node S k ih => simp only [allB, decide_eq_true_eq, CTree.AllLeaves, ih]

/-! ### Inputs -/

/-- A graph on `Fin n` as a configuration: `0` on the diagonal, `1` on edges, `2` otherwise. -/
def graphCfg {n : ℕ} (adj : Fin n → Fin n → Bool) (x y : Fin n) : ℕ :=
  if x = y then 0 else if adj x y then 1 else 2

/-- The Petersen graph: 2-subsets of `{0, …, 4}`, adjacent when disjoint. -/
def petersenPts : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)]

def petersen (x y : Fin 10) : Bool :=
  let a := petersenPts.getD x.val (0, 0)
  let b := petersenPts.getD y.val (0, 0)
  a.1 ≠ b.1 && a.1 ≠ b.2 && a.2 ≠ b.1 && a.2 ≠ b.2

/-- The Clebsch graph: `𝔽₂⁴`, adjacent when the difference has weight `1` or `4`. -/
def clebsch (x y : Fin 16) : Bool :=
  let w := (List.range 4).countP fun i => Nat.testBit (x.val ^^^ y.val) i
  w = 1 || w = 4

/-- Uniprimitivity by computation: homogeneous, every off-diagonal colour graph has a single
component (`comp`), and not a clique. -/
def uniprimB {n : ℕ} (c : Fin n → Fin n → ℕ) : Bool :=
  decide ((∀ x ∈ (univ : Finset (Fin n)), ∀ y ∈ (univ : Finset (Fin n)), c x x = c y y) ∧
    (∀ r ∈ offCols (univ : Finset (Fin n)) c, ∀ x ∈ (univ : Finset (Fin n)),
      comp (univ : Finset (Fin n)) c r x = (univ : Finset (Fin n))) ∧
    ¬ IsClique c (univ : Finset (Fin n)))

theorem uniprimB_spec {n : ℕ} {c : Fin n → Fin n → ℕ} (h : uniprimB c = true) :
    IsUniprimitive univ c := by
  simp only [uniprimB, decide_eq_true_eq] at h
  obtain ⟨hh, hc, hcl⟩ := h
  refine ⟨⟨hh, fun r hr x hx y _ => (mem_comp.1 ?_).2⟩, hcl⟩
  rw [hc r hr x hx]
  exact mem_univ y

/-- A classical structure is coherent, by computation: every pair gets the signature
`(c y x, c x x, c y y, [x = y], sorted list of (c x z, c z y) over z)`, and pairs of one colour
must have one signature. -/
def coh2B {n : ℕ} (c : Fin n → Fin n → ℕ) : Bool :=
  let sig (x y : Fin n) : List ℕ :=
    [c y x, c x x, c y y, if x = y then 1 else 0] ++
      ((List.finRange n).map fun z => Nat.pair (c x z) (c z y)).mergeSort (· ≤ ·)
  let L := ((List.finRange n).flatMap fun x => (List.finRange n).map fun y =>
    c x y :: sig x y).mergeSort fun a b => decide (a ≤ b)
  (L.zip L.tail).all fun p => p.1.headD 0 != p.2.headD 0 || p.1 == p.2

/-! ### Theorem 5.3 -/

instance {n : ℕ} : DecidableEq (CPart (Fin n)) := fun p q =>
  decidable_of_iff (p.col = q.col ∧ p.blk = q.blk) (by cases p; cases q; simp)

instance {n : ℕ} : DecidableEq (JEmb (Fin n)) := fun J K =>
  decidable_of_iff (J.V0 = K.V0 ∧ J.Λ = K.Λ ∧ J.s = K.s ∧ J.f = K.f)
    (by cases J; cases K; simp)


/-- Check `soj` on a configuration: the input is coherent and uniprimitive (brute force), every
leaf is valid, the count is the number of leaves, and canonicity holds at every `x` for `σ`. -/
def checkSoj {n : ℕ} (name : String) (c : Fin n → Fin n → ℕ) (t : ℕ) (σ : Equiv.Perm (Fin n))
    (expected : ℕ) : IO Unit := do
  unless uniprimB c && coh2B c do
    throw <| IO.userError s!"{name}: input not a uniprimitive coherent configuration"
  let T := soj c t
  unless allB (validB univ t) T do throw <| IO.userError s!"{name}: invalid leaf"
  unless T.count = expected do
    throw <| IO.userError s!"{name}: count {T.count}, expected {expected}"
  for x in (List.finRange n) do
    let L := (sojAt c t x).leaves
    let L' := (sojAt (relab2 σ c) t (σ x)).leaves
    unless L.card * n = expected do throw <| IO.userError s!"{name}: leaves at {x}"
    unless L' = L.image (σ • ·) do throw <| IO.userError s!"{name}: not canonical at {x}"
  let johnson := allB (fun o : Option (Out (Fin n)) => match o with
    | some (Sum.inr _) => true
    | _ => false) T
  IO.println s!"{name}: {expected} valid leaves, canonical{if johnson then ", all Johnson" else ""}"

#eval checkSoj "Petersen, t = 6" (graphCfg petersen) 6 (Equiv.swap 0 3 * Equiv.swap 1 7) 10
#eval checkSoj "Clebsch, t = 9" (graphCfg clebsch) 9 (Equiv.swap 0 5 * Equiv.swap 2 11) 16

/-! ### Proposition 5.8 -/

/-- The ordered pairs of distinct points of `{0, …, 4}`. -/
def pairs20 : List (ℕ × ℕ) :=
  (List.range 5).flatMap fun a => ((List.range 5).filter (· ≠ a)).map fun b => (a, b)

/-- The orbital configuration of `Sym(5)` on the 20 ordered pairs (points `0 … 19`) and the 10
2-subsets (points `20 … 29`) of `{0, …, 4}`: the colour of two points is their equality
pattern. -/
def sym5 (p q : Fin 30) : ℕ :=
  let P (i : Fin 30) := pairs20.getD i.val (0, 0)
  let S (i : Fin 30) := petersenPts.getD (i.val - 20) (0, 0)
  let b (x : Bool) := if x then 1 else 0
  if p.val < 20 then
    if q.val < 20 then
      8 * b ((P p).1 = (P q).1) + 4 * b ((P p).1 = (P q).2) + 2 * b ((P p).2 = (P q).1) +
        b ((P p).2 = (P q).2)
    else 16 + 2 * b ((P p).1 = (S q).1 || (P p).1 = (S q).2) +
      b ((P p).2 = (S q).1 || (P p).2 = (S q).2)
  else if q.val < 20 then 20 + 2 * b ((P q).1 = (S p).1 || (P q).1 = (S p).2) +
      b ((P q).2 = (S p).1 || (P q).2 = (S p).2)
  else 24 + b ((S p).1 = (S q).1 || (S p).1 = (S q).2) + b ((S p).2 = (S q).1 || (S p).2 = (S q).2)

/-- The 3-subsets (points `0 … 34`) and 2-subsets (points `35 … 55`) of `{0, …, 6}`. -/
def subs3 : List (List ℕ) := ((List.range 7).sublistsLen 3)
def subs2 : List (List ℕ) := ((List.range 7).sublistsLen 2)

/-- The orbital configuration of `Sym(7)` on the 3-subsets and the 2-subsets of `{0, …, 6}`:
the colour records the two sides and the size of the intersection. -/
def sym7 (p q : Fin 56) : ℕ :=
  let set (i : Fin 56) := if i.val < 35 then subs3.getD i.val [] else subs2.getD (i.val - 35) []
  let side (i : Fin 56) := if i.val < 35 then 0 else 1
  10 * (2 * side p + side q) + ((set p).filter (· ∈ set q)).length

/-- The ideal points of `W₂` are nonempty pairwise disjoint subsets of `C₂`, and there are at
most `|C₂|/2` of them. -/
def idealB {n : ℕ} (C₂ : Finset (Fin n)) (W₂ : Finset (Finset (Fin n))) : Bool :=
  cellsB W₂ && decide (W₂.biUnion id ⊆ C₂) && decide (2 * W₂.card ≤ C₂.card)

/-- `W₁ ⊆ C₁`, `|C₁| ≤ 2|W₁|`, and the twin classes of `W₁` have at most `|W₁|/2` points. -/
def sideB {n : ℕ} (C₁ W₁ : Finset (Fin n)) (W₂ : Finset (Finset (Fin n)))
    (A : Fin n → Finset (Fin n) → Bool) : Bool :=
  decide (W₁ ⊆ C₁) && decide (C₁.card ≤ 2 * W₁.card) &&
    decide (∀ x ∈ W₁, 2 * (twinCls W₁ W₂ A x).card ≤ W₁.card)

/-- Validity of a leaf of `cohSoj`, as a Boolean. -/
def cohOkB {n : ℕ} (C₁ C₂ : Finset (Fin n)) : Option (CohOut (Fin n)) → Bool
  | some (.part p) => decide (IsColPart C₁ (C₁.card / 2) p)
  | some (.bip W₁ W₂ A) => sideB C₁ W₁ W₂ A && idealB C₂ W₂
  | none => false

/-- Check `cohSoj` on a coherent configuration on `C₁ ∪ C₂ = Fin n`: the hypotheses hold, every
leaf is valid, the count is at most `|C₂|`. -/
def checkCoh {n : ℕ} (name : String) (c : Fin n → Fin n → ℕ) (C₁ C₂ : Finset (Fin n)) :
    IO Unit := do
  unless coh2B c do throw <| IO.userError s!"{name}: not coherent"
  let hyp := decide ((∀ x ∈ C₁, ∀ y ∈ C₁, c x x = c y y) ∧ (∀ x ∈ C₂, ∀ y ∈ C₂, c x x = c y y) ∧
    (∀ x ∈ C₁, ∀ y ∈ C₂, c x x ≠ c y y) ∧ C₂.card < C₁.card ∧
    (∃ x ∈ C₁, ∃ y ∈ C₂, ∃ x' ∈ C₁, ∃ y' ∈ C₂, c x y ≠ c x' y') ∧ ¬ IsClique c C₂)
  unless hyp do throw <| IO.userError s!"{name}: hypotheses fail"
  let T := cohSoj C₁ C₂ c
  unless allB (cohOkB C₁ C₂) T do throw <| IO.userError s!"{name}: invalid leaf"
  unless T.count ≤ C₂.card do throw <| IO.userError s!"{name}: count {T.count}"
  IO.println s!"{name}: {T.count} valid leaves"

/-- The two orbits of `Sym(5)`. -/
def sym5C₁ : Finset (Fin 30) := univ.filter fun i => i.val < 20
def sym5C₂ : Finset (Fin 30) := univ.filter fun i => 20 ≤ i.val

/-- The two orbits of `Sym(7)`. -/
def sym7C₁ : Finset (Fin 56) := univ.filter fun i => i.val < 35
def sym7C₂ : Finset (Fin 56) := univ.filter fun i => 35 ≤ i.val

#eval checkCoh "Sym(5) on ordered pairs and 2-subsets" sym5 sym5C₁ sym5C₂
#eval checkCoh "Sym(7) on 3-subsets and 2-subsets" sym7 sym7C₁ sym7C₂

/-! ### Steps of Proposition 5.7 -/

/-! ### Proposition 5.7 -/

/-- Run `bsoj` on `V₁ = ` the `k`-subsets of `{0, …, m − 1}` with the listed ones removed (as
points `0, 1, …`) against the `m` cells `{N}, …, {N + m − 1}` (`N` = the number of subsets),
adjacency = membership, threshold `t`: the hypotheses of `bipartite_split_or_johnson` hold,
every leaf is valid, and the count is as expected. -/
def checkBsoj (name : String) (m k t : ℕ) (drop : List ℕ) (expected : ℕ)
    (johnson : Bool) : IO Unit := do
  let subs := ((List.range m).sublistsLen k).zipIdx.filter fun p => p.2 ∉ drop
  let N := ((List.range m).sublistsLen k).length
  let n := N + m
  let V₁ : Finset (Fin n) := univ.filter fun i => i.val ∈ subs.map Prod.snd
  let V₂ : Finset (Finset (Fin n)) := (univ.filter fun i : Fin n => N ≤ i.val).image singleton
  let A : Fin n → Finset (Fin n) → Bool := fun x s =>
    decide (∃ y ∈ s, y.val - N ∈ (((List.range m).sublistsLen k).getD x.val []))
  let hyp := decide (V₂.card ≤ t ∧ V₁.card + 2 ≤ 2 * t ∧ t < V₁.card ∧
    ∀ x ∈ V₁, (twinCls V₁ V₂ A x).card ≤ t) && cellsB V₂
  unless hyp do throw <| IO.userError s!"{name}: hypotheses fail"
  let T := bsoj t V₁ V₂ A
  unless allB (validB V₁ t) T do throw <| IO.userError s!"{name}: invalid leaf"
  unless T.count = expected do throw <| IO.userError s!"{name}: count {T.count}"
  let isJ := allB (fun o : Option (Out (Fin n)) => match o with
    | some (Sum.inr _) => true
    | _ => false) T
  unless isJ = johnson do throw <| IO.userError s!"{name}: outcome type"
  IO.println s!"{name}: {expected} valid leaves{if johnson then ", Johnson" else ""}"

#eval checkBsoj "J(7, 3) incidence, t = 19" 7 3 19 [] 1 true
#eval checkBsoj "J(6, 2) minus a point, t = 8" 6 2 8 [0] 720 false

end GraphIsoChecks.SplitJohnson
