module

public import GraphIso.SplitJohnson.CoherentDef
public import GraphIso.Coherent.WLOn
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Finset.Sum
public import Mathlib.Data.Fintype.List
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Nat.Pairing

/-!
# Bipartite Split-or-Johnson: the procedure

Helfgott, Prop. 5.7. The input is a bipartite graph `(V₁, V₂; A)`: `V₁` is a set of points,
`V₂` a set of cells (Babai's "ideal points", nonempty and pairwise disjoint), and
`A : α → Finset α → Bool`; with it a threshold `t` that stays fixed through the recursion
(Helfgott's "original value of `|V₁|`"). `bsoj t V₁ V₂ A` returns a choice tree whose leaves
are colored `t`-partitions of `V₁` or Johnson embeddings in `V₁` on more than `t` points.

One level (`bstep`), with the recursive calls supplied by `rec`:
1. **Twins and degrees**: colour `V₁` by twin-class size and degree, splitting the classes
   with twins into twin classes (`twinPart`); done unless the points without twins of some
   degree `d₁` form a set `V₁'` of more than `t` points.
2. **Johnson**: complementing if `2d₁ > v` (`v = |V₂|`), the neighbourhoods `f x` are distinct
   `s`-subsets of `V₂`; if all `s`-subsets occur, `V₁'` is the Johnson scheme `J(v, s)`.
3. **Base** (`v² ≤ 27 L³`, `L = ⌈log₂ 2t⌉`): choose an enumeration of `V₂` and colour `V₁` by
   neighbourhoods (`nbrCode`). Helfgott takes the base case first; testing for a Johnson
   scheme first makes no choice and lets small inputs reach the Johnson outcome.
   Otherwise, **the `d`-ary structure** on `V₂`, `d = min(s, 6j)` with `j = ⌈log_v |V₁'|⌉`: a
   tuple of distinct cells is coloured by `1 +` the number of neighbourhoods containing it
   (`daryCol`). If more than half of `V₂` are twins, recurse on one side of the split
   (Exercise 5.5, `pickSide`). Otherwise refine by Weisfeiler–Leman and choose a list `x` that
   satisfies the Design Lemma with threshold `⌊2v/3⌋` (`dlGood`).
4. **After the choice**: (a) without a dominant colour, recurse on a third of `V₂`
   (`selThird`, `pickSide`); (b) with a dominant class `C` and a non-clique 2-skeleton `Y`,
   refine the graph on `V₁' ⊔ V₂` (with `Y` on `V₂`) by Weisfeiler–Leman (`cQ`), find the
   dominant classes `C₂ ⊆ V₂` and `C₁ ⊆ V₁'`, and either recurse on `V₂ \ C₂` (if the colour
   is constant on `C₁ × C₂`) or apply Coherent Split-or-Johnson to `C₁ ⊔ C₂` and recurse on
   its bipartite graph, whose ideal points become cells by union (`cellOf`).

Points dropped at a level get new colours, each set as one block (`addPiece`), so a colored
partition found deeper extends to the current `V₁`.
-/

@[expose] public section

namespace GraphIso.SplitJohnson

open Finset Pointwise GraphIso.Coherent

variable {α : Type*} [DecidableEq α]

/-- The trees of Split-or-Johnson. -/
abbrev STree (α : Type*) := CTree (Choice α) (Option (Out α))

instance {V : Type*} [DecidableEq V] (c : V → V → ℕ) (C : Finset V) :
    Decidable (IsClique c C) := by
  unfold IsClique
  infer_instance

instance {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ} (c : (Fin k → V) → ℕ) (u v : V) :
    Decidable (IsTwin c u v) := by
  unfold IsTwin
  infer_instance

/-- Relabel a bipartite relation between points and cells. -/
def relabA (σ : Equiv.Perm α) (A : α → Finset α → Bool) : α → Finset α → Bool :=
  fun x s => A (σ⁻¹ • x) (σ⁻¹ • s)

/-! ### Dropped pieces -/

/-- Colour the points of `D` by a new colour, with `D` as one block. -/
def addPiece (D : Finset α) (p : CPart α) : CPart α :=
  ⟨fun x => if x ∈ D then 0 else p.col x + 1, fun x => if x ∈ D then D else p.blk x⟩

/-- `addPiece` on a leaf. -/
def addPieceOut (D : Finset α) : Option (Out α) → Option (Out α)
  | some (Sum.inl p) => some (Sum.inl (addPiece D p))
  | o => o

/-- Add a dropped piece to every leaf. -/
def withPiece (D : Finset α) (t : STree α) : STree α :=
  t.bind fun o => .leaf (addPieceOut D o)

/-! ### Step 0: the base case -/

/-- The cells of a choice. -/
def choiceCells (ch : Choice α) : List (Finset α) :=
  List.filterMap (fun q : α ⊕ Finset α => q.getRight?) (show List (α ⊕ Finset α) from ch)

/-- The adjacency vector of `x` along the list `e`, as a binary number. -/
def nbrCode (A : α → Finset α → Bool) (e : List (Finset α)) (x : α) : ℕ :=
  Nat.ofDigits 2 (e.map fun s => if A x s then 1 else 0)

/-- The base threshold: `v² ≤ 27 L³` with `L = ⌈log₂ 2t⌉`. -/
def IsBase (t v : ℕ) : Prop := v ^ 2 ≤ 27 * Nat.clog 2 (2 * t) ^ 3

instance (t v : ℕ) : Decidable (IsBase t v) := by
  unfold IsBase
  infer_instance

/-- The enumerations of `V₂`, as choices. -/
def enums (V₂ : Finset (Finset α)) : Finset (Choice α) :=
  (Multiset.lists V₂.val).toFinset.image fun l => l.map Sum.inr

/-! ### Step 1: twins and degrees -/

/-- The degree of `x`. -/
def deg (V₂ : Finset (Finset α)) (A : α → Finset α → Bool) (x : α) : ℕ :=
  (V₂.filter fun s => A x s).card

/-- The size of the twin class of `x`. -/
def tw (V₁ : Finset α) (V₂ : Finset (Finset α)) (A : α → Finset α → Bool) (x : α) : ℕ :=
  (twinCls V₁ V₂ A x).card

/-- The points of `V₁` without twins and of degree `d`. -/
def tfDeg (V₁ : Finset α) (V₂ : Finset (Finset α)) (A : α → Finset α → Bool) (d : ℕ) :
    Finset α :=
  V₁.filter fun x => tw V₁ V₂ A x = 1 ∧ deg V₂ A x = d

/-- The degrees whose points without twins are more than `t`. -/
def bigDegs (t : ℕ) (V₁ : Finset α) (V₂ : Finset (Finset α)) (A : α → Finset α → Bool) :
    Finset ℕ :=
  (V₁.image (deg V₂ A)).filter fun d => t < (tfDeg V₁ V₂ A d).card

/-- Colour by twin-class size and degree; classes with twins are split into twin classes. -/
def twinPart (V₁ : Finset α) (V₂ : Finset (Finset α)) (A : α → Finset α → Bool) : CPart α :=
  ⟨fun x => Nat.pair (tw V₁ V₂ A x) (deg V₂ A x), fun x =>
    if tw V₁ V₂ A x = 1 then tfDeg V₁ V₂ A (deg V₂ A x) else twinCls V₁ V₂ A x⟩

/-! ### Step 2: the Johnson test -/

/-- The neighbourhood of `x` in `V₂`. -/
def nbr (V₂ : Finset (Finset α)) (A : α → Finset α → Bool) (x : α) : Finset (Finset α) :=
  V₂.filter fun s => A x s

/-- The size of the neighbourhoods after complementing (if `2d₁ > v`). -/
def sOf (v d₁ : ℕ) : ℕ := if v < 2 * d₁ then v - d₁ else d₁

/-- The neighbourhoods after complementing (if `2d₁ > |V₂|`). -/
def fOf (V₂ : Finset (Finset α)) (A : α → Finset α → Bool) (d₁ : ℕ) (x : α) :
    Finset (Finset α) :=
  if V₂.card < 2 * d₁ then V₂ \ nbr V₂ A x else nbr V₂ A x

/-- The arity of the structure on `V₂`: `min(s, 6 ⌈log_v n₁⌉)`. -/
def arity (v s n₁ : ℕ) : ℕ := min s (6 * Nat.clog v n₁)

/-! ### Step 3: the `d`-ary structure -/

/-- A `d`-tuple of distinct cells is coloured by `1 +` the number of sets of `H` containing
it; other tuples by `0`. -/
def daryCol (V₂ : Finset (Finset α)) (H : Finset (Finset (Finset α))) (d : ℕ)
    (x : Fin d → V₂) : ℕ :=
  if (univ.image fun i => (x i).val).card = d then
    1 + (H.filter fun e => (univ.image fun i => (x i).val) ⊆ e).card
  else 0

/-- The points of `V₂` whose twin class has more than half of `V₂`, as cells. -/
def bigTwins (V₂ : Finset (Finset α)) {d : ℕ} (c : (Fin d → V₂) → ℕ) : Finset (Finset α) :=
  (univ.filter fun u : V₂ =>
    V₂.card < 2 * (univ.filter fun w => IsTwin c u w).card).map (Function.Embedding.subtype _)

/-- Exercise 5.5's choice between `S` and `V₂ \ S`: `S` if it leaves no twin class of
`|V₁|/2 + 1` or more points in `V₁`. -/
def pickSide (V₁ : Finset α) (V₂ S : Finset (Finset α)) (A : α → Finset α → Bool) :
    Finset (Finset α) :=
  if ∀ x ∈ V₁, 2 * (twinCls V₁ S A x).card < V₁.card + 2 then S else V₂ \ S

/-- The lists of length `n` over `S`. -/
def tuples {β : Type*} [DecidableEq β] (S : Finset β) : ℕ → Finset (List β)
  | 0 => {[]}
  | n + 1 => (S ×ˢ tuples S n).image fun p => p.1 :: p.2

/-- The lists of length less than `d` over `S`. -/
def tuplesLt {β : Type*} [DecidableEq β] (S : Finset β) (d : ℕ) : Finset (List β) :=
  (range d).biUnion (tuples S)

/-- The Design Lemma's conclusion at `x`, threshold `t₂`. -/
def DLGood {V : Type*} [Fintype V] [DecidableEq V] {d : ℕ} (W : (Fin d → V) → ℕ) (t₂ : ℕ)
    (x : List V) : Prop :=
  (∀ u, (cls1 W x u).card ≤ t₂) ∨
    (x.length + 2 ≤ d ∧ ∃ u, t₂ < (cls1 W x u).card ∧ ¬ IsClique (skel2 W x) (cls1 W x u))

instance {V : Type*} [Fintype V] [DecidableEq V] {d : ℕ} (W : (Fin d → V) → ℕ) (t₂ : ℕ)
    (x : List V) : Decidable (DLGood W t₂ x) := by
  unfold DLGood
  infer_instance

/-- The cells of a choice that lie in `V₂`, as points of `↥V₂`. -/
def decodeV₂ (V₂ : Finset (Finset α)) (ch : Choice α) : List V₂ :=
  (choiceCells ch).filterMap fun s => if h : s ∈ V₂ then some ⟨s, h⟩ else none

/-- A third of `S` by colour: the reddest class of more than `|S|/3` points if there is one,
otherwise the union of the reddest classes until it exceeds `|S|/3`. -/
def selThird {β : Type*} [DecidableEq β] (S : Finset β) (col : β → ℕ) : Finset β :=
  let cols := (S.image col).sort (· ≤ ·)
  match cols.find? (fun k => decide (S.card < 3 * (S.filter fun x => col x = k).card)) with
  | some k => S.filter fun x => col x = k
  | none =>
    let m := ((List.range (cols.length + 1)).find? fun m =>
      decide (S.card < 3 * (S.filter fun x => col x ∈ cols.take m).card)).getD cols.length
    S.filter fun x => col x ∈ cols.take m

/-! ### Step 4: the classical structure on `V₁' ⊔ V₂` -/

/-- The initial colours on `V₁' ⊔ V₂`: the edges `A` (both directions) and the 2-skeleton `Y`
on `V₂`. -/
def code (A : α → Finset α → Bool) (Y : Finset α → Finset α → ℕ) :
    α ⊕ Finset α → α ⊕ Finset α → ℕ
  | .inl _, .inl _ => 0
  | .inl x, .inr s => if A x s then 1 else 2
  | .inr s, .inl x => if A x s then 3 else 4
  | .inr s, .inr s' => 5 + Y s s'

/-- The classical Weisfeiler–Leman refinement of `code A Y` on `S`, extended by `0`. -/
def cohOn (S : Finset (α ⊕ Finset α)) (c₀ : α ⊕ Finset α → α ⊕ Finset α → ℕ) :
    α ⊕ Finset α → α ⊕ Finset α → ℕ :=
  fun a b => if h : a ∈ S ∧ b ∈ S then
    wlOn 2 (fun p : Fin 2 → S => c₀ (p 0).val (p 1).val) ![⟨a, h.1⟩, ⟨b, h.2⟩] else 0

/-- The cell of an ideal point: the union of its cells. -/
def cellOf (B : Finset (α ⊕ Finset α)) : Finset α := B.toRight.sup id

/-- Extend a 2-skeleton on `↥V₂` to all cells by `0`. -/
def extCells (V₂ : Finset (Finset α)) (Y : V₂ → V₂ → ℕ) (s s' : Finset α) : ℕ :=
  if h : s ∈ V₂ ∧ s' ∈ V₂ then Y ⟨s, h.1⟩ ⟨s', h.2⟩ else 0

/-! ### One level -/

/-- Continue after Coherent Split-or-Johnson on `C₁ ⊔ C₂`. -/
def cohCont (t : ℕ) (V₁ V₁' C₁ : Finset α) (rec : Finset α → Finset (Finset α) →
    (α → Finset α → Bool) → STree α) : Option (CohOut (α ⊕ Finset α)) → STree α
  | some (.part p) =>
    .leaf (some (.inl (addPiece (V₁ \ V₁') (addPiece (V₁' \ C₁)
      ⟨fun x => p.col (.inl x), fun x => (p.blk (.inl x)).toLeft⟩))))
  | some (.bip W₁ W₂ A') =>
    let W := W₁.toLeft
    if W.card ≤ t then
      .leaf (some (.inl (addPiece (V₁ \ V₁') (addPiece (V₁' \ C₁) (addPiece (C₁ \ W)
        (colPart W fun _ => 0))))))
    else
      withPiece (V₁ \ V₁') (withPiece (V₁' \ C₁) (withPiece (C₁ \ W)
        (rec W (W₂.image cellOf) fun x s => decide (∃ B ∈ W₂, cellOf B = s ∧ A' (.inl x) B))))
  | none => .leaf none

/-- Recursive calls after a choice must shrink `V₂` to at most two thirds (this always holds
under the hypotheses; the guard makes the count bound unconditional). -/
def shrink (V₂ : Finset (Finset α)) (rec : Finset α → Finset (Finset α) →
    (α → Finset α → Bool) → STree α) (V₁' : Finset α) (V₂' : Finset (Finset α))
    (A' : α → Finset α → Bool) : STree α :=
  if 3 * V₂'.card ≤ 2 * V₂.card then rec V₁' V₂' A' else .leaf none

/-- Continue after the Design Lemma's choice `x`. -/
def dlCont (t : ℕ) (V₁ V₁' : Finset α) (V₂ : Finset (Finset α)) (A : α → Finset α → Bool)
    {d : ℕ} (W : (Fin d → V₂) → ℕ) (rec₀ : Finset α → Finset (Finset α) →
    (α → Finset α → Bool) → STree α) (x : List V₂) : STree α :=
  let rc := shrink V₂ rec₀
  let t₂ := 2 * V₂.card / 3
  if ∀ u, (cls1 W x u).card ≤ t₂ then
    -- (a) no dominant colour: recurse on a third of `V₂`
    withPiece (V₁ \ V₁') (rc V₁'
      (pickSide V₁' V₂ ((selThird univ (skel1 W x)).map (Function.Embedding.subtype _)) A) A)
  else
    -- (b) a dominant class with a non-clique 2-skeleton
    let SQ := V₁'.disjSum V₂
    let cQ := cohOn SQ (code A (extCells V₂ (skel2 W x)))
    let col₂ := fun s => cQ (.inr s) (.inr s)
    if ∀ s ∈ V₂, (V₂.filter fun s' => col₂ s' = col₂ s).card ≤ t₂ then
      withPiece (V₁ \ V₁') (rc V₁' (pickSide V₁' V₂ (selThird V₂ col₂) A) A)
    else
      let C₂ := V₂.filter fun s => t₂ < (V₂.filter fun s' => col₂ s' = col₂ s).card
      let col₁ := fun y => cQ (.inl y) (.inl y)
      let C₁ := V₁'.filter fun y => t < (V₁'.filter fun y' => col₁ y' = col₁ y).card
      if C₁ = ∅ then
        .leaf (some (.inl (addPiece (V₁ \ V₁') (colPart V₁' col₁))))
      else if ∀ y ∈ C₁, ∀ s ∈ C₂, ∀ y' ∈ C₁, ∀ s' ∈ C₂,
          cQ (.inl y) (.inr s) = cQ (.inl y') (.inr s') then
        withPiece (V₁ \ V₁') (rc V₁' (V₂ \ C₂) A)
      else
        ((cohSoj (C₁.map ⟨Sum.inl, Sum.inl_injective⟩) (C₂.map ⟨Sum.inr, Sum.inr_injective⟩)
            cQ).trans (fun q => [q]) (fun ch : Choice α =>
              (show List (α ⊕ Finset α) from ch).headD (.inr ∅)) id).bind
          (cohCont t V₁ V₁' C₁ rc)

/-- **One level of Bipartite Split-or-Johnson**, with the recursive calls supplied by `rec`. -/
def bstep (t : ℕ) (V₁ : Finset α) (V₂ : Finset (Finset α)) (A : α → Finset α → Bool)
    (rec : Finset α → Finset (Finset α) → (α → Finset α → Bool) → STree α) : STree α :=
  if h : (bigDegs t V₁ V₂ A).Nonempty then
    let d₁ := (bigDegs t V₁ V₂ A).min' h
    let V₁' := tfDeg V₁ V₂ A d₁
    let v := V₂.card
    let s := sOf v d₁
    if V₁'.card = v.choose s then
      -- 2. Johnson
      .leaf (some (.inr ⟨V₁', V₂, s, fOf V₂ A d₁⟩))
    else if IsBase t v then
      -- 0. base: individualize all of `V₂`
      .node (enums V₂) fun e => .leaf (some (.inl (colPart V₁ (nbrCode A (choiceCells e)))))
    else
      -- 3. the `d`-ary structure on `V₂`
      let d := arity v s V₁'.card
      let cd := daryCol V₂ (V₁'.image (fOf V₂ A d₁)) d
      let S := bigTwins V₂ cd
      if S.Nonempty then
        withPiece (V₁ \ V₁') (rec V₁' (pickSide V₁' V₂ S A) A)
      else
        let W := wlOn d cd
        .node (((tuplesLt univ d).filter (DLGood W (2 * v / 3))).image
            fun x => x.map fun u => (.inr u.val : α ⊕ Finset α)) fun ch =>
          dlCont t V₁ V₁' V₂ A W rec (decodeV₂ V₂ ch)
  else
    -- 1. no large class without twins
    .leaf (some (.inl (twinPart V₁ V₂ A)))

/-- **Bipartite Split-or-Johnson** (Helfgott, Prop. 5.7), by recursion on the number of
cells. -/
def bsoj (t : ℕ) (V₁ : Finset α) (V₂ : Finset (Finset α)) (A : α → Finset α → Bool) :
    STree α :=
  bstep t V₁ V₂ A fun V₁' V₂' A' =>
    if _h : V₂'.card < V₂.card then bsoj t V₁' V₂' A' else .leaf none
termination_by V₂.card

end GraphIso.SplitJohnson
